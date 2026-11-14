-- Prove2me | Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_Access
-- name    : ConsistentSubmodular_Deterministic_Certificates_Access
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:14:26.496431+00:00
-- url     : https://prove2.me/theorems/e2261dd4-60f2-468c-a405-b1cdf4ab1d0e
-- title:
--   Access certificates and strong credit on atomic profiles: pessimistically safe edges, root access, extension
-- statement:
--   Let $P$ be an atomic profile with stages $0,\dots,m$, designated mass $A_t$ (`designated`), residuals $r_{h,s}$ (`residual`), benchmark $B_t$ (`benchmark`), and let `SafePath` $P\,0\,\tfrac34\,\gamma$ mean that the path $\gamma$ stays in the simplex with stage-$0$ value at least $3/4$ at all nodes and along all segments.
--
--   - `AccessCertificate` $P\,h$: a structure with an `entry` path $\gamma$, `initial` ($\gamma$ starts at the vertex $\delta_0$), `terminal` ($\gamma$ ends at $\delta_h$), `safe` ($\gamma$ is safe at stage $0$ at level $3/4$), and `pieces` (at most $h$ segments).
--   - `StrongCredit` $h$: $\tfrac12\le B_h-1$ or $1-A_h\le (B_h-1)(1-(B_h-1))$.
--   - `PessimisticSafeEdge` $h\,s$: for all $z\in[0,1]$,
--   $$\tfrac34\le A_h-(A_h-A_s)z-r_{h,s}\,z(1-z),$$
--   the pessimistic lower bound for the stage-$0$ value along the edge from $\delta_h$ to $\delta_s$.
--   - `rootAccess`: for a canonical profile, the zero-piece path constant at $\delta_0$ is an access certificate for $h=0$.
--   - `extendAccess` $h\,s$: for $h<s$ and a pessimistically safe edge $h\to s$, the access certificate to $h$ extended by the segment $\delta_h\to\delta_s$ is an access certificate to $s$, with one more piece.
--
--   The file also proves that a pessimistically safe edge is a safe path, that it propagates strong credit from $h$ to $s$, and that strong credit together with $A_h\ge 3/4$ gives the baseline budget $2(1-A_h)\le L_h$.
--
--   These objects build the entry paths of the clairvoyant certificates for the deterministic $3/4$ bound (Appendix B) by walking forward along safe relays from the first vertex.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Certificates/Access.lean (definitions and supporting lemmas of this module, ported from Lean v4.30.0-rc1 to Lean v4.33.1)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_BaselineStop
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_RelayError
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_Checkpoint

noncomputable section

namespace ConsistentSubmodular

variable {m atomCount : ℕ}

structure AccessCertificate (P : AtomicProfile m atomCount) (h : Fin (m + 1)) where
  entry : PolygonalPath m
  initial : entry.node 0 = vertex 0
  terminal : entry.node (Fin.last entry.pieces) = vertex h
  safe : SafePath P 0 ((3 : ℝ) / 4) entry
  pieces : entry.pieces ≤ h.val

namespace AtomicProfile

variable (P : AtomicProfile m atomCount)

def StrongCredit (h : Fin (m + 1)) : Prop :=
  (1 : ℝ) / 2 ≤ P.benchmark h - 1 ∨
    1 - P.designated h ≤ (P.benchmark h - 1) * (1 - (P.benchmark h - 1))

def PessimisticSafeEdge (h s : Fin (m + 1)) : Prop :=
  ∀ z : ℝ, 0 ≤ z → z ≤ 1 → (3 : ℝ) / 4 ≤
    P.designated h - (P.designated h - P.designated s) * z -
      P.residual h s * z * (1 - z)

def rootAccess (hP : P.Canonical) : AccessCertificate P 0 where
  entry := PolygonalPath.constant (vertex 0)
  initial := rfl
  terminal := rfl
  safe := by
    apply (safePath_constant_iff _ _ _ _).2
    refine ⟨simplex_vertex 0, ?_⟩
    rw [P.value_designated_vertex, P.benchmark_zero hP]
    norm_num
  pieces := by simp

theorem pessimisticEdge_safe (h s : Fin (m + 1)) (hhs : h < s)
    (hsafe : P.PessimisticSafeEdge h s) :
    SafePath P 0 ((3 : ℝ) / 4) (PolygonalPath.segment (vertex h) (vertex s)) := by
  apply safePath_segment
  intro z hz hz1
  refine ⟨(simplex_vertex h).mix (simplex_vertex s) hz hz1, ?_⟩
  have hlow := P.value_mix_vertices_lower 0 h s (ne_of_lt hhs) hz hz1
    (P.overlap_le_persistent h s 0)
  rw [P.baseline_zero, P.residual_persistence h 0 (Fin.zero_le _),
    P.residual_persistence s 0 (Fin.zero_le _)] at hlow
  have hs := hsafe z hz hz1
  nlinarith

def extendAccess (h s : Fin (m + 1)) (hhs : h < s)
    (access : AccessCertificate P h) (hsafe : P.PessimisticSafeEdge h s) :
    AccessCertificate P s := by
  let seg := PolygonalPath.segment (vertex h) (vertex s)
  have hjoin : access.entry.node (Fin.last access.entry.pieces) = seg.node 0 := access.terminal
  exact {
    entry := PolygonalPath.append access.entry seg
    initial := by rw [PolygonalPath.append_initial, access.initial]
    terminal := by
      rw [PolygonalPath.append_terminal _ _ hjoin]
      exact PolygonalPath.segment_terminal _ _
    safe := access.safe.append (P.pessimisticEdge_safe h s hhs hsafe) hjoin
    pieces := by
      simp only [PolygonalPath.append_pieces]
      change access.entry.pieces + 1 ≤ s.val
      have := access.pieces
      have : h.val < s.val := hhs
      omega }

theorem strongCredit_of_pessimisticEdge (hP : P.Canonical)
    (h s : Fin (m + 1)) (hhs : h ≤ s) (hsafe : P.PessimisticSafeEdge h s) :
    P.StrongCredit s := by
  have hpersist := P.persistence_credit h s hhs
  have hcanon := P.one_le_benchmark hP h
  unfold benchmark at hcanon
  exact safe_relay_strong_credit (P.designated h) (P.designated s) (P.residual h s)
    (P.benchmark s - 1) (P.designated_le_one hP h) (P.designated_antitone hP hhs)
    (P.residual_nonnegative h s) (hP.2 s h) (by linarith) hsafe

theorem strongCredit_baseline (hP : P.Canonical) (h : Fin (m + 1))
    (hA : (3 : ℝ) / 4 ≤ P.designated h) (hc : P.StrongCredit h) :
    2 * (1 - P.designated h) ≤ P.baseline h :=
  strong_credit_baseline (P.designated h) (P.baseline h)
    (P.designated_le_one hP h) hc hA

end AtomicProfile

end ConsistentSubmodular

end


