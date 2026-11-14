-- Prove2me | Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_VertexCheckpoint
-- name    : ConsistentSubmodular_Deterministic_Certificates_VertexCheckpoint
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:15:32.846519+00:00
-- url     : https://prove2.me/theorems/5a703112-f9b4-4b4b-a839-658b901ceceb
-- title:
--   Checkpoint certificate at a vertex $\delta_h$ when the raw envelope is nonpositive
-- statement:
--   Let $P$ be a canonical atomic profile with stages $0,\dots,m$ and let $h$ be a stage with $\mathrm{designated}_h \ge 3/4$, a strong credit and an access certificate (a safe entry path from $\delta_0$ to $\delta_h$ with at most $h$ pieces), such that the raw envelope of $h$ is nonpositive (hence zero).
--
--   - `checkpoint_of_nonpositive` produces a `CheckpointCertificate` for $P$ whose point is the vertex $\delta_h$. Its entry path is the access path of $h$. Its exit path is either the constant path at $\delta_h$ (when $h = m$ or stage $m$ is inactive) or a path of at most two segments from $\delta_h$ to $\delta_m$ safe at stage $m$ at level $\tfrac34\,\mathrm{benchmark}_m$. The point is a simplex point of support $1$, it is $\tfrac34$-safe at every stage, and the total piece count is at most $(m+1)+2$.
--
--   The file also proves that, under these hypotheses, $\tfrac34\,\mathrm{benchmark}_t \le \mathrm{value}_t(\delta_h)$ at every stage $t$.
--
--   This is the terminal branch of the selector in the construction of $(3/4, m+3)$-certificates (Theorem 7): when the envelope vanishes, the vertex itself is a valid anchor.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Certificates/VertexCheckpoint.lean (definitions and supporting lemmas of this module, ported from Lean v4.30.0-rc1 to Lean v4.33.1)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_Access
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_ActualCheckpoint

noncomputable section

namespace ConsistentSubmodular

namespace AtomicProfile

variable {m atomCount : ℕ} (P : AtomicProfile m atomCount)

theorem vertex_stages_of_nonpositive (hP : P.Canonical) (h : Fin (m + 1))
    (hA : (3 : ℝ) / 4 ≤ P.designated h) (hraw : P.rawEnvelope h ≤ 0) :
    ∀ t, (3 : ℝ) / 4 * P.benchmark t ≤ P.value t (vertex h) := by
  classical
  have hzero : P.rawEnvelope h = 0 := le_antisymm hraw (P.rawEnvelope_nonnegative h)
  intro t
  by_cases ht : P.Active t
  · rw [P.value_vertex]
    by_cases hth : t ≤ h
    · rw [P.residual_persistence h t hth]
      have hb := P.baseline_nonnegative t
      have hg := P.designated_le_one hP t
      unfold benchmark
      linarith
    · have henv := P.rawEnvelope_valid hP h t
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, lt_of_not_ge hth, ht⟩)
      rw [hzero] at henv
      unfold envelopeSlack benchmark at *
      nlinarith
  · exact P.inactive_stage_safe t (simplex_vertex h) (le_of_not_gt ht)

def checkpoint_of_nonpositive (hP : P.Canonical) (h : Fin (m + 1))
    (hA : (3 : ℝ) / 4 ≤ P.designated h) (hcredit : P.StrongCredit h)
    (access : AccessCertificate P h) (hraw : P.rawEnvelope h ≤ 0) :
    CheckpointCertificate P := by
  classical
  have hstages := P.vertex_stages_of_nonpositive hP h hA hraw
  have hzero : P.rawEnvelope h = 0 := le_antisymm hraw (P.rawEnvelope_nonnegative h)
  have hexit : ∃ γ : PolygonalPath m,
      γ.node 0 = vertex h ∧ γ.node (Fin.last γ.pieces) = vertex (Fin.last m) ∧
      SafePath P (Fin.last m) ((3 : ℝ) / 4 * P.benchmark (Fin.last m)) γ ∧
      γ.pieces ≤ 2 := by
    by_cases hh : h = Fin.last m
    · refine ⟨PolygonalPath.constant (vertex h), rfl, ?_, ?_, by simp⟩
      · simp [hh, PolygonalPath.constant]
      · exact (safePath_constant_iff _ _ _ _).2 ⟨simplex_vertex h, hstages _⟩
    · by_cases ht : P.Active (Fin.last m)
      · have henv := P.rawEnvelope_valid hP h (Fin.last m)
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _,
            lt_of_le_of_ne (Fin.le_last h) hh, ht⟩)
        rw [hzero] at henv
        have hterm := P.terminal_envelope_inequality h 0 henv
        have hbase := P.strongCredit_baseline hP h hA hcredit
        have hpersist := P.baseline_add_residual_monotone h (Fin.le_last h)
        change P.baseline h + P.designated h ≤
          P.baseline (Fin.last m) + P.residual h (Fin.last m) at hpersist
        have hbudget : 3 ≤ P.designated h +
            2 * (P.baseline (Fin.last m) + P.residual h (Fin.last m)) := by
          have hA1 := P.designated_le_one hP h
          linarith
        have he := P.actual_terminal_exit_of_budget hP h (Fin.last m) hh 0
          (by norm_num) (by norm_num) (by simpa using hstages (Fin.last m))
          hbudget (by simpa using hterm)
        simpa using he
      · exact P.inactive_terminal_exit _ (simplex_vertex h) ht
  let exit := Classical.choose hexit
  have he := Classical.choose_spec hexit
  exact {
    point := vertex h
    entry := access.entry
    exit := exit
    simplex := simplex_vertex h
    support := by rw [supportCard_vertex]; norm_num
    stages := hstages
    entry_initial := access.initial
    entry_terminal := access.terminal
    exit_initial := he.1
    exit_terminal := he.2.1
    entry_safe := access.safe
    exit_safe := he.2.2.1
    piece_budget := by
      have hp := access.pieces
      have hepiece : exit.pieces ≤ 2 := he.2.2.2
      have hh := h.isLt
      omega }

end AtomicProfile

end ConsistentSubmodular

end


