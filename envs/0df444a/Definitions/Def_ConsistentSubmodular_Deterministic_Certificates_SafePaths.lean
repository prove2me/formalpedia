-- Prove2me | Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_SafePaths
-- name    : ConsistentSubmodular_Deterministic_Certificates_SafePaths
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:09:05.2597+00:00
-- url     : https://prove2.me/theorems/eb3cf81b-600d-4af8-80cb-df1eba4c1a93
-- title:
--   Safe polygonal paths for atomic profiles: constant paths, segments, concatenation
-- statement:
--   For an atomic profile $P$, a stage $t$, a level $\ell\in\mathbb R$ and a polygonal path $\gamma$, `SafePath P t ℓ γ` states that every node of $\gamma$ and every point of every piece (the points $\mathrm{mix}(\gamma_j,\gamma_{j+1},x)$ for $x\in[0,1]$) lies in the simplex $\Delta$ and has $V_t\ge\ell$, where $V_t$ is `AtomicProfile.value P t`. This file introduces no new definitions. It proves the rules by which safe paths are built.
--
--   - A constant path at $p$ is safe iff $p\in\Delta$ and $V_t(p)\ge\ell$.
--   - A segment from $p$ to $q$ is safe if every point $\mathrm{mix}(p,q,x)$, $x\in[0,1]$, lies in $\Delta$ and has $V_t\ge\ell$.
--   - Concatenation: if $\gamma$ and $\delta$ are safe at the same stage and level and the last node of $\gamma$ equals the first node of $\delta$, then the concatenation of $\gamma$ and $\delta$ is safe.
--
--   The rules let the entry and exit paths of a certificate be assembled from short pieces, so that safety needs to be checked only segment by segment. They serve the construction of the paths of the $3/4$ certificates (Section 3, Appendix B) from atomic profiles.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Certificates/SafePaths.lean (definitions and supporting lemmas of this module, ported from Lean v4.30.0-rc1 to Lean v4.33.1)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Basic_Paths
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_AtomicFacts

noncomputable section

namespace ConsistentSubmodular

variable {m atomCount : ℕ}

theorem safePath_constant_iff (P : AtomicProfile m atomCount) (t : Fin (m + 1))
    (level : ℝ) (p : Point m) :
    SafePath P t level (PolygonalPath.constant p) ↔ IsSimplex p ∧ level ≤ P.value t p := by
  constructor
  · intro h
    exact h.1 0
  · intro h
    constructor
    · intro _
      exact h
    · intro j
      exact Fin.elim0 j

theorem safePath_segment (P : AtomicProfile m atomCount) (t : Fin (m + 1))
    (level : ℝ) (p q : Point m)
    (h : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → IsSimplex (mix p q x) ∧
      level ≤ P.value t (mix p q x)) :
    SafePath P t level (PolygonalPath.segment p q) := by
  constructor
  · intro j
    fin_cases j
    · simpa [PolygonalPath.segment] using h 0 le_rfl zero_le_one
    · simpa [PolygonalPath.segment] using h 1 zero_le_one le_rfl
  · intro j x hx hx'
    fin_cases j
    simpa [PolygonalPath.segment] using h x hx hx'

theorem SafePath.append {P : AtomicProfile m atomCount} {t : Fin (m + 1)}
    {level : ℝ} {γ δ : PolygonalPath m} (hγ : SafePath P t level γ)
    (hδ : SafePath P t level δ) (hjoin : γ.node (Fin.last γ.pieces) = δ.node 0) :
    SafePath P t level (PolygonalPath.append γ δ) := by
  constructor
  · intro i
    by_cases hi : i.val ≤ γ.pieces
    · rw [PolygonalPath.append_node_left γ δ i hi]
      exact hγ.1 _
    · rw [PolygonalPath.append_node_right γ δ hjoin i (by omega)]
      exact hδ.1 _
  · intro j x hx hx'
    by_cases hj : j.val < γ.pieces
    · rw [PolygonalPath.append_node_left γ δ j.castSucc (by simpa [-PolygonalPath.append_pieces] using Nat.le_of_lt hj),
        PolygonalPath.append_node_left γ δ j.succ (by simpa [-PolygonalPath.append_pieces] using hj)]
      exact hγ.2 ⟨j.val, hj⟩ x hx hx'
    · have hj' : γ.pieces ≤ j.val := Nat.le_of_not_gt hj
      rw [PolygonalPath.append_node_right γ δ hjoin j.castSucc (by simpa [-PolygonalPath.append_pieces] using hj'),
        PolygonalPath.append_node_right γ δ hjoin j.succ (by simp only [Fin.val_succ]; omega)]
      have hbound : j.val - γ.pieces < δ.pieces := by
        have := j.isLt
        simp only [PolygonalPath.append_pieces] at this
        omega
      have hend : (⟨j.succ.val - γ.pieces, by
          simp only [Fin.val_succ]
          omega⟩ : Fin (δ.pieces + 1)) =
          (⟨j.val - γ.pieces, hbound⟩ : Fin δ.pieces).succ := by
        apply Fin.ext
        simp only [Fin.val_succ]
        omega
      rw [hend]
      exact hδ.2 ⟨j.val - γ.pieces, hbound⟩ x hx hx'

end ConsistentSubmodular

end


