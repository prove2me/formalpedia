-- Prove2me | Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_SchedulingBasics
-- name    : ConsistentSubmodular_Deterministic_Reduction_SchedulingBasics
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:07:53.638007+00:00
-- url     : https://prove2.me/theorems/16cba111-319a-422e-bc7a-f482efb0d549
-- title:
--   Scheduling basics: triangle inequality for recourse, union bound, rolling buffer
-- statement:
--   Recourse of two sets $A,B$ of stream elements is $|A \triangle B|$ (`recourse`), and $X_t=\{x_1,\dots,x_t\}$ is the arrived prefix (`arrivedPrefix`).
--
--   - `ConsistentSubmodular.rollingBuffer` $(n, w, t)$: the set of the most recent $w$ arrivals,
--   $$X_t \setminus X_{t-w} = \{e : t - w \le e < t\},$$
--   where $t-w$ is truncated subtraction on $\mathbb{N}$ (so the buffer is all of $X_t$ when $t \le w$).
--
--   The file also proves elementary facts used throughout the scheduling arguments: recourse satisfies the triangle inequality $|A \triangle C| \le |A\triangle B| + |B \triangle C|$; recourse of unions is subadditive, $|(A\cup R)\triangle(B\cup T)| \le |A\triangle B| + |R \triangle T|$, so overlap between a physical core and a buffer never increases recourse; membership in the arrived prefix is $e<t$; and the buffered optimum is monotone in the ground set.
--
--   These facts and the rolling buffer belong to the reduction from consistency to clairvoyant certificates in Section 3.2: they allow recourse of the core and of the buffer to be counted separately.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Reduction/SchedulingBasics.lean (definitions and supporting lemmas of this module, ported from Lean v4.30.0-rc1 to Lean v4.33.1)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Basic_Model

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular

variable {n : ℕ}

theorem recourse_triangle (A B C : Finset (Fin n)) :
    recourse A C ≤ recourse A B + recourse B C := by
  have hsub : (A \ C) ∪ (C \ A) ⊆
      ((A \ B) ∪ (B \ A)) ∪ ((B \ C) ∪ (C \ B)) := by
    intro e he
    simp only [Finset.mem_union, Finset.mem_sdiff] at *
    tauto
  exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)

/-- Overlap between a physical core and a buffer does not increase recourse. -/
theorem recourse_union_le (A B R T : Finset (Fin n)) :
    recourse (A ∪ R) (B ∪ T) ≤ recourse A B + recourse R T := by
  have hsub : ((A ∪ R) \ (B ∪ T)) ∪ ((B ∪ T) \ (A ∪ R)) ⊆
      ((A \ B) ∪ (B \ A)) ∪ ((R \ T) ∪ (T \ R)) := by
    intro e he
    simp only [Finset.mem_union, Finset.mem_sdiff] at *
    tauto
  exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)

@[simp] theorem mem_arrivedPrefix (e : Fin n) (t : ℕ) :
    e ∈ arrivedPrefix n t ↔ e.val < t := by simp [arrivedPrefix]

def rollingBuffer (n width t : ℕ) : Finset (Fin n) :=
  arrivedPrefix n t \ arrivedPrefix n (t - width)

namespace Objective

variable (f : Objective n)

theorem bufferedOptimum_mono_ground {N M Q : Finset (Fin n)} {k : ℕ}
    (hNM : N ⊆ M) : f.bufferedOptimum N Q k ≤ f.bufferedOptimum M Q k := by
  have hA := f.bufferedOptimizer_spec N Q k
  exact f.le_bufferedOptimum (hA.1.trans hNM) hA.2.1

end Objective

end ConsistentSubmodular

end


