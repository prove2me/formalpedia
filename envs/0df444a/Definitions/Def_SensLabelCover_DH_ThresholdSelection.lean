-- Prove2me | Definitions.Def_SensLabelCover_DH_ThresholdSelection
-- name    : SensLabelCover_DH_ThresholdSelection
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T16:34:38.820281+00:00
-- url     : https://prove2.me/theorems/51465bd3-4482-47fe-bfe8-06fabec4fbd2
-- title:
--   Random-threshold selection: the first score meeting a uniform threshold
-- statement:
--   Let $J\subseteq[0,1]$ be an interval of length $w>0$. For scores $q_1,\dots,q_R\in[0,1]$ and a threshold $\theta\in J$, **random-threshold selection** returns the smallest index $i$ with $q_i\ge\theta$, or the default index $0$ if no score meets the threshold. The threshold is uniform on $J$, so an event $S$ of thresholds has probability $\mathrm{vol}(S\cap J)/w$. For two score lists $q,\tilde q$,
--   $$A=\{i\in[R]: [\min\{q_i,\tilde q_i\},\max\{q_i,\tilde q_i\}]\cap J\neq\emptyset\}.$$
--
--   This is the selection rule the paper's recovery procedures use to choose among candidate outputs stably.
--
--   **Formalization Note** Scores are `q : Fin R → ℝ` (0-based); `select q θ : Option (Fin R)` returns `some i` for the selected index and `none` for the default index $0$. `thresholdProb J w S = vol(S ∩ J)/w` (Lebesgue measure). `crossingSet J q q'` is the set $A$.
-- source:
--   Fleming, Hopkins, Yoshida, Sensitivity and Locality Lower Bounds via Low-Soundness Label Cover, STOC 2027 submission (manuscript sha256 5bfe95ad…), p. 21 (PDF 24), Stable Selection and Lemma 3.5

import Mathlib

open scoped BigOperators

namespace SensLabelCover.DH

/-! Fleming, Hopkins, Yoshida, *Sensitivity and Locality Lower Bounds via Low-Soundness Label
Cover*, STOC 2027 submission (manuscript sha256 5bfe95ad…), §3, "Stable Selection" (p. 21,
PDF p. 24): random-threshold selection.

Scores `q_1, …, q_R` are `q : Fin R → ℝ` (index `i ∈ [R]` is `i : Fin R`, 0-based); the default
index `0` is `none : Option (Fin R)`, and index `i ≥ 1` is `some i`. The threshold `θ` is
uniform on an interval `J ⊆ [0, 1]` of length `w > 0`, so `Pr[θ ∈ S] = vol(S ∩ J)/w`. -/

noncomputable section

open MeasureTheory

open Classical in
/-- Random-threshold selection: for a threshold `θ`, the smallest index `i` with `q_i ≥ θ`, or the
default index (`none`) if no score meets the threshold. -/
def select {R : ℕ} (q : Fin R → ℝ) (θ : ℝ) : Option (Fin R) :=
  if h : ∃ i, θ ≤ q i then
    some (Finset.min' (Finset.univ.filter (fun i => θ ≤ q i)) (by
      obtain ⟨i, hi⟩ := h
      exact ⟨i, by simp [hi]⟩))
  else
    none

/-- Probability of an event `S ⊆ ℝ` for a threshold `θ` uniform on `J` of length `w`:
`vol(S ∩ J)/w`. -/
def thresholdProb (J : Set ℝ) (w : ℝ) (S : Set ℝ) : ℝ :=
  (volume (S ∩ J)).toReal / w

open Classical in
/-- The set `A = {i ∈ [R] : [min{q_i, q̃_i}, max{q_i, q̃_i}] ∩ J ≠ ∅}` of Lemma 3.5. -/
def crossingSet {R : ℕ} (J : Set ℝ) (q q' : Fin R → ℝ) : Finset (Fin R) :=
  Finset.univ.filter (fun i => (Set.Icc (min (q i) (q' i)) (max (q i) (q' i)) ∩ J).Nonempty)

end

end SensLabelCover.DH


