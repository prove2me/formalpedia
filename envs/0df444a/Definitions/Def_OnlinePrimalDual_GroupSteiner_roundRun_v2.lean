-- Prove2me | Definitions.Def_OnlinePrimalDual_GroupSteiner_roundRun_v2
-- name    : OnlinePrimalDual_GroupSteiner_roundRun_v2
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-10-06T05:18:27.29808+00:00
-- url     : https://prove2.me/theorems/6df2626f-af49-473e-adfc-9ae4b983f97e
-- title:
--   The online rounding algorithm's random cover (Section 11.2), as a probability distribution computed from the data
-- statement:
--   `coinProb tr w w' δ e C` is the probability with which the rounding algorithm adds edge $e$ to the current cover $C$ in an iteration augmenting the weights from $w$ to $w' = w+\delta$: only edges with $\delta_e > 0$ are processed; if $w'_e > 1$, $e$ is added deterministically; otherwise, if $e$ is incident to the root or $w'_{e(p)} > 1$, with probability $\delta_e/(1-w_e)$; otherwise, if the parent edge $e(p)\in C$, with probability $\delta_e/(w'_{e(p)} - w_e)$, and never while the parent is absent. `coinProbClamped` clips it to $[0,1]$ (inert under the section's standing assumptions). `edgeStep` is the resulting transition of the cover distribution for one edge, `iterStep` one iteration (edges processed in the topological order `ord`), `fracWeight δs` the cumulative weight $\sum_{\delta\in\delta s}\delta_e$, `roundPMF` the distribution after the iterations `δs` starting from the empty cover, and `roundCover tr ord δs : RandomCover E` the same distribution packaged with its (proved) non-negativity and normalization.
-- source:
--   Buchbinder & Naor, The Design of Competitive Online Algorithms via a Primal-Dual Approach, FnT TCS 4(2-3), 2009, p. 229-230, Section 11.2 (rounding box)

import Mathlib
import Definitions.Def_OnlinePrimalDual_GroupSteiner_RandomCover
import Definitions.Def_OnlinePrimalDual_GroupSteiner_RoundedTree

namespace OnlinePrimalDual.GroupSteiner

/-- The probability with which the online rounding algorithm of Buchbinder & Naor, *The Design of
Competitive Online Algorithms via a Primal-Dual Approach*, FnT TCS 2009, Section 11.2 (rounding
box, p. 229-230) adds edge `e` to the current random cover `C` during an iteration in which the
fractional weights are augmented from `w` to `w' = w + δ` — the book's three bullets, read off
the current realisation `C` of the cover: only edges whose weight increased (`δ e > 0`) are
processed; if `w'ₑ > 1`, `e` is added deterministically; otherwise, if `e` is incident to the
root or its parent edge `e(p)` has `w'_{e(p)} > 1` (so the parent is certainly in `C`), `e` is
added with probability `δₑ/(1 − wₑ)`; otherwise `e` is added, provided its parent edge is in `C`,
with probability `δₑ/(w'_{e(p)} − wₑ)` (and is never added while its parent is absent). Under the
section's standing assumptions (weights non-decreasing in time, and `wₑ ≤ w_{e(p)}` along every
root path — the fractional solution is a flow from the root) every value here lies in `[0, 1]`. -/
noncomputable def coinProb {E : Type*} [Fintype E] [DecidableEq E] (tr : RoundedTree E)
    (w w' δ : E → ℝ) (e : E) (C : Finset E) : ℝ :=
  if δ e ≤ 0 then 0
  else if 1 < w' e then 1
  else
    match tr.parent e with
    | none => δ e / (1 - w e)
    | some p => if 1 < w' p then δ e / (1 - w e) else if p ∈ C then δ e / (w' p - w e) else 0

/-- `coinProb` clipped to `[0, 1]`, so that the transition below is always a probability
kernel. The clipping is inert under the standing assumptions listed at `coinProb`. -/
noncomputable def coinProbClamped {E : Type*} [Fintype E] [DecidableEq E] (tr : RoundedTree E)
    (w w' δ : E → ℝ) (e : E) (C : Finset E) : ℝ :=
  max 0 (min 1 (coinProb tr w w' δ e C))

/-- The distribution of the random cover after the rounding algorithm processes edge `e`
(weights `w → w' = w + δ`), given the distribution `p` of the cover before: with probability
`coinProbClamped … e C` the cover `C` becomes `insert e C`, otherwise it stays `C`. -/
noncomputable def edgeStep {E : Type*} [Fintype E] [DecidableEq E] (tr : RoundedTree E)
    (w w' δ : E → ℝ) (e : E) (p : Finset E → ℝ) : Finset E → ℝ :=
  fun C' => ∑ C, p C *
    (coinProbClamped tr w w' δ e C * (if C' = insert e C then 1 else 0) +
      (1 - coinProbClamped tr w w' δ e C) * (if C' = C then 1 else 0))

/-- One iteration of the rounding algorithm (p. 229-230): the fractional weights are augmented
from `w` to `w + δ`, and the edges are processed one after the other in the fixed order `ord`
(a topological order of the tree from the root: every edge after its parent edge, as the book
prescribes), each by `edgeStep`. -/
noncomputable def iterStep {E : Type*} [Fintype E] [DecidableEq E] (tr : RoundedTree E)
    (ord : List E) (w δ : E → ℝ) (p : Finset E → ℝ) : Finset E → ℝ :=
  ord.foldl (fun q e => edgeStep tr w (w + δ) δ e q) p

/-- The fractional weight vector after the increments `δs` (one per iteration, in order) have
been applied, starting from `0`: `wₑ = ∑_{δ ∈ δs} δₑ`. -/
def fracWeight {E : Type*} (δs : List (E → ℝ)) : E → ℝ :=
  fun e => (δs.map fun δ => δ e).sum

/-- The probability mass function of the random cover produced by the online rounding algorithm
(Section 11.2) after the iterations with weight increments `δs`, processing edges in the order
`ord` in every iteration, starting from the empty cover (`C = ∅` with probability `1`) and the
zero fractional solution. -/
noncomputable def roundPMF {E : Type*} [Fintype E] [DecidableEq E] (tr : RoundedTree E)
    (ord : List E) (δs : List (E → ℝ)) : Finset E → ℝ :=
  (δs.foldl (fun (st : (E → ℝ) × (Finset E → ℝ)) δ => (st.1 + δ, iterStep tr ord st.1 δ st.2))
    (0, fun C => if C = ∅ then 1 else 0)).2

lemma coinProbClamped_nonneg {E : Type*} [Fintype E] [DecidableEq E] (tr : RoundedTree E)
    (w w' δ : E → ℝ) (e : E) (C : Finset E) : 0 ≤ coinProbClamped tr w w' δ e C :=
  le_max_left _ _

lemma coinProbClamped_le_one {E : Type*} [Fintype E] [DecidableEq E] (tr : RoundedTree E)
    (w w' δ : E → ℝ) (e : E) (C : Finset E) : coinProbClamped tr w w' δ e C ≤ 1 :=
  max_le (by norm_num) (min_le_left _ _)

lemma edgeStep_nonneg {E : Type*} [Fintype E] [DecidableEq E] (tr : RoundedTree E)
    (w w' δ : E → ℝ) (e : E) (p : Finset E → ℝ) (hp : ∀ C, 0 ≤ p C) (C' : Finset E) :
    0 ≤ edgeStep tr w w' δ e p C' := by
  unfold edgeStep
  apply Finset.sum_nonneg
  intro C _
  have hq0 := coinProbClamped_nonneg tr w w' δ e C
  have hq1 := coinProbClamped_le_one tr w w' δ e C
  apply mul_nonneg (hp C)
  apply add_nonneg
  · apply mul_nonneg hq0; split_ifs <;> norm_num
  · apply mul_nonneg (by linarith); split_ifs <;> norm_num

lemma edgeStep_sum {E : Type*} [Fintype E] [DecidableEq E] (tr : RoundedTree E)
    (w w' δ : E → ℝ) (e : E) (p : Finset E → ℝ) :
    ∑ C', edgeStep tr w w' δ e p C' = ∑ C, p C := by
  unfold edgeStep
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro C _
  rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

lemma iterStep_nonneg {E : Type*} [Fintype E] [DecidableEq E] (tr : RoundedTree E)
    (ord : List E) (w δ : E → ℝ) (p : Finset E → ℝ) (hp : ∀ C, 0 ≤ p C) :
    ∀ C, 0 ≤ iterStep tr ord w δ p C := by
  unfold iterStep
  induction ord generalizing p with
  | nil => simpa using hp
  | cons e rest ih =>
    simp only [List.foldl_cons]
    exact ih _ (edgeStep_nonneg tr w (w + δ) δ e p hp)

lemma iterStep_sum {E : Type*} [Fintype E] [DecidableEq E] (tr : RoundedTree E)
    (ord : List E) (w δ : E → ℝ) (p : Finset E → ℝ) :
    ∑ C, iterStep tr ord w δ p C = ∑ C, p C := by
  unfold iterStep
  induction ord generalizing p with
  | nil => simp
  | cons e rest ih =>
    simp only [List.foldl_cons]
    rw [ih, edgeStep_sum]

lemma roundPMF_nonneg {E : Type*} [Fintype E] [DecidableEq E] (tr : RoundedTree E)
    (ord : List E) (δs : List (E → ℝ)) : ∀ C, 0 ≤ roundPMF tr ord δs C := by
  unfold roundPMF
  suffices h : ∀ (st : (E → ℝ) × (Finset E → ℝ)), (∀ C, 0 ≤ st.2 C) →
      ∀ C, 0 ≤ (δs.foldl (fun (st : (E → ℝ) × (Finset E → ℝ)) δ =>
        (st.1 + δ, iterStep tr ord st.1 δ st.2)) st).2 C by
    apply h
    intro C
    dsimp only
    split_ifs <;> norm_num
  induction δs with
  | nil => intro st hst; simpa using hst
  | cons δ rest ih =>
    intro st hst
    simp only [List.foldl_cons]
    exact ih _ (iterStep_nonneg tr ord st.1 δ st.2 hst)

lemma roundPMF_sum {E : Type*} [Fintype E] [DecidableEq E] (tr : RoundedTree E)
    (ord : List E) (δs : List (E → ℝ)) : ∑ C, roundPMF tr ord δs C = 1 := by
  unfold roundPMF
  suffices h : ∀ (st : (E → ℝ) × (Finset E → ℝ)),
      ∑ C, (δs.foldl (fun (st : (E → ℝ) × (Finset E → ℝ)) δ =>
        (st.1 + δ, iterStep tr ord st.1 δ st.2)) st).2 C = ∑ C, st.2 C by
    rw [h]
    simp [Finset.sum_ite_eq']
  induction δs with
  | nil => intro st; simp
  | cons δ rest ih =>
    intro st
    simp only [List.foldl_cons]
    rw [ih, iterStep_sum]

/-- The random cover `C` produced by the online rounding algorithm of Section 11.2 (p. 229-230)
after the iterations with weight increments `δs`, processing edges in the order `ord` in every
iteration, as a `RandomCover` (a probability distribution over edge subsets): the algorithm's
own output, computed from the tree, the processing order and the sequence of fractional
solutions. -/
noncomputable def roundCover {E : Type*} [Fintype E] [DecidableEq E] (tr : RoundedTree E)
    (ord : List E) (δs : List (E → ℝ)) : RandomCover E where
  p := roundPMF tr ord δs
  hp_nonneg := roundPMF_nonneg tr ord δs
  hp_sum := roundPMF_sum tr ord δs

end OnlinePrimalDual.GroupSteiner


