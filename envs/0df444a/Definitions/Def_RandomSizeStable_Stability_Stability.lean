-- Prove2me | Definitions.Def_RandomSizeStable_Stability_Stability
-- name    : RandomSizeStable_Stability_Stability
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:52:05.832196+00:00
-- url     : https://prove2.me/theorems/2435ca6e-9735-4269-94c1-d2af5665b29f
-- title:
--   Exact and approximate random-size stability
-- statement:
--   For finite nonempty voter and candidate sets, let $E$ be their strict-ranking profile, $D$ a positive-integer draw law, and $P$ a lottery. Average the operational singleton comparison probability uniformly over voters:
--   $$L_c(P)=\frac1{|V|}\sum_{v\in V}L_{v,c}(P).$$
--   The lottery is random-size stable for $D$ if
--   $$\forall c\in C,\quad L_c(P)\le\mu_D.$$
--   Its approximate version replaces the right side by $\mu_D+\delta$. Both predicates explicitly require nonnegative masses summing to one; applications of approximate stability also require $\delta\ge0$.
--
--   These predicates express the source's comparisons directly. They impose no minimization property, auxiliary score-function restrictions, metric condition, or numerical certificate. They are the common interfaces for existence and distortion statements.
-- source:
--   Nisarg Shah, Draw, Then Draw: The Metric Distortion of Random-Size Stable Lotteries, STOC 2027 submission #1342 (October 2026), p. 10, 13, Definition 3, Equation (3.1); Lemma 5.

import Mathlib
import Definitions.Def_RandomSizeStable_Stability_Comparison
import Definitions.Def_StableVotingDistortion_voterMean

set_option autoImplicit false

open MeasureTheory PctDistortion StableVotingDistortion

namespace RandomSizeStable.Stability

/-- Equation (3.1), p.10: the uniform-voter comparison score of a challenger. -/
noncomputable def score {V C : Type} [Fintype V] [Fintype C] (D : PMF ℕ+)
    (E : Election V C) (P : C → ℝ) (c : C) : ℝ :=
  voterMean (fun v => comparison D E P v c)

/-- Definition 3, p.10: an actual lottery satisfying all explicit comparisons.
No minimizer, score-function restriction or certificate is assumed. -/
def IsStable {V C : Type} [Fintype V] [Fintype C] (D : PMF ℕ+)
    (E : Election V C) (P : C → ℝ) : Prop :=
  P ∈ stdSimplex ℝ C ∧ ∀ c, score D E P c ≤ benchmark D

/-- Lemma 5, p.13: the approximate version, with additive comparison error δ. -/
def IsApproximatelyStable {V C : Type} [Fintype V] [Fintype C] (D : PMF ℕ+)
    (E : Election V C) (P : C → ℝ) (δ : ℝ) : Prop :=
  P ∈ stdSimplex ℝ C ∧ ∀ c, score D E P c ≤ benchmark D + δ

end RandomSizeStable.Stability


