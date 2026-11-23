-- Prove2me | Definitions.Def_WeightedMajority_Shifting_Supplement_StrongIndependence
-- name    : WeightedMajority_Shifting_Supplement_StrongIndependence
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T12:54:35.526245+00:00
-- url     : https://prove2.me/theorems/520b8763-391f-49b0-b0bc-33f2f2c62d85
-- title:
--   Strong independence conditioned on the entire external sequence
-- statement:
--   Let $P$ be a probability measure. For a finite run of $t$ trials, let $x^j$ be the vector of pool predictions, $\rho^j$ the label and $\lambda^j$ the master's prediction. Let $\gamma^j$ be the published WMR weighted average. Write $G=\sigma((x^0,\rho^0),\ldots,(x^{t-1},\rho^{t-1}))$ and $H_j=G\vee\sigma(\lambda^0,\ldots,\lambda^{j-1})$. Strong independence means
--
--   $$P[\lambda^j\mid H_j]=\gamma^j\quad\text{almost surely for every }j<t.$$
--
--   The external-data and past-prediction algebras are constructed from these variables, including future external data. This extends the published WMR model with precisely the strong condition used by the conditional tail theorem and established by the lazy implementation. Trial indices start at zero.
-- source:
--   Littlestone, Warmuth, The Weighted Majority Algorithm, Inform. and Comput. 108 (1994), DOI 10.1006/inco.1994.1009, p. 238, strong independence condition

import Definitions.Def_WeightedMajority_Randomized_WMRModel

open MeasureTheory

namespace WeightedMajority.Shifting.Supplement

/-- The entire external prediction/label sequence, including trials after the current one.
The paper's positive trial indices are shifted down by one. -/
@[reducible] def external {Ω : Type*} {n : ℕ} (t : ℕ) (x : ℕ → Fin n → Ω → ℝ)
    (ρ : ℕ → Ω → ℝ) : MeasurableSpace Ω :=
  MeasurableSpace.comap
    (fun ω => fun j : Fin t => ((fun i => x j.val i ω), ρ j.val ω)) inferInstance

/-- Only master predictions strictly before trial `j`. -/
@[reducible] def pastPredictions {Ω : Type*} (j : ℕ) (lam : ℕ → Ω → ℝ) : MeasurableSpace Ω :=
  MeasurableSpace.comap (fun ω => fun k : Fin j => lam k.val ω) inferInstance

/-- The strong independence condition, p. 238: condition on all external data and all
strictly earlier master predictions. This predicate asserts no tail bound. -/
def StrongIndependence {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {n : ℕ}
    (t : ℕ) (w1 : Fin n → ℝ) (F : ℕ → Fin n → ℝ → ℝ → ℝ)
    (x : ℕ → Fin n → Ω → ℝ) (ρ lam : ℕ → Ω → ℝ) : Prop :=
  ∀ j < t, P[lam j | external t x ρ ⊔ pastPredictions j lam]
    =ᵐ[P] WeightedMajority.Randomized.gamma w1 F x ρ j

end WeightedMajority.Shifting.Supplement


