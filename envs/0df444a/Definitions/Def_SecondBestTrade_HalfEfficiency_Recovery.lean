-- Prove2me | Definitions.Def_SecondBestTrade_HalfEfficiency_Recovery
-- name    : SecondBestTrade_HalfEfficiency_Recovery
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:06:01.32917+00:00
-- url     : https://prove2.me/theorems/74806872-d9ac-4668-85fb-d4c284b6f87a
-- title:
--   Lemma 5.4 — Finite-state recovery interface
-- statement:
--   For a finite-state matrix $Q$ and true and virtual coordinate matrices $V,\widetilde V$, `recoveryProperties` collects the full recovery assertion:
--   $$R=(I-Q)^{-1}=\int_0^\infty e^{-\theta}e^{\theta Q}\,d\theta,\qquad R\widetilde V=V.$$
--   It includes invertibility, entrywise convergence, stochastic rows, the continuous semigroup law, existence of a probability-space process with the stated finite-dimensional transition laws from each initial state, and the exponential-stop distribution and expected-coordinate identities. The process predicate is the published `LambdaCoalescent.Rates.IsRateChain`; no coalescent-specific assumption enters it. The finite state space has the discrete measurable structure.
--
--   This is an assertion interface, not an axiom: Lemma 5.4 must prove it for the explicitly constructed market generators. Exponential stopping is represented entrywise by integration against its rate-one density $e^{-\theta}$ on $(0,\infty)$. All scalar integrals used for recovery are asserted integrable as part of the conclusion, so their default values cannot supply recovery.
-- source:
--   Dirk Bergemann, Yang Cai, Kangning Wang, Jinzhao Wu, Renzhe Xu, STOC 2027 submission #529 (October 2026), §5.2, Lemma 5.4, (5.8)–(5.10), printed pp. 9–10 (PDF pp. 10–11); Appendix A.3, printed p. 26 (PDF p. 27)

import Mathlib
import Definitions.Def_SecondBestTrade_HalfEfficiency_Dual
import Definitions.Def_LambdaCoalescent_Rates_FiniteChain

open scoped BigOperators NNReal
open MeasureTheory
set_option autoImplicit false
noncomputable section

namespace SecondBestTrade.HalfEfficiency

/-- Transition and exponential-stop meaning, stated for a finite-state generator.
The process predicate is reused from the finite-chain library, without coalescent assumptions. -/
def recoveryProperties {S E : Type} [Fintype S] [DecidableEq S] [Fintype E]
    (Q : Matrix S S ℝ) (V Vtilde : S → E → ℝ) : Prop :=
  letI : MeasurableSpace S := ⊤
  IsUnit (1 - Q) ∧
  (∀ t s, IntegrableOn (fun theta : ℝ => Real.exp (-theta) *
    NormedSpace.exp (theta • Q) t s) (Set.Ioi 0)) ∧
  (∀ t s, (1 - Q)⁻¹ t s = ∫ theta in Set.Ioi (0 : ℝ),
    Real.exp (-theta) * NormedSpace.exp (theta • Q) t s) ∧
  (∀ theta, 0 ≤ theta → (∀ t s, 0 ≤ NormedSpace.exp (theta • Q) t s) ∧
    ∀ t, ∑ s, NormedSpace.exp (theta • Q) t s = 1) ∧
  NormedSpace.exp ((0 : ℝ) • Q) = 1 ∧
  (∀ theta eta, 0 ≤ theta → 0 ≤ eta →
    NormedSpace.exp ((theta + eta) • Q) =
      NormedSpace.exp (theta • Q) * NormedSpace.exp (eta • Q)) ∧
  Continuous (fun theta : ℝ => NormedSpace.exp (theta • Q)) ∧
  (∀ t : S, ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω)
    (X : ℝ≥0 → Ω → S), IsProbabilityMeasure P ∧
      LambdaCoalescent.Rates.IsRateChain P Q t X) ∧
  (∀ t s, 0 ≤ (1 - Q)⁻¹ t s) ∧ (∀ t, ∑ s, (1 - Q)⁻¹ t s = 1) ∧
  (∀ t e, ∑ s, (1 - Q)⁻¹ t s * Vtilde s e = V t e) ∧
  (∀ t e, IntegrableOn (fun theta : ℝ => Real.exp (-theta) *
    ∑ s, NormedSpace.exp (theta • Q) t s * Vtilde s e) (Set.Ioi 0)) ∧
  (∀ t e, (∫ theta in Set.Ioi (0 : ℝ), Real.exp (-theta) *
    ∑ s, NormedSpace.exp (theta • Q) t s * Vtilde s e) = V t e)

end SecondBestTrade.HalfEfficiency


