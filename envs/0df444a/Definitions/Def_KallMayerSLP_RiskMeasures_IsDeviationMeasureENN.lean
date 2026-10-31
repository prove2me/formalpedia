-- Prove2me | Definitions.Def_KallMayerSLP_RiskMeasures_IsDeviationMeasureENN
-- name    : KallMayerSLP_RiskMeasures_IsDeviationMeasureENN
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:40:05.346422+00:00
-- url     : https://prove2.me/theorems/15322a49-79e2-4491-a81f-ed94255826f1
-- title:
--   Deviation measure with values in $[0,\infty]$
-- statement:
--   The axioms (7.4) of a deviation measure, for a functional $\rho:\Upsilon\to[0,\infty]$ on a linear space $\Upsilon$ of real random variables on a probability space $(\Omega,\mathcal F,P)$: for all $\vartheta,\vartheta_1,\vartheta_2\in\Upsilon$ and all real $\lambda\ge0$, $C$,
--
--   1. (D1) $\rho(\vartheta_1+\vartheta_2)\le\rho(\vartheta_1)+\rho(\vartheta_2)$;
--   2. (D2) $\rho(\lambda\vartheta)=\lambda\rho(\vartheta)$, with $0\cdot\infty=0$;
--   3. (D3) $\rho(\vartheta)>0$ if $\vartheta$ is not constant, $\rho(\vartheta)=0$ otherwise;
--   4. (D4) $\rho(\vartheta+C)=\rho(\vartheta)$.
--
--   This is the form needed for the upper and lower standard semideviations on $\mathcal L^1_1$, the domain printed in Proposition 7.6 (K), where they can be $+\infty$. For a finite-valued functional the axioms are exactly those of a deviation measure.
--
--   **Formalization Note** "Constant" means almost surely constant: $\vartheta=C$ $P$-a.s. for some real $C$. All deviation measures of the book are expectations, which do not distinguish almost surely equal random variables, so under the pointwise reading (D3) would fail for them.
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 2, §7.1, (7.4), p.183 (PDF 193), applied to Proposition 7.6 (K), p.188 (PDF 198)

import Mathlib

open MeasureTheory
open scoped ENNReal

namespace KallMayerSLP.RiskMeasures

/-- **Deviation measure with values in `[0, ∞]`** (axioms (7.4) for an extended-valued `ρ`).
Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 2, §7.1, (7.4), p.183 (PDF 193), read for a functional `ρ : Υ → [0, ∞]`:

* (D1) `ρ(ϑ₁ + ϑ₂) ≤ ρ(ϑ₁) + ρ(ϑ₂)`;
* (D2) `ρ(λϑ) = λρ(ϑ)` for real `λ ≥ 0` (with `0 · ∞ = 0`);
* (D3) `ρ(ϑ) > 0` for `ϑ` non-constant, `ρ(ϑ) = 0` otherwise;
* (D4) `ρ(ϑ + C) = ρ(ϑ)` for `C ∈ ℝ`.

This is the form in which Prop. 7.6 (K) holds on the printed domain `𝓛¹₁`, where the upper and
lower semideviations `σ^±` can be `+∞` (a heavy tail). On `𝓛²₁` they are finite and the
axioms are those of `IsDeviationMeasure`.

**Formalization Note.** `Υ` is a submodule of the functions `Ω → ℝ`; only the values of `ρ`
on `Υ` matter. "`ϑ` constant" is read as *almost surely constant* (`ϑ = C` `P`-a.s. for some
real `C`): every deviation measure of the book is an expectation, which cannot distinguish a
random variable from an almost surely equal one, so the pointwise reading would make
Prop. 7.6 false. Positive homogeneity is for `λ ≥ 0`, shift invariance for every real `C`. -/
def IsDeviationMeasureENN {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Υ : Submodule ℝ (Ω → ℝ)) (ρ : (Ω → ℝ) → ℝ≥0∞) : Prop :=
  (∀ ϑ₁ ∈ Υ, ∀ ϑ₂ ∈ Υ, ρ (ϑ₁ + ϑ₂) ≤ ρ ϑ₁ + ρ ϑ₂) ∧
  (∀ ϑ ∈ Υ, ∀ c : ℝ, 0 ≤ c → ρ (c • ϑ) = ENNReal.ofReal c * ρ ϑ) ∧
  (∀ ϑ ∈ Υ, (¬ ∃ C : ℝ, ϑ =ᵐ[P] fun _ => C) → 0 < ρ ϑ) ∧
  (∀ ϑ ∈ Υ, (∃ C : ℝ, ϑ =ᵐ[P] fun _ => C) → ρ ϑ = 0) ∧
  (∀ ϑ ∈ Υ, ∀ C : ℝ, ρ (ϑ + fun _ => C) = ρ ϑ)

end KallMayerSLP.RiskMeasures


