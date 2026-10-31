-- Prove2me | Definitions.Def_KallMayerSLP_RiskMeasures_IsDeviationMeasure
-- name    : KallMayerSLP_RiskMeasures_IsDeviationMeasure
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:41:02.196903+00:00
-- url     : https://prove2.me/theorems/6a5aa2d9-da93-4f64-be0b-74a41f0f741a
-- title:
--   Deviation measure, axioms (7.4)
-- statement:
--   Let $(\Omega,\mathcal F,P)$ be a probability space and $\Upsilon$ a linear space of real random variables on it. A function $\rho:\Upsilon\to\mathbb R$ is a **deviation measure** (Rockafellar, Uryasev and Zabarankin) if for all $\vartheta,\vartheta_1,\vartheta_2\in\Upsilon$ and all real $\lambda\ge0$, $C$:
--
--   1. (D1) $\rho(\vartheta_1+\vartheta_2)\le\rho(\vartheta_1)+\rho(\vartheta_2)$ (subadditivity);
--   2. (D2) $\rho(\lambda\vartheta)=\lambda\rho(\vartheta)$ (positive homogeneity);
--   3. (D3) $\rho(\vartheta)>0$ if $\vartheta$ is not constant, and $\rho(\vartheta)=0$ otherwise (nonnegativity);
--   4. (D4) $\rho(\vartheta+C)=\rho(\vartheta)$ (shift invariance).
--
--   **Formalization Note** "Constant" means almost surely constant: $\vartheta=C$ $P$-a.s. for some real $C$. All deviation measures of the book are expectations, which do not distinguish almost surely equal random variables, so under the pointwise reading (D3) would fail for them.
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 2, §7.1, (7.4), p.183 (PDF 193)

import Mathlib
import Definitions.Def_KallMayerSLP_RiskMeasures_IsPosHomogeneous
import Definitions.Def_KallMayerSLP_RiskMeasures_IsSubadditive

open MeasureTheory
open scoped ENNReal

namespace KallMayerSLP.RiskMeasures

/-- **Deviation measure** (Rockafellar–Uryasev–Zabarankin axioms (7.4)).
Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 2, §7.1, (7.4), p.183 (PDF 193), for `ρ : Υ → ℝ` on a linear space `Υ` of random variables
on `(Ω, 𝓕, P)`:

* (D1) `ρ(ϑ₁ + ϑ₂) ≤ ρ(ϑ₁) + ρ(ϑ₂)` (subadditivity);
* (D2) `ρ(λϑ) = λρ(ϑ)` for `λ ≥ 0` (positive homogeneity);
* (D3) `ρ(ϑ) > 0` for `ϑ` non-constant, `ρ(ϑ) = 0` otherwise (nonnegativity);
* (D4) `ρ(ϑ + C) = ρ(ϑ)` for `C ∈ ℝ` (shift invariance).

**Formalization Note.** `Υ` is a submodule of the functions `Ω → ℝ`; only the values of `ρ`
on `Υ` matter. "`ϑ` constant" is read as *almost surely constant* (`ϑ = C` `P`-a.s. for some
real `C`): every deviation measure of the book is an expectation, which cannot distinguish a
random variable from an almost surely equal one, so the pointwise reading would make
Prop. 7.6 false. Positive homogeneity is for `λ ≥ 0`, shift invariance for every real `C`. -/
def IsDeviationMeasure {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Υ : Submodule ℝ (Ω → ℝ)) (ρ : (Ω → ℝ) → ℝ) : Prop :=
  IsSubadditive (fun ϑ : Υ => ρ ϑ) ∧
  IsPosHomogeneous (fun ϑ : Υ => ρ ϑ) ∧
  (∀ ϑ ∈ Υ, (¬ ∃ C : ℝ, ϑ =ᵐ[P] fun _ => C) → 0 < ρ ϑ) ∧
  (∀ ϑ ∈ Υ, (∃ C : ℝ, ϑ =ᵐ[P] fun _ => C) → ρ ϑ = 0) ∧
  (∀ ϑ ∈ Υ, ∀ C : ℝ, ρ (ϑ + fun _ => C) = ρ ϑ)

end KallMayerSLP.RiskMeasures


