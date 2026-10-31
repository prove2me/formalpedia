-- Prove2me | Definitions.Def_KallMayerSLP_RiskMeasures_IsCoherentRiskMeasure
-- name    : KallMayerSLP_RiskMeasures_IsCoherentRiskMeasure
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:41:00.910529+00:00
-- url     : https://prove2.me/theorems/c5023fe3-084a-44ec-920c-9e4476bf2daf
-- title:
--   Coherent risk measure, axioms (7.2)
-- statement:
--   Let $(\Omega,\mathcal F,P)$ be a probability space and $\Upsilon$ a linear space of real random variables on it, interpreted as losses. A function $\rho:\Upsilon\to\mathbb R$ is a **coherent risk measure** if for all $\vartheta,\vartheta_1,\vartheta_2\in\Upsilon$ and all real $\lambda\ge0$, $C$:
--
--   1. (A1) $\rho(\vartheta_1+\vartheta_2)\le\rho(\vartheta_1)+\rho(\vartheta_2)$ (subadditivity);
--   2. (A2) $\rho(\lambda\vartheta)=\lambda\rho(\vartheta)$ (positive homogeneity);
--   3. (A3) if $\vartheta_1\le\vartheta_2$ then $\rho(\vartheta_1)\le\rho(\vartheta_2)$ (monotonicity);
--   4. (A4) $\rho(\vartheta+C)=\rho(\vartheta)+C$ (translation invariance).
--
--   These are the axioms of Artzner, Delbaen, Eber and Heath, written for losses rather than future values.
--
--   **Formalization Note** $\Upsilon$ is a submodule of the functions $\Omega\to\mathbb R$ and $\rho$ a function on all functions, of which only the values on $\Upsilon$ matter. The hypothesis $\vartheta_1\le\vartheta_2$ in (A3) is taken $P$-almost surely, which is weaker than the pointwise order; the predicate therefore implies the one with the pointwise order.
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 2, §7.1, (7.2), p.183 (PDF 193)

import Mathlib
import Definitions.Def_KallMayerSLP_RiskMeasures_IsPosHomogeneous
import Definitions.Def_KallMayerSLP_RiskMeasures_IsSubadditive

open MeasureTheory
open scoped ENNReal

namespace KallMayerSLP.RiskMeasures

/-- **Coherent risk measure** (Artzner–Delbaen–Eber–Heath axioms (7.2), loss convention).
Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 2, §7.1, (7.2) and (7.3), p.183 (PDF 193). The axioms are required "for any
`ϑ, ϑ₁, ϑ₂ ∈ Υ` and `λ, C ∈ ℝ, λ ≥ 0`", for a function `ρ : Υ → ℝ` on a linear space `Υ` of
random variables on a probability space `(Ω, 𝓕, P)`, representing losses.

* (A1) `ρ(ϑ₁ + ϑ₂) ≤ ρ(ϑ₁) + ρ(ϑ₂)` (subadditivity);
* (A2) `ρ(λϑ) = λρ(ϑ)` for `λ ≥ 0` (positive homogeneity);
* (A3) if `ϑ₁ ≤ ϑ₂` then `ρ(ϑ₁) ≤ ρ(ϑ₂)` (monotonicity);
* (A4) `ρ(ϑ + C) = ρ(ϑ) + C` for `C ∈ ℝ` (translation invariance).

**Formalization Note.** `Υ` is a submodule of the functions `Ω → ℝ` and `ρ` is a function on
all of `Ω → ℝ` of which only the values on `Υ` matter. The hypothesis `ϑ₁ ≤ ϑ₂` of monotonicity is
taken almost surely (`ϑ₁ ≤ ϑ₂` `P`-a.s.); this is weaker than the pointwise hypothesis used in the
book's proof of Prop. 7.3 (B) ("`ϑ₁(ω) ≤ ϑ₂(ω)` for all `ω`"), so the predicate implies the
pointwise one. `ϑ + C` adds the constant random variable `C`. -/
def IsCoherentRiskMeasure {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (Υ : Submodule ℝ (Ω → ℝ)) (ρ : (Ω → ℝ) → ℝ) : Prop :=
  IsSubadditive (fun ϑ : Υ => ρ ϑ) ∧
  IsPosHomogeneous (fun ϑ : Υ => ρ ϑ) ∧
  (∀ ϑ₁ ∈ Υ, ∀ ϑ₂ ∈ Υ, ϑ₁ ≤ᵐ[P] ϑ₂ → ρ ϑ₁ ≤ ρ ϑ₂) ∧
  (∀ ϑ ∈ Υ, ∀ C : ℝ, ρ (ϑ + fun _ => C) = ρ ϑ + C)

end KallMayerSLP.RiskMeasures


