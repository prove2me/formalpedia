-- Prove2me | Definitions.Def_TightQLB_Supplement_Entropy
-- name    : TightQLB_Supplement_Entropy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:23:07.60743+00:00
-- url     : https://prove2.me/theorems/b6799313-a79c-4bc8-b31c-60d6137a818d
-- title:
--   Families of positive operators, $p_{\mathrm{guess}}$, $H_{\min}$, fidelity, purified distance and smooth min-entropy (Definition 3.4)
-- statement:
--   A **family of positive operators** is a map $\omega\mapsto(\tau^\omega_z)_z$ from oracles to tuples of positive semidefinite operators on Eve's space $E$, measurable with respect to the law of the oracle; it is **normalized** if $\mathbb E_\omega\sum_z\operatorname{Tr}\tau^\omega_z=1$. For normalized families $\rho,\tau$:
--
--   $$
--   p_{\mathrm{guess}}(Z\mid RE)_\tau=\mathbb E_\omega\sup_M\sum_z\operatorname{Tr}(M_z\tau^\omega_z),\qquad H_{\min}(Z\mid RE)_\tau=-\log p_{\mathrm{guess}}(Z\mid RE)_\tau,
--   $$
--
--   $$
--   F(\rho,\tau)=\mathbb E_\omega\sum_z\big\|\sqrt{\rho^\omega_z}\sqrt{\tau^\omega_z}\big\|_1,\qquad P(\rho,\tau)=\sqrt{1-F(\rho,\tau)^2},
--   $$
--
--   the supremum over measurements $M=(M_z)_z$ on $E$ and $\|T\|_1=\operatorname{Tr}\sqrt{T^\dagger T}$. For $0\le\eta\le1$ the **smooth min-entropy** is
--
--   $$
--   H^\eta_{\min}(Z\mid RE)_\rho=\sup\{H_{\min}(Z\mid RE)_\tau:\ \tau\text{ normalized},\ P(\rho,\tau)\le\eta\}.
--   $$
--
--   Logarithms are to base 2. Eve's knowledge of the oracle (the register $R$) enters through the measurement chosen for each $\omega$. These quantities state the randomness guarantees, Theorems 7.2 and 7.9.
--
--   **Formalization Note** The oracle ranges over a measurable space with a probability law; measurability is entrywise; normalization includes integrability. Square roots of positive semidefinite matrices are the continuous functional calculus `CFC.sqrt`. The suprema are real suprema of bounded nonempty sets.
-- source:
--   Bhateja, Esmaili, Mantri, Tight Query Lower Bounds for Quantum Sampling, with an Application to Certified Randomness, arXiv:2610.06721 (version of sha256 00a999f1…), §3.4, Definition 3.4, p. 18 (PDF p. 21)

import Mathlib
open MeasureTheory
open scoped Matrix MatrixOrder ComplexOrder

set_option autoImplicit false

namespace TightQLB.Supplement

/-!
# Families of positive operators, guessing probability, fidelity, purified distance, smooth
min-entropy (Definition 3.4)

Bhateja, Esmaili, Mantri, *Tight Query Lower Bounds for Quantum Sampling, with an Application to
Certified Randomness*, arXiv:2610.06721 (version of sha256 00a999f1…), §3.4, Definition 3.4,
p.18 (PDF p.21).

"A family of positive operators is a map `ω ↦ (τ^ω_z)_{z∈{0,1}^n}` from oracles to tuples of
positive semidefinite operators on `E`, measurable with respect to the distribution of the oracle.
It is normalized if `E_ω Σ_z Tr τ^ω_z = 1`. … For normalized families `ρ` and `τ` define
`p_guess(Z | RE)_τ = E_ω sup_M Σ_z Tr(M_z τ^ω_z)`, `H_min(Z | RE)_τ = −log p_guess(Z | RE)_τ`,
`F(ρ, τ) = E_ω Σ_z ‖√ρ^ω_z √τ^ω_z‖₁`, `P(ρ, τ) = √(1 − F(ρ, τ)²)`, where the supremum is over all
measurements `M = (M_z)_z` on `E`, … and where `‖T‖₁ = Tr √(T†T)` is the trace norm. … For
`0 ≤ η ≤ 1`, the smooth min-entropy is `H^η_min(Z | RE)_ρ = sup{H_min(Z | RE)_τ : τ a normalized
family with P(ρ, τ) ≤ η}`." Logarithms are to base 2 (§3.1).

**Formalization Note.**
* The oracle ranges over a measurable space `Ω` with its law `P` (a probability measure), the
  outcome over a finite type `Z`, and Eve's register is the coordinate space of a finite type `E`.
* "Measurable" is entrywise: `ω ↦ (τ^ω_z)_{ij}` is measurable for every `z, i, j`. Normalization
  includes integrability of `ω ↦ Σ_z Tr τ^ω_z` (otherwise the Bochner integral is `0`).
* `√·` of a positive semidefinite matrix is the continuous functional calculus `CFC.sqrt`;
  `‖T‖₁ = Re Tr √(T†T)`.
* The supremum over measurements is a real `iSup` over POVMs; it is bounded by `Σ_z Tr τ^ω_z`.
  The smoothing supremum is a real `sSup` of a set that contains `H_min(ρ)` (as `P(ρ, ρ) = 0`)
  and is bounded above by `log N` when `Z` has `N` elements.
-/

variable {Ω : Type} [MeasurableSpace Ω] {Z E : Type} [Fintype Z] [Fintype E] [DecidableEq E]

/-- Definition 3.4: a family of positive operators: positive semidefinite, entrywise measurable in
the oracle. -/
def IsFamily (τ : Ω → Z → Matrix E E ℂ) : Prop :=
  (∀ ω z, (τ ω z).PosSemidef) ∧ ∀ z i j, Measurable fun ω => τ ω z i j

/-- Definition 3.4: a normalized family, `E_ω Σ_z Tr τ^ω_z = 1`. -/
def IsNormalized (P : Measure Ω) (τ : Ω → Z → Matrix E E ℂ) : Prop :=
  IsFamily τ ∧ Integrable (fun ω => ∑ z, (τ ω z).trace.re) P ∧
    ∫ ω, ∑ z, (τ ω z).trace.re ∂P = 1

/-- A measurement `(M_z)_z` on `E`: positive semidefinite operators summing to `I_E`. -/
def IsPOVM (M : Z → Matrix E E ℂ) : Prop :=
  (∀ z, (M z).PosSemidef) ∧ ∑ z, M z = 1

/-- `sup_M Σ_z Tr(M_z τ_z)` over measurements on `E`. -/
noncomputable def guessAt (τω : Z → Matrix E E ℂ) : ℝ :=
  ⨆ M : {M : Z → Matrix E E ℂ // IsPOVM M}, ∑ z, (M.1 z * τω z).trace.re

/-- Definition 3.4: the guessing probability `p_guess(Z | RE)_τ = E_ω sup_M Σ_z Tr(M_z τ^ω_z)`. -/
noncomputable def pGuess (P : Measure Ω) (τ : Ω → Z → Matrix E E ℂ) : ℝ :=
  ∫ ω, guessAt (τ ω) ∂P

/-- Definition 3.4: `H_min(Z | RE)_τ = −log₂ p_guess(Z | RE)_τ`. -/
noncomputable def hMin (P : Measure Ω) (τ : Ω → Z → Matrix E E ℂ) : ℝ :=
  -Real.logb 2 (pGuess P τ)

/-- The trace norm `‖T‖₁ = Tr √(T†T)`. -/
noncomputable def traceNorm (T : Matrix E E ℂ) : ℝ :=
  (CFC.sqrt (Tᴴ * T)).trace.re

/-- Definition 3.4: the fidelity `F(ρ, τ) = E_ω Σ_z ‖√ρ^ω_z √τ^ω_z‖₁` of two families. -/
noncomputable def fidelity (P : Measure Ω) (ρ τ : Ω → Z → Matrix E E ℂ) : ℝ :=
  ∫ ω, ∑ z, traceNorm (CFC.sqrt (ρ ω z) * CFC.sqrt (τ ω z)) ∂P

/-- Definition 3.4: the purified distance `P(ρ, τ) = √(1 − F(ρ, τ)²)`. -/
noncomputable def purDist (P : Measure Ω) (ρ τ : Ω → Z → Matrix E E ℂ) : ℝ :=
  Real.sqrt (1 - fidelity P ρ τ ^ 2)

/-- Definition 3.4: the smooth min-entropy
`H^η_min(Z | RE)_ρ = sup{H_min(Z | RE)_τ : τ a normalized family with P(ρ, τ) ≤ η}`. -/
noncomputable def smoothHMin (P : Measure Ω) (η : ℝ) (ρ : Ω → Z → Matrix E E ℂ) : ℝ :=
  sSup {h : ℝ | ∃ τ : Ω → Z → Matrix E E ℂ, IsNormalized P τ ∧ purDist P ρ τ ≤ η ∧
    h = hMin P τ}

end TightQLB.Supplement


