-- Prove2me | Definitions.Def_GaussOptCVQKD_Purification
-- name    : GaussOptCVQKD_Purification
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T16:00:10.40811+00:00
-- url     : https://prove2.me/theorems/2fbaa00e-a1fa-4e5b-b80e-b02450b43bb0
-- title:
--   Eve's purification $|\Psi\rangle_{ABE}$, her state $\rho_E$ and her conditional states $\rho^a_E$
-- statement:
--   **Purification (p.2).** "Alice and Bob are assumed to share a bipartite quantum state $\rho_{AB}$, whose purification is given to Eve": a unit vector $\Psi\in\mathcal H_{AB}\otimes\mathcal H_E$ with $\operatorname{Tr}_E|\Psi\rangle\langle\Psi|=\rho_{AB}$. Eve's state is $\rho_E=\operatorname{Tr}_{AB}|\Psi\rangle\langle\Psi|$.
--
--   **Eve's conditional states (p.2).** After party $p$ measures and obtains $a$ (law $\nu$), Eve holds $\rho^a_E$, characterized by: each $\rho^a_E$ is a density, and for all basis labels $e,e'$ of $\mathcal H_E$ and frequencies $\eta$,
--   $$
--   \int e^{i\eta\cdot a}\,\langle e|\rho^a_E|e'\rangle\,d\nu(a)=\operatorname{Tr}\bigl(|\Psi\rangle\langle\Psi|\,(F(\eta)\otimes|e'\rangle\langle e|)\bigr),
--   $$
--   with $F(\eta)$ the characteristic operator of party $p$'s measurement (the other party's modes are traced out). Eve's averaged conditional entropy is $\int d\nu(a)\,S(\rho^a_E)$, so that her Holevo information is $\chi_{aE}=S(\rho_E)-\int da\,p(a)S(\rho^a_E)$.
--
--   **Formalization Note** $\mathcal H_E=\ell^2(J)$ for an arbitrary index type $J$. The averaged entropy is an infimum over all admissible families, $+\infty$ if there is none.
-- source:
--   García-Patrón, Cerf, Unconditional optimality of Gaussian attacks against continuous-variable QKD, arXiv:quant-ph/0608032v1, 'Entanglement-based version of CV-QKD', p.2

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P14
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P33
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P07
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P14
import Definitions.Def_GaussOptCVQKD_MeasurementModel

open MeasureTheory
open scoped ENNReal
open QAlgorithms.RealRegisters (Hilbert)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open QAlgorithms.Papers.Independent.Dependency50.P33 (IsDensity rankOne)
open QAlgorithms.Papers.Independent.Frontier18.P07 (extendedEntropyNats)
open QAlgorithms.Papers.Independent.Frontier30.P14 (partialRight partialLeft)
open QAlgorithms.Papers.Independent.Support50.P14 (OscillatorKernel oscillatorWeylKernel)

namespace GaussOptCVQKD

/-- **Eve holds a purification of `ρ_AB`**, García-Patrón, Cerf, arXiv:quant-ph/0608032v1,
"Entanglement-based version of CV-QKD", p.2: "Alice and Bob are assumed to share a bipartite
quantum state ρAB, whose purification is given to Eve."

`Ψ` is a unit vector of `H_AB ⊗ H_E`, with `H_AB` the Fock space of the modes `I` and
`H_E = ℓ²(J)` for an arbitrary index type `J`, and `Tr_E |Ψ⟩⟨Ψ| = ρ_AB`. -/
def IsPurification {I J : Type} (Ψ : Hilbert (Occupation I × J)) (ρ : OscillatorKernel I) :
    Prop :=
  ‖Ψ‖ = 1 ∧ partialRight (rankOne Ψ) = ρ

/-- **Eve's state** `ρ_E = Tr_AB |Ψ⟩⟨Ψ|`. -/
noncomputable def eveState {I J : Type} (Ψ : Hilbert (Occupation I × J)) : Matrix J J ℂ :=
  partialLeft (rankOne Ψ)

/-- **Eve's conditional states `ρ^a_E`**, arXiv:quant-ph/0608032v1, p.2 (the term
`∫ da p(a) S(ρ^a_E)` of `χ_aE = S(ρ_E) − ∫ da p(a) S(ρ^a_E)`).

`ν` is the law of party `p`'s outcome and `c a` Eve's state given outcome `a`: every `c a` is a
density on `ℓ²(J)` and, for all basis labels `e, e'` and frequency vectors `η`,
`∫ exp(i η·a) ⟨e|c a|e'⟩ dν(a) = Tr(|Ψ⟩⟨Ψ| (F(η) ⊗ |e'⟩⟨e|))`, where
`F(η) = W(η on p's measured quadratures) · (heterodyne factor)` is the characteristic operator of
party `p`'s measurement (the other party's modes are traced out). -/
def IsEveConditionalFamily {I J : Type} [Fintype I] (owner : I → Fin 2)
    (choice : Fin 2 → Measurement) (Ψ : Hilbert (Occupation I × J)) (p : Fin 2)
    (ν : Measure (PartyOutcome owner choice p)) (c : PartyOutcome owner choice p → Matrix J J ℂ) :
    Prop :=
  IsProbabilityMeasure ν ∧ (∀ a, IsDensity (c a)) ∧
    (∀ e e' : J, Integrable (fun a => c a e e') ν) ∧
    ∀ (η : PartyOutcome owner choice p) (e e' : J),
      ∫ a, Complex.exp (Complex.I * (pairing η a : ℂ)) * c a e e' ∂ν =
        (∑' x : Occupation I, ∑' y : Occupation I,
          rankOne Ψ (x, e) (y, e') * oscillatorWeylKernel (embedOutcome owner choice p η) y x) *
          (heterodyneFactor choice p η : ℂ)

/-- **Eve's averaged conditional entropy `∫ da p(a) S(ρ^a_E)`** (nats, in `[0, ∞]`); an infimum
over all families satisfying `IsEveConditionalFamily`, `⊤` if there is none. -/
noncomputable def eveHolevoIntegral {I J : Type} [Fintype I] (owner : I → Fin 2)
    (choice : Fin 2 → Measurement) (Ψ : Hilbert (Occupation I × J)) (p : Fin 2) : ℝ≥0∞ :=
  ⨅ (ν : Measure (PartyOutcome owner choice p)) (c : PartyOutcome owner choice p → Matrix J J ℂ)
    (_ : IsEveConditionalFamily owner choice Ψ p ν c),
    ∫⁻ a, extendedEntropyNats (c a) ∂ν

end GaussOptCVQKD


