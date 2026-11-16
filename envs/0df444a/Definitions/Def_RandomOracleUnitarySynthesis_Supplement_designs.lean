-- Prove2me | Definitions.Def_RandomOracleUnitarySynthesis_Supplement_designs
-- name    : RandomOracleUnitarySynthesis_Supplement_designs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T11:34:23.360349+00:00
-- url     : https://prove2.me/theorems/c61216d3-b899-4ee6-a5c7-cc886c520480
-- title:
--   Standard non-adaptive and strong adaptive unitary designs
-- statement:
--   Let $N=2^n$. A probability law $\nu$ on $U(N)$ is a standard non-adaptive $T$-design of error $\delta$ when every mixed state $\rho$ on $T$ query registers and any finite reference, and every effect $0\le E\le I$, obey
--
--   $$\left|\mathbb E_{U\sim\nu}\operatorname{Re}\operatorname{tr}\bigl(E(U^{\otimes T}\otimes I)\rho(U^{\otimes T}\otimes I)^\dagger\bigr)-\mathbb E_{U\sim\mathrm{Haar}}\operatorname{Re}\operatorname{tr}\bigl(E(U^{\otimes T}\otimes I)\rho(U^{\otimes T}\otimes I)^\dagger\bigr)\right|\le\delta.$$
--
--   A strong adaptive design instead requires this advantage bound for every algorithm making at most $T$ calls chosen classically and adaptively from $U,U^\dagger,\overline U,U^T,cU,cU^\dagger,c\overline U,cU^T$. The workspace dimension is arbitrary and finite; the initial density, intermediate CPTP operations, and final effect are arbitrary. A nine-valued selector includes no call. Before every call its off-diagonal blocks are removed, enforcing classical choice. Classical outcomes and feedback can be stored in the workspace. A selector zero pads an unused query slot.
--
--   These predicates specify exactly the two access models used in the supplement. The strong ensemble law is a Borel measure on the ambient matrix space, required to be a probability and supported almost surely on unitaries. On this support the acceptance functions are continuous, bounded between zero and one, and hence integrable; the integrals do not use nonintegrability defaults.
-- source:
--   Andrew Huang, Akshar Ramkumar, John Wright, STOC 2027 submission #157 (October 2026), Definitions 2.1–2.2, printed p. 11 (PDF p. 13); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/157.pdf; published basis; PDF SHA256 2f2d7fa67fe2665257ec12cb0d11d7e2a80752cdecc0484b26a311d1223c5d11

import Definitions.Def_RandomOracleUnitarySynthesis_synthesis_matrix_model
import Definitions.Def_WildeQIT_EntBreaking_IsQuantumChannel
import Definitions.Def_QAlgorithms_Defs_Gates

open scoped Matrix ComplexConjugate ComplexOrder
open MeasureTheory
noncomputable section

namespace RandomOracleUnitarySynthesis.Supplement

instance matrixMeasurable (n : ℕ) : MeasurableSpace (synthesis_Mat n) := borel _
instance matrixBorel (n : ℕ) : BorelSpace (synthesis_Mat n) := ⟨rfl⟩

/-! Huang–Ramkumar–Wright, §2.2, Definitions 2.1–2.2, printed p.11 / PDF p.13.
The standard design uses the operational equivalent stated on that page. The strong
model dephases a nine-valued oracle selector at EVERY call. Arbitrary CPTP maps on
the whole workspace include measurements, storage of classical outcomes, discarding,
and adaptive feedback. The selector is never coherently queried. -/

abbrev ParallelBasis (n T b : ℕ) := (Fin T → synthesis_Bits n) × Fin b

/-- U^{⊗T} ⊗ I_b, with an arbitrary finite reference b. -/
def parallelOracle {n : ℕ} (U : synthesis_Unitary n) (T b : ℕ) :
    Matrix (ParallelBasis n T b) (ParallelBasis n T b) ℂ :=
  fun x y => if x.2 = y.2 then ∏ j : Fin T, (U : synthesis_Mat n) (x.1 j) (y.1 j) else 0

/-- Born probability after the T parallel forward calls. -/
def parallelAccept {n T b : ℕ} (ρ E : Matrix (ParallelBasis n T b) (ParallelBasis n T b) ℂ)
    (U : synthesis_Unitary n) : ℝ :=
  (E * parallelOracle U T b * ρ * (parallelOracle U T b)ᴴ).trace.re

/-- Operational Definition 2.1: all mixed joint inputs, every finite reference,
and every two-outcome POVM. Equivalent to half the twirl diamond norm ≤ δ. -/
def StandardDesign {n : ℕ} (ν : Measure (synthesis_Unitary n)) (T : ℕ) (δ : ℝ) : Prop :=
  IsProbabilityMeasure ν ∧ ∀ (b : ℕ)
    (ρ E : Matrix (ParallelBasis n T b) (ParallelBasis n T b) ℂ),
    WildeQIT.IsDensityOperator ρ → E.PosSemidef → (1-E).PosSemidef →
    |(∫ U, parallelAccept ρ E U ∂ν) -
      (∫ U, parallelAccept ρ E U ∂(synthesis_haar n))| ≤ δ

abbrev QueryBasis (n : ℕ) := Bool × synthesis_Bits n
abbrev AdaptiveBasis (n b : ℕ) := Fin 9 × (QueryBasis n × Fin b)
abbrev AdaptiveMat (n b : ℕ) := Matrix (AdaptiveBasis n b) (AdaptiveBasis n b) ℂ

/-- An uncontrolled call leaves the extra control qubit untouched. -/
def uncontrolled {n : ℕ} (V : synthesis_Mat n) : Matrix (QueryBasis n) (QueryBasis n) ℂ :=
  fun x y => if x.1 = y.1 then V x.2 y.2 else 0

/-- Exactly no call, U, U†, conjugate U, transpose U, and their four controlled versions.
Transpose and conjugation are in the fixed computational basis. -/
def oracleBranch {n : ℕ} (U : synthesis_Mat n) :
    Fin 9 → Matrix (QueryBasis n) (QueryBasis n) ℂ
  | 0 => 1
  | 1 => uncontrolled U
  | 2 => uncontrolled Uᴴ
  | 3 => uncontrolled (U.map star)
  | 4 => uncontrolled Uᵀ
  | 5 => QAlgorithms.controlled U
  | 6 => QAlgorithms.controlled Uᴴ
  | 7 => QAlgorithms.controlled (U.map star)
  | 8 => QAlgorithms.controlled Uᵀ

/-- Block oracle on selector ⊗ control ⊗ query ⊗ arbitrary finite workspace. -/
def selectedOracle {n : ℕ} (U : synthesis_Mat n) (b : ℕ) : AdaptiveMat n b :=
  fun x y => if x.1 = y.1 ∧ x.2.2 = y.2.2 then
    oracleBranch U x.1 x.2.1 y.2.1 else 0

/-- Measure the selector and forget the external record. Its classical value remains
in the selector, and can also be copied to workspace by the intermediate CPTP maps. -/
def dephaseSelector {n b : ℕ} (ρ : AdaptiveMat n b) : AdaptiveMat n b :=
  fun x y => if x.1 = y.1 then ρ x y else 0

def adaptiveCall {n b : ℕ} (U : synthesis_Mat n) (ρ : AdaptiveMat n b) : AdaptiveMat n b :=
  selectedOracle U b * dephaseSelector ρ * (selectedOracle U b)ᴴ

/-- At most T calls: selector 0 pads an unused slot. All data are independent of U.
The initial state is arbitrary and mixed. The final effect absorbs any final quantum
operation. Workspace dimension b is quantified without a bound in StrongDesign. -/
structure AdaptiveAlgorithm (n b T : ℕ) where
  initial : AdaptiveMat n b
  initial_density : WildeQIT.IsDensityOperator initial
  operations : Fin T → (AdaptiveMat n b →ₗ[ℂ] AdaptiveMat n b)
  operations_channel : ∀ j, WildeQIT.EntBreaking.IsQuantumChannel (operations j)
  effect : AdaptiveMat n b
  effect_positive : effect.PosSemidef
  effect_complement_positive : (1-effect).PosSemidef

def adaptiveAccept {n b T : ℕ} (A : AdaptiveAlgorithm n b T) (U : synthesis_Mat n) : ℝ :=
  (A.effect * (List.ofFn A.operations).foldl
    (fun ρ operation => adaptiveCall U (operation ρ)) A.initial).trace.re

/-- Definition 2.2, using the ambient matrix space for the ensemble law. Probability
and unitary support are explicit, so this is exactly a Borel law on U(N). Every
algorithm has arbitrary finite workspace, arbitrary CPTP operations and classical
adaptive choices among all eight oracles. -/
def StrongDesign {n : ℕ} (μ : Measure (synthesis_Mat n)) (T : ℕ) (δ : ℝ) : Prop :=
  IsProbabilityMeasure μ ∧ (∀ᵐ U ∂μ, U ∈ Matrix.unitaryGroup (synthesis_Bits n) ℂ) ∧
  ∀ (b : ℕ) (A : AdaptiveAlgorithm n b T),
    |(∫ U, adaptiveAccept A U ∂μ) -
      (∫ U, adaptiveAccept A (U : synthesis_Mat n) ∂(synthesis_haar n))| ≤ δ

end RandomOracleUnitarySynthesis.Supplement


