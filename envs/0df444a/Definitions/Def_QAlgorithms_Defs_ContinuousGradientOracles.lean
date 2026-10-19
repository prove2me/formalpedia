-- Prove2me | Definitions.Def_QAlgorithms_Defs_ContinuousGradientOracles
-- name    : QAlgorithms_Defs_ContinuousGradientOracles
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:14:13.290271+00:00
-- url     : https://prove2.me/theorems/1ac4fa3b-8073-4ce7-bf9c-4dd145e669b4
-- title:
--   ContinuousGradientOracles
-- statement:
--   ContinuousGradientOracles
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\ContinuousGradientOracles.lean

import Definitions.Def_QAlgorithms_Defs_SingleQubitCert
noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace QAlgorithms.StochasticOptimization

variable {n m d k b w M K N c out : ℕ}

/-- Euclidean vector space, the norm convention of 2308.01582 p.2. -/
abbrev Vector (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- Measurable unbiased gradient kernel, 2308.01582 p.4 Definition 2.
The source p.2 footnote 1 assumes every objective differentiable, excluding
Mathlib gradient defaults at nondifferentiable points. Integrability is
part of the SGO; moment/variance bounds and Lipschitz-gradient smoothness
are separate. -/
structure StochasticGradientLaw (d : ℕ) (f : Vector d → ℝ) where
  differentiable : Differentiable ℝ f
  kernel : Kernel (Vector d) (Vector d)
  markov : IsMarkovKernel kernel
  mean_integrable : ∀ x, Integrable (fun v => v) (kernel x)
  unbiased : ∀ x, ∫ v, v ∂kernel x = gradient f x

/-- L-bounded means a second-moment bound, not a support bound
(2308.01582 p.4 Definition 2). -/
def StochasticGradientLaw.IsBounded {d : ℕ} {f : Vector d → ℝ}
    (S : StochasticGradientLaw d f) (L : ℝ) : Prop :=
  0 ≤ L ∧ ∀ x, Integrable (fun v => ‖v‖ ^ 2) (S.kernel x) ∧
    ∫ v, ‖v‖ ^ 2 ∂S.kernel x ≤ L ^ 2

/-- Projection-valued Borel value measurement, 2308.01582 pp.3–4.
The Born law is tied to event projections for every vector. Countable
orthogonal additivity is strong-operator additivity; this permits continuous
L2 realizations as well as atomic summands without Dirac-amplitude fiction. -/
structure ValueMeasurement (d : ℕ) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] where
  projection : Set (Vector d) → H →L[ℂ] H
  empty : projection ∅ = 0
  total : projection Set.univ = ContinuousLinearMap.id ℂ H
  idempotent : ∀ B, MeasurableSet B → (projection B).comp (projection B) = projection B
  selfadjoint : ∀ B, MeasurableSet B → ∀ x y,
    inner ℂ x (projection B y) = inner ℂ (projection B x) y
  disjoint : ∀ B C, MeasurableSet B → MeasurableSet C → Disjoint B C →
    (projection B).comp (projection C) = 0
  additive : ∀ B : ℕ → Set (Vector d), (∀ i, MeasurableSet (B i)) →
    Pairwise (fun i j => Disjoint (B i) (B j)) → ∀ psi,
      HasSum (fun i => projection (B i) psi) (projection (⋃ i, B i) psi)
  born : H → Measure (Vector d)
  born_eq : ∀ psi B, MeasurableSet B → born psi B = ENNReal.ofReal (‖projection B psi‖ ^ 2)

/-- Public sampling registers: fixed reset state and value measurement,
2308.01582 p.3 Definition 1. This layout is fixed before unknown laws/oracles,
so fresh preparation and measurement cannot reveal a law for free. -/
structure SamplingRegisters (d : ℕ) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] where
  zero : H
  zero_norm : ‖zero‖ = 1
  measurement : ValueMeasurement d H

/-- Continuous sampling realization, 2308.01582 p.3 Definition 1,
on public fixed registers. Garbage and unitary extensions are unrestricted;
the normalized value law is tied exactly to the prepared state. -/
structure QuantumSamplingOracle (d : ℕ) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (registers : SamplingRegisters d H) where
  distribution : Measure (Vector d)
  probability : IsProbabilityMeasure distribution
  unitary : H ≃ₗᵢ[ℂ] H
  law : registers.measurement.born (unitary registers.zero) = distribution

/-- Public point/value registers and clean query subspace, 2308.01582 pp.3–4.
Separate-register query/value projections commute. Atomic point embeddings
coexist with continuous Hilbert summands; no separability or finite-support
restriction is imposed. -/
structure GradientRegisters (d : ℕ) (H W : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W] where
  sampling : SamplingRegisters d W
  atPoint : Vector d → W →ₗᵢ[ℂ] H
  orthogonal : ∀ x y, x ≠ y → ∀ a b, inner ℂ (atPoint x a) (atPoint y b) = 0
  cleanSpace : Submodule ℂ H
  cleanPoint : ∀ x, atPoint x sampling.zero ∈ cleanSpace
  queryMeasurement : ValueMeasurement d H
  valueMeasurement : ValueMeasurement d H
  pointEigen : ∀ x a B, MeasurableSet B →
    (x ∈ B → queryMeasurement.projection B (atPoint x a) = atPoint x a) ∧
      (x ∉ B → queryMeasurement.projection B (atPoint x a) = 0)
  commuting : ∀ B C, MeasurableSet B → MeasurableSet C →
    (queryMeasurement.projection B).comp (valueMeasurement.projection C) =
      (valueMeasurement.projection C).comp (queryMeasurement.projection B)

/-- Coherent QSGO with fixed public layout, 2308.01582 pp.3–4 Definition 3.
Only the clean-input action is specified; dirty-input unitary extensions
are unrestricted. The joint Born rule on every clean coherent input gives the integral
preparation formula meaning also in continuous sectors. This is the exact
oracle-access contract, not an algorithm success or resource assumption. -/
structure QuantumStochasticGradientOracle (d : ℕ) (f : Vector d → ℝ)
    (H W : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]
    (registers : GradientRegisters d H W) where
  stochastic : StochasticGradientLaw d f
  unitary : H ≃ₗᵢ[ℂ] H
  fiber : Vector d → W ≃ₗᵢ[ℂ] W
  coherent : ∀ x, unitary (registers.atPoint x registers.sampling.zero) =
    registers.atPoint x (fiber x registers.sampling.zero)
  fiber_law : ∀ x,
    registers.sampling.measurement.born (fiber x registers.sampling.zero) = stochastic.kernel x
  joint_law : ∀ psi ∈ registers.cleanSpace, ‖psi‖ = 1 →
    ∀ B C, MeasurableSet B → MeasurableSet C →
      ENNReal.ofReal (‖registers.queryMeasurement.projection B
        (registers.valueMeasurement.projection C (unitary psi))‖ ^ 2) =
      ∫⁻ x in B, stochastic.kernel x C ∂registers.queryMeasurement.born psi

/-- Sanity check for the modeled source objects (arxiv-2308.01582v2, PDF pp.3,4). -/
example {d : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (M : ValueMeasurement d H) (psi : H) :
    M.born psi Set.univ = ENNReal.ofReal (‖psi‖ ^ 2) := by
  rw [M.born_eq psi Set.univ MeasurableSet.univ, M.total]
  rfl

/-- Sanity check for the modeled source objects (arxiv-2308.01582v2, PDF pp.3,4). -/
example {d : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (R : SamplingRegisters d H) (O : QuantumSamplingOracle d H R) :
    O.unitary.symm (O.unitary R.zero) = R.zero :=
  O.unitary.symm_apply_apply R.zero

end QAlgorithms.StochasticOptimization


