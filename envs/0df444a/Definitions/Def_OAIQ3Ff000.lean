-- Prove2me | Definitions.Def_OAIQ3Ff000
-- name    : OAIQ3Ff000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-25T23:29:06.144432+00:00
-- url     : https://prove2.me/theorems/014b9a08-4cba-47e9-8d24-369896e1a827
-- title:
--   Definitions bundle OAIQ3Ff000 of the split of OpenAI, Invariant-projection counterexamples for every irrational rotation
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.FiniteFactor.main_theorem`, carved from OpenAI's openai/math development (OpenAI, *Invariant-projection counterexamples for every irrational rotation*, OpenAI Math Release, September 27, 2026, result family 293, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 399 declarations of OpenAI's Lean: 228 definitions, 7 inductive types or structures, 28 instances and 136 theorems. The definitions and types are `OAI.FiniteFactor.Coefficients`, `OAI.FiniteFactor.CouplingParameters`, `OAI.FiniteFactor.CouplingParameters.BlockCoordinate`, `OAI.FiniteFactor.CouplingParameters.badHalfEvent`, `OAI.FiniteFactor.CouplingParameters.blockPrefix`, `OAI.FiniteFactor.CouplingParameters.blockProductCoupling`, `OAI.FiniteFactor.CouplingParameters.blockProductEndpoint`, `OAI.FiniteFactor.CouplingParameters.coupling`, `OAI.FiniteFactor.CouplingParameters.crossingLabel`, `OAI.FiniteFactor.CouplingParameters.crossingPartner`, `OAI.FiniteFactor.CouplingParameters.currentBoundary`, `OAI.FiniteFactor.CouplingParameters.currentNonTag`, `OAI.FiniteFactor.CouplingParameters.currentTag`, `OAI.FiniteFactor.CouplingParameters.diagonalHaarReference`, `OAI.FiniteFactor.CouplingParameters.diagonalMass`, `OAI.FiniteFactor.CouplingParameters.eligible`, `OAI.FiniteFactor.CouplingParameters.eligibleIndices`, `OAI.FiniteFactor.CouplingParameters.endpoint`, `OAI.FiniteFactor.CouplingParameters.endpointComponentDensity`, `OAI.FiniteFactor.CouplingParameters.endpointComponentLaw`, `OAI.FiniteFactor.CouplingParameters.endpointDensity`, `OAI.FiniteFactor.CouplingParameters.endpointInterval`, `OAI.FiniteFactor.CouplingParameters.endpointLength`, `OAI.FiniteFactor.CouplingParameters.finiteProductDensity`, `OAI.FiniteFactor.CouplingParameters.labelMass`, `OAI.FiniteFactor.CouplingParameters.labelledCoupling`, `OAI.FiniteFactor.CouplingParameters.leftLength`, `OAI.FiniteFactor.CouplingParameters.minimumLength`, `OAI.FiniteFactor.CouplingParameters.mixedPosteriorKernel`, `OAI.FiniteFactor.CouplingParameters.orderedPairs`, `OAI.FiniteFactor.CouplingParameters.orientPair`, `OAI.FiniteFactor.CouplingParameters.pairComponentLaw`, `OAI.FiniteFactor.CouplingParameters.posteriorKernel`, `OAI.FiniteFactor.CouplingParameters.posteriorLaw`, `OAI.FiniteFactor.CouplingParameters.posteriorMass`, `OAI.FiniteFactor.CouplingParameters.prefixDensity`, `OAI.FiniteFactor.CouplingParameters.replacementMass`, `OAI.FiniteFactor.CouplingParameters.rho`, `OAI.FiniteFactor.CouplingParameters.rightLength`, `OAI.FiniteFactor.CouplingParameters.selectedDensity` and 195 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis, in whole or in part: `FiniteFactor_BiasedPairs_Measures`, `FiniteFactor_BiasedPairs_PrefixLimit`, `FiniteFactor_BiasedPairs_ReferenceDomination`, `FiniteFactor_BoundedMatrixOperator`, `FiniteFactor_Contradiction`, `FiniteFactor_Convolution`, `FiniteFactor_Coupling_BadEvents`, `FiniteFactor_Coupling_Bayes`, `FiniteFactor_Coupling_BlockLimit`, `FiniteFactor_Coupling_Bounds`, `FiniteFactor_Coupling_Crossing`, `FiniteFactor_Coupling_Density`, `FiniteFactor_Coupling_FiniteDisintegration`, `FiniteFactor_Coupling_FiniteLaw`, `FiniteFactor_Coupling_FinitePosteriorAC`, `FiniteFactor_Coupling_Law`, `FiniteFactor_Coupling_Marginals`, `FiniteFactor_Coupling_Mixture`, `FiniteFactor_Coupling_Noncrossing`, `FiniteFactor_Coupling_Order`, `FiniteFactor_Coupling_Parameters`, `FiniteFactor_Coupling_Prefix`, `FiniteFactor_Coupling_Products`, `FiniteFactor_Coupling_TaggedAdmissibility`, `FiniteFactor_Coupling_VectorBayes`, `FiniteFactor_CrossedProduct_AngleLaw`, `FiniteFactor_CrossedProduct_AngleRelations`, `FiniteFactor_CrossedProduct_AssignedBadEvents`, `FiniteFactor_CrossedProduct_BoundaryEvent`, `FiniteFactor_CrossedProduct_CappedPair`, `FiniteFactor_CrossedProduct_CentralScalarField`, `FiniteFactor_CrossedProduct_Cocycle`, `FiniteFactor_CrossedProduct_ColumnSquareMass`, `FiniteFactor_CrossedProduct_ConjugationVacuum`, `FiniteFactor_CrossedProduct_CurrentTaggedEvent`, `FiniteFactor_CrossedProduct_EventLossAssembly`, `FiniteFactor_CrossedProduct_FiberEnergy`, `FiniteFactor_CrossedProduct_FiberIndicators`, `FiniteFactor_CrossedProduct_FiberTotal`, `FiniteFactor_CrossedProduct_FieldRepresentation`, `FiniteFactor_CrossedProduct_FiniteVectors`, `FiniteFactor_CrossedProduct_FloorSupport`, `FiniteFactor_CrossedProduct_GeneratedAlgebra`, `FiniteFactor_CrossedProduct_InvariantConull`, `FiniteFactor_CrossedProduct_MultiplicationAdjoint`, `FiniteFactor_CrossedProduct_NormalFunctionalSpace`, `FiniteFactor_CrossedProduct_Operator`, `FiniteFactor_CrossedProduct_OperatorField`, `FiniteFactor_CrossedProduct_OrderedTorusSampling`, `FiniteFactor_CrossedProduct_PhaseCount`, `FiniteFactor_CrossedProduct_PhaseCoverage`, `FiniteFactor_CrossedProduct_PhaseDecay`, `FiniteFactor_CrossedProduct_PhaseFirst`, `FiniteFactor_CrossedProduct_Phases`, `FiniteFactor_CrossedProduct_Powers`, `FiniteFactor_CrossedProduct_ProjectionColumns`, `FiniteFactor_CrossedProduct_ProjectionEvent`, `FiniteFactor_CrossedProduct_Reflection`, `FiniteFactor_CrossedProduct_Rotation`, `FiniteFactor_CrossedProduct_RotationCommutant`, `FiniteFactor_CrossedProduct_ScalarCommutant`, `FiniteFactor_CrossedProduct_StageCoupling`, `FiniteFactor_CrossedProduct_StageOperator`, `FiniteFactor_CrossedProduct_Stages`, `FiniteFactor_CrossedProduct_TagLaw`, `FiniteFactor_CrossedProduct_TorusCharacters`, `FiniteFactor_CrossedProduct_TorusModel`, `FiniteFactor_CrossedProduct_TorusOperatorField`, `FiniteFactor_CrossedProduct_Transport`, `FiniteFactor_CrossedProduct_VacuumFunctional`, `FiniteFactor_Fiber_Diagonal`, `FiniteFactor_Fiber_PairZeroSet`, `FiniteFactor_Fiber_Shift`, `FiniteFactor_FiniteMixtureAlgebra`, `FiniteFactor_FiniteProductMixture`, `FiniteFactor_FiniteSingleTag`, `FiniteFactor_IndependentCount`, `FiniteFactor_Matrix_Action`, `FiniteFactor_Matrix_Entries`, `FiniteFactor_OperatorTracialRepresentation`, `FiniteFactor_OperatorUltraweak`, `FiniteFactor_OrbitSampling_CompactTorus`, `FiniteFactor_OrbitSampling_Cube`, `FiniteFactor_OrbitSampling_LimitMeasure`, `FiniteFactor_OrbitSampling_Measures`, `FiniteFactor_OrbitSampling_OrderedRestriction`, `FiniteFactor_OrbitSampling_Powers`, `FiniteFactor_OrbitSampling_RationalTests`, `FiniteFactor_OrbitSampling_TorusMarginals`, `FiniteFactor_OrbitSampling_TorusSupport`, `FiniteFactor_OrbitSampling_TrimmedWeak`, `FiniteFactor_OrbitSampling_WeakLimit`, `FiniteFactor_OrbitSampling_Weights`, `FiniteFactor_Polynomial`, `FiniteFactor_ProductKernel`, `FiniteFactor_Sampling_FirstInterval`, `FiniteFactor_Sampling_IntervalSums`, `FiniteFactor_Sampling_Kernel`, `FiniteFactor_Sampling_OrientedMoments`, `FiniteFactor_Sampling_SecondDensity`, `FiniteFactor_Sampling_SecondInterval`, `FiniteFactor_Sampling_SecondLevels`, `FiniteFactor_Sampling_SecondMoment`, `FiniteFactor_Sampling_Selection`, `FiniteFactor_Sampling_Smoothing`, `FiniteFactor_Sampling_SmoothingLaw`, `FiniteFactor_Sampling_TestedFirstMoment`, `FiniteFactor_Sampling_TestedSecondMoment`, `FiniteFactor_Sampling_Transport`, `FiniteFactor_Sampling_Weights`, `FiniteFactor_Truncation`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ3Ff002`; the statements `OAI.FiniteFactor.sourceBiasedPrefix_domination`, `OAI.FiniteFactor.sourceSampling_coordinate_pair_error` and `OAI.FiniteFactor.sourceSampling_mass_limit_event`; the proof of `OAI.FiniteFactor.sourceSampling_coordinate_pair_error`.
-- source:
--   OpenAI, Invariant-projection counterexamples for every irrational rotation, OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 293; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Invariant-projection-counterexamples-for-every-irrational-rotation-September-27-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis at commit adc7f12

import Mathlib

section
-- module Solutions.OAIQ3_FF.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
/-- Mathlib's newer name for `measurable_pi_lambda` (with `f` implicit). -/
theorem Measurable.of_eval {δ ι : Type*} {π : ι → Type*} [MeasurableSpace δ]
    [∀ i, MeasurableSpace (π i)] {f : δ → ∀ i, π i}
    (h : ∀ i, Measurable fun a => f a i) : Measurable f := measurable_pi_lambda f h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_Coupling_Density
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory
open scoped ENNReal
noncomputable section

/-- Normalized restriction density, relative to the probability base measure. -/
def intervalDensity {X : Type*} (U : Set X) (length : ℝ) : X → ℝ :=
  U.indicator (fun _ => length⁻¹)

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]

theorem intervalDensity_integrable {U : Set X} (hU : MeasurableSet U) (l : ℝ) :
    Integrable (intervalDensity U l) μ := (integrable_const _).indicator hU

omit [MeasurableSpace X] in
theorem intervalDensity_nonneg [MeasurableSpace X] {U : Set X} {l : ℝ} (hl : 0 ≤ l) (x : X) :
    0 ≤ intervalDensity U l x := by
  classical
  by_cases hx : x ∈ U <;> simp [intervalDensity, hx, inv_nonneg.mpr hl]

omit [IsProbabilityMeasure μ] in
theorem intervalDensity_integral [IsProbabilityMeasure μ] {U : Set X} (hU : MeasurableSet U)
    {l : ℝ} (hl : 0 < l) (hm : μ.real U = l) :
    ∫ x, intervalDensity U l x ∂μ = 1 := by
  rw [intervalDensity, integral_indicator hU, setIntegral_const, smul_eq_mul, hm]
  exact mul_inv_cancel₀ hl.ne'

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_Coupling_Parameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
noncomputable section
/-- One block of the actual coupling, with two distinct width labels. The
boolean records whether this is the tagged block. -/
structure CouplingParameters where
  m : ℝ
  kappa : ℝ
  width : Fin 2 → ℝ
  tagged : Bool
  m_ge : 100 ≤ m
  kappa_nonneg : 0 ≤ kappa
  kappa_le : kappa ≤ 1/100
  width_lower : ∀ i, 1/m ≤ width i
  width_upper : ∀ i, width i ≤ 1/4

namespace CouplingParameters
variable (p : CouplingParameters)

theorem m_pos : 0 < p.m := by linarith [p.m_ge]
theorem width_pos (i : Fin 2) : 0 < p.width i :=
  (one_div_pos.mpr p.m_pos).trans_le (p.width_lower i)

def rho (i : Fin 2) : ℝ := p.kappa * Real.sqrt (p.width i / p.m)
def tagMass : ℝ := if p.tagged then 1/p.m else 0
def diagonalMass : ℝ := 1 - 2*p.rho 0 - 2*p.rho 1 - p.tagMass

theorem rho_nonneg (i : Fin 2) : 0 ≤ p.rho i :=
  mul_nonneg p.kappa_nonneg (Real.sqrt_nonneg _)

theorem rho_le (i : Fin 2) : p.rho i ≤ p.kappa * p.width i := by
  apply mul_le_mul_of_nonneg_left _ p.kappa_nonneg
  apply (Real.sqrt_le_iff).2
  refine ⟨(p.width_pos i).le, ?_⟩
  apply (div_le_iff₀ p.m_pos).2
  have h := (div_le_iff₀ p.m_pos).1 (p.width_lower i)
  nlinarith [p.width_pos i, mul_nonneg (p.width_pos i).le (sub_nonneg.mpr h)]

theorem tagMass_nonneg : 0 ≤ p.tagMass := by
  unfold tagMass
  split
  · exact div_nonneg zero_le_one p.m_pos.le
  · exact le_rfl

theorem tagMass_le : p.tagMass ≤ 1/100 := by
  unfold tagMass
  split
  · exact one_div_le_one_div_of_le (by norm_num) p.m_ge
  · norm_num

theorem diagonalMass_lower : 98/100 ≤ p.diagonalMass := by
  have h₀ := (p.rho_le 0).trans (mul_le_mul_of_nonneg_left (p.width_upper 0) p.kappa_nonneg)
  have h₁ := (p.rho_le 1).trans (mul_le_mul_of_nonneg_left (p.width_upper 1) p.kappa_nonneg)
  unfold diagonalMass
  linarith [p.kappa_le, p.tagMass_le]

theorem diagonalMass_pos : 0 < p.diagonalMass := by linarith [p.diagonalMass_lower]

/-- 0/1 are top/bottom of width 0, 2/3 of width 1, 4 is the tag.
In particular equal numerical widths do not identify labels. -/
def replacementMass : Fin 5 → ℝ :=
  ![p.rho 0, p.rho 0, p.rho 1, p.rho 1, p.tagMass]

def leftLength : Fin 5 → ℝ :=
  ![1-p.width 0/2, p.width 0/2, 1-p.width 1/2, p.width 1/2, 1/p.m]

def rightLength : Fin 5 → ℝ :=
  ![p.width 0/2, 1-p.width 0/2, p.width 1/2, 1-p.width 1/2, 1/p.m]

theorem replacementMass_nonneg (i : Fin 5) : 0 ≤ p.replacementMass i := by
  fin_cases i <;> simp [replacementMass, rho_nonneg, tagMass_nonneg]

theorem mass_sum : p.diagonalMass + ∑ i, p.replacementMass i = 1 := by
  simp [replacementMass, Fin.sum_univ_succ, diagonalMass]
  ring

theorem leftLength_pos (i : Fin 5) : 0 < p.leftLength i := by
  have h₀ := p.width_pos 0
  have h₁ := p.width_pos 1
  have hu₀ := p.width_upper 0
  have hu₁ := p.width_upper 1
  have hm := one_div_pos.mpr p.m_pos
  fin_cases i <;> simp [leftLength] <;> linarith [p.m_pos]

theorem rightLength_pos (i : Fin 5) : 0 < p.rightLength i := by
  have h₀ := p.width_pos 0
  have h₁ := p.width_pos 1
  have hu₀ := p.width_upper 0
  have hu₁ := p.width_upper 1
  have hm := one_div_pos.mpr p.m_pos
  fin_cases i <;> simp [rightLength] <;> linarith [p.m_pos]

theorem lengths_sum_le (i : Fin 5) : p.leftLength i + p.rightLength i ≤ 1 := by
  have hm : 1/p.m ≤ 1/100 := one_div_le_one_div_of_le (by norm_num) p.m_ge
  simp only [one_div] at hm
  fin_cases i <;> simp [leftLength, rightLength]
  linarith

end CouplingParameters
end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_Coupling_Mixture
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory
noncomputable section

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]
variable {ι : Type*} [Fintype ι]

def mixtureDensity (q : ℝ) (π : ι → ℝ) (d : ι → X → ℝ) (x : X) : ℝ :=
  q + ∑ i, π i * d i x

def unitIntervalMeasure : Measure ℝ := volume.restrict (Set.Ico 0 1)

instance instIsProbabilityMeasureRealUnitIntervalMeasure : IsProbabilityMeasure unitIntervalMeasure := by
  constructor
  simp [unitIntervalMeasure, Real.volume_Ico]

theorem unitIntervalMeasure_interval {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    unitIntervalMeasure.real (Set.Ico a b) = b-a := by
  rw [unitIntervalMeasure, measureReal_restrict_apply measurableSet_Ico,
    Set.inter_eq_left.mpr (Set.Ico_subset_Ico ha hb), Real.volume_real_Ico_of_le hab]

namespace CouplingParameters
variable (p : CouplingParameters)

def endpointLength (right : Bool) (i : Fin 5) : ℝ :=
  if right then p.rightLength i else p.leftLength i

def endpointInterval (right : Bool) (i : Fin 5) : Set ℝ :=
  if right then Set.Ico (1-p.rightLength i) 1 else Set.Ico 0 (p.leftLength i)

def endpointComponentDensity (right : Bool) (i : Fin 5) : ℝ → ℝ :=
  intervalDensity (p.endpointInterval right i) (p.endpointLength right i)

def endpointDensity (right : Bool) : ℝ → ℝ :=
  mixtureDensity p.diagonalMass p.replacementMass (p.endpointComponentDensity right)

theorem endpointLength_pos (right : Bool) (i : Fin 5) : 0 < p.endpointLength right i := by
  cases right <;> simp [endpointLength, leftLength_pos, rightLength_pos]

theorem endpointLength_le (right : Bool) (i : Fin 5) : p.endpointLength right i ≤ 1 := by
  have := p.lengths_sum_le i
  have := p.leftLength_pos i
  have := p.rightLength_pos i
  cases right <;> simp [endpointLength] <;> linarith

theorem endpointInterval_measurable (right : Bool) (i : Fin 5) :
    MeasurableSet (p.endpointInterval right i) := by
  cases right <;> exact measurableSet_Ico

theorem endpointInterval_mass (right : Bool) (i : Fin 5) :
    unitIntervalMeasure.real (p.endpointInterval right i) = p.endpointLength right i := by
  have hpos := p.endpointLength_pos right i
  have hle := p.endpointLength_le right i
  cases right
  · simpa [endpointInterval, endpointLength] using
      unitIntervalMeasure_interval (a := 0) (by norm_num) hpos.le hle
  · have h₀ : 0 ≤ 1-p.rightLength i := by simpa [endpointLength] using sub_nonneg.mpr hle
    have h₁ : 1-p.rightLength i ≤ 1 := by have := p.rightLength_pos i; linarith
    simpa [endpointInterval, endpointLength] using
      unitIntervalMeasure_interval h₀ h₁ le_rfl

theorem endpointDensity_lower (right : Bool) (t : ℝ) :
    p.diagonalMass ≤ p.endpointDensity right t := by
  apply le_add_of_nonneg_right
  exact Finset.sum_nonneg fun i _ => mul_nonneg (p.replacementMass_nonneg i)
    (intervalDensity_nonneg (p.endpointLength_pos right i).le t)

end CouplingParameters
end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_Coupling_Bounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory
noncomputable section
namespace CouplingParameters
variable (p : CouplingParameters)

def minimumLength : Fin 5 → ℝ :=
  ![p.width 0/2, p.width 0/2, p.width 1/2, p.width 1/2, 1/p.m]

end CouplingParameters
end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_Coupling_Law
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory
open scoped ENNReal
noncomputable section

/-- A probability density gives an actual probability measure. -/
theorem densityMeasure_probability {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {d : X → ℝ} (hd : Integrable d μ)
    (h0 : ∀ x, 0 ≤ d x) (hm : ∫ x, d x ∂μ = 1) :
    IsProbabilityMeasure (μ.withDensity (fun x => ENNReal.ofReal (d x))) := by
  constructor
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hd (Filter.Eventually.of_forall h0), hm]
  simp

namespace CouplingParameters
variable (p : CouplingParameters)

def endpointComponentLaw (right : Bool) (i : Fin 5) : Measure ℝ :=
  unitIntervalMeasure.withDensity (fun t => ENNReal.ofReal (p.endpointComponentDensity right i t))

instance endpointComponentLaw_probability (right : Bool) (i : Fin 5) :
    IsProbabilityMeasure (p.endpointComponentLaw right i) := by
  apply densityMeasure_probability
  · exact intervalDensity_integrable (p.endpointInterval_measurable right i) _
  · exact intervalDensity_nonneg (p.endpointLength_pos right i).le
  · exact intervalDensity_integral (p.endpointInterval_measurable right i)
      (p.endpointLength_pos right i) (p.endpointInterval_mass right i)

/-- Six labels: zero is diagonal; the five successors retain both widths and the tag. -/
def labelMass : Fin 6 → ℝ := Fin.cons p.diagonalMass p.replacementMass

def pairComponentLaw : Fin 6 → Measure (ℝ × ℝ) :=
  Fin.cons (unitIntervalMeasure.map (fun t => (t,t)))
    (fun i => (p.endpointComponentLaw false i).prod (p.endpointComponentLaw true i))

theorem labelMass_nonneg (i : Fin 6) : 0 ≤ p.labelMass i := by
  refine Fin.cases p.diagonalMass_pos.le (fun i => p.replacementMass_nonneg i) i

theorem labelMass_sum : ∑ i, p.labelMass i = 1 := by
  simpa [labelMass, Fin.sum_univ_succ] using p.mass_sum

instance pairComponentLaw_probability (i : Fin 6) : IsProbabilityMeasure (p.pairComponentLaw i) := by
  refine Fin.cases ?_ (fun i => ?_) i
  · constructor
    have hm : Measurable (fun t : ℝ => (t,t)) := measurable_id.prodMk measurable_id
    rw [pairComponentLaw, Fin.cons_zero, Measure.map_apply hm MeasurableSet.univ]
    simp
  · change IsProbabilityMeasure ((p.endpointComponentLaw false i).prod (p.endpointComponentLaw true i))
    infer_instance

/-- The actual augmented one-coordinate law, including its mixture label. -/
def labelledCoupling : Measure (Fin 6 × (ℝ × ℝ)) :=
  ∑ i, ENNReal.ofReal (p.labelMass i) •
    (p.pairComponentLaw i).map (fun xy => (i,xy))

instance labelledCoupling_probability : IsProbabilityMeasure p.labelledCoupling := by
  constructor
  have hmap (i : Fin 6) : ((p.pairComponentLaw i).map (fun xy => (i,xy))) Set.univ = 1 := by
    have hm : Measurable (fun xy : ℝ × ℝ => (i,xy)) := measurable_const.prodMk measurable_id
    rw [Measure.map_apply hm MeasurableSet.univ]
    simp
  simp only [labelledCoupling, Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul,
    hmap, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => p.labelMass_nonneg i), p.labelMass_sum]
  simp

/-- Forgetting labels gives the one-coordinate pair law. -/
def coupling : Measure (ℝ × ℝ) := p.labelledCoupling.map Prod.snd

instance coupling_probability : IsProbabilityMeasure p.coupling := by
  constructor
  rw [coupling, Measure.map_apply measurable_snd MeasurableSet.univ]
  simp

end CouplingParameters
end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_Coupling_Marginals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory
open scoped ENNReal
noncomputable section

namespace CouplingParameters
variable (p : CouplingParameters)

def endpoint (right : Bool) (xy : ℝ × ℝ) : ℝ := if right then xy.2 else xy.1

theorem endpoint_measurable (right : Bool) : Measurable (endpoint right) := by
  cases right
  · exact measurable_fst
  · exact measurable_snd

theorem endpointComponentDensity_measurable (right : Bool) (i : Fin 5) :
    Measurable (p.endpointComponentDensity right i) :=
  measurable_const.indicator (p.endpointInterval_measurable right i)

end CouplingParameters
end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_Coupling_Order
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory
open scoped ENNReal
noncomputable section
namespace CouplingParameters
variable (p : CouplingParameters)

def orderedPairs : Set (ℝ × ℝ) := {xy | xy.1 ≤ xy.2}

end CouplingParameters
end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_Coupling_Crossing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory
open scoped ENNReal
noncomputable section
namespace CouplingParameters
variable (p : CouplingParameters)

/-- Conditioning on y uses a bottom label; conditioning on x uses a top label. -/
def crossingLabel (right : Bool) (w : Fin 2) : Fin 5 :=
  if right then ![1,3] w else ![0,2] w

/-- This is the conditional label weight from conditional-kernel. -/
def posteriorMass (right : Bool) (t : ℝ) (i : Fin 5) : ℝ :=
  p.replacementMass i * p.endpointComponentDensity right i t / p.endpointDensity right t

theorem posteriorMass_nonneg (right : Bool) (t : ℝ) (i : Fin 5) :
    0 ≤ p.posteriorMass right t i := by
  apply div_nonneg
  · exact mul_nonneg (p.replacementMass_nonneg i)
      (intervalDensity_nonneg (p.endpointLength_pos right i).le t)
  · exact (p.diagonalMass_pos.trans_le (p.endpointDensity_lower right t)).le

theorem posteriorMass_sum (right : Bool) (t : ℝ) :
    p.diagonalMass / p.endpointDensity right t + ∑ i, p.posteriorMass right t i = 1 := by
  simp only [posteriorMass]
  rw [← Finset.sum_div, ← add_div]
  change p.endpointDensity right t / p.endpointDensity right t = 1
  exact div_self (ne_of_gt (p.diagonalMass_pos.trans_le (p.endpointDensity_lower right t)))

/-- The actual probability measure in the displayed conditional-kernel formula.
The disintegration identities are proved separately. -/
def posteriorLaw (right : Bool) (t : ℝ) : Measure ℝ :=
  ENNReal.ofReal (p.diagonalMass / p.endpointDensity right t) • Measure.dirac t +
    ∑ i, ENNReal.ofReal (p.posteriorMass right t i) • p.endpointComponentLaw (!right) i

instance posteriorLaw_probability (right : Bool) (t : ℝ) :
    IsProbabilityMeasure (p.posteriorLaw right t) := by
  constructor
  simp only [posteriorLaw, Measure.add_apply, Measure.finsetSum_apply, Measure.smul_apply,
    smul_eq_mul, measure_univ, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => p.posteriorMass_nonneg right t i),
    ← ENNReal.ofReal_add (div_nonneg p.diagonalMass_pos.le
      (p.diagonalMass_pos.trans_le (p.endpointDensity_lower right t)).le)
      (Finset.sum_nonneg (fun i _ => p.posteriorMass_nonneg right t i)),
    p.posteriorMass_sum]
  simp

end CouplingParameters
end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_Coupling_Bayes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory ProbabilityTheory
open scoped ENNReal
noncomputable section
namespace CouplingParameters
variable (p : CouplingParameters)

theorem endpointDensity_measurable (right : Bool) : Measurable (p.endpointDensity right) := by
  apply Measurable.add measurable_const
  exact Finset.measurable_sum _ fun i _ => measurable_const.mul (p.endpointComponentDensity_measurable right i)

theorem posteriorMass_measurable (right : Bool) (i : Fin 5) :
    Measurable (fun t => p.posteriorMass right t i) :=
  (measurable_const.mul (p.endpointComponentDensity_measurable right i)).div
    (p.endpointDensity_measurable right)

def posteriorKernel (right : Bool) : Kernel ℝ ℝ where
  toFun := p.posteriorLaw right
  measurable' := by
    apply Measure.measurable_of_measurable_coe
    intro S hS
    simp only [posteriorLaw, Measure.add_apply, Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul]
    apply Measurable.add
    · exact (measurable_const.div (p.endpointDensity_measurable right)).ennreal_ofReal.mul
        ((Measure.measurable_coe hS).comp Measure.measurable_dirac)
    · exact Finset.measurable_sum _ fun i _ =>
        (p.posteriorMass_measurable right i).ennreal_ofReal.mul measurable_const

instance posteriorKernel_markov (right : Bool) : IsMarkovKernel (p.posteriorKernel right) :=
  ⟨fun t => p.posteriorLaw_probability right t⟩

end CouplingParameters
end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_Coupling_Products
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory
open scoped ENNReal
noncomputable section

/-- The source's kappa_s, with natural indices shifted to start at one. -/
def sourceKappa (s : ℕ) : ℝ := 1 / (100*((s : ℝ)+1))

namespace CouplingParameters

/-- A coordinate may be omitted altogether, and every included coordinate may
choose its endpoint independently of every other coordinate. -/
def selectedDensity (p : CouplingParameters) (enabled right : Bool) (t : ℝ) : ℝ :=
  if enabled then p.endpointDensity right t else 1

/-- Actual finite product of the chosen coordinate densities. -/
def finiteProductDensity {ι : Type*} [Fintype ι] (p : ι → CouplingParameters)
    (enabled right : ι → Bool) (x : ι → ℝ) : ℝ :=
  ∏ i, (p i).selectedDensity (enabled i) (right i) (x i)

end CouplingParameters
end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_Coupling_FiniteLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory
open scoped ENNReal
noncomputable section
namespace CouplingParameters

def selectedLaw (p : CouplingParameters) (enabled right : Bool) : Measure ℝ :=
  unitIntervalMeasure.withDensity (fun t => ENNReal.ofReal (p.selectedDensity enabled right t))

end CouplingParameters
end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_ProductKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory ProbabilityTheory Finset MeasurableSpace
open scoped ENNReal
noncomputable section

/-- Products of Markov kernels, with measurability proved on the generating
finite cylinders and extended to the entire product sigma algebra. -/
def independentKernel {ι : Type*} {X Y : ι → Type*}
    [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSpace (Y i)]
    (κ : ∀ i, Kernel (X i) (Y i)) [∀ i, IsMarkovKernel (κ i)] :
    Kernel (∀ i, X i) (∀ i, Y i) where
  toFun x := Measure.infinitePi (fun i => κ i (x i))
  measurable' := by
    apply Measurable.measure_of_isPiSystem_of_isProbabilityMeasure
      generateFrom_squareCylinders.symm
      (isPiSystem_squareCylinders (fun _ => isPiSystem_measurableSet) (by simp))
    rintro _ ⟨I, S, hS, rfl⟩
    have hs (i : ι) : MeasurableSet (S i) := hS i (Set.mem_univ i)
    simp_rw [Measure.infinitePi_pi _ (fun i _ => hs i)]
    exact Finset.measurable_prod _ fun i _ => ((κ i).measurable_coe (hs i)).comp (measurable_pi_apply i)

instance independentKernel_markov {ι : Type*} {X Y : ι → Type*}
    [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSpace (Y i)]
    (κ : ∀ i, Kernel (X i) (Y i)) [∀ i, IsMarkovKernel (κ i)] :
    IsMarkovKernel (independentKernel κ) := ⟨fun x => by
      change IsProbabilityMeasure (Measure.infinitePi (fun i => κ i (x i)))
      infer_instance⟩

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_Coupling_VectorBayes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal
noncomputable section
namespace CouplingParameters

/-- The orientation records the conditioning endpoint first. -/
def orientPair (right : Bool) (z : ℝ × ℝ) : ℝ × ℝ :=
  (endpoint right z, endpoint (!right) z)

def vectorCoupling {ι : Type*} (p : ι → CouplingParameters) :
    Measure (ι → Fin 6 × (ℝ × ℝ)) := Measure.infinitePi (fun i => (p i).labelledCoupling)

instance vectorCoupling_probability {ι : Type*} (p : ι → CouplingParameters) :
    IsProbabilityMeasure (vectorCoupling p) := by unfold vectorCoupling; infer_instance

def vectorEndpoint {ι : Type*} (right : ι → Bool) (ω : ι → Fin 6 × (ℝ × ℝ)) (i : ι) : ℝ :=
  endpoint (right i) (ω i).2

theorem vectorEndpoint_measurable {ι : Type*} (right : ι → Bool) : Measurable (vectorEndpoint right) := by
  exact Measurable.of_eval (fun i => (endpoint_measurable (right i)).comp
    (measurable_snd.comp (measurable_pi_apply i)))

def vectorPosterior {ι : Type*} (p : ι → CouplingParameters) (right : ι → Bool) :
    Kernel (ι → ℝ) (ι → ℝ) := independentKernel (fun i => (p i).posteriorKernel (right i))

instance vectorPosterior_markov {ι : Type*} (p : ι → CouplingParameters) (right : ι → Bool) :
    IsMarkovKernel (vectorPosterior p right) := by unfold vectorPosterior; infer_instance

end CouplingParameters
end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_Coupling_Prefix
attribute [-instance] _root_.OAI.FiniteFactor.CouplingParameters.vectorCoupling_probability _root_.OAI.FiniteFactor.CouplingParameters.vectorPosterior_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter Finset
open scoped Topology ENNReal
noncomputable section

namespace CouplingParameters
variable {ι : Type*}

def prefixDensity (p : ι → CouplingParameters) (right : ι → Bool)
    (I : Finset ι) (x : ι → ℝ) : ℝ := ∏ i ∈ I, (p i).endpointDensity (right i) (x i)

end CouplingParameters
end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_Coupling_BlockLimit
attribute [-instance] _root_.OAI.FiniteFactor.CouplingParameters.vectorCoupling_probability _root_.OAI.FiniteFactor.CouplingParameters.vectorPosterior_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter Finset
open scoped Topology ENNReal
noncomputable section
namespace CouplingParameters

/-- The source coordinates, retaining the block and the position in that block. -/
abbrev BlockCoordinate (m : ℕ → ℕ) := Σ s : ℕ, Fin (m s)

def blockPrefix (m : ℕ → ℕ) (n : ℕ) : Finset (BlockCoordinate m) :=
  (Finset.range n).sigma (fun _ => Finset.univ)

/-- Actual augmented law on the block-indexed coordinates. -/
def blockProductCoupling (p : ℕ → CouplingParameters) (m : ℕ → ℕ) :
    Measure (BlockCoordinate m → Fin 6 × (ℝ × ℝ)) :=
  Measure.infinitePi (fun i => (p i.1).labelledCoupling)

instance blockProductCoupling_probability (p : ℕ → CouplingParameters) (m : ℕ → ℕ) :
    IsProbabilityMeasure (blockProductCoupling p m) := by unfold blockProductCoupling; infer_instance

def blockProductEndpoint {m : ℕ → ℕ} (right : BlockCoordinate m → Bool)
    (ω : BlockCoordinate m → Fin 6 × (ℝ × ℝ)) (i : BlockCoordinate m) : ℝ :=
  endpoint (right i) (ω i).2

end CouplingParameters
end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_FloorSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal
noncomputable section

/-- Source coordinate floors. Integer times include both directions. -/
def coordinateFloor {ι : Type*} (θ : ι → ℝ) (k : ℤ) (x : ι → ℝ) (i : ι) : ℤ :=
  Int.floor (x i + (k : ℝ)*θ i)

def finiteFloorSupport {ι : Type*} (θ : ι → ℝ) (x : ι → ℝ) : Prop :=
  ∀ k : ℤ, (Function.support (coordinateFloor θ k x)).Finite

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_Cocycle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal
noncomputable section

/-- Integer iterates of the source rotation, in [0,1) representatives. -/
def coordinateRotate {ι : Type*} (θ : ι → ℝ) (k : ℤ) (x : ι → ℝ) (i : ι) : ℝ :=
  Int.fract (x i + (k : ℝ)*θ i)

/-- The source logarithmic cocycle, using the actual weighted floor sum. -/
def sourceLog {ι : Type*} (θ c : ι → ℝ) (k : ℤ) (x : ι → ℝ) : ℝ :=
  ∑' i, c i * (coordinateFloor θ k x i : ℝ)

def sourceCocycle {ι : Type*} (θ c : ι → ℝ) (k : ℤ) (x : ι → ℝ) : ℝ :=
  Real.exp (-sourceLog θ c k x)

theorem sourceCocycle_pos {ι : Type*} (θ c : ι → ℝ) (k : ℤ) (x : ι → ℝ) :
    0 < sourceCocycle θ c k x := Real.exp_pos _

theorem sourceCocycle_measurable {ι : Type*} [Countable ι]
    (θ c : ι → ℝ) (k : ℤ) :
    @Measurable (ι → ℝ) ℝ
      (@MeasurableSpace.pi ι (fun _ => ℝ) (fun _ => Real.measurableSpace))
      Real.measurableSpace (sourceCocycle θ c k) := by
  apply Real.continuous_exp.measurable.comp
  apply Measurable.neg
  apply Measurable.tsum
  intro i
  have hm0 : Measurable (fun x : ι → ℝ => x i + (k : ℝ)*θ i) :=
    (measurable_pi_apply i).add measurable_const
  have hm := Int.measurable_floor.comp hm0
  exact measurable_const.mul ((measurable_of_countable (fun z : ℤ => (z : ℝ))).comp hm)

/-- The weight f=F_1 is positive and at most one on the source coordinate cube. -/
theorem sourceWeight_le_one {ι : Type*} (θ c : ι → ℝ)
    (hθ : ∀ i, 0 ≤ θ i) (hc : ∀ i, 0 ≤ c i) {x : ι → ℝ}
    (hx : ∀ i, x i ∈ Set.Ico 0 1) : sourceCocycle θ c 1 x ≤ 1 := by
  apply Real.exp_le_one_iff.mpr
  apply neg_nonpos.mpr
  apply tsum_nonneg
  intro i
  apply mul_nonneg (hc i)
  unfold coordinateFloor
  exact_mod_cast Int.floor_nonneg.mpr (show 0 ≤ x i + (1 : ℤ)*θ i by simpa using add_nonneg (hx i).1 (hθ i))

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_Operator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal
noncomputable section

/-- The regular representation written as L2(X × Z), canonically equivalent
to the source's L2(X; l2(Z)). -/
abbrev sourceMeasure (ι : Type*) : Measure ((ι → ℝ) × ℤ) :=
  (Measure.infinitePi (fun _ : ι => unitIntervalMeasure)).prod Measure.count

abbrev SourceHilbert (ι : Type*) : Type _ := Lp ℂ 2 (sourceMeasure ι)

/-- The actual diagonal entry f(sigma^k x) of pi(f). -/
def sourceDiagonal {ι : Type*} (θ c : ι → ℝ) (z : (ι → ℝ) × ℤ) : ℂ :=
  sourceCocycle θ c 1 (coordinateRotate θ z.2 z.1)

theorem sourceDiagonal_measurable {ι : Type*} [Countable ι] (θ c : ι → ℝ) :
    Measurable (sourceDiagonal θ c) := by
  apply Complex.measurable_ofReal.comp
  apply (sourceCocycle_measurable θ c 1).comp
  apply Measurable.of_eval
  intro i
  unfold coordinateRotate
  fun_prop

theorem sourceDiagonal_norm_le {ι : Type*} (θ c : ι → ℝ)
    (hθ : ∀ i, 0 ≤ θ i) (hc : ∀ i, 0 ≤ c i) (z : (ι → ℝ) × ℤ) :
    ‖sourceDiagonal θ c z‖ ≤ 1 := by
  rw [sourceDiagonal, Complex.norm_real, Real.norm_of_nonneg (sourceCocycle_pos _ _ _ _).le]
  apply sourceWeight_le_one θ c hθ hc
  intro i
  exact ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩

theorem sourceDiagonal_memLp {ι : Type*} [Countable ι] (θ c : ι → ℝ)
    (hθ : ∀ i, 0 ≤ θ i) (hc : ∀ i, 0 ≤ c i) :
    MemLp (sourceDiagonal θ c) ∞ (sourceMeasure ι) :=
  memLp_top_of_bound (sourceDiagonal_measurable θ c).aestronglyMeasurable 1
    (Eventually.of_forall (sourceDiagonal_norm_le θ c hθ hc))

/-- The shift S e_k=e_(k+1), so its action on coordinate functions uses k-1. -/
def sourceShiftIndex {ι : Type*} (z : (ι → ℝ) × ℤ) : (ι → ℝ) × ℤ := (z.1, z.2-1)

theorem sourceShiftIndex_preserving (ι : Type*) :
    MeasurePreserving (sourceShiftIndex (ι := ι)) (sourceMeasure ι) (sourceMeasure ι) := by
  have hm : Measurable (fun k : ℤ => k-1) := measurable_of_countable _
  have hi : Function.Injective (fun k : ℤ => k-1) := by intro a b h; dsimp at h; omega
  have hs : Function.Surjective (fun k : ℤ => k-1) := by intro k; exact ⟨k+1, by dsimp; omega⟩
  have hp : MeasurePreserving (fun k : ℤ => k-1) Measure.count Measure.count := by
    refine ⟨hm, ?_⟩
    ext S hS
    rw [Measure.map_apply hm hS, Measure.count_apply (hS.preimage hm), Measure.count_apply hS,
      ← hi.encard_image, Set.image_preimage_eq S hs]
  exact (MeasurePreserving.id _).prod hp

def sourceShift (ι : Type*) : SourceHilbert ι →L[ℂ] SourceHilbert ι :=
  (Lp.compMeasurePreservingₗᵢ ℂ sourceShiftIndex (sourceShiftIndex_preserving ι)).toContinuousLinearMap

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_Powers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal Topology
noncomputable section

/-- Composition of the actual representative rotations. -/
theorem coordinateRotate_add {ι : Type*} (θ : ι → ℝ) (k n : ℤ) (x : ι → ℝ) :
    coordinateRotate θ n (coordinateRotate θ k x) = coordinateRotate θ (k+n) x := by
  funext i
  unfold coordinateRotate
  rw [Int.fract_eq_fract]
  refine ⟨-Int.floor (x i + (k : ℝ)*θ i), ?_⟩
  rw [Int.fract]
  push_cast
  ring

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_Polynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open Polynomial

theorem product_has_low_nonzero_coeff (K : ℕ) (p q : ℂ[X])
    (hp : p.coeff K ≠ 0) (hq : q.coeff K ≠ 0) :
    ∃ n ≤ 2 * K, (p * q).coeff n ≠ 0 := by
  have hp0 : p ≠ 0 := by intro h; simp [h] at hp
  have hq0 : q ≠ 0 := by intro h; simp [h] at hq
  refine ⟨(p * q).natTrailingDegree, ?_,
    Polynomial.coeff_natTrailingDegree_ne_zero.mpr (mul_ne_zero hp0 hq0)⟩
  rw [Polynomial.natTrailingDegree_mul hp0 hq0]
  have ha := Polynomial.natTrailingDegree_le_of_ne_zero hp
  have hb := Polynomial.natTrailingDegree_le_of_ne_zero hq
  omega

abbrev Coefficients (K : ℕ) := Fin (2 * K + 1) → ℂ

noncomputable def coefficientPolynomial {K : ℕ} (a : Coefficients K) : ℂ[X] :=
  ∑ i : Fin (2 * K + 1), Polynomial.monomial i.val (a i)

theorem coefficientPolynomial_coeff {K : ℕ} (a : Coefficients K)
    (i : Fin (2 * K + 1)) : (coefficientPolynomial a).coeff i.val = a i := by
  classical
  simp [coefficientPolynomial, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial,
    Fin.val_inj]

noncomputable def productCoefficient {K : ℕ} (a b : Coefficients K) (n : ℕ) : ℂ :=
  ∑ i : Fin (2 * K + 1), ∑ j : Fin (2 * K + 1),
    if i.val + j.val = n then a i * b j else 0

theorem productCoefficient_eq {K : ℕ} (a b : Coefficients K) (n : ℕ) :
    productCoefficient a b n =
      (coefficientPolynomial a * coefficientPolynomial b).coeff n := by
  classical
  simp only [productCoefficient, coefficientPolynomial, Finset.sum_mul, Finset.mul_sum,
    Polynomial.monomial_mul_monomial, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
  exact Finset.sum_comm

theorem continuous_productCoefficient (K n : ℕ) :
    Continuous (fun ab : Coefficients K × Coefficients K =>
      productCoefficient ab.1 ab.2 n) := by
  classical
  unfold productCoefficient
  apply continuous_finsetSum
  intro i _
  apply continuous_finsetSum
  intro j _
  split_ifs <;> fun_prop

noncomputable def lowCoefficients {K : ℕ} (ab : Coefficients K × Coefficients K) :
    Coefficients K := fun n => productCoefficient ab.1 ab.2 n.val

theorem continuous_lowCoefficients (K : ℕ) : Continuous (@lowCoefficients K) :=
  continuous_pi fun n => continuous_productCoefficient K n.val

theorem lowCoefficients_ne_zero {K : ℕ} (ab : Coefficients K × Coefficients K)
    (ha : ab.1 ⟨K, by omega⟩ ≠ 0) (hb : ab.2 ⟨K, by omega⟩ ≠ 0) :
    lowCoefficients ab ≠ 0 := by
  have ha' : (coefficientPolynomial ab.1).coeff K ≠ 0 := by
    simpa using (coefficientPolynomial_coeff ab.1 ⟨K, by omega⟩).trans_ne ha
  have hb' : (coefficientPolynomial ab.2).coeff K ≠ 0 := by
    simpa using (coefficientPolynomial_coeff ab.2 ⟨K, by omega⟩).trans_ne hb
  obtain ⟨n, hn, hne⟩ := product_has_low_nonzero_coeff K _ _ ha' hb'
  intro h
  have hz := congrFun h ⟨n, by omega⟩
  exact hne (by simpa [lowCoefficients, productCoefficient_eq] using hz)

def admissibleCoefficients (K : ℕ) (D δ : ℝ) : Set (Coefficients K) :=
  {a | ∀ i, ‖a i‖ ≤ D} ∩ {a | δ ≤ ‖a ⟨K, by omega⟩‖}

theorem isCompact_admissibleCoefficients (K : ℕ) (D δ : ℝ) :
    IsCompact (admissibleCoefficients K D δ) := by
  have hc : IsCompact {a : Coefficients K | ∀ i, ‖a i‖ ≤ D} := by
    simpa [Set.pi, Metric.mem_closedBall, dist_zero_right] using
      (isCompact_pi_infinite fun _ : Fin (2 * K + 1) =>
        isCompact_closedBall (0 : ℂ) D)
  exact hc.inter_right (isClosed_le continuous_const (continuous_apply (⟨K, by omega⟩ : Fin (2 * K + 1))).norm)

theorem uniform_product_coefficient_bound (K : ℕ) (D δ : ℝ) (hδ : 0 < δ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ a b : Coefficients K,
      (∀ i, ‖a i‖ ≤ D) → (∀ i, ‖b i‖ ≤ D) →
      δ ≤ ‖a ⟨K, by omega⟩‖ → δ ≤ ‖b ⟨K, by omega⟩‖ →
      ∃ n : Fin (2 * K + 1), ε ≤ ‖productCoefficient a b n.val‖ := by
  classical
  let S := (admissibleCoefficients K D δ).prod (admissibleCoefficients K D δ)
  have hc : IsCompact S := (isCompact_admissibleCoefficients K D δ).prod
    (isCompact_admissibleCoefficients K D δ)
  by_cases hs : S.Nonempty
  · obtain ⟨ab, hab, hmin⟩ := hc.exists_isMinOn hs
      (continuous_lowCoefficients K).norm.continuousOn
    have hpos : 0 < ‖lowCoefficients ab‖ := by
      apply norm_pos_iff.mpr
      apply lowCoefficients_ne_zero
      · exact norm_pos_iff.mp (hδ.trans_le hab.1.2)
      · exact norm_pos_iff.mp (hδ.trans_le hab.2.2)
    refine ⟨‖lowCoefficients ab‖, hpos, ?_⟩
    intro a b ha hb ha0 hb0
    have hm : ‖lowCoefficients ab‖ ≤ ‖lowCoefficients (a, b)‖ :=
      hmin ⟨⟨ha, ha0⟩, ⟨hb, hb0⟩⟩
    by_contra hn
    push Not at hn
    have hlt : ‖lowCoefficients (a, b)‖ < ‖lowCoefficients ab‖ :=
      (pi_norm_lt_iff hpos).mpr hn
    exact (not_lt_of_ge hm) hlt
  · refine ⟨1, zero_lt_one, ?_⟩
    intro a b ha hb ha0 hb0
    exact False.elim (hs ⟨(a, b), ⟨⟨ha, ha0⟩, ⟨hb, hb0⟩⟩⟩)

/-- Coefficient of z^r in the two Laurent polynomials supported on [-K,K].
The finite indices enumerate each Laurent exponent exactly once as i-K. -/
noncomputable def laurentProductCoefficient (K : ℕ) (A B : ℤ → ℂ) (r : ℤ) : ℂ :=
  ∑ i : Fin (2 * K + 1), ∑ j : Fin (2 * K + 1),
    if (i.val : ℤ) - K + ((j.val : ℤ) - K) = r then
      A ((i.val : ℤ) - K) * B ((j.val : ℤ) - K) else 0

end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_Stages
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open Filter Finset
open scoped Topology
noncomputable section

def sourceNextCutoff (m : ℕ) : ℕ := Nat.ceil ((m : ℝ)^((3/4 : ℝ)*(m : ℝ)))

theorem sourceNextCutoff_large (m : ℕ) (hm : 100 ≤ m) : 2*m < sourceNextCutoff m := by
  have hmR : (100 : ℝ) ≤ m := by exact_mod_cast hm
  have hp : (m : ℝ)^2 ≤ (m : ℝ)^((3/4 : ℝ)*(m : ℝ)) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num; linarith)
  have hh := hp.trans (Nat.le_ceil _)
  have hh2 : (2 : ℝ)*m < (sourceNextCutoff m : ℝ) := by
    change (m : ℝ)^2 ≤ (sourceNextCutoff m : ℝ) at hh
    nlinarith
  exact_mod_cast hh2

theorem exists_source_block_length (R κ L G : ℝ) (hκ : 0 < κ) (hG : 0 < G) :
    ∃ m : ℕ, R ≤ (m : ℝ) ∧ 100 ≤ m ∧ κ*(m : ℝ)^(1/40 : ℝ) ≥ L ∧
      G*(sourceNextCutoff m : ℝ) < (m : ℝ)^((4/5 : ℝ)*(m : ℝ)) := by
  have ht : Tendsto (fun m : ℕ => (m : ℝ)^(1/40 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  obtain ⟨m, hmR, hm100, hmG, hmκ⟩ :=
    ((tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop R)).and
      ((eventually_ge_atTop (100 : ℕ)).and
        ((tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop (2*G))).and
          (ht.eventually (eventually_ge_atTop (L/κ)))))).exists
  refine ⟨m, hmR, hm100, (div_le_iff₀ hκ).mp hmκ |>.trans_eq (mul_comm _ _), ?_⟩
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
  have hm0 : (0 : ℝ) < m := lt_of_lt_of_le zero_lt_one hm1
  let A : ℝ := (m : ℝ)^((3/4 : ℝ)*(m : ℝ))
  have hApos : 0 < A := Real.rpow_pos_of_pos hm0 _
  have hA1 : 1 ≤ A := Real.one_le_rpow hm1 (by positivity)
  have hceil : (sourceNextCutoff m : ℝ) ≤ 2*A := by
    have hh := Nat.ceil_lt_add_one hApos.le
    change (Nat.ceil A : ℝ) ≤ 2*A
    linarith
  calc
    G*(sourceNextCutoff m : ℝ) ≤ G*(2*A) := mul_le_mul_of_nonneg_left hceil hG.le
    _ < (m : ℝ)*A := by nlinarith
    _ = (m : ℝ)^((3/4 : ℝ)*(m : ℝ)+1) := by rw [Real.rpow_add hm0, Real.rpow_one]; ring
    _ ≤ (m : ℝ)^((4/5 : ℝ)*(m : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hm1 (by
        have hh : (100 : ℝ) ≤ m := by exact_mod_cast hm100
        linarith)

/-- State already fixed before the new block length is chosen. B is the
previous weighted block-size sum; d is the previous coordinate count. -/
structure SourceStageState where
  K : ℕ
  G : ℝ
  d : ℕ
  B : ℝ
  previousL : ℝ
  K_ge : 1 ≤ K
  G_ge : 1 ≤ G
  B_nonneg : 0 ≤ B
  previousL_ge : 1 ≤ previousL

def SourceStageState.D (a : SourceStageState) : ℝ := Real.exp (((a.K : ℝ)+1)*a.B)

/-- Complete numerical output of one source stage. The polynomial bound is
proved before L, Gnext and m are selected. Stages use s=0 for source j=1. -/
structure SourceStageChoice (s : ℕ) (a : SourceStageState) where
  ε : ℝ
  L : ℝ
  Gnext : ℝ
  m : ℕ
  ε_pos : 0 < ε
  polynomial : ∀ u v : Coefficients a.K,
    (∀ i, ‖u i‖ ≤ a.D) → (∀ i, ‖v i‖ ≤ a.D) →
    1/((s : ℝ)+1) ≤ ‖u ⟨a.K, by omega⟩‖ → 1/((s : ℝ)+1) ≤ ‖v ⟨a.K, by omega⟩‖ →
    ∃ n : Fin (2*a.K+1), ε ≤ ‖productCoefficient u v n.val‖
  L_ge : a.previousL ≤ L
  decay : ((2*a.K : ℕ)+1 : ℝ)*3*Real.exp (-L/10000) ≤ ε/((s : ℝ)+1)
  Gnext_ge : 1 ≤ Gnext
  next_budget : sourceKappa (s+1) * Real.sqrt Gnext ≥ L
  m_ge_K : a.K ≤ m
  m_ge_pow : 2^(s+1) ≤ m
  m_ge_G : 4*a.G ≤ (m : ℝ)
  m_ge_100 : 100 ≤ m
  previous_size : (a.d : ℝ) ≤ (m : ℝ)/100
  current_budget : sourceKappa s * (m : ℝ)^(1/40 : ℝ) ≥ L
  next_gap : Gnext*(sourceNextCutoff m : ℝ) < (m : ℝ)^((4/5 : ℝ)*(m : ℝ))

theorem exists_sourceStageChoice (s : ℕ) (a : SourceStageState) :
    Nonempty (SourceStageChoice s a) := by
  have hs : 0 < (s : ℝ)+1 := by positivity
  have hk (j : ℕ) : 0 < sourceKappa j := by unfold sourceKappa; positivity
  obtain ⟨ε, hε, hp⟩ := uniform_product_coefficient_bound a.K a.D (1/((s : ℝ)+1)) (by positivity)
  let target : ℝ := (ε/((s : ℝ)+1))/(((2*a.K : ℕ)+1 : ℝ)*3)
  have ht : 0 < target := by dsimp [target]; positivity
  obtain ⟨t, htL, htt⟩ := ((eventually_ge_atTop (a.previousL/10000)).and
    (Real.tendsto_exp_neg_atTop_nhds_zero.eventually (gt_mem_nhds ht))).exists
  let L : ℝ := 10000*t
  have hL : a.previousL ≤ L := by dsimp [L]; linarith
  have hLpos : 0 < L := lt_of_lt_of_le (by linarith [a.previousL_ge]) hL
  let G : ℝ := (1+L/sourceKappa (s+1))^2
  have hG : 1 ≤ G := by dsimp [G]; nlinarith [div_pos hLpos (hk (s+1))]
  have hbudget : L ≤ sourceKappa (s+1)*Real.sqrt G := by
    rw [show Real.sqrt G = 1+L/sourceKappa (s+1) by
      dsimp [G]; rw [Real.sqrt_sq (by linarith [div_pos hLpos (hk (s+1))])]]
    rw [mul_add, mul_one, mul_div_cancel₀ _ (hk (s+1)).ne']
    linarith [hk (s+1)]
  let R : ℝ := max (a.K : ℝ) (max ((2^(s+1) : ℕ) : ℝ) (max (4*a.G) (100*(a.d : ℝ))))
  obtain ⟨m, hmR, hm100, hmκ, hmgap⟩ := exists_source_block_length R (sourceKappa s) L G (hk s) (by linarith)
  have hmK : (a.K : ℝ) ≤ m := (le_max_left _ _).trans hmR
  have hm2 : (((2^(s+1) : ℕ)) : ℝ) ≤ m := (le_max_left _ _).trans ((le_max_right _ _).trans hmR)
  have hmG : 4*a.G ≤ (m : ℝ) := (le_max_left _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hmR))
  have hmd : 100*(a.d : ℝ) ≤ m := (le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hmR))
  refine ⟨⟨ε, L, G, m, hε, hp, hL, ?_, hG, hbudget,
    by exact_mod_cast hmK, by exact_mod_cast hm2, hmG, hm100, by linarith, hmκ, hmgap⟩⟩
  have hden : 0 < (((2*a.K : ℕ)+1 : ℝ)*3) := by positivity
  have htt' := (lt_div_iff₀ hden).mp htt
  have he : -L/10000 = -t := by dsimp [L]; ring
  rw [he]
  nlinarith

def selectedSourceStage (s : ℕ) (a : SourceStageState) : SourceStageChoice s a :=
  Classical.choice (exists_sourceStageChoice s a)

def SourceStageChoice.C {s : ℕ} {a : SourceStageState} (b : SourceStageChoice s a) : ℝ :=
  max b.L ((a.K : ℝ)^2)

def SourceStageChoice.next {s : ℕ} {a : SourceStageState} (b : SourceStageChoice s a) : SourceStageState where
  K := sourceNextCutoff b.m
  G := b.Gnext
  d := a.d+b.m
  B := a.B+b.C*(b.m : ℝ)
  previousL := b.L
  K_ge := by have := sourceNextCutoff_large b.m b.m_ge_100; omega
  G_ge := b.Gnext_ge
  B_nonneg := add_nonneg a.B_nonneg (mul_nonneg (le_max_of_le_right (sq_nonneg _)) (Nat.cast_nonneg _))
  previousL_ge := a.previousL_ge.trans b.L_ge

/-- The infinite numerical construction is fixed without an operator or a
candidate invariant projection as an input. -/
def sourceStageState : ℕ → SourceStageState
  | 0 => ⟨100, 1, 0, 0, 1, by norm_num, le_rfl, le_rfl, le_rfl⟩
  | s+1 => (selectedSourceStage s (sourceStageState s)).next

def sourceStage (s : ℕ) : SourceStageChoice s (sourceStageState s) :=
  selectedSourceStage s (sourceStageState s)

theorem sourceStage_cutoff_growth (s : ℕ) :
    2*(sourceStageState s).K < (sourceStageState (s+1)).K := by
  have h := sourceNextCutoff_large (sourceStage s).m (sourceStage s).m_ge_100
  exact (Nat.mul_le_mul_left 2 (sourceStage s).m_ge_K).trans_lt h

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_StageOperator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter Finset
open scoped Topology ENNReal
noncomputable section

def sourceBlockSize (s : ℕ) : ℕ := (sourceStage s).m
abbrev SourceCoordinate := CouplingParameters.BlockCoordinate sourceBlockSize

def sourceLogWeight (i : SourceCoordinate) : ℝ := (sourceStage i.1).C

def SourceAngles (θ : SourceCoordinate → ℝ) : Prop :=
  let realGroup : GroupWithZero ℝ :=
    (@DivisionRing.toDivisionSemiring ℝ Real.instField.toDivisionRing).toGroupWithZero
  let realOrder : LE ℝ := @Preorder.toLE ℝ Real.partialOrder.toPreorder
  ∀ i : SourceCoordinate,
    let block : ℝ := @Nat.cast ℝ Real.instNatCast (sourceBlockSize i.1)
    let cutoff : ℝ := @Nat.cast ℝ Real.instNatCast (sourceStageState i.1).K
    let denominator : ℝ := @Mul.mul ℝ Real.instMul block cutoff
    let lower : ℝ :=
      @Div.div ℝ realGroup.toDiv (@One.one ℝ Real.instOne) denominator
    let upper : ℝ :=
      @Div.div ℝ realGroup.toDiv (@Nat.cast ℝ Real.instNatCast 2) denominator
    @LE.le ℝ realOrder lower (θ i) ∧ @LE.le ℝ realOrder (θ i) upper

theorem sourceBlockSize_pos (s : ℕ) : (0 : ℝ) < sourceBlockSize s := by
  exact_mod_cast (show 0 < (sourceStage s).m by have := (sourceStage s).m_ge_100; omega)

theorem sourceCutoff_pos (s : ℕ) : (0 : ℝ) < (sourceStageState s).K := by
  exact_mod_cast (show 0 < (sourceStageState s).K by have := (sourceStageState s).K_ge; omega)

theorem SourceAngles.nonneg {θ : SourceCoordinate → ℝ} (hθ : SourceAngles θ)
    (i : SourceCoordinate) :
    @LE.le ℝ (@Preorder.toLE ℝ Real.partialOrder.toPreorder)
      (@Zero.zero ℝ Real.instZero) (θ i) :=
  let realGroup : GroupWithZero ℝ :=
    (@DivisionRing.toDivisionSemiring ℝ Real.instField.toDivisionRing).toGroupWithZero
  let realOrder : Preorder ℝ := Real.partialOrder.toPreorder
  let realStrict : @PosMulStrictMono ℝ Real.instMul Real.instZero realOrder :=
    @IsStrictOrderedRing.toPosMulStrictMono ℝ Real.semiring Real.partialOrder
      Real.instIsStrictOrderedRing
  let realReflect : @PosMulReflectLT ℝ Real.instMul Real.instZero realOrder :=
    @PosMulMono.toPosMulReflectLT ℝ Real.instMul Real.instZero Real.linearOrder
      (@IsOrderedRing.toPosMulMono ℝ Real.semiring Real.partialOrder
        Real.instIsOrderedRing)
  let block : ℝ := @Nat.cast ℝ Real.instNatCast (sourceBlockSize i.1)
  let cutoff : ℝ := @Nat.cast ℝ Real.instNatCast (sourceStageState i.1).K
  let denominator : ℝ := @Mul.mul ℝ Real.instMul block cutoff
  let lower : ℝ :=
    @Div.div ℝ realGroup.toDiv (@One.one ℝ Real.instOne) denominator
  let upper : ℝ :=
    @Div.div ℝ realGroup.toDiv (@Nat.cast ℝ Real.instNatCast 2) denominator
  let zeroReal : ℝ := @Zero.zero ℝ Real.instZero
  @le_trans ℝ realOrder zeroReal lower (θ i)
    (@le_of_lt ℝ realOrder zeroReal lower
      ((@one_div_pos ℝ realGroup Real.partialOrder realReflect denominator).mpr
        (@mul_pos ℝ realGroup.toMulZeroClass (a := block) (b := cutoff)
          realOrder realStrict (sourceBlockSize_pos i.1) (sourceCutoff_pos i.1))))
    (@And.left
      (@LE.le ℝ realOrder.toLE lower (θ i))
      (@LE.le ℝ realOrder.toLE (θ i) upper)
      (hθ i))

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_StageCoupling
attribute [-instance] _root_.OAI.FiniteFactor.CouplingParameters.vectorCoupling_probability _root_.OAI.FiniteFactor.CouplingParameters.vectorPosterior_markov
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter Finset
open scoped ENNReal
noncomputable section

/-- Both source widths, derived from the stages already constructed. -/
def sourceWidth (s : ℕ) : Fin 2 → ℝ :=
  ![(sourceStageState s).G/(sourceBlockSize s : ℝ), (sourceBlockSize s : ℝ)^(-19/20 : ℝ)]

theorem sourceWidth_bounds (s : ℕ) (w : Fin 2) :
    1/(sourceBlockSize s : ℝ) ≤ sourceWidth s w ∧ sourceWidth s w ≤ 1/4 := by
  have hm : (100 : ℝ) ≤ sourceBlockSize s := by exact_mod_cast (sourceStage s).m_ge_100
  have hm0 := sourceBlockSize_pos s
  fin_cases w
  · simp only [sourceWidth]
    constructor
    · exact div_le_div_of_nonneg_right (sourceStageState s).G_ge hm0.le
    · apply (div_le_iff₀ hm0).mpr
      have hh := (sourceStage s).m_ge_G
      change 4*(sourceStageState s).G ≤ (sourceBlockSize s : ℝ) at hh
      linarith
  · simp only [sourceWidth]
    constructor
    · rw [one_div, ← Real.rpow_neg_one]
      exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
    · have hsqrt : (4 : ℝ) ≤ Real.sqrt (sourceBlockSize s : ℝ) := by
        apply (Real.le_sqrt (by norm_num) hm0.le).mpr
        nlinarith
      have hpow : Real.sqrt (sourceBlockSize s : ℝ) ≤ (sourceBlockSize s : ℝ)^(19/20 : ℝ) := by
        rw [Real.sqrt_eq_rpow]
        exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
      have hh := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 4) (hsqrt.trans hpow)
      rw [show (-19/20 : ℝ) = -(19/20) by ring, Real.rpow_neg hm0.le]
      simpa [one_div] using hh

/-- The source coupling parameters now have all width and scale hypotheses
discharged by the recursive construction. j is the unique tagged block. -/
def stagedCouplingParameters (j s : ℕ) : CouplingParameters where
  m := sourceBlockSize s
  kappa := sourceKappa s
  width := sourceWidth s
  tagged := decide (s=j)
  m_ge := by exact_mod_cast (sourceStage s).m_ge_100
  kappa_nonneg := by unfold sourceKappa; positivity
  kappa_le := by
    unfold sourceKappa
    apply one_div_le_one_div_of_le (by norm_num)
    have hh : (0 : ℝ) ≤ s := Nat.cast_nonneg s
    nlinarith
  width_lower := fun w => (sourceWidth_bounds s w).1
  width_upper := fun w => (sourceWidth_bounds s w).2

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_AngleLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology
noncomputable section

/-- The source angle interval has length 1/N_s, where N_s=m_s K_s. -/
def sourceAngleUnit (i : SourceCoordinate) : ℝ :=
  1 / ((sourceBlockSize i.1 : ℝ) * (sourceStageState i.1).K)

def sourceAngleInterval (i : SourceCoordinate) : Set ℝ :=
  Set.Icc (sourceAngleUnit i) (2 * sourceAngleUnit i)

/-- Normalized Lebesgue measure on the actual source interval. -/
def sourceAngleMarginal (i : SourceCoordinate) : Measure ℝ :=
  cond volume (sourceAngleInterval i)

instance sourceAngleMarginal_atomless (i : SourceCoordinate) :
    NullSingletonClass (sourceAngleMarginal i) := by
  constructor
  intro x
  exact cond_absolutelyContinuous (measure_singleton x)

/-- This law is selected before any invariant projection is considered. -/
def sourceAngleLaw : Measure (SourceCoordinate → ℝ) :=
  Measure.infinitePi sourceAngleMarginal

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_Rotation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal
noncomputable section

def sourceCircleRepresentative (x : AddCircle (1 : ℝ)) : ℝ :=
  (AddCircle.equivIco 1 0 x).val

theorem sourceCircleRepresentative_measurable : Measurable sourceCircleRepresentative :=
  measurable_subtype_coe.comp (AddCircle.measurableEquivIco 1 0).measurable

theorem sourceCircleRepresentative_coe (x : ℝ) :
    sourceCircleRepresentative (x : AddCircle (1 : ℝ)) = Int.fract x := by
  have hx : Int.fract x ∈ Set.Ico (0 : ℝ) (0+1) :=
    ⟨Int.fract_nonneg _, by simpa using Int.fract_lt_one x⟩
  have he := AddCircle.equivIco_coe_eq (p := (1 : ℝ)) (a := 0) hx
  rw [AddCircle.coe_fract] at he
  exact congrArg Subtype.val he

theorem sourceCircle_mk_preserving :
    MeasurePreserving ((↑) : ℝ → AddCircle (1 : ℝ)) unitIntervalMeasure volume := by
  simpa [unitIntervalMeasure, restrict_Ico_eq_restrict_Ioc] using
    AddCircle.measurePreserving_mk 1 0

theorem sourceCircleRepresentative_preserving :
    MeasurePreserving sourceCircleRepresentative volume unitIntervalMeasure := by
  refine ⟨sourceCircleRepresentative_measurable, ?_⟩
  rw [← sourceCircle_mk_preserving.map_eq,
    Measure.map_map sourceCircleRepresentative_measurable sourceCircle_mk_preserving.measurable]
  have he : (sourceCircleRepresentative ∘ ((↑) : ℝ → AddCircle (1 : ℝ))) =ᵐ[unitIntervalMeasure] id := by
    filter_upwards [ae_restrict_mem measurableSet_Ico] with x hx
    rw [Function.comp_apply, sourceCircleRepresentative_coe]
    exact Int.fract_eq_self.mpr hx
  rw [Measure.map_congr he, Measure.map_id]

/-- Translation modulo one preserves the exact real representative measure. -/
theorem unitInterval_rotate_preserving (a : ℝ) :
    MeasurePreserving (fun x : ℝ => Int.fract (x+a)) unitIntervalMeasure unitIntervalMeasure := by
  have hh := sourceCircleRepresentative_preserving.comp
    ((measurePreserving_add_right (volume : Measure (AddCircle (1 : ℝ))) (a : AddCircle (1 : ℝ))).comp
      sourceCircle_mk_preserving)
  convert hh using 1
  funext x
  simpa only [Function.comp_apply, ← AddCircle.coe_add] using (sourceCircleRepresentative_coe (x+a)).symm

/-- All integer iterates of the countable source rotation preserve its actual
infinite product measure. This is not an assumed action property. -/
theorem coordinateRotate_preserving {ι : Type*} (θ : ι → ℝ) (k : ℤ) :
    MeasurePreserving (coordinateRotate θ k)
      (Measure.infinitePi (fun _ : ι => unitIntervalMeasure))
      (Measure.infinitePi (fun _ : ι => unitIntervalMeasure)) := by
  have hm (i : ι) : Measurable (fun x : ℝ => Int.fract (x+(k : ℝ)*θ i)) :=
    (unitInterval_rotate_preserving _).measurable
  refine ⟨Measurable.of_eval (fun i => (hm i).comp (measurable_pi_apply i)), ?_⟩
  unfold coordinateRotate
  rw [Measure.infinitePi_map_pi _ hm]
  simp_rw [(unitInterval_rotate_preserving _).map_eq]

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_IndependentCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Finset
open scoped ENNReal Classical
noncomputable section

/-- The finite union event specifying at least q coordinate misses. -/
def coordinateMissEvent (I : Finset SourceCoordinate) (q : ℕ)
    (S : SourceCoordinate → Set ℝ) : Set (SourceCoordinate → ℝ) :=
  ⋃ J ∈ I.powersetCard q, Set.pi (J : Set SourceCoordinate) S

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_PhaseCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Finset
open scoped ENNReal Classical
noncomputable section

def sourceBlockCoordinates (s : ℕ) : Finset SourceCoordinate :=
  Finset.univ.map ⟨fun i : Fin (sourceBlockSize s) => ⟨s,i⟩, by intro i j h; cases h; rfl⟩

@[simp] theorem sourceBlockCoordinates_card (s : ℕ) :
    (sourceBlockCoordinates s).card = sourceBlockSize s := by simp [sourceBlockCoordinates]

theorem mem_sourceBlockCoordinates {s : ℕ} {i : SourceCoordinate}
    (hi : i ∈ sourceBlockCoordinates s) : i.1 = s := by
  obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hi
  rfl

def sourcePhaseMissSet (s : ℕ) (k : ℤ) : Set ℝ :=
  {t | 1-Int.fract ((k : ℝ)*t) ∉ Set.Icc (sourceWidth s 1) (1-sourceWidth s 1)}

def sourceFewPhases (s : ℕ) (k : ℤ) : Set (SourceCoordinate → ℝ) :=
  {θ | (((sourceBlockCoordinates s).filter (fun i => θ i ∉ sourcePhaseMissSet s k)).card : ℝ) <
    (sourceBlockSize s : ℝ)/20}

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_PhaseDecay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal Topology
noncomputable section

theorem sourceBlockSize_tendsto : Tendsto sourceBlockSize atTop atTop := by
  have hs : StrictMono (fun s => (sourceStageState s).K) := by
    apply strictMono_nat_of_lt_succ
    intro s
    have hh := sourceStage_cutoff_growth s
    omega
  exact tendsto_atTop_mono (fun s => (sourceStage s).m_ge_K) hs.tendsto_atTop

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_Sampling_Selection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open Finset

/-- Finite greedy packing, with the precise loss supplied by forbidden neighbors. -/
theorem finite_greedy_packing {α : Type*} [DecidableEq α] (bad : α → α → Prop)
    [DecidableRel bad] (symm : ∀ a b, bad a b → bad b a)
    (refl : ∀ a, bad a a) (S : Finset α) (D : ℕ)
    (bound : ∀ a ∈ S, (S.filter (bad a)).card ≤ D) :
    ∃ N ⊆ S, (N : Set α).Pairwise (fun a b => ¬bad a b) ∧ S.card ≤ D*N.card := by
  classical
  induction S using Finset.strongInductionOn with
  | _ S ih =>
    by_cases hs : S = ∅
    · subst S; exact ⟨∅, by simp, by simp, by simp⟩
    obtain ⟨a, ha⟩ := Finset.nonempty_iff_ne_empty.mpr hs
    let T := S.filter (fun b => ¬bad a b)
    have hTa : a ∉ T := by simp [T, refl]
    have hTS : T ⊂ S := Finset.ssubset_iff_subset_ne.mpr
      ⟨filter_subset _ _, fun h => hTa (h.symm ▸ ha)⟩
    obtain ⟨N,hNT,hN,hcard⟩ := ih T hTS (fun b hb =>
      (card_le_card (filter_subset_filter _ (filter_subset _ _))).trans (bound b (mem_of_mem_filter b hb)))
    have haN : a ∉ N := fun h => hTa (hNT h)
    refine ⟨insert a N, insert_subset ha (hNT.trans (filter_subset _ _)), ?_, ?_⟩
    · rw [coe_insert, Set.pairwise_insert_of_notMem haN]
      refine ⟨hN, ?_⟩
      intro b hb
      constructor
      · exact (mem_filter.mp (hNT hb)).2
      · intro h; exact (mem_filter.mp (hNT hb)).2 (symm b a h)
    · have hsplit : (S.filter (bad a)).card + T.card = S.card := by
        exact card_filter_add_card_filter_not (s := S) (bad a)
      rw [card_insert_of_notMem haN]
      have := bound a ha
      rw [Nat.mul_add, Nat.mul_one]
      omega

/-- A fixed nonzero second frequency excludes at most 2R+1 integers. -/
theorem forbidden_frequency_card (S : Finset ℤ) (v v' n : ℤ) (R : ℕ) (hv' : v' ≠ 0) :
    (S.filter (fun n' => |v*n+v'*n'| ≤ (R : ℤ))).card ≤ 2*R+1 := by
  have h := card_le_card_of_injOn (fun n' : ℤ => v*n+v'*n')
    (s := S.filter (fun n' => |v*n+v'*n'| ≤ (R : ℤ)))
    (t := Finset.Icc (-(R : ℤ)) (R : ℤ))
    (fun n' hn' => Finset.mem_Icc.mpr (abs_le.mp (mem_filter.mp hn').2))
    (fun a _ b _ he => mul_left_cancel₀ hv' (add_left_cancel he))
  have hc : (Finset.Icc (-(R : ℤ)) (R : ℤ)).card = 2*R+1 := by
    rw [Int.card_Icc]
    omega
  exact h.trans_eq hc

/-- Failure of the full symmetric bounded-frequency separation condition. -/
def SamplingConflict (H R : ℕ) (n n' : ℤ) : Prop :=
  ∃ v ∈ Finset.Icc (-(H : ℤ)) (H : ℤ),
    ∃ v' ∈ Finset.Icc (-(H : ℤ)) (H : ℤ),
      (v ≠ 0 ∨ v' ≠ 0) ∧ |v*n+v'*n'| ≤ (R : ℤ)

noncomputable instance instDecidableRelIntSamplingConflict (H R : ℕ) : DecidableRel (SamplingConflict H R) := fun _ _ =>
  inferInstanceAs (Decidable (∃ v ∈ Finset.Icc (-(H : ℤ)) (H : ℤ),
    ∃ v' ∈ Finset.Icc (-(H : ℤ)) (H : ℤ), _))

theorem samplingConflict_symm (H R : ℕ) (n n' : ℤ) :
    SamplingConflict H R n n' → SamplingConflict H R n' n := by
  rintro ⟨v,hv,v',hv',hne,hb⟩
  exact ⟨v',hv',v,hv,hne.symm,by simpa [add_comm] using hb⟩

theorem samplingConflict_refl (H R : ℕ) (hH : 1 ≤ H) (n : ℤ) :
    SamplingConflict H R n n := by
  refine ⟨1, mem_Icc.mpr ?_, -1, mem_Icc.mpr ?_, Or.inl (by omega), ?_⟩
  · constructor <;> omega
  · constructor <;> omega
  · simp

/-- Total forbidden-neighbor count, with no unspecified asymptotic constant. -/
theorem samplingConflict_card (H R : ℕ) (S : Finset ℤ) (n : ℤ) (hn : (R : ℤ) < n) :
    (S.filter (SamplingConflict H R n)).card ≤ (2*H+1)^2*(2*R+1) := by
  let F := (Finset.Icc (-(H : ℤ)) (H : ℤ)).product
    ((Finset.Icc (-(H : ℤ)) (H : ℤ)).filter (fun v => v ≠ 0))
  let B := fun p : ℤ × ℤ => S.filter (fun n' => |p.1*n+p.2*n'| ≤ (R : ℤ))
  have hsub : S.filter (SamplingConflict H R n) ⊆ F.biUnion B := by
    intro n' hn'
    obtain ⟨hs,v,hv,v',hv',hne,hb⟩ := mem_filter.mp hn'
    have hv'0 : v' ≠ 0 := by
      intro he
      subst v'
      have hv0 := hne.resolve_right (by simp)
      have hv1 : 1 ≤ |v| := by have := abs_pos.mpr hv0; omega
      have hn0 : 0 ≤ n := by omega
      simp only [zero_mul, add_zero, abs_mul, abs_of_nonneg hn0] at hb
      nlinarith
    exact mem_biUnion.mpr ⟨(v,v'), mem_product.mpr ⟨hv,mem_filter.mpr ⟨hv',hv'0⟩⟩,
      mem_filter.mpr ⟨hs,hb⟩⟩
  have hF : F.card ≤ (2*H+1)^2 := by
    have hc : (Finset.Icc (-(H : ℤ)) (H : ℤ)).card = 2*H+1 := by
      rw [Int.card_Icc]; omega
    dsimp [F]
    rw [card_product]
    calc
      _ ≤ (Finset.Icc (-(H : ℤ)) (H : ℤ)).card ^ 2 := by
        rw [pow_two]
        exact Nat.mul_le_mul_left _ (card_filter_le _ _)
      _ = _ := by rw [hc]
  calc
    _ ≤ (F.biUnion B).card := card_le_card hsub
    _ ≤ ∑ p ∈ F, (B p).card := card_biUnion_le
    _ ≤ ∑ _p ∈ F, (2*R+1) := sum_le_sum fun p hp =>
      forbidden_frequency_card S p.1 p.2 n R (mem_filter.mp (mem_product.mp hp).2).2
    _ = F.card*(2*R+1) := by simp
    _ ≤ _ := Nat.mul_le_mul_right _ hF

/-- Deterministic selection from any positive integer interval above R. -/
theorem exists_sampling_separated (H R : ℕ) (hH : 1 ≤ H) (S : Finset ℤ)
    (hS : ∀ n ∈ S, (R : ℤ) < n) :
    ∃ N ⊆ S, (N : Set ℤ).Pairwise (fun n n' => ¬SamplingConflict H R n n') ∧
      S.card ≤ ((2*H+1)^2*(2*R+1))*N.card :=
  finite_greedy_packing (SamplingConflict H R) (samplingConflict_symm H R)
    (samplingConflict_refl H R hH) S _ (fun n hn => samplingConflict_card H R S n (hS n hn))

end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_OrbitSampling_Powers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open Finset Filter
open scoped Topology
noncomputable section

def samplingQ (m : ℕ) : ℝ := (m : ℝ)^((7/10 : ℝ)*(m : ℝ))
def samplingH (m : ℕ) : ℕ := m^300
def samplingR (m K : ℕ) : ℕ := m*K*m^1000

theorem sampling_integer_candidates (Q : ℝ) (hQ : 4 ≤ Q) :
    Q/4 ≤ ((Finset.Icc ⌈Q/2⌉ ⌊Q⌋).card : ℝ) := by
  have hf := Int.sub_one_lt_floor Q
  have hc := Int.ceil_lt_add_one (Q/2)
  have horder : ⌈Q/2⌉ ≤ ⌊Q⌋ := by
    have : (⌈Q/2⌉ : ℝ) < (⌊Q⌋ : ℝ)+1 := by linarith
    have ht : ⌈Q/2⌉ < ⌊Q⌋+1 := by exact_mod_cast this
    omega
  rw [Int.card_Icc]
  have hcast : ((⌊Q⌋+1-⌈Q/2⌉).toNat : ℝ) = (⌊Q⌋ : ℝ)+1-(⌈Q/2⌉ : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg (by omega : 0 ≤ ⌊Q⌋+1-⌈Q/2⌉)
  rw [hcast]
  linarith

theorem sampling_forbidden_budget (m K : ℕ) (hm : 4 ≤ m) (hK : K ≤ m) :
    (((2*samplingH m+1)^2*(2*samplingR m K+1) : ℕ) : ℝ) ≤ (m : ℝ)^1605 := by
  have hm1 : 1 ≤ m := by omega
  have hh : 1 ≤ samplingH m := one_le_pow₀ hm1
  have hr : samplingR m K ≤ m^1002 := by
    unfold samplingR
    calc
      m*K*m^1000 ≤ m*m*m^1000 := by gcongr
      _ = m^1002 := by ring
  have hp : 1 ≤ m^1002 := one_le_pow₀ hm1
  have hD : (2*samplingH m+1)^2*(2*samplingR m K+1) ≤ 27*m^1602 := by
    calc
      _ ≤ (3*samplingH m)^2*(3*m^1002) := by gcongr <;> omega
      _ = _ := by unfold samplingH; ring
  have h27 : 27 ≤ m^3 := (by norm_num : 27 ≤ (4 : ℕ)^3).trans (Nat.pow_le_pow_left hm 3)
  have hhD : (2*samplingH m+1)^2*(2*samplingR m K+1) ≤ m^1605 := by
    calc
      _ ≤ 27*m^1602 := hD
      _ ≤ m^3*m^1602 := Nat.mul_le_mul_right _ h27
      _ = _ := by ring
  exact_mod_cast hhD

/-- An explicit sufficiently-large threshold discharges the source's greedy
asymptotics, retaining Q, H, R and the exponent 0.69m exactly. -/
theorem exists_source_sampling_powers (m K : ℕ) (hm : 200000 ≤ m) (hK : K ≤ m) :
    ∃ N : Finset ℤ,
      (∀ n ∈ N, samplingQ m/2 ≤ (n : ℝ) ∧ (n : ℝ) ≤ samplingQ m ∧ 0 < n) ∧
      (m : ℝ)^((69/100 : ℝ)*(m : ℝ)) ≤ (N.card : ℝ) ∧
      (N : Set ℤ).Pairwise (fun n n' => ¬SamplingConflict (samplingH m) (samplingR m K) n n') := by
  have hmR : (200000 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  have hm1 : (1 : ℝ) ≤ m := by linarith
  have hQ : (m : ℝ)^1606 ≤ samplingQ m := by
    unfold samplingQ
    rw [← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le hm1
    norm_num
    linarith
  have hmQ : (m : ℝ) ≤ samplingQ m := by
    calc
      _ ≤ (m : ℝ)^1606 := le_self_pow₀ hm1 (by norm_num)
      _ ≤ _ := hQ
  have hQ4 : 4 ≤ samplingQ m := by linarith
  have hR : (samplingR m K : ℝ) < samplingQ m/2 := by
    have hr : samplingR m K ≤ m^1002 := by
      unfold samplingR
      calc
        m*K*m^1000 ≤ m*m*m^1000 := by gcongr
        _ = _ := by ring
    have hsmall : (m : ℝ)^1002 * (m : ℝ) ≤ (m : ℝ)^1606 := by
      rw [← pow_succ]
      exact pow_le_pow_right₀ hm1 (by norm_num)
    have hrR : (samplingR m K : ℝ) ≤ (m : ℝ)^1002 := by exact_mod_cast hr
    have hpos : 0 < (m : ℝ)^1002 := by positivity
    nlinarith
  let S := Finset.Icc ⌈samplingQ m/2⌉ ⌊samplingQ m⌋
  have hS (n : ℤ) (hn : n ∈ S) :
      samplingQ m/2 ≤ (n : ℝ) ∧ (n : ℝ) ≤ samplingQ m := by
    have hh := mem_Icc.mp hn
    constructor
    · exact (Int.le_ceil _).trans (by exact_mod_cast hh.1)
    · exact (show (n : ℝ) ≤ (⌊samplingQ m⌋ : ℝ) by exact_mod_cast hh.2).trans (Int.floor_le _)
  obtain ⟨N,hNS,hpair,hcard⟩ := exists_sampling_separated (samplingH m) (samplingR m K)
    (one_le_pow₀ (by omega)) S (fun n hn => by exact_mod_cast hR.trans_le (hS n hn).1)
  refine ⟨N, fun n hn => ⟨(hS n (hNS hn)).1, (hS n (hNS hn)).2, ?_⟩, ?_, hpair⟩
  · have hh := (hS n (hNS hn)).1
    have : (0 : ℝ) < n := by linarith
    exact_mod_cast this
  · have hcount : samplingQ m/4 ≤
        (((2*samplingH m+1)^2*(2*samplingR m K+1) : ℕ) : ℝ)*(N.card : ℝ) :=
      (sampling_integer_candidates _ hQ4).trans (by exact_mod_cast hcard)
    have hDb := sampling_forbidden_budget m K (by omega) hK
    have hcount' : samplingQ m/4 ≤ (m : ℝ)^1605*(N.card : ℝ) :=
      hcount.trans (mul_le_mul_of_nonneg_right hDb (Nat.cast_nonneg _))
    have hexp : (m : ℝ)^1605*(m : ℝ)^((69/100 : ℝ)*(m : ℝ))*(m : ℝ) ≤ samplingQ m := by
      unfold samplingQ
      calc
        _ = (m : ℝ)^(1605+(69/100 : ℝ)*(m : ℝ)+1) := by
          rw [Real.rpow_add hm0, Real.rpow_one, Real.rpow_add hm0]
          norm_num [Real.rpow_ofNat]
        _ ≤ _ := by
          apply Real.rpow_le_rpow_of_exponent_le hm1
          norm_num
          linarith
    have hprod : 0 < (m : ℝ)^1605 := by positivity
    have htarget : 0 ≤ (m : ℝ)^((69/100 : ℝ)*(m : ℝ)) := by positivity
    apply (mul_le_mul_iff_right₀ hprod).mp
    nlinarith

/-- A deterministic finite set fixed from the numerical stages alone. -/
def sourceSamplingPowers (s : ℕ) : Finset ℤ :=
  if h : 200000 ≤ sourceBlockSize s then
    Classical.choose (exists_source_sampling_powers (sourceBlockSize s)
      (sourceStageState s).K h (sourceStage s).m_ge_K)
  else ∅

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_Sampling_Kernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Finset
open scoped ComplexConjugate
noncomputable section

def samplingCharacter (v : ℤ) (t : ℝ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * v * t)

/-- The finite Fejer kernel, as a nonnegative real function. -/
def samplingKernel (H : ℕ) (t : ℝ) : ℝ :=
  ‖∑ r ∈ Finset.range H, samplingCharacter (r : ℤ) t‖^2 / (H : ℝ)

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_Sampling_Smoothing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Finset
open scoped ComplexConjugate ENNReal
noncomputable section

def samplingSmooth (H : ℕ) (E : Set ℝ) (t : ℝ) : ℝ :=
  ∫ u in E, samplingKernel H (t-u) ∂unitIntervalMeasure

def samplingIntervalCoefficient (E : Set ℝ) (v : ℤ) : ℂ :=
  ∫ u in E, samplingCharacter (-v) u ∂unitIntervalMeasure

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_Sampling_SmoothingLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory
open scoped ENNReal
noncomputable section

def samplingBoundary (a b δ : ℝ) : Set ℝ :=
  (Set.Icc δ (1-δ))ᶜ ∪ Set.Icc (a-δ) (a+δ) ∪ Set.Icc (b-δ) (b+δ)

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_Sampling_Weights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory
noncomputable section

/-- Distance of a representative to the two ends of the unit interval. -/
def samplingDistance (s : ℝ) : ℝ := min s (1-s)

def samplingWeight (triangular : Bool) (h α s t : ℝ) : ℝ :=
  if triangular then
    if 0 < t ∧ t < 1-s then 1 else 0
  else
    if α ≤ samplingDistance s ∧ 0 < t ∧ t < h*samplingDistance s then
      1/(h*samplingDistance s)
    else 0

theorem samplingWeight_bounds (triangular : Bool) (h α s t : ℝ) (hh : 0 < h) (hα : 0 < α) :
    0 ≤ samplingWeight triangular h α s t ∧
      samplingWeight triangular h α s t ≤ max 1 (1/(h*α)) := by
  cases triangular
  · unfold samplingWeight
    simp only [Bool.false_eq_true,ite_false]
    split_ifs with hc
    · have hd : 0 < samplingDistance s := hα.trans_le hc.1
      exact ⟨by positivity, (one_div_le_one_div_of_le (mul_pos hh hα)
        (mul_le_mul_of_nonneg_left hc.1 hh.le)).trans (le_max_right _ _)⟩
    · exact ⟨le_rfl,le_trans (by norm_num) (le_max_left _ _)⟩
  · unfold samplingWeight
    simp only [ite_true]
    split_ifs <;> constructor <;> first | positivity | exact le_max_left _ _

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_OrbitSampling_Weights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Finset Filter
open scoped ENNReal
noncomputable section

def sourceSamplingWidth (s : ℕ) : ℝ := (sourceBlockSize s : ℝ)^(-3/5 : ℝ)
def sourceSamplingCutoff (s : ℕ) : ℝ := (sourceBlockSize s : ℝ)^(-2 : ℝ)
def sourceSamplingPrefix (s : ℕ) : Finset SourceCoordinate :=
  CouplingParameters.blockPrefix sourceBlockSize (s+1)

theorem sourceSampling_parameters (s : ℕ) :
    0 < sourceSamplingWidth s ∧ sourceSamplingWidth s < 1 ∧ 0 < sourceSamplingCutoff s := by
  have hm : (100 : ℝ) ≤ sourceBlockSize s := by exact_mod_cast (sourceStage s).m_ge_100
  refine ⟨by unfold sourceSamplingWidth; positivity, ?_, by unfold sourceSamplingCutoff; positivity⟩
  exact Real.rpow_lt_one_of_one_lt_of_neg (by linarith) (by norm_num)

theorem sourceSampling_weight_bound (s : ℕ) (triangular : Bool) (x t : ℝ) :
    0 ≤ samplingWeight triangular (sourceSamplingWidth s) (sourceSamplingCutoff s) x t ∧
      samplingWeight triangular (sourceSamplingWidth s) (sourceSamplingCutoff s) x t ≤
        (sourceBlockSize s : ℝ)^(13/5 : ℝ) := by
  have hp := sourceSampling_parameters s
  have hb := samplingWeight_bounds triangular _ _ x t hp.1 hp.2.2
  refine ⟨hb.1,hb.2.trans ?_⟩
  have hm := sourceBlockSize_pos s
  have hm1 : (1 : ℝ) ≤ sourceBlockSize s := by
    have hh : (100 : ℝ) ≤ sourceBlockSize s := by exact_mod_cast (sourceStage s).m_ge_100
    linarith
  apply max_le
  · exact Real.one_le_rpow hm1 (by norm_num)
  · unfold sourceSamplingWidth sourceSamplingCutoff
    rw [← Real.rpow_add hm]
    norm_num
    rw [Real.rpow_neg hm.le,inv_inv]

def sourceSamplingWeight (I : Finset SourceCoordinate) (s : ℕ)
    (θ : SourceCoordinate → ℝ) (n : ℤ) (x : SourceCoordinate → ℝ) : ℝ :=
  ∏ i ∈ sourceSamplingPrefix s,
    samplingWeight (decide (i ∈ I)) (sourceSamplingWidth s) (sourceSamplingCutoff s)
      (x i) (Int.fract ((n : ℝ)*θ i))

theorem sourceSamplingWeight_bounds (I : Finset SourceCoordinate) (s : ℕ)
    (θ : SourceCoordinate → ℝ) (n : ℤ) (x : SourceCoordinate → ℝ) :
    0 ≤ sourceSamplingWeight I s θ n x ∧ sourceSamplingWeight I s θ n x ≤
      ((sourceBlockSize s : ℝ)^(13/5 : ℝ))^(sourceSamplingPrefix s).card := by
  constructor
  · exact prod_nonneg (fun i hi => (sourceSampling_weight_bound s _ _ _).1)
  · unfold sourceSamplingWeight
    calc
      _ ≤ ∏ _i ∈ sourceSamplingPrefix s, (sourceBlockSize s : ℝ)^(13/5 : ℝ) :=
        prod_le_prod (fun i hi => (sourceSampling_weight_bound s _ _ _).1)
          (fun i hi => (sourceSampling_weight_bound s _ _ _).2)
      _ = _ := by simp

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_OrbitSampling_Measures
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Finset Filter
open scoped ENNReal
noncomputable section

abbrev sourceSamplingHaar : Measure (SourceCoordinate → ℝ) :=
  Measure.infinitePi (fun _ : SourceCoordinate => unitIntervalMeasure)

def sourceSamplingWeightedMeasure (I : Finset SourceCoordinate) (s : ℕ)
    (θ : SourceCoordinate → ℝ) (n : ℤ) : Measure (SourceCoordinate → ℝ) :=
  sourceSamplingHaar.withDensity (fun x => ENNReal.ofReal (sourceSamplingWeight I s θ n x))

instance sourceSamplingWeightedMeasure_finite (I : Finset SourceCoordinate) (s : ℕ)
    (θ : SourceCoordinate → ℝ) (n : ℤ) : IsFiniteMeasure (sourceSamplingWeightedMeasure I s θ n) := by
  apply isFiniteMeasure_withDensity
  let C := ((sourceBlockSize s : ℝ)^(13/5 : ℝ))^(sourceSamplingPrefix s).card
  have hh : (∫⁻ x, ENNReal.ofReal (sourceSamplingWeight I s θ n x) ∂sourceSamplingHaar) ≤ ENNReal.ofReal C := by
    calc
      _ ≤ ∫⁻ _x, ENNReal.ofReal C ∂sourceSamplingHaar :=
        lintegral_mono (fun x => ENNReal.ofReal_le_ofReal (sourceSamplingWeight_bounds I s θ n x).2)
      _ = _ := by simp
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hh

def sourceSamplingSummand (I : Finset SourceCoordinate) (s : ℕ)
    (θ : SourceCoordinate → ℝ) (n : ℤ) :
    Measure ((SourceCoordinate → ℝ) × (SourceCoordinate → ℝ)) :=
  (sourceSamplingWeightedMeasure I s θ n).map (fun x => (x,coordinateRotate θ n x))

instance sourceSamplingSummand_finite (I : Finset SourceCoordinate) (s : ℕ)
    (θ : SourceCoordinate → ℝ) (n : ℤ) : IsFiniteMeasure (sourceSamplingSummand I s θ n) := by
  unfold sourceSamplingSummand
  infer_instance

/-- Finite positive untrimmed measures averaged over the constructed powers.
No weak limit or uniform marginal bound is asserted by this definition. -/
def sourceSamplingUntrimmed (I : Finset SourceCoordinate) (s : ℕ) (θ : SourceCoordinate → ℝ) :
    Measure ((SourceCoordinate → ℝ) × (SourceCoordinate → ℝ)) :=
  ENNReal.ofReal (1/((sourceSamplingPowers s).card : ℝ)) •
    ∑ n ∈ sourceSamplingPowers s, sourceSamplingSummand I s θ n

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_Sampling_Transport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory
open scoped ENNReal
noncomputable section

/-- The uncut diagonal model moves z by v times its endpoint distance. -/
def samplingTransport (v z : ℝ) : ℝ := z+v*samplingDistance z

/-- Exact density of the two affine branches of the uncut transport. -/
def samplingTransportDensity (v s : ℝ) : ℝ :=
  if s ≤ (1+v)/2 then 1/(1+v) else 1/(1-v)

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_Sampling_SecondMoment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal
noncomputable section

def samplingVelocityMeasure (h : ℝ) : Measure ℝ := cond volume (Set.Ioc (0 : ℝ) h)

/-- Actual averaged density of the uncut diagonal transport. -/
def samplingIdealSecond (h s : ℝ) : ℝ :=
  ∫ v, samplingTransportDensity v s ∂samplingVelocityMeasure h

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_Sampling_SecondDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal
noncomputable section

def samplingSecondWeight (h α s t : ℝ) : ℝ :=
  samplingWeight false h α (Int.fract (s-t)) t

def samplingSecondDensity (h α s : ℝ) : ℝ :=
  ∫ t, samplingSecondWeight h α s t ∂unitIntervalMeasure

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_Sampling_TestedSecondMoment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal
noncomputable section

/-- Exact x- and y-tests in the second diagonal orientation. -/
def samplingTestedSecondWeight (h α : ℝ) (E G : Set ℝ) (s t : ℝ) : ℝ := by
  classical
  exact if Int.fract (s-t) ∈ E ∧ s ∈ G then samplingSecondWeight h α s t else 0

def samplingTestedSecondDensity (h α : ℝ) (E G : Set ℝ) (s : ℝ) : ℝ :=
  ∫ t, samplingTestedSecondWeight h α E G s t ∂unitIntervalMeasure

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_Sampling_TestedFirstMoment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
noncomputable section

def samplingTestedFirstWeight (b : Bool) (h α : ℝ) (E G : Set ℝ) (s t : ℝ) : ℝ := by
  classical
  exact if s ∈ E ∧ Int.fract (s+t) ∈ G then samplingWeight b h α s t else 0

def samplingTestedFirstDensity (b : Bool) (h α : ℝ) (E G : Set ℝ) (s : ℝ) : ℝ :=
  ∫ t, samplingTestedFirstWeight b h α E G s t ∂unitIntervalMeasure

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_Sampling_OrientedMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
noncomputable section

/-- Both source orientations and both coordinate types, with exact x/y tests. -/
def samplingOrientedWeight (second triangular : Bool) (h α : ℝ) (E G : Set ℝ) (s t : ℝ) : ℝ := by
  classical
  exact if second then
    if Int.fract (s-t) ∈ E ∧ s ∈ G then samplingWeight triangular h α (Int.fract (s-t)) t else 0
  else samplingTestedFirstWeight triangular h α E G s t

def samplingOrientedDensity (second triangular : Bool) (h α : ℝ) (E G : Set ℝ) (s : ℝ) : ℝ :=
  ∫ t, samplingOrientedWeight second triangular h α E G s t ∂unitIntervalMeasure

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_Sampling_FirstInterval
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped Classical
noncomputable section

def samplingFirstLength (b : Bool) (h s : ℝ) : ℝ :=
  if b then 1-s else h*samplingDistance s

def samplingFirstHeight (b : Bool) (h α s : ℝ) : ℝ :=
  if b then 1 else if α ≤ samplingDistance s then 1/(h*samplingDistance s) else 0

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_Sampling_IntervalSums
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped Classical ENNReal
noncomputable section

def samplingClosedIndicator (a b t : ℝ) : ℝ :=
  (Set.Icc a b).indicator (fun _ => 1) t

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_Sampling_SecondInterval
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped Classical
noncomputable section

def samplingSecondLength (h s : ℝ) : ℝ := min (h*s/(1+h)) (h*(1-s)/(1-h))

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_Sampling_SecondLevels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped Classical
noncomputable section

/-- The two closed intervals representing a positive superlevel of the
second-oriented tested reciprocal. Endpoint changes are dealt with separately. -/
def samplingSecondLevelLeft (h α a c s r : ℝ) : Set ℝ :=
  Set.Icc (max 0 (max (s-(1-α)) (s-c)))
    (min (min (min (samplingSecondLength h s) (min (s-α) (s-a))) (s-1/2)) (s-1+1/(h*r)))

def samplingSecondLevelRight (h α a c s r : ℝ) : Set ℝ :=
  Set.Icc (max (max (max 0 (max (s-(1-α)) (s-c))) (s-1/2)) (s-1/(h*r)))
    (min (samplingSecondLength h s) (min (s-α) (s-a)))

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_OrbitSampling_RationalTests
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter Finset
open scoped Classical ENNReal Topology
noncomputable section

/-- A finite rational cylinder test, with two closed intervals per tested
coordinate. Whole-circle tests fill the remaining coordinates. -/
abbrev SourceSamplingRationalTest :=
  Σ K : Finset SourceCoordinate, K → (ℚ × ℚ) × (ℚ × ℚ)

instance instCountableSourceSamplingRationalTest : Countable SourceSamplingRationalTest := inferInstance

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_OrbitSampling_LimitMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter Finset
open scoped Classical ENNReal Topology
noncomputable section

abbrev sourceSamplingPairHaar : Measure (SourceCoordinate → ℝ × ℝ) :=
  Measure.infinitePi (fun _ : SourceCoordinate => unitIntervalMeasure.prod unitIntervalMeasure)

def sourceSamplingTriangleSet (I : Finset SourceCoordinate) : Set (SourceCoordinate → ℝ × ℝ) :=
  {p | ∀ i ∈ I, (p i).1 < (p i).2}

def sourceSamplingLimitMap (I : Finset SourceCoordinate) (p : SourceCoordinate → ℝ × ℝ) :
    (SourceCoordinate → ℝ) × (SourceCoordinate → ℝ) :=
  (fun i => (p i).1,fun i => if i ∈ I then (p i).2 else (p i).1)

def sourceSamplingLambda (I : Finset SourceCoordinate) :
    Measure ((SourceCoordinate → ℝ) × (SourceCoordinate → ℝ)) :=
  (sourceSamplingPairHaar.restrict (sourceSamplingTriangleSet I)).map (sourceSamplingLimitMap I)

instance sourceSamplingLambda_finite (I : Finset SourceCoordinate) : IsFiniteMeasure (sourceSamplingLambda I) := by
  unfold sourceSamplingLambda
  infer_instance

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_OrbitSampling_Cube
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter Finset
open scoped Classical ENNReal Topology
noncomputable section

abbrev SourceSamplingPair := (SourceCoordinate → ℝ) × (SourceCoordinate → ℝ)

instance sourceSamplingUntrimmed_finite (I : Finset SourceCoordinate) (s : ℕ)
    (θ : SourceCoordinate → ℝ) : IsFiniteMeasure (sourceSamplingUntrimmed I s θ) := by
  constructor
  unfold sourceSamplingUntrimmed
  rw [Measure.smul_apply, smul_eq_mul]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_OrbitSampling_WeakLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter Finset
open scoped Classical ENNReal Topology
noncomputable section

def sourceSamplingLambdaFinite (I : Finset SourceCoordinate) : FiniteMeasure SourceSamplingPair :=
  ⟨sourceSamplingLambda I,inferInstance⟩

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_OrbitSampling_CompactTorus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter Finset
open scoped Classical ENNReal Topology
noncomputable section

abbrev SourceSamplingTorus := (SourceCoordinate → UnitAddCircle) × (SourceCoordinate → UnitAddCircle)

def sourceSamplingTorusMap (p : SourceSamplingPair) : SourceSamplingTorus :=
  (fun i => (p.1 i : UnitAddCircle),fun i => (p.2 i : UnitAddCircle))

def sourceSamplingLambdaTorus (I : Finset SourceCoordinate) : FiniteMeasure SourceSamplingTorus :=
  (sourceSamplingLambdaFinite I).map sourceSamplingTorusMap

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_TorusModel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal Classical
noncomputable section

abbrev SourceTorus := SourceCoordinate → UnitAddCircle
abbrev sourceTorusHaar : Measure SourceTorus :=
  Measure.infinitePi (fun _ : SourceCoordinate => (volume : Measure UnitAddCircle))

instance sourceUnitCircle_probability : IsProbabilityMeasure (volume : Measure UnitAddCircle) := by
  rw [← sourceCircle_mk_preserving.map_eq]
  exact Measure.isProbabilityMeasure_map sourceCircle_mk_preserving.measurable.aemeasurable

def sourceTorusRepresentative (z : SourceTorus) : SourceCoordinate → ℝ :=
  fun i => sourceCircleRepresentative (z i)

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_OrbitSampling_OrderedRestriction
attribute [-instance] _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter Finset
open scoped Classical ENNReal Topology
noncomputable section

def sourceSamplingOrdered : Set SourceSamplingPair := {p | ∀ i, p.1 i ≤ p.2 i}

/-- The actual ordered restriction of the already constructed average. -/
def sourceSamplingTrimmed (I : Finset SourceCoordinate) (s : ℕ) (θ : SourceCoordinate → ℝ) :
    Measure SourceSamplingPair := (sourceSamplingUntrimmed I s θ).restrict sourceSamplingOrdered

instance sourceSamplingTrimmed_finite (I : Finset SourceCoordinate) (s : ℕ)
    (θ : SourceCoordinate → ℝ) : IsFiniteMeasure (sourceSamplingTrimmed I s θ) := by
  unfold sourceSamplingTrimmed
  infer_instance

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_OrbitSampling_TrimmedWeak
attribute [-instance] _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter Finset
open scoped Classical ENNReal Topology
noncomputable section

def sourceSamplingTrimmedFinite (I : Finset SourceCoordinate) (s : ℕ)
    (θ : SourceCoordinate → ℝ) : FiniteMeasure SourceSamplingPair :=
  ⟨sourceSamplingTrimmed I s θ,inferInstance⟩

def sourceSamplingTrimmedTorus (I : Finset SourceCoordinate) (s : ℕ)
    (θ : SourceCoordinate → ℝ) : FiniteMeasure SourceSamplingTorus :=
  (sourceSamplingTrimmedFinite I s θ).map sourceSamplingTorusMap

def finiteMeasureRestrict {Ω : Type*} [MeasurableSpace Ω]
    (μ : FiniteMeasure Ω) (A : Set Ω) : FiniteMeasure Ω :=
  ⟨(μ : Measure Ω).restrict A,inferInstance⟩

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_OrbitSampling_TorusMarginals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal
noncomputable section

def sourceTorusEndpoint (r : Bool) (p : SourceSamplingTorus) : SourceTorus := if r then p.2 else p.1

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_BiasedPairs_Measures
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter CouplingParameters
open scoped ENNReal Topology
noncomputable section

abbrev SourceBiasedSample := SourceCoordinate → Fin 6 × (ℝ × ℝ)
abbrev sourceBiasedLaw (j : ℕ) : Measure SourceBiasedSample :=
  blockProductCoupling (stagedCouplingParameters j) sourceBlockSize

def sourceBiasedEndpoint (r : SourceCoordinate → Bool) : SourceBiasedSample → (SourceCoordinate → ℝ) :=
  blockProductEndpoint r

theorem sourceBiasedEndpoint_measurable (r : SourceCoordinate → Bool) :
    Measurable (sourceBiasedEndpoint r) := vectorEndpoint_measurable r

/-- The mixed pair has the original x endpoint and selects x or y coordinatewise. -/
def sourceBiasedPair (r : SourceCoordinate → Bool) (ω : SourceBiasedSample) : SourceSamplingPair :=
  (sourceBiasedEndpoint (fun _ => false) ω,sourceBiasedEndpoint r ω)

theorem sourceBiasedPair_measurable (r : SourceCoordinate → Bool) : Measurable (sourceBiasedPair r) :=
  (sourceBiasedEndpoint_measurable _).prodMk (sourceBiasedEndpoint_measurable _)

def sourceBiasedRealMeasure (j : ℕ) (r : SourceCoordinate → Bool) : Measure SourceSamplingPair :=
  (sourceBiasedLaw j).map (sourceBiasedPair r)

instance sourceBiasedRealMeasure_probability (j : ℕ) (r : SourceCoordinate → Bool) :
    IsProbabilityMeasure (sourceBiasedRealMeasure j r) :=
  Measure.isProbabilityMeasure_map (sourceBiasedPair_measurable r).aemeasurable

def sourceBiasedTorusMeasure (j : ℕ) (r : SourceCoordinate → Bool) : FiniteMeasure SourceSamplingTorus :=
  ⟨(sourceBiasedRealMeasure j r).map sourceSamplingTorusMap,by infer_instance⟩

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_BiasedPairs_PrefixLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
noncomputable section

/-- At prefix n, use y in the first n source blocks and x in the tail. -/
def sourceBiasedPrefixMask (n : ℕ) (i : SourceCoordinate) : Bool := decide (i.1 < n)

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_Coupling_FinitePosteriorAC
attribute [-instance] _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory ProbabilityTheory
open scoped ENNReal
noncomputable section
namespace CouplingParameters

/-- A normalized reference law allowing either a diagonal or a Haar draw. -/
def diagonalHaarReference (t : ℝ) : Measure ℝ :=
  (2 : ℝ≥0∞)⁻¹ • (Measure.dirac t + unitIntervalMeasure)

instance diagonalHaarReference_probability (t : ℝ) :
    IsProbabilityMeasure (diagonalHaarReference t) := by
  constructor
  simpa [diagonalHaarReference,Measure.smul_apply,Measure.add_apply,measure_univ] using ENNReal.inv_two_add_inv_two

end CouplingParameters
end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_Coupling_FiniteDisintegration
attribute [-instance] _root_.OAI.FiniteFactor.CouplingParameters.blockProductCoupling_probability _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory ProbabilityTheory
open scoped ENNReal
noncomputable section
namespace CouplingParameters

/-- The mixed posterior keeps every unselected coordinate fixed. -/
def mixedPosteriorKernel {ι : Type*} (p : ι → CouplingParameters) (r : ι → Bool) :
    Kernel (ι → ℝ) (ι → ℝ) := by
  letI : ∀ i, IsMarkovKernel (if r i then (p i).posteriorKernel false else Kernel.id) :=
    fun i => by split_ifs <;> infer_instance
  exact independentKernel (fun i => if r i then (p i).posteriorKernel false else Kernel.id)

instance mixedPosteriorKernel_markov {ι : Type*} (p : ι → CouplingParameters) (r : ι → Bool) :
    IsMarkovKernel (mixedPosteriorKernel p r) := by
  unfold mixedPosteriorKernel
  let : ∀ i, IsMarkovKernel (if r i then (p i).posteriorKernel false else Kernel.id) :=
    fun i => by split_ifs <;> infer_instance
  infer_instance

end CouplingParameters
end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_BiasedPairs_ReferenceDomination
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory ProbabilityTheory CouplingParameters
open scoped ENNReal
noncomputable section

def sourceDiagonalHaarKernel : Kernel ℝ ℝ where
  toFun := diagonalHaarReference
  measurable' := by
    apply Measure.measurable_of_measurable_coe
    intro S hS
    simp only [diagonalHaarReference,Measure.smul_apply,Measure.add_apply,smul_eq_mul]
    exact measurable_const.mul (((Measure.measurable_coe hS).comp Measure.measurable_dirac).add measurable_const)

instance sourceDiagonalHaarKernel_markov : IsMarkovKernel sourceDiagonalHaarKernel :=
  ⟨fun t => diagonalHaarReference_probability t⟩

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_BoundedMatrixOperator
attribute [-instance] _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open Filter
open scoped ENNReal Topology
noncomputable section

abbrev SourceFiberHilbert := lp (fun _ : ℤ => ℂ) 2

/-- Canonical inclusion of finite coordinate vectors in l2(Z). -/
def fiberFiniteEmbedding : (ℤ →₀ ℂ) →ₗ[ℂ] SourceFiberHilbert :=
  Finsupp.linearCombination ℂ (fun n => lp.single 2 n (1 : ℂ))

/-- The algebraic action of a matrix on finite vectors. -/
def fiberMatrixLinear (m : ℤ → ℤ → ℂ) : (ℤ →₀ ℂ) →ₗ[ℂ] (ℤ → ℂ) :=
  Finsupp.linearCombination ℂ (fun n k => m k n)

theorem fiberMatrixLinear_apply (m : ℤ → ℤ → ℂ) (a : ℤ →₀ ℂ) (k : ℤ) :
    fiberMatrixLinear m a k = ∑ n ∈ a.support, a n * m k n := by
  simp [fiberMatrixLinear, Finsupp.linearCombination_apply, Finsupp.sum, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul]

variable (m : ℤ → ℤ → ℂ) (C : ℝ)
variable (hb : ∀ (s t : Finset ℤ) (a : ℤ → ℂ),
  (∑ k ∈ t, ‖∑ n ∈ s, a n * m k n‖ ^ 2) ≤ C ^ 2 * ∑ n ∈ s, ‖a n‖ ^ 2)

include C hb in
theorem fiberMatrixLinear_mem (a : ℤ →₀ ℂ) : Memℓp (fiberMatrixLinear m a) 2 := by
  apply memℓp_gen' (C := C ^ 2 * ∑ n ∈ a.support, ‖a n‖ ^ 2)
  intro t
  simpa [fiberMatrixLinear_apply] using hb a.support t a

/-- The finite matrix action takes values in actual l2, by the finite-sum bound. -/
def fiberMatrixFinite : (ℤ →₀ ℂ) →ₗ[ℂ] SourceFiberHilbert where
  toFun a := ⟨fiberMatrixLinear m a, fiberMatrixLinear_mem m C hb a⟩
  map_add' a b := by apply Subtype.ext; exact map_add (fiberMatrixLinear m) a b
  map_smul' c a := by apply Subtype.ext; exact map_smul (fiberMatrixLinear m) c a

/-- Extension of the bounded finite matrix action to every l2 vector. -/
def boundedMatrixOperator : SourceFiberHilbert →L[ℂ] SourceFiberHilbert :=
  (fiberMatrixFinite m C hb).extendOfNorm fiberFiniteEmbedding

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_Contradiction
attribute [-instance] _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped Topology

noncomputable def coefficientMass (K : ℕ) (A B : ℤ → ℂ) : ℝ :=
  ∑ n ∈ Finset.range (2*K+1), ‖laurentProductCoefficient K A B (-(n : ℤ))‖

end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_Convolution
attribute [-instance] _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open scoped ComplexConjugate ENNReal

/-- Exact rescaling used in coefficient-sequences; neither sequence is required
 to belong to ℓ². -/
noncomputable def leftCoefficient (F : ℤ → ℝ) (ξ : ℤ → ℂ) (v : ℤ) : ℂ :=
  ξ v / (F v : ℂ)

noncomputable def rightCoefficient (G : ℤ → ℝ) (γ : ℤ → ℂ) (v : ℤ) : ℂ :=
  (G (-v) : ℂ) * conj (γ (-v))

/-- The deterministic omitted-index choice used for both complementary masks. -/
def omittedIndex (K : ℕ) (n v : ℤ) : ℤ :=
  if (K : ℤ) < |v| then v else n+v

end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_Coupling_Noncrossing
attribute [-instance] _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory ProbabilityTheory Filter Finset
open scoped ENNReal
noncomputable section
namespace CouplingParameters

/-- The interval in which the unconditioned partner crosses an eligible threshold. -/
def crossingPartner (right : Bool) (u : ℝ) : Set ℝ :=
  if right then Set.Iio u else Set.Ici u

end CouplingParameters
end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_Coupling_BadEvents
attribute [-instance] _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory ProbabilityTheory Filter Finset
open scoped ENNReal
noncomputable section
namespace CouplingParameters

def eligible (right : Bool) (x u : ℝ) : Prop := if right then u ≤ x else x < u

instance eligible_decidable (right : Bool) (x u : ℝ) : Decidable (eligible right x u) := by
  unfold eligible
  infer_instance

def eligibleIndices {ι : Type*} (right : ι → Bool) (x u : ι → ℝ) (I : Finset ι) : Finset ι :=
  I.filter (fun i => eligible (right i) (x i) (u i))

/-- A measurable half of the noncrossing event, with the eligibility count
read from the conditioning vector. Taking right=false or right=true gives
the two orientations used in the contradiction. -/
def badHalfEvent {ι : Type*} (right : ι → Bool) (u : ι → ℝ) (I : Finset ι) (q : ℝ) :
    Set ((ι → ℝ) × (ι → ℝ)) :=
  {z | q/2 ≤ ((eligibleIndices right z.1 u I).card : ℝ) ∧
    ∀ i : I, ¬(eligible (right i) (z.1 i) (u i) ∧ z.2 i ∈ crossingPartner (right i) (u i))}

end CouplingParameters
end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_GeneratedAlgebra
attribute [-instance] _root_.OAI.FiniteFactor.sourceAngleMarginal_atomless _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceSamplingLambda_finite _root_.OAI.FiniteFactor.sourceSamplingSummand_finite _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingUntrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingWeightedMeasure_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal Pointwise
noncomputable section

/-- A bounded Borel function on the source cube. Values outside the cube
are irrelevant because the representation evaluates rotation representatives. -/
structure SourceBaseFunction where
  toFun : (SourceCoordinate → ℝ) → ℂ
  measurable : Measurable toFun
  bound : ℝ
  bound_nonneg : 0 ≤ bound
  norm_le : ∀ x, (∀ i, x i ∈ Set.Ico 0 1) → ‖toFun x‖ ≤ bound

def sourcePiSymbol (θ : SourceCoordinate → ℝ) (g : SourceBaseFunction)
    (z : (SourceCoordinate → ℝ) × ℤ) : ℂ := g.toFun (coordinateRotate θ z.2 z.1)

theorem sourcePiSymbol_measurable (θ : SourceCoordinate → ℝ) (g : SourceBaseFunction) :
    Measurable (sourcePiSymbol θ g) := by
  apply g.measurable.comp
  apply Measurable.of_eval
  intro i
  unfold coordinateRotate
  fun_prop

theorem sourcePiSymbol_bound (θ : SourceCoordinate → ℝ) (g : SourceBaseFunction) (z) :
    ‖sourcePiSymbol θ g z‖ ≤ g.bound :=
  g.norm_le _ (fun _ => ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩)

theorem sourcePiSymbol_memLp (θ : SourceCoordinate → ℝ) (g : SourceBaseFunction) :
    MemLp (sourcePiSymbol θ g) ∞ (sourceMeasure SourceCoordinate) :=
  memLp_top_of_bound (sourcePiSymbol_measurable θ g).aestronglyMeasurable g.bound
    (Eventually.of_forall (sourcePiSymbol_bound θ g))

def sourcePi (θ : SourceCoordinate → ℝ) (g : SourceBaseFunction) :
    SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate :=
  (ContinuousLinearMap.mul ℂ ℂ).holderL (sourceMeasure SourceCoordinate) ∞ 2 2
    ((sourcePiSymbol_memLp θ g).toLp (sourcePiSymbol θ g))

theorem sourcePi_apply_ae (θ : SourceCoordinate → ℝ) (g : SourceBaseFunction)
    (f : SourceHilbert SourceCoordinate) :
    sourcePi θ g f =ᵐ[sourceMeasure SourceCoordinate] fun z => sourcePiSymbol θ g z * f z := by
  have hh := (ContinuousLinearMap.mul ℂ ℂ).coeFn_holder
    ((sourcePiSymbol_memLp θ g).toLp (sourcePiSymbol θ g)) f (r := 2)
  filter_upwards [hh, (sourcePiSymbol_memLp θ g).coeFn_toLp] with z hz hg
  simpa [sourcePi, hg] using hz

/-- Double commutant of a concrete family, including its adjoints. -/
def sourceGeneratedVonNeumann {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (S : Set (H →L[ℂ] H)) : VonNeumannAlgebra H where
  toStarSubalgebra := StarSubalgebra.centralizer ℂ (StarSubalgebra.centralizer ℂ S)
  centralizer_centralizer' := by
    have he : (StarSubalgebra.centralizer ℂ (StarSubalgebra.centralizer ℂ S)).carrier =
        Set.centralizer (Set.centralizer (S ∪ star S)) :=
      StarSubalgebra.coe_centralizer_centralizer ℂ S
    rw [he]
    simp

/-- The actual generated algebra of the source regular representation.
Factor, trace, finiteness and predual properties are separate obligations. -/
def sourceAlgebra (θ : SourceCoordinate → ℝ) : VonNeumannAlgebra (SourceHilbert SourceCoordinate) :=
  sourceGeneratedVonNeumann ({sourceShift SourceCoordinate} ∪ Set.range (sourcePi θ))

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_MultiplicationAdjoint
attribute [-instance] _root_.OAI.FiniteFactor.sourceAngleMarginal_atomless _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceSamplingLambda_finite _root_.OAI.FiniteFactor.sourceSamplingSummand_finite _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingUntrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingWeightedMeasure_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal ComplexConjugate
noncomputable section

/-- Conjugate of a bounded source base function, with the same bound. -/
def sourceBaseStar (g : SourceBaseFunction) : SourceBaseFunction where
  toFun := fun x => star (g.toFun x)
  measurable := Complex.continuous_conj.measurable.comp g.measurable
  bound := g.bound
  bound_nonneg := g.bound_nonneg
  norm_le := by intro x hx; simpa using g.norm_le x hx

/-- The multiplication representation has the actual Hilbert adjoint. -/
theorem sourcePi_star (θ : SourceCoordinate → ℝ) (g : SourceBaseFunction) :
    star (sourcePi θ g) = sourcePi θ (sourceBaseStar g) := by
  rw [ContinuousLinearMap.star_eq_adjoint]
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro f h
  change (∫ z, inner ℂ ((sourcePi θ (sourceBaseStar g) f) z) (h z) ∂sourceMeasure SourceCoordinate) =
    ∫ z, inner ℂ (f z) ((sourcePi θ g h) z) ∂sourceMeasure SourceCoordinate
  apply integral_congr_ae
  filter_upwards [sourcePi_apply_ae θ (sourceBaseStar g) f,
    sourcePi_apply_ae θ g h] with z hf hh
  rw [hf, hh]
  simp [sourcePiSymbol, sourceBaseStar, RCLike.inner_apply, mul_comm, mul_left_comm, mul_assoc]

/-- Any two such multiplication operators commute, even for different angles. -/
theorem sourcePi_commute (θ φ : SourceCoordinate → ℝ) (g h : SourceBaseFunction) :
    sourcePi θ g * sourcePi φ h = sourcePi φ h * sourcePi θ g := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [sourcePi_apply_ae θ g (sourcePi φ h f),
    sourcePi_apply_ae φ h f, sourcePi_apply_ae φ h (sourcePi θ g f),
    sourcePi_apply_ae θ g f] with z hg hh hg' hh'
  change (sourcePi θ g (sourcePi φ h f)) z = (sourcePi φ h (sourcePi θ g f)) z
  rw [hg, hh, hg', hh']
  ring

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_ScalarCommutant
attribute [-instance] _root_.OAI.FiniteFactor.sourceAngleMarginal_atomless _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceSamplingLambda_finite _root_.OAI.FiniteFactor.sourceSamplingSummand_finite _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingUntrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingWeightedMeasure_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
noncomputable section

/-- Scalar base multiplication, independent of the fiber coordinate. -/
def sourceScalar (g : SourceBaseFunction) :
    SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate :=
  sourcePi (fun _ => 0) g

theorem sourceScalar_star (g : SourceBaseFunction) :
    star (sourceScalar g) = sourceScalar (sourceBaseStar g) :=
  sourcePi_star _ _

theorem sourceShift_apply_ae (f : SourceHilbert SourceCoordinate) :
    sourceShift SourceCoordinate f =ᵐ[sourceMeasure SourceCoordinate]
      fun z => f (sourceShiftIndex z) :=
  Lp.coeFn_compMeasurePreserving f (sourceShiftIndex_preserving _)

theorem sourceScalar_shift_commute (g : SourceBaseFunction) :
    sourceScalar g * sourceShift SourceCoordinate =
      sourceShift SourceCoordinate * sourceScalar g := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  have hg := (sourceShiftIndex_preserving SourceCoordinate).quasiMeasurePreserving.ae
    (sourcePi_apply_ae (fun _ => 0) g f)
  filter_upwards [sourcePi_apply_ae (fun _ => 0) g (sourceShift SourceCoordinate f),
    sourceShift_apply_ae f, sourceShift_apply_ae (sourceScalar g f), hg] with z h1 h2 h3 h4
  change (sourcePi (fun _ => 0) g (sourceShift SourceCoordinate f)) z =
    (sourceShift SourceCoordinate (sourceScalar g f)) z
  rw [h1, h2, h3]
  change _ = (sourcePi (fun _ => 0) g f) (sourceShiftIndex z)
  rw [h4]
  have he : sourcePiSymbol (fun _ => 0) g z =
      sourcePiSymbol (fun _ => 0) g (sourceShiftIndex z) := by
    unfold sourcePiSymbol
    congr 1
    funext i
    simp [coordinateRotate, sourceShiftIndex]
  rw [he]

/-- The scalar multipliers commute with the generators and their adjoints. -/
theorem sourceScalar_mem_generator_commutant (θ : SourceCoordinate → ℝ)
    (g : SourceBaseFunction) :
    sourceScalar g ∈ StarSubalgebra.centralizer ℂ
      ({sourceShift SourceCoordinate} ∪ Set.range (sourcePi θ)) := by
  apply (StarSubalgebra.mem_centralizer_iff ℂ).mpr
  intro A hA
  rcases hA with hA | ⟨h, rfl⟩
  · obtain rfl : A = sourceShift SourceCoordinate := hA
    refine ⟨(sourceScalar_shift_commute g).symm, ?_⟩
    have hs := congrArg star (sourceScalar_shift_commute (sourceBaseStar g))
    have hg : star (sourceScalar (sourceBaseStar g)) = sourceScalar g := by
      rw [← sourceScalar_star, star_star]
    simpa only [star_mul, hg] using hs
  · exact ⟨sourcePi_commute θ _ h g, by
      rw [sourcePi_star]
      exact sourcePi_commute θ _ (sourceBaseStar h) g⟩

/-- The commutation holds for every element of the actual double commutant. -/
theorem sourceAlgebra_commutes_scalar (θ : SourceCoordinate → ℝ)
    {H : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate}
    (hH : H ∈ sourceAlgebra θ) (g : SourceBaseFunction) :
    sourceScalar g * H = H * sourceScalar g := by
  change H ∈ StarSubalgebra.centralizer ℂ
    (StarSubalgebra.centralizer ℂ
      ({sourceShift SourceCoordinate} ∪ Set.range (sourcePi θ))) at hH
  exact ((StarSubalgebra.mem_centralizer_iff ℂ).mp hH _
    (sourceScalar_mem_generator_commutant θ g)).1

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_Transport
attribute [-instance] _root_.OAI.FiniteFactor.sourceAngleMarginal_atomless _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceSamplingLambda_finite _root_.OAI.FiniteFactor.sourceSamplingSummand_finite _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingUntrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingWeightedMeasure_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
noncomputable section

/-- Combined integer base rotation and fiber translation. -/
def sourceTransportIndex (θ : SourceCoordinate → ℝ) (n m : ℤ)
    (z : (SourceCoordinate → ℝ) × ℤ) : (SourceCoordinate → ℝ) × ℤ :=
  (coordinateRotate θ n z.1, z.2 - m)

theorem sourceTransportIndex_preserving (θ : SourceCoordinate → ℝ) (n m : ℤ) :
    MeasurePreserving (sourceTransportIndex θ n m)
      (sourceMeasure SourceCoordinate) (sourceMeasure SourceCoordinate) := by
  have hm : Measurable (fun k : ℤ => k-m) := measurable_of_countable _
  have hi : Function.Injective (fun k : ℤ => k-m) := by intro a b h; dsimp at h; omega
  have hs : Function.Surjective (fun k : ℤ => k-m) := by intro k; exact ⟨k+m, by dsimp; omega⟩
  have hp : MeasurePreserving (fun k : ℤ => k-m) Measure.count Measure.count := by
    refine ⟨hm, ?_⟩
    ext S hS
    rw [Measure.map_apply hm hS, Measure.count_apply (hS.preimage hm), Measure.count_apply hS,
      ← hi.encard_image, Set.image_preimage_eq S hs]
  exact (coordinateRotate_preserving θ n).prod hp

def sourceTransport (θ : SourceCoordinate → ℝ) (n m : ℤ) :
    SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate :=
  (Lp.compMeasurePreservingₗᵢ ℂ (sourceTransportIndex θ n m)
    (sourceTransportIndex_preserving θ n m)).toContinuousLinearMap

theorem sourceTransport_apply_ae (θ : SourceCoordinate → ℝ) (n m : ℤ)
    (f : SourceHilbert SourceCoordinate) :
    sourceTransport θ n m f =ᵐ[sourceMeasure SourceCoordinate]
      fun z => f (sourceTransportIndex θ n m z) :=
  Lp.coeFn_compMeasurePreserving f (sourceTransportIndex_preserving θ n m)

theorem sourceTransport_mul (θ : SourceCoordinate → ℝ) (n m p q : ℤ) :
    sourceTransport θ n m * sourceTransport θ p q = sourceTransport θ (n+p) (m+q) := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  have ht := (sourceTransportIndex_preserving θ n m).quasiMeasurePreserving.ae
    (sourceTransport_apply_ae θ p q f)
  filter_upwards [sourceTransport_apply_ae θ n m (sourceTransport θ p q f),
    sourceTransport_apply_ae θ (n+p) (m+q) f, ht] with z h1 h2 h3
  change (sourceTransport θ n m (sourceTransport θ p q f)) z = _
  rw [h1, h2, h3]
  congr 1
  simp [sourceTransportIndex, coordinateRotate_add, sub_sub]

theorem sourceHilbert_cube : ∀ᵐ z ∂sourceMeasure SourceCoordinate,
    ∀ i, z.1 i ∈ Set.Ico (0 : ℝ) 1 := by
  have hc : ∀ᵐ x ∂Measure.infinitePi (fun _ : SourceCoordinate => unitIntervalMeasure),
      ∀ i, x i ∈ Set.Ico (0 : ℝ) 1 := by
    rw [ae_all_iff]
    intro i
    have hh : ∀ᵐ t ∂(Measure.infinitePi (fun _ : SourceCoordinate => unitIntervalMeasure)).map
        (fun x => x i), t ∈ Set.Ico (0 : ℝ) 1 := by
      rw [Measure.infinitePi_map_eval]
      exact ae_restrict_mem measurableSet_Ico
    exact (ae_map_iff (measurable_pi_apply i).aemeasurable measurableSet_Ico).mp hh
  exact Measure.quasiMeasurePreserving_fst.ae hc

theorem sourceTransport_zero (θ : SourceCoordinate → ℝ) : sourceTransport θ 0 0 = 1 := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [sourceTransport_apply_ae θ 0 0 f, sourceHilbert_cube] with z hz hc
  change (sourceTransport θ 0 0 f) z = f z
  rw [hz]
  congr 1
  apply Prod.ext
  · funext i
    simpa [sourceTransportIndex, coordinateRotate] using Int.fract_eq_self.mpr (hc i)
  · simp [sourceTransportIndex]

theorem sourceTransport_star (θ : SourceCoordinate → ℝ) (n m : ℤ) :
    star (sourceTransport θ n m) = sourceTransport θ (-n) (-m) := by
  have hi (f h : SourceHilbert SourceCoordinate) :
      inner ℂ (sourceTransport θ n m f) (sourceTransport θ n m h) = inner ℂ f h :=
    (Lp.compMeasurePreservingₗᵢ ℂ (sourceTransportIndex θ n m)
      (sourceTransportIndex_preserving θ n m)).inner_map_map f h
  have hinv : sourceTransport θ n m * sourceTransport θ (-n) (-m) = 1 := by
    rw [sourceTransport_mul]; simp only [add_neg_cancel, sourceTransport_zero]
  rw [ContinuousLinearMap.star_eq_adjoint]
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro f h
  have hih := hi (sourceTransport θ (-n) (-m) f) h
  have he : sourceTransport θ n m (sourceTransport θ (-n) (-m) f) = f := by
    change (sourceTransport θ n m * sourceTransport θ (-n) (-m)) f = f
    rw [hinv]; rfl
  rw [he] at hih
  exact hih.symm

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_RotationCommutant
attribute [-instance] _root_.OAI.FiniteFactor.sourceAngleMarginal_atomless _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceSamplingLambda_finite _root_.OAI.FiniteFactor.sourceSamplingSummand_finite _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingUntrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingWeightedMeasure_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
noncomputable section

def sourceCommutantRotation (θ : SourceCoordinate → ℝ) (n : ℤ) := sourceTransport θ n n

theorem sourceCommutantRotation_star (θ : SourceCoordinate → ℝ) (n : ℤ) :
    star (sourceCommutantRotation θ n) = sourceCommutantRotation θ (-n) :=
  sourceTransport_star θ n n

theorem sourceCommutantRotation_pi (θ : SourceCoordinate → ℝ) (n : ℤ)
    (g : SourceBaseFunction) :
    sourceCommutantRotation θ n * sourcePi θ g = sourcePi θ g * sourceCommutantRotation θ n := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  have ht := (sourceTransportIndex_preserving θ n n).quasiMeasurePreserving.ae
    (sourcePi_apply_ae θ g f)
  filter_upwards [sourceTransport_apply_ae θ n n (sourcePi θ g f),
    sourcePi_apply_ae θ g (sourceTransport θ n n f), sourceTransport_apply_ae θ n n f,
    ht] with z h1 h2 h3 h4
  change (sourceTransport θ n n (sourcePi θ g f)) z = (sourcePi θ g (sourceTransport θ n n f)) z
  rw [h1,h2,h3,h4]
  have he : sourcePiSymbol θ g (sourceTransportIndex θ n n z) = sourcePiSymbol θ g z := by
    unfold sourcePiSymbol sourceTransportIndex
    dsimp only
    rw [coordinateRotate_add]
    congr 2
    omega
  rw [he]

theorem sourceTransport_shift (θ : SourceCoordinate → ℝ) (n m : ℤ) :
    sourceTransport θ n m * sourceShift SourceCoordinate =
      sourceShift SourceCoordinate * sourceTransport θ n m := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  have ht := (sourceTransportIndex_preserving θ n m).quasiMeasurePreserving.ae
    (sourceShift_apply_ae f)
  have hs := (sourceShiftIndex_preserving SourceCoordinate).quasiMeasurePreserving.ae
    (sourceTransport_apply_ae θ n m f)
  filter_upwards [sourceTransport_apply_ae θ n m (sourceShift SourceCoordinate f),
    sourceShift_apply_ae (sourceTransport θ n m f), ht, hs] with z h1 h2 h3 h4
  change (sourceTransport θ n m (sourceShift SourceCoordinate f)) z =
    (sourceShift SourceCoordinate (sourceTransport θ n m f)) z
  rw [h1,h2,h3,h4]
  congr 1
  apply Prod.ext
  · rfl
  · dsimp [sourceTransportIndex, sourceShiftIndex]; omega

theorem sourceCommutantRotation_mem (θ : SourceCoordinate → ℝ) (n : ℤ) :
    sourceCommutantRotation θ n ∈ StarSubalgebra.centralizer ℂ
      ({sourceShift SourceCoordinate} ∪ Set.range (sourcePi θ)) := by
  apply (StarSubalgebra.mem_centralizer_iff ℂ).mpr
  intro A hA
  rcases hA with hA | ⟨g,rfl⟩
  · obtain rfl : A = sourceShift SourceCoordinate := hA
    refine ⟨(sourceTransport_shift θ n n).symm, ?_⟩
    have hs := congrArg star (sourceTransport_shift θ (-n) (-n))
    have he : star (sourceTransport θ (-n) (-n)) = sourceTransport θ n n := by
      rw [sourceTransport_star]; simp
    simpa only [star_mul, he, sourceCommutantRotation] using hs
  · exact ⟨(sourceCommutantRotation_pi θ n g).symm, by
      rw [sourcePi_star]
      exact (sourceCommutantRotation_pi θ n (sourceBaseStar g)).symm⟩

theorem sourceAlgebra_commutes_rotation (θ : SourceCoordinate → ℝ)
    {H : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate}
    (hH : H ∈ sourceAlgebra θ) (n : ℤ) :
    sourceCommutantRotation θ n * H = H * sourceCommutantRotation θ n := by
  change H ∈ StarSubalgebra.centralizer ℂ
    (StarSubalgebra.centralizer ℂ
      ({sourceShift SourceCoordinate} ∪ Set.range (sourcePi θ))) at hH
  exact ((StarSubalgebra.mem_centralizer_iff ℂ).mp hH _
    (sourceCommutantRotation_mem θ n)).1

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_OperatorUltraweak
attribute [-instance] _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace FiniteFactor
variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The actual ultraweak topology, generated by absolutely summable vector
functionals. No continuity of a chosen trace is built into this definition. -/
@[instance_reducible] def ultraweakTopology : TopologicalSpace (H →L[ℂ] H) :=
  ⨅ (ξ : ℕ → H) (η : ℕ → H) (_ : Summable (fun n => ‖ξ n‖ * ‖η n‖)),
    TopologicalSpace.induced (fun T : H →L[ℂ] H => ∑' n, inner ℂ (ξ n) (T (η n)))
      inferInstance

end FiniteFactor

end

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_VacuumFunctional
attribute [-instance] _root_.OAI.FiniteFactor.sourceAngleMarginal_atomless _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceSamplingLambda_finite _root_.OAI.FiniteFactor.sourceSamplingSummand_finite _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingUntrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingWeightedMeasure_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal
noncomputable section

/-- The constant e_0 field in the actual L2(X times Z) source model. -/
def sourceVacuum : SourceHilbert SourceCoordinate :=
  @indicatorConstLp ((SourceCoordinate → ℝ) × ℤ) ℂ
    (@Prod.instMeasurableSpace (SourceCoordinate → ℝ) ℤ
      (@MeasurableSpace.pi SourceCoordinate (fun _ => ℝ)
        (fun _ => Real.measurableSpace)) Int.instMeasurableSpace)
    (sourceMeasure SourceCoordinate) Complex.instNormedAddCommGroup
    (Set.univ ×ˢ {(0 : ℤ)})
    (@Nat.cast ENNReal
      (ENNReal.instAddCommMonoidWithOne.toAddMonoidWithOne.toNatCast)
      (Nat.succ (Nat.succ Nat.zero)))
    (MeasurableSet.univ.prod (measurableSet_singleton (0 : ℤ)))
    (letI : IsProbabilityMeasure unitIntervalMeasure :=
       ⟨(Measure.restrict_apply_univ
           (μ := (volume : Measure ℝ)) (Set.Ico (0 : ℝ) 1)).trans
         ((Real.volume_Ico (a := 0) (b := 1)).trans
           ((congrArg ENNReal.ofReal (sub_zero (1 : ℝ))).trans
             ENNReal.ofReal_one))⟩
     let base : Measure (SourceCoordinate → ℝ) :=
       Measure.infinitePi (fun _ : SourceCoordinate => unitIntervalMeasure)
     let mass_one :=
       (Measure.prod_prod (μ := base) (ν := (Measure.count : Measure ℤ))
         Set.univ {(0 : ℤ)}).trans
         ((congrArg₂ (fun left right : ℝ≥0∞ => left * right)
           (measure_univ (μ := base))
           (Measure.count_singleton (0 : ℤ))).trans (one_mul (1 : ℝ≥0∞)))
     fun mass_top => ENNReal.one_ne_top (mass_one.symm.trans mass_top)) (1 : ℂ)

@[instance_reducible] def sourceAlgebraUltraweakTopology (θ : SourceCoordinate → ℝ) :
    TopologicalSpace (sourceAlgebra θ).toStarSubalgebra :=
  TopologicalSpace.induced (fun T : (sourceAlgebra θ).toStarSubalgebra =>
    (T : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate))
    (ultraweakTopology (SourceHilbert SourceCoordinate))

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_FiberIndicators
attribute [-instance] _root_.OAI.FiniteFactor.sourceAngleMarginal_atomless _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceSamplingLambda_finite _root_.OAI.FiniteFactor.sourceSamplingSummand_finite _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingUntrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingWeightedMeasure_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal
noncomputable section

/-- Bounded measurable indicator on the base. -/
def sourceBaseIndicator (A : Set (SourceCoordinate → ℝ)) (hA : MeasurableSet A) :
    SourceBaseFunction where
  toFun := A.indicator (fun _ => (1 : ℂ))
  measurable := measurable_const.indicator hA
  bound := 1
  bound_nonneg := zero_le_one
  norm_le := by intro x _; by_cases hx : x ∈ A <;> simp [hx]

theorem sourceFiberMeasure_ne_top (A : Set (SourceCoordinate → ℝ)) (n : ℤ) :
    sourceMeasure SourceCoordinate (A ×ˢ {n}) ≠ ∞ := by
  rw [Measure.prod_prod]
  simp

def sourceFiberIndicator (A : Set (SourceCoordinate → ℝ)) (hA : MeasurableSet A) (n : ℤ) :
    SourceHilbert SourceCoordinate :=
  indicatorConstLp 2 (hA.prod (measurableSet_singleton n)) (sourceFiberMeasure_ne_top A n) (1 : ℂ)

theorem sourceFiberIndicator_coe (A : Set (SourceCoordinate → ℝ)) (hA : MeasurableSet A) (n : ℤ) :
    sourceFiberIndicator A hA n =ᵐ[sourceMeasure SourceCoordinate]
      (A ×ˢ {n}).indicator (fun _ => (1 : ℂ)) :=
  indicatorConstLp_coeFn

theorem sourceVacuum_coe : sourceVacuum =ᵐ[sourceMeasure SourceCoordinate]
    (Set.univ ×ˢ {(0 : ℤ)}).indicator (fun _ => (1 : ℂ)) :=
  indicatorConstLp_coeFn

/-- Every bounded base indicator on an arbitrary fiber is in the vacuum's
commutant orbit. No cyclicity or separating property is assumed. -/
theorem sourceFiberIndicator_eq_orbit (θ : SourceCoordinate → ℝ)
    (A : Set (SourceCoordinate → ℝ)) (hA : MeasurableSet A) (n : ℤ) :
    sourceFiberIndicator A hA n = sourceScalar (sourceBaseIndicator A hA)
      (sourceCommutantRotation θ n sourceVacuum) := by
  apply Lp.ext
  have hv := (sourceTransportIndex_preserving θ n n).quasiMeasurePreserving.ae sourceVacuum_coe
  filter_upwards [sourceFiberIndicator_coe A hA n, sourceHilbert_cube,
    sourcePi_apply_ae (fun _ => 0) (sourceBaseIndicator A hA)
      (sourceTransport θ n n sourceVacuum), sourceTransport_apply_ae θ n n sourceVacuum,
    hv] with z hi hc hs ht hv
  change (sourceFiberIndicator A hA n) z =
    (sourcePi (fun _ => 0) (sourceBaseIndicator A hA) (sourceTransport θ n n sourceVacuum)) z
  rw [hi,hs,ht,hv]
  have he : coordinateRotate (fun _ : SourceCoordinate => 0) z.2 z.1 = z.1 := by
    funext i
    simpa [coordinateRotate] using Int.fract_eq_self.mpr (hc i)
  unfold sourcePiSymbol
  rw [he]
  by_cases ha : z.1 ∈ A <;> by_cases hn : z.2 = n <;>
    simp [sourceBaseIndicator, sourceTransportIndex, ha, hn, sub_eq_zero]

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_FiberTotal
attribute [-instance] _root_.OAI.FiniteFactor.sourceAngleMarginal_atomless _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceSamplingLambda_finite _root_.OAI.FiniteFactor.sourceSamplingSummand_finite _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingUntrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingWeightedMeasure_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal
noncomputable section

/-- Measurable base indicators on the integer fibers determine an L2 vector. -/
theorem sourceFiberIndicators_total (f : SourceHilbert SourceCoordinate)
    (hf : ∀ (A : Set (SourceCoordinate → ℝ)) (hA : MeasurableSet A) (n : ℤ),
      inner ℂ (sourceFiberIndicator A hA n) f = 0) : f = 0 := by
  apply Lp.ext
  refine (Lp.ae_eq_zero_of_forall_setIntegral_eq_zero f (by norm_num) (by norm_num)
    (fun s _ hs => integrableOn_Lp_of_measure_ne_top f (by norm_num) hs.ne) ?_).trans ?_
  · intro s hs hμs
    let A : ℤ → Set (SourceCoordinate → ℝ) := fun n => {x | (x,n) ∈ s}
    have hA (n : ℤ) : MeasurableSet (A n) := hs.preimage (measurable_id.prodMk measurable_const)
    have hcover : s = ⋃ n : ℤ, A n ×ˢ {n} := by
      ext z
      simp only [Set.mem_iUnion, Set.mem_prod, Set.mem_singleton_iff, A, Set.mem_ofPred_eq]
      constructor
      · intro hz; exact ⟨z.2, hz, rfl⟩
      · rintro ⟨n,hn,he⟩; simpa only [← he, Prod.eta] using hn
    have hd : Pairwise (fun n m : ℤ => Disjoint (A n ×ˢ {n}) (A m ×ˢ {m})) := by
      intro n m hnm
      apply Set.disjoint_left.mpr
      rintro z ⟨_,hn⟩ ⟨_,hm⟩
      exact hnm (hn.symm.trans hm)
    have hi : IntegrableOn f (⋃ n : ℤ, A n ×ˢ {n}) (sourceMeasure SourceCoordinate) := by
      rw [← hcover]
      exact integrableOn_Lp_of_measure_ne_top f (by norm_num) hμs.ne
    rw [hcover, integral_iUnion (fun n => (hA n).prod (measurableSet_singleton n)) hd hi]
    have hz (n : ℤ) : ∫ z in A n ×ˢ {n}, f z ∂sourceMeasure SourceCoordinate = 0 := by
      have he := hf (A n) (hA n) n
      rw [sourceFiberIndicator, L2.inner_indicatorConstLp_one] at he
      exact he
    simp_rw [hz]
    exact tsum_zero
  · exact (Lp.coeFn_zero _ _ _).symm

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_Matrix_Entries
attribute [-instance] _root_.OAI.FiniteFactor.sourceAngleMarginal_atomless _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceSamplingLambda_finite _root_.OAI.FiniteFactor.sourceSamplingSummand_finite _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingUntrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingWeightedMeasure_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal
noncomputable section

abbrev sourceBaseMeasure : Measure (SourceCoordinate → ℝ) :=
  Measure.infinitePi (fun _ => unitIntervalMeasure)

/-- Constant coordinate vector, realized in the original source L2 space. -/
def sourceBasis (n : ℤ) : SourceHilbert SourceCoordinate :=
  sourceFiberIndicator Set.univ MeasurableSet.univ n

/-- Actual matrix coefficients obtained by applying H to constant e_n. -/
def sourceMatrixEntry (H : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate)
    (k n : ℤ) (x : SourceCoordinate → ℝ) : ℂ := (H (sourceBasis n)) (x,k)

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_FiberEnergy
attribute [-instance] _root_.OAI.FiniteFactor.sourceAngleMarginal_atomless _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceSamplingLambda_finite _root_.OAI.FiniteFactor.sourceSamplingSummand_finite _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingUntrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingWeightedMeasure_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal
noncomputable section

/-- Squared fiber norm of an actual source L2 vector. Fubini proves finiteness
and identifies it with the square-summable coordinate norm almost everywhere. -/
def sourceFiberEnergy (f : SourceHilbert SourceCoordinate) (x : SourceCoordinate → ℝ) : ℝ :=
  ∫ n : ℤ, ‖f (x,n)‖ ^ 2 ∂Measure.count

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_FiniteVectors
attribute [-instance] _root_.OAI.FiniteFactor.sourceAngleMarginal_atomless _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceSamplingLambda_finite _root_.OAI.FiniteFactor.sourceSamplingSummand_finite _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingUntrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingWeightedMeasure_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal
noncomputable section

/-- Finite coordinate vectors as actual constant-base L2 vectors. -/
def sourceFiniteVector (s : Finset ℤ) (a : ℤ → ℂ) : SourceHilbert SourceCoordinate :=
  ∑ n ∈ s, a n • sourceBasis n

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_OperatorField
attribute [-instance] _root_.OAI.FiniteFactor.sourceAngleMarginal_atomless _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceSamplingLambda_finite _root_.OAI.FiniteFactor.sourceSamplingSummand_finite _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingUntrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingWeightedMeasure_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal
noncomputable section

def sourceMatrixGood (H : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate)
    (x : SourceCoordinate → ℝ) : Prop :=
  ∀ (s t : Finset ℤ) (a : ℤ → ℂ),
    (∑ k ∈ t, ‖∑ n ∈ s, a n * sourceMatrixEntry H k n x‖ ^ 2) ≤
      ‖H‖ ^ 2 * ∑ n ∈ s, ‖a n‖ ^ 2

/-- A Borel good set, removing just one null set for algebra elements. -/
def sourceFieldGoodSet
    (H : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate) :
    Set (SourceCoordinate → ℝ) :=
  (toMeasurable sourceBaseMeasure {x | ¬ sourceMatrixGood H x})ᶜ

theorem sourceFieldGoodSet_good
    (H : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate)
    {x : SourceCoordinate → ℝ} (hx : x ∈ sourceFieldGoodSet H) : sourceMatrixGood H x := by
  by_contra hn
  exact hx (subset_toMeasurable sourceBaseMeasure _ hn)

/-- The actual bounded operator field, extended by zero on a Borel null set. -/
def sourceOperatorField
    (H : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate)
    (x : SourceCoordinate → ℝ) : SourceFiberHilbert →L[ℂ] SourceFiberHilbert := by
  classical
  exact if hx : x ∈ sourceFieldGoodSet H then
    boundedMatrixOperator (fun k n => sourceMatrixEntry H k n x) ‖H‖
      (sourceFieldGoodSet_good H hx)
  else 0

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_Matrix_Action
attribute [-instance] _root_.OAI.FiniteFactor.sourceAngleMarginal_atomless _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceSamplingLambda_finite _root_.OAI.FiniteFactor.sourceSamplingSummand_finite _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingUntrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingWeightedMeasure_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal ComplexConjugate
noncomputable section

def sourceFiberInner (f g : SourceHilbert SourceCoordinate) (x : SourceCoordinate → ℝ) : ℂ :=
  ∫ n : ℤ, inner ℂ (f (x,n)) (g (x,n)) ∂Measure.count

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_FieldRepresentation
attribute [-instance] _root_.OAI.FiniteFactor.sourceAngleMarginal_atomless _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceSamplingLambda_finite _root_.OAI.FiniteFactor.sourceSamplingSummand_finite _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingUntrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingWeightedMeasure_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal Topology
noncomputable section

/-- A fiber vector with an irrelevant zero value on the exceptional null set. -/
def sourceFiberVector (f : SourceHilbert SourceCoordinate) (x : SourceCoordinate → ℝ) :
    SourceFiberHilbert := by
  classical
  exact if h : Memℓp (fun n : ℤ => f (x,n)) 2 then ⟨fun n => f (x,n), h⟩ else 0

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_TorusOperatorField
attribute [-instance] _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal
noncomputable section

/-- The proved source field on the actual compact sampling torus. -/
def sourceTorusOperatorField
    (H : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate) (z : SourceTorus) :
    SourceFiberHilbert →L[ℂ] SourceFiberHilbert :=
  sourceOperatorField H (sourceTorusRepresentative z)

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_Fiber_Diagonal
attribute [-instance] _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped Topology
noncomputable section

/-- A bounded diagonal on the original l2(Z) fiber. -/
def fiberDiagonal (d : ℤ → ℂ) (hd : ∀ k, ‖d k‖ ≤ 1) :
    SourceFiberHilbert →L[ℂ] SourceFiberHilbert :=
  LinearMap.mkContinuous
    { toFun := fun v => ⟨fun k => d k * v k,
        (lp.memℓp v).mono' (fun k => by
          rw [norm_mul]
          exact (mul_le_mul_of_nonneg_right (hd k) (norm_nonneg _)).trans_eq (one_mul _))⟩
      map_add' := fun u v => by apply Subtype.ext; funext k; exact mul_add _ _ _
      map_smul' := fun c v => by apply Subtype.ext; funext k; exact mul_left_comm _ _ _ }
    1 (fun v => by
      rw [one_mul]
      apply lp.norm_mono (by norm_num)
      intro k
      change ‖d k * v k‖ ≤ ‖v k‖
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_right (hd k) (norm_nonneg _)).trans_eq (one_mul _))

@[simp] theorem fiberDiagonal_apply (d : ℤ → ℂ) (hd : ∀ k, ‖d k‖ ≤ 1)
    (v : SourceFiberHilbert) (k : ℤ) : fiberDiagonal d hd v k = d k * v k := rfl

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_Fiber_PairZeroSet
attribute [-instance] _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped Topology
noncomputable section

/-- The actual bounded operator whose vanishing is the pair identity. -/
def fiberPairResidual {X : Type*}
    (P : X → SourceFiberHilbert →L[ℂ] SourceFiberHilbert)
    (d : X × X → ℤ → ℂ) (hd : ∀ z k, ‖d z k‖ ≤ 1) (z : X × X) :
    SourceFiberHilbert →L[ℂ] SourceFiberHilbert :=
  (1 - P z.2) * fiberDiagonal (d z) (hd z) * P z.1

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_CappedPair
attribute [-instance] _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped Topology ENNReal
noncomputable section

def sourceCappedRatio (θ : SourceCoordinate → ℝ) (z : SourceTorus × SourceTorus) (k : ℤ) : ℂ :=
  (min (sourceCocycle θ sourceLogWeight k (sourceTorusRepresentative z.2) /
    sourceCocycle θ sourceLogWeight k (sourceTorusRepresentative z.1)) 1 : ℝ)

theorem sourceCappedRatio_norm (θ : SourceCoordinate → ℝ) (z : SourceTorus × SourceTorus) (k : ℤ) :
    ‖sourceCappedRatio θ z k‖ ≤ 1 := by
  rw [sourceCappedRatio, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (le_min (le_of_lt (div_pos (sourceCocycle_pos ..) (sourceCocycle_pos ..))) zero_le_one)]
  exact min_le_right _ _

/-- The capped equation uses the previously constructed field of the original
operator, on the actual sampling torus. -/
def sourceCappedPairZeroSet (θ : SourceCoordinate → ℝ)
    (H : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate) :
    Set (SourceTorus × SourceTorus) :=
  {z | fiberPairResidual (sourceTorusOperatorField H) (sourceCappedRatio θ)
    (sourceCappedRatio_norm θ) z = 0}

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_OrbitSampling_TorusSupport
attribute [-instance] _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal Classical
noncomputable section

def sourceTorusRotate (θ : SourceCoordinate → ℝ) (n : ℤ) (z : SourceTorus) : SourceTorus :=
  fun i => z i + n • (θ i : UnitAddCircle)

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_OrderedTorusSampling
attribute [-instance] _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal Topology
noncomputable section

structure SourceOrderedTorusSampling (θ : SourceCoordinate → ℝ) : Prop where
  weak : ∀ (I : Finset SourceCoordinate) (f : C(SourceSamplingTorus,ℝ)),
    Tendsto (fun s => ∫ p, f p ∂(sourceSamplingTrimmedTorus I s θ : Measure SourceSamplingTorus))
      atTop (𝓝 (∫ p, f p ∂(sourceSamplingLambdaTorus I : Measure SourceSamplingTorus)))
  support : ∀ (I : Finset SourceCoordinate) (s : ℕ),
    ∀ᵐ p ∂(sourceSamplingTrimmedTorus I s θ : Measure SourceSamplingTorus),
      (∀ i, sourceTorusRepresentative p.1 i ≤ sourceTorusRepresentative p.2 i) ∧
      ∃ n ∈ sourceSamplingPowers s, 0 < n ∧ p.2 = sourceTorusRotate θ n p.1
  marginals : ∀ (I : Finset SourceCoordinate) (r : Bool), ∃ C : ℝ, ∀ s,
    ∃ g : SourceTorus → ℝ, Measurable g ∧ (∀ z, 0 ≤ g z) ∧
      (sourceSamplingTrimmedTorus I s θ : Measure SourceSamplingTorus).map (sourceTorusEndpoint r) =
        sourceTorusHaar.withDensity (fun z => ENNReal.ofReal (g z)) ∧
      MemLp g 2 sourceTorusHaar ∧ (∫ z, g z^2 ∂sourceTorusHaar) ≤ C
  positive : ∀ I : Finset SourceCoordinate, ∀ᶠ s in atTop,
    0 < ((sourceSamplingTrimmedTorus I s θ : Measure SourceSamplingTorus) Set.univ).toReal

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_Fiber_Shift
attribute [-instance] _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open Filter
open scoped ENNReal
noncomputable section

/-- Coordinate translation on the original l2 fiber. -/
def fiberShiftVector (n : ℤ) (v : SourceFiberHilbert) : SourceFiberHilbert :=
  ⟨fun k => v (k-n), memℓp_gen
    ((Equiv.subRight n).summable_iff.mpr ((lp.memℓp v).summable (by norm_num)))⟩

theorem fiberShiftVector_norm (n : ℤ) (v : SourceFiberHilbert) :
    ‖fiberShiftVector n v‖ = ‖v‖ := by
  have he : ‖fiberShiftVector n v‖ ^ 2 = ‖v‖ ^ 2 := by
    rw [show ‖fiberShiftVector n v‖ ^ 2 =
      ∑' k, ‖fiberShiftVector n v k‖ ^ 2 by
        simpa using lp.norm_rpow_eq_tsum (p := (2 : ℝ≥0∞)) (by norm_num) (fiberShiftVector n v)]
    rw [show ‖v‖ ^ 2 = ∑' k, ‖v k‖ ^ 2 by
      simpa using lp.norm_rpow_eq_tsum (p := (2 : ℝ≥0∞)) (by norm_num) v]
    exact (Equiv.subRight n).tsum_eq (fun k => ‖v k‖ ^ 2)
  nlinarith [norm_nonneg (fiberShiftVector n v), norm_nonneg v]

def fiberShift (n : ℤ) : SourceFiberHilbert →L[ℂ] SourceFiberHilbert :=
  LinearMap.mkContinuous
    { toFun := fiberShiftVector n
      map_add' := fun u v => rfl
      map_smul' := fun c v => rfl }
    1 (fun v => by
      change ‖fiberShiftVector n v‖ ≤ 1 * ‖v‖
      rw [one_mul, fiberShiftVector_norm])

@[simp] theorem fiberShift_apply (n : ℤ) (v : SourceFiberHilbert) (k : ℤ) :
    fiberShift n v k = v (k-n) := rfl

@[simp] theorem fiberShift_mul (n m : ℤ) : fiberShift n * fiberShift m = fiberShift (n+m) := by
  apply ContinuousLinearMap.ext
  intro v
  apply Subtype.ext
  funext k
  change v (k-n-m) = v (k-(n+m))
  exact congrArg v (by omega)

@[simp] theorem fiberShift_zero : fiberShift 0 = 1 := by
  apply ContinuousLinearMap.ext
  intro v
  apply Subtype.ext
  funext k
  change v (k-0) = v k
  rw [sub_zero]

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_InvariantConull
attribute [-instance] _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal Topology
noncomputable section

@[simp] theorem sourceTorusRotate_zero (θ : SourceCoordinate → ℝ) (z : SourceTorus) :
    sourceTorusRotate θ 0 z = z := by
  funext i
  simp [sourceTorusRotate]

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_AngleRelations
attribute [-instance] _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceSamplingLambda_finite _root_.OAI.FiniteFactor.sourceSamplingSummand_finite _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingUntrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingWeightedMeasure_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal
noncomputable section

/-- Exact integer formulation of rational independence of 1 and all angles. -/
def SourceRationalIndependent (θ : SourceCoordinate → ℝ) : Prop :=
  ∀ (v : SourceCoordinate →₀ ℤ) (c : ℤ),
    v.sum (fun i n => (n : ℝ)*θ i) = (c : ℝ) → v = 0 ∧ c = 0

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_CentralScalarField
attribute [-instance] _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceSamplingLambda_finite _root_.OAI.FiniteFactor.sourceSamplingSummand_finite _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingUntrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingWeightedMeasure_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal
noncomputable section

/-- The scalar coefficient is the actual field's 00 entry. -/
def sourceCentralCoefficient
    (A : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate)
    (x : SourceCoordinate → ℝ) : ℂ := sourceOperatorField A x (lp.single 2 0 (1 : ℂ)) 0

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_TorusCharacters
attribute [-instance] _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter Set Algebra Submodule
open scoped ENNReal ComplexConjugate
noncomputable section

def sourceCharacter (v : SourceCoordinate →₀ ℤ) : C(SourceTorus, ℂ) where
  toFun x := fourier 1 (v.sum fun i n => n • x i)
  continuous_toFun := (fourier 1).continuous.comp (by
    unfold Finsupp.sum
    exact continuous_finsetSum _ fun i _ => (continuous_apply i).zsmul (v i))

theorem sourceCharacter_zero : sourceCharacter 0 = 1 := by
  ext x
  simp [sourceCharacter]

theorem sourceCharacter_add (v w : SourceCoordinate →₀ ℤ) :
    sourceCharacter (v+w) = sourceCharacter v * sourceCharacter w := by
  ext x
  simp only [sourceCharacter, ContinuousMap.coe_mk, ContinuousMap.mul_apply]
  rw [Finsupp.sum_add_index (by simp) (by intros; simp [add_zsmul])]
  simp [fourier, AddCircle.toCircle_add]

theorem sourceCharacter_neg (v : SourceCoordinate →₀ ℤ) :
    sourceCharacter (-v) = star (sourceCharacter v) := by
  ext x
  have he := congrArg (fun f : C(SourceTorus, ℂ) => f x) (sourceCharacter_add v (-v))
  rw [add_neg_cancel, sourceCharacter_zero] at he
  have hn : ‖sourceCharacter v x‖ = 1 := by
    change ‖(AddCircle.toCircle (1 • v.sum (fun i n => n • x i)) : ℂ)‖ = 1
    exact Circle.norm_coe _
  have hc : sourceCharacter v x * star (sourceCharacter v x) = 1 := by
    change sourceCharacter v x * conj (sourceCharacter v x) = 1
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hn]
    norm_num
  change sourceCharacter (-v) x = star (sourceCharacter v x)
  exact mul_left_cancel₀ (by intro h; simp [h] at hn) (he.symm.trans hc.symm)

def sourceCharacterAlgebra : StarSubalgebra ℂ C(SourceTorus, ℂ) where
  toSubalgebra := Algebra.adjoin ℂ (range sourceCharacter)
  star_mem' := by
    change Algebra.adjoin ℂ (range sourceCharacter) ≤ star (Algebra.adjoin ℂ (range sourceCharacter))
    refine adjoin_le ?_
    rintro _ ⟨v,rfl⟩
    exact subset_adjoin ⟨-v,sourceCharacter_neg v⟩

abbrev sourceCharacterL2 (v : SourceCoordinate →₀ ℤ) : Lp ℂ 2 sourceTorusHaar :=
  ContinuousMap.toLp 2 sourceTorusHaar ℂ (sourceCharacter v)

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_FiniteMixtureAlgebra
attribute [-instance] _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Finset
open scoped ENNReal
noncomputable section

/-- Equal-weight mixture of two probability measures. -/
def probabilityAverage {X : Type*} [MeasurableSpace X] (μ ν : Measure X) : Measure X :=
  (2 : ℝ≥0∞)⁻¹ • (μ + ν)

instance probabilityAverage_probability {X : Type*} [MeasurableSpace X]
    (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (probabilityAverage μ ν) := by
  constructor
  simpa [probabilityAverage,Measure.smul_apply,Measure.add_apply,measure_univ]
    using ENNReal.inv_two_add_inv_two

/-- A single-coordinate update, as a linear operation on the remaining law. -/
def coordinateUpdateLaw {ι X : Type*} [DecidableEq ι] [MeasurableSpace X]
    (i : ι) (μ : Measure X) (ν : Measure (ι → X)) : Measure (ι → X) :=
  (μ.prod ν).map (fun z : X × (ι → X) => Function.update z.2 i z.1)

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_FiniteProductMixture
attribute [-instance] _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Finset
open scoped ENNReal
noncomputable section
variable {ι X : Type*} [DecidableEq ι] [MeasurableSpace X]

variable (μ ν : ι → Measure X) [∀ i, IsProbabilityMeasure (μ i)] [∀ i, IsProbabilityMeasure (ν i)]

def finiteChoiceLaw (I : Finset ι) : Measure (ι → X) := by
  letI : ∀ i, IsProbabilityMeasure (if i ∈ I then ν i else μ i) :=
    fun i => by split_ifs <;> infer_instance
  exact Measure.infinitePi (fun i => if i ∈ I then ν i else μ i)

instance finiteChoiceLaw_probability (I : Finset ι) : IsProbabilityMeasure (finiteChoiceLaw μ ν I) := by
  unfold finiteChoiceLaw
  infer_instance

def finiteAverageLaw (F : Finset ι) : Measure (ι → X) := by
  letI : ∀ i, IsProbabilityMeasure (if i ∈ F then probabilityAverage (μ i) (ν i) else μ i) :=
    fun i => by split_ifs <;> infer_instance
  exact Measure.infinitePi (fun i => if i ∈ F then probabilityAverage (μ i) (ν i) else μ i)

instance finiteAverageLaw_probability (F : Finset ι) : IsProbabilityMeasure (finiteAverageLaw μ ν F) := by
  unfold finiteAverageLaw
  infer_instance

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_PhaseFirst
attribute [-instance] _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceSamplingLambda_finite _root_.OAI.FiniteFactor.sourceSamplingSummand_finite _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingUntrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingWeightedMeasure_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped Topology
noncomputable section

/-- Fractional-part threshold in the small phase range, with both signs. -/
theorem phase_threshold_of_abs {a t : ℝ} (ha : 0 < a) (ha4 : a ≤ 1/4)
    (hlo : a ≤ |t|) (hhi : |t| ≤ 1/2) :
    1 - Int.fract t ∈ Set.Icc a (1-a) := by
  have ht0 : |t| ≠ 0 := ne_of_gt (ha.trans_le hlo)
  have hf : Int.fract |t| = |t| := Int.fract_eq_self.mpr ⟨abs_nonneg _, by linarith⟩
  rcases le_total 0 t with hp | hn
  · rw [abs_of_nonneg hp] at hf hlo hhi
    rw [hf]
    constructor <;> linarith
  · have he : t = -|t| := by rw [abs_of_nonpos hn]; ring
    rw [he, Int.fract_neg (by rw [hf]; exact ht0), hf]
    constructor <;> linarith

/-- Phase bounds for every stage and realization.
There is no eventual-stage or probabilistic assumption. -/
theorem SourceAngles.first_phase {θ : SourceCoordinate → ℝ} (hθ : SourceAngles θ)
    (s : ℕ) (k : ℤ)
    (hlo : (sourceStageState s).G * (sourceStageState s).K ≤ |(k : ℝ)|)
    (hhi : |(k : ℝ)| ≤ ((sourceBlockSize s : ℝ) * (sourceStageState s).K)/4)
    (i : Fin (sourceBlockSize s)) :
    1 - Int.fract ((k : ℝ)*θ ⟨s,i⟩) ∈
      Set.Icc ((sourceStageState s).G/(sourceBlockSize s : ℝ))
        (1-(sourceStageState s).G/(sourceBlockSize s : ℝ)) := by
  have hm := sourceBlockSize_pos s
  have hK := sourceCutoff_pos s
  have hG : 0 < (sourceStageState s).G := lt_of_lt_of_le zero_lt_one (sourceStageState s).G_ge
  have ha4 : (sourceStageState s).G / (sourceBlockSize s : ℝ) ≤ 1/4 := by
    apply (div_le_iff₀ hm).mpr
    have hh := (sourceStage s).m_ge_G
    change 4*(sourceStageState s).G ≤ (sourceBlockSize s : ℝ) at hh
    linarith
  apply phase_threshold_of_abs (div_pos hG hm) ha4
  · rw [abs_mul, abs_of_nonneg (hθ.nonneg ⟨s,i⟩)]
    calc
      (sourceStageState s).G / (sourceBlockSize s : ℝ) =
          ((sourceStageState s).G*(sourceStageState s).K) *
            (1/((sourceBlockSize s : ℝ)*(sourceStageState s).K)) := by field_simp
      _ ≤ |(k : ℝ)| *θ ⟨s,i⟩ :=
        mul_le_mul hlo (hθ ⟨s,i⟩).1 (by positivity) (abs_nonneg _)
  · rw [abs_mul, abs_of_nonneg (hθ.nonneg ⟨s,i⟩)]
    calc
      |(k : ℝ)| *θ ⟨s,i⟩ ≤
          (((sourceBlockSize s : ℝ)*(sourceStageState s).K)/4) *
            (2/((sourceBlockSize s : ℝ)*(sourceStageState s).K)) :=
        mul_le_mul hhi (hθ ⟨s,i⟩).2 (hθ.nonneg _) (by positivity)
      _ = 1/2 := by field_simp; norm_num

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_TagLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter CouplingParameters
open scoped ENNReal
noncomputable section

namespace CouplingParameters

def tagGood (p : CouplingParameters) : Set (Fin 6 × (ℝ × ℝ)) :=
  {z | z.1 = 5 → z.2.1 < 1/p.m ∧ 1-1/p.m ≤ z.2.2}

end CouplingParameters

def sourceTaggedEvent (j : ℕ) : Set SourceBiasedSample :=
  {ω | ∃ i : Fin (sourceBlockSize j), (ω ⟨j,i⟩).1 = 5}

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_Coupling_TaggedAdmissibility
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory
open scoped ENNReal
noncomputable section
namespace CouplingParameters

def currentBoundary (p : CouplingParameters) : Set (Fin 6 × (ℝ × ℝ)) :=
  {z | z.2.1 < 1-2/p.m ∧ 2/p.m < z.2.2}

def currentTag (p : CouplingParameters) : Set (Fin 6 × (ℝ × ℝ)) :=
  {z | z.1 = 5} ∩ p.currentBoundary

def currentNonTag (p : CouplingParameters) : Set (Fin 6 × (ℝ × ℝ)) :=
  {z | z.1 ≠ 5} ∩ p.currentBoundary

end CouplingParameters
end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_Phases
attribute [-instance] _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter Finset
open scoped ENNReal Topology Classical
noncomputable section

def sourcePhaseUpper (s : ℕ) : ℝ :=
  (sourceBlockSize s : ℝ)^((4/5 : ℝ)*(sourceBlockSize s : ℝ))

def sourcePhaseLower (s : ℕ) : ℝ :=
  ((sourceBlockSize s : ℝ)*(sourceStageState s).K)/4

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_PhaseCoverage
attribute [-instance] _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceSamplingLambda_finite _root_.OAI.FiniteFactor.sourceSamplingSummand_finite _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingUntrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingWeightedMeasure_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter Finset
open scoped ENNReal Topology Classical
noncomputable section

def sourceFirstPhaseLower (s : ℕ) : ℝ := (sourceStageState s).G*(sourceStageState s).K

theorem sourcePhaseUpper_tendsto : Tendsto sourcePhaseUpper atTop atTop := by
  apply tendsto_atTop_mono (f := fun s => (sourceBlockSize s : ℝ)) _
    (tendsto_natCast_atTop_atTop.comp sourceBlockSize_tendsto)
  intro s
  have hm : (100 : ℝ) ≤ sourceBlockSize s := by exact_mod_cast (sourceStage s).m_ge_100
  unfold sourcePhaseUpper
  conv_lhs => rw [← Real.rpow_one (sourceBlockSize s : ℝ)]
  exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)

theorem sourcePhaseOverlap (s : ℕ) : sourceFirstPhaseLower (s+1) < sourcePhaseUpper s :=
  (sourceStage s).next_gap

/-- The real interval coverage from the contradiction, with the first range
used only at strictly later blocks. No magnitude is silently omitted. -/
theorem sourcePhase_range_coverage (j : ℕ) (t : ℝ) (ht : sourcePhaseLower j ≤ t) :
    ∃ s : ℕ,
      (j ≤ s ∧ sourcePhaseLower s ≤ t ∧ t ≤ sourcePhaseUpper s) ∨
      (j < s ∧ sourceFirstPhaseLower s ≤ t ∧ t ≤ sourcePhaseLower s) := by
  have hex : ∃ s : ℕ, j ≤ s ∧ t ≤ sourcePhaseUpper s :=
    ((eventually_ge_atTop j).and (sourcePhaseUpper_tendsto.eventually (eventually_ge_atTop t))).exists
  let s := Nat.find hex
  have hs := Nat.find_spec hex
  change j ≤ s ∧ t ≤ sourcePhaseUpper s at hs
  by_cases he : s = j
  · exact ⟨s, Or.inl ⟨hs.1, by simpa [he] using ht, hs.2⟩⟩
  · have hj : j < s := by omega
    by_cases hmid : sourcePhaseLower s ≤ t
    · exact ⟨s, Or.inl ⟨hs.1,hmid,hs.2⟩⟩
    · obtain ⟨p,hp⟩ := Nat.exists_eq_succ_of_ne_zero (show s ≠ 0 by omega)
      have hprev : ¬(j ≤ p ∧ t ≤ sourcePhaseUpper p) := Nat.find_min hex (by change p < s; omega)
      have htprev : sourcePhaseUpper p < t := by
        by_contra hh
        apply hprev
        exact ⟨by omega, le_of_not_gt hh⟩
      refine ⟨s, Or.inr ⟨hj, ?_, (lt_of_not_ge hmid).le⟩⟩
      rw [hp]
      exact (sourcePhaseOverlap p).le.trans htprev.le

/-- The finite deterministic qualifying list at one selected block. -/
def sourceQualifying (θ : SourceCoordinate → ℝ) (s : ℕ) (k : ℤ) (w : Fin 2) :
    Finset SourceCoordinate :=
  (sourceBlockCoordinates s).filter (fun i =>
    1-Int.fract ((k : ℝ)*θ i) ∈ Set.Icc (sourceWidth s w) (1-sourceWidth s w))

def SourceSecondPhasesFrom (θ : SourceCoordinate → ℝ) (j : ℕ) : Prop :=
  ∀ s : ℕ, j ≤ s → ∀ k : ℤ, sourcePhaseLower s ≤ |(k : ℝ)| →
    |(k : ℝ)| ≤ sourcePhaseUpper s →
    (sourceBlockSize s : ℝ)/20 ≤ ((sourceQualifying θ s k 1).card : ℝ)

/-- For every large omitted index, this constructs a block, width, and finite
qualifying list depending only on the fixed angles and the index. -/
theorem exists_source_qualifying_assignment (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ)
    (j : ℕ) (hphase : SourceSecondPhasesFrom θ j) (k : ℤ)
    (hk : sourcePhaseLower j ≤ |(k : ℝ)|) :
    ∃ (s : ℕ) (w : Fin 2) (I : Finset SourceCoordinate),
      j ≤ s ∧ (w = 0 → j < s) ∧ I ⊆ sourceBlockCoordinates s ∧
      (sourceBlockSize s : ℝ)/20 ≤ (I.card : ℝ) ∧
      ∀ i ∈ I, 1-Int.fract ((k : ℝ)*θ i) ∈ Set.Icc (sourceWidth s w) (1-sourceWidth s w) := by
  obtain ⟨s, hs | hs⟩ := sourcePhase_range_coverage j |(k : ℝ)| hk
  · refine ⟨s, 1, sourceQualifying θ s k 1, hs.1, by simp, Finset.filter_subset _ _,
      hphase s hs.1 k hs.2.1 hs.2.2, ?_⟩
    intro i hi
    exact (Finset.mem_filter.mp hi).2
  · refine ⟨s, 0, sourceBlockCoordinates s, hs.1.le, fun _ => hs.1, le_rfl, ?_, ?_⟩
    · rw [sourceBlockCoordinates_card]
      have hh : (0 : ℝ) ≤ sourceBlockSize s := Nat.cast_nonneg _
      linarith
    · intro i hi
      have his := mem_sourceBlockCoordinates hi
      rcases i with ⟨t,i⟩
      change t = s at his
      subst t
      exact hθ.first_phase s k hs.2.1 hs.2.2 i

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_AssignedBadEvents
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter CouplingParameters
open scoped ENNReal
noncomputable section

/-- A deterministic source phase assignment, chosen from the fixed angles. -/
structure SourcePhaseAssignment (θ : SourceCoordinate → ℝ) (j : ℕ) (k : ℤ) where
  block : ℕ
  width : Fin 2
  indices : Finset SourceCoordinate
  later : j ≤ block
  first_later : width = 0 → j < block
  subset : indices ⊆ sourceBlockCoordinates block
  card_lower : (sourceBlockSize block : ℝ)/20 ≤ (indices.card : ℝ)
  threshold : ∀ i ∈ indices,
    1-Int.fract ((k : ℝ)*θ i) ∈ Set.Icc (sourceWidth block width) (1-sourceWidth block width)

def sourceChosenAssignment (θ : SourceCoordinate → ℝ) (hθ : SourceAngles θ)
    (j : ℕ) (hphase : SourceSecondPhasesFrom θ j) (k : ℤ)
    (hk : sourcePhaseLower j ≤ |(k : ℝ)|) : SourcePhaseAssignment θ j k := by
  have hex : Nonempty (SourcePhaseAssignment θ j k) := by
    obtain ⟨s,w,I,hjs,hw,hI,hcard,hu⟩ := exists_source_qualifying_assignment θ hθ j hphase k hk
    exact ⟨⟨s,w,I,hjs,hw,hI,hcard,hu⟩⟩
  exact Classical.choice hex

namespace SourcePhaseAssignment
variable {θ : SourceCoordinate → ℝ} {j : ℕ} {k : ℤ}

def badEvent (a : SourcePhaseAssignment θ j k) (b : Bool) : Set SourceBiasedSample :=
  (fun ω => (sourceBiasedEndpoint (fun _ => b) ω,
    sourceBiasedEndpoint (fun _ => !b) ω)) ⁻¹'
    badHalfEvent (fun _ => b) (fun i => 1-Int.fract ((k : ℝ)*θ i)) a.indices a.indices.card

end SourcePhaseAssignment
end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_BoundaryEvent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
noncomputable section

/-- The source margin 2K_j/N_s. At s=j it is exactly 2/m_j. -/
def sourceExclusionWidth (j : ℕ) (i : SourceCoordinate) : ℝ :=
  2*(sourceStageState j).K/((sourceBlockSize i.1 : ℝ)*(sourceStageState i.1).K)

def sourceBoundaryEvent (j : ℕ) : Set SourceBiasedSample :=
  {ω | ∀ i : SourceCoordinate, j ≤ i.1 →
    sourceBiasedEndpoint (fun _ => false) ω i < 1-sourceExclusionWidth j i ∧
    sourceExclusionWidth j i < sourceBiasedEndpoint (fun _ => true) ω i}

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_ProjectionColumns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory
open scoped ComplexConjugate
noncomputable section

def sourceProjectionColumn
    (p : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate)
    (x : SourceCoordinate → ℝ) : SourceFiberHilbert := sourceOperatorField p x (lp.single 2 0 (1 : ℂ))

def sourceComplementColumn
    (p : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate)
    (x : SourceCoordinate → ℝ) : SourceFiberHilbert := (1-sourceOperatorField p x) (lp.single 2 0 (1 : ℂ))

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_ColumnSquareMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal
noncomputable section

def sourceColumn (p : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate)
    (b : Bool) (x : SourceCoordinate → ℝ) : SourceFiberHilbert :=
  if b then sourceComplementColumn p x else sourceProjectionColumn p x

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_Reflection
attribute [-instance] _root_.OAI.FiniteFactor.sourceAngleMarginal_atomless _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceSamplingLambda_finite _root_.OAI.FiniteFactor.sourceSamplingSummand_finite _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingUntrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingWeightedMeasure_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ComplexConjugate
noncomputable section

/-- The reflection for the source regular representation. -/
def sourceReflectionIndex (θ : SourceCoordinate → ℝ)
    (z : (SourceCoordinate → ℝ) × ℤ) : (SourceCoordinate → ℝ) × ℤ :=
  (coordinateRotate θ z.2 z.1, -z.2)

theorem sourceReflectionIndex_preserving (θ : SourceCoordinate → ℝ) :
    MeasurePreserving (sourceReflectionIndex θ)
      (sourceMeasure SourceCoordinate) (sourceMeasure SourceCoordinate) := by
  have hn : MeasurePreserving (fun n : ℤ => -n) Measure.count Measure.count := by
    refine ⟨measurable_of_countable _, ?_⟩
    ext S hS
    rw [Measure.map_apply (measurable_of_countable _) hS,
      Measure.count_apply (hS.preimage (measurable_of_countable _)), Measure.count_apply hS,
      ← neg_injective.encard_image, Set.image_preimage_eq S neg_surjective]
  have hm : Measurable (Function.uncurry (fun (n : ℤ) (x : SourceCoordinate → ℝ) => coordinateRotate θ n x)) := by
    apply Measurable.of_eval
    intro i
    unfold coordinateRotate
    fun_prop
  have hp := hn.skew_product hm (Eventually.of_forall (fun n => (coordinateRotate_preserving θ n).map_eq))
  exact Measure.measurePreserving_swap.comp (hp.comp Measure.measurePreserving_swap)

def sourceReflectionLinear (θ : SourceCoordinate → ℝ) :
    SourceHilbert SourceCoordinate →ₗᵢ[ℂ] SourceHilbert SourceCoordinate :=
  Lp.compMeasurePreservingₗᵢ ℂ (sourceReflectionIndex θ) (sourceReflectionIndex_preserving θ)

/-- Explicit conjugate-linear isometry; no modular or tracial property assumed. -/
def sourceConjugation (θ : SourceCoordinate → ℝ) (f : SourceHilbert SourceCoordinate) :
    SourceHilbert SourceCoordinate := star (sourceReflectionLinear θ f)

theorem sourceConjugation_apply_ae (θ : SourceCoordinate → ℝ) (f : SourceHilbert SourceCoordinate) :
    sourceConjugation θ f =ᵐ[sourceMeasure SourceCoordinate]
      fun z => star (f (sourceReflectionIndex θ z)) := by
  filter_upwards [Lp.coeFn_star (sourceReflectionLinear θ f),
    Lp.coeFn_compMeasurePreserving f (sourceReflectionIndex_preserving θ)] with z hs hr
  change (star (sourceReflectionLinear θ f)) z = _
  rw [hs]
  change star ((sourceReflectionLinear θ f) z) = _
  change (sourceReflectionLinear θ f) z = f (sourceReflectionIndex θ z) at hr
  rw [hr]

theorem sourceConjugation_involutive (θ : SourceCoordinate → ℝ) (f : SourceHilbert SourceCoordinate) :
    sourceConjugation θ (sourceConjugation θ f) = f := by
  apply Lp.ext
  have ht := (sourceReflectionIndex_preserving θ).quasiMeasurePreserving.ae (sourceConjugation_apply_ae θ f)
  filter_upwards [sourceConjugation_apply_ae θ (sourceConjugation θ f), ht, sourceHilbert_cube] with z h1 h2 hc
  rw [h1,h2,star_star]
  congr 1
  apply Prod.ext
  · change coordinateRotate θ (-z.2) (coordinateRotate θ z.2 z.1) = z.1
    rw [coordinateRotate_add, add_neg_cancel]
    funext i
    simpa [coordinateRotate] using Int.fract_eq_self.mpr (hc i)
  · simp [sourceReflectionIndex]

theorem sourceL2_star_inner (f g : SourceHilbert SourceCoordinate) :
    inner ℂ (star f) (star g) = star (inner ℂ f g) := by
  rw [L2.inner_def, L2.inner_def]
  change _ = conj (∫ z, inner ℂ (f z) (g z) ∂sourceMeasure SourceCoordinate)
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_star f, Lp.coeFn_star g] with z hf hg
  rw [hf,hg]
  simp [RCLike.inner_apply, mul_comm]

theorem sourceConjugation_inner (θ : SourceCoordinate → ℝ) (f g : SourceHilbert SourceCoordinate) :
    inner ℂ (sourceConjugation θ f) (sourceConjugation θ g) = star (inner ℂ f g) := by
  rw [sourceConjugation, sourceConjugation, sourceL2_star_inner,
    (sourceReflectionLinear θ).inner_map_map]

theorem sourceConjugation_inner_symm (θ : SourceCoordinate → ℝ) (f g : SourceHilbert SourceCoordinate) :
    inner ℂ f (sourceConjugation θ g) = inner ℂ g (sourceConjugation θ f) := by
  have hh := sourceConjugation_inner θ (sourceConjugation θ f) g
  rw [sourceConjugation_involutive] at hh
  rw [hh]
  exact inner_conj_symm _ _

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_ConjugationVacuum
attribute [-instance] _root_.OAI.FiniteFactor.sourceAngleMarginal_atomless _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceSamplingLambda_finite _root_.OAI.FiniteFactor.sourceSamplingSummand_finite _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingUntrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingWeightedMeasure_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
noncomputable section

/-- Reflection of each total vacuum test equals its commutant adjoint on the vacuum. -/
theorem sourceConjugation_fiberIndicator (θ : SourceCoordinate → ℝ)
    (A : Set (SourceCoordinate → ℝ)) (hA : MeasurableSet A) (n : ℤ) :
    sourceConjugation θ (sourceFiberIndicator A hA n) =
      star (sourceScalar (sourceBaseIndicator A hA) * sourceCommutantRotation θ n) sourceVacuum := by
  rw [star_mul, sourceScalar_star, sourceCommutantRotation_star]
  apply Lp.ext
  have hf := (sourceReflectionIndex_preserving θ).quasiMeasurePreserving.ae
    (sourceFiberIndicator_coe A hA n)
  have hs := (sourceTransportIndex_preserving θ (-n) (-n)).quasiMeasurePreserving.ae
    (sourcePi_apply_ae (fun _ => 0) (sourceBaseStar (sourceBaseIndicator A hA)) sourceVacuum)
  have hv := (sourceTransportIndex_preserving θ (-n) (-n)).quasiMeasurePreserving.ae sourceVacuum_coe
  filter_upwards [sourceConjugation_apply_ae θ (sourceFiberIndicator A hA n), hf,
    sourceTransport_apply_ae θ (-n) (-n)
      (sourcePi (fun _ => 0) (sourceBaseStar (sourceBaseIndicator A hA)) sourceVacuum), hs, hv]
      with z h1 h2 h3 h4 h5
  change (sourceConjugation θ (sourceFiberIndicator A hA n)) z =
    (sourceTransport θ (-n) (-n) (sourcePi (fun _ => 0) (sourceBaseStar (sourceBaseIndicator A hA)) sourceVacuum)) z
  rw [h1,h2,h3,h4,h5]
  have he : coordinateRotate (fun _ : SourceCoordinate => 0) (z.2 - -n)
      (coordinateRotate θ (-n) z.1) = coordinateRotate θ (-n) z.1 := by
    funext i
    simp [coordinateRotate, Int.fract_fract]
  unfold sourcePiSymbol sourceTransportIndex
  dsimp only
  rw [he]
  by_cases hn : z.2 = -n
  · by_cases ha : coordinateRotate θ (-n) z.1 ∈ A <;>
      simp [sourceReflectionIndex, sourceBaseStar, sourceBaseIndicator, hn, ha]
  · have hn' : -z.2 ≠ n := by omega
    have hn'' : z.2 + n ≠ 0 := by omega
    simp [sourceReflectionIndex, sourceBaseStar, sourceBaseIndicator, hn', hn'']

/-- The actual reflection sends H e_0 to H* e_0 for every source-algebra element. -/
theorem sourceConjugation_algebra_vacuum (θ : SourceCoordinate → ℝ)
    {H : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate}
    (hH : H ∈ sourceAlgebra θ) :
    sourceConjugation θ (H sourceVacuum) = star H sourceVacuum := by
  apply sub_eq_zero.mp
  apply sourceFiberIndicators_total
  intro A hA n
  rw [inner_sub_right]
  apply sub_eq_zero.mpr
  rw [sourceConjugation_inner_symm, sourceConjugation_fiberIndicator,
    ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right,
    ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
  have hr := congrArg (fun T : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate =>
    T sourceVacuum) (sourceAlgebra_commutes_rotation θ hH n)
  rw [sourceFiberIndicator_eq_orbit θ A hA n]
  congr 1
  change sourceScalar (sourceBaseIndicator A hA) (sourceCommutantRotation θ n (H sourceVacuum)) =
    H (sourceScalar (sourceBaseIndicator A hA) (sourceCommutantRotation θ n sourceVacuum))
  have hs' := congrArg (fun T : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate =>
    T (sourceCommutantRotation θ n sourceVacuum))
    (sourceAlgebra_commutes_scalar θ hH (sourceBaseIndicator A hA))
  change sourceCommutantRotation θ n (H sourceVacuum) = H (sourceCommutantRotation θ n sourceVacuum) at hr
  change sourceScalar (sourceBaseIndicator A hA) (H (sourceCommutantRotation θ n sourceVacuum)) = _ at hs'
  rw [hr]
  exact hs'

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_ProjectionEvent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ComplexConjugate
noncomputable section

def sourceDiagonalEvent
    (p : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate) (j : ℕ) : Set SourceBiasedSample :=
  {ω | 1/((j : ℝ)+1) ≤ (sourceCentralCoefficient p (sourceBiasedEndpoint (fun _ => false) ω)).re ∧
    1/((j : ℝ)+1) ≤ 1-(sourceCentralCoefficient p (sourceBiasedEndpoint (fun _ => true) ω)).re}

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_FiniteSingleTag
attribute [-instance] _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Finset
open scoped ENNReal Classical
noncomputable section

variable {ι X : Type*} [Countable ι] [MeasurableSpace X]

def singleTagCylinder (F : Finset ι) (T A : ι → Set X) (i : ι) : Set (ι → X) :=
  Set.pi (F : Set ι) (fun q => if q = i then T q else A q)

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_CurrentTaggedEvent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter CouplingParameters
open scoped ENNReal
noncomputable section

def sourceCurrentTaggedEvent (j : ℕ) : Set SourceBiasedSample :=
  sourceTaggedEvent j ∩ {ω | ∀ i : Fin (sourceBlockSize j),
    ω ⟨j,i⟩ ∈ (stagedCouplingParameters j j).currentBoundary}

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_EventLossAssembly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal Topology
noncomputable section

def sourceDiagonalLossSet
    (p : SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate)
    (j : ℕ) (b : Bool) : Set SourceBiasedSample :=
  {ω | (if b then 1-(sourceCentralCoefficient p (sourceBiasedEndpoint (fun _ => true) ω)).re
    else (sourceCentralCoefficient p (sourceBiasedEndpoint (fun _ => false) ω)).re) < 1/((j : ℝ)+1)}

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_CrossedProduct_NormalFunctionalSpace
attribute [-instance] _root_.OAI.FiniteFactor.sourceAngleMarginal_atomless _root_.OAI.FiniteFactor.sourceBiasedRealMeasure_probability _root_.OAI.FiniteFactor.sourceSamplingLambda_finite _root_.OAI.FiniteFactor.sourceSamplingSummand_finite _root_.OAI.FiniteFactor.sourceSamplingTrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingUntrimmed_finite _root_.OAI.FiniteFactor.sourceSamplingWeightedMeasure_finite _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open TopologicalSpace
noncomputable section

abbrev SourceAlgebraSpace (θ : SourceCoordinate → ℝ) := (sourceAlgebra θ).toStarSubalgebra

def sourceAlgebraInclusion (θ : SourceCoordinate → ℝ) :
    SourceAlgebraSpace θ →L[ℂ] (SourceHilbert SourceCoordinate →L[ℂ] SourceHilbert SourceCoordinate) :=
  (sourceAlgebra θ).toStarSubalgebra.toSubmodule.subtypeL

/-- An actual vector functional restricted to the original source algebra. -/
def sourceVectorFunctional (θ : SourceCoordinate → ℝ)
    (ξ η : SourceHilbert SourceCoordinate) : StrongDual ℂ (SourceAlgebraSpace θ) :=
  (innerSL ℂ ξ).comp ((ContinuousLinearMap.apply ℂ (SourceHilbert SourceCoordinate) η).comp
    (sourceAlgebraInclusion θ))

@[simp] theorem sourceVectorFunctional_apply (θ : SourceCoordinate → ℝ)
    (ξ η : SourceHilbert SourceCoordinate) (A : SourceAlgebraSpace θ) :
    sourceVectorFunctional θ ξ η A = inner ℂ ξ ((A : SourceHilbert SourceCoordinate →L[ℂ]
      SourceHilbert SourceCoordinate) η) := rfl

/-- The norm-closed span of actual vector functionals. This constructs a
Banach space; identifying its whole dual with the source algebra is a
separate surjectivity theorem, not part of this definition. -/
abbrev sourceNormalFunctionalSpace (θ : SourceCoordinate → ℝ) :
    Submodule ℂ (StrongDual ℂ (SourceAlgebraSpace θ)) :=
  (Submodule.span ℂ (Set.range (fun z : SourceHilbert SourceCoordinate × SourceHilbert SourceCoordinate =>
    sourceVectorFunctional θ z.1 z.2))).topologicalClosure

/-- A named carrier keeps the inherited Banach-space structures coherent in
iterated continuous duals. Its underlying set is exactly the closed span. -/
def SourceNormalPredualSpace (θ : SourceCoordinate → ℝ) : Type :=
  sourceNormalFunctionalSpace θ

end
end FiniteFactor

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_OperatorTracialRepresentation
attribute [-instance] _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace FiniteFactor
open scoped Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A concrete finite tracial von Neumann algebra in a faithful vector-trace
representation. These are operator-algebra data, without approximation assumptions. -/
structure TracialRepresentation (M : VonNeumannAlgebra H) where
  vector : H
  norm_vector : ‖vector‖ = 1
  cyclic : ∀ S T : M.toStarSubalgebra,
    inner ℂ vector ((S : H →L[ℂ] H) ((T : H →L[ℂ] H) vector)) =
    inner ℂ vector ((T : H →L[ℂ] H) ((S : H →L[ℂ] H) vector))
  separating : ∀ T : M.toStarSubalgebra, (T : H →L[ℂ] H) vector = 0 → T = 0

end FiniteFactor

end

end OAI
end

section
-- module Solutions.OAIQ3_FF.FiniteFactor_Truncation
attribute [-instance] _root_.OAI.FiniteFactor.sourceUnitCircle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace FiniteFactor
open scoped ComplexConjugate

/-- A finite subset of ℤ, exactly the two simultaneous coefficient cutoffs. -/
noncomputable def convolutionWindow (K : ℕ) (n : ℤ) : Finset ℤ :=
  (Finset.Icc (-(K : ℤ)) K).filter (fun v => -(K : ℤ) ≤ -n-v ∧ -n-v ≤ K)

end FiniteFactor

end OAI
end


