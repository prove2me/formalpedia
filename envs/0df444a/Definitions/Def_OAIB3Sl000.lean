-- Prove2me | Definitions.Def_OAIB3Sl000
-- name    : OAIB3Sl000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-25T12:52:19.118598+00:00
-- url     : https://prove2.me/theorems/b42aacd3-4713-438c-a5fb-85d92edb1fb2
-- title:
--   Definitions bundle OAIB3Sl000 of the split of OpenAI, A single-lattice covering bound of order n log n
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.SingleLatticeCovering.single_lattice_covering`, carved from OpenAI's openai/math development (OpenAI, *A single-lattice covering bound of order n log n*, OpenAI Math Release, September 23, 2026, result family 92, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 440 declarations of OpenAI's Lean: 336 definitions, 5 inductive types or structures, 26 instances and 73 theorems. The definitions and types are `OAI.SingleLatticeCovering.AffineCircuit.IsCircuit`, `OAI.SingleLatticeCovering.AffineCircuit.circuits`, `OAI.SingleLatticeCovering.AffineCircuit.coefficientCircuits`, `OAI.SingleLatticeCovering.AffineCircuit.integerRows`, `OAI.SingleLatticeCovering.AffineVoid.fullMiss`, `OAI.SingleLatticeCovering.AffineVoid.meanFull`, `OAI.SingleLatticeCovering.AffineVoid.meanNormalized`, `OAI.SingleLatticeCovering.AffineVoid.normalDual`, `OAI.SingleLatticeCovering.AffineVoid.normalizedMiss`, `OAI.SingleLatticeCovering.Assembly.coversAtBound`, `OAI.SingleLatticeCovering.Bits.Frozen`, `OAI.SingleLatticeCovering.Bits.Selected`, `OAI.SingleLatticeCovering.Bits.alpha`, `OAI.SingleLatticeCovering.Bits.badMixture`, `OAI.SingleLatticeCovering.Bits.biasedAverage`, `OAI.SingleLatticeCovering.Bits.bitMass`, `OAI.SingleLatticeCovering.Bits.componentGood`, `OAI.SingleLatticeCovering.Bits.conditionalBit`, `OAI.SingleLatticeCovering.Bits.conditionalMass`, `OAI.SingleLatticeCovering.Bits.count`, `OAI.SingleLatticeCovering.Bits.cubeSplit`, `OAI.SingleLatticeCovering.Bits.fairAverage`, `OAI.SingleLatticeCovering.Bits.fairRate`, `OAI.SingleLatticeCovering.Bits.filled`, `OAI.SingleLatticeCovering.Bits.groupShift`, `OAI.SingleLatticeCovering.Bits.integral`, `OAI.SingleLatticeCovering.Bits.likelyBit`, `OAI.SingleLatticeCovering.Bits.meanCount`, `OAI.SingleLatticeCovering.Bits.productMass`, `OAI.SingleLatticeCovering.Blocks.Direction`, `OAI.SingleLatticeCovering.Blocks.collision`, `OAI.SingleLatticeCovering.Blocks.instDecidable_solutions`, `OAI.SingleLatticeCovering.Blocks.lineMax`, `OAI.SingleLatticeCovering.Blocks.lineSum`, `OAI.SingleLatticeCovering.Blocks.sparseWeight`, `OAI.SingleLatticeCovering.Blocks.usableMass`, `OAI.SingleLatticeCovering.BrokenCircuit.Active`, `OAI.SingleLatticeCovering.BrokenCircuit.NoBrokenCircuit`, `OAI.SingleLatticeCovering.BrokenCircuit.avoidanceIndicator`, `OAI.SingleLatticeCovering.BrokenCircuit.binomialPolynomial` and 301 more.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: `LatticeCovering_Bits`, `LatticeCovering_BrokenCircuits`, `LatticeCovering_Chains`, `LatticeCovering_CircuitErrors`, `LatticeCovering_CircuitLattices`, `LatticeCovering_CircuitSums`, `LatticeCovering_CircuitVolumes`, `LatticeCovering_Completion`, `LatticeCovering_Concentration`, `LatticeCovering_Covering`, `LatticeCovering_Desmoothing`, `LatticeCovering_Folded`, `LatticeCovering_GaussianMoments`, `LatticeCovering_GaussianPositions`, `LatticeCovering_GaussianRates`, `LatticeCovering_GaussianSections`, `LatticeCovering_GaussianSmoothing`, `LatticeCovering_GridCounts`, `LatticeCovering_Horizontal`, `LatticeCovering_Isotropy`, `LatticeCovering_Lines`, `LatticeCovering_LogConcavity`, `LatticeCovering_Marginals`, `LatticeCovering_MeanHoles`, `LatticeCovering_Patterns`, `LatticeCovering_PrimeGrids`, `LatticeCovering_PrimeKernels`, `LatticeCovering_Products`, `LatticeCovering_ProjectionBounds`, `LatticeCovering_RadialBounds`, `LatticeCovering_Rates`, `LatticeCovering_Residuals`, `LatticeCovering_Rounding`, `LatticeCovering_Sampling`, `LatticeCovering_SamplingBounds`, `LatticeCovering_Sections`, `LatticeCovering_Shears`, `LatticeCovering_Transport`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the statements `OAI.SingleLatticeCovering.Assembly.sections_and_circuits_cover` and `OAI.SingleLatticeCovering.GaussianProjection.actual_smoothed_lower`; the proofs of `OAI.SingleLatticeCovering.Assembly.sections_and_circuits_cover`, `OAI.SingleLatticeCovering.GaussianProjection.actual_smoothed_lower` and `OAI.SingleLatticeCovering.single_lattice_covering`.
-- source:
--   OpenAI, A single-lattice covering bound of order n log n, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 92; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-single-lattice-covering-bound-of-order-n-log-n-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit adc7f12

import Mathlib

section
-- module Solutions.OAIB3_Slc.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
/-- Mathlib's newer `TensorProduct.inductionOn` (no `zero` case: it is the `tmul` case at
`0 ⊗ₜ 0`); ours has only `TensorProduct.induction_on`, which asks for one. Not named
`TensorProduct.inductionOn`: inside `namespace OAI` that would make `open TensorProduct` open
`OAI.TensorProduct` instead of Mathlib's. -/
@[elab_as_elim]
theorem tensorInductionOn {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] {motive : TensorProduct R M N → Prop} (z : TensorProduct R M N)
    (tmul : ∀ x y, motive (TensorProduct.tmul R x y))
    (add : ∀ x y, motive x → motive y → motive (x + y)) : motive z :=
  TensorProduct.induction_on z (by simpa using tmul 0 0) tmul add
/-- Mathlib's newer case names for `FreeGroup.induction_on` (`one`, where ours says `C1`). -/
@[elab_as_elim]
theorem freeGroupInductionOn {α : Type*} {C : FreeGroup α → Prop} (z : FreeGroup α) (one : C 1)
    (of : ∀ x, C (FreeGroup.of x)) (inv_of : ∀ x, C (FreeGroup.of x) → C (FreeGroup.of x)⁻¹)
    (mul : ∀ x y, C x → C y → C (x * y)) : C z :=
  FreeGroup.induction_on z one of inv_of mul
/-- For a measurable equivalence `e`, `IsProbabilityMeasure (μ.map e)` is found by instance search
(Mathlib d13f23b finds it for every map `f`: there `Measure.map` of a non-measurable map is a Dirac
mass, here it is `0`, so only the measurable case can be shimmed). -/
instance isProbabilityMeasure_map_measurableEquiv {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {μ : MeasureTheory.Measure α} [MeasureTheory.IsProbabilityMeasure μ]
    (e : α ≃ᵐ β) : MeasureTheory.IsProbabilityMeasure (μ.map e) :=
  MeasureTheory.Measure.isProbabilityMeasure_map e.measurable.aemeasurable
end OAICompat434

end OAI
end

section
-- module Solutions.OAIB3_Slc.LatticeCovering_Folded
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section





section



noncomputable section
open scoped BigOperators
open Real

namespace SingleLatticeCovering.Folded
variable {ι : Type*} [Fintype ι]

def gamma1 (x : ℝ) : ℝ := Real.exp (-(x^2)/2) / Real.sqrt (2*Real.pi)
def gamma (x : ι → ℝ) : ℝ := ∏ j, gamma1 (x j)
def height (b : ℕ) : ℝ := Real.sqrt ((9/4 : ℝ)*Real.log (b : ℝ))
def density (h t : ℝ) : ℝ := h*gamma1 (h*t)+h*gamma1 (h*(t-1))
def folded (h : ℝ) (t : ι → ℝ) : ℝ := ∏ j, density h (t j)
def bitValue (e : Bool) : ℝ := if e then 1 else 0
def probability (h t : ℝ) (e : Bool) : ℝ :=
  h*gamma1 (h*(t-bitValue e))/density h t
def wordMass (h : ℝ) (t : ι → ℝ) (e : ι → Bool) : ℝ := ∏ j, probability h (t j) (e j)
def atom (h : ℝ) (t : ι → ℝ) (e : ι → Bool) : ℝ :=
  h^Fintype.card ι * gamma (fun j => h*(t j-bitValue (e j)))

def alpha : ℝ := (1+Real.exp 1)⁻¹



end SingleLatticeCovering.Folded

namespace SingleLatticeCovering.Folded
open MeasureTheory ProbabilityTheory Set


def totalMass (h : ℝ) : ℝ := ∫ t in (0 : ℝ)..1, density h t

def logMean (h : ℝ) : ℝ :=
  (∫ t in (0 : ℝ)..1, density h t*Real.log (density h t))/totalMass h



end SingleLatticeCovering.Folded

namespace SingleLatticeCovering.Folded
open MeasureTheory ProbabilityTheory Set Real

def foldMoment (h t : ℝ) : ℝ :=
  h*(gamma1 (h*t)*(h*t)^2)+h*(gamma1 (h*(t-1))*(h*(t-1))^2)



end SingleLatticeCovering.Folded

namespace SingleLatticeCovering.Folded
open MeasureTheory ProbabilityTheory Set Real


def law (h : ℝ) : Measure ℝ :=
  (volume.restrict (Icc (0 : ℝ) 1)).withDensity
    (fun t => ENNReal.ofReal (density h t/totalMass h))



end SingleLatticeCovering.Folded



end
end
end

end OAI
end

section
-- module Solutions.OAIB3_Slc.LatticeCovering_Concentration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped BigOperators
open Real
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set

namespace SingleLatticeCovering.Folded
open MeasureTheory ProbabilityTheory Set Real


def centralInterval (h : ℝ) : Set ℝ := Icc (1/2-1/(2*h^2)) (1/2+1/(2*h^2))

variable {ι : Type*} [Fintype ι]

def cubeLaw (h : ℝ) : Measure (ι → ℝ) := Measure.pi (fun _ : ι => law h)




end SingleLatticeCovering.Folded
noncomputable section
open scoped BigOperators
open MeasureTheory Set

namespace SingleLatticeCovering.Folded
open MeasureTheory ProbabilityTheory Set Real
variable {ι : Type*} [Fintype ι]

def cube : Set (ι → ℝ) := Set.univ.pi (fun _ => Set.Icc (0 : ℝ) 1)



end SingleLatticeCovering.Folded



noncomputable section
open Module Submodule MeasureTheory
open scoped BigOperators

namespace SingleLatticeCovering.ConstructionA

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def generator (p : ℕ) (a : ι → ℤ) : ι → ℝ := fun j => (a j : ℝ) / p

def matrix (p : ℕ) (i : ι) (a : ι → ℤ) : Matrix ι ι ℝ :=
  (1 : Matrix ι ι ℝ).updateRow i (generator p a)

lemma det_matrix (p : ℕ) (i : ι) (a : ι → ℤ) (ha : a i = 1) :
    (matrix p i a).det = (p : ℝ)⁻¹ := by
  have hs : (∑ j, (generator p a j) • (1 : Matrix ι ι ℝ) j) = generator p a := by
    ext k
    simp [Matrix.one_apply, Pi.smul_apply, smul_eq_mul]
  rw [matrix, ← hs, Matrix.det_updateRow_sum]
  simp [generator, ha]

lemma independent_matrix (p : ℕ) (hp : 0 < p) (i : ι) (a : ι → ℤ) (ha : a i = 1) :
    LinearIndependent ℝ (matrix p i a) := by
  apply Matrix.linearIndependent_rows_iff_isUnit.mpr
  rw [Matrix.isUnit_iff_isUnit_det]
  change IsUnit (matrix p i a).det
  rw [det_matrix p i a ha]
  exact isUnit_iff_ne_zero.mpr (inv_ne_zero (by exact_mod_cast hp.ne'))

def basis (p : ℕ) (hp : 0 < p) (i : ι) (a : ι → ℤ) (ha : a i = 1) :
    Basis ι ℝ (ι → ℝ) := by
  letI : Nonempty ι := ⟨i⟩
  exact Basis.mk (independent_matrix p hp i a ha)
    (by rw [(independent_matrix p hp i a ha).span_eq_top_of_card_eq_finrank
      (Module.finrank_pi ℝ).symm])

@[simp] lemma basis_apply (p : ℕ) (hp : 0 < p) (i : ι) (a : ι → ℤ) (ha : a i = 1)
    (j : ι) : basis p hp i a ha j = matrix p i a j := by
  unfold basis
  exact Basis.mk_apply _ _ j

@[simp] lemma basis_pivot (p : ℕ) (hp : 0 < p) (i : ι) (a : ι → ℤ) (ha : a i = 1) :
    basis p hp i a ha i = generator p a := by
  rw [basis_apply]
  exact Matrix.updateRow_self

lemma basis_other (p : ℕ) (hp : 0 < p) (i : ι) (a : ι → ℤ) (ha : a i = 1)
    (j : ι) (hj : j ≠ i) : basis p hp i a ha j = (Pi.basisFun ℝ ι) j := by
  rw [basis_apply]
  change (1 : Matrix ι ι ℝ).updateRow i (generator p a) j = _
  rw [Matrix.updateRow_ne hj]
  ext k
  simp [Pi.basisFun_apply, Matrix.one_apply, Pi.single_apply, eq_comm]

def lattice (p : ℕ) (hp : 0 < p) (i : ι) (a : ι → ℤ) (ha : a i = 1) :
    Submodule ℤ (ι → ℝ) := span ℤ (Set.range (basis p hp i a ha))

instance lattice_discrete (p : ℕ) (hp : 0 < p) (i : ι) (a : ι → ℤ) (ha : a i = 1) :
    DiscreteTopology (lattice p hp i a ha) := inferInstanceAs
      (DiscreteTopology (span ℤ (Set.range (basis p hp i a ha))))

instance lattice_full (p : ℕ) (hp : 0 < p) (i : ι) (a : ι → ℤ) (ha : a i = 1) :
    IsZLattice ℝ (lattice p hp i a ha) := inferInstanceAs
      (IsZLattice ℝ (span ℤ (Set.range (basis p hp i a ha))))

lemma covolume_lattice (p : ℕ) (hp : 0 < p) (i : ι) (a : ι → ℤ) (ha : a i = 1) :
    ZLattice.covolume (lattice p hp i a ha) = (p : ℝ)⁻¹ := by
  change ZLattice.covolume (span ℤ (Set.range (basis p hp i a ha))) = _
  rw [ZLattice.covolume_eq_measure_fundamentalDomain _ volume
    (ZSpan.isAddFundamentalDomain (basis p hp i a ha) volume),
    ZSpan.volume_real_fundamentalDomain]
  have he : Matrix.of (basis p hp i a ha) = matrix p i a := by ext; simp
  rw [he, det_matrix p i a ha, abs_of_pos (inv_pos.mpr (by exact_mod_cast hp))]

lemma generator_mem (p : ℕ) (hp : 0 < p) (i : ι) (a : ι → ℤ) (ha : a i = 1) :
    generator p a ∈ lattice p hp i a ha := by
  rw [← basis_pivot p hp i a ha]
  exact subset_span ⟨i, rfl⟩

lemma integer_mem (p : ℕ) (hp : 0 < p) (i : ι) (a : ι → ℤ) (ha : a i = 1)
    (z : ι → ℤ) : (fun j => (z j : ℝ)) ∈ lattice p hp i a ha := by
  rw [lattice, Submodule.mem_span_range_iff_exists_fun]
  refine ⟨fun j => if j = i then (p : ℤ)*z i else z j-z i*a j, ?_⟩
  ext k
  rw [Finset.sum_apply, ← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
  simp only [Pi.smul_apply, basis_pivot, generator, zsmul_eq_mul]
  have he : ∑ j ∈ Finset.univ.erase i,
      ((if j = i then (p : ℤ)*z i else z j-z i*a j) : ℤ) •
        basis p hp i a ha j k =
      if k = i then 0 else (z k : ℝ) - (z i : ℝ)*(a k : ℝ) := by
    calc
      _ = ∑ j ∈ Finset.univ.erase i,
          ((z j : ℝ)-(z i : ℝ)*(a j : ℝ)) * (if j = k then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro j hj
        have hji := (Finset.mem_erase.mp hj).1
        rw [ite_eq_right hji, basis_other p hp i a ha j hji]
        simp [Pi.basisFun_apply, Pi.single_apply, eq_comm, zsmul_eq_mul]
      _ = _ := by
        by_cases hki : k = i
        · subst k
          simp only [↓reduceIte]
          apply Finset.sum_eq_zero
          intro j hj
          simp [(Finset.mem_erase.mp hj).1]
        · simp [hki, Finset.mem_erase]
  simp only [zsmul_eq_mul] at he
  rw [he]
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  by_cases hki : k = i
  · subst k; simp [ha]; field_simp
  · rw [ite_eq_right hki]
    push_cast
    field_simp
    ring

lemma mem_lattice_iff (p : ℕ) (hp : 0 < p) (i : ι) (a : ι → ℤ) (ha : a i = 1)
    (x : ι → ℝ) : x ∈ lattice p hp i a ha ↔
      ∃ (z : ι → ℤ) (m : ℤ), x = (fun j => (z j : ℝ)) + m • generator p a := by
  constructor
  · intro hx
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hx
    refine ⟨fun j => if j = i then 0 else c j, c i, ?_⟩
    rw [← hc]
    ext k
    rw [Finset.sum_apply, ← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
    simp only [Pi.add_apply, Pi.smul_apply, basis_pivot]
    congr 1
    calc
      _ = ∑ j ∈ Finset.univ.erase i, (c j : ℝ) * (if j = k then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [basis_other p hp i a ha j (Finset.mem_erase.mp hj).1]
        simp [Pi.basisFun_apply, Pi.single_apply, eq_comm, zsmul_eq_mul]
      _ = _ := by
        by_cases hki : k = i
        · subst k
          simp only [↓reduceIte, Int.cast_zero]
          apply Finset.sum_eq_zero
          intro j hj
          simp [(Finset.mem_erase.mp hj).1]
        · simp [hki, Finset.mem_erase]
  · rintro ⟨z, m, rfl⟩
    exact (lattice p hp i a ha).add_mem (integer_mem p hp i a ha z)
      ((lattice p hp i a ha).smul_mem m (generator_mem p hp i a ha))



end SingleLatticeCovering.ConstructionA

namespace SingleLatticeCovering.ConstructionA
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def residue (p : ℕ) (k : ι → ℤ) : ι → ZMod p := fun j => (k j : ZMod p)



def codeLattice (p : ℕ) (C : Submodule (ZMod p) (ι → ZMod p)) :
    Submodule ℤ (ι → ℝ) where
  carrier := {x | ∃ k : ι → ℤ, residue p k ∈ C ∧ generator p k = x}
  zero_mem' := ⟨0, by convert C.zero_mem using 1 ; ext j ; simp [residue], by ext; simp [generator]⟩
  add_mem' := by
    rintro x y ⟨k, hk, rfl⟩ ⟨l, hl, rfl⟩
    refine ⟨k+l, ?_, ?_⟩
    · convert C.add_mem hk hl using 1 ; ext j ; simp [residue]
    · ext j; simp [generator, add_div]
  smul_mem' := by
    rintro m x ⟨k, hk, rfl⟩
    refine ⟨m • k, ?_, ?_⟩
    · convert C.smul_mem (m : ZMod p) hk using 1 ; ext j ; simp [residue]
    · ext j; simp [generator, zsmul_eq_mul, mul_div_assoc]

lemma lattice_eq_codeLattice (p : ℕ) (hp : 0 < p) (i : ι) (a : ι → ℤ) (ha : a i = 1) :
    lattice p hp i a ha = codeLattice p (Submodule.span (ZMod p) {residue p a}) := by
  let : NeZero p := ⟨hp.ne'⟩
  ext x
  rw [mem_lattice_iff]
  constructor
  · rintro ⟨z, m, rfl⟩
    refine ⟨fun j => (p : ℤ)*z j+m*a j, ?_, ?_⟩
    · apply Submodule.mem_span_singleton.mpr
      refine ⟨(m : ZMod p), ?_⟩
      ext j
      simp [residue]
    · ext j
      simp only [Pi.add_apply, zsmul_eq_mul, Pi.mul_apply]
      change ((p : ℤ)*z j+m*a j : ℤ) / (p : ℝ) = (z j : ℝ) + (m : ℝ)*((a j : ℝ)/p)
      push_cast
      field_simp

  · rintro ⟨k, hk, rfl⟩
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hk
    let m : ℤ := r.val
    have hm : (m : ZMod p) = r := by simp [m]
    have hd (j : ι) : (p : ℤ) ∣ k j - m*a j := by
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
      have hj := congr_fun hr j
      simpa [residue, hm] using sub_eq_zero.mpr hj.symm
    choose z hz using hd
    refine ⟨z, m, ?_⟩
    ext j
    have hj : (k j : ℝ) - (m : ℝ)*(a j : ℝ) = (p : ℝ)*(z j : ℝ) := by
      exact_mod_cast hz j
    simp only [Pi.add_apply, zsmul_eq_mul, Pi.mul_apply]
    change (k j : ℝ)/(p : ℝ) = (z j : ℝ)+(m : ℝ)*((a j : ℝ)/p)
    apply (div_eq_iff (show (p : ℝ) ≠ 0 by exact_mod_cast hp.ne')).mpr
    field_simp
    nlinarith

lemma normalized_lift {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ℕ) [Fact p.Prime] (v : ι → ZMod p) (hv : v ≠ 0) :
    ∃ (i : ι) (a : ι → ℤ), a i = 1 ∧
      Submodule.span (ZMod p) {residue p a} = Submodule.span (ZMod p) {v} := by
  have hp : p.Prime := Fact.out
  let : Fact (1 < p) := ⟨hp.one_lt⟩
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra! h
    exact hv (funext h)
  let a : ι → ℤ := fun j => ((v i)⁻¹*v j).val
  have ha : a i = 1 := by simp only [a, inv_mul_cancel₀ hi, ZMod.val_one, Nat.cast_one]
  have hr : residue p a = (v i)⁻¹ • v := by
    ext j
    simp [residue, a]
  refine ⟨i, a, ha, ?_⟩
  apply le_antisymm
  · apply Submodule.span_le.mpr
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    rw [hx]
    exact Submodule.mem_span_singleton.mpr ⟨(v i)⁻¹, hr.symm⟩
  · apply Submodule.span_le.mpr
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    rw [hx]
    apply Submodule.mem_span_singleton.mpr
    refine ⟨v i, ?_⟩
    rw [hr, smul_smul, mul_inv_cancel₀ hi, one_smul]



theorem line_lattice (p : ℕ) [Fact p.Prime] (v : ι → ZMod p) (hv : v ≠ 0) :
    ∃ (_ : DiscreteTopology (codeLattice p (Submodule.span (ZMod p) {v}))),
      IsZLattice ℝ (codeLattice p (Submodule.span (ZMod p) {v})) ∧
      ZLattice.covolume (codeLattice p (Submodule.span (ZMod p) {v})) = (p : ℝ)⁻¹ := by
  obtain ⟨i, a, ha, hspan⟩ := normalized_lift p v hv
  have hp : 0 < p := (show p.Prime from Fact.out).pos
  have he : codeLattice p (Submodule.span (ZMod p) {v}) = lattice p hp i a ha := by
    rw [lattice_eq_codeLattice p hp i a ha, hspan]
  rw [he]
  exact ⟨inferInstance, inferInstance, covolume_lattice p hp i a ha⟩


end SingleLatticeCovering.ConstructionA

namespace SingleLatticeCovering.ConstructionA
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def floorVector (p : ℕ) (t : ι → ℝ) : ι → ℤ := fun j => ⌊(p : ℝ)*t j⌋
def anchor (p : ℕ) (z : ι → ZMod p) : ι → ℝ := fun j => (z j).val / (p : ℝ)
def integerLift (p : ℕ) (z : ι → ZMod p) : ι → ℤ := fun j => (z j).val

def gridCell (p : ℕ) (z : ι → ZMod p) : Set (ι → ℝ) :=
  {t | ∀ j, t j - anchor p z j ∈ Set.Ico 0 (p : ℝ)⁻¹}

def cellPoint (p : ℕ) (t : ι → ℝ) (z : ι → ZMod p) : ι → ℝ :=
  generator p (floorVector p t - integerLift p z)


end SingleLatticeCovering.ConstructionA


end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIB3_Slc.LatticeCovering_Rounding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped BigOperators
open Real
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set
noncomputable section
open scoped BigOperators
open MeasureTheory Set
noncomputable section
open Module Submodule MeasureTheory
open scoped BigOperators

namespace SingleLatticeCovering.Folded
open Set MeasureTheory Real ConstructionA
variable {ι : Type*} [Fintype ι] [DecidableEq ι]


def gridMass (h : ℝ) (p : ℕ) [NeZero p] (E : Finset (ι → ZMod p)) : ℝ :=
  ((p : ℝ)⁻¹)^Fintype.card ι * ∑ z ∈ E, folded h (anchor p z)


end SingleLatticeCovering.Folded

namespace SingleLatticeCovering.Folded
open Set MeasureTheory Real ConstructionA
variable {ι : Type*} [Fintype ι] [DecidableEq ι]


def gridEligible (h μ D r : ℝ) (p : ℕ) [NeZero p] : Finset (ι → ZMod p) := by
  classical
  exact Finset.univ.filter (fun z => |Real.log (folded h (anchor p z))-(Fintype.card ι : ℝ)*μ| ≤ D ∧
    r ≤ (Finset.univ.filter fun j => |anchor p z j-1/2| ≤ (h^2)⁻¹).card)


end SingleLatticeCovering.Folded

namespace SingleLatticeCovering.Folded
open Set MeasureTheory Real ConstructionA
variable {ι : Type*} [Fintype ι] [DecidableEq ι]


def continuousGood (h c r : ℝ) : Set (ι → ℝ) :=
  {t | |Real.log (folded h t)-(Fintype.card ι : ℝ)*logMean h| < c ∧
    r ≤ ∑ j, (centralInterval h).indicator (fun _ => (1 : ℝ)) (t j)}


end SingleLatticeCovering.Folded





noncomputable section
open Real Filter Topology


namespace SingleLatticeCovering.Folded
open Real Filter Topology Asymptotics



def heightR (b : ℝ) : ℝ := Real.sqrt ((9/4 : ℝ)*Real.log b)




end SingleLatticeCovering.Folded



end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIB3_Slc.LatticeCovering_Sampling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped BigOperators
open Real
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set
noncomputable section
open scoped BigOperators
open MeasureTheory Set
noncomputable section
open Module Submodule MeasureTheory
open scoped BigOperators
noncomputable section
open Real Filter Topology





noncomputable section
open scoped BigOperators

namespace SingleLatticeCovering.Sampler

universe u v

section FiniteAverages
variable {α : Type u} {β : Type v} [Fintype α] [Fintype β]


def consEquiv (k : ℕ) (α : Type u) : (Fin (k + 1) → α) ≃ α × (Fin k → α) where
  toFun w := (w 0, Fin.tail w)
  invFun z := Fin.cons z.1 z.2
  left_inv w := Fin.cons_self_tail w
  right_inv z := by simp

end FiniteAverages

section FiniteProbability
variable {α : Type u} {β : Type v} [Fintype α] [Fintype β]


def probability (p : α → Prop) : ℝ := by
  classical
  exact 𝔼 x, if p x then 1 else 0

end FiniteProbability

section GroupAverages
variable {G : Type u} [AddCommGroup G] [Fintype G]


def step (w : G) (f : G → ℝ) (x : G) : ℝ := (f x + f (x - w)) / 2


def binaryAverage : {k : ℕ} → (Fin k → G) → (G → ℝ) → G → ℝ
  | 0, _, f => f
  | _ + 1, w, f => step (w 0) (binaryAverage (Fin.tail w) f)

@[simp] lemma binaryAverage_zero {G : Type u} [AddCommGroup G] [Fintype G] (w : Fin 0 → G) (f : G → ℝ) :
    binaryAverage w f = f := rfl

@[simp] lemma binaryAverage_cons {G : Type u} [AddCommGroup G] [Fintype G] {k : ℕ} (a : G) (w : Fin k → G) (f : G → ℝ) :
    binaryAverage (Fin.cons a w) f = step a (binaryAverage w f) := rfl


def subsetShift {k : ℕ} (w : Fin k → G) (e : Fin k → Bool) : G :=
  ∑ i, if e i then w i else 0



def binarySum {k : ℕ} (w : Fin k → G) (f : G → ℝ) (x : G) : ℝ :=
  (2 : ℝ)^k * binaryAverage w f x

@[simp] lemma binarySum_zero {G : Type u} [AddCommGroup G] [Fintype G] (w : Fin 0 → G) (f : G → ℝ) (x : G) :
    binarySum w f x = f x := by simp [binarySum]

@[simp] lemma binarySum_cons {G : Type u} [AddCommGroup G] [Fintype G] {k : ℕ} (a : G) (w : Fin k → G) (f : G → ℝ) (x : G) :
    binarySum (Fin.cons a w) f x = binarySum w f x + binarySum w f (x-a) := by
  simp only [binarySum, binaryAverage_cons, step, pow_succ]
  ring


def potential (θ : ℝ) (f : G → ℝ) : ℝ := 𝔼 x, Real.exp (-θ * f x)

end GroupAverages
end SingleLatticeCovering.Sampler




end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIB3_Slc.LatticeCovering_SamplingBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped BigOperators
open Real
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set
noncomputable section
open scoped BigOperators
open MeasureTheory Set
noncomputable section
open Module Submodule MeasureTheory
open scoped BigOperators
noncomputable section
open Real Filter Topology
noncomputable section
open scoped BigOperators
noncomputable section
open Filter Topology Asymptotics

namespace SingleLatticeCovering.Sampler.Numeric

def cStar : ℝ := Real.log 2 / 8

def delta (b : ℝ) : ℝ := b^(-1/10 : ℝ)
def theta (s : ℕ) : ℝ := cStar*(s : ℝ)/2

end SingleLatticeCovering.Sampler.Numeric




noncomputable section

open scoped BigOperators
open Classical

namespace SingleLatticeCovering.Bits
universe u v
variable {I : Type u} [Fintype I]


def bitMass (q : ℝ) (e : Bool) : ℝ := if e then q else 1-q

def productMass (q : I → ℝ) (e : I → Bool) : ℝ := ∏ i, bitMass (q i) (e i)

def integral (q : I → ℝ) (f : (I → Bool) → ℝ) : ℝ := ∑ e, productMass q e * f e


def count (e : I → Bool) : ℝ := ∑ i, if e i then (1 : ℝ) else 0

def meanCount (q : I → ℝ) : ℝ := ∑ i, q i


def fairRate (q : ℝ) : ℝ := 2*min q (1-q)
def likelyBit (q : ℝ) : Bool := decide (1/2 ≤ q)
def conditionalBit (q : ℝ) (s e : Bool) : ℝ :=
  if s then 1/2 else if e=likelyBit q then 1 else 0

def conditionalMass (q : I → ℝ) (s e : I → Bool) : ℝ :=
  ∏ i, conditionalBit (q i) (s i) (e i)

end SingleLatticeCovering.Bits



namespace SingleLatticeCovering.Bits
universe u w
variable {I : Type u} [Fintype I]


abbrev Selected (s : I → Bool) := {i // s i = true}
abbrev Frozen (s : I → Bool) := {i // ¬s i = true}

def cubeSplit (s : I → Bool) : (I → Bool) ≃ ((Selected s → Bool) × (Frozen s → Bool)) :=
  Equiv.piEquivPiSubtypeProd (fun i => s i=true) (fun _ => Bool)

def filled (q : I → ℝ) (s : I → Bool) (a : Selected s → Bool) : I → Bool :=
  (cubeSplit s).symm (a, fun j => likelyBit (q j))

end SingleLatticeCovering.Bits




end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIB3_Slc.LatticeCovering_Bits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped BigOperators
open Real
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set
noncomputable section
open scoped BigOperators
open MeasureTheory Set
noncomputable section
open Module Submodule MeasureTheory
open scoped BigOperators
noncomputable section
open Real Filter Topology
noncomputable section
open scoped BigOperators
noncomputable section
open Filter Topology Asymptotics
noncomputable section
open scoped BigOperators
open Classical

namespace SingleLatticeCovering.Bits
universe u v w
variable {I : Type u} {J : Type v} {G : Type w} [Fintype I] [Fintype J]
  [AddCommGroup G] [Fintype G]


def groupShift (w : I → G) (e : I → Bool) : G := ∑ i, if e i then w i else 0

def fairAverage (w : I → G) (f : G → ℝ) (x : G) : ℝ :=
  (∑ e, f (x-groupShift w e))/(2 : ℝ)^(Fintype.card I)

def biasedAverage (q : I → ℝ) (w : I → G) (f : G → ℝ) (x : G) : ℝ :=
  integral q (fun e => f (x-groupShift w e))



def componentGood (b A : ℝ) (f : G → ℝ) (w : I → G) (s : I → Bool) : Prop :=
  b^(69/100 : ℝ) ≤ (Fintype.card (Selected s) : ℝ) ∧
    ∀ x, A ≤ fairAverage (fun j : Selected s => w j) f x

def badMixture (b A : ℝ) (q : I → ℝ) (f : G → ℝ) (w : I → G) : ℝ :=
  integral (fun i => fairRate (q i)) (fun s => if componentGood b A f w s then 0 else 1)

end SingleLatticeCovering.Bits





noncomputable section

open scoped BigOperators
open Classical
namespace SingleLatticeCovering.WeightedSelection
universe u v
variable {Z : Type u} {W : Type v} [Fintype Z] [Fintype W] [Nonempty W]


def mass (F : Z → ℝ) (E : Finset Z) : ℝ := 𝔼 z, if z ∈ E then F z else 0

def loss (F : Z → ℝ) (E : Finset Z) (q : W → Z → ℝ) (w : W) : ℝ :=
  𝔼 z, if z ∈ E then F z*q w z else 0

end SingleLatticeCovering.WeightedSelection

namespace SingleLatticeCovering.Bits
universe u v w
open Filter
open scoped Topology


def alpha : ℝ := (1+Real.exp 1)⁻¹

end SingleLatticeCovering.Bits





noncomputable section
open scoped BigOperators
open Classical

namespace SingleLatticeCovering.Blocks
local instance instDecidable_solutions : (p : Prop) → Decidable p := Classical.propDecidable

universe u v
variable {K : Type u} {V : Type v} [Field K] [Fintype K]
  [AddCommGroup V] [Module K V] [Fintype V]

abbrev Direction (V : Type v) [Zero V] := {v : V // v ≠ 0}


def lineSum (f : V → ℝ) (v x : V) : ℝ := ∑ a : K, f (x-a • v)


def lineMax (f : V → ℝ) (v x : V) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun a : K => f (x-a • v))


def collision (U : Finset V) (v z : V) : Prop :=
  ∃ w ∈ U, w ≠ z ∧ ∃ a : K, a • v = w-z


def usableMass (U : Finset V) (F : V → ℝ) : ℝ :=
  𝔼 z, if z ∈ U then F z else 0



def sparseWeight (U : Finset V) (F : V → ℝ) (z : V) : ℝ :=
  if z ∈ U then F z / (Fintype.card K : ℝ) else 0

end SingleLatticeCovering.Blocks





end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIB3_Slc.LatticeCovering_Lines
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped BigOperators
open Real
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set
noncomputable section
open scoped BigOperators
open MeasureTheory Set
noncomputable section
open Module Submodule MeasureTheory
open scoped BigOperators
noncomputable section
open Real Filter Topology
noncomputable section
open scoped BigOperators
noncomputable section
open Filter Topology Asymptotics
noncomputable section
open scoped BigOperators
open Classical
noncomputable section
open scoped BigOperators
open Classical
noncomputable section
open scoped BigOperators
open Classical

namespace SingleLatticeCovering.Folded
open Filter Topology Real ConstructionA Blocks
open scoped BigOperators
universe u


def eligible (b p : ℕ) [NeZero p] : Finset (Fin b → ZMod p) :=
  gridEligible (height b) (logMean (height b)) ((b : ℝ)^(56/100 : ℝ)) ((b : ℝ)^(70/100 : ℝ)) p

def anchorWeight (b p : ℕ) (z : Fin b → ZMod p) : ℝ := folded (height b) (anchor p z)

def blockFunction (b p : ℕ) [Fact p.Prime] (U : Finset (Fin b → ZMod p))
    (v : Fin b → ZMod p) : (Fin b → ZMod p) → ℝ :=
  lineMax (K := ZMod p) (sparseWeight (K := ZMod p) U (anchorWeight b p)) v




end SingleLatticeCovering.Folded

namespace SingleLatticeCovering.Folded
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
open Filter Topology


def balanced (h : ℝ) (t : ι → ℝ) : Finset ι :=
  Finset.univ.filter (fun j => |t j-1/2| ≤ (h^2)⁻¹)


end SingleLatticeCovering.Folded





noncomputable section
open scoped BigOperators

namespace SingleLatticeCovering.Vertical

variable {E V W : Type*} [Fintype E]

def join (P : E → Finset V) (point : E → W) : Finset (V × W) := by
  classical
  exact Finset.univ.biUnion (fun e => (P e).image (fun x => (x,point e)))



def SuffixBinary {m : ℕ} (P : Finset (Fin m → ℝ)) : Prop :=
  ∀ j : Fin m, ∀ y : Fin m → ℝ, ∃ a : ℝ, ∀ x ∈ P,
    (∀ k, j<k → x k=y k) → x j=a ∨ x j=a+1

def bits (b : ℕ) (lam : Fin b → ℝ) (e : Fin b → Bool) : Fin b → ℝ :=
  fun j => lam j + if e j then 1 else 0


end SingleLatticeCovering.Vertical


end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIB3_Slc.LatticeCovering_Chains
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped BigOperators
open Real
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set
noncomputable section
open scoped BigOperators
open MeasureTheory Set
noncomputable section
open Module Submodule MeasureTheory
open scoped BigOperators
noncomputable section
open Real Filter Topology
noncomputable section
open scoped BigOperators
noncomputable section
open Filter Topology Asymptotics
noncomputable section
open scoped BigOperators
open Classical
noncomputable section
open scoped BigOperators
open Classical
noncomputable section
open scoped BigOperators
open Classical
noncomputable section
open scoped BigOperators

namespace SingleLatticeCovering.Vertical
open scoped BigOperators


def concat {m b : ℕ} (P : (Fin b → Bool) → Finset (Fin m → ℝ))
    (lam : Fin b → ℝ) : Finset (Fin (m+b) → ℝ) := by
  classical
  exact (join P (bits b lam)).image (fun x => Fin.append x.1 x.2)


end SingleLatticeCovering.Vertical

namespace SingleLatticeCovering.Vertical
open Folded ConstructionA Blocks
open scoped BigOperators


structure Block where
  b : ℕ
  p : ℕ
  prime : p.Prime
  h : ℝ
  h_pos : 0 < h
  usable : Finset (Fin b → ZMod p)
  direction : Fin b → ZMod p
  direction_ne : direction ≠ 0

namespace Block
abbrev Group (B : Block) := Fin B.b → ZMod B.p
abbrev Vec (B : Block) := Fin B.b → ℝ
instance instFactPrimeP (B : Block) : Fact B.p.Prime := ⟨B.prime⟩

def lattice (B : Block) : Submodule ℤ B.Vec :=
  codeLattice B.p (Submodule.span (ZMod B.p) {B.direction})

def g (B : Block) : B.Group → ℝ :=
  lineMax (K := ZMod B.p) (sparseWeight (K := ZMod B.p) B.usable
    (fun z => folded B.h (anchor B.p z))) B.direction

def grid (B : Block) (y : B.Vec) : B.Group :=
  residue B.p (floorVector B.p (fun j => y j/B.h))

def weight (B : Block) (y l : B.Vec) : ℝ :=
  B.h^B.b/(B.p : ℝ)*gamma (fun j => y j-B.h*l j)

def det (B : Block) : ℝ := B.h^B.b/(B.p : ℝ)


def shift (A B : Block) (w : Fin B.b → A.Group) (l : B.Vec) : A.Vec :=
  fun j => A.h/(A.p : ℝ)*∑ k, ((w k j).val : ℝ)*l k



end Block
end SingleLatticeCovering.Vertical

namespace SingleLatticeCovering.Vertical
open Folded ConstructionA Blocks
open scoped BigOperators



inductive Chain : Block → Type
  | base (B : Block) : Chain B
  | append {A : Block} (c : Chain A) (B : Block)
      (w : Fin B.b → A.Group) : Chain B

namespace Chain
variable {A B : Block}

abbrev dim : {B : Block} → Chain B → ℕ
  | _, .base B => B.b
  | _, .append c B _ => c.dim+B.b

abbrev Vec (c : Chain B) := Fin c.dim → ℝ

def last : {B : Block} → (c : Chain B) → c.Vec → B.Vec
  | _, .base _, y => y
  | _, .append c _ _, y => fun j => y (Fin.natAdd c.dim j)

def subLast : {B : Block} → (c : Chain B) → c.Vec → B.Vec → c.Vec
  | _, .base _, y, t => y-t
  | _, .append c _ _, y, t =>
      Fin.append (fun j => y (Fin.castAdd _ j)) (fun j => y (Fin.natAdd c.dim j)-t j)

@[simp] lemma last_subLast (c : Chain B) (y : c.Vec) (t : B.Vec) :
    c.last (c.subLast y t) = c.last y-t := by
  cases c <;> simp [last, subLast, Pi.sub_def]


def RawMem : {B : Block} → (c : Chain B) → c.Vec → Prop
  | _, .base B, l => l ∈ B.lattice
  | _, .append c B _, l =>
      c.RawMem (fun j => l (Fin.castAdd B.b j)) ∧
      (fun j => l (Fin.natAdd c.dim j)) ∈ B.lattice



def weight : {B : Block} → (c : Chain B) → c.Vec → c.Vec → ℝ
  | _, .base B, y, l => B.weight y l
  | _, .append (A := A) c B w, y, l =>
      c.weight (c.subLast (fun j => y (Fin.castAdd B.b j))
        (A.shift B w (fun j => l (Fin.natAdd c.dim j))))
        (fun j => l (Fin.castAdd B.b j)) *
      B.weight (fun j => y (Fin.natAdd c.dim j)) (fun j => l (Fin.natAdd c.dim j))

def Residual : {B : Block} → (c : Chain B) → c.Vec → c.Vec → Prop
  | _, .base B, y, l => ∀ j, |y j-B.h*l j| ≤ B.h
  | _, .append (A := A) c B w, y, l =>
      c.Residual (c.subLast (fun j => y (Fin.castAdd B.b j))
        (A.shift B w (fun j => l (Fin.natAdd c.dim j))))
        (fun j => l (Fin.castAdd B.b j)) ∧
      ∀ j, |y (Fin.natAdd c.dim j)-B.h*l (Fin.natAdd c.dim j)| ≤ B.h



def coefficient (loss : Block → ℝ) : {B : Block} → Chain B → ℝ
  | _, .base B => Real.exp (-((B.b : ℝ)*B.h^2/B.p))
  | _, .append (A := A) c B _ =>
      c.coefficient loss * Real.exp (-((B.b : ℝ)*B.h^2/B.p)) * (1-loss B)*(1-loss A)

def Good (loss : Block → ℝ) : {B : Block} → Chain B → Prop
  | _, .base _ => True
  | _, .append (A := A) c B w =>
      c.Good loss ∧ 0 ≤ 1-loss B ∧ 0 ≤ 1-loss A ∧
      1-loss A ≤ (𝔼 x, A.g x) ∧
      ∀ z ∈ B.usable, ∀ x : A.Group,
        (1-loss B)*(𝔼 y, A.g y) ≤
          ∑ e : Fin B.b → Bool, wordMass B.h (anchor B.p z) e * A.g (x-Bits.groupShift w e)


end Chain
end SingleLatticeCovering.Vertical

namespace SingleLatticeCovering.Vertical
open Folded Blocks ConstructionA Filter Topology
open scoped BigOperators

def blockLoss (A : ℝ) (B : Block) : ℝ := A*(B.b : ℝ)^(-(1/100 : ℝ))


def Regular (A : ℝ) (B : Block) : Prop :=
  B.h = height B.b ∧
  (B.b : ℝ)*logMean (height B.b)-4*(B.b : ℝ)^(56/100 : ℝ) ≤ Real.log B.p ∧
  Real.log B.p ≤ (B.b : ℝ)*logMean (height B.b)-3*(B.b : ℝ)^(56/100 : ℝ) ∧
  B.usable ⊆ eligible B.b B.p ∧
  |(𝔼 x, B.g x)-1| ≤ blockLoss A B ∧
  (∀ x, B.g x ≤ Real.exp (5*(B.b : ℝ)^(56/100 : ℝ)))


end SingleLatticeCovering.Vertical

namespace SingleLatticeCovering.Vertical
open Folded ConstructionA Blocks
open scoped BigOperators
namespace Block

def roundingLoss (B : Block) : ℝ := (B.b : ℝ)*B.h^2/(B.p : ℝ)
end Block

namespace Chain
variable {A B : Block}

def first : {B : Block} → Chain B → Block
  | _, .base B => B
  | _, .append c _ _ => c.first

def Every (P : Block → Prop) : {B : Block} → Chain B → Prop
  | _, .base B => P B
  | _, .append c B _ => c.Every P ∧ P B

def blockSum (f : Block → ℝ) : {B : Block} → Chain B → ℝ
  | _, .base B => f B
  | _, .append c B _ => c.blockSum f+f B

def Halving : {B : Block} → Chain B → Prop
  | _, .base _ => True
  | _, .append (A := A) c B _ => c.Halving ∧ 2*B.b ≤ A.b



end Chain
end SingleLatticeCovering.Vertical

namespace SingleLatticeCovering.Vertical
open Folded ConstructionA Blocks Filter Topology
open scoped BigOperators


def nextSize (b : ℕ) : ℕ := ⌈(b : ℝ)^(9/10 : ℝ)⌉₊

namespace Chain
variable {B : Block}
def CeilingSizes : {B : Block} → Chain B → Prop
  | _, .base _ => True
  | _, .append (A := A) c B _ => c.CeilingSizes ∧ B.b=nextSize A.b
end Chain



end SingleLatticeCovering.Vertical

end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIB3_Slc.LatticeCovering_Products
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped BigOperators
open Real
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set
noncomputable section
open scoped BigOperators
open MeasureTheory Set
noncomputable section
open Module Submodule MeasureTheory
open scoped BigOperators
noncomputable section
open Real Filter Topology
noncomputable section
open scoped BigOperators
noncomputable section
open Filter Topology Asymptotics
noncomputable section
open scoped BigOperators
open Classical
noncomputable section
open scoped BigOperators
open Classical
noncomputable section
open scoped BigOperators
open Classical
noncomputable section
open scoped BigOperators
noncomputable section
open Module MeasureTheory

namespace SingleLatticeCovering.LatticeGeometry


def appendEquiv (m n : ℕ) : ((Fin m → ℝ) × (Fin n → ℝ)) ≃ₗ[ℝ] (Fin (m+n) → ℝ) :=
  { Fin.appendEquiv m n with
    map_add' := by
      intro x y
      ext j
      refine Fin.addCases ?_ ?_ j <;> intro k <;> simp [Fin.appendEquiv]
    map_smul' := by
      intro a x
      ext j
      refine Fin.addCases ?_ ?_ j <;> intro k <;> simp [Fin.appendEquiv] }

@[simp] lemma appendEquiv_apply (m n : ℕ) (x : (Fin m → ℝ) × (Fin n → ℝ)) :
    appendEquiv m n x = Fin.append x.1 x.2 := rfl
@[simp] lemma appendEquiv_symm_apply (m n : ℕ) (y : Fin (m+n) → ℝ) :
    (appendEquiv m n).symm y =
      (fun j => y (Fin.castAdd n j),fun j => y (Fin.natAdd m j)) := rfl

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

instance prod_discrete (L : Submodule ℤ E) (N : Submodule ℤ F)
    [DiscreteTopology L] [DiscreteTopology N] : DiscreteTopology (L.prod N) :=
  (Homeomorph.Set.prod (L : Set E) (N : Set F)).symm.discreteTopology

instance prod_full (L : Submodule ℤ E) (N : Submodule ℤ F)
    [DiscreteTopology L] [DiscreteTopology N] [IsZLattice ℝ L] [IsZLattice ℝ N] :
    IsZLattice ℝ (L.prod N) := by
  constructor
  change Submodule.span ℝ ((L : Set E) ×ˢ (N : Set F)) = ⊤
  rw [Submodule.span_prod_eq ℝ L.zero_mem N.zero_mem, IsZLattice.span_top, IsZLattice.span_top]
  ext x
  simp

def prodSubtypeEquiv (L : Submodule ℤ E) (N : Submodule ℤ F) :
    (L.prod N) ≃ₗ[ℤ] (L × N) where
  toFun x := (⟨x.1.1,x.2.1⟩,⟨x.1.2,x.2.2⟩)
  invFun x := ⟨(x.1.1,x.2.1),x.1.2,x.2.2⟩
  left_inv := by intro x; rfl
  right_inv := by intro x; rfl
  map_add' := by intro x y; rfl
  map_smul' := by intro a x; rfl

abbrev finProduct {m n : ℕ} (L : Submodule ℤ (Fin m → ℝ))
    (N : Submodule ℤ (Fin n → ℝ)) : Submodule ℤ (Fin (m+n) → ℝ) :=
  ZLattice.comap ℝ (L.prod N) (appendEquiv m n).symm.toLinearMap

@[simp] lemma mem_finProduct {m n : ℕ} (L : Submodule ℤ (Fin m → ℝ))
    (N : Submodule ℤ (Fin n → ℝ)) (x : Fin (m+n) → ℝ) :
    x ∈ finProduct L N ↔
      (fun j => x (Fin.castAdd n j)) ∈ L ∧ (fun j => x (Fin.natAdd m j)) ∈ N := Iff.rfl

instance finProduct_discrete {m n : ℕ} (L : Submodule ℤ (Fin m → ℝ))
    (N : Submodule ℤ (Fin n → ℝ)) [DiscreteTopology L] [DiscreteTopology N] :
    DiscreteTopology (finProduct L N) := by
  change DiscreteTopology (ZLattice.comap ℝ (L.prod N)
    (appendEquiv m n).symm.toContinuousLinearEquiv.toLinearMap)
  infer_instance

instance finProduct_full {m n : ℕ} (L : Submodule ℤ (Fin m → ℝ))
    (N : Submodule ℤ (Fin n → ℝ)) [DiscreteTopology L] [DiscreteTopology N]
    [IsZLattice ℝ L] [IsZLattice ℝ N] : IsZLattice ℝ (finProduct L N) := by
  change IsZLattice ℝ (ZLattice.comap ℝ (L.prod N)
    (appendEquiv m n).symm.toContinuousLinearEquiv.toLinearMap)
  infer_instance

def finProductBasis {m n : ℕ} (L : Submodule ℤ (Fin m → ℝ))
    (N : Submodule ℤ (Fin n → ℝ)) (b : Basis (Fin m) ℤ L) (c : Basis (Fin n) ℤ N) :
    Basis (Fin (m+n)) ℤ (finProduct L N) :=
  (((b.prod c).map (prodSubtypeEquiv L N).symm).ofZLatticeComap ℝ (L.prod N)
    (appendEquiv m n).symm).reindex finSumFinEquiv


end SingleLatticeCovering.LatticeGeometry

namespace SingleLatticeCovering.LatticeGeometry
open Module MeasureTheory
variable {ι : Type*} [Fintype ι] [DecidableEq ι]


abbrev image (L : Submodule ℤ (ι → ℝ)) (e : (ι → ℝ) ≃ₗ[ℝ] (ι → ℝ)) : Submodule ℤ (ι → ℝ) :=
  ZLattice.comap ℝ L e.symm.toLinearMap

instance image_discrete (L : Submodule ℤ (ι → ℝ)) (e : (ι → ℝ) ≃ₗ[ℝ] (ι → ℝ))
    [DiscreteTopology L] : DiscreteTopology (image L e) := by
  change DiscreteTopology (ZLattice.comap ℝ L e.symm.toContinuousLinearEquiv.toLinearMap)
  infer_instance

instance image_full (L : Submodule ℤ (ι → ℝ)) (e : (ι → ℝ) ≃ₗ[ℝ] (ι → ℝ))
    [DiscreteTopology L] [IsZLattice ℝ L] : IsZLattice ℝ (image L e) := by
  change IsZLattice ℝ (ZLattice.comap ℝ L e.symm.toContinuousLinearEquiv.toLinearMap)
  infer_instance


end SingleLatticeCovering.LatticeGeometry

namespace SingleLatticeCovering.LatticeGeometry
open Module MeasureTheory



def triangular {m n : ℕ} (e : (Fin m → ℝ) ≃ₗ[ℝ] (Fin m → ℝ))
    (f : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ)) (S : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ)) :
    (Fin (m+n) → ℝ) ≃ₗ[ℝ] (Fin (m+n) → ℝ) where
  toFun x := Fin.append (e (fun j => x (Fin.castAdd n j)) + S (fun j => x (Fin.natAdd m j)))
    (f (fun j => x (Fin.natAdd m j)))
  invFun y := Fin.append
    (e.symm ((fun j => y (Fin.castAdd n j))-S (f.symm (fun j => y (Fin.natAdd m j)))))
    (f.symm (fun j => y (Fin.natAdd m j)))
  left_inv := by
    intro x
    simp only [Fin.append_left, Fin.append_right, LinearEquiv.symm_apply_apply,
      add_sub_cancel_right]
    exact (Fin.appendEquiv m n).apply_symm_apply x
  right_inv := by
    intro y
    simp only [Fin.append_left, Fin.append_right, LinearEquiv.apply_symm_apply,
      sub_add_cancel]
    exact (Fin.appendEquiv m n).apply_symm_apply y
  map_add' := by
    intro x y
    ext j
    refine Fin.addCases ?_ ?_ j <;> intro k
    · simp only [Fin.append_left, Pi.add_apply]
      change e ((fun j => x (Fin.castAdd n j)) + (fun j => y (Fin.castAdd n j))) k +
        S ((fun j => x (Fin.natAdd m j)) + (fun j => y (Fin.natAdd m j))) k = _
      simp only [map_add, Pi.add_apply]
      ring
    · simp only [Fin.append_right, Pi.add_apply]
      change f ((fun j => x (Fin.natAdd m j)) + (fun j => y (Fin.natAdd m j))) k = _
      simp only [map_add, Pi.add_apply]
  map_smul' := by
    intro a x
    ext j
    refine Fin.addCases ?_ ?_ j <;> intro k
    · simp only [Fin.append_left, Pi.add_apply, Pi.smul_apply, RingHom.id_apply]
      change e (a • (fun j => x (Fin.castAdd n j))) k +
        S (a • (fun j => x (Fin.natAdd m j))) k = _
      simp only [map_smul, Pi.smul_apply, smul_eq_mul]
      ring
    · simp only [Fin.append_right, Pi.smul_apply, RingHom.id_apply]
      change f (a • (fun j => x (Fin.natAdd m j))) k = _
      simp only [map_smul, Pi.smul_apply, smul_eq_mul]

@[simp] lemma triangular_append {m n : ℕ}
    (e : (Fin m → ℝ) ≃ₗ[ℝ] (Fin m → ℝ))
    (f : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ)) (S : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (x : Fin m → ℝ) (y : Fin n → ℝ) :
    triangular e f S (Fin.append x y) = Fin.append (e x+S y) (f y) := by
  simp [triangular]


end SingleLatticeCovering.LatticeGeometry

namespace SingleLatticeCovering.Vertical
open Folded ConstructionA Blocks LatticeGeometry
open scoped BigOperators

namespace Block
instance lattice_discrete (B : Block) : DiscreteTopology B.lattice :=
  Classical.choose (line_lattice B.p B.direction B.direction_ne)
instance lattice_full (B : Block) : IsZLattice ℝ B.lattice :=
  (Classical.choose_spec (line_lattice B.p B.direction B.direction_ne)).1

def linear (B : Block) : B.Vec ≃ₗ[ℝ] B.Vec :=
  LinearEquiv.smulOfNeZero ℝ B.Vec B.h B.h_pos.ne'
@[simp] lemma linear_apply (B : Block) (l : B.Vec) : B.linear l = B.h • l := rfl

def shiftMap (A B : Block) (w : Fin B.b → A.Group) : B.Vec →ₗ[ℝ] A.Vec :=
  Matrix.mulVecLin (fun j k => A.h/(A.p : ℝ)*((w k j).val : ℝ))
@[simp] lemma shiftMap_apply (A B : Block) (w : Fin B.b → A.Group) (l : B.Vec) :
    A.shiftMap B w l = A.shift B w l := by
  ext j
  change (∑ k, (A.h/(A.p : ℝ)*((w k j).val : ℝ))*l k) =
    A.h/(A.p : ℝ)*∑ k, ((w k j).val : ℝ)*l k
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  ring
end Block

namespace Chain
variable {A B : Block}

def injectLast : {B : Block} → (c : Chain B) → B.Vec →ₗ[ℝ] c.Vec
  | _, .base _ => LinearMap.id
  | _, .append c B _ => (appendEquiv c.dim B.b).toLinearMap.comp (LinearMap.inr ℝ c.Vec B.Vec)

abbrev rawLattice : {B : Block} → (c : Chain B) → Submodule ℤ c.Vec
  | _, .base B => B.lattice
  | _, .append c B _ => finProduct c.rawLattice B.lattice
instance raw_discrete (c : Chain B) : DiscreteTopology c.rawLattice := by
  induction c with
  | base B => exact B.lattice_discrete
  | append c B w ih => let := ih; exact finProduct_discrete _ _
instance raw_full (c : Chain B) : IsZLattice ℝ c.rawLattice := by
  induction c with
  | base B => exact B.lattice_full
  | append c B w ih => let := ih; exact finProduct_full _ _

def linear : {B : Block} → (c : Chain B) → c.Vec ≃ₗ[ℝ] c.Vec
  | _, .base B => B.linear
  | _, .append (A := A) c B w =>
    triangular c.linear B.linear (c.injectLast.comp (A.shiftMap B w))
def det : {B : Block} → Chain B → ℝ
  | _, .base B => B.det
  | _, .append c B _ => c.det*B.det
abbrev physicalLattice (c : Chain B) : Submodule ℤ c.Vec := image c.rawLattice c.linear



end Chain
end SingleLatticeCovering.Vertical

namespace SingleLatticeCovering.Vertical
open scoped BigOperators


def terminalColumns (b p : ℕ) : Fin (b*Nat.clog 2 p) → Fin b → ZMod p :=
  fun i => Pi.single (finProdFinEquiv.symm i).1
    ((2 : ZMod p)^((finProdFinEquiv.symm i).2 : ℕ))


end SingleLatticeCovering.Vertical

namespace SingleLatticeCovering.Vertical
open Folded ConstructionA Blocks LatticeGeometry Module Submodule MeasureTheory
open scoped BigOperators

abbrev integerLattice (n : ℕ) : Submodule ℤ (Fin n → ℝ) :=
  Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin n)))

namespace Block
abbrev terminalDim (B : Block) : ℕ := B.b*Nat.clog 2 B.p

def shiftDim (B : Block) (d : ℕ) (w : Fin d → B.Group) (l : Fin d → ℝ) : B.Vec :=
  fun j => B.h/(B.p : ℝ)*∑ k, ((w k j).val : ℝ)*l k

def shiftDimMap (B : Block) (d : ℕ) (w : Fin d → B.Group) : (Fin d → ℝ) →ₗ[ℝ] B.Vec :=
  Matrix.mulVecLin (fun j k => B.h/(B.p : ℝ)*((w k j).val : ℝ))
@[simp] lemma shiftDimMap_apply (B : Block) (d : ℕ) (w : Fin d → B.Group) (l : Fin d → ℝ) :
    B.shiftDimMap d w l = B.shiftDim d w l := by
  ext j
  change (∑ k, (B.h/(B.p : ℝ)*((w k j).val : ℝ))*l k) =
    B.h/(B.p : ℝ)*∑ k, ((w k j).val : ℝ)*l k
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  ring

abbrev terminalShift (B : Block) : (Fin B.terminalDim → ℝ) →ₗ[ℝ] B.Vec :=
  B.shiftDimMap B.terminalDim (terminalColumns B.b B.p)



end Block

namespace Chain
variable {B : Block}
abbrev fullDim (c : Chain B) : ℕ := c.dim+B.terminalDim
abbrev FullVec (c : Chain B) := Fin c.fullDim → ℝ
abbrev fullRaw (c : Chain B) : Submodule ℤ c.FullVec := finProduct c.rawLattice (integerLattice B.terminalDim)
def fullLinear (c : Chain B) : c.FullVec ≃ₗ[ℝ] c.FullVec :=
  triangular c.linear (LinearEquiv.refl ℝ _) (c.injectLast.comp B.terminalShift)
abbrev fullLattice (c : Chain B) : Submodule ℤ c.FullVec := image c.fullRaw c.fullLinear



end Chain
end SingleLatticeCovering.Vertical

namespace SingleLatticeCovering.Vertical
open Folded ConstructionA Blocks
open scoped BigOperators

namespace Block

def Selected (B : Block) (y l : B.Vec) : Prop :=
  ∃ z ∈ B.usable, ∃ lam : B.Vec,
    ((fun j => y j/B.h)-lam) ∈ gridCell B.p z ∧
    ∃ e : Fin B.b → Bool, l=bits B.b lam e

end Block

namespace Chain
variable {A B : Block}

def Selected : {B : Block} → (c : Chain B) → c.Vec → c.Vec → Prop
  | _, .base B, y, l => B.Selected y l
  | _, .append (A := A) c B w, y, l =>
      c.Selected (c.subLast (fun j => y (Fin.castAdd B.b j))
        (A.shift B w (fun j => l (Fin.natAdd c.dim j))))
        (fun j => l (Fin.castAdd B.b j)) ∧
      B.Selected (fun j => y (Fin.natAdd c.dim j)) (fun j => l (Fin.natAdd c.dim j))


end Chain
end SingleLatticeCovering.Vertical


end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIB3_Slc.LatticeCovering_Residuals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open scoped BigOperators
open Real
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set
noncomputable section
open scoped BigOperators
open MeasureTheory Set
noncomputable section
open Module Submodule MeasureTheory
open scoped BigOperators
noncomputable section
open Real Filter Topology
noncomputable section
open scoped BigOperators
noncomputable section
open Filter Topology Asymptotics
noncomputable section
open scoped BigOperators
open Classical
noncomputable section
open scoped BigOperators
open Classical
noncomputable section
open scoped BigOperators
open Classical
noncomputable section
open scoped BigOperators
noncomputable section
open Module MeasureTheory

namespace SingleLatticeCovering.Vertical
open Folded ConstructionA Blocks LatticeGeometry Module Submodule MeasureTheory
open scoped BigOperators

namespace Chain
variable {B : Block}

def FullResidual (c : Chain B) (y l : c.FullVec) : Prop :=
  c.Residual (c.subLast (fun j => y (Fin.castAdd B.terminalDim j))
    (B.terminalShift (fun j => l (Fin.natAdd c.dim j))))
    (fun j => l (Fin.castAdd B.terminalDim j)) ∧
  ∀ j, |y (Fin.natAdd c.dim j)-l (Fin.natAdd c.dim j)| ≤ 1

def FullSelected (c : Chain B) (y l : c.FullVec) : Prop :=
  c.Selected (c.subLast (fun j => y (Fin.castAdd B.terminalDim j))
    (B.terminalShift (fun j => l (Fin.natAdd c.dim j))))
    (fun j => l (Fin.castAdd B.terminalDim j))




end Chain
end SingleLatticeCovering.Vertical

namespace SingleLatticeCovering.Vertical
open Folded ConstructionA Blocks LatticeGeometry Module Submodule MeasureTheory
open scoped BigOperators

namespace Chain
variable {A B : Block}

def heights : {B : Block} → (c : Chain B) → c.Vec
  | _, .base B => fun _ => B.h
  | _, .append c B _ => Fin.append c.heights (fun _ => B.h)

def radiusSq (c : Chain B) : ℝ := c.blockSum (fun Q => (Q.b : ℝ)*Q.h^2)

def AtomBound (q : Block → ℝ) (B : Block) : Prop :=
  ∀ z ∈ B.usable, ∀ t : B.Vec, t ∈ gridCell B.p z →
    ∀ e : Fin B.b → Bool, atom B.h t e/(B.p : ℝ) ≤ q B



end Chain
end SingleLatticeCovering.Vertical

namespace SingleLatticeCovering.Vertical
open Folded ConstructionA Blocks LatticeGeometry
open scoped BigOperators

namespace Chain
variable {B : Block}

def alphabetRadius (c : Chain B) : ℕ := 1+(c.fullDim+2)^c.fullDim


def denominators : {B : Block} → (c : Chain B) → Fin c.dim → ℕ
  | _, .base B => fun _ => B.p
  | _, .append c B _ => Fin.append c.denominators (fun _ => B.p)

def fullDenominators (c : Chain B) : Fin c.fullDim → ℕ :=
  Fin.append c.denominators (fun _ => 1)

end Chain


noncomputable def rationalAlphabet (Q p : ℕ) : Finset ℝ :=
  (Finset.Icc (-(Q*p : ℤ)) (Q*p : ℤ)).image (fun k : ℤ => (k : ℝ)/(p : ℝ))

noncomputable def Chain.alphabets {B : Block} (c : Chain B) : Fin c.fullDim → Finset ℝ :=
  fun j => rationalAlphabet c.alphabetRadius (c.fullDenominators j)


end SingleLatticeCovering.Vertical


end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIB3_Slc.LatticeCovering_Patterns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section





noncomputable section
open MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal Pointwise
namespace SingleLatticeCovering.Shear

section Haar
variable {T : Type*} [AddCommGroup T] [MeasurableSpace T]
  [MeasurableAdd₂ T] [MeasurableNeg T]
  (μ : Measure T) [IsProbabilityMeasure μ] [IsAddLeftInvariant μ] [IsNegInvariant μ]



def translate (A : Set T) (t : T) : Set T := (fun x => x-t) ⁻¹' A

end Haar

end SingleLatticeCovering.Shear

namespace SingleLatticeCovering.Shear

universe u



inductive Pattern (α : Type u) : ℕ → Type u where
  | leaf (a : α) : Pattern α 0
  | mono {q : ℕ} (v : ℝ) (p : Pattern α q) : Pattern α (q+1)
  | split {q : ℕ} (v : ℝ) (p r : Pattern α q) : Pattern α (q+1)

namespace Pattern
variable {α : Type*}

def size : {q : ℕ} → Pattern α q → ℕ
  | _, .leaf _ => 1
  | _, .mono _ p => p.size
  | _, .split _ p r => p.size+r.size

lemma size_pos {q : ℕ} (p : Pattern α q) : 0 < p.size := by
  induction p with
  | leaf => exact Nat.zero_lt_one
  | mono v p ih => exact ih
  | split v p r ih ihr => exact Nat.add_pos_left ih _

def weight (L : ℝ≥0∞) (η : α → ℝ≥0∞) : {q : ℕ} → Pattern α q → ℝ≥0∞
  | _, .leaf a => η a
  | _, .mono _ p => p.weight L η
  | _, .split _ p r => L * p.weight L η * r.weight L η

def labelProduct (η : α → ℝ≥0∞) : {q : ℕ} → Pattern α q → ℝ≥0∞
  | _, .leaf a => η a
  | _, .mono _ p => p.labelProduct η
  | _, .split _ p r => p.labelProduct η * r.labelProduct η

def first {q : ℕ} : Pattern α (q+1) → Pattern α q
  | .mono _ p => p
  | .split _ p _ => p

def second {q : ℕ} : Pattern α (q+1) → Pattern α q
  | .mono _ p => p
  | .split _ _ r => r

def branches {q : ℕ} : Pattern α (q+1) → Prop
  | .mono _ _ => False
  | .split _ _ _ => True

section Evaluation
variable {E T : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup T]

def failure (π : E →+ T) (U : α → Set T) : {q : ℕ} → Pattern α q → (Fin q → E) → Set T
  | _, .leaf a, _ => U a
  | _, .mono v p, Z => translate (p.failure π U (Fin.init Z)) (π (v • Z (Fin.last _)))
  | _, .split v p r, Z =>
    translate (p.failure π U (Fin.init Z)) (π (v • Z (Fin.last _))) ∩
    translate (r.failure π U (Fin.init Z)) (π ((v+1) • Z (Fin.last _)))

end Evaluation
end Pattern



def restrictColumns {E : Type*} {q d : ℕ} (h : q ≤ d) (Z : Fin d → E) : Fin q → E :=
  fun i => Z (Fin.castLE h i)

@[simp] lemma restrictColumns_self {E : Type*} {d : ℕ} (Z : Fin d → E) :
    restrictColumns (le_refl d) Z = Z := rfl

def SliceClosed {α : Type*} (P : (q : ℕ) → Finset (Pattern α q)) (D : ℕ) : Prop :=
  ∀ q < D, ∀ p ∈ P (q+1), p.first ∈ P q ∧ p.second ∈ P q

end SingleLatticeCovering.Shear

namespace SingleLatticeCovering.Shear.Pattern
variable {α : Type*}
local instance instDecidableEqProdForallFinReal {q : ℕ} : DecidableEq ((Fin q → ℝ) × α) := Classical.decEq _



def appendPoint {q : ℕ} (v : ℝ) (l : (Fin q → ℝ) × α) : (Fin (q+1) → ℝ) × α :=
  (Fin.snoc l.1 v, l.2)

lemma appendPoint_injective {q : ℕ} (v : ℝ) :
    Function.Injective (appendPoint (α := α) (q := q) v) := by
  intro x y h
  have h1 := congrArg (fun l : (Fin (q+1) → ℝ) × α => Fin.init l.1) h
  have h2 := congrArg Prod.snd h
  exact Prod.ext (by simpa only [appendPoint, Fin.init_snoc] using h1) h2

lemma appendPoint_disjoint {q : ℕ} (v : ℝ) (s t : Finset ((Fin q → ℝ) × α)) :
    Disjoint (s.image (appendPoint v)) (t.image (appendPoint (v+1))) := by
  classical
  apply Finset.disjoint_left.mpr
  intro x hx hy
  obtain ⟨a,ha,hax⟩ := Finset.mem_image.mp hx
  obtain ⟨b,hb,hbx⟩ := Finset.mem_image.mp hy
  have h := congrArg (fun l : (Fin (q+1) → ℝ) × α => l.1 (Fin.last q)) (hax.trans hbx.symm)
  simp only [appendPoint, Fin.snoc_last] at h
  linarith


def points : {q : ℕ} → Pattern α q → Finset ((Fin q → ℝ) × α)
  | _, .leaf a => {(0,a)}
  | _, .mono v p => by classical exact p.points.image (appendPoint v)
  | _, .split v p r => by
    classical
    exact p.points.image (appendPoint v) ∪ r.points.image (appendPoint (v+1))

lemma points_card {q : ℕ} (p : Pattern α q) : p.points.card = p.size := by
  classical
  induction p with
  | leaf a => simp [points, size]
  | mono v p ih =>
    simp only [points, Finset.card_image_of_injective _ (appendPoint_injective _), size, ih]
  | split v p r ih ihr =>
    rw [points, Finset.card_union_of_disjoint (appendPoint_disjoint _ _ _)]
    simp only [Finset.card_image_of_injective _ (appendPoint_injective _), size, ih, ihr]

lemma points_nonempty {q : ℕ} (p : Pattern α q) : p.points.Nonempty := by
  rw [← Finset.card_pos, points_card]
  exact p.size_pos

section Semantics
variable {E T : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup T]

def linearShift {q : ℕ} (Z : Fin q → E) (x : Fin q → ℝ) : E := ∑ i, x i • Z i

end Semantics
end SingleLatticeCovering.Shear.Pattern


end
end
end

end OAI
end

section
-- module Solutions.OAIB3_Slc.LatticeCovering_Shears
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal Pointwise

namespace SingleLatticeCovering.Shear.Pattern
variable {α : Type*}
local instance instDecidableEqProdForallFinReal_1 {q : ℕ} : DecidableEq ((Fin q → ℝ) × α) := Classical.decEq _


def slice {q : ℕ} (s : Finset ((Fin (q+1) → ℝ) × α)) (v : ℝ) :
    Finset ((Fin q → ℝ) × α) := by
  classical
  exact (s.filter (fun l => l.1 (Fin.last q) = v)).image (fun l => (Fin.init l.1,l.2))

lemma mem_slice {q : ℕ} (s : Finset ((Fin (q+1) → ℝ) × α)) (v : ℝ)
    (l : (Fin q → ℝ) × α) : l ∈ slice s v ↔ appendPoint v l ∈ s := by
  classical
  simp only [slice, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨a, ⟨ha,hav⟩,hal⟩
    have heq : appendPoint v l = a := by
      rw [← hal]
      simp only [appendPoint, ← hav, Fin.snoc_init_self]
    simpa only [heq] using ha
  · intro hl
    refine ⟨appendPoint v l, ⟨hl, by simp [appendPoint]⟩, ?_⟩
    simp only [appendPoint, Fin.init_snoc]

lemma slice_image {q : ℕ} (s : Finset ((Fin q → ℝ) × α)) (a v : ℝ) :
    slice (s.image (appendPoint a)) v = if a=v then s else ∅ := by
  classical
  ext l
  rw [mem_slice]
  simp only [Finset.mem_image]
  by_cases hav : a=v
  · subst v
    simp only [↓reduceIte, (appendPoint_injective a).eq_iff, exists_eq_right]
  · simp only [hav, ↓reduceIte, Finset.notMem_empty, iff_false, not_exists, not_and]
    intro b hb heq
    have h := congrArg (fun x : (Fin (q+1) → ℝ) × α => x.1 (Fin.last q)) heq
    simp only [appendPoint, Fin.snoc_last] at h
    exact hav h

lemma slice_union {q : ℕ} (s t : Finset ((Fin (q+1) → ℝ) × α)) (v : ℝ) :
    slice (s ∪ t) v = slice s v ∪ slice t v := by
  classical
  ext l
  simp only [mem_slice, Finset.mem_union]

@[simp] lemma slice_mono {q : ℕ} (v : ℝ) (p : Pattern α q) :
    slice (Pattern.mono v p).points v = p.points := by
  simp [points, slice_image]

@[simp] lemma slice_split_left {q : ℕ} (v : ℝ) (p r : Pattern α q) :
    slice (Pattern.split v p r).points v = p.points := by
  simp [points, slice_union, slice_image]

@[simp] lemma slice_split_right {q : ℕ} (v : ℝ) (p r : Pattern α q) :
    slice (Pattern.split v p r).points (v+1) = r.points := by
  simp [points, slice_union, slice_image]

lemma height_mono {q : ℕ} {v : ℝ} {p : Pattern α q}
    {l : (Fin (q+1) → ℝ) × α} (hl : l ∈ (Pattern.mono v p).points) :
    l.1 (Fin.last q) = v := by
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hl
  simp only [appendPoint, Fin.snoc_last]

lemma height_split {q : ℕ} {v : ℝ} {p r : Pattern α q}
    {l : (Fin (q+1) → ℝ) × α} (hl : l ∈ (Pattern.split v p r).points) :
    l.1 (Fin.last q) = v ∨ l.1 (Fin.last q) = v+1 := by
  rcases Finset.mem_union.mp hl with hl | hl
  · exact Or.inl (height_mono (p := p) hl)
  · exact Or.inr (height_mono (p := r) hl)

lemma mono_base_unique {q : ℕ} {v w : ℝ} {p r : Pattern α q}
    (h : (Pattern.mono v p).points = (Pattern.mono w r).points) : v=w := by
  obtain ⟨a,ha⟩ := p.points_nonempty
  have hm : appendPoint v a ∈ (Pattern.mono w r).points := by rw [← h]; exact Finset.mem_image.mpr ⟨a,ha,rfl⟩
  simpa only [appendPoint, Fin.snoc_last] using height_mono hm

lemma mono_ne_split {q : ℕ} (v w : ℝ) (p r s : Pattern α q) :
    (Pattern.mono v p).points ≠ (Pattern.split w r s).points := by
  intro h
  obtain ⟨a,ha⟩ := r.points_nonempty
  obtain ⟨b,hb⟩ := s.points_nonempty
  have h1 : appendPoint w a ∈ (Pattern.mono v p).points := by
    rw [h, points]; exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨a,ha,rfl⟩)
  have h2 : appendPoint (w+1) b ∈ (Pattern.mono v p).points := by
    rw [h, points]; exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨b,hb,rfl⟩)
  have h1' := height_mono h1
  have h2' := height_mono h2
  simp only [appendPoint, Fin.snoc_last] at h1' h2'
  linarith

lemma split_base_unique {q : ℕ} {v w : ℝ} {p r s t : Pattern α q}
    (h : (Pattern.split v p r).points = (Pattern.split w s t).points) : v=w := by
  obtain ⟨a,ha⟩ := p.points_nonempty
  obtain ⟨b,hb⟩ := s.points_nonempty
  have h1 : appendPoint v a ∈ (Pattern.split w s t).points := by
    rw [← h, points]; exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨a,ha,rfl⟩)
  have h2 : appendPoint w b ∈ (Pattern.split v p r).points := by
    rw [h, points]; exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨b,hb,rfl⟩)
  have h1' := height_split h1
  have h2' := height_split h2
  simp only [appendPoint, Fin.snoc_last] at h1' h2'
  rcases h1' with h1' | h1'
  · exact h1'
  · rcases h2' with h2' | h2' <;> linarith



lemma points_injective (q : ℕ) : Function.Injective (points (α := α) (q := q)) := by
  induction q with
  | zero =>
    intro p r h
    cases p with
    | leaf a =>
      cases r with
      | leaf b =>
        have : a=b := by simpa [points] using h
        subst b
        rfl
  | succ q ih =>
    intro p z h
    cases p with
    | mono v p =>
      cases z with
      | mono w r =>
        have hv := mono_base_unique h
        subst w
        have hp := congrArg (fun s => slice s v) h
        simp only [slice_mono] at hp
        rw [ih hp]
      | split w r s => exact (mono_ne_split _ _ _ _ _ h).elim
    | split v p r =>
      cases z with
      | mono w s => exact (mono_ne_split _ _ _ _ _ h.symm).elim
      | split w s t =>
        have hv := split_base_unique h
        subst w
        have hp := congrArg (fun s => slice s v) h
        have hr := congrArg (fun s => slice s (v+1)) h
        simp only [slice_split_left] at hp
        simp only [slice_split_right] at hr
        rw [ih hp, ih hr]

end SingleLatticeCovering.Shear.Pattern

namespace SingleLatticeCovering.Shear
variable {α : Type*}
local instance instDecidableEqProdForallFinReal_solutions {q : ℕ} : DecidableEq ((Fin q → ℝ) × α) := Classical.decEq _



def UniqueLabels {q : ℕ} (s : Finset ((Fin q → ℝ) × α)) : Prop :=
  ∀ l ∈ s, ∀ r ∈ s, l.1=r.1 → l.2=r.2




def SuffixBinary {q : ℕ} (s : Finset ((Fin q → ℝ) × α)) : Prop :=
  ∀ j : Fin q, ∀ y : Fin q → ℝ, ∃ v : ℝ, ∀ l ∈ s,
    (∀ k : Fin q, j<k → l.1 k = y k) → l.1 j = v ∨ l.1 j = v+1

def SourcePattern {q : ℕ} (s : Finset ((Fin q → ℝ) × α)) : Prop :=
  s.Nonempty ∧ UniqueLabels s ∧ SuffixBinary s

end SingleLatticeCovering.Shear

namespace SingleLatticeCovering.Shear
open Pattern
variable {α : Type*}


noncomputable def encodeFamily (S : (q : ℕ) → Finset (Finset ((Fin q → ℝ) × α)))
    (q : ℕ) : Finset (Pattern α q) :=
  (S q).preimage Pattern.points (Pattern.points_injective q).injOn

@[simp] lemma mem_encodeFamily (S : (q : ℕ) → Finset (Finset ((Fin q → ℝ) × α)))
    (q : ℕ) (p : Pattern α q) : p ∈ encodeFamily S q ↔ p.points ∈ S q :=
  Finset.mem_preimage


def SourceSliceClosed (S : (q : ℕ) → Finset (Finset ((Fin q → ℝ) × α))) (D : ℕ) : Prop :=
  ∀ q < D, ∀ s ∈ S (q+1), ∀ v : ℝ, (slice s v).Nonempty → slice s v ∈ S q

end SingleLatticeCovering.Shear



namespace SingleLatticeCovering.Shear
open scoped BigOperators

noncomputable def alphabetPoints {α : Type*} (A : ℕ → Finset ℝ) (labels : Finset α) (q : ℕ) :
    Finset ((Fin q → ℝ) × α) :=
  (Fintype.piFinset (fun j : Fin q => A j.val)).product labels

noncomputable def allPatterns {α : Type*} (A : ℕ → Finset ℝ) (labels : Finset α) (q : ℕ) :
    Finset (Finset ((Fin q → ℝ) × α)) := by
  classical
  exact (alphabetPoints A labels q).powerset.filter SourcePattern


end SingleLatticeCovering.Shear

end
end

section



noncomputable section
open MeasureTheory MeasureTheory.Measure Set Module
open scoped Pointwise ENNReal

namespace SingleLatticeCovering.Completion

abbrev Torus (n : ℕ) := Fin n → AddCircle (1 : ℝ)

def torusMeasure (n : ℕ) : Measure (Torus n) := addHaarMeasure ⊤

instance torusMeasure_haar (n : ℕ) : IsAddHaarMeasure (torusMeasure n) :=
  inferInstanceAs (IsAddHaarMeasure (addHaarMeasure ⊤))

instance torusMeasure_probability (n : ℕ) : IsProbabilityMeasure (torusMeasure n) :=
  ⟨addHaarMeasure_self⟩

abbrev RealSpace (n : ℕ) := Fin n → ℝ

def latticeBasis {n : ℕ} (L : Submodule ℤ (RealSpace n))
    [DiscreteTopology L] [IsZLattice ℝ L] : Basis (Fin n) ℝ (RealSpace n) :=
  (IsZLattice.basis L).ofZLatticeBasis ℝ



def latticeProjection {n : ℕ} (L : Submodule ℤ (RealSpace n))
    [DiscreteTopology L] [IsZLattice ℝ L] : RealSpace n →ₜ+ Torus n where
  toFun x i := ((latticeBasis L).equivFun x i : AddCircle (1 : ℝ))
  map_zero' := by ext i; simp
  map_add' x y := by ext i; simp
  continuous_toFun := by
    apply continuous_pi
    intro i
    exact (AddCircle.continuous_mk' (1 : ℝ)).comp
      ((continuous_apply i).comp (latticeBasis L).equivFun.toContinuousLinearEquiv.continuous)



def contractLattice {n : ℕ} (L : Submodule ℤ (RealSpace n)) (a : ℝ) (ha : a ≠ 0) :
    Submodule ℤ (RealSpace n) :=
  ZLattice.comap ℝ L (LinearEquiv.smulOfNeZero ℝ (RealSpace n) a ha).toLinearMap

instance contractLattice_discrete {n : ℕ} (L : Submodule ℤ (RealSpace n))
    [DiscreteTopology L] (a : ℝ) (ha : a ≠ 0) : DiscreteTopology (contractLattice L a ha) := by
  change DiscreteTopology (ZLattice.comap ℝ L
    (LinearEquiv.smulOfNeZero ℝ (RealSpace n) a ha).toContinuousLinearEquiv.toLinearMap)
  infer_instance

instance contractLattice_fullSpan {n : ℕ} (L : Submodule ℤ (RealSpace n))
    [DiscreteTopology L] [IsZLattice ℝ L] (a : ℝ) (ha : a ≠ 0) :
    IsZLattice ℝ (contractLattice L a ha) := by
  change IsZLattice ℝ (ZLattice.comap ℝ L
    (LinearEquiv.smulOfNeZero ℝ (RealSpace n) a ha).toContinuousLinearEquiv.toLinearMap)
  infer_instance



end SingleLatticeCovering.Completion

end
end

end

end OAI
end

section
-- module Solutions.OAIB3_Slc.LatticeCovering_Completion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

namespace SingleLatticeCovering.Vertical
open scoped BigOperators

noncomputable def labelPattern {α : Type*} {D : ℕ}
    (P : Finset (Fin D → ℝ)) (a : (Fin D → ℝ) → α) :
    Finset ((Fin D → ℝ) × α) := by
  classical
  exact P.image (fun l => (l,a l))


end SingleLatticeCovering.Vertical

noncomputable section
namespace SingleLatticeCovering.CoverGeometry
open MeasureTheory LatticeGeometry Completion
open scoped BigOperators Pointwise ENNReal



def columnMap {m D : ℕ} (Z : Fin D → (Fin m → ℝ)) :
    (Fin D → ℝ) →ₗ[ℝ] (Fin m → ℝ) where
  toFun l := ∑ j, l j • Z j
  map_add' l r := by simp [add_smul,Finset.sum_add_distrib]
  map_smul' a l := by simp [Finset.smul_sum,smul_smul]

@[simp] lemma columnMap_apply {m D : ℕ} (Z : Fin D → (Fin m → ℝ)) (l : Fin D → ℝ) :
    columnMap Z l = Shear.Pattern.linearShift Z l := rfl

abbrev joinedLattice {m D : ℕ} (L : Submodule ℤ (Fin m → ℝ))
    (N : Submodule ℤ (Fin D → ℝ)) (M : (Fin D → ℝ) ≃ₗ[ℝ] (Fin D → ℝ))
    (Z : Fin D → (Fin m → ℝ)) : Submodule ℤ (Fin (m+D) → ℝ) :=
  image (finProduct L N) (triangular (LinearEquiv.refl ℝ _) M (columnMap Z))


def horizontalHole {m D : ℕ} (L : Submodule ℤ (Fin m → ℝ))
    [DiscreteTopology L] [IsZLattice ℝ L]
    (K : Set (Fin (m+D) → ℝ)) (Γ : Submodule ℤ (Fin (m+D) → ℝ))
    (y : Fin D → ℝ) : Set (Torus m) :=
  latticeProjection L '' {x | Fin.append x y ∉ K+(Γ : Set (Fin (m+D) → ℝ))}



end SingleLatticeCovering.CoverGeometry

namespace SingleLatticeCovering.CoverGeometry
open MeasureTheory LatticeGeometry Completion Shear
open scoped BigOperators Pointwise ENNReal

instance torusMeasure_neg (n : ℕ) : (torusMeasure n).IsNegInvariant :=
  inferInstanceAs ((Measure.addHaarMeasure ⊤ : Measure (Torus n)).IsNegInvariant)




end SingleLatticeCovering.CoverGeometry

namespace SingleLatticeCovering.CoverGeometry
open MeasureTheory Completion LatticeGeometry
open scoped Pointwise ENNReal


def appendTorus (m D : ℕ) : (Torus m × Torus D) →ₜ+ Torus (m+D) where
  toFun t := Fin.append t.1 t.2
  map_zero' := by ext i; refine Fin.addCases ?_ ?_ i <;> intro k <;> simp
  map_add' x y := by ext i; refine Fin.addCases ?_ ?_ i <;> intro k <;> simp
  continuous_toFun := by
    apply continuous_pi
    intro i
    refine Fin.addCases ?_ ?_ i <;> intro k
    · simp only [Fin.append_left]
      fun_prop
    · simp only [Fin.append_right]
      fun_prop


def productProjection {m D : ℕ} (L : Submodule ℤ (Fin m → ℝ))
    [DiscreteTopology L] [IsZLattice ℝ L] (N : Submodule ℤ (Fin D → ℝ))
    [DiscreteTopology N] [IsZLattice ℝ N] : (Fin (m+D) → ℝ) →ₜ+ Torus (m+D) where
  toFun x := Fin.append (latticeProjection L (fun j => x (Fin.castAdd D j)))
    (latticeProjection N (fun j => x (Fin.natAdd m j)))
  map_zero' := by
    change Fin.append (latticeProjection L 0) (latticeProjection N 0) = 0
    rw [map_zero,map_zero]
    ext i; refine Fin.addCases ?_ ?_ i <;> intro k <;> simp
  map_add' x y := by
    ext i; refine Fin.addCases ?_ ?_ i <;> intro k
    · simp only [Pi.add_apply,Fin.append_left]
      change latticeProjection L ((fun j => x (Fin.castAdd D j))+
        (fun j => y (Fin.castAdd D j))) k = _
      simp
    · simp only [Pi.add_apply,Fin.append_right]
      change latticeProjection N ((fun j => x (Fin.natAdd m j))+
        (fun j => y (Fin.natAdd m j))) k = _
      simp
  continuous_toFun := by
    apply continuous_pi
    intro i
    refine Fin.addCases ?_ ?_ i <;> intro k
    · simp only [Fin.append_left]
      exact (continuous_apply k).comp ((latticeProjection L).continuous.comp
        (continuous_pi (fun j => continuous_apply _)))
    · simp only [Fin.append_right]
      exact (continuous_apply k).comp ((latticeProjection N).continuous.comp
        (continuous_pi (fun j => continuous_apply _)))

@[simp] lemma productProjection_apply {m D : ℕ}
    (L : Submodule ℤ (Fin m → ℝ)) [DiscreteTopology L] [IsZLattice ℝ L]
    (N : Submodule ℤ (Fin D → ℝ)) [DiscreteTopology N] [IsZLattice ℝ N]
    (x : Fin (m+D) → ℝ) : productProjection L N x =
      Fin.append (latticeProjection L (fun j => x (Fin.castAdd D j)))
        (latticeProjection N (fun j => x (Fin.natAdd m j))) := rfl

@[simp] lemma productProjection_append {m D : ℕ}
    (L : Submodule ℤ (Fin m → ℝ)) [DiscreteTopology L] [IsZLattice ℝ L]
    (N : Submodule ℤ (Fin D → ℝ)) [DiscreteTopology N] [IsZLattice ℝ N]
    (x : Fin m → ℝ) (z : Fin D → ℝ) :
    productProjection L N (Fin.append x z) =
      Fin.append (latticeProjection L x) (latticeProjection N z) := by
  simp only [productProjection_apply,Fin.append_left,Fin.append_right]


def joinedProjection {m D : ℕ}
    (L : Submodule ℤ (Fin m → ℝ)) [DiscreteTopology L] [IsZLattice ℝ L]
    (N : Submodule ℤ (Fin D → ℝ)) [DiscreteTopology N] [IsZLattice ℝ N]
    (M : (Fin D → ℝ) ≃ₗ[ℝ] (Fin D → ℝ)) (Z : Fin D → (Fin m → ℝ)) :
    (Fin (m+D) → ℝ) →ₜ+ Torus (m+D) :=
  (productProjection L N).comp
    ((triangular (LinearEquiv.refl ℝ _) M (columnMap Z)).symm.toContinuousLinearEquiv :
      (Fin (m+D) → ℝ) →ₜ+ (Fin (m+D) → ℝ))

@[simp] lemma joinedProjection_append {m D : ℕ}
    (L : Submodule ℤ (Fin m → ℝ)) [DiscreteTopology L] [IsZLattice ℝ L]
    (N : Submodule ℤ (Fin D → ℝ)) [DiscreteTopology N] [IsZLattice ℝ N]
    (M : (Fin D → ℝ) ≃ₗ[ℝ] (Fin D → ℝ)) (Z : Fin D → (Fin m → ℝ))
    (x : Fin m → ℝ) (z : Fin D → ℝ) :
    joinedProjection L N M Z (Fin.append x (M z)) =
      Fin.append (latticeProjection L (x-columnMap Z z)) (latticeProjection N z) := by
  change productProjection L N
    ((triangular (LinearEquiv.refl ℝ _) M (columnMap Z)).symm (Fin.append x (M z))) = _
  simp only [triangular,LinearEquiv.coe_symm_mk,Fin.append_left,Fin.append_right,
    LinearEquiv.symm_apply_apply,LinearEquiv.refl_symm,LinearEquiv.refl_apply]
  exact productProjection_append L N _ _


end SingleLatticeCovering.CoverGeometry


end
end
end

end OAI
end

section
-- module Solutions.OAIB3_Slc.LatticeCovering_Covering
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section

namespace SingleLatticeCovering.Vertical
open ConstructionA LatticeGeometry

namespace Chain
variable {B : Block}

noncomputable def alphabetSeq (c : Chain B) (j : ℕ) : Finset ℝ :=
  if h : j<c.fullDim then c.alphabets ⟨j,h⟩ else ∅

@[simp] lemma alphabetSeq_fin (c : Chain B) (j : Fin c.fullDim) :
    c.alphabetSeq j.val=c.alphabets j := by
  simp [alphabetSeq,j.isLt]
end Chain
end SingleLatticeCovering.Vertical

end
end

section


noncomputable section
open Set Metric MeasureTheory MeasureTheory.Measure Module
open scoped ENNReal NNReal BigOperators




noncomputable section
open Set Metric MeasureTheory MeasureTheory.Measure Module
open scoped Pointwise ENNReal NNReal BigOperators
namespace SingleLatticeCovering.Sections

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def fiber (K : Set (E × F)) (y : F) : Set E := {x | (x,y) ∈ K}




end SingleLatticeCovering.Sections





end
end
end
end

end OAI
end

section
-- module Solutions.OAIB3_Slc.LatticeCovering_Sections
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Metric MeasureTheory MeasureTheory.Measure Module
open scoped ENNReal NNReal BigOperators
noncomputable section
open Set Metric MeasureTheory MeasureTheory.Measure Module
open scoped Pointwise ENNReal NNReal BigOperators
noncomputable section

noncomputable section
namespace SingleLatticeCovering.Sections
open Set Metric MeasureTheory MeasureTheory.Measure Module
open scoped Pointwise ENNReal NNReal BigOperators

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]



def gaussian (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (y : F) : ℝ := (Real.sqrt (2*Real.pi))^(-(finrank ℝ F : ℤ))*Real.exp (-‖y‖^2/2)


end SingleLatticeCovering.Sections

noncomputable section
namespace SingleLatticeCovering.Sections
open Set MeasureTheory MeasureTheory.Measure Module
open scoped Pointwise ENNReal BigOperators

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]



def sectionShear (T : F →ᵃ[ℝ] E) : (E × F) ≃ᵃ[ℝ] (E × F) :=
  AffineEquiv.ofBijective (φ := ((AffineMap.fst : (E × F) →ᵃ[ℝ] E)-T.comp AffineMap.snd).prod
    AffineMap.snd) (by
      constructor
      · rintro ⟨x,y⟩ ⟨x',y'⟩ h
        have hy : y=y' := congrArg Prod.snd h
        subst y'
        have hx : x-T y=x'-T y := congrArg Prod.fst h
        exact Prod.ext (by simpa using congrArg (fun z => z+T y) hx) rfl
      · rintro ⟨x,y⟩
        refine ⟨(x+T y,y),?_⟩
        change (x+T y-T y,y)=(x,y)
        simp)

@[simp] lemma sectionShear_apply (T : F →ᵃ[ℝ] E) (x : E) (y : F) :
    sectionShear T (x,y)=(x-T y,y) := rfl


end SingleLatticeCovering.Sections

end
end
end
end
end
end

section

noncomputable section
namespace SingleLatticeCovering.Sections
open MeasureTheory LatticeGeometry
open scoped BigOperators

def flatten (m D : ℕ) : ((Fin m → ℝ) × EuclideanSpace ℝ (Fin D)) ≃ₗ[ℝ] (Fin (m+D) → ℝ) :=
  ((LinearEquiv.refl ℝ (Fin m → ℝ)).prodCongr (WithLp.linearEquiv 2 ℝ (Fin D → ℝ))).trans
    (appendEquiv m D)

@[simp] lemma flatten_apply (m D : ℕ) (x : Fin m → ℝ) (y : EuclideanSpace ℝ (Fin D)) :
    flatten m D (x,y)=Fin.append x (WithLp.ofLp y) := rfl

end SingleLatticeCovering.Sections

end
end

section

noncomputable section
namespace SingleLatticeCovering.Sections
open MeasureTheory Set
open scoped BigOperators



def coordinateFiber {m D : ℕ} (K : Set (Fin (m+D) → ℝ)) (y : Fin D → ℝ) :
    Set (Fin m → ℝ) := {x | Fin.append x y ∈ K}


end SingleLatticeCovering.Sections

end
end

end

end OAI
end

section
-- module Solutions.OAIB3_Slc.LatticeCovering_Rates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Real Filter Topology Asymptotics

namespace SingleLatticeCovering.FinalRates

def firstSize (n : ℕ) : ℕ := ⌈(Real.log (Real.log (n : ℝ)))^2⌉₊



end SingleLatticeCovering.FinalRates
noncomputable section

namespace SingleLatticeCovering.FinalRates
open Real Filter Topology Asymptotics

def eta (m : ℕ) : ℝ := (m : ℝ)/4*Real.log (27/16 : ℝ)-3*Real.log (m : ℝ)




end SingleLatticeCovering.FinalRates

end
end
end

section

noncomputable section
namespace SingleLatticeCovering.Shear
open Real Filter Topology
open scoped BigOperators



def pointBudget {α : Type*} (A : ℕ → Finset ℝ) (s : Finset α) (D : ℕ) : ℕ :=
  (s.card+1)*∏ j ∈ Finset.range D, ((A j).card+1)

def patternTotal {α : Type*} (A : ℕ → Finset ℝ) (s : Finset α) (D : ℕ) : ℕ :=
  ∑ q ∈ Finset.range (D+1), (allPatterns A s q).card


end SingleLatticeCovering.Shear

end
end

end

end OAI
end

section
-- module Solutions.OAIB3_Slc.LatticeCovering_Horizontal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section

namespace SingleLatticeCovering.Horizontal
open MeasureTheory Completion
open scoped ENNReal BigOperators



structure FullLattice (m : ℕ) where
  module : Submodule ℤ (Fin m → ℝ)
  discrete : DiscreteTopology module
  full : IsZLattice ℝ module

attribute [instance] FullLattice.discrete FullLattice.full

namespace FullLattice

def hole {m : ℕ} (L : FullLattice m) (J : Set (Fin m → ℝ)) : ℝ≥0∞ :=
  torusMeasure m ((latticeProjection L.module '' J)ᶜ)

end FullLattice




end SingleLatticeCovering.Horizontal

end
end

section

noncomputable section
namespace SingleLatticeCovering.FinalRates
open Real Filter Topology


def sectionRadius (C : ℝ) (n : ℕ) : ℝ := (C+1)*((firstSize n : ℝ)+1)


end SingleLatticeCovering.FinalRates

end
end

section

noncomputable section
namespace SingleLatticeCovering.Assembly
open MeasureTheory Folded LatticeGeometry Completion Shear CoverGeometry Vertical Sections Horizontal
open Filter Topology
open scoped BigOperators Pointwise ENNReal


def coversAtBound (n : ℕ) (d : ℝ) : Prop :=
  ∀ K : Set (Fin n → ℝ), IsCompact K → Convex ℝ K → (interior K).Nonempty →
    ∃ (Λ : Submodule ℤ (Fin n → ℝ)) (_ : DiscreteTopology Λ), IsZLattice ℝ Λ ∧
      K+(Λ : Set (Fin n → ℝ))=Set.univ ∧
      (volume K).toReal/ZLattice.covolume Λ volume ≤ d






end SingleLatticeCovering.Assembly

end
end

end

end OAI
end

section
-- module Solutions.OAIB3_Slc.LatticeCovering_Isotropy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section



noncomputable section
namespace SingleLatticeCovering.Isotropization
open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace

abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

def uniformLaw {n : ℕ} (K : Set (E n)) : Measure (E n) :=
  (volume K)⁻¹ • volume.restrict K




def adjointEquiv {n : ℕ} (T : E n ≃L[ℝ] E n) : E n ≃L[ℝ] E n where
  toLinearEquiv :=
    { toLinearMap := T.toContinuousLinearMap.adjoint.toLinearMap
      invFun := T.symm.toContinuousLinearMap.adjoint
      left_inv x := by
        change (T.symm.toContinuousLinearMap.adjoint.comp T.toContinuousLinearMap.adjoint) x=x
        rw [←ContinuousLinearMap.adjoint_comp]
        have h : T.toContinuousLinearMap.comp T.symm.toContinuousLinearMap=
            ContinuousLinearMap.id ℝ (E n) := by ext x; simp
        rw [h,ContinuousLinearMap.adjoint_id]
        rfl
      right_inv x := by
        change (T.toContinuousLinearMap.adjoint.comp T.symm.toContinuousLinearMap.adjoint) x=x
        rw [←ContinuousLinearMap.adjoint_comp]
        have h : T.symm.toContinuousLinearMap.comp T.toContinuousLinearMap=
            ContinuousLinearMap.id ℝ (E n) := by ext x; simp
        rw [h,ContinuousLinearMap.adjoint_id]
        rfl }
  continuous_toFun := T.toContinuousLinearMap.adjoint.continuous
  continuous_invFun := T.symm.toContinuousLinearMap.adjoint.continuous

end SingleLatticeCovering.Isotropization

end
end

section
noncomputable section
namespace SingleLatticeCovering.Isotropization
open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace




def centeredEquiv {n : ℕ} (μ : Measure (E n)) (A : E n ≃L[ℝ] E n) : E n ≃ᵃ[ℝ] E n :=
  (AffineEquiv.constVAdd ℝ (E n) (-(∫ x, x ∂μ))).trans A.toLinearEquiv.toAffineEquiv



end SingleLatticeCovering.Isotropization

end
end

section
noncomputable section
namespace SingleLatticeCovering.Isotropization
open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace




def affineMeasurableEquiv {n : ℕ} (e : E n ≃ᵃ[ℝ] E n) : E n ≃ᵐ E n where
  toEquiv := e.toEquiv
  measurable_toFun := e.toAffineMap.continuous_of_finiteDimensional.measurable
  measurable_invFun := e.symm.toAffineMap.continuous_of_finiteDimensional.measurable






def LogConcave {n : ℕ} (f : E n → ℝ) : Prop :=
  (∀ x, 0 ≤ f x) ∧ ∀ (x y : E n) (a b : ℝ), 0 < a → 0 < b → a+b=1 →
    f x ^ a * f y ^ b ≤ f (a • x+b • y)

def uniformPdf {n : ℕ} (K : Set (E n)) : E n → ℝ :=
  K.indicator (fun _ => ((volume K)⁻¹).toReal)



def IsIsotropic {n : ℕ} (μ : Measure (E n)) : Prop :=
  (∫ x, x ∂μ)=0 ∧ ∀ u v : E n, (∫ x, ⟪u,x⟫*⟪v,x⟫ ∂μ)=⟪u,v⟫




end SingleLatticeCovering.Isotropization

end
end

end

end OAI
end

section
-- module Solutions.OAIB3_Slc.LatticeCovering_GaussianSections
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
namespace SingleLatticeCovering.Horizontal
open Completion MeasureTheory Set Topology
open scoped ENNReal Pointwise

namespace FullLattice

def image {m : ℕ} (L : FullLattice m) (e : (Fin m → ℝ) ≃ₗ[ℝ] (Fin m → ℝ)) : FullLattice m :=
  ⟨LatticeGeometry.image L.module e,inferInstance,inferInstance⟩

end FullLattice

end SingleLatticeCovering.Horizontal

end
end

section

noncomputable section
namespace SingleLatticeCovering.Inputs
open Completion Horizontal MeasureTheory Set Topology
open scoped ENNReal Pointwise




def determinantScale (m : ℕ) (Dh : ℝ) (hDh : 0 < Dh) :
    (Fin m → ℝ) ≃ₗ[ℝ] (Fin m → ℝ) :=
  LinearEquiv.smulOfNeZero ℝ (Fin m → ℝ) (Dh^((m : ℝ)⁻¹))
    (ne_of_gt (Real.rpow_pos_of_pos hDh _))


end SingleLatticeCovering.Inputs

end
end









noncomputable section
namespace SingleLatticeCovering.FiniteKernel
open Module Submodule MeasureTheory
open scoped BigOperators Pointwise

variable {ι : Type*} [Fintype ι]

abbrev integerLattice (ι : Type*) [Fintype ι] : Submodule ℤ (ι → ℝ) :=
  Submodule.span ℤ (Set.range (Pi.basisFun ℝ ι))

def integerCoordinates : integerLattice ι ≃ₗ[ℤ] (ι → ℤ) :=
  ((Pi.basisFun ℝ ι).restrictScalars ℤ).equivFun

variable {U : Type*} [AddCommGroup U]

def kernelLattice (A : integerLattice ι →ₗ[ℤ] U) : Submodule ℤ (ι → ℝ) :=
  (LinearMap.ker A).map (integerLattice ι).subtype

lemma kernelLattice_le (A : integerLattice ι →ₗ[ℤ] U) :
    kernelLattice A ≤ integerLattice ι := by
  rintro x ⟨y,hy,rfl⟩
  exact y.property

instance kernelLattice_discrete (A : integerLattice ι →ₗ[ℤ] U) :
    DiscreteTopology (kernelLattice A) :=
  DiscreteTopology.of_subset (inferInstance : DiscreteTopology (integerLattice ι))
    (kernelLattice_le A)




def gridRelationForm {r d : ℕ} (q : ℕ) (a : Fin r → ℤ) :
    integerLattice (Fin r × Fin d) →ₗ[ℤ] (Fin d → ZMod q) where
  toFun x j := ∑ i, (a i : ZMod q) * (integerCoordinates x (i,j) : ZMod q)
  map_add' x y := by ext j; simp [mul_add, Finset.sum_add_distrib]
  map_smul' c x := by
    ext j
    simp only [map_smul, Pi.smul_apply, zsmul_eq_mul, Int.cast_mul, RingHom.id_apply,
      Finset.mul_sum, Int.cast_id]
    apply Finset.sum_congr rfl
    intro i _
    ring



end SingleLatticeCovering.FiniteKernel


end
end

end OAI
end

section
-- module Solutions.OAIB3_Slc.LatticeCovering_GridCounts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section


noncomputable section
namespace SingleLatticeCovering.GridGeometry
open MeasureTheory Measure Set Bornology
open scoped BigOperators Pointwise



def weightedGridConfiguration {r d : ℕ} (J : Set (Fin d → ℝ)) (c : Fin r → ℝ) :
    Set (Fin r × Fin d → ℝ) :=
  {x | (∀ i, (fun j => x (i,j)) ∈ J) ∧ (fun j => ∑ i, c i*x (i,j)) ∈ J}



end SingleLatticeCovering.GridGeometry

namespace SingleLatticeCovering.GridLimit
open MeasureTheory Measure Filter Set
open FiniteKernel GridGeometry
open scoped Topology Pointwise BigOperators

lemma finite_scaled_lattice_inter {ι : Type*} [Fintype ι]
    (L : Submodule ℤ (ι → ℝ)) [DiscreteTopology L]
    {S : Set (ι → ℝ)} (hS : IsCompact S) {t : ℝ} (ht : t ≠ 0) :
    (S ∩ t⁻¹ • (L : Set (ι → ℝ))).Finite := by
  have hT : ((t • S) ∩ (L : Set (ι → ℝ))).Finite := by
    apply Metric.finite_isBounded_inter_isClosed DiscreteTopology.isDiscrete
      (hS.smul t).isBounded
    exact AddSubgroup.isClosed_of_discrete (H := L.toAddSubgroup)
  apply Set.Finite.of_injOn (t := (t • S) ∩ (L : Set (ι → ℝ)))
    (f := fun x => t • x) ?_ ?_ hT
  · rintro x ⟨hx, y, hy, rfl⟩
    constructor
    · exact ⟨t⁻¹ • y,hx,rfl⟩
    · simpa only [smul_smul, mul_inv_cancel₀ ht, one_smul] using hy
  · intro x hx y hy hxy
    exact smul_right_injective (ι → ℝ) ht hxy


end SingleLatticeCovering.GridLimit







noncomputable section
namespace SingleLatticeCovering.SimplexYoung
open MeasureTheory Measure Set Matrix Filter Topology
open scoped ENNReal BigOperators

abbrev V (r : ℕ) := Fin r → ℝ

def simplexMean {r : ℕ} (u : V (r+1)) : ℝ := (∑ i, u i) / (r+1:ℕ)

def simplexForm {r : ℕ} (i : Fin (r+1)) : V r →ₗ[ℝ] ℝ :=
  Fin.cases (-(∑ j : Fin r, (LinearMap.proj j : V r →ₗ[ℝ] ℝ)))
    (fun j => LinearMap.proj j) i

def simplexDual {r : ℕ} : V (r+1) →ₗ[ℝ] V r where
  toFun u j := u j.succ - simplexMean u
  map_add' u v := by
    ext j
    simp [simplexMean, Finset.sum_add_distrib, add_div]; ring
  map_smul' c u := by
    ext j
    simp only [simplexMean, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [←Finset.mul_sum]
    ring

def simplexJacobian {r : ℕ} (s : V (r+1)) : Matrix (Fin r) (Fin r) ℝ :=
  Matrix.diagonal (fun j : Fin r => s j.succ) +
    Matrix.replicateCol Unit (fun _ : Fin r => (1:ℝ)) *
      Matrix.replicateRow Unit (fun j : Fin r => (s 0-s j.succ)/(r+1:ℕ))


def simplexTransport {r : ℕ} (T : Fin (r+1) → ℝ → ℝ) (x : V r) : V r :=
  simplexDual (fun i => T i (simplexForm i x))

def simplexDerivative {r : ℕ} (s : V (r+1)) : V r →L[ℝ] V r :=
  simplexDual.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i => s i • (simplexForm i).toContinuousLinearMap))


def simplexRoot {r : ℕ} : Matrix (Fin r) (Fin r) ℝ :=
  1 + Matrix.replicateCol Unit (fun _ : Fin r => (1:ℝ)) *
    Matrix.replicateRow Unit (fun _ : Fin r => (1:ℝ)/(Real.sqrt (r+1:ℕ)+1))



end SingleLatticeCovering.SimplexYoung





open MeasureTheory Filter Set
open scoped Topology
end
end
end
end

end OAI
end

section
-- module Solutions.OAIB3_Slc.LatticeCovering_Transport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
noncomputable section
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
noncomputable section

namespace SingleLatticeCovering.SharpYoung

structure PositiveDensity where
  toFun : ℝ → ℝ
  continuous : Continuous toFun
  positive : ∀ x, 0 < toFun x
  integrable : Integrable toFun volume
  integral_one : ∫ x, toFun x = 1

instance instCoeFunPositiveDensityForallReal : CoeFun PositiveDensity (fun _ => ℝ → ℝ) := ⟨PositiveDensity.toFun⟩

def densityCDF (f : PositiveDensity) (x : ℝ) : ℝ := ∫ t in Iic x, f t

lemma densityCDF_hasDerivAt (f : PositiveDensity) (x : ℝ) :
    HasDerivAt (densityCDF f) (f x) x := by
  have h := (intervalIntegral.integral_hasDerivAt_right
    (f.integrable.intervalIntegrable (a := 0) (b := x))
    (f.continuous.stronglyMeasurableAtFilter volume (𝓝 x)) f.continuous.continuousAt).const_add
      (densityCDF f 0)
  convert! h using 1
  funext u
  have hdiff := intervalIntegral.integral_Iic_sub_Iic
    (f.integrable.integrableOn (s := Iic 0)) (f.integrable.integrableOn (s := Iic u))
  dsimp [densityCDF] at *
  linarith

lemma densityCDF_continuous (f : PositiveDensity) : Continuous (densityCDF f) :=
  continuous_iff_continuousAt.mpr (fun x => (densityCDF_hasDerivAt f x).continuousAt)

lemma densityCDF_strictMono (f : PositiveDensity) : StrictMono (densityCDF f) := by
  apply strictMono_of_deriv_pos
  intro x
  rw [(densityCDF_hasDerivAt f x).deriv]
  exact f.positive x

lemma densityCDF_add_tail (f : PositiveDensity) (x : ℝ) :
    densityCDF f x + (∫ t in Ioi x, f t) = 1 := by
  simpa [densityCDF, f.integral_one] using integral_add_compl measurableSet_Iic f.integrable

lemma densityCDF_mem_Ioo (f : PositiveDensity) (x : ℝ) : densityCDF f x ∈ Ioo 0 1 := by
  have hnonneg (y : ℝ) : 0 ≤ densityCDF f y := integral_nonneg (fun t => (f.positive t).le)
  have hle (y : ℝ) : densityCDF f y ≤ 1 := by
    have ht : 0 ≤ ∫ t in Ioi y, f t := integral_nonneg (fun t => (f.positive t).le)
    linarith [densityCDF_add_tail f y]
  constructor
  · exact lt_of_le_of_lt (hnonneg (x-1)) (densityCDF_strictMono f (by linarith))
  · exact lt_of_lt_of_le (densityCDF_strictMono f (show x < x+1 by linarith)) (hle (x+1))

lemma densityCDF_tendsto_bot (f : PositiveDensity) :
    Tendsto (densityCDF f) atBot (𝓝 0) := tendsto_integral_Iic_zero tendsto_id

lemma densityCDF_tendsto_top (f : PositiveDensity) :
    Tendsto (densityCDF f) atTop (𝓝 1) := by
  have h : Tendsto (fun x : ℝ => 1 - ∫ t in Ioi x, f t) atTop (𝓝 (1-0)) :=
    tendsto_const_nhds.sub (tendsto_integral_Ioi_zero tendsto_id)
  convert h using 1
  · funext x
    linarith [densityCDF_add_tail f x]
  · norm_num

lemma densityCDF_surjOn (f : PositiveDensity) :
    SurjOn (densityCDF f) univ (Ioo 0 1) := by
  exact isPreconnected_univ.intermediate_value_Ioo (by simp) (by simp)
    (densityCDF_continuous f).continuousOn (densityCDF_tendsto_bot f) (densityCDF_tendsto_top f)

def densityCDFIso (f : PositiveDensity) : ℝ ≃o Ioo (0 : ℝ) 1 :=
  StrictMono.orderIsoOfSurjective (fun x => ⟨densityCDF f x, densityCDF_mem_Ioo f x⟩)
    (fun _ _ h => densityCDF_strictMono f h)
    (fun y => by
      obtain ⟨x, _, hx⟩ := densityCDF_surjOn f y.property
      exact ⟨x, Subtype.ext hx⟩)

@[simp] lemma densityCDFIso_apply (f : PositiveDensity) (x : ℝ) :
    (densityCDFIso f x : ℝ) = densityCDF f x := rfl


def densityTransport (f g : PositiveDensity) : ℝ ≃o ℝ :=
  (densityCDFIso f).trans (densityCDFIso g).symm


def normalizedGaussianDensity : PositiveDensity where
  toFun := fun x => Real.exp (-x^2) / Real.sqrt Real.pi
  continuous := by fun_prop
  positive := fun x => div_pos (Real.exp_pos _) (Real.sqrt_pos.mpr Real.pi_pos)
  integrable := by
    have h := integrable_exp_neg_mul_sq (show (0:ℝ) < 1 by norm_num)
    simpa using h.div_const (Real.sqrt Real.pi)
  integral_one := by
    simp_rw [div_eq_mul_inv]
    rw [integral_mul_const]
    have h := integral_gaussian (1 : ℝ)
    simp only [neg_mul, one_mul, div_one] at h
    rw [h, mul_inv_cancel₀ (ne_of_gt (Real.sqrt_pos.mpr Real.pi_pos))]



end SingleLatticeCovering.SharpYoung

namespace SingleLatticeCovering.SimplexYoung
open SingleLatticeCovering.SharpYoung
open MeasureTheory Filter Set
open scoped Topology ENNReal


def simplexConstant (r : ℕ) : ℝ :=
  (Real.sqrt ((r:ℝ)/(r+1:ℕ)))⁻¹^r / Real.sqrt (r+1:ℕ)

lemma integral_pos_of_continuous_density {f : ℝ → ℝ}
    (hp : ∀ x, 0 < f x) (hi : Integrable f volume) : 0 < ∫ x, f x := by
  apply (integral_pos_iff_support_of_nonneg (fun x => (hp x).le) hi).mpr
  have he : Function.support f = univ := by
    ext x
    simp [Function.mem_support, ne_of_gt (hp x)]
  rw [he]
  simp

def normalizePositiveDensity (f : ℝ → ℝ) (hc : Continuous f) (hp : ∀ x, 0 < f x)
    (hi : Integrable f volume) : PositiveDensity where
  toFun := fun x => f x / ∫ t, f t
  continuous := hc.div_const _
  positive := fun x => div_pos (hp x) (integral_pos_of_continuous_density hp hi)
  integrable := hi.div_const _
  integral_one := by
    rw [integral_div, div_self (ne_of_gt (integral_pos_of_continuous_density hp hi))]



end SingleLatticeCovering.SimplexYoung


open MeasureTheory Filter Set
open scoped Topology ENNReal
noncomputable section
namespace SingleLatticeCovering.SharpYoung

def finMarginal {d : ℕ} (f : (Fin (d+1) → ℝ) → ℝ) (y : Fin d → ℝ) : ℝ :=
  ∫ t : ℝ, f (Fin.cons t y)



end SingleLatticeCovering.SharpYoung

namespace SingleLatticeCovering.SimplexYoung
open SingleLatticeCovering.SharpYoung
open MeasureTheory Filter Set
open scoped Topology ENNReal
def simplexSpatial {r d : ℕ} (i : Fin (r+1)) (x : Fin d → V r) : Fin d → ℝ :=
  fun j => simplexForm i (x j)



end SingleLatticeCovering.SimplexYoung

namespace SingleLatticeCovering.SimplexYoung
open MeasureTheory Filter Set
open scoped Topology ENNReal


def simplexConfiguration {r d : ℕ} (J : Fin (r+1) → Set (Fin d → ℝ)) :
    Set (Fin d → V r) := {x | ∀ i, simplexSpatial i x ∈ J i}


end SingleLatticeCovering.SimplexYoung

namespace SingleLatticeCovering.SimplexYoung
open MeasureTheory Measure Set Matrix
open scoped ENNReal Pointwise


def weightedSimplexConfiguration {r d : ℕ} (J : Set (Fin d → ℝ))
    (c : Fin r → ℝ) : Set (Fin d → V r) :=
  {x | (∀ j, (fun a => x a j) ∈ J) ∧ (fun a => ∑ j, c j * x a j) ∈ J}

def simplexDiagonal {r d : ℕ} (c : Fin r → ℝ) :
    (Fin d → V r) →ₗ[ℝ] (Fin d → V r) :=
  LinearMap.pi (fun a : Fin d => (Matrix.diagonal c).mulVecLin.comp (LinearMap.proj a))

def scaledCircuitFamily {r d : ℕ} (J : Set (Fin d → ℝ)) (c : Fin r → ℝ) :
    Fin (r+1) → Set (Fin d → ℝ) := Fin.cons ((-1:ℝ) • J) (fun j => c j • J)


end SingleLatticeCovering.SimplexYoung



end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIB3_Slc.LatticeCovering_CircuitVolumes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
noncomputable section
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal
noncomputable section
noncomputable section

namespace SingleLatticeCovering.SimplexYoung
open MeasureTheory
open scoped ENNReal BigOperators



def rationalCircuitVolume {r d : ℕ} (J : Set (Fin d → ℝ))
    (a : Fin (r+1) → ℤ) : ℝ≥0∞ :=
  if ∀ j, a j ≠ 0 then ENNReal.ofReal (|(a 0:ℝ)|⁻¹^d) *
    volume (weightedSimplexConfiguration J (fun j => -(a j.succ:ℝ)/(a 0:ℝ))) else 0



def rationalCircuitVolumeSum {r d : ℕ} (J : Set (Fin d → ℝ)) : ℝ≥0∞ :=
  ∑' a : Fin (r+1) → ℤ, rationalCircuitVolume J a




end SingleLatticeCovering.SimplexYoung

namespace SingleLatticeCovering.SimplexYoung
open MeasureTheory
open scoped ENNReal BigOperators



def affineCircuitVolumeSum {r d : ℕ} (J : Set (Fin d → ℝ)) : ℝ≥0∞ :=
  ∑' a : Fin (r+1) → ℤ, if ∑ j, a j = 0 then rationalCircuitVolume J a else 0




end SingleLatticeCovering.SimplexYoung




noncomputable section
namespace SingleLatticeCovering.GridCoordinates
open MeasureTheory Measure Set TopologicalSpace.PositiveCompacts
open scoped BigOperators


def flatten {r d : ℕ} : (Fin d → Fin r → ℝ) ≃ₗ[ℝ] (Fin r × Fin d → ℝ) where
  toFun x ij := x ij.2 ij.1
  invFun x j i := x (i,j)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl


end SingleLatticeCovering.GridCoordinates

namespace SingleLatticeCovering.CircuitVolume
open MeasureTheory Measure Set Filter
open GridCoordinates GridGeometry SimplexYoung
open scoped Topology Pointwise BigOperators


def PrimitiveAffineCoefficients (r : ℕ) :=
  {a : Fin (r+1) → ℤ // (∀ i, a i ≠ 0) ∧ Finset.univ.gcd a = 1 ∧ ∑ i, a i = 0}



end SingleLatticeCovering.CircuitVolume





end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIB3_Slc.LatticeCovering_CircuitLattices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
noncomputable section
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section

namespace SingleLatticeCovering.CircuitArithmetic
open Module Submodule MeasureTheory
open scoped BigOperators Pointwise

abbrev integerLattice (r : ℕ) : Submodule ℤ (Fin r → ℝ) :=
  Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin r)))

def integerCoordinates (r : ℕ) : integerLattice r ≃ₗ[ℤ] (Fin r → ℤ) :=
  ((Pi.basisFun ℝ (Fin r)).restrictScalars ℤ).equivFun


def congruenceKernel {r q : ℕ} (A : integerLattice r →ₗ[ℤ] ZMod q) :
    Submodule ℤ (Fin r → ℝ) := (LinearMap.ker A).map (integerLattice r).subtype

lemma congruenceKernel_le {r q : ℕ} (A : integerLattice r →ₗ[ℤ] ZMod q) :
    congruenceKernel A ≤ integerLattice r := by
  rintro x ⟨y,hy,rfl⟩
  exact y.property

instance congruenceKernel_discrete {r q : ℕ} (A : integerLattice r →ₗ[ℤ] ZMod q) :
    DiscreteTopology (congruenceKernel A) :=
  DiscreteTopology.of_subset (inferInstance : DiscreteTopology (integerLattice r))
    (congruenceKernel_le A)


def relationForm {r : ℕ} (q : ℕ) (a : Fin r → ℤ) :
    integerLattice r →ₗ[ℤ] ZMod q where
  toFun x := ∑ i, (a i : ZMod q) * (integerCoordinates r x i : ZMod q)
  map_add' x y := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [map_smul, Pi.smul_apply, zsmul_eq_mul, Int.cast_mul, RingHom.id_apply,
      Finset.mul_sum, Int.cast_id]
    apply Finset.sum_congr rfl
    intro i _
    ring

end SingleLatticeCovering.CircuitArithmetic

namespace SingleLatticeCovering.CircuitGrid
open Module Submodule MeasureTheory CircuitArithmetic
open scoped BigOperators



def affineRows {r d : ℕ} (x : Fin r → Fin d → ℤ) : Matrix (Fin r) (Fin (d+1)) ℝ :=
  fun i => Fin.cons 1 (fun j => (x i j : ℝ))





end SingleLatticeCovering.CircuitGrid

end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIB3_Slc.LatticeCovering_CircuitSums
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
noncomputable section
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section




noncomputable section

noncomputable section


noncomputable section

namespace SingleLatticeCovering.AffineCircuit
open Matrix CircuitVolume CircuitGrid
open scoped BigOperators


def integerRows {s d : ℕ} (x : Fin s → Fin d → ℤ) : Matrix (Fin s) (Fin (d+1)) ℤ :=
  fun i => Fin.cons 1 (x i)


def IsCircuit {r d : ℕ} (x : Fin (r+1) → Fin d → ℤ) : Prop :=
  ¬LinearIndependent ℚ ((integerRows x).map (fun z => (z:ℚ))).row ∧
    ∀ e : Equiv.Perm (Fin (r+1)),
      LinearIndependent ℚ ((integerRows (fun i => x (e i.succ))).map (fun z => (z:ℚ))).row


def circuits {d : ℕ} (S : Finset (Fin d → ℤ)) (r : ℕ) : Finset (Fin (r+1) → Fin d → ℤ) := by
  classical
  exact (Fintype.piFinset (fun _ : Fin (r+1) => S)).filter IsCircuit

def coefficientCircuits {r d : ℕ} (S : Finset (Fin d → ℤ)) (a : PrimitiveAffineCoefficients r) :
    Finset (Fin (r+1) → Fin d → ℤ) := by
  classical
  exact (circuits S r).filter (fun x => ∀ j, ∑ i, a.val i*x i j = 0)



end SingleLatticeCovering.AffineCircuit



noncomputable section
namespace SingleLatticeCovering.CircuitEnumeration
open scoped BigOperators

variable {ι : Type*} [DecidableEq ι]



def Enumerations (B : Finset (Finset ι)) (r : ℕ) :=
  (T : B) × (Fin r ≃ T.val)

instance instFintypeEnumerations (B : Finset (Finset ι)) (r : ℕ) : Fintype (Enumerations B r) := by
  unfold Enumerations
  infer_instance

def orderedCircuit {r : ℕ} {B : Finset (Finset ι)} (e : B → ι)
    (x : Enumerations B r) : Fin (r+1) → ι :=
  Fin.cons (e x.1) (fun i => (x.2 i).val)



end SingleLatticeCovering.CircuitEnumeration



noncomputable section
namespace SingleLatticeCovering.BrokenCircuit
open scoped BigOperators
open Submodule

variable {ι K V : Type*} [LinearOrder ι] [Field K] [AddCommGroup V] [Module K V]



def Active (v : ι → V) (S : Finset ι) (e : ι) : Prop :=
  v e ∈ Submodule.span K (v '' (↑(S.filter (fun j => e < j)) : Set ι))

def NoBrokenCircuit (v : ι → V) (S : Finset ι) : Prop :=
  ∀ e, ¬Active (K := K) v S e

section Pointwise
variable [Fintype ι]

def zeroFamily (v : ι → V) (L : V →ₗ[K] K) : Finset ι := by
  classical
  exact Finset.univ.filter (fun e => L (v e) = 0)

def nbcFaces (v : ι → V) (Z : Finset ι) : Finset (Finset ι) := by
  classical
  exact Z.powerset.filter (NoBrokenCircuit (K := K) v)

def nbcValue (v : ι → V) (L : V →ₗ[K] K) (k : ℕ) : ℝ :=
  ∑ S ∈ nbcFaces (K := K) v (zeroFamily v L), if S.card ≤ k then (-1:ℝ)^S.card else 0

def avoidanceIndicator (v : ι → V) (L : V →ₗ[K] K) : ℝ := by
  classical
  exact if ∀ e, L (v e) ≠ 0 then 1 else 0




end Pointwise


section FiniteField
attribute [local instance] Classical.propDecidable
variable {τ κ : Type*} [Fintype τ] [Fintype κ]


variable [Fintype K] [Fintype ι]


def vectorAverage (f : (τ → K) → ℝ) : ℝ :=
  (∑ a, f a) / Fintype.card (τ → K)

def nbcPolynomial (v : ι → V) (t : ℝ) (k : ℕ) : ℝ :=
  ∑ S ∈ nbcFaces (K := K) v Finset.univ,
    if S.card ≤ k then (-1:ℝ)^S.card * t^S.card else 0





end FiniteField
end SingleLatticeCovering.BrokenCircuit


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIB3_Slc.LatticeCovering_BrokenCircuits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
noncomputable section
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section

namespace SingleLatticeCovering.BrokenCircuit
open scoped BigOperators
variable {ι : Type*} [DecidableEq ι]

def minimalObstructions (P : Finset ι → Prop) (A : Finset ι) : Finset (Finset ι) := by
  classical
  exact A.powerset.filter (fun T => ¬P T ∧ ∀ U, U ⊂ T → P U)

attribute [local instance] Classical.propDecidable




def truncatedFacesPolynomial (P : Finset ι → Prop) (A : Finset ι) (t : ℝ) (k : ℕ) : ℝ :=
  ∑ S ∈ A.powerset.filter P, if S.card ≤ k then (-1:ℝ)^S.card*t^S.card else 0

def binomialPolynomial (M : ℕ) (t : ℝ) (k : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (k+1), (M.choose j : ℝ) * (-1:ℝ)^j * t^j




end SingleLatticeCovering.BrokenCircuit

namespace SingleLatticeCovering.BrokenCircuit
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
variable {ι τ K : Type*} [LinearOrder ι] [Fintype ι] [Fintype τ] [Field K] [Fintype K]



def finiteCircuitError (v : ι → τ → K) (k : ℕ) : ℝ :=
  (1+(Fintype.card K : ℝ)⁻¹)^(Fintype.card ι) *
    ∑ T ∈ (minimalObstructions (NoBrokenCircuit (K := K) v) Finset.univ).filter
      (fun T => T.card ≤ k), ((Fintype.card K : ℝ)⁻¹)^T.card



end
end SingleLatticeCovering.BrokenCircuit

namespace SingleLatticeCovering.PrimeCircuit
open Matrix AffineCircuit CircuitEnumeration BrokenCircuit
open scoped BigOperators

variable {d r p : ℕ} [Fact p.Prime]

def homogeneousRow (z : Fin d → ℤ) : Fin (d+1) → ZMod p :=
  Fin.cons 1 (fun j => (z j:ZMod p))


end SingleLatticeCovering.PrimeCircuit

namespace SingleLatticeCovering.ConvexGrid
open FiniteKernel MeasureTheory Measure Filter
open scoped Topology Pointwise

def scaledIntegerPoint {d : ℕ} (t : ℝ) (z : Fin d → ℤ) : Fin d → ℝ := fun j => t⁻¹*(z j:ℝ)

def gridSet {d : ℕ} (J : Set (Fin d → ℝ)) (t : ℝ) : Set (Fin d → ℤ) :=
  {z | scaledIntegerPoint t z ∈ J}

lemma scaledPoint_injective {d : ℕ} {t : ℝ} (ht : t ≠ 0) :
    Function.Injective (scaledIntegerPoint (d:=d) t) := by
  intro z w h
  funext j
  apply Int.cast_injective (α:=ℝ)
  exact mul_left_cancel₀ (inv_ne_zero ht) (congrFun h j)

lemma integerPoint_mem_lattice {d : ℕ} (z : Fin d → ℤ) :
    (fun j => (z j:ℝ)) ∈ integerLattice (Fin d) := by
  apply ((Pi.basisFun ℝ (Fin d)).mem_span_iff_repr_mem ℤ _).mpr
  intro j
  exact ⟨z j,by simp⟩

lemma gridSet_finite {d : ℕ} {J : Set (Fin d → ℝ)} (hJ : IsCompact J)
    {t : ℝ} (ht : t ≠ 0) : (gridSet J t).Finite := by
  apply Set.Finite.of_injOn (f:=scaledIntegerPoint t)
    (t:=J ∩ t⁻¹ • (integerLattice (Fin d) : Set (Fin d → ℝ)))
  · intro z hz
    exact ⟨hz,⟨fun j => (z j:ℝ),integerPoint_mem_lattice z,rfl⟩⟩
  · exact (scaledPoint_injective ht).injOn
  · exact GridLimit.finite_scaled_lattice_inter _ hJ ht


def integerGrid {d : ℕ} (J : Set (Fin d → ℝ)) (hJ : IsCompact J) (t : ℝ) : Finset (Fin d → ℤ) := by
  classical
  exact if ht : t ≠ 0 then (gridSet_finite hJ ht).toFinset else ∅



end SingleLatticeCovering.ConvexGrid





end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIB3_Slc.LatticeCovering_PrimeGrids
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
noncomputable section
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section

namespace SingleLatticeCovering.ConvexGrid
open scoped BigOperators

def primeScale (d p : ℕ) : ℝ := (p:ℝ)^((d:ℝ)⁻¹)




end SingleLatticeCovering.ConvexGrid


noncomputable section

namespace SingleLatticeCovering.ConvexGrid
open MeasureTheory Filter Topology AffineCircuit BrokenCircuit PrimeCircuit
open scoped BigOperators


def primeGridVoid {d : ℕ} (J : Set (Fin d → ℝ)) (hJ : IsCompact J)
    (p : ℕ) [Fact p.Prime] : ℝ :=
  vectorAverage (fun a : Fin (d+1) → ZMod p => avoidanceIndicator
    (fun z : integerGrid J hJ (primeScale d p) => homogeneousRow (p:=p) z.val)
    (dotProductBilin (ZMod p) (ZMod p) a))

def continuumCircuitError {d : ℕ} (J : Set (Fin d → ℝ)) (k : ℕ) : ℝ :=
  Real.exp (volume.real J) * ∑ r ∈ Finset.Icc 2 k,
    (SimplexYoung.affineCircuitVolumeSum (r:=r) J).toReal/(r.factorial:ℝ)



end SingleLatticeCovering.ConvexGrid

namespace SingleLatticeCovering.SimplexYoung
open scoped BigOperators



def circuitTerm (d : ℕ) (V : ℝ) (r : ℕ) : ℝ :=
  (4:ℝ)^r * (simplexConstant r)^d * V^r / (r.factorial:ℝ)




end SingleLatticeCovering.SimplexYoung

namespace SingleLatticeCovering.SimplexYoung


def sourceEta (d : ℕ) : ℝ := (d:ℝ)/4 * Real.log (27/16:ℝ) - 3*Real.log (d:ℝ)


end SingleLatticeCovering.SimplexYoung




noncomputable section
namespace SingleLatticeCovering.RogersPreparation
open Finset Set
open scoped BigOperators

def poissonPartial (u : ℝ) (k : ℕ) : ℝ :=
  ∑ j ∈ range (k+1), (-u)^j/(j.factorial : ℝ)


end SingleLatticeCovering.RogersPreparation


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIB3_Slc.LatticeCovering_CircuitErrors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
noncomputable section
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section








section











section

noncomputable section
namespace SingleLatticeCovering.RogersPreparation
open Horizontal Completion MeasureTheory Set Topology
open scoped ENNReal Pointwise BigOperators

instance lattice_vadd_invariant {m : ℕ} (L : FullLattice m) :
    VAddInvariantMeasure L.module (Fin m → ℝ) volume :=
  inferInstanceAs (VAddInvariantMeasure L.module.toAddSubgroup (Fin m → ℝ) volume)



def periodize {m : ℕ} (L : FullLattice m) (f : (Fin m → ℝ) → ℝ≥0∞)
    (x : Fin m → ℝ) : ℝ≥0∞ := ∑' z : L.module, f (x+z)

def pointCount {m : ℕ} (L : FullLattice m) (J : Set (Fin m → ℝ)) :
    (Fin m → ℝ) → ℝ≥0∞ := periodize L (J.indicator 1)

def cell {m : ℕ} (L : FullLattice m) : Set (Fin m → ℝ) :=
  ZSpan.fundamentalDomain (latticeBasis L.module)


def translateLaw {m : ℕ} (L : FullLattice m) : Measure (Fin m → ℝ) :=
  (volume (cell L))⁻¹ • volume.restrict (cell L)



end SingleLatticeCovering.RogersPreparation

end
end




noncomputable section
open Module Submodule MeasureTheory
open scoped BigOperators

namespace SingleLatticeCovering.PrimeKernel
variable {ι : Type*} [Fintype ι] [DecidableEq ι]


def tailForm (i : ι) (a : ι → ℤ) (x : ι → ℝ) : ℝ :=
  ∑ j ∈ Finset.univ.erase i, (a j : ℝ)*x j

lemma tailForm_update (i : ι) (a : ι → ℤ) (x : ι → ℝ) (r : ℝ) :
    tailForm i a (Function.update x i r) = tailForm i a x := by
  unfold tailForm
  apply Finset.sum_congr rfl
  intro j hj
  rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]

lemma tailForm_add (i : ι) (a : ι → ℤ) (x y : ι → ℝ) :
    tailForm i a (x+y) = tailForm i a x+tailForm i a y := by
  simp [tailForm, mul_add, Finset.sum_add_distrib]
lemma tailForm_smul (i : ι) (a : ι → ℤ) (r : ℝ) (x : ι → ℝ) :
    tailForm i a (r • x) = r*tailForm i a x := by
  simp only [tailForm, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_left_comm]


def coordinates (p : ℕ) (hp : 0 < p) (i : ι) (a : ι → ℤ) :
    (ι → ℝ) ≃ₗ[ℝ] (ι → ℝ) where
  toFun x := Function.update x i ((x i+tailForm i a x)/p)
  invFun x := Function.update x i ((p : ℝ)*x i-tailForm i a x)
  left_inv x := by
    have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
    ext j
    by_cases hji : j=i
    · subst j
      simp only [Function.update_self,tailForm_update]
      field_simp [hpR]
      ring
    · simp [Function.update_of_ne hji]
  right_inv x := by
    have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
    ext j
    by_cases hji : j=i
    · subst j
      simp only [Function.update_self,tailForm_update]
      field_simp [hpR]
      ring
    · simp [Function.update_of_ne hji]
  map_add' x y := by
    ext j
    by_cases hji : j=i
    · subst j
      simp only [Function.update_self,Pi.add_apply,tailForm_add]
      ring
    · simp [Function.update_of_ne hji]
  map_smul' r x := by
    ext j
    by_cases hji : j=i
    · subst j
      simp only [Function.update_self,Pi.smul_apply,smul_eq_mul,tailForm_smul,RingHom.id_apply]
      ring
    · simp [Function.update_of_ne hji]

def basis (p : ℕ) (hp : 0 < p) (i : ι) (a : ι → ℤ) : Basis ι ℝ (ι → ℝ) :=
  Basis.ofEquivFun (coordinates p hp i a)

def lattice (p : ℕ) (hp : 0 < p) (i : ι) (a : ι → ℤ) : Submodule ℤ (ι → ℝ) :=
  Submodule.span ℤ (Set.range (basis p hp i a))

instance lattice_discrete (p : ℕ) (hp : 0 < p) (i : ι) (a : ι → ℤ) :
    DiscreteTopology (lattice p hp i a) := inferInstanceAs
      (DiscreteTopology (Submodule.span ℤ (Set.range (basis p hp i a))))
instance lattice_full (p : ℕ) (hp : 0 < p) (i : ι) (a : ι → ℤ) :
    IsZLattice ℝ (lattice p hp i a) := inferInstanceAs
      (IsZLattice ℝ (Submodule.span ℤ (Set.range (basis p hp i a))))





end SingleLatticeCovering.PrimeKernel




end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIB3_Slc.LatticeCovering_PrimeKernels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
noncomputable section
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
section
noncomputable section
open Module Submodule MeasureTheory
open scoped BigOperators

namespace SingleLatticeCovering.PrimeKernel
open LatticeGeometry Module Submodule MeasureTheory
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def scaleFactor (p : ℕ) : ℝ := (p : ℝ)^(-(Fintype.card ι : ℝ)⁻¹)
lemma scaleFactor_pos {ι : Type*} [Fintype ι] [DecidableEq ι] (p : ℕ) (hp : 0 < p) : 0 < scaleFactor (ι := ι) p :=
  Real.rpow_pos_of_pos (by exact_mod_cast hp) _

def normalizeEquiv (p : ℕ) (hp : 0 < p) : (ι → ℝ) ≃ₗ[ℝ] (ι → ℝ) :=
  LinearEquiv.smulOfNeZero ℝ (ι → ℝ) (scaleFactor (ι := ι) p) (scaleFactor_pos p hp).ne'

abbrev normalized (p : ℕ) (hp : 0 < p) (i : ι) (a : ι → ℤ) : Submodule ℤ (ι → ℝ) :=
  image (lattice p hp i a) (normalizeEquiv p hp)


def gridMap (p : ℕ) (hp : 0 < p) : (ι → ℤ) →+ (ι → ℝ) where
  toFun z := normalizeEquiv p hp (fun j => (z j : ℝ))
  map_zero' := by
    simp only [Pi.zero_apply,Int.cast_zero]
    exact map_zero (normalizeEquiv (ι := ι) p hp)
  map_add' z w := by
    change normalizeEquiv p hp (fun j => ((z+w) j : ℝ))=_
    rw [show (fun j => ((z+w) j : ℝ)) = (fun j => (z j : ℝ))+(fun j => (w j : ℝ)) by
      ext j; simp]
    exact map_add _ _ _

def modForm (p : ℕ) (i : ι) (a : ι → ℤ) : (ι → ℤ) →+ ZMod p where
  toFun z := (z i : ZMod p)+∑ j ∈ Finset.univ.erase i, (a j : ZMod p)*(z j : ZMod p)
  map_zero' := by simp
  map_add' z w := by
    simp only [Pi.add_apply,Int.cast_add,mul_add,Finset.sum_add_distrib]
    ring



end SingleLatticeCovering.PrimeKernel

namespace SingleLatticeCovering.PrimeKernel
open Set MeasureTheory
open scoped Pointwise BigOperators ENNReal
variable {ι : Type*} [Fintype ι] [DecidableEq ι]



def rectangularCell (p : ℕ) (i : ι) : Set (ι → ℝ) :=
  Set.univ.pi (fun j => Set.Ico (0:ℝ) (if j=i then (p:ℝ) else 1))


end SingleLatticeCovering.PrimeKernel

namespace SingleLatticeCovering.PrimeKernel
open Set MeasureTheory
open scoped Pointwise BigOperators ENNReal
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

abbrev normalizedRectangularCell (p : ℕ) (hp : 0 < p) (i : ι) : Set (ι → ℝ) :=
  normalizeEquiv p hp '' rectangularCell p i



end SingleLatticeCovering.PrimeKernel

namespace SingleLatticeCovering.PrimeKernel
open Set MeasureTheory
open scoped Pointwise BigOperators ENNReal
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def gridUnitCell : Set (ι → ℝ) := Set.univ.pi (fun _ => Set.Ico (0:ℝ) 1)
def offsetVector (i : ι) (b : ℤ) : ι → ℤ := Pi.single i b

def offsetCell (p : ℕ) (hp : 0 < p) (i : ι) (b : Fin p) : Set (ι → ℝ) :=
  normalizeEquiv p hp '' ((fun j => ((offsetVector i b.val j:ℤ):ℝ)) +ᵥ gridUnitCell)


end SingleLatticeCovering.PrimeKernel

namespace SingleLatticeCovering.PrimeKernel
open Set MeasureTheory
open scoped Pointwise BigOperators ENNReal
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def badOffsets (p : ℕ) (i : ι) (a : ι → ℤ) (S : Finset (ι → ℤ)) : Finset (Fin p) := by
  classical
  exact Finset.univ.filter (fun b => ∀ z ∈ S, modForm p i a z ≠ (b.val:ZMod p))

end SingleLatticeCovering.PrimeKernel

namespace SingleLatticeCovering.PrimeKernel
open RogersPreparation Horizontal Set MeasureTheory
open scoped Pointwise ENNReal
variable {d : ℕ}

def normalizedFull (p : ℕ) (hp : 0 < p) (i : Fin d) (a : Fin d → ℤ) : FullLattice d :=
  ⟨normalized p hp i a,inferInstance,inferInstance⟩

end SingleLatticeCovering.PrimeKernel


noncomputable section
namespace SingleLatticeCovering.AffineVoid
open scoped BigOperators
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
variable {n : ℕ} {σ : Type*} [Fintype σ]

def normalDual (c : Kˣ) (b : K) (a : Fin n → K) : Fin (n+2) → K :=
  Fin.cons (-(c:K)*b) (Fin.cons (c:K) (fun j => (c:K)*a j))

def fullMiss (v : σ → Fin (n+1) → K) (w : Fin (n+2) → K) : ℝ := by
  classical
  exact if ∀ i, (∑ j, w j * (Fin.cons (1:K) (v i) : Fin (n+2) → K) j) ≠ 0 then 1 else 0

def normalizedMiss (v : σ → Fin (n+1) → K) (a : Fin n → K) (b : K) : ℝ := by
  classical
  exact if ∀ i, v i 0 + ∑ j, a j*v i j.succ ≠ b then 1 else 0

def meanFull (v : σ → Fin (n+1) → K) : ℝ :=
  (∑ w : Fin (n+2) → K, fullMiss v w)/(Fintype.card K:ℝ)^(n+2)
def meanNormalized (v : σ → Fin (n+1) → K) : ℝ :=
  (∑ a : Fin n → K, ∑ b : K, normalizedMiss v a b)/(Fintype.card K:ℝ)^(n+1)


end SingleLatticeCovering.AffineVoid


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIB3_Slc.LatticeCovering_MeanHoles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
noncomputable section
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
section
noncomputable section
open Module Submodule MeasureTheory
open scoped BigOperators
noncomputable section
noncomputable section

namespace SingleLatticeCovering.PrimeKernel
open Set MeasureTheory Filter Topology AffineVoid ConvexGrid BrokenCircuit PrimeCircuit
open scoped Pointwise ENNReal BigOperators
variable {n : ℕ}

def liftCoeff {p : ℕ} (a : Fin n → ZMod p) : Fin (n+1) → ℤ :=
  Fin.cons 0 (fun j => (a j).val)

def finResidue (p : ℕ) [NeZero p] : Fin p ≃ ZMod p where
  toFun b := (b.val:ZMod p)
  invFun b := ⟨b.val,ZMod.val_lt b⟩
  left_inv b := by apply Fin.ext; simp [ZMod.val_natCast,Nat.mod_eq_of_lt b.isLt]
  right_inv b := ZMod.natCast_zmod_val b

abbrev ensembleFull (p : ℕ) (hp : 0<p) (a : Fin n → ZMod p) : Horizontal.FullLattice (n+1) :=
  normalizedFull p hp 0 (liftCoeff a)

def meanPrimeHole (J : Set (Fin (n+1) → ℝ)) (p : ℕ) [Fact p.Prime] : ℝ :=
  (∑ a : Fin n → ZMod p, ((ensembleFull p (Nat.Prime.pos Fact.out) a).hole J).toReal)/(p:ℝ)^n



end SingleLatticeCovering.PrimeKernel

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIB3_Slc.LatticeCovering_GaussianMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section




noncomputable section

namespace SingleLatticeCovering.GaussianProjection
open MeasureTheory ProbabilityTheory Set Filter
open SingleLatticeCovering.Isotropization
open scoped ENNReal RealInnerProductSpace BigOperators

def radialGaussianAverage {n : ℕ} (μ : Measure (E n)) (s : ℝ) : ℝ :=
  ∫ x, Real.exp (-s^2*‖x‖^2/2) ∂μ



end SingleLatticeCovering.GaussianProjection

namespace SingleLatticeCovering.GaussianProjection
open MeasureTheory ProbabilityTheory Set Filter
open SingleLatticeCovering.Isotropization
open scoped ENNReal RealInnerProductSpace BigOperators ComplexConjugate

noncomputable def phase {n : ℕ} (s : ℝ) (x g : E n) : ℂ :=
  Complex.exp ((s*⟪x,g⟫ : ℝ)*Complex.I)



end SingleLatticeCovering.GaussianProjection

namespace SingleLatticeCovering.GaussianProjection
open MeasureTheory ProbabilityTheory Set Filter
open SingleLatticeCovering.Isotropization
open scoped ENNReal RealInnerProductSpace BigOperators ComplexConjugate

abbrev MatrixSpace (n k : ℕ) := EuclideanSpace ℝ (Fin n × Fin k)

noncomputable def rowApply {n k : ℕ} (g : MatrixSpace n k) (t : E k) : E n :=
  WithLp.toLp 2 (fun i => ∑ j : Fin k, g (i,j)*t j)

noncomputable def colApply {n k : ℕ} (g : MatrixSpace n k) (x : E n) : E k :=
  WithLp.toLp 2 (fun j => ∑ i : Fin n, g (i,j)*x i)

noncomputable def tensor {n k : ℕ} (x : E n) (t : E k) : MatrixSpace n k :=
  WithLp.toLp 2 (fun p => x p.1*t p.2)


end SingleLatticeCovering.GaussianProjection

namespace SingleLatticeCovering.GaussianProjection
open MeasureTheory ProbabilityTheory Set Filter
open SingleLatticeCovering.Isotropization
open scoped ENNReal RealInnerProductSpace BigOperators ComplexConjugate

noncomputable def matrixSmoothingError {n k : ℕ} (μ : Measure (E n)) (a : ℝ) (g : MatrixSpace n k) : ℝ :=
  ∫ t, ‖charFun μ (a•rowApply g t)-(radialGaussianAverage μ (a*‖t‖) : ℂ)‖ ∂stdGaussian (E k)

noncomputable def smoothedProjection {n k : ℕ} (μ : Measure (E n)) (s r : ℝ)
    (g : MatrixSpace n k) (y : E k) : ℝ :=
  ∫ x, Real.exp (-r^2*‖y-s•colApply g x‖^2/2) ∂μ

noncomputable def radialSmoothedModel {n k : ℕ} (μ : Measure (E n)) (s r : ℝ) (y : E k) : ℂ :=
  ∫ t, phase r y t*(radialGaussianAverage μ ((-r*s)*‖t‖) : ℂ) ∂stdGaussian (E k)




end SingleLatticeCovering.GaussianProjection


end
end

end OAI
end

section
-- module Solutions.OAIB3_Slc.LatticeCovering_GaussianSmoothing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section

namespace SingleLatticeCovering.GaussianProjection
open MeasureTheory ProbabilityTheory Set Filter
open SingleLatticeCovering.Isotropization
open scoped ENNReal RealInnerProductSpace BigOperators ComplexConjugate

noncomputable def radialSmoothedDensity {n k : ℕ} (μ : Measure (E n)) (s r : ℝ) (y : E k) : ℝ :=
  (radialSmoothedModel μ s r y).re



end SingleLatticeCovering.GaussianProjection
noncomputable section
namespace SingleLatticeCovering.GaussianDensity
open MeasureTheory ProbabilityTheory Set Filter GaussianFourier
open scoped ENNReal RealInnerProductSpace ComplexConjugate
abbrev E (k : ℕ) := EuclideanSpace ℝ (Fin k)

def normalizer (k : ℕ) (b : ℝ) : ℝ := (Real.pi/b)^((k:ℝ)/2)
def density {k : ℕ} (b : ℝ) (y : E k) : ℝ := (normalizer k b)⁻¹*Real.exp (-b*‖y‖^2)
def law (k : ℕ) (b : ℝ) : Measure (E k) :=
  volume.withDensity (fun y => ENNReal.ofReal (density b y))


end SingleLatticeCovering.GaussianDensity





open MeasureTheory Filter Set
open scoped Topology
noncomputable section



namespace SingleLatticeCovering.Prekopa
open MeasureTheory Set Filter
open scoped ENNReal Topology BigOperators

abbrev RV (d : ℕ) := Fin d → ℝ

def gaussianKernel (d : ℕ) (c : ℝ) (x : RV d) : ℝ :=
  Real.exp (-c*∑ i, (x i)^2)



def GaussianBound {d : ℕ} (f : RV d → ℝ) : Prop :=
  ∃ A c : ℝ, 0 < A ∧ 0 < c ∧ ∀ x, |f x| ≤ A*gaussianKernel d c x

def marginalOne {d : ℕ} (f : RV (d+1) → ℝ) (y : RV d) : ℝ :=
  ∫ t, f (Fin.cons t y)


end SingleLatticeCovering.Prekopa


end
end
end
end

end OAI
end

section
-- module Solutions.OAIB3_Slc.LatticeCovering_LogConcavity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
noncomputable section

noncomputable section
namespace SingleLatticeCovering.Prekopa
open MeasureTheory Set Filter Metric
open scoped ENNReal Topology BigOperators

def softIndicator {d : ℕ} (K : Set (RV d)) (t : ℝ) (x : RV d) : ℝ :=
  Real.exp (-t*(infDist x K)^2)



end SingleLatticeCovering.Prekopa

namespace SingleLatticeCovering.Prekopa
open MeasureTheory Set Filter
open scoped ENNReal Topology

def ScalarLogConcave (f : ℝ → ℝ) : Prop :=
  (∀ t, 0 ≤ f t) ∧ ∀ u v a b : ℝ, 0 < a → 0 < b → a+b=1 →
    f u^a*f v^b ≤ f (a*u+b*v)



end SingleLatticeCovering.Prekopa

namespace SingleLatticeCovering.Prekopa
open MeasureTheory Set Filter
open scoped Topology

def shellRate (u : ℝ) : ℝ := u-1-Real.log u



end SingleLatticeCovering.Prekopa


end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIB3_Slc.LatticeCovering_RadialBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
noncomputable section
noncomputable section

namespace SingleLatticeCovering.Radial
open Set MeasureTheory Isotropization
open scoped RealInnerProductSpace Topology

noncomputable def radialInf {k : ℕ} (f : E k → ℝ) (y : E k) : ℝ :=
  ⨅ U : E k ≃ₗᵢ[ℝ] E k, f (U y)




end SingleLatticeCovering.Radial

namespace SingleLatticeCovering.Prekopa
open MeasureTheory Set Filter Metric Sections Isotropization
open scoped ENNReal Topology BigOperators RealInnerProductSpace

noncomputable def smoothingKernel {n D : ℕ} (A : RV n →ₗ[ℝ] E D) (c : ℝ) (y : E D) (x : RV n) : ℝ :=
  Real.exp (-c*‖y-A x‖^2)


end SingleLatticeCovering.Prekopa

namespace SingleLatticeCovering.Prekopa
open MeasureTheory Set Filter
open scoped ENNReal Topology

noncomputable def fourthMomentConstant : ℝ := 8*Real.exp 1*16^4*6



end SingleLatticeCovering.Prekopa


end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIB3_Slc.LatticeCovering_Marginals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace SingleLatticeCovering.GaussianProjection
open MeasureTheory ProbabilityTheory Set Filter Isotropization GaussianDensity Prekopa
open scoped ENNReal Topology RealInnerProductSpace BigOperators

noncomputable def colLinear {n k : ℕ} (g : MatrixSpace n k) : Isotropization.E n →ₗ[ℝ] Isotropization.E k where
  toFun := colApply g
  map_add' x z := by
    ext j
    simp only [colApply,PiLp.add_apply,mul_add,Finset.sum_add_distrib]
  map_smul' a x := by
    ext j
    simp only [colApply,PiLp.smul_apply,smul_eq_mul,RingHom.id_apply]
    simp only [←Finset.mul_sum,mul_left_comm]

noncomputable def normalizedProjection {n k : ℕ} (μ : Measure (Isotropization.E n)) (s r : ℝ)
    (g : MatrixSpace n k) (y : Isotropization.E k) : ℝ :=
  (normalizer k (r^2/2))⁻¹*smoothedProjection μ s r g y


end SingleLatticeCovering.GaussianProjection


end

end OAI
end

section
-- module Solutions.OAIB3_Slc.LatticeCovering_ProjectionBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace SingleLatticeCovering.GaussianProjection
open MeasureTheory ProbabilityTheory Set Filter Isotropization GaussianDensity Prekopa Radial
open scoped ENNReal Topology RealInnerProductSpace BigOperators

noncomputable def scaleVariance {n : ℕ} (s r : ℝ) (x : Isotropization.E n) : ℝ :=
  (s*‖x‖)^2+1/r^2

noncomputable def normalizedModel {n k : ℕ} (μ : Measure (Isotropization.E n)) (s r : ℝ)
    (y : Isotropization.E k) : ℝ :=
  (normalizer k (r^2/2))⁻¹*radialSmoothedDensity μ s r y

noncomputable def projectionError (n k : ℕ) (s r : ℝ) : ℝ :=
  (normalizer k (r^2/2))⁻¹*|r*s| *Real.sqrt (Real.sqrt (n:ℝ))*Real.sqrt (k:ℝ)


end SingleLatticeCovering.GaussianProjection

end

section
namespace SingleLatticeCovering.GaussianProjection
open MeasureTheory ProbabilityTheory Set Filter Isotropization GaussianDensity Prekopa Radial
open scoped ENNReal Topology RealInnerProductSpace BigOperators

noncomputable def shellError (n k : ℕ) (s r T ε : ℝ) : ℝ :=
  (4*((k-1:ℕ)+1:ℝ)/((k-1:ℕ)*ε)*Real.exp (-((k-1:ℕ):ℝ)*ε^2/9))+
    2*(projectionError n k s r*volume.real (Metric.closedBall (0:Isotropization.E k) T)+
      (k:ℝ)*(s^2*(n:ℝ)+1/r^2)/T^2)

noncomputable def shellLoss (n k : ℕ) (s r T ε : ℝ) : ℝ :=
  shellError n k s r T ε/(1-Real.exp (-(k:ℝ)*ε^2/16))


end SingleLatticeCovering.GaussianProjection

end

section
namespace SingleLatticeCovering.GaussianDensity
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal RealInnerProductSpace

noncomputable def densityFloor (k : ℕ) (R : ℝ) : ℝ :=
  (normalizer k (1/8))⁻¹*Real.exp (-8*(R+1)^2)


end SingleLatticeCovering.GaussianDensity

end

end OAI
end

section
-- module Solutions.OAIB3_Slc.LatticeCovering_Desmoothing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace SingleLatticeCovering.CanonicalDensity
open MeasureTheory MeasureTheory.Measure Set Filter Topology Isotropization Sections Prekopa
open scoped ENNReal

noncomputable def canonical {m D : ℕ} (K : Set ((Fin m → ℝ) × E D)) (y : E D) : ℝ :=
  ((volume K)⁻¹).toReal*(volume (fiber K y)).toReal



end SingleLatticeCovering.CanonicalDensity

end

section
namespace SingleLatticeCovering.GaussianProjection
open MeasureTheory ProbabilityTheory Set Filter Isotropization GaussianDensity Prekopa Radial CanonicalDensity
open scoped ENNReal Topology RealInnerProductSpace BigOperators

noncomputable def localStep (R : ℝ) : ℝ := 1/(100*(R+1))
noncomputable def tailError (D : ℕ) (r R : ℝ) : ℝ :=
  (normalizer D (r^2/2))⁻¹*Real.exp (-(r^2/2)*(localStep R)^2)


end SingleLatticeCovering.GaussianProjection

end

section
namespace SingleLatticeCovering.CanonicalDensity
open MeasureTheory MeasureTheory.Measure Set Isotropization Sections
open scoped ENNReal

noncomputable def verticalScale (m D : ℕ) {a : ℝ} (ha : a ≠ 0) :
    ((Fin m → ℝ) × E D) ≃ₗ[ℝ] ((Fin m → ℝ) × E D) :=
  (LinearEquiv.refl ℝ _).prodCongr (LinearEquiv.smulOfNeZero ℝ (E D) a ha)


end SingleLatticeCovering.CanonicalDensity

end

end OAI
end

section
-- module Solutions.OAIB3_Slc.LatticeCovering_GaussianRates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace SingleLatticeCovering.GaussianNumerics
open MeasureTheory Filter GaussianDensity GaussianProjection Asymptotics
open scoped Topology

noncomputable def A : ℝ := 1000+|Real.log (8*Real.pi)|+|Real.log Real.pi|
noncomputable def B : ℝ := 2*A+100

noncomputable def errBound (t : ℝ) := Real.exp (B*t^20-t^30)
noncomputable def tailBound (t : ℝ) := Real.exp ((A+10)*t^6-t^16/980000)

end SingleLatticeCovering.GaussianNumerics

end

section
namespace SingleLatticeCovering.GaussianNumerics
open MeasureTheory Filter GaussianDensity GaussianProjection
open scoped Topology

noncomputable def shellRate (t : ℝ) := 800*t*Real.exp (-t^2/180000)
noncomputable def denRate (t : ℝ) := Real.exp (-t^2/160000)
noncomputable def shellBound (t : ℝ) := 2*(shellRate t+2*(errBound t+2/t^16))

end SingleLatticeCovering.GaussianNumerics

end




end OAI
end

section
-- module Solutions.OAIB3_Slc.LatticeCovering_GaussianPositions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace SingleLatticeCovering.FinalRates
open Real Filter Topology Asymptotics

noncomputable def localScale (C : ℝ) (n : ℕ) : ℕ := ⌈sectionRadius C n⌉₊+2


end SingleLatticeCovering.FinalRates



end OAI
end


