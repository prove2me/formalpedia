-- Prove2me | Definitions.Def_OAIQ16Cd000
-- name    : OAIQ16Cd000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-26T14:40:11.803713+00:00
-- url     : https://prove2.me/theorems/35e67156-08a3-4fcf-88e8-b2523e62bd07
-- title:
--   Definitions bundle OAIQ16Cd000 of the split of OpenAI, The optimal order of convex-body covering density
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.CoveringOrder.optimal_order`, carved from OpenAI's openai/math development (OpenAI, *The optimal order of convex-body covering density*, OpenAI Math Release, September 23, 2026, result family 92, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 487 declarations of OpenAI's Lean: 387 definitions, 8 inductive types or structures, 23 instances and 69 theorems. The definitions and types are `OAI.ActivityBins.count`, `OAI.AllLatticeExclusion.Space`, `OAI.BlockGeometry.loss`, `OAI.BlockGeometry.radius`, `OAI.BlockSets.clipped`, `OAI.BlockSets.common`, `OAI.BlockSets.cost`, `OAI.Blocks.weight`, `OAI.BodySelection.Space`, `OAI.BodySelection.bad`, `OAI.BodyVolume.law`, `OAI.CapAffinity.signed`, `OAI.CapCost.intensity`, `OAI.CapCost.rate`, `OAI.CapGeometry.axial`, `OAI.CapGeometry.axis`, `OAI.CapGeometry.halfcap`, `OAI.CapGeometry.radial`, `OAI.CapLens.unit`, `OAI.CellCounts.assignmentWeight`, `OAI.CellCounts.collisionSum`, `OAI.CellCounts.force`, `OAI.CellCounts.injectiveSum`, `OAI.CellCounts.pairs`, `OAI.CellCounts.slotWeight`, `OAI.CellMatching.Classes`, `OAI.CellMatching.ExactPair`, `OAI.CellMatching.IsMatching`, `OAI.CellMatching.Matching`, `OAI.CellMatching.allDiagramsEquiv`, `OAI.CellMatching.classIncidence`, `OAI.CellMatching.collapse`, `OAI.CellMatching.diagramEquiv`, `OAI.CellMatching.exactMatching`, `OAI.CellMatching.expand`, `OAI.CellMatching.jointWeight`, `OAI.CellMatching.pairWeight`, `OAI.CellMatching.rightClass`, `OAI.CellMatching.support`, `OAI.ConeStretch.Space` and 355 more.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: `CoveringDensity_Main`, `LatticeCovering_Bits`, `LatticeCovering_BrokenCircuits`, `LatticeCovering_CircuitErrors`, `LatticeCovering_CircuitLattices`, `LatticeCovering_CircuitSums`, `LatticeCovering_CircuitVolumes`, `LatticeCovering_Completion`, `LatticeCovering_Concentration`, `LatticeCovering_Covering`, `LatticeCovering_Desmoothing`, `LatticeCovering_Folded`, `LatticeCovering_GaussianMoments`, `LatticeCovering_GaussianPositions`, `LatticeCovering_GaussianRates`, `LatticeCovering_GaussianSections`, `LatticeCovering_GaussianSmoothing`, `LatticeCovering_GridCounts`, `LatticeCovering_Horizontal`, `LatticeCovering_Isotropy`, `LatticeCovering_Lines`, `LatticeCovering_LogConcavity`, `LatticeCovering_Marginals`, `LatticeCovering_MeanHoles`, `LatticeCovering_Model`, `LatticeCovering_Patterns`, `LatticeCovering_PrimeGrids`, `LatticeCovering_PrimeKernels`, `LatticeCovering_Products`, `LatticeCovering_ProjectionBounds`, `LatticeCovering_RadialBounds`, `LatticeCovering_Rates`, `LatticeCovering_Rounding`, `LatticeCovering_Sampling`, `LatticeCovering_SamplingBounds`, `LatticeCovering_Sections`, `LatticeCovering_Shears`, `LatticeCovering_Transport`, `TranslativeCovering_ActivityBins`, `TranslativeCovering_AllLatticeExclusion`, `TranslativeCovering_BlockGeometry`, `TranslativeCovering_BlockSets`, `TranslativeCovering_Blocks`, `TranslativeCovering_BodySelection`, `TranslativeCovering_BodyVolume`, `TranslativeCovering_CapAffinity`, `TranslativeCovering_CapCost`, `TranslativeCovering_CapGeometry`, `TranslativeCovering_CapLens`, `TranslativeCovering_CellCounts`, `TranslativeCovering_CellMatching`, `TranslativeCovering_ConeStretch`, `TranslativeCovering_CubicLattice`, `TranslativeCovering_CylinderProbability`, `TranslativeCovering_CylinderVolume`, `TranslativeCovering_FiniteJanson`, `TranslativeCovering_JansonSampling`, `TranslativeCovering_LatticeAveraging`, `TranslativeCovering_LocalizationComplete`, `TranslativeCovering_LocalizationGood`, `TranslativeCovering_LocalizationMeans`, `TranslativeCovering_LocalizationRates`, `TranslativeCovering_LocalizationRounding`, `TranslativeCovering_MatchingAlgebra`, `TranslativeCovering_MatchingBounds`, `TranslativeCovering_MatchingSelf`, `TranslativeCovering_PatternCross`, `TranslativeCovering_PatternEnumeration`, `TranslativeCovering_PatternGeometry`, `TranslativeCovering_PatternRounding`, `TranslativeCovering_PatternTail`, `TranslativeCovering_PatternWitness`, `TranslativeCovering_PeriodicDensity`, `TranslativeCovering_PeriodicEquality`, `TranslativeCovering_Periodization`, `TranslativeCovering_PoissonCells`, `TranslativeCovering_PoissonConfig`, `TranslativeCovering_PoissonDiagrams`, `TranslativeCovering_PoissonFinite`, `TranslativeCovering_PoissonMeasureCells`, `TranslativeCovering_PoissonRealization`, `TranslativeCovering_PoissonSample`, `TranslativeCovering_ProjectiveCaps`, `TranslativeCovering_RadialCost`, `TranslativeCovering_RadialIntegral`, `TranslativeCovering_RadialShell`, `TranslativeCovering_RandomBody`, `TranslativeCovering_ResidualCaps`, `TranslativeCovering_ShellCaps`, `TranslativeCovering_SourceLocalization`, `TranslativeCovering_SourceParameters`, `TranslativeCovering_SphericalLaw`.
--
--   **Imports.** It imports the published bundle `Def_CoveringDensity`.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ16Cd002`; the statements `OAI.AllLatticeExclusion.no_cover`, `OAI.Blocks.block_estimates`, `OAI.BodySelection.volume_lower`, `OAI.CapCost.clipped_cost`, `OAI.CapCost.raw_upper`, `OAI.CapGeometry.halfcap_ratio`, `OAI.CapOverlap.cap_ratio_decay`, `OAI.LensDeployment.tangent_bad_vector`, `OAI.LocalizationComplete.localize`, `OAI.NormalizedCaps.clipped_affinity`, `OAI.PatternTail.bound`, `OAI_PatternWitness_construct`, `OAI.PoissonBinned.bound`, `OAI.PoissonLimit.lower_tail`, `OAI.RadiusLens.lens_at_radius`, `OAI_SingleLatticeCovering_Assembly_sections_and_circuits_cover`, `OAI.SingleLatticeCovering.GaussianNumerics.eventually_local_position`, `OAI.SingleLatticeCovering.PrimeKernel.eventually_meanPrimeHole_all`, `OAI.SlotGeometry.ratio`, `OAI.SourcePatternTail.uniform`, `OAI_SphericalBlocks_blocks`, `OAI_SphericalBlocks_uniform_lens` and `OAI.WitnessConstruction.shell`; the proofs of `OAI.AllLatticeExclusion.no_cover`, `OAI.Blocks.block_estimates`, `OAI.CapOverlap.cap_ratio_decay`, `OAI.LocalizationComplete.localize`, `OAI_PatternWitness_construct`, `OAI.PoissonBinned.bound`, `OAI.PoissonLimit.lower_tail`, `OAI_SingleLatticeCovering_Assembly_sections_and_circuits_cover`, `OAI.SourcePatternTail.uniform`, `OAI_SphericalBlocks_blocks`, `OAI_SphericalBlocks_uniform_lens` and `OAI.WitnessConstruction.shell`.
-- source:
--   OpenAI, The optimal order of convex-body covering density, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 92; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Translative-covering-densities-of-order-n-log-n-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit adc7f12

import Mathlib
import Definitions.Def_CoveringDensity

section
-- module Solutions.OAIQ16_CD.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    dite p a b = a h := dif_pos h
theorem dite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : ¬p) :
    dite p a b = b h := dif_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ16_CD.LatticeCovering_Model
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Convex bodies and exact coverings by a single lattice in real coordinate space. -/

namespace SingleLatticeCovering

open MeasureTheory
open scoped Pointwise

abbrev Space (n : ℕ) := Fin n → ℝ

def IsConvexBody {n : ℕ} (K : Set (Space n)) : Prop :=
  IsCompact K ∧ Convex ℝ K ∧ (interior K).Nonempty

def LatticeCovers {n : ℕ} (K : Set (Space n)) (L : Submodule ℤ (Space n)) : Prop :=
  K + (L : Set (Space n)) = Set.univ

end SingleLatticeCovering

end OAI
end

section
-- module Solutions.OAIQ16_CD.LatticeCovering_Folded
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
-- module Solutions.OAIQ16_CD.LatticeCovering_Concentration
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
-- module Solutions.OAIQ16_CD.LatticeCovering_Rounding
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
-- module Solutions.OAIQ16_CD.LatticeCovering_Sampling
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
-- module Solutions.OAIQ16_CD.LatticeCovering_SamplingBounds
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
-- module Solutions.OAIQ16_CD.LatticeCovering_Bits
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
-- module Solutions.OAIQ16_CD.LatticeCovering_Lines
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
open Filter Topology Real ConstructionA _root_.OAI.SingleLatticeCovering.Blocks
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
-- module Solutions.OAIQ16_CD.LatticeCovering_Products
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
-- module Solutions.OAIQ16_CD.LatticeCovering_Patterns
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

def first {q : ℕ} : Pattern α (q+1) → Pattern α q
  | .mono _ p => p
  | .split _ p _ => p

end Pattern



end SingleLatticeCovering.Shear

namespace SingleLatticeCovering.Shear.Pattern
variable {α : Type*}
local instance instDecidableEqProdForallFinReal {q : ℕ} : DecidableEq ((Fin q → ℝ) × α) := Classical.decEq _



def appendPoint {q : ℕ} (v : ℝ) (l : (Fin q → ℝ) × α) : (Fin (q+1) → ℝ) × α :=
  (Fin.snoc l.1 v, l.2)

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
-- module Solutions.OAIQ16_CD.LatticeCovering_Shears
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

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
-- module Solutions.OAIQ16_CD.LatticeCovering_Completion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

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
-- module Solutions.OAIQ16_CD.LatticeCovering_Covering
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
-- module Solutions.OAIQ16_CD.LatticeCovering_Sections
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
-- module Solutions.OAIQ16_CD.LatticeCovering_Rates
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

end

end OAI
end

section
-- module Solutions.OAIQ16_CD.LatticeCovering_Horizontal
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
open MeasureTheory Folded LatticeGeometry Completion Shear CoverGeometry Sections Horizontal
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
-- module Solutions.OAIQ16_CD.LatticeCovering_Isotropy
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
-- module Solutions.OAIQ16_CD.LatticeCovering_GaussianSections
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
  ⟨LatticeGeometry.image L.module e,inferInstance,by first | infer_instance | exact Measure.isProbabilityMeasure_map (by fun_prop)⟩

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
-- module Solutions.OAIQ16_CD.LatticeCovering_GridCounts
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
-- module Solutions.OAIQ16_CD.LatticeCovering_Transport
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
  all_goals try with_reducible_and_instances rfl
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


open MeasureTheory Filter Set
open scoped Topology ENNReal
noncomputable section
namespace SingleLatticeCovering.SharpYoung

def finMarginal {d : ℕ} (f : (Fin (d+1) → ℝ) → ℝ) (y : Fin d → ℝ) : ℝ :=
  ∫ t : ℝ, f (Fin.cons t y)



end SingleLatticeCovering.SharpYoung

namespace SingleLatticeCovering.SimplexYoung
open MeasureTheory Measure Set Matrix
open scoped ENNReal Pointwise


def weightedSimplexConfiguration {r d : ℕ} (J : Set (Fin d → ℝ))
    (c : Fin r → ℝ) : Set (Fin d → V r) :=
  {x | (∀ j, (fun a => x a j) ∈ J) ∧ (fun a => ∑ j, c j * x a j) ∈ J}


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
-- module Solutions.OAIQ16_CD.LatticeCovering_CircuitVolumes
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
-- module Solutions.OAIQ16_CD.LatticeCovering_CircuitLattices
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
-- module Solutions.OAIQ16_CD.LatticeCovering_CircuitSums
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
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by fun_prop)

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
-- module Solutions.OAIQ16_CD.LatticeCovering_BrokenCircuits
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
-- module Solutions.OAIQ16_CD.LatticeCovering_PrimeGrids
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
-- module Solutions.OAIQ16_CD.LatticeCovering_CircuitErrors
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
-- module Solutions.OAIQ16_CD.LatticeCovering_PrimeKernels
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
  ⟨normalized p hp i a,inferInstance,by first | infer_instance | exact Measure.isProbabilityMeasure_map (by fun_prop)⟩

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
-- module Solutions.OAIQ16_CD.LatticeCovering_MeanHoles
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
-- module Solutions.OAIQ16_CD.LatticeCovering_GaussianMoments
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
-- module Solutions.OAIQ16_CD.LatticeCovering_GaussianSmoothing
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
-- module Solutions.OAIQ16_CD.LatticeCovering_LogConcavity
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
-- module Solutions.OAIQ16_CD.LatticeCovering_RadialBounds
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
-- module Solutions.OAIQ16_CD.LatticeCovering_Marginals
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
-- module Solutions.OAIQ16_CD.LatticeCovering_ProjectionBounds
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
-- module Solutions.OAIQ16_CD.LatticeCovering_Desmoothing
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
-- module Solutions.OAIQ16_CD.LatticeCovering_GaussianRates
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
-- module Solutions.OAIQ16_CD.LatticeCovering_GaussianPositions
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

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_LatticeAveraging
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7

namespace LatticeAveraging
open Set MeasureTheory
open scoped ENNReal BigOperators Pointwise
abbrev Space (n : ℕ) := EuclideanSpace ℝ (Fin n)

noncomputable def field {n : ℕ} {I : Type u_1} [Fintype I]
    (Λ : Submodule ℤ (Space n)) (p : I → Space n) (f : Space n → ℝ≥0∞) (y : Space n) : ℝ≥0∞ :=
  ∑ i,∑' l : Λ,f (y-p i-l.val)

noncomputable def uniformWindow {n : ℕ} (F : Set (Space n)) : Measure (Space n) :=
  (volume F)⁻¹ • volume.restrict F

end LatticeAveraging

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_LocalizationRounding
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal

namespace LocalizationRounding
open Set Finset
open scoped BigOperators
abbrev Space (n : ℕ) := EuclideanSpace ℝ (Fin n)
noncomputable def weight (n : ℕ) (a r : ℝ) : ℝ := 1+(n:ℝ)*max (1-r^2/a^2) 0

noncomputable def rounded {n : ℕ} (h : ℝ) (x : Space n) : Space n :=
  WithLp.toLp 2 (fun i => h*(round (x i/h):ℝ))

noncomputable def latticePoint {n : ℕ} (h : ℝ) (z : Fin n → ℤ) : Space n :=
  WithLp.toLp 2 (fun i => h*(z i:ℝ))
noncomputable def integerBox (n : ℕ) (m : ℤ) : Finset (Fin n → ℤ) :=
  Fintype.piFinset (fun _ => Finset.Icc (-m) m)
noncomputable def alphabet (n : ℕ) (h L : ℝ) : Finset (Space n) := by
  classical
  exact ((integerBox n ⌊L/h⌋).image (latticePoint h)).filter (fun x => ‖x‖ ≤ L)

abbrev BoundedLists (n : ℕ) (h L : ℝ) (N : ℕ) :=
  (m : Fin (N+1)) × (Fin m.val → {x // x ∈ alphabet n h L})

end LocalizationRounding

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_LocalizationGood
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal

universe u_1 u_2 u_3 u_4 u_5 u_6

namespace LocalizationGood
open Set MeasureTheory Metric LatticeAveraging
open scoped BigOperators ENNReal

noncomputable def countFn {n : ℕ} (B : Set (Space n)) : Space n → ℝ≥0∞ := B.indicator (fun _ => 1)
noncomputable def weightedFn {n : ℕ} (a β : ℝ) : Space n → ℝ≥0∞ :=
  (closedBall (0 : Space n) β).indicator (fun x => ENNReal.ofReal (LocalizationRounding.weight n a ‖x‖))

noncomputable def good {n : ℕ} {I : Type u_3} [Fintype I] (Λ : Submodule ℤ (Space n))
    (p : I → Space n) (a r β : ℝ) (C : ℝ≥0∞) : Set (Space n) :=
  {y | field Λ p (countFn (ball (0 : Space n) r)) y = 0 ∧
    field Λ p (countFn (closedBall (0 : Space n) β)) y ≤ C ∧ field Λ p (weightedFn a β) y ≤ C}

end LocalizationGood

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_SphericalLaw
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal

namespace SphericalLaw
open Set MeasureTheory Metric
open scoped ENNReal Pointwise
abbrev Space (n : ℕ) := EuclideanSpace ℝ (Fin n)
abbrev Sphere (n : ℕ) := sphere (0 : Space n) 1

noncomputable def σ (n : ℕ) : Measure (Sphere n) :=
  ((volume : Measure (Space n)).toSphere univ)⁻¹ • (volume : Measure (Space n)).toSphere

instance probability (n : ℕ) [NeZero n] : IsProbabilityMeasure (σ n) := by
  constructor
  rw [σ, Measure.smul_apply, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (fun h => Measure.toSphere_ne_zero (volume : Measure (Space n))
    (Measure.measure_univ_eq_zero.mp h)) (measure_ne_top _ _)

def cap {n : ℕ} (x : Space n) (t : ℝ) : Set (Sphere n) :=
  {u | t < |inner ℝ u.val x|}

end SphericalLaw

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_PoissonConfig
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9

namespace PoissonConfig

variable {Ω : Type u_1} [MeasurableSpace Ω]

abbrev Config (Ω : Type u_2) := Σ n : ℕ, {f : Fin n → Ω // Function.Injective f}

noncomputable def count (E : Set Ω) (x : Config Ω) : ℕ :=
  (Finset.univ.filter (fun i => x.2.val i ∈ E)).card

noncomputable def witnessCount {I : Type u_6} [Fintype I] (E : I → Set Ω)
    (x : Config Ω) : ℕ :=
  (Finset.univ.filter (fun f : I ↪ Fin x.1 => ∀ i, x.2.val (f i) ∈ E i)).card

noncomputable def occupied (E : Set Ω) (x : Config Ω) : Bool :=
  decide (0 < count E x)

structure HasVoidLaw (μ : Measure Ω) (P : Measure (Config Ω)) : Prop where
  void : ∀ E, MeasurableSet E → P {x | count E x = 0} =
    ENNReal.ofReal (Real.exp (-μ.real E))

end PoissonConfig

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_PoissonSample
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

universe u_1 u_2 u_3 u_4

namespace PoissonSample
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal NNReal

variable {Ω : Type u_1} [MeasurableSpace Ω]
abbrev RawConfig (Ω : Type u_2) := Σ n : ℕ, Fin n → Ω

noncomputable def sample (r : ℝ≥0) (σ : Measure Ω) : Measure (RawConfig Ω) :=
  Measure.sum fun n => poissonMeasure r {n} •
    (Measure.pi (fun _ : Fin n => σ)).map (Sigma.mk n)

def avoidance (E : Set Ω) : Set (RawConfig Ω) := {x | ∀ i, x.2 i ∉ E}

end PoissonSample

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_PoissonRealization
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

universe u_1

namespace PoissonSample
open Set MeasureTheory ProbabilityTheory
open scoped Classical ENNReal NNReal
variable {Ω : Type u_1} [MeasurableSpace Ω] [StandardBorelSpace Ω]

noncomputable def simplify (x : RawConfig Ω) : PoissonConfig.Config Ω :=
  if h : Function.Injective x.2 then ⟨x.1, ⟨x.2,h⟩⟩
  else ⟨0, ⟨Fin.elim0, fun i => Fin.elim0 i⟩⟩

noncomputable def simpleSample (r : ℝ≥0) (σ : Measure Ω) :
    Measure (PoissonConfig.Config Ω) := (sample r σ).map simplify

end PoissonSample

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_RandomBody
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

universe u_1 u_2 u_3

namespace RandomBody
open Set MeasureTheory Metric SphericalLaw
open scoped ENNReal NNReal

def body {n : ℕ} (b t : ℝ) (U : PoissonConfig.Config (Sphere n)) : Set (Space n) :=
  closedBall 0 b ∩ ⋂ i, {x | |inner ℝ (U.2.val i).val x| ≤ t}

end RandomBody

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_PatternGeometry
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7

namespace PatternGeometry
abbrev Space (n : ℕ) := SphericalLaw.Space n
open Set Metric MeasureTheory SphericalLaw PoissonConfig LocalizationRounding
open scoped BigOperators ENNReal Classical

noncomputable def relevant {n : ℕ} {I : Type u_1} [Fintype I] (p : I → Space n)
    (L : ℝ) (y : Space n) : Finset I := Finset.univ.filter (fun i => ‖y-p i‖ ≤ L)

noncomputable def roundedGood {n : ℕ} {I : Type u_2} [Fintype I] (p : I → Space n)
    (a D r L C : ℝ) : Set (Space n) :=
  {y | y ∈ closedBall 0 D ∧ (∀ i,r ≤ ‖y-p i‖) ∧
    ((relevant p L y).card:ℝ) ≤ C ∧
    ∑ i ∈ relevant p L y,weight n a ‖y-p i‖ ≤ C}

end PatternGeometry

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_PatternRounding
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

universe u_1 u_2 u_3

namespace PatternRounding
abbrev Space (n : ℕ) := SphericalLaw.Space n
open Set Metric MeasureTheory SphericalLaw LocalizationRounding PatternGeometry
open LatticeAveraging LocalizationGood
open scoped ENNReal BigOperators Classical

end PatternRounding

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_LocalizationComplete
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

universe u_1 u_2

namespace LocalizationComplete
open Set Metric MeasureTheory LatticeAveraging LocalizationGood
open PatternGeometry PatternRounding LocalizationRounding
open scoped ENNReal BigOperators Classical
abbrev Space (n : ℕ) := SphericalLaw.Space n

end LocalizationComplete

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_RadialIntegral
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

namespace RadialIntegral
open Set MeasureTheory Metric
open scoped ENNReal
abbrev Space (n : ℕ) := EuclideanSpace ℝ (Fin n)

end RadialIntegral

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_PatternEnumeration
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

universe u_1 u_2 u_3 u_4

namespace PatternEnumeration
open Set Metric MeasureTheory PatternGeometry LocalizationRounding
open scoped BigOperators ENNReal Classical

noncomputable def points {n N : ℕ} {h L : ℝ} (P : BoundedLists n h L N) : Fin P.1.val → PatternGeometry.Space n :=
  fun i => (P.2 i).val

abbrev Retained (n N : ℕ) (h L a D r b C : ℝ) :=
  {P : BoundedLists n h L N // volume (closedBall (0 : PatternGeometry.Space n) D) ≤
    4*volume (roundedGood (points P) a D r b C)}

noncomputable instance retainedFintype (n N : ℕ) (h L a D r b C : ℝ) :
    Fintype (Retained n N h L a D r b C) := Fintype.ofFinite _

end PatternEnumeration

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_RadialShell
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

namespace RadialShell
open Filter
open scoped Topology
noncomputable def η (n : ℕ) : ℝ := ((n:ℝ)⁻¹)^4
noncomputable def low (a : ℝ) (n : ℕ) : ℝ := a*(1-10*(Real.log n/(n:ℝ)))-3*η n
noncomputable def high (a : ℝ) (n : ℕ) : ℝ := a*(1+(n:ℝ)⁻¹)+3*η n

end RadialShell

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_SourceParameters
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

namespace SourceParameters
open Filter
open scoped Topology
noncomputable def ε : ℝ := 1/1073741824
noncomputable def a : ℝ := 1+ε
noncomputable def D : ℝ := 1/1024
noncomputable def v : ℝ := 1/64
noncomputable def b (n : ℕ) : ℝ := a*(1+(n:ℝ)⁻¹)
noncomputable def rminus (n : ℕ) : ℝ := a*(1-10*Real.log n/(n:ℝ))
noncomputable def h (n : ℕ) : ℝ := RadialShell.η n/(100*(n:ℝ))
noncomputable def L (n : ℕ) : ℝ := D+b n+5*RadialShell.η n
noncomputable def Cloc : ℝ := 1000/v
noncomputable def N (n : ℕ) (R : ℝ) : ℕ := ⌈20*R/v*(L n/a)^n⌉₊
end SourceParameters

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_LocalizationRates
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

namespace LocalizationRates
open Filter SourceParameters Metric MeasureTheory
open scoped Topology ENNReal
abbrev Space (n : ℕ) := EuclideanSpace ℝ (Fin n)
noncomputable def β (n : ℕ) : ℝ := b n+4*RadialShell.η n
noncomputable def W (n : ℕ) : ℝ := D+b n+4*RadialShell.η n
noncomputable def rround (n : ℕ) : ℝ := rminus n-2*RadialShell.η n
end LocalizationRates

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_LocalizationMeans
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

universe u_1 u_2

namespace LocalizationMeans
open Set MeasureTheory Metric SourceParameters LocalizationRates LatticeAveraging LocalizationGood
open scoped ENNReal
abbrev Space (n : ℕ) := EuclideanSpace ℝ (Fin n)
end LocalizationMeans

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_ConeStretch
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

namespace ConeStretch
open Set MeasureTheory Metric
open scoped ENNReal Pointwise
abbrev Space (n : ℕ) := EuclideanSpace ℝ (Fin n)

noncomputable def stretch {n : ℕ} (i : Fin n) (k : ℝ) : Space n →ₗ[ℝ] Space n :=
  Matrix.toEuclideanLin (Matrix.diagonal (fun j => if j = i then k else 1))

def cone {n : ℕ} (i : Fin n) (t R : ℝ) : Set (Space n) :=
  {x | 0 < ‖x‖ ∧ ‖x‖ < R ∧ t*‖x‖ < x i}

end ConeStretch

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_CapGeometry
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

namespace CapGeometry
open Set MeasureTheory Metric
open scoped ENNReal Pointwise
open SphericalLaw

def halfcap {n : ℕ} (x : Space n) (t : ℝ) : Set (Sphere n) :=
  {u | t < inner ℝ u.val x}

noncomputable def axis {n : ℕ} (i : Fin n) : Sphere n :=
  ⟨EuclideanSpace.basisFun (Fin n) ℝ i, by simp⟩

noncomputable def radial (t s : ℝ) : ℝ := Real.sqrt ((1-t^2)/(1-s^2))
noncomputable def axial (t s : ℝ) : ℝ := (s/t)*radial t s

end CapGeometry

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_CapLens
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

universe u_1

namespace CapLens
open Set MeasureTheory Metric SphericalLaw CapGeometry
open scoped ENNReal Pointwise

noncomputable def unit {n : ℕ} (x : Space n) (hx : x ≠ 0) : Sphere n :=
  ⟨‖x‖⁻¹ • x, by rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr (norm_pos_iff.mpr hx)), inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]⟩

end CapLens

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_ProjectiveCaps
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

universe u_1 u_2 u_3 u_4 u_5 u_6

namespace ProjectiveCaps
open InnerProductGeometry Real
variable {V : Type u_1} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

noncomputable def angle (x y : V) : ℝ :=
  min (InnerProductGeometry.angle x y) (InnerProductGeometry.angle x (-y))

noncomputable def costDist {I : Type u_2} (n : ℕ) (x : I → V) (s : I → ℝ) (i j : I) : ℝ :=
  Real.sqrt n * angle (x i) (x j) + Real.sqrt |s i-s j|

end ProjectiveCaps

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_CapAffinity
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

namespace CapAffinity
open Set MeasureTheory Metric SphericalLaw CapGeometry

noncomputable def signed {n : ℕ} (e : Sphere n) (b : Bool) : Sphere n :=
  if b then e else ⟨-e.val, by simpa only [mem_sphere_zero_iff_norm, norm_neg]
    using mem_sphere_zero_iff_norm.mp e.property⟩

end CapAffinity

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_CapCost
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

namespace CapCost
open MeasureTheory SphericalLaw CapGeometry CapAffinity
open scoped ENNReal NNReal

noncomputable def rate {n : ℕ} (e : Sphere n) (t : ℝ) : ℝ≥0 :=
  ⟨((σ n).real (cap e.val t))⁻¹, inv_nonneg.mpr measureReal_nonneg⟩
noncomputable def intensity {n : ℕ} (e : Sphere n) (t : ℝ) : Measure (Sphere n) :=
  rate e t • σ n

instance intensity_finite {n : ℕ} [NeZero n] (e : Sphere n) (t : ℝ) :
    IsFiniteMeasure (intensity e t) := inferInstanceAs (IsFiniteMeasure (rate e t • σ n))

end CapCost

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_BlockGeometry
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

universe u_1

namespace BlockGeometry
open Finset
variable {I : Type u_1}
noncomputable def radius (d : I → I → ℝ) (S : Finset I) : ℝ :=
  if h : S.Nonempty then S.inf' h (fun j => S.sup' h (fun i => d j i ^ 2)) else 0

noncomputable def loss (L : ℝ) (d : I → I → ℝ) (S : Finset I) : ℝ :=
  if S.card ≤ 1 then 0 else L*(1+radius d S+Real.log S.card)

end BlockGeometry

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_BlockSets
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology

universe u_1 u_2

namespace BlockSets
open MeasureTheory Finset BlockGeometry
open scoped BigOperators
variable {Ω : Type u_1} {I : Type u_2} [MeasurableSpace Ω]

noncomputable def clipped (μ : Measure Ω) (C : I → Set Ω) (i : I) : ℝ :=
  min (μ.real (C i)) (1/2)
noncomputable def cost (μ : Measure Ω) (C : I → Set Ω) (i : I) : ℝ :=
  -Real.log (clipped μ C i)

def common (C : I → Set Ω) (S : Finset I) : Set Ω := ⋂ i ∈ S, C i

end BlockSets

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_Blocks
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology

universe u_1 u_2

namespace Blocks
universe u₁ u₂
open Finset MeasureTheory BlockGeometry BlockSets
open scoped BigOperators
variable {Ω : Type u_1} {I : Type u_2} [MeasurableSpace Ω]

noncomputable def weight (μ : Measure Ω) (E F : Set Ω) : ℝ :=
  μ.real (E ∩ F)/Real.sqrt (μ.real E*(1+μ.real E)*μ.real F*(1+μ.real F))

end Blocks

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_CellMatching
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators

universe u_1 u_2 u_3 u_4 u_5 u_6

namespace CellMatching

variable {I : Type u_1} {J : Type u_2} {C : Type u_3} [Fintype I] [Fintype J]

def IsMatching (M : Finset (I × J)) : Prop :=
  (∀ i j k, (i,j) ∈ M → (i,k) ∈ M → j = k) ∧
  (∀ i j k, (i,k) ∈ M → (j,k) ∈ M → i = j)

abbrev Matching (I : Type u_4) (J : Type u_5) [Fintype I] [Fintype J] :=
  {M : Finset (I × J) // IsMatching M}

abbrev Classes (M : Matching I J) := I ⊕ {j : J // ∀ i, (i,j) ∉ M.val}

noncomputable def rightClass (M : Matching I J) (j : J) : Classes M :=
  if h : ∃ i, (i,j) ∈ M.val then Sum.inl h.choose
  else Sum.inr ⟨j, by simpa only [not_exists] using h⟩

lemma rightClass_of_edge (M : Matching I J) {i : I} {j : J}
    (hij : (i,j) ∈ M.val) : rightClass M j = Sum.inl i := by
  have h : ∃ i, (i,j) ∈ M.val := ⟨i, hij⟩
  rw [rightClass, dite_eq_left h]
  congr 1
  exact M.property.2 _ _ _ h.choose_spec hij

lemma rightClass_unmatched (M : Matching I J) (j : J)
    (hj : ∀ i, (i,j) ∉ M.val) : rightClass M j = Sum.inr ⟨j,hj⟩ := by
  have h : ¬ ∃ i, (i,j) ∈ M.val := by simpa only [not_exists] using hj
  simp only [rightClass, dite_eq_right h]

lemma inl_eq_rightClass (M : Matching I J) (i : I) (j : J) :
    Sum.inl i = rightClass M j ↔ (i,j) ∈ M.val := by
  constructor
  · intro h
    unfold rightClass at h
    split_ifs at h with hj
    · have hi := Sum.inl.inj h
      simpa only [hi] using hj.choose_spec
  · intro h
    exact (rightClass_of_edge M h).symm

lemma rightClass_injective (M : Matching I J) : Function.Injective (rightClass M) := by
  intro j k h
  by_cases hj : ∃ i, (i,j) ∈ M.val
  · obtain ⟨i, hi⟩ := hj
    have hk : (i,k) ∈ M.val := (inl_eq_rightClass M i k).mp
      ((rightClass_of_edge M hi).symm.trans h)
    exact M.property.1 _ _ _ hi hk
  · have hj' : ∀ i, (i,j) ∉ M.val := by simpa only [not_exists] using hj
    rw [rightClass_unmatched M j hj'] at h
    unfold rightClass at h
    split_ifs at h with hk
    · exact congrArg Subtype.val (Sum.inr.inj h)

noncomputable def exactMatching (f : I ↪ C) (g : J ↪ C) : Matching I J :=
  ⟨Finset.univ.filter (fun ij => f ij.1 = g ij.2), by
    constructor
    · intro i j k hj hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj hk
      exact g.injective (hj.symm.trans hk)
    · intro i j k hi hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
      exact f.injective (hi.trans hj.symm)⟩

@[simp] lemma mem_exactMatching (f : I ↪ C) (g : J ↪ C) (i : I) (j : J) :
    (i,j) ∈ (exactMatching f g).val ↔ f i = g j := by
  simp only [exactMatching, Finset.mem_filter, Finset.mem_univ, true_and]

abbrev ExactPair (M : Matching I J) (C : Type u_6) :=
  {fg : (I ↪ C) × (J ↪ C) // ∀ i j, fg.1 i = fg.2 j ↔ (i,j) ∈ M.val}

noncomputable def expand (M : Matching I J) (q : Classes M ↪ C) : ExactPair M C :=
  ⟨(⟨fun i => q (Sum.inl i), q.injective.comp Sum.inl_injective⟩,
    ⟨fun j => q (rightClass M j), q.injective.comp (rightClass_injective M)⟩), by
    intro i j
    exact q.injective.eq_iff.trans (inl_eq_rightClass M i j)⟩

noncomputable def collapse (M : Matching I J) (fg : ExactPair M C) : Classes M ↪ C :=
  ⟨Sum.elim fg.val.1 (fun j => fg.val.2 j.val), by
    rintro (i | j) (i' | j') h
    · exact congrArg Sum.inl (fg.val.1.injective h)
    · exact False.elim (j'.property i ((fg.property i j').mp h))
    · exact False.elim (j.property i' ((fg.property i' j).mp h.symm))
    · exact congrArg Sum.inr (Subtype.ext (fg.val.2.injective h))⟩

lemma collapse_right (M : Matching I J) (fg : ExactPair M C) (j : J) :
    collapse M fg (rightClass M j) = fg.val.2 j := by
  unfold rightClass
  split_ifs with h
  · exact (fg.property h.choose j).mpr h.choose_spec
  · rfl

noncomputable def diagramEquiv (M : Matching I J) :
    (Classes M ↪ C) ≃ ExactPair M C where
  toFun := expand M
  invFun := collapse M
  left_inv q := by
    ext (i | j)
    · rfl
    · change q (rightClass M j) = q (Sum.inr j)
      rw [rightClass_unmatched M j j.property]
  right_inv fg := by
    apply Subtype.ext
    apply Prod.ext
    · ext i
      rfl
    · ext j
      exact collapse_right M fg j

def classIncidence (M : Matching I J) (A : I → C → Prop) (B : J → C → Prop) :
    Classes M → C → Prop :=
  Sum.elim (fun i c => A i c ∧ ∀ j, (i,j) ∈ M.val → B j c)
    (fun j c => B j.val c)

variable [Fintype C]

noncomputable def support (f : I ↪ C) : Finset C := Finset.univ.image f

noncomputable def jointWeight (p : C → ℝ) (f : I ↪ C) (g : J ↪ C) : ℝ :=
  ∏ c ∈ support f ∪ support g, p c

noncomputable def pairWeight (A : I → C → Prop) (B : J → C → Prop) (p : C → ℝ)
    (fg : (I ↪ C) × (J ↪ C)) : ℝ :=
  if (∀ i, A i (fg.1 i)) ∧ (∀ j, B j (fg.2 j)) then jointWeight p fg.1 fg.2 else 0

noncomputable def allDiagramsEquiv :
    ((I ↪ C) × (J ↪ C)) ≃ Σ M : Matching I J, ExactPair M C where
  toFun fg := ⟨exactMatching fg.1 fg.2, ⟨fg, fun i j => (mem_exactMatching _ _ i j).symm⟩⟩
  invFun mq := mq.2.val
  left_inv fg := rfl
  right_inv mq := by
    rcases mq with ⟨M, fg, hfg⟩
    have hM : exactMatching fg.1 fg.2 = M := by
      apply Subtype.ext
      ext ij
      exact (mem_exactMatching _ _ ij.1 ij.2).trans (hfg ij.1 ij.2)
    cases hM
    rfl

end CellMatching

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_MatchingAlgebra
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators

universe u_1 u_2

namespace MatchingAlgebra
variable {I : Type u_1} {J : Type u_2} [Fintype I] [Fintype J]

noncomputable def leftWeight (M : Finset (I × J)) (a : I → ℝ) (w : I → J → ℝ) (i : I) : ℝ :=
  if h : ∃ j, (i,j) ∈ M then w i h.choose else a i

end MatchingAlgebra

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_CellCounts
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical

universe u_1 u_2 u_3 u_4

namespace CellCounts

variable {I : Type u_1} {C : Type u_2} [Fintype I] [Fintype C]

noncomputable def assignmentWeight (w : I → C → ℝ) (f : I → C) : ℝ :=
  ∏ i, w i (f i)

noncomputable def injectiveSum (w : I → C → ℝ) : ℝ :=
  ∑ f : I → C, if Function.Injective f then assignmentWeight w f else 0

noncomputable def collisionSum (w : I → C → ℝ) (i j : I) : ℝ :=
  ∑ f : I → C, if f i = f j then assignmentWeight w f else 0

noncomputable def force (w : I → C → ℝ) (i j : I) (c : C) (v : I) (d : C) : ℝ :=
  if v = i ∨ v = j then if d = c then w v d else 0 else w v d

noncomputable def pairs (I : Type u_3) [Fintype I] [LinearOrder I] : Finset (I × I) :=
  Finset.univ.filter (fun ij => ij.1 < ij.2)

noncomputable def slotWeight (A : I → C → Prop) (q : C → ℝ) (i : I) (c : C) : ℝ :=
  if A i c then q c else 0

end CellCounts

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_PoissonMeasureCells
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical

universe u_1 u_2 u_3 u_4 u_5

namespace PoissonMeasureCells

open Set MeasureTheory
open scoped ENNReal

variable {Ω : Type u_1} {C : Type u_2} {I : Type u_3} [MeasurableSpace Ω] [Fintype C] [Fintype I]

structure Partition (Ω : Type u_4) (C : Type u_5) [MeasurableSpace Ω] [Fintype C] where
  cell : C → Set Ω
  measurable : ∀ c, MeasurableSet (cell c)
  disjoint : Pairwise (fun c d => Disjoint (cell c) (cell d))
  cover : (⋃ c, cell c) = univ

omit [Fintype I] in
 def Respects (P : Partition Ω C) (F : Set Ω) : Prop :=
  ∀ c, P.cell c ⊆ F ∨ Disjoint (P.cell c) F

noncomputable def Q (μ : Measure Ω) (P : Partition Ω C) (F : I → Set Ω) : ℝ :=
  CellCounts.injectiveSum (CellCounts.slotWeight (fun i c => P.cell c ⊆ F i)
    (fun c => 1 - Real.exp (- μ.real (P.cell c))))

end PoissonMeasureCells

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_PoissonDiagrams
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7

namespace PoissonDiagrams
open Set MeasureTheory CellMatching PoissonMeasureCells
open scoped Classical BigOperators
variable {Ω : Type u_1} {I : Type u_2} {J : Type u_3} {C : Type u_4} [MeasurableSpace Ω] [Fintype I] [Fintype J] [Fintype C]

omit [Fintype C] in

def classSet (M : Matching I J) (E : I → Set Ω) (F : J → Set Ω) : Classes M → Set Ω :=
  Sum.elim (fun i => {x | x ∈ E i ∧ ∀ j, (i,j) ∈ M.val → x ∈ F j}) (fun j => F j.val)

omit [Fintype C] in

noncomputable def diagram (μ : Measure Ω) (E : I → Set Ω) (F : J → Set Ω) : ℝ :=
  (∏ i, μ.real (E i)) * (∏ j, μ.real (F j)) *
    ∑ M : Matching I J, if M.val.Nonempty then
      ∏ ij ∈ M.val, μ.real (E ij.1 ∩ F ij.2) / (μ.real (E ij.1) * μ.real (F ij.2))
      else 0

end PoissonDiagrams

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_MatchingBounds
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical

universe u_1 u_2

namespace MatchingBounds
open CellMatching
open scoped Classical BigOperators
variable {I : Type u_1} {J : Type u_2} [Fintype I] [Fintype J]

noncomputable def emptyMatching : Matching I J := ⟨∅, by simp [IsMatching]⟩

end MatchingBounds

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_MatchingSelf
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical

universe u_1 u_2

namespace MatchingSelf
open CellMatching
open scoped Classical BigOperators
variable {I : Type u_1} [Fintype I]

abbrev OffMatching (I : Type u_2) [Fintype I] :=
  {M : Matching I I // ∀ e ∈ M.val, e.1 ≠ e.2}

noncomputable def off (M : Matching I I) : OffMatching I :=
  ⟨⟨M.val.filter (fun e => e.1 ≠ e.2), by
    constructor
    · intro i j k h hj; exact M.property.1 i j k
        (Finset.mem_filter.mp h).1 (Finset.mem_filter.mp hj).1
    · intro i j k h hj; exact M.property.2 i j k
        (Finset.mem_filter.mp h).1 (Finset.mem_filter.mp hj).1⟩,
    by intro e he; exact (Finset.mem_filter.mp he).2⟩

noncomputable def available (P : OffMatching I) : Finset I :=
  Finset.univ.filter (fun i => (∀ j, (i,j) ∉ P.val.val) ∧ (∀ j, (j,i) ∉ P.val.val))

abbrev Loops (P : OffMatching I) := {L : Finset I // L ⊆ available P}

noncomputable def loops (M : Matching I I) : Loops (off M) :=
  ⟨Finset.univ.filter (fun i => (i,i) ∈ M.val), by
    intro i hi
    have h := (Finset.mem_filter.mp hi).2
    simp only [available, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro j hj
      have hh := (Finset.mem_filter.mp hj)
      exact hh.2 (M.property.1 i j i hh.1 h).symm
    · intro j hj
      have hh := (Finset.mem_filter.mp hj)
      exact hh.2 (M.property.2 j i i hh.1 h)⟩

noncomputable def join (P : OffMatching I) (L : Loops P) : Matching I I :=
  ⟨P.val.val ∪ L.val.diag, by
    constructor
    · intro i j k hij hik
      rcases Finset.mem_union.mp hij with hp | hl
      · rcases Finset.mem_union.mp hik with hq | hm
        · exact P.val.property.1 _ _ _ hp hq
        · have hd := Finset.mem_diag.mp hm
          dsimp only [Prod.fst, Prod.snd] at hd
          obtain ⟨hi, rfl⟩ := hd
          exact False.elim ((Finset.mem_filter.mp (L.property hi)).2.1 j hp)
      · have hd := Finset.mem_diag.mp hl
        dsimp only [Prod.fst, Prod.snd] at hd
        obtain ⟨hi, rfl⟩ := hd
        rcases Finset.mem_union.mp hik with hq | hm
        · exact False.elim ((Finset.mem_filter.mp (L.property hi)).2.1 k hq)
        · exact (Finset.mem_diag.mp hm).2
    · intro i j k hik hjk
      rcases Finset.mem_union.mp hik with hp | hl
      · rcases Finset.mem_union.mp hjk with hq | hm
        · exact P.val.property.2 _ _ _ hp hq
        · have hd := Finset.mem_diag.mp hm
          dsimp only [Prod.fst, Prod.snd] at hd
          obtain ⟨hi, rfl⟩ := hd
          exact False.elim ((Finset.mem_filter.mp (L.property hi)).2.2 i hp)
      · have hd := Finset.mem_diag.mp hl
        dsimp only [Prod.fst, Prod.snd] at hd
        obtain ⟨hi, rfl⟩ := hd
        rcases Finset.mem_union.mp hjk with hq | hm
        · exact False.elim ((Finset.mem_filter.mp (L.property hi)).2.2 j hq)
        · exact (Finset.mem_diag.mp hm).2.symm⟩

lemma join_off_loops (M : Matching I I) : join (off M) (loops M) = M := by
  apply Subtype.ext
  ext ⟨i,j⟩
  simp only [join, off, loops, Finset.mem_union, Finset.mem_filter,
    Finset.mem_diag, Finset.mem_univ, true_and]
  constructor
  · rintro (⟨h,_⟩ | ⟨h,rfl⟩) <;> exact h
  · intro h
    by_cases hij : i = j
    · subst j; exact Or.inr ⟨h,rfl⟩
    · exact Or.inl ⟨h,hij⟩

lemma off_join (P : OffMatching I) (L : Loops P) : off (join P L) = P := by
  apply Subtype.ext
  apply Subtype.ext
  ext ⟨i,j⟩
  simp only [off, join, Finset.mem_filter, Finset.mem_union, Finset.mem_diag]
  constructor
  · rintro ⟨h, hne⟩
    rcases h with h | ⟨_, he⟩
    · exact h
    · exact False.elim (hne he)
  · intro h; exact ⟨Or.inl h, P.property _ h⟩

lemma loops_join_val (P : OffMatching I) (L : Loops P) :
    (loops (join P L)).val = L.val := by
  ext i
  simp only [loops, join, Finset.mem_filter, Finset.mem_univ,
    Finset.mem_union, Finset.mem_diag, and_true, true_and]
  exact or_iff_right (fun h => P.property (i,i) h rfl)

noncomputable def splitEquiv : Matching I I ≃ (Σ P : OffMatching I, Loops P) where
  toFun M := ⟨off M, loops M⟩
  invFun x := join x.1 x.2
  left_inv := join_off_loops
  right_inv := by
    intro ⟨P,L⟩
    apply Sigma.ext (off_join P L)
    apply (Subtype.heq_iff_coe_eq (by intro x; dsimp only; rw [off_join])).mpr
    exact loops_join_val P L

noncomputable def leftChoice (P : OffMatching I) (i : I) : Option I :=
  if h : ∃ j, (i,j) ∈ P.val.val then some h.choose else none

noncomputable def rowWeight (w : I × I → ℝ) (i : I) : Option I → ℝ
  | none => 1
  | some j => if i ≠ j then w (i,j) else 0

end MatchingSelf

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_RadialCost
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical

namespace RadialCost
noncomputable def weight (n : ℕ) (a r : ℝ) : ℝ := 1+(n:ℝ)*max (1-r^2/a^2) 0

end RadialCost

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_ShellCaps
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical

namespace ShellCaps
open Set MeasureTheory SphericalLaw CapCost
open scoped BigOperators
noncomputable def A (l u : ℝ) : ℝ := 1/l+1/(1-u^2)
noncomputable def C (a l u : ℝ) : ℝ := Real.log 2+8*A l u/a

end ShellCaps

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_ResidualCaps
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

namespace ResidualCaps
open Set Metric SphericalLaw

noncomputable def unit {n : ℕ} (x : Space n) (hx : x ≠ 0) : Sphere n :=
  ⟨‖x‖⁻¹ • x,by simp [norm_smul,(norm_pos_iff.mpr hx).ne']⟩

end ResidualCaps

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_CylinderVolume
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

namespace CylinderVolume
open Set MeasureTheory Metric Finset ConeStretch
open scoped ENNReal
noncomputable def scale {n : ℕ} (i : Fin n) (a b : ℝ) : Space n →ₗ[ℝ] Space n :=
  Matrix.toEuclideanLin (Matrix.diagonal (fun j => if j = i then a else b))

def cylinder {n : ℕ} (i : Fin n) (D r : ℝ) : Set (Space n) :=
  {x | |x i| ≤ D ∧ ‖x‖^2-(x i)^2 ≤ r^2}

end CylinderVolume

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_CylinderProbability
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

namespace CylinderProbability
open Set MeasureTheory Metric ConeStretch
open scoped ENNReal

noncomputable def uniform {n : ℕ} (G : Set (Space n)) : Measure (Space n) :=
  (volume G)⁻¹ • volume.restrict G

def pairEvent {n : ℕ} (p q : Space n) (L ξ : ℝ) : Set (Space n × Space n) :=
  {z | z.1-p ≠ 0 ∧ ‖z.1-p‖ ≤ L ∧ z.2-q ≠ 0 ∧ ‖z.2-q‖ ≤ L ∧
     ProjectiveCaps.angle (z.1-p) (z.2-q) ≤ ξ}

end CylinderProbability

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_PatternWitness
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

universe u_1 u_2 u_3

namespace PatternWitness
abbrev Space (n : ℕ) := SphericalLaw.Space n
open Set Metric MeasureTheory SphericalLaw PatternGeometry ResidualCaps PoissonDiagrams CapCost
open scoped BigOperators Classical

structure Certificate {n : ℕ} {J : Type u_1} [Fintype J] (e : Sphere n)
    (p : J → Space n) (y : Space n) (a K A C : ℝ) where
  P : Finpartition (Finset.univ : Finset (relevant p (RadialShell.high a n) y))
  nonempty : P.parts.Nonempty
  card_le : P.parts.card ≤ n^2
  anchor : P.parts → relevant p (RadialShell.high a n) y
  slot : P.parts → Set (Sphere n)
  measurable_slot : ∀ S,MeasurableSet (slot S)
  subset_cap : ∀ S,slot S ⊆ cap (y-p (anchor S)) (1+3*RadialShell.η n)
  thinned : ∀ S,Real.exp (-K*Real.log n)*min
    ((intensity e (1/a)).real (cap (y-p (anchor S)) (1+3*RadialShell.η n))) (1/2) ≤
      (intensity e (1/a)).real (slot S)
  positive : ∀ S,0 < (intensity e (1/a)).real (slot S)
  lower : Real.exp (-A*C) ≤ ∏ S,(intensity e (1/a)).real (slot S)
  upper : (∏ S,(intensity e (1/a)).real (slot S)) ≤ 1
  self : diagram (intensity e (1/a)) slot slot ≤
    (∏ S,(intensity e (1/a)).real (slot S))^2*Real.exp (2*A*C)
  hole : ∀ U : PoissonConfig.Config (Sphere n),0 < PoissonConfig.witnessCount slot U →
    ∀ j,y-p j ∉ RandomBody.body (RadialShell.high a n) (1+3*RadialShell.η n) U

end PatternWitness

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_PatternCross
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical

universe u_1 u_2 u_3

namespace PatternCross
abbrev Space (n : ℕ) := SphericalLaw.Space n
open Set MeasureTheory SphericalLaw CapCost PatternGeometry PatternWitness ResidualCaps PoissonDiagrams
open scoped BigOperators

noncomputable def activity {n : ℕ} {J : Type u_1} [Fintype J] {e : Sphere n}
    {p : J → Space n} {x : Space n} {a K A C : ℝ} (W : Certificate e p x a K A C) : ℝ :=
  ∏ S,(intensity e (1/a)).real (W.slot S)

end PatternCross

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_FiniteJanson
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11

namespace FiniteJanson

variable {V : Type u_1} [Fintype V]

noncomputable def atom (p : V → ℝ) (x : V → Bool) : ℝ :=
  ∏ v, if x v then p v else 1 - p v

noncomputable def prob (p : V → ℝ) (A : Set (V → Bool)) : ℝ :=
  ∑ x, if x ∈ A then atom p x else 0

variable {p : V → ℝ}

@[simp] theorem prob_empty (p : V → ℝ) : prob p ∅ = 0 := by
  simp [prob]

noncomputable def ind (A : Set (V → Bool)) (x : V → Bool) : ℝ :=
  if x ∈ A then 1 else 0

def Supported (S : Set V) (A : Set (V → Bool)) : Prop :=
  ∀ x y, (∀ v ∈ S, x v = y v) → (x ∈ A ↔ y ∈ A)

def occurs (H : Finset V) : Set (V → Bool) := {x | ∀ v ∈ H, x v = true}

omit [Fintype V] in
@[simp] theorem occurs_union (H K : Finset V) : occurs (H ∪ K) = occurs H ∩ occurs K := by
  ext x
  simp [occurs, or_imp, forall_and]

def avoids {ι : Type u_2} (H : ι → Finset V) (s : Finset ι) : Set (V → Bool) :=
  {x | ∀ i ∈ s, x ∉ occurs (H i)}

omit [Fintype V] in
@[simp] theorem avoids_empty {ι : Type u_3} (H : ι → Finset V) : avoids H ∅ = Set.univ := by
  ext x
  simp [avoids]

omit [Fintype V] in
@[simp] theorem avoids_insert {ι : Type u_4} (H : ι → Finset V) (s : Finset ι) (i : ι) :
    avoids H (insert i s) = avoids H s ∩ (occurs (H i))ᶜ := by
  ext x
  simp [avoids, and_comm]

variable {ι : Type u_10}

noncomputable def mean (p : V → ℝ) (H : ι → Finset V) (s : Finset ι) : ℝ :=
  ∑ i ∈ s, prob p (occurs (H i))

noncomputable def offCost (p : V → ℝ) (H : ι → Finset V) (i j : ι) : ℝ :=
  if i = j ∨ Disjoint (H i) (H j) then 0 else prob p (occurs (H i) ∩ occurs (H j))

noncomputable def offSum (p : V → ℝ) (H : ι → Finset V) (s : Finset ι) : ℝ :=
  ∑ i ∈ s, ∑ j ∈ s, offCost p H i j

@[simp] theorem offCost_self (p : V → ℝ) (H : ι → Finset V) (i : ι) :
    offCost p H i i = 0 := by simp [offCost]

@[simp] theorem mean_insert (p : V → ℝ) (H : ι → Finset V) (s : Finset ι)
    (a : ι) (ha : a ∉ s) : mean p H (insert a s) = prob p (occurs (H a)) + mean p H s := by
  exact Finset.sum_insert ha

@[simp] theorem prob_singleton (p : V → ℝ) (x : V → Bool) :
    prob p {x} = atom p x := by
  simp [prob]

variable {W : Type u_11} [Fintype W]

noncomputable def gated (H : ι → Finset V) (i : ι) : Finset (V ⊕ ι) :=
  (H i).map Function.Embedding.inl ∪ {Sum.inr i}

omit [Fintype V] in
@[simp] theorem occurs_gated (H : ι → Finset V) (i : ι) (x : V ⊕ ι → Bool) :
    x ∈ occurs (gated H i) ↔ x ∘ Sum.inl ∈ occurs (H i) ∧ x (Sum.inr i) = true := by
  simp [gated, occurs, Function.comp_def, or_imp, forall_and, and_comm]

noncomputable def depSum (p : V → ℝ) (H : ι → Finset V) (s : Finset ι) : ℝ :=
  ∑ i ∈ s, ∑ j ∈ s,
    if Disjoint (H i) (H j) then 0 else prob p (occurs (H i) ∩ occurs (H j))

end FiniteJanson

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_JansonSampling
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open MeasureTheory ProbabilityTheory Set

universe u_1 u_2 u_3

namespace FiniteJanson

variable {Ω : Type u_1} {V : Type u_2} [MeasurableSpace Ω] [Fintype V]
  {P : Measure Ω} [IsProbabilityMeasure P] {X : V → Ω → Bool}

noncomputable def successProb (P : Measure Ω) (X : V → Ω → Bool) (v : V) : ℝ :=
  P.real {ω | X v ω = true}

end FiniteJanson

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_PoissonFinite
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open MeasureTheory ProbabilityTheory Set
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical

universe u_1 u_2 u_3 u_4 u_5 u_6

namespace PoissonFinite
open Set MeasureTheory ProbabilityTheory PoissonConfig PoissonMeasureCells CellMatching PoissonDiagrams
open scoped Classical BigOperators
variable {Ω : Type u_1} {A : Type u_2} {C : Type u_3} [MeasurableSpace Ω] [Fintype A] [Fintype C]
variable {I : A → Type u_4} [∀ a, Fintype (I a)]

abbrev Assignment (I : A → Type u_5) (C : Type u_6) := Σ a, I a ↪ C

noncomputable def valid (P : Partition Ω C) (E : ∀ a, I a → Set Ω)
    (f : Assignment I C) : Prop := ∀ i, P.cell (f.2 i) ⊆ E f.1 i

noncomputable def validAssignments (P : Partition Ω C) (E : ∀ a, I a → Set Ω) :
    Finset (Assignment I C) := Finset.univ.filter (valid P E)

noncomputable def assignmentSupport (f : Assignment I C) : Finset C := support f.2

end PoissonFinite

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_PoissonCells
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open MeasureTheory ProbabilityTheory Set
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set MeasureTheory
open scoped ENNReal Classical

universe u_1 u_2

namespace PoissonCells

variable {Ω : Type u_1} {J : Type u_2} [MeasurableSpace Ω] [Fintype J]

noncomputable def atom (E : J → Set Ω) (b : J → Bool) : Set Ω :=
  {x | ∀ j, decide (x ∈ E j) = b j}

end PoissonCells

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_ActivityBins
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open MeasureTheory ProbabilityTheory Set
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set MeasureTheory
open scoped ENNReal Classical

universe u_1

namespace ActivityBins
open Finset
open scoped BigOperators
noncomputable def count (B : ℝ) : ℕ := ⌊B/Real.log 2⌋₊+1

end ActivityBins

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_BodyVolume
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open MeasureTheory ProbabilityTheory Set
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set MeasureTheory
open scoped ENNReal Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

universe u_1

namespace BodyVolume
open Set MeasureTheory Metric SphericalLaw RandomBody CapCost
open scoped ENNReal NNReal

noncomputable def law {n : ℕ} (e : Sphere n) (a : ℝ) :
    Measure (PoissonConfig.Config (Sphere n)) :=
  PoissonSample.simpleSample (rate e (1/a)) (σ n)

end BodyVolume

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_PatternTail
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open MeasureTheory ProbabilityTheory Set
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set MeasureTheory
open scoped ENNReal Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

universe u_1 u_2 u_3

namespace PatternTail
open Set Metric MeasureTheory SphericalLaw CapCost PatternGeometry PatternWitness PoissonDiagrams
open scoped BigOperators ENNReal Classical
abbrev Space (n : ℕ) := SphericalLaw.Space n

noncomputable def coverEvent {n : ℕ} {J : Type u_1} [Fintype J] (p : J → Space n)
    (a D : ℝ) : Set (PoissonConfig.Config (Sphere n)) :=
  {U | ∀ y ∈ closedBall (0 : Space n) D, ∃ i,y-p i ∈
    RandomBody.body (RadialShell.high a n) (1+3*RadialShell.η n) U}

end PatternTail

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_SourceLocalization
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open MeasureTheory ProbabilityTheory Set
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set MeasureTheory
open scoped ENNReal Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

universe u_1 u_2

namespace SourceLocalization
open Set Metric MeasureTheory SourceParameters LocalizationRates LocalizationRounding PatternGeometry PatternEnumeration
open scoped ENNReal Classical
abbrev Patterns (n : ℕ) (R : ℝ) := Retained n (N n R) (h n) (L n) a D (rround n) (RadialShell.high a n) (2*Cloc*R)
end SourceLocalization

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_BodySelection
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open MeasureTheory ProbabilityTheory Set
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set MeasureTheory
open scoped ENNReal Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open MeasureTheory ProbabilityTheory Set
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set MeasureTheory
open scoped ENNReal Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

namespace BodySelection
open Set Metric MeasureTheory Filter SourceParameters LocalizationRates PatternEnumeration SourceLocalization SphericalLaw
open scoped ENNReal Topology Classical
abbrev Space (n : ℕ) := EuclideanSpace ℝ (Fin n)
noncomputable def bad {n : ℕ} (R : ℝ) : Set (PoissonConfig.Config (Sphere n)) :=
  ⋃ P : Patterns n R,PatternTail.coverEvent (points P.val) a D
end BodySelection

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_AllLatticeExclusion
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open MeasureTheory ProbabilityTheory Set
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set MeasureTheory
open scoped ENNReal Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open MeasureTheory ProbabilityTheory Set
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set MeasureTheory
open scoped ENNReal Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal

universe u_1 u_2

namespace AllLatticeExclusion
open Set Metric MeasureTheory SourceParameters LocalizationRates PatternEnumeration SourceLocalization
open scoped ENNReal Classical
abbrev Space (n : ℕ) := EuclideanSpace ℝ (Fin n)
end AllLatticeExclusion

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_Periodization
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open MeasureTheory ProbabilityTheory Set
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set MeasureTheory
open scoped ENNReal Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open MeasureTheory ProbabilityTheory Set
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set MeasureTheory
open scoped ENNReal Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal

namespace TranslativeCovering

open scoped Classical Topology

def cubePeriod {n : ℕ} (L : ℝ) (z : Fin n → ℤ) : Space n :=
  WithLp.toLp 2 (fun i => 2 * L * (z i : ℝ))

def repeatCube {n : ℕ} (L : ℝ) (S : Set (Space n)) : Set (Space n) :=
  {x | ∃ s ∈ S, ∃ z : Fin n → ℤ, x = s + cubePeriod L z}

structure CubicCover {n : ℕ} (K : Set (Space n)) where
  L : ℝ
  positive : 0 < L
  centers : Finset (Space n)
  covers : Covers K (repeatCube L (centers : Set (Space n)))

end TranslativeCovering

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_CubicLattice
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open MeasureTheory ProbabilityTheory Set
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set MeasureTheory
open scoped ENNReal Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open MeasureTheory ProbabilityTheory Set
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set MeasureTheory
open scoped ENNReal Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal

namespace CubicLattice
open Module Set MeasureTheory TranslativeCovering
open scoped ENNReal BigOperators Classical
noncomputable def basis (n : ℕ) (L : ℝ) (hL : 0<L) : Basis (Fin n) ℝ (Space n) :=
  (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.isUnitSMul (fun _ => isUnit_iff_ne_zero.mpr (by positivity : (2*L:ℝ)≠0))
lemma basis_apply {n : ℕ} {L : ℝ} (hL : 0<L) (i : Fin n) :
    basis n L hL i = (2*L) • (EuclideanSpace.basisFun (Fin n) ℝ) i := by
  exact Basis.isUnitSMul_apply _ i

lemma period_mem {n : ℕ} {L : ℝ} (hL : 0<L) (z : Fin n → ℤ) :
    cubePeriod L z ∈ Submodule.span ℤ (Set.range (basis n L hL)) := by
  have he : cubePeriod L z = ∑ i,(z i) • basis n L hL i := by
    ext j
    simp [cubePeriod,basis_apply,EuclideanSpace.basisFun_apply,
      Pi.single_apply,mul_ite]
  rw [he]
  apply Submodule.sum_mem
  intro i _
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i,rfl⟩)

lemma covering {n : ℕ} {K : Set (Space n)} (P : CubicCover K) :
    ∀ y,∃ (i : P.centers) (l : Submodule.span ℤ (Set.range (basis n P.L P.positive))),
      y-i.val-l.val ∈ K := by
  intro y
  obtain ⟨x,hx,hy⟩ := P.covers y
  obtain ⟨s,hs,z,rfl⟩ := hx
  refine ⟨⟨s,hs⟩,⟨cubePeriod P.L z,period_mem P.positive z⟩,?_⟩
  simpa only [sub_add_eq_sub_sub] using hy
end CubicLattice

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_PeriodicEquality
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open MeasureTheory ProbabilityTheory Set
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set MeasureTheory
open scoped ENNReal Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open MeasureTheory ProbabilityTheory Set
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set MeasureTheory
open scoped ENNReal Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal

universe u_1 u_2 u_3 u_4 u_5

namespace PeriodicEquality
open Set Filter MeasureTheory TranslativeCovering LatticeAveraging
open scoped ENNReal Topology BigOperators Classical
abbrev Space (n : ℕ) := EuclideanSpace ℝ (Fin n)

noncomputable def centers {n : ℕ} {I : Type u_1} (Λ : Submodule ℤ (Space n)) (p : I → Space n) : Set (Space n) :=
  {x | ∃ (i : I) (l : Λ),x=p i+l.val}

end PeriodicEquality

end OAI
end

section
-- module Solutions.OAIQ16_CD.TranslativeCovering_PeriodicDensity
attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open MeasureTheory ProbabilityTheory Set
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set MeasureTheory
open scoped ENNReal Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open MeasureTheory ProbabilityTheory Set
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set MeasureTheory
open scoped ENNReal Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal

namespace TranslativeCovering
open Set MeasureTheory Module
open scoped ENNReal Classical

structure PeriodicCover {n : ℕ} (K : Set (Space n)) where
  lattice : Submodule ℤ (Space n)
  discrete : DiscreteTopology lattice
  fullrank : IsZLattice ℝ lattice
  m : ℕ
  offsets : Fin m → Space n
  covers : ∀ y,∃ (i : Fin m) (l : lattice),y-offsets i-l.val∈K

end TranslativeCovering

end OAI
end

section
-- module Solutions.OAIQ16_CD.CoveringDensity_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CoveringOrder
open Set MeasureTheory
open scoped ENNReal

/-- A single lattice is a one-coset periodic covering. -/
def LatticeCover.toPeriodic {n : ℕ} {K : Set (Space n)} (P : LatticeCover K) :
    TranslativeCovering.PeriodicCover K where
  lattice := P.lattice
  discrete := P.discrete
  fullrank := P.fullrank
  m := 1
  offsets := fun _ => 0
  covers := by
    intro y
    obtain ⟨l, hl⟩ := P.covers y
    exact ⟨0, l, by simpa using hl⟩

end CoveringOrder

end OAI
end


