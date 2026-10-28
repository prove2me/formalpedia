-- Prove2me | Definitions.Def_OAIQ054H001
-- name    : OAIQ054H001
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T19:39:50.265466+00:00
-- url     : https://prove2.me/theorems/2057e0aa-4b9c-4ff3-9129-79556552ee82
-- title:
--   Definitions bundle OAIQ054H001 of the split of OpenAI, Ground-state condensation in the dilute hard-sphere gas (result family 267)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.HardSphere.condensation_with_mixed`, carved from OpenAI's openai/math development (OpenAI, *Ground-state condensation in the dilute hard-sphere gas (result family 267)*, OpenAI Math Release, September 24, 2026, result family 267, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 110 declarations of OpenAI's Lean: 75 definitions, 1 inductive type or structure, 6 instances and 28 theorems. The definitions and types are `OAI.HardSphere.Groups.paddedLabels`, `OAI.HardSphere.Groups.slotCenter`, `OAI.HardSphere.Lattice.JointBadLaw`, `OAI.HardSphere.Lattice.encounterConstant`, `OAI.HardSphere.PathCutoff.scalarRegularBound`, `OAI.HardSphere.PathCutoff.sourceMesh`, `OAI.HardSphere.PathCutoff.sourceStep`, `OAI.HardSphere.Phase.HasCommonPhase`, `OAI.HardSphere.Phase.geometricLoss`, `OAI.HardSphere.Phase.modulusOccupation`, `OAI.HardSphere.Phase.occupation`, `OAI.HardSphere.SmoothContraction`, `OAI.HardSphere.SpatialLift`, `OAI.HardSphere.SphericalCoordinates.Point`, `OAI.HardSphere.SphericalCoordinates.activeLabels`, `OAI.HardSphere.SphericalCoordinates.angle`, `OAI.HardSphere.SphericalCoordinates.axis0`, `OAI.HardSphere.SphericalCoordinates.axis1`, `OAI.HardSphere.SphericalCoordinates.axis2`, `OAI.HardSphere.SphericalCoordinates.configurationFin`, `OAI.HardSphere.SphericalCoordinates.cube`, `OAI.HardSphere.SphericalCoordinates.direction`, `OAI.HardSphere.SphericalCoordinates.gradSq`, `OAI.HardSphere.SphericalCoordinates.indexGradSq`, `OAI.HardSphere.SphericalCoordinates.particleGradSq`, `OAI.HardSphere.SphericalCoordinates.pointFin`, `OAI.HardSphere.SphericalCoordinates.reindexPoint`, `OAI.HardSphere.SphericalCoordinates.spherePoint`, `OAI.HardSphere.SphericalCoordinates.sqRadius`, `OAI.HardSphere.SphericalCoordinates.subcubeBase`, `OAI.HardSphere.SphericalCoordinates.subsetPointFill`, `OAI.HardSphere.SphericalCoordinates.subsetPointLinear`, `OAI.HardSphere.Variational.energy`, `OAI.HardSphere.Variational.gradientPairing`, `OAI.HardSphere.Wiener.PartialIndex`, `OAI.HardSphere.Wiener.leftIndex`, `OAI.HardSphere.Wiener.moment`, `OAI.HardSphere.Wiener.moment8`, `OAI.HardSphere.Wiener.rightIndex`, `OAI.HardSphere.Wiener.weight` and 36 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis/HardSphere, in whole or in part: `HardSphere_Allocation_PhysicalLabelLaw`, `HardSphere_Allocation_RouteCenters`, `HardSphere_Bridges_Index`, `HardSphere_Bridges_Moment8`, `HardSphere_Bridges_PartialIndex`, `HardSphere_Collisions_InsertionCount`, `HardSphere_Comparison_ActiveLabels`, `HardSphere_Comparison_LaplaceIntegrand`, `HardSphere_Comparison_SafeMass`, `HardSphere_Conditioning_Phase`, `HardSphere_Conditioning_PhaseTransfer`, `HardSphere_Cutoffs_Mesh`, `HardSphere_Cutoffs_RegularizationWeight`, `HardSphere_Cutoffs_Regularize`, `HardSphere_FormDomain_Energy`, `HardSphere_FormDomain_HilbertJet`, `HardSphere_Fourier_ArgumentAdd`, `HardSphere_Geometry_BadGraph`, `HardSphere_Geometry_CandidateConstant`, `HardSphere_Geometry_CoordinateLine`, `HardSphere_Geometry_EuclideanTorus`, `HardSphere_Geometry_FirstVariation`, `HardSphere_Geometry_GeneratorScalar`, `HardSphere_Geometry_GraphLiftHeatBound`, `HardSphere_Geometry_GridActivePenalty`, `HardSphere_Geometry_HalfShiftCover`, `HardSphere_Geometry_HeatScalar`, `HardSphere_Geometry_InjectiveNear`, `HardSphere_Geometry_KilledEigenvector`, `HardSphere_Geometry_LocalAE`, `HardSphere_Geometry_ParticleGradSq`, `HardSphere_Geometry_PartitionErrorIntegral`, `HardSphere_Geometry_Point`, `HardSphere_Geometry_PointFin`, `HardSphere_Geometry_RadialIndicator`, `HardSphere_Geometry_RadiusLaw`, `HardSphere_Geometry_SelectedEnergyAddCompl`, `HardSphere_Geometry_SpatialPartitionEnergy`, `HardSphere_Geometry_SubcubeBase`, `HardSphere_Geometry_SubsetPointLinear`, `HardSphere_Operators_Regularize`, `HardSphere_Operators_SemigroupLaplaceCommute`, `HardSphere_Orbitals_FieldApply`, `HardSphere_Orbitals_SelectedDeletion`, `HardSphere_PathBounds_LatticeExponentialSum`, `HardSphere_Thermodynamics_CutoffAsymptotics`, `HardSphere_Thermodynamics_SpatialCloseScale`.
--
--   **Imports.** It imports the published bundle `Def_HardSphere`.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ054H002`; the statement `OAI.HardSphere.physical_uniform_phase_error`.
-- source:
--   OpenAI, Ground-state condensation in the dilute hard-sphere gas (result family 267), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 267; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Ground-state-condensation-in-the-dilute-hard-sphere-gas-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis/HardSphere at commit adc7f12

import Mathlib
import Definitions.Def_HardSphere

section
-- module Solutions.OAIQ054_HS.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434

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
/-- The first projection of a probability measure on a product: found by instance search in d13f23b
(total `Measure.map`), here a measurable map. -/
instance isProbabilityMeasure_map_fst {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure (α × β)} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Prod.fst) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
instance isProbabilityMeasure_map_snd {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure (α × β)} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Prod.snd) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
instance isProbabilityMeasure_map_subtype_val {α : Type*} [MeasurableSpace α] {p : α → Prop}
    {μ : MeasureTheory.Measure {a // p a}} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Subtype.val) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_subtype_coe.aemeasurable
/-- Mathlib d13f23b's `YoungDiagram.card_transpose`. -/
@[simp]
theorem _root_.YoungDiagram.card_transpose (μ : YoungDiagram) : μ.transpose.card = μ.card := by
  unfold YoungDiagram.card
  apply Finset.card_bij (fun c _ => c.swap)
  · intro c hc
    have : c ∈ μ.transpose := hc
    rw [YoungDiagram.mem_transpose] at this
    exact this
  · intro a _ b _ h
    simpa using h
  · intro b hb
    refine ⟨b.swap, ?_, by simp⟩
    show b.swap ∈ μ.transpose
    rw [YoungDiagram.mem_transpose]
    simpa using hb
/-- For a measurable equivalence `e`, `IsProbabilityMeasure (μ.map e)` is found by instance search
(Mathlib d13f23b finds it for every map `f`: there `Measure.map` of a non-measurable map is a Dirac
mass, here it is `0`, so only the measurable case can be shimmed). -/
instance isProbabilityMeasure_map_measurableEquiv {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {μ : MeasureTheory.Measure α} [MeasureTheory.IsProbabilityMeasure μ]
    (e : α ≃ᵐ β) : MeasureTheory.IsProbabilityMeasure (μ.map e) :=
  MeasureTheory.Measure.isProbabilityMeasure_map e.measurable.aemeasurable
/-- `simp` closes `2 ≤ ∞` in `WithTop ℕ∞` (the smoothness order) in Mathlib d13f23b; ours has the
lemma only for `1` and casts (AffineBernstein, `isSymmSndFDerivAt (by simp)`, 2026-10-26). -/
@[simp]
theorem ofNat_le_infty (n : ℕ) [n.AtLeastTwo] : (no_index (OfNat.ofNat n) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) :=
  ENat.LEInfty.out
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_Index
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
noncomputable section
open scoped BigOperators ComplexConjugate
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Wiener

def moment : ℝ≥0∞ := (eLpNorm (id : ℝ → ℝ) 4 (gaussianReal 0 1)) ^ 4

def leftIndex (n : ℕ) (k : Fin (2^n)) : Fin (2^(n+1)) :=
  ⟨k.val, by have := k.isLt; simp only [pow_succ]; omega⟩
def rightIndex (n : ℕ) (k : Fin (2^n)) : Fin (2^(n+1)) :=
  ⟨2^n + k.val, by have := k.isLt; simp only [pow_succ]; omega⟩

def weight (n : ℕ) : ℝ := (1/4 : ℝ)*(1/2 : ℝ)^n

end HardSphere.Wiener
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_PartialIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
noncomputable section
open scoped BigOperators ComplexConjugate
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Wiener

abbrev PartialIndex (n : ℕ) := Unit ⊕ (Σ m : Fin n, Fin (2 ^ m.val))

end HardSphere.Wiener
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_FormDomain_Energy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
noncomputable section
open scoped BigOperators ComplexConjugate
namespace HardSphere.Variational
variable {H J : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [Fintype J]

def energy (u : H × (J → H)) : ℝ := ∑ i, ‖u.2 i‖ ^ 2

def gradientPairing (u v : H × (J → H)) : ℂ := ∑ i, inner ℂ (u.2 i) (v.2 i)

end HardSphere.Variational

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_FirstVariation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
namespace HardSphere

def permuteLift {N : ℕ} (σ : Equiv.Perm (Fin N)) :
    LiftedConfiguration N ≃L[ℝ] LiftedConfiguration N where
  toFun X := fun i ↦ X (σ i)
  invFun X := fun i ↦ X (σ.symm i)
  left_inv X := by funext i; simp
  right_inv X := by funext i; simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  continuous_toFun := continuous_pi fun _ ↦ continuous_apply _
  continuous_invFun := continuous_pi fun _ ↦ continuous_apply _

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_FormDomain_HilbertJet
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
noncomputable section
open scoped BigOperators ComplexConjugate
namespace HardSphere

def innerRadius (a : ℝ) (n : ℕ) : ℝ := a + 1 / ((n:ℝ)+1)

end HardSphere

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_CoordinateLine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
namespace HardSphere

open scoped ComplexConjugate

section

local instance complexTopologicalSemiring : IsTopologicalSemiring ℂ := inferInstance

end

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Operators_Regularize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
namespace HilbertRegularization
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def regularize (ε : ℝ) (z : E) : ℂ := (Real.sqrt (‖z‖^2+ε^2)-ε : ℝ)

def differential (ε : ℝ) (z : E) : E →L[ℝ] ℂ :=
  (Real.sqrt (‖z‖^2+ε^2))⁻¹ • (Complex.ofRealCLM.comp (innerSL ℝ z))

lemma smooth {ε : ℝ} (hε : 0<ε) :
    ContDiff ℝ ((⊤:ℕ∞):WithTop ℕ∞) (regularize (E := E) ε) := by
  apply Complex.ofRealCLM.contDiff.comp
  apply ContDiff.sub _ contDiff_const
  apply ContDiff.sqrt ((contDiff_norm_sq ℝ).add contDiff_const)
  intro z
  positivity

omit [InnerProductSpace ℝ E] in
lemma zero {ε : ℝ} (hε : 0≤ε) : regularize (E := E) ε 0=0 := by
  simp [regularize,Real.sqrt_sq hε]

end HilbertRegularization

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_PartitionErrorIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
open MeasureTheory Filter Set
open scoped ENNReal Topology
open MeasureTheory Set
open scoped ENNReal

namespace HardSphere
open MeasureTheory Set Filter

def selectedAllEquiv {n : ℕ} (p : Fin n → Prop) (hp : ∀ i, p i) : {i // p i} ≃ Fin n :=
  Equiv.ofBijective Subtype.val ⟨Subtype.val_injective,fun i ↦ ⟨⟨i,hp i⟩,rfl⟩⟩

def selectedDeleteEquiv {n : ℕ} (p : Fin (n+1) → Prop) (j : Fin (n+1)) (hj : ¬p j) :
    {i : Fin n // p (j.succAbove i)} ≃ {i : Fin (n+1) // p i} :=
  Equiv.ofBijective (fun i ↦ ⟨j.succAbove i.val,i.property⟩) (by
    constructor
    · intro x y h
      apply Subtype.ext
      exact Fin.succAbove_right_injective (congrArg Subtype.val h)
    · intro x
      have hx : x.val≠j := by intro h; exact hj (h ▸ x.property)
      obtain ⟨i,hi⟩ := Fin.exists_succAbove_eq hx
      refine ⟨⟨i,hi ▸ x.property⟩,?_⟩
      exact Subtype.ext hi)

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_SelectedEnergyAddCompl
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
open MeasureTheory Filter Set
open scoped ENNReal Topology
open MeasureTheory Set
open scoped ENNReal

namespace HardSphere
open MeasureTheory Set Filter ContinuousLinearMap
open scoped Convolution NNReal

abbrev SpatialLift := Fin 3 → ℝ

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Comparison_SafeMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
namespace HardSphere
open MeasureTheory Set Filter
open scoped ComplexConjugate

def safeMass (z : ℝ) : ℝ := z + Real.smoothTransition (2-4*z)

lemma safeMass_ge (z : ℝ) : z ≤ safeMass z :=
  le_add_of_nonneg_right (Real.smoothTransition.nonneg _)

lemma safeMass_pos {z : ℝ} (hz : 0≤z) : 0 < safeMass z := by
  by_cases h : z=0
  · subst z
    norm_num [safeMass,Real.smoothTransition.one_of_one_le]
  · exact (lt_of_le_of_ne hz (Ne.symm h)).trans_le (safeMass_ge z)

lemma safeMass_smooth : ContDiff ℝ ((⊤:ℕ∞):WithTop ℕ∞) safeMass :=
  contDiff_id.add (Real.smoothTransition.contDiff.comp (contDiff_const.sub (contDiff_const.mul contDiff_id)))

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Collisions_InsertionCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
namespace HardSphere
open MeasureTheory Set Filter
open scoped ComplexConjugate
open scoped Classical

noncomputable def insertionCount {S : Type*} [DecidableEq S] (site : ℕ → S) (t : ℕ) (z : S) : ℕ :=
  ((Finset.range t).filter (fun i ↦ site i=z)).card

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_EuclideanTorus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
open MeasureTheory Filter Set
open scoped ENNReal Topology
open MeasureTheory Set
open scoped ENNReal
namespace HardSphere
open MeasureTheory Set Filter ContinuousLinearMap
open scoped NNReal ComplexConjugate

def spatialMetricConstant : ℝ≥0 := (3:ℝ≥0)^((1/(2:ENNReal)).toReal)

def spatialDistanceBump : ContDiffBump (0 : SpatialLift) where
  rIn := 1/(2*((spatialMetricConstant:ℝ)+1))
  rOut := 1/((spatialMetricConstant:ℝ)+1)
  rIn_pos := by positivity
  rIn_lt_rOut := by
    have hp : 0<(spatialMetricConstant:ℝ)+1 := by positivity
    apply one_div_lt_one_div_of_lt hp
    linarith

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_InjectiveNear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
open MeasureTheory Filter Set
open scoped ENNReal Topology
open MeasureTheory Set
open scoped ENNReal

namespace HardSphere
open MeasureTheory Set Filter

def closeRamp (t : ℝ) : ℝ := max 0 (min 1 t)

lemma closeRamp_lipschitz : LipschitzWith 1 closeRamp :=
  (LipschitzWith.id.const_min 1).const_max 0

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Fourier_ArgumentAdd
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate

namespace HardSphere
open scoped ComplexConjugate
open Submodule Algebra

section

local instance complexBoundedSMul : IsBoundedSMul ℂ ℂ := inferInstance

end

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_HeatScalar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
namespace HardSphere

def heatScalar (t x : ℝ) : ℝ := Real.exp t * expNegInvGlue (x/t)

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Cutoffs_RegularizationWeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
noncomputable section
open scoped BigOperators ComplexConjugate
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
noncomputable section
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
namespace HardSphere
open scoped Topology
open ContinuousLinearMap

def regularizationWeight (δ x : ℝ) : ℝ := (δ+(1-δ)*x)⁻¹

section
variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
  [InnerProductSpace ℂ E] [InnerProductSpace ℂ F] [CompleteSpace E] [CompleteSpace F] [Nontrivial F]
local instance scalarOperatorRealAlgebraRegularizedLift : Algebra ℝ (F →L[ℂ] F) := Algebra.restrictScalars ℝ ℂ _

end
end HardSphere

namespace HardSphere
open ContinuousLinearMap Filter
open scoped Topology

section
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [CompleteSpace F] [Nontrivial F]
local instance instAlgebraRealContinuousLinearMapComplexId_solutions : Algebra ℝ (F →L[ℂ] F) := Algebra.restrictScalars ℝ ℂ _

def regularizationOperator (R : F →L[ℂ] F) (δ : ℝ) : F →L[ℂ] F :=
  cfc (p := IsSelfAdjoint) (fun x ↦ x*regularizationWeight δ x) R

end
end HardSphere

end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_GeneratorScalar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
noncomputable section
open scoped BigOperators ComplexConjugate
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
noncomputable section
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
namespace HardSphere
open ContinuousLinearMap Filter
open scoped Topology

def generatorScalar (t x : ℝ) : ℝ := t⁻¹*x*(1-heatScalar t x)

section
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [CompleteSpace F] [Nontrivial F]
local instance instAlgebraRealContinuousLinearMapComplexId_solutions_1 : Algebra ℝ (F →L[ℂ] F) := Algebra.restrictScalars ℝ ℂ _

def generatorOperator (R : F →L[ℂ] F) (t : ℝ) : F →L[ℂ] F :=
  cfc (p := IsSelfAdjoint) (generatorScalar t) R

end
end HardSphere

end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_GraphLiftHeatBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
namespace HardSphere
open ContinuousLinearMap Filter
open scoped Topology
variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
  [InnerProductSpace ℂ E] [InnerProductSpace ℂ F] [CompleteSpace E] [CompleteSpace F] [Nontrivial F]
local instance graphLiftHeatBoundRealAlgebra : Algebra ℝ (F →L[ℂ] F) :=
  Algebra.restrictScalars ℝ ℂ _

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Comparison_LaplaceIntegrand
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
namespace HardSphere
open MeasureTheory Set Filter
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def laplaceIntegrand (K : ℝ → E→L[ℂ] E) (f : E) (t : ℝ) : E :=
  Real.exp (-t) • K (max 0 t) f

def semigroupLaplace (K : ℝ → E→L[ℂ] E) (f : E) : E :=
  ∫ t in Ioi (0:ℝ), laplaceIntegrand K f t

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Bridges_Moment8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
namespace HardSphere.Wiener

def moment8 : ℝ≥0∞ := (eLpNorm (id : ℝ → ℝ) 8 (gaussianReal 0 1)) ^ 8

end HardSphere.Wiener

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_KilledEigenvector
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
noncomputable section
open scoped BigOperators ComplexConjugate
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
noncomputable section
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory

namespace HardSphere
open Filter Set ContinuousLinearMap
open scoped Topology
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F] [Nontrivial F]
local instance instAlgebraRealContinuousLinearMapComplexId_solutions_2 : Algebra ℝ (F →L[ℂ] F) := Algebra.restrictScalars ℝ ℂ _

def regularHeat (R : F →L[ℂ] F) (t : ℝ) : F →L[ℂ] F :=
  if 0<t then cfc (p := IsSelfAdjoint) (heatScalar t) R else 1

end HardSphere

end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Operators_SemigroupLaplaceCommute
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
noncomputable section
open scoped BigOperators ComplexConjugate
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
noncomputable section
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
namespace HardSphere
open MeasureTheory Set Filter ContinuousLinearMap
open scoped Topology
noncomputable section
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F] [Nontrivial F]
local instance instAlgebraRealContinuousLinearMapComplexId_solutions_3 : Algebra ℝ (F →L[ℂ] F) := Algebra.restrictScalars ℝ ℂ _
local instance instInnerProductSpaceReal_solutions : InnerProductSpace ℝ F := InnerProductSpace.rclikeToReal ℂ F

end
end HardSphere

end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Orbitals_FieldApply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal BigOperators

namespace L2Contraction
variable {α E F G : Type*} [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup G]

section Field
variable [NormedSpace ℝ E] [NormedSpace ℝ F]
    (A : α → E →L[ℝ] F) (hA : AEStronglyMeasurable A μ)
    (hbound : ∀ᵐ x ∂μ, ‖A x‖ ≤ 1)
include hA hbound

lemma field_memLp (v : Lp E 2 μ) : MemLp (fun x ↦ A x (v x)) 2 μ := by
  apply (Lp.memLp v).of_le ((continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
    (hA.prodMk (Lp.aestronglyMeasurable v)))
  filter_upwards [hbound] with x hx
  exact (A x).le_opNorm (v x) |>.trans (by nlinarith [norm_nonneg (v x)])

def fieldApply (v : Lp E 2 μ) : Lp F 2 μ :=
  (field_memLp A hA hbound v).toLp _

end Field

variable [NormedSpace ℝ E] [NormedSpace ℝ F]

lemma coeff_meas (A : G → E →L[ℝ] F) (hA : Continuous A) (u : Lp G 2 μ) :
    AEStronglyMeasurable (fun x ↦ A (u x)) μ :=
  hA.comp_aestronglyMeasurable (Lp.aestronglyMeasurable u)

end L2Contraction

namespace HardSphere

structure SmoothContraction where
  toFun : ℂ → ℂ
  smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) toFun
  zero : toFun 0 = 0
  derivative_le : ∀ z, ‖fderiv ℝ toFun z‖ ≤ 1

namespace SmoothContraction
variable (f : SmoothContraction)

lemma lipschitz : LipschitzWith 1 f.toFun :=
  lipschitzWith_of_nnnorm_fderiv_le (f.smooth.differentiable (by simp))
    (fun z ↦ NNReal.coe_le_coe.mp (f.derivative_le z))

lemma derivative_continuous : Continuous (fderiv ℝ f.toFun) :=
  f.smooth.continuous_fderiv (by simp)

end SmoothContraction
end HardSphere

open scoped RealInnerProductSpace

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Cutoffs_Regularize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal BigOperators
open scoped RealInnerProductSpace

namespace HardSphere

def regularizationScale (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

lemma regularizationScale_pos (n : ℕ) : 0 < regularizationScale n := by
  unfold regularizationScale
  positivity

lemma tendsto_regularizationScale : Tendsto regularizationScale atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

lemma modulus_lipschitz : LipschitzWith 1 (fun z : ℂ ↦ (‖z‖ : ℂ)) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  simpa only [dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, NNReal.coe_one, one_mul]
    using dist_norm_norm_le z w

end HardSphere

end
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_Point
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
open MeasureTheory Filter Set
open scoped ENNReal Topology
open MeasureTheory Set
open scoped ENNReal
namespace HardSphere.SphericalCoordinates

abbrev Point := ℝ × (ℝ × ℝ)
def angle : Set ℝ := Ioo (-Real.pi) Real.pi

def spherePoint (r φ θ : ℝ) : Point :=
  (r*Real.sin φ,(r*Real.cos φ*Real.cos θ,r*Real.cos φ*Real.sin θ))

open Filter
open scoped Topology BigOperators

def sqRadius (x : Point) : ℝ := x.1^2+x.2.1^2+x.2.2^2

def direction (φ θ : ℝ) : Point :=
  (Real.sin φ,(Real.cos φ*Real.cos θ,Real.cos φ*Real.sin θ))

end HardSphere.SphericalCoordinates

namespace HardSphere.SphericalCoordinates
open scoped Topology

def axis0 : Point := (1,(0,0))
def axis1 : Point := (0,(1,0))
def axis2 : Point := (0,(0,1))

def gradSq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : Point → E) (x : Point) : ℝ :=
  ‖fderiv ℝ f x axis0‖^2+‖fderiv ℝ f x axis1‖^2+‖fderiv ℝ f x axis2‖^2

end HardSphere.SphericalCoordinates

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_RadialIndicator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
open MeasureTheory Filter Set
open scoped ENNReal Topology
open MeasureTheory Set
open scoped ENNReal
namespace HardSphere.SphericalCoordinates

open scoped Topology

def cube (b : Point) (l : ℝ) : Set Point := Icc b (b+(l,(l,l)))

end HardSphere.SphericalCoordinates

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_ParticleGradSq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
open MeasureTheory Filter Set
open scoped ENNReal Topology
open MeasureTheory Set
open scoped ENNReal
namespace HardSphere.SphericalCoordinates
open Filter
open scoped Topology BigOperators

def particleGradSq {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : (Fin n → Point) → E) (i : Fin n) (X : Fin n → Point) : ℝ :=
  ‖fderiv ℝ F X (Pi.single i axis0)‖^2+
  ‖fderiv ℝ F X (Pi.single i axis1)‖^2+
  ‖fderiv ℝ F X (Pi.single i axis2)‖^2

end HardSphere.SphericalCoordinates

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Comparison_ActiveLabels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
open MeasureTheory Filter Set
open scoped ENNReal Topology
open MeasureTheory Set
open scoped ENNReal
namespace HardSphere.SphericalCoordinates
open scoped BigOperators

noncomputable def activeLabels {α ι : Type*} [Fintype α] (σ : α → ι) : Finset α := by
  classical
  exact Finset.univ.filter (fun i ↦ ∃ j, j≠i ∧ σ j=σ i)

end HardSphere.SphericalCoordinates

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_SubcubeBase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
open MeasureTheory Filter Set
open scoped ENNReal Topology
open MeasureTheory Set
open scoped ENNReal
namespace HardSphere.SphericalCoordinates
open scoped BigOperators

lemma interval_subdivision (b : ℝ) {h : ℝ} (hh : 0≤h) (j : ℕ) :
    (volume : Measure ℝ).restrict (Icc b (b+j*h))=
      Measure.sum (fun i : Fin j ↦ volume.restrict (Icc (b+(i:ℝ)*h) (b+((i:ℝ)+1)*h))) := by
  simp_rw [← restrict_Ioc_eq_restrict_Icc,Measure.sum_fintype]
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc,Fin.val_last,Nat.cast_add,Nat.cast_one]
    rw [← ih]
    rw [← Measure.restrict_union (Set.Ioc_disjoint_Ioc_of_le (le_refl _)) measurableSet_Ioc,
      Set.Ioc_union_Ioc_eq_Ioc (le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg j) hh)) (by nlinarith : b+(j:ℝ)*h≤b+((j:ℝ)+1)*h)]

def subcubeBase {j : ℕ} (b : Point) (h : ℝ) (v : Fin j × Fin j × Fin j) : Point :=
  (b.1+(v.1:ℝ)*h,(b.2.1+(v.2.1:ℝ)*h,b.2.2+(v.2.2:ℝ)*h))

lemma cube_volume (b : Point) (h : ℝ) :
    volume.restrict (cube b h)=
      ((volume : Measure ℝ).restrict (Icc b.1 (b.1+h))).prod
        (((volume : Measure ℝ).restrict (Icc b.2.1 (b.2.1+h))).prod
          ((volume : Measure ℝ).restrict (Icc b.2.2 (b.2.2+h)))) := by
  rw [Measure.prod_restrict,Measure.prod_restrict,← Measure.volume_eq_prod,← Measure.volume_eq_prod]
  congr 1
  ext x
  rcases b with ⟨b1,b2,b3⟩
  rcases x with ⟨x1,x2,x3⟩
  simp only [cube,Set.mem_Icc,Set.mem_prod,Prod.mk_le_mk,Prod.mk_add_mk]
  tauto

lemma cube_subdivision (b : Point) {h : ℝ} (hh : 0≤h) (j : ℕ) :
    volume.restrict (cube b (j*h))=
      Measure.sum (fun v : Fin j × Fin j × Fin j ↦ volume.restrict (cube (subcubeBase b h v) h)) := by
  rw [cube_volume]
  simp_rw [interval_subdivision _ hh j]
  rw [Measure.prod_sum,Measure.prod_sum]
  congr 1
  funext v
  rw [cube_volume]
  simp only [subcubeBase,add_mul,one_mul,add_assoc]

lemma pi_sum_sectors {α ι β : Type*} [Fintype α] [Fintype ι] [MeasurableSpace β]
    (ν : ι → Measure β) [∀v,IsFiniteMeasure (ν v)] :
    Measure.pi (fun _ : α ↦ Measure.sum ν)=
      Measure.sum (fun σ : α → ι ↦ Measure.pi (fun i ↦ ν (σ i))) := by
  classical
  apply Measure.pi_eq
  intro s hs
  rw [Measure.sum_apply _ (MeasurableSet.pi Set.countable_univ (fun i _ ↦ hs i))]
  simp_rw [Measure.pi_pi,Measure.sum_apply _ (hs _),tsum_fintype]
  exact (Fintype.prod_sum (fun i v ↦ ν v (s i))).symm

lemma cube_configuration_subdivision {n j : ℕ} (b : Point) {h : ℝ} (hh : 0≤h) :
    Measure.pi (fun _ : Fin n ↦ volume.restrict (cube b (j*h)))=
      Measure.sum (fun σ : Fin n → Fin j × Fin j × Fin j ↦
        Measure.pi (fun i ↦ volume.restrict (cube (subcubeBase b h (σ i)) h))) := by
  rw [cube_subdivision b hh j]
  have : ∀v : Fin j × Fin j × Fin j,IsFiniteMeasure (volume.restrict (cube (subcubeBase b h v) h)) :=
    fun v ↦ by rw [cube_volume]; infer_instance
  exact pi_sum_sectors _

end HardSphere.SphericalCoordinates

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_PointFin
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
open MeasureTheory Filter Set
open scoped ENNReal Topology
open MeasureTheory Set
open scoped ENNReal
namespace HardSphere.SphericalCoordinates
open scoped BigOperators

noncomputable def pointFin : Point →L[ℝ] (Fin 3 → ℝ) :=
  ContinuousLinearMap.pi ![ContinuousLinearMap.fst ℝ ℝ (ℝ×ℝ),
    (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ×ℝ)),
    (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ×ℝ))]

lemma pointFin_preserving (b h : ℝ) :
    MeasurePreserving pointFin (volume.restrict (cube (b,(b,b)) h))
      (Measure.pi (fun _ : Fin 3 ↦ (volume : Measure ℝ).restrict (Icc b (b+h)))) := by
  rw [cube_volume]
  let μ := (volume : Measure ℝ).restrict (Icc b (b+h))
  have hp := (measurePreserving_piFinSuccAbove (fun _ : Fin 3 ↦ μ) 0).symm
  have hq := (MeasurePreserving.id μ).prod (measurePreserving_piFinTwo (fun _ : Fin 2 ↦ μ)).symm
  convert hp.comp hq using 1
  all_goals try with_reducible_and_instances rfl
  funext x i
  fin_cases i <;> rfl

noncomputable def configurationFin (n : ℕ) : (Fin n → Point) →L[ℝ] (Fin n → Fin 3 → ℝ) :=
  ContinuousLinearMap.pi (fun i ↦ pointFin.comp (ContinuousLinearMap.proj i))

lemma configurationFin_preserving (n : ℕ) (b h : ℝ) :
    MeasurePreserving (configurationFin n)
      (Measure.pi (fun _ : Fin n ↦ volume.restrict (cube (b,(b,b)) h)))
      (Measure.pi (fun _ : Fin n ↦ Measure.pi (fun _ : Fin 3 ↦ (volume : Measure ℝ).restrict (Icc b (b+h))))) :=
  measurePreserving_pi _ _ (fun _ ↦ pointFin_preserving b h)

end HardSphere.SphericalCoordinates

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_RadiusLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
open MeasureTheory Filter Set
open scoped ENNReal Topology
open MeasureTheory Set
open scoped ENNReal
namespace HardSphere
open MeasureTheory Set Filter ProbabilityTheory

def radiusLaw : Measure ℝ := expMeasure 1
instance radiusLaw_probability : IsProbabilityMeasure radiusLaw := isProbabilityMeasure_expMeasure (by norm_num)
instance radiusLaw_noAtoms : NullSingletonClass radiusLaw := by
  unfold radiusLaw expMeasure gammaMeasure
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_SpatialPartitionEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
open MeasureTheory Filter Set
open scoped ENNReal Topology
open MeasureTheory Set
open scoped ENNReal

open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators

namespace HardSphere.SphericalCoordinates
open scoped BigOperators

noncomputable def reindexPoint {I J : Type*} [Fintype I] [Fintype J] (e : I ≃ J) :
    (J → Point) →L[ℝ] (I → Point) :=
  ContinuousLinearMap.pi (fun i ↦ ContinuousLinearMap.proj (e i))

def indexGradSq {I : Type*} [Fintype I] [DecidableEq I]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : (I → Point) → E) (i : I) (X : I → Point) : ℝ :=
  ‖fderiv ℝ F X (Pi.single i axis0)‖^2+
  ‖fderiv ℝ F X (Pi.single i axis1)‖^2+
  ‖fderiv ℝ F X (Pi.single i axis2)‖^2

end HardSphere.SphericalCoordinates

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_SubsetPointLinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
open MeasureTheory Filter Set
open scoped ENNReal Topology
open MeasureTheory Set
open scoped ENNReal
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
namespace HardSphere.SphericalCoordinates
open scoped BigOperators

noncomputable def subsetPointLinear {I : Type*} [Fintype I] (p : I → Prop) [DecidablePred p] :
    ({i // p i} → Point) →L[ℝ] (I → Point) :=
  ContinuousLinearMap.pi (fun i ↦ if hi : p i then ContinuousLinearMap.proj ⟨i,hi⟩ else 0)

def subsetPointFill {I : Type*} (p : I → Prop) [DecidablePred p]
    (Y : {i // ¬p i} → Point) (X : {i // p i} → Point) (i : I) : Point :=
  if hi : p i then X ⟨i,hi⟩ else Y ⟨i,hi⟩

end HardSphere.SphericalCoordinates

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_HalfShiftCover
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
open MeasureTheory Filter Set
open scoped ENNReal Topology
open MeasureTheory Set
open scoped ENNReal
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open Set Function MeasureTheory
open scoped ENNReal
namespace HardSphere.SphericalCoordinates
open scoped BigOperators
lemma pointFin_preserving_base (b : Point) (h : ℝ) :
    MeasurePreserving pointFin (volume.restrict (cube b h))
      (Measure.pi (fun q : Fin 3 ↦ (volume : Measure ℝ).restrict (Icc (pointFin b q) (pointFin b q+h)))) := by
  rw [cube_volume]
  let μ := fun q : Fin 3 ↦ (volume : Measure ℝ).restrict (Icc (pointFin b q) (pointFin b q+h))
  have hp := (measurePreserving_piFinSuccAbove μ 0).symm
  have hq := (MeasurePreserving.id (μ 0)).prod (measurePreserving_piFinTwo (fun q : Fin 2 ↦ μ (Fin.succ q))).symm
  convert hp.comp hq using 1 <;> try rfl
  funext x i
  fin_cases i <;> rfl

lemma configurationFin_preserving_base (n : ℕ) (b : Point) (h : ℝ) :
    MeasurePreserving (configurationFin n)
      (Measure.pi (fun _ : Fin n ↦ volume.restrict (cube b h)))
      (Measure.pi (fun _ : Fin n ↦ Measure.pi (fun q : Fin 3 ↦ (volume : Measure ℝ).restrict (Icc (pointFin b q) (pointFin b q+h))))) :=
  measurePreserving_pi _ _ (fun _ ↦ pointFin_preserving_base b h)
end HardSphere.SphericalCoordinates

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_GridActivePenalty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
open MeasureTheory Filter Set
open scoped ENNReal Topology
open MeasureTheory Set
open scoped ENNReal
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open Set Function MeasureTheory
open scoped ENNReal
namespace HardSphere
open SphericalCoordinates
open scoped BigOperators

noncomputable def halfGridBase (l : ℝ) (s : Fin 3 → Bool) : Point :=
  (if s 0 then l/2 else 0,if s 1 then l/2 else 0,if s 2 then l/2 else 0)

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_BadGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical ENNReal
namespace HardSphere.Lattice
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

def JointBadLaw (μ : PMF (Finset V)) (p : ℝ≥0∞) : Prop :=
  ∀ A : Finset V, (∑' B, if A⊆B then μ B else 0) ≤ p^A.card

end HardSphere.Lattice
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_PathBounds_LatticeExponentialSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
noncomputable section
open scoped BigOperators ComplexConjugate
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
noncomputable section
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace HardSphere
open MeasureTheory Set Filter SphericalCoordinates
open scoped ENNReal
noncomputable section

def latticeExponentialSum : ℝ := ∑' z : ℤ, Real.exp (-|(z:ℝ)|/3)

end
end HardSphere

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
-- module Solutions.OAIQ054_HS.HardSphere_Thermodynamics_SpatialCloseScale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
open MeasureTheory Filter Set
open scoped ENNReal Topology
open MeasureTheory Set
open scoped ENNReal
namespace HardSphere
open MeasureTheory Set Filter SphericalCoordinates
open scoped ENNReal

def spatialCloseScale (D b : ℝ) : ℝ := b*D^(-(1/3:ℝ))

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Orbitals_SelectedDeletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators
namespace HardSphere

def selectedPermutation {m n : ℕ} (S : Finset (Fin (m+n))) (hS : S.card=m) : Equiv.Perm (Fin (m+n)) := by
  classical
  have hc : Fintype.card {i : Fin (m+n) // i∉S}=n := by
    simp [hS]
  let eS : Fin m ≃ {i : Fin (m+n) //i∈S} := (S.equivFinOfCardEq hS).symm
  let eT : Fin n ≃ {i : Fin (m+n) //i∉S} := (Fintype.equivFinOfCardEq hc).symm
  exact (finSumFinEquiv (m:=m) (n:=n)).symm.trans
    ((eS.sumCongr eT).trans (Equiv.sumCompl fun i : Fin (m+n) ↦ i∈S))

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
open Wiener

end HardSphere

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Cutoffs_Mesh
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.PathCutoff

def sourceMesh (t r : ℝ) : ℕ := 2*⌈t/r^2⌉₊
def sourceStep (t r : ℝ) : ℝ := t/(⌈t/r^2⌉₊:ℝ)

end HardSphere.PathCutoff

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Thermodynamics_CutoffAsymptotics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Filter
open scoped Topology
namespace HardSphere.PathCutoff

def scalarRegularBound (C M c a b D : ℝ) : ℝ :=
  C*D^2*M*Real.exp (-(c/1296)*D^(1/6:ℝ))+
    Real.exp (-(a/8)*D)+2*M*Real.exp (-(c*b^2/82944)*D^(1/3:ℝ))

end HardSphere.PathCutoff

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Allocation_PhysicalLabelLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace HardSphere.Groups
open Wiener PathCutoff HardSphere.Lattice
attribute [local instance] Classical.propDecidable

variable {J : Type*} [Fintype J] [DecidableEq J] [MeasurableSpace J] [MeasurableSingletonClass J]

def paddedLabels (s : Finset J) : Finset (Option J) :=
  if s.Nonempty then s.image some else {none}

end HardSphere.Groups
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Allocation_RouteCenters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace HardSphere.Groups
attribute [local instance] Classical.propDecidable
variable {J : Type*} [Fintype J] [DecidableEq J]

def slotCenter {K : ℕ} (home : J→Fin 3→Fin K) (v : Fin 3→Fin K) : Option J→Fin 3→Fin K :=
  fun i ↦ i.elim v home

end HardSphere.Groups
end
end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_LocalAE
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped Topology
namespace LocalAE
variable {α β : Type*} [TopologicalSpace α] [MeasurableSpace α] (μ : Measure α)

def region (P : α → Prop) : Set α :=
  {x | ∃U : Set α, IsOpen U ∧ x∈U ∧ ∀ᵐ y ∂μ.restrict U, P y}

def representative [Inhabited β] (f : α → β) (x : α) : β := by
  classical
  exact if h : ∃z,x∈region μ (fun y ↦ f y=z) then Classical.choose h else default

end LocalAE

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Conditioning_Phase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology BigOperators ComplexConjugate
namespace HardSphere
open Wiener

def complexPhase (z : ℂ) : ℂ := z/(‖z‖:ℂ)

end HardSphere

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Conditioning_PhaseTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal

namespace HardSphere.Phase

variable {X : Type*} [MeasurableSpace X] {ν : Measure X}

def HasCommonPhase (f : X → ℂ) (U : Set X) (ν : Measure X) : Prop :=
  ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ᵐ x ∂ν.restrict U, f x = c * (‖f x‖ : ℂ)

end HardSphere.Phase

namespace HardSphere.Phase

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  {ν : Measure X} {μ : Measure Y} [IsFiniteMeasure ν] [IsFiniteMeasure μ]

def occupation (f : Y × X → ℂ) (μ : Measure Y) (ν : Measure X) : ℝ :=
  (∫ y, ‖∫ x, f (y,x) ∂ν‖^2 ∂μ) / ν.real univ

def modulusOccupation (f : Y × X → ℂ) (μ : Measure Y) (ν : Measure X) : ℝ :=
  (∫ y, (∫ x, ‖f (y,x)‖ ∂ν)^2 ∂μ) / ν.real univ

def geometricLoss (f : Y × X → ℂ) (U : Set (Y × X))
    (μ : Measure Y) (ν : Measure X) : ℝ :=
  (∫ y, ν.real (Prod.mk y ⁻¹' Uᶜ) * (∫ x, ‖f (y,x)‖^2 ∂ν) ∂μ) / ν.real univ

end HardSphere.Phase

end
end

end

end OAI
end

section
-- module Solutions.OAIQ054_HS.HardSphere_Geometry_CandidateConstant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped ENNReal NNReal
namespace HardSphere.Lattice

def encounterConstant (R : ℕ) : ℕ := 343*(2*R+1)^3

end HardSphere.Lattice

open scoped ENNReal

end

end OAI
end


