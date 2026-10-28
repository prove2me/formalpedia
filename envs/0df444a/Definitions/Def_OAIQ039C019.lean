-- Prove2me | Definitions.Def_OAIQ039C019
-- name    : OAIQ039C019
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T09:07:59.388366+00:00
-- url     : https://prove2.me/theorems/242b1bde-588e-438e-920a-bf8b0633b4bf
-- title:
--   Definitions bundle OAIQ039C019 of the split of OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 35 declarations of OpenAI's Lean: 17 definitions, 6 instances and 12 theorems. The definitions and types are `OAI.Kadison.TracialSequence.doubleCompressionPreGNS`, `OAI.Kadison.UnitaryTransport.copies`, `OAI.Kadison.WOTDistance.AlgebraBall`, `OAI.Kadison.WOTDistance.coeffLM`, `OAI.Kadison.WOTDistance.commutant`, `OAI.Kadison.WeakOperatorLimit.Converges`, `OAI.Kadison.algebraUnitaryLift`, `OAI.Kadison.algebraUnitaryRepresentation`, `OAI.Kadison.compactHaarProbability`, `OAI.Kadison.normalizedTrace`, `OAI.Kadison.operatorColumn`, `OAI.Kadison.operatorRow`, `OAI.Kadison.projectionSymmetry`, `OAI.Kadison.representedCommutator`, `OAI.Kadison.vonNeumannCentralizer`, `OAI.Kadison.zeroLimitSpace`, `OAI.l2InfiniteSumCoordinatesDecidableEq`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis/Commutator, in whole or in part: `Commutator_EndpointModule2`, `Commutator_FiniteDimensionalAverage`, `Commutator_FreePropagation`, `Commutator_HomogeneousBound`, `Commutator_L2InfiniteSumCoordinates`, `Commutator_MatrixColumnCorner`, `Commutator_MatrixCompactGroup`, `Commutator_MinimalProjection`, `Commutator_ProperlyInfinite`, `Commutator_TracialDoubleCompression`, `Commutator_UnitaryMainTransport`, `Commutator_WOTBallSeparable`, `Commutator_WOTCompact`, `Commutator_WOTFunctionals`, `Commutator_WeakConvergence`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the statements `OAI.Kadison.MatrixModule.endpoint_unit_bound`, `OAI.Kadison.commutator_column_bound`, `OAI.Kadison.isometry_column_error_bound`, `OAI.Kadison.isometry_row_adjoint_comp`, `OAI.Kadison.isometry_row_error_bound`, `OAI.Kadison.isometry_row_norm_le`, `OAI.Kadison.projectionSymmetry_half`, `OAI.Kadison.projectionSymmetry_left` and `OAI.Kadison.projectionSymmetry_right`; the proofs of `OAI.Kadison.AtomicFactor.Decomposition.finite_dimensional`, `OAI.Kadison.CentralAverage.exists_center_average`, `OAI.Kadison.CompactAverage.exists_stage_average`, `OAI.Kadison.CyclicSpectral.stableUnitary_intertwines`, `OAI.Kadison.FreeBlocks.exists_free_symmetrization`, `OAI.Kadison.FreeBlocks.normal_free_corner_bound`, `OAI.Kadison.FreeBlocks.propagation_of_local_module`, `OAI.Kadison.MatrixModule.endpoint_unit_bound`, `OAI.Kadison.MatrixTower.rectangular_bound_after_average`, `OAI.Kadison.NormalGNS.separable_gns`, `OAI.Kadison.RepresentedTower.exists_tower_average`, `OAI.Kadison.TracialGNS.stageCoefficient_rank_one`, `OAI.Kadison.TracialSequence.double_embedding`, `OAI.Kadison.UnitaryTransport.bound_of_conjugate_bound`, `OAI.Kadison.WOTDistance.annihilator_bound`, `OAI.Kadison.WOTDistance.exists_commutant_approximation`, `OAI.Kadison.commutator_column_bound`, `OAI.Kadison.isometry_column_error_bound`, `OAI.Kadison.isometry_row_adjoint_comp`, `OAI.Kadison.isometry_row_error_bound`, `OAI.Kadison.isometry_row_norm_le`, `OAI.Kadison.projectionSymmetry_half`, `OAI.Kadison.projectionSymmetry_left`, `OAI.Kadison.projectionSymmetry_right`, `OAI.Kadison.uniform_commutator`, `OAI.Kadison.uniform_commutator_finiteDimensional` and `OAI.Kadison.uniform_commutator_of_isometries`.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis/Commutator at commit adc7f12

import Mathlib

section
-- module Solutions.OAIQ039_CM.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
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
-- module Solutions.OAIQ039_CM.Commutator_EndpointModule2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace
open scoped TensorProduct
open scoped TensorProduct InnerProductSpace Topology
open UniformSpace Completion Filter
open scoped TensorProduct
open UniformSpace Completion

namespace Kadison

variable {I : Type*} [Fintype I] [DecidableEq I]

def normalizedTrace (A : Matrix I I ℂ) : ℂ :=
  (Fintype.card I : ℂ)⁻¹ * Matrix.trace A

end Kadison
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FiniteDimensionalAverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace

open ContinuousLinearMap MeasureTheory

universe u

namespace Kadison

variable {K : Type u} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

def algebraUnitaryLift (P : VonNeumannAlgebra K) : unitary P →* unitary (K →L[ℂ] K) where
  toFun v := ⟨((v:P):K →L[ℂ] K),Unitary.map_mem P.toStarSubalgebra.subtype v.property⟩
  map_one' := rfl
  map_mul' _ _ := rfl

def algebraUnitaryRepresentation (P : VonNeumannAlgebra K) : unitary P →* (K ≃ₗᵢ[ℂ] K) :=
  Unitary.linearIsometryEquiv.toMonoidHom.comp
    (algebraUnitaryLift P)

@[simp] lemma algebraUnitaryRepresentation_coe (P : VonNeumannAlgebra K) (v : unitary P) :
    (algebraUnitaryRepresentation P v : K →L[ℂ] K)=((v:P):K →L[ℂ] K) := rfl

end Kadison

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FreePropagation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open scoped ComplexOrder InnerProductSpace

noncomputable section

namespace Kadison

open Filter _root_.Topology

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]

def zeroLimitSpace (F : ℕ → H →L[ℂ] H) : Submodule ℂ H where
  carrier := {x | Tendsto (fun n => F n x) atTop (𝓝 0)}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    change Tendsto (fun n => F n (x+y)) atTop (𝓝 0)
    simpa only [map_add, add_zero] using hx.add hy
  smul_mem' := by
    intro c x hx
    change Tendsto (fun n => F n (c • x)) atTop (𝓝 0)
    simpa only [map_smul, smul_zero] using hx.const_smul c

end Kadison

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_HomogeneousBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

namespace Kadison

variable {V W : Type*}
  [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W]

section Algebra

variable {A B : Type*} [Ring A] [Ring B] [Algebra ℂ A] [Algebra ℂ B] [Star A] [Star B]

def representedCommutator (ρ : A →⋆ₐ[ℂ] B) (Y : B) : A →ₗ[ℂ] B where
  toFun x := Y*ρ x-ρ x*Y
  map_add' x y := by
    simp only [map_add,mul_add,add_mul]
    abel
  map_smul' z x := by
    simp only [map_smul,mul_smul_comm,smul_mul_assoc,smul_sub,RingHom.id_apply]

end Algebra

end Kadison

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_L2InfiniteSumCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

local instance l2InfiniteSumCoordinatesDecidableEq {α : Sort*} : DecidableEq α := Classical.decEq α

open MeasureTheory Filter

open scoped InnerProductSpace Topology ENNReal

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_MatrixColumnCorner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder Matrix.Norms.L2Operator

namespace Kadison

variable {A : Type*} [CStarAlgebra A] {p : A} (hp : IsStarProjection p)

include hp

lemma projection_symmetry_square : (p+p-1)*(p+p-1)=1 := by
  have h := hp.isIdempotentElem.eq
  noncomm_ring [h]

lemma projection_symmetry_selfadjoint : star (p+p-1)=p+p-1 := by
  simp only [star_sub,star_add,star_one,hp.isSelfAdjoint.star_eq]

def projectionSymmetry : unitary A :=
  ⟨p+p-1,by constructor <;> rw [projection_symmetry_selfadjoint hp,projection_symmetry_square hp]⟩

@[simp] lemma projectionSymmetry_coe : (projectionSymmetry hp : A)=p+p-1 := rfl

end Kadison

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_MatrixCompactGroup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped Matrix.Norms.L2Operator

open MeasureTheory MeasureTheory.Measure TopologicalSpace

namespace Kadison

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G]

def compactHaarProbability : Measure G :=
  haarMeasure (⟨⟨Set.univ,isCompact_univ⟩,by simp⟩ : PositiveCompacts G)

instance compactHaarProbability_isProbability : IsProbabilityMeasure (compactHaarProbability G) where
  measure_univ := haarMeasure_self

instance compactHaarProbability_isLeftInvariant : IsMulLeftInvariant (compactHaarProbability G) :=
  inferInstanceAs (IsMulLeftInvariant (haarMeasure _))

end Kadison

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_MinimalProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace BigOperators

namespace Kadison

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def vonNeumannCentralizer (s : Set (H →L[ℂ] H)) : VonNeumannAlgebra H where
  toStarSubalgebra := StarSubalgebra.centralizer ℂ s
  centralizer_centralizer' := by
    change Set.centralizer (Set.centralizer (↑(StarSubalgebra.centralizer ℂ s) : Set (H →L[ℂ] H))) = (↑(StarSubalgebra.centralizer ℂ s) : Set (H →L[ℂ] H))
    rw [StarSubalgebra.coe_centralizer,Set.centralizer_centralizer_centralizer]

end Kadison

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_ProperlyInfinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace BigOperators

universe u

namespace Kadison

variable {K : Type u} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

def operatorColumn (h : ℕ) (a : Fin h → (K →L[ℂ] K)) :
    K →L[ℂ] PiLp 2 (fun _ : Fin h => K) :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin h => K)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi a)

def operatorRow (h : ℕ) (a : Fin h → (K →L[ℂ] K)) :
    PiLp 2 (fun _ : Fin h => K) →L[ℂ] K :=
  ∑ i, (a i).comp (PiLp.proj 2 (fun _ : Fin h => K) i)

omit [CompleteSpace K] in
@[simp] lemma operatorColumn_apply (h : ℕ) (a : Fin h → (K →L[ℂ] K)) (x : K) (i : Fin h) :
    operatorColumn h a x i=a i x := by simp [operatorColumn]

omit [CompleteSpace K] in
@[simp] lemma operatorRow_apply (h : ℕ) (a : Fin h → (K →L[ℂ] K))
    (x : PiLp 2 (fun _ : Fin h => K)) : operatorRow h a x=∑ i,a i (x i) := by
  simp [operatorRow]

end Kadison

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_TracialDoubleCompression
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped InnerProductSpace ComplexOrder BoundedContinuousFunction

open Filter UniformSpace ContinuousLinearMap

namespace Kadison.TracialSequence

abbrev doubleCompressionPreGNS {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] (functional : A →ₚ[ℂ] ℂ) :
    SeminormedAddCommGroup functional.PreGNS :=
  InnerProductSpace.Core.toSeminormedAddCommGroup (c := functional.preGNSpreInnerProdSpace)

end Kadison.TracialSequence

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_UnitaryMainTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace BigOperators

namespace Kadison.UnitaryTransport

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

variable (U : H ≃ₗᵢ[ℂ] K)

def copies (h : ℕ) : PiLp 2 (fun _ : Fin h => H) ≃ₗᵢ[ℂ] PiLp 2 (fun _ : Fin h => K) :=
  LinearIsometryEquiv.piLpCongrRight 2 (fun _ => U)

omit [CompleteSpace H] [CompleteSpace K] in
@[simp] lemma copies_apply (h : ℕ) (x : PiLp 2 (fun _ : Fin h => H)) (i : Fin h) :
    copies U h x i=U (x i) := rfl

omit [CompleteSpace H] [CompleteSpace K] in
@[simp] lemma copies_symm_apply (h : ℕ) (x : PiLp 2 (fun _ : Fin h => K)) (i : Fin h) :
    (copies U h).symm x i=U.symm (x i) := rfl

end Kadison.UnitaryTransport

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_WOTCompact
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped Topology InnerProductSpace Pointwise

open Filter ContinuousLinearMapWOT

namespace Kadison.WOTDistance

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def commutant (S : Set (H →L[ℂ] H)) : Submodule ℂ (H →WOT[ℂ] H) where
  carrier := {T | ∀ a∈S, ofCLM a*T=T*ofCLM a}
  zero_mem' := by simp
  add_mem' := by intro x y hx hy a ha; simp [mul_add,add_mul,hx a ha,hy a ha]
  smul_mem' := by
    intro z x hx a ha
    apply toCLM_injective
    change a*(z • x.toCLM)=(z • x.toCLM)*a
    have hh : a*x.toCLM=x.toCLM*a := congrArg toCLM (hx a ha)
    rw [mul_smul_comm,smul_mul_assoc,hh]

end Kadison.WOTDistance

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_WOTBallSeparable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace Topology

open ContinuousLinearMapWOT

namespace Kadison.WOTDistance

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

abbrev AlgebraBall (M : VonNeumannAlgebra H) (C : ℝ) :=
  {T : H →WOT[ℂ] H // T.toCLM∈M ∧ ‖T.toCLM‖≤C}

end Kadison.WOTDistance

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_WOTFunctionals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators InnerProductSpace

open ContinuousLinearMapWOT

namespace Kadison.WOTDistance

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def coeffLM (p : H × StrongDual ℂ H) : (H →WOT[ℂ] H) →ₗ[ℂ] ℂ :=
  (LinearMap.proj p).comp (inducingFn (RingHom.id ℂ) H H)

omit [CompleteSpace H] in
@[simp] lemma coeffLM_apply (p : H × StrongDual ℂ H) (T : H →L[ℂ] H) :
    coeffLM p (ofCLM T)=p.2 (T p.1) := rfl

end Kadison.WOTDistance

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_WeakConvergence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped Topology InnerProductSpace

open Filter

namespace Kadison.WeakOperatorLimit

variable {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

variable {l : Filter ι} {T : ι → H →L[ℂ] H} {V : H →L[ℂ] H}

def Converges (T : ι → H →L[ℂ] H) (V : H →L[ℂ] H) (l : Filter ι) : Prop :=
  ∀ x y, Tendsto (fun i => inner ℂ (T i x) y) l (𝓝 (inner ℂ (V x) y))

end Kadison.WeakOperatorLimit

end

end
end

end OAI
end


