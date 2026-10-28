-- Prove2me | Definitions.Def_OAIQ039C018
-- name    : OAIQ039C018
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T09:08:14.132791+00:00
-- url     : https://prove2.me/theorems/c22d79f3-ca2e-45a6-8e86-b5fcc7ebea84
-- title:
--   Definitions bundle OAIQ039C018 of the split of OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Kadison.uniform_commutator`, carved from OpenAI's openai/math development (OpenAI, *Kadison's similarity theorem through uniform derivation estimates (result family 288)*, OpenAI Math Release, September 23, 2026, result family 288, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 30 declarations of OpenAI's Lean: 17 definitions, 3 instances and 10 theorems. The definitions and types are `OAI.Kadison.StrongContinuity.vectors`, `OAI.Kadison.SymmetryAlgebra.algebra`, `OAI.Kadison.SymmetryAlgebra.factors`, `OAI.Kadison.TracialGNS.operatorStage`, `OAI.Kadison.TracialGNS.stageAlgebra`, `OAI.Kadison.TracialGNS.stageUnitary`, `OAI.Kadison.TracialGNS.stageUnitaryHom`, `OAI.Kadison.TracialSequence.constantSequence`, `OAI.Kadison.TracialSequence.evalSequence`, `OAI.Kadison.TracialSequence.leftFamily`, `OAI.Kadison.TracialSequence.mapSequence`, `OAI.Kadison.TracialSequence.pullUnitary`, `OAI.Kadison.UnitaryDualAction.act`, `OAI.Kadison.UnitaryHaar.compactUnitary`, `OAI.Kadison.UnitaryHaar.probability`, `OAI.Kadison.UnitaryHaar.whole`, `OAI.Kadison.WOTDistance.normBall`.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis/Commutator, in whole or in part: `Commutator_FreeSymmetrization`, `Commutator_MainMatrix`, `Commutator_MatrixGNS`, `Commutator_StageGeneration`, `Commutator_StrongContinuity`, `Commutator_SubfactorExpectation`, `Commutator_TracialDoubleCompression`, `Commutator_TracialSequence`, `Commutator_TracialSmallCorners`, `Commutator_UnitaryDualAction`, `Commutator_UnitaryEquivMoments`, `Commutator_UnitaryHaar`, `Commutator_UnitarySequence`, `Commutator_WOTCompact`.
--
--   **Imports.** It imports the published bundle `Def_UniformCommutator`.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ039C030`; the statements `OAI.Kadison.FreeBlocks.normal_free_corner_bound`, `OAI.Kadison.FreeBlocks.normal_free_original_bound`, `OAI.Kadison.TracialGNS.exists_corner_weak_zero`, `OAI.Kadison.TracialSequence.pullUnitary_moment_limits` and `OAI.Kadison.WOTDistance.ball_functional_bound`; the proofs of `OAI.Kadison.Decomposable.localized_matrix_commutator_bound`, `OAI.Kadison.Decomposable.matrix_commutator_bound_of_countable_factor_fields`, `OAI.Kadison.FreeBlocks.normal_free_original_bound`, `OAI.Kadison.IntertwinerCompression.seminorm_le`, `OAI.Kadison.OrbitStateHull.exists_tracial_hull_of_norm_separable`, `OAI.Kadison.TracialSequence.pullUnitary_moment_limits`, `OAI.Kadison.UnitaryTransport.bound_of_conjugate_bound`, `OAI.Kadison.WOTDistance.ball_functional_bound`, `OAI.Kadison.WOTDistance.exists_commutant_approximation`, `OAI.Kadison.commutatorSeminorm_nonneg`, `OAI.Kadison.isometry_row_error_bound` and `OAI.Kadison.uniform_commutator_of_isometries`.
-- source:
--   OpenAI, Kadison's similarity theorem through uniform derivation estimates (result family 288), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 288; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Kadisons-similarity-theorem-through-uniform-derivation-estimates-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis/Commutator at commit adc7f12

import Mathlib
import Definitions.Def_UniformCommutator

section
-- module Solutions.OAIQ039_CM.Commutator_StrongContinuity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped Topology

open Filter

namespace Kadison.StrongContinuity

variable {X E : Type*} [TopologicalSpace X] [NormedAddCommGroup E] [NormedSpace ℂ E]

variable (T : X → E →ₗᵢ[ℂ] E)

def vectors : Submodule ℂ E where
  carrier := {x | Continuous (fun g => T g x)}
  zero_mem' := by
    change Continuous (fun g => T g (0:E))
    simpa only [map_zero] using (continuous_const : Continuous (fun _ : X => (0:E)))
  add_mem' := by
    intro x y hx hy
    change Continuous (fun g => T g x) at hx
    change Continuous (fun g => T g y) at hy
    change Continuous (fun g => T g (x+y))
    simp only [map_add]
    exact hx.add hy
  smul_mem' := by
    intro a x hx
    change Continuous (fun g => T g x) at hx
    change Continuous (fun g => T g (a • x))
    simp only [map_smul]
    exact continuous_const.smul hx

end Kadison.StrongContinuity

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_MatrixGNS
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace

namespace Kadison.TracialGNS

open Matrix

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ) (hτ : ∀ a b : A, τ (a * b) = τ (b * a)) (h1 : τ 1 = 1)

variable {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]

variable (φ : Matrix I I ℂ →⋆ₐ[ℂ] A)

def stageUnitary (u : unitary (Matrix I I ℂ)) : unitary A :=
  ⟨φ u, Unitary.map_mem φ u.property⟩

end Kadison.TracialGNS
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_StageGeneration
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
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace Kadison.TracialGNS

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ)

variable (I : ℕ → Type*) [∀ n, Fintype (I n)] [∀ n, DecidableEq (I n)]

variable (φ : ∀ n, Matrix (I n) (I n) ℂ →⋆ₐ[ℂ] A)

def operatorStage (n : ℕ) : StarSubalgebra ℂ (τ.GNS →L[ℂ] τ.GNS) :=
  (τ.gnsStarAlgHom.comp (φ n)).range

def stageAlgebra : StarSubalgebra ℂ (τ.GNS →L[ℂ] τ.GNS) :=
  ⨆ n, operatorStage τ I φ n

end Kadison.TracialGNS
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FreeSymmetrization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace Matrix.Norms.L2Operator

open MeasureTheory MeasureTheory.Measure

namespace Kadison.TracialGNS

variable {D : Type*} [CStarAlgebra D]

variable {I : Type*} [Fintype I] [DecidableEq I]

def stageUnitaryHom (φ : Matrix I I ℂ →⋆ₐ[ℂ] D) : unitary (Matrix I I ℂ) →* unitary D where
  toFun := stageUnitary φ
  map_one' := Subtype.ext (map_one φ)
  map_mul' a b := Subtype.ext (map_mul φ (a:Matrix I I ℂ) (b:Matrix I I ℂ))

end Kadison.TracialGNS

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_MainMatrix
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

universe u

open scoped InnerProductSpace BigOperators ComplexOrder

namespace Kadison

variable {K : Type u} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

lemma commutator_ball_bdd (P : VonNeumannAlgebra K) (Y : K →L[ℂ] K) :
    BddAbove {r : ℝ | ∃ a : K →L[ℂ] K, a∈P ∧ ‖a‖ ≤ 1 ∧ r=‖Y*a-a*Y‖} := by
  refine ⟨2*‖Y‖,?_⟩
  rintro r ⟨a,_,ha,rfl⟩
  calc
    ‖Y*a-a*Y‖ ≤ ‖Y*a‖+‖a*Y‖ := norm_sub_le _ _
    _ ≤ ‖Y‖*‖a‖+‖a‖*‖Y‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ ≤ 2*‖Y‖ := by nlinarith [norm_nonneg Y]

lemma commutator_bound_unitball (P : VonNeumannAlgebra K) (Y : K →L[ℂ] K)
    {a : K →L[ℂ] K} (ha : a∈P) (hn : ‖a‖ ≤ 1) :
    ‖Y*a-a*Y‖ ≤ commutatorSeminorm P Y :=
  le_csSup (commutator_ball_bdd P Y) ⟨a,ha,hn,rfl⟩

lemma commutator_bound (P : VonNeumannAlgebra K) (Y : K →L[ℂ] K)
    {a : K →L[ℂ] K} (ha : a∈P) :
    ‖Y*a-a*Y‖ ≤ commutatorSeminorm P Y*‖a‖ := by
  by_cases hz : a=0
  · simp [hz]
  have hpos := norm_pos_iff.mpr hz
  have hn : ‖((‖a‖⁻¹:ℝ):ℂ) • a‖ ≤ 1 := by
    rw [norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hpos),inv_mul_cancel₀ hpos.ne']
  have hb := commutator_bound_unitball P Y (P.toStarSubalgebra.smul_mem ha (((‖a‖⁻¹:ℝ):ℂ))) hn
  have he : Y*(((‖a‖⁻¹:ℝ):ℂ) • a)-(((‖a‖⁻¹:ℝ):ℂ) • a)*Y=((‖a‖⁻¹:ℝ):ℂ) • (Y*a-a*Y) := by
    simp only [mul_smul_comm,smul_mul_assoc,smul_sub]
  rw [he,norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hpos)] at hb
  have hh := mul_le_mul_of_nonneg_left hb hpos.le
  rw [←mul_assoc,mul_inv_cancel₀ hpos.ne',one_mul] at hh
  simpa only [mul_comm ‖a‖] using hh

end Kadison

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_SubfactorExpectation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

namespace Kadison.SymmetryAlgebra

variable {A : Type*} [Ring A] [Algebra ℂ A] [StarRing A] [StarModule ℂ A]

variable (s : A) (hs : star s=s) (hs2 : s*s=1)

def algebra : StarSubalgebra ℂ A where
  carrier := {a | ∃ z w : ℂ, a=z • (1:A)+w • s}
  zero_mem' := ⟨0,0,by simp⟩
  one_mem' := ⟨1,0,by simp⟩
  add_mem' := by
    rintro a b ⟨z,w,rfl⟩ ⟨z',w',rfl⟩
    exact ⟨z+z',w+w',by module⟩
  mul_mem' := by
    rintro a b ⟨z,w,rfl⟩ ⟨z',w',rfl⟩
    refine ⟨z*z'+w*w',z*w'+w*z',?_⟩
    simp only [add_mul,mul_add,smul_mul_assoc,mul_smul_comm,
      one_mul,mul_one,hs2]
    module
  algebraMap_mem' z := ⟨z,0,by simp [Algebra.algebraMap_eq_smul_one]⟩
  star_mem' := by
    rintro a ⟨z,w,rfl⟩
    exact ⟨star z,star w,by simp only [star_add,star_smul,star_one,hs]⟩

@[simp] lemma mem_algebra {a : A} : a∈algebra s hs hs2 ↔ ∃ z w : ℂ,a=z • (1:A)+w • s := Iff.rfl

variable (S : Bool → StarSubalgebra ℂ A) (τ : A →ₗ[ℂ] ℂ)

def factors : Bool → StarSubalgebra ℂ A := fun i => if i then algebra s hs hs2 else S false

end Kadison.SymmetryAlgebra

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_TracialSequence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped Topology InnerProductSpace BoundedContinuousFunction ComplexOrder

open Filter UniformSpace Completion

namespace Kadison.TracialSequence

open TracialGNS

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ) (ω : Ultrafilter ℕ)

def leftFamily (a : ℕ →ᵇ A) : ℕ →ᵇ (τ.GNS →L[ℂ] τ.GNS) :=
  BoundedContinuousFunction.mkOfDiscrete (fun i => τ.gnsStarAlgHom (a i)) (2*‖a‖)
    (fun i j => (dist_le_norm_add_norm _ _).trans (by
      have hi := (NonUnitalStarAlgHom.norm_apply_le τ.gnsStarAlgHom (a i)).trans (a.norm_coe_le_norm i)
      have hj := (NonUnitalStarAlgHom.norm_apply_le τ.gnsStarAlgHom (a j)).trans (a.norm_coe_le_norm j)
      linarith))

@[simp] lemma leftFamily_apply (a : ℕ →ᵇ A) (i : ℕ) : leftFamily τ a i=τ.gnsStarAlgHom (a i) := rfl

end Kadison.TracialSequence

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

open TracialGNS

def constantSequence {A : Type} [CStarAlgebra A] : A →⋆ₐ[ℂ] (ℕ →ᵇ A) where
  toFun := BoundedContinuousFunction.const ℕ
  map_one' := by ext i; rfl
  map_mul' a b := by ext i; rfl
  map_zero' := by ext i; rfl
  map_add' a b := by ext i; rfl
  commutes' z := by ext i; rfl
  map_star' a := by ext i; rfl

@[simp] lemma constantSequence_apply {A : Type} [CStarAlgebra A] (a : A) :
    constantSequence a=BoundedContinuousFunction.const ℕ a := rfl

end Kadison.TracialSequence

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_TracialSmallCorners
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

attribute [local instance] Classical.propDecidable

open scoped Topology InnerProductSpace BoundedContinuousFunction ComplexOrder

open Filter UniformSpace Completion

namespace Kadison.TracialSequence

open TracialGNS

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

def mapSequence (f : A →⋆ₐ[ℂ] B) : (ℕ →ᵇ A) →⋆ₐ[ℂ] (ℕ →ᵇ B) where
  toFun a := BoundedContinuousFunction.ofNormedAddCommGroupDiscrete (fun i => f (a i))
    ‖a‖ (fun i => (NonUnitalStarAlgHom.norm_apply_le f (a i)).trans (a.norm_coe_le_norm i))
  map_one' := by ext i; exact map_one f
  map_mul' a b := by ext i; exact map_mul f (a i) (b i)
  map_zero' := by ext i; exact map_zero f
  map_add' a b := by ext i; exact map_add f (a i) (b i)
  commutes' z := by ext i; exact AlgHom.commutes f.toAlgHom z
  map_star' a := by ext i; exact map_star f (a i)

@[simp] lemma mapSequence_apply (f : A →⋆ₐ[ℂ] B) (a : ℕ →ᵇ A) (i : ℕ) :
    mapSequence f a i=f (a i) := rfl

end Kadison.TracialSequence

end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_UnitaryDualAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

namespace Kadison.UnitaryDualAction

variable {A : Type*} [CStarAlgebra A]

lemma weak_ext {f g : WeakDual ℂ A} (h : ∀ a,f a=g a) : f=g :=
  WeakDual.toStrongDual.injective (ContinuousLinearMap.ext h)

def act (u : unitary A) (f : WeakDual ℂ A) : WeakDual ℂ A :=
  StrongDual.toWeakDual (f.toStrongDual.comp (ContinuousLinearMap.mulLeftRight ℂ A (star (u:A)) (u:A)))

@[simp] lemma act_apply (u : unitary A) (f : WeakDual ℂ A) (a : A) :
    act u f a=f (star (u:A)*a*(u:A)) := rfl

instance action : MulAction (unitary A) (WeakDual ℂ A) where
  smul := act
  one_smul f := by apply weak_ext; intro a; change f (star (1:A)*a*1)=f a; simp
  mul_smul u v f := by
    apply weak_ext
    intro a
    change f (star ((u:A)*(v:A))*a*((u:A)*(v:A)))=
      f (star (v:A)*(star (u:A)*a*(u:A))*(v:A))
    simp only [star_mul,mul_assoc]

@[simp] lemma smul_apply (u : unitary A) (f : WeakDual ℂ A) (a : A) :
    (u • f) a=f (star (u:A)*a*(u:A)) := rfl

instance continuous_action : ContinuousConstSMul (unitary A) (WeakDual ℂ A) where
  continuous_const_smul u := WeakDual.continuous_of_continuous_eval
    (fun a => WeakDual.eval_continuous (star (u:A)*a*(u:A)))

end Kadison.UnitaryDualAction

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_UnitarySequence
attribute [-instance] _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped ComplexOrder Topology BoundedContinuousFunction

open Filter

namespace Kadison.TracialSequence

variable {A : Type} [CStarAlgebra A]

def evalSequence (n : ℕ) : (ℕ →ᵇ A) →⋆ₐ[ℂ] A where
  toFun a := a n
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl
  map_star' _ := rfl

end Kadison.TracialSequence

end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_UnitaryEquivMoments
attribute [-instance] _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped ComplexOrder Topology BoundedContinuousFunction

open Filter

namespace Kadison.TracialSequence

variable {A B : Type} [CStarAlgebra A] [CStarAlgebra B]

def pullUnitary (e : A ≃⋆ₐ[ℂ] B) (u : unitary B) : unitary A :=
  ⟨e.symm u,Unitary.map_mem e.symm.toStarAlgHom u.property⟩

end Kadison.TracialSequence

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_UnitaryHaar
attribute [-instance] _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open MeasureTheory MeasureTheory.Measure TopologicalSpace

namespace Kadison.UnitaryHaar

variable (A : Type*) [CStarAlgebra A] [FiniteDimensional ℂ A] [Nontrivial A]

abbrev compactUnitary : CompactSpace (unitary A) := by
  let : ProperSpace A := FiniteDimensional.proper ℂ A
  apply isCompact_iff_compactSpace.mp
  apply (isCompact_closedBall (0:A) 1).of_isClosed_subset isClosed_unitary
  intro a ha
  simp only [Metric.mem_closedBall,dist_zero_right]
  exact (CStarRing.norm_of_mem_unitary ha).le

variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G]

def whole : PositiveCompacts G where
  carrier := Set.univ
  isCompact' := isCompact_univ
  interior_nonempty' := by simp

def probability : Measure G := haarMeasure (whole G)

instance instIsMulLeftInvariantProbability : IsMulLeftInvariant (probability G) := by
  dsimp only [probability]
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | (apply Measurable.aemeasurable; measurability) | measurability)

end Kadison.UnitaryHaar

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_WOTCompact
attribute [-instance] _root_.OAI.Kadison.UnitaryDualAction.action
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

def normBall (C : ℝ) : Set (H →WOT[ℂ] H) := {T | ‖T.toCLM‖≤C}

end Kadison.WOTDistance

end

end
end

end OAI
end


