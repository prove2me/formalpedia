-- Prove2me | Definitions.Def_OAIQ031A043
-- name    : OAIQ031A043
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T13:04:18.769597+00:00
-- url     : https://prove2.me/theorems/aaa07acb-7cf6-47bb-9735-4c382df45960
-- title:
--   Definitions bundle OAIQ031A043 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 25 declarations of OpenAI's Lean: 4 definitions, 1 instance and 20 theorems. The definitions and types are `OAI.ArExplicit.parameterUnit`, `OAI.ArExplicit.scalarExtensionHom`, `OAI.ArExplicit.scalarExtensionHomLinear`, `OAI.ArExplicit.scalarExtensionMap`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Algebras_Radical`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Algebras/Radical.lean), [`AuslanderReiten_BaseChange_ScalarExtension`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/BaseChange/ScalarExtension.lean), [`AuslanderReiten_BaseChange_ScalarExtensionExact`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/BaseChange/ScalarExtensionExact.lean), [`AuslanderReiten_BaseChange_ScalarExtensionHom`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/BaseChange/ScalarExtensionHom.lean), [`AuslanderReiten_Complete_FrobeniusGorenstein`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Complete/FrobeniusGorenstein.lean), [`AuslanderReiten_Coordinates_ConcreteParameters`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Coordinates/ConcreteParameters.lean), [`AuslanderReiten_Coordinates_MappedBiproductRow`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Coordinates/MappedBiproductRow.lean), [`AuslanderReiten_Fibers_FiberProjectionProfile`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Fibers/FiberProjectionProfile.lean), [`AuslanderReiten_Fibers_FiberProjectionZero`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Fibers/FiberProjectionZero.lean), [`AuslanderReiten_Modules_TwistedBimodule`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Modules/TwistedBimodule.lean), [`AuslanderReiten_Parameters`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Parameters.lean).
--
--   **Imports.** It imports the bundles `OAIQ031A001`, `OAIQ031A003`, `OAIQ031A007`, `OAIQ031A012`, `OAIQ031A016`, `OAIQ031A019`, `OAIQ031A020`, `OAIQ031A022` and `OAIQ031A023` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ031A060` and `OAIQ031A104`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A001
import Definitions.Def_OAIQ031A003
import Definitions.Def_OAIQ031A007
import Definitions.Def_OAIQ031A012
import Definitions.Def_OAIQ031A016
import Definitions.Def_OAIQ031A019
import Definitions.Def_OAIQ031A020
import Definitions.Def_OAIQ031A022
import Definitions.Def_OAIQ031A023

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Algebras_Radical
attribute [-instance] _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit

variable {R S : Type*} [Ring R] [Ring S]

theorem field_pi_jacobson_eq_bot (k ι : Type*) [Field k] : Ring.jacobson (ι → k) = ⊥ := by
  apply le_antisymm _ bot_le
  intro x hx
  change x = 0
  funext i
  let f : (ι → k) →+* k := Pi.evalRingHom (fun _ : ι => k) i
  let : RingHomSurjective f := ⟨fun c => ⟨fun _ => c, rfl⟩⟩
  have h := Ring.le_comap_jacobson f hx
  simpa [field_jacobson_eq_bot, Ideal.mem_comap, Ideal.mem_bot, f] using h

end ArExplicit

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_BaseChange_ScalarExtension
attribute [-instance] _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
namespace ArExplicit
universe u v w

section Maps

variable (k : Type u) [Field k] (E : Type v) [Field E] [Algebra k E]
  (R : Type w) [Ring R] [Algebra k R]
  {M N L : Type w}
  [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M]
  [AddCommGroup N] [Module R N] [Module k N] [IsScalarTower k R N]
  [AddCommGroup L] [Module R L] [Module k L] [IsScalarTower k R L]

attribute [local instance] scalarExtensionModule

def scalarExtensionMap (f : M →ₗ[R] N) :
    (E ⊗[k] M) →ₗ[E ⊗[k] R] (E ⊗[k] N) where
  toAddHom := ((f.restrictScalars k).baseChange E).toAddHom
  map_smul' a x := by
    change ((f.restrictScalars k).baseChange E) (a • x) =
      a • ((f.restrictScalars k).baseChange E) x
    induction a using OAI.tensorInductionOn with
    | add a b ha hb => simp only [add_smul, map_add, ha, hb]
    | tmul e r =>
      induction x using OAI.tensorInductionOn with
      | add x y hx hy => simp only [smul_add, map_add, hx, hy]
      | tmul e' m =>
        simp only [scalarExtension_smul_tmul, LinearMap.baseChange_tmul,
          LinearMap.restrictScalars_apply, map_smul]

@[simp]
theorem scalarExtensionMap_tmul (f : M →ₗ[R] N) (e : E) (m : M) :
    scalarExtensionMap k E R f (e ⊗ₜ[k] m) = e ⊗ₜ[k] f m := rfl

@[simp]
theorem scalarExtensionMap_id :
    scalarExtensionMap k E R (LinearMap.id : M →ₗ[R] M) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  induction x using OAI.tensorInductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul e m => rfl

@[simp]
theorem scalarExtensionMap_comp (g : N →ₗ[R] L) (f : M →ₗ[R] N) :
    scalarExtensionMap k E R (g.comp f) =
      (scalarExtensionMap k E R g).comp (scalarExtensionMap k E R f) := by
  apply LinearMap.ext
  intro x
  induction x using OAI.tensorInductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul e m => rfl

end Maps

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_BaseChange_ScalarExtensionExact
attribute [-instance] _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct

namespace ArExplicit

universe u v w

variable (k : Type u) [Field k] (E : Type v) [Field E] [Algebra k E]
  (R : Type w) [Ring R] [Algebra k R]
  {M N L : Type w}
  [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M]
  [AddCommGroup N] [Module R N] [Module k N] [IsScalarTower k R N]
  [AddCommGroup L] [Module R L] [Module k L] [IsScalarTower k R L]

attribute [local instance] scalarExtensionModule

theorem scalarExtensionMap_exact (f : M →ₗ[R] N) (g : N →ₗ[R] L)
    (h : Function.Exact f g) :
    Function.Exact (scalarExtensionMap k E R f) (scalarExtensionMap k E R g) := by
  change Function.Exact ((f.restrictScalars k).lTensor E) ((g.restrictScalars k).lTensor E)
  exact Module.Flat.lTensor_exact E h

theorem scalarExtensionMap_surjective (f : M →ₗ[R] N) (h : Function.Surjective f) :
    Function.Surjective (scalarExtensionMap k E R f) := by
  change Function.Surjective ((f.restrictScalars k).lTensor E)
  exact LinearMap.lTensor_surjective E h

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_BaseChange_ScalarExtensionHom
attribute [-instance] _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct
namespace ArExplicit
universe u v w
variable (k : Type u) [Field k] (E : Type v) [Field E] [Algebra k E]
  (R : Type w) [Ring R] [Algebra k R]
  {M N L : Type w}
  [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M]
  [AddCommGroup N] [Module R N] [Module k N] [IsScalarTower k R N]
  [AddCommGroup L] [Module R L] [Module k L] [IsScalarTower k R L]

attribute [local instance] scalarExtensionModule

def scalarExtensionHomLinear : (M →ₗ[R] N) →ₗ[k]
    ((E ⊗[k] M) →ₗ[E ⊗[k] R] (E ⊗[k] N)) where
  toFun := scalarExtensionMap k E R
  map_add' f g := by
    ext x
    induction x using OAI.tensorInductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul e m => simp [TensorProduct.tmul_add]
  map_smul' a f := by
    ext x
    induction x using OAI.tensorInductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul e m => simp [TensorProduct.tmul_smul]

def scalarExtensionHom : E ⊗[k] (M →ₗ[R] N) →ₗ[E]
    ((E ⊗[k] M) →ₗ[E ⊗[k] R] (E ⊗[k] N)) :=
  (scalarExtensionHomLinear k E R).liftBaseChange E

@[simp]
theorem scalarExtensionHom_tmul (e : E) (f : M →ₗ[R] N) :
    scalarExtensionHom k E R (e ⊗ₜ[k] f) = e • scalarExtensionMap k E R f := rfl

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Parameters
attribute [-instance] _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit

theorem parameters_algebraicallyIndependent :
    AlgebraicIndependent (ZMod 2) parameter := by
  exact (MvPolynomial.algebraicIndependent_X (Fin 3) (ZMod 2)).map'
    (f := IsScalarTower.toAlgHom (ZMod 2) ParameterRing BaseField)
    (IsFractionRing.injective ParameterRing BaseField)

theorem parameter_ne_zero (i : Fin 3) : parameter i ≠ 0 := by
  exact parameters_algebraicallyIndependent.ne_zero i

theorem parameter_pow_ne_one (i : Fin 3) (n : ℕ) (hn : 0 < n) :
    parameter i ^ n ≠ 1 := by
  intro h
  have he : (MvPolynomial.X i : ParameterRing) ^ n = 1 := by
    apply IsFractionRing.injective ParameterRing BaseField
    simpa only [map_pow, map_one, parameter] using h
  have hd := congrArg MvPolynomial.totalDegree he
  simp only [MvPolynomial.totalDegree_X_pow, MvPolynomial.totalDegree_one] at hd
  omega

theorem parameter_pow_ne (i j : Fin 3) (hij : i ≠ j) (n : ℕ) (hn : 0 < n) :
    parameter i ^ n ≠ parameter j ^ n := by
  intro h
  have he : (MvPolynomial.X i : ParameterRing) ^ n = MvPolynomial.X j ^ n := by
    apply IsFractionRing.injective ParameterRing BaseField
    simpa only [map_pow, parameter] using h
  have hd := congrArg (MvPolynomial.degreeOf i) he
  simp only [MvPolynomial.degreeOf_X_self_pow, MvPolynomial.degreeOf_X_pow_of_ne n hij] at hd
  omega

theorem q_pow_add_one_ne_zero (n : ℕ) (hn : 0 < n) : q ^ n + 1 ≠ 0 := by
  intro h
  apply parameter_pow_ne_one 0 n hn
  calc
    q ^ n = q ^ n + (1 + 1) := by rw [CharTwo.add_self_eq_zero, add_zero]
    _ = 1 := by rw [← add_assoc, h, zero_add]

end ArExplicit

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Complete_FrobeniusGorenstein
attribute [-instance] _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit

universe u

variable {R : Type u} [Ring R]

theorem gorensteinProjective_of_totallyAcyclic
    (M : Type u) [AddCommGroup M] [Module R M]
    (P : ChainComplex (ModuleCat.{u} R) ℤ) (hP : TotallyAcyclicComplex P)
    (e : M ≃ₗ[R] CompleteComparison.Cokernel P 0) : GorensteinProjective R M := by
  refine ⟨P, fun n => ⟨hP.finite n, hP.projective n⟩, hP.exactAt, ?_, ⟨e⟩⟩
  intro n f hf
  obtain ⟨g, hg⟩ := hP.dualExact n f hf
  exact ⟨g, hg.symm⟩

end ArExplicit

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Coordinates_ConcreteParameters
attribute [-instance] _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit

def parameterUnit (i : Fin 3) : BaseFieldˣ := Units.mk0 (parameter i) (parameter_ne_zero i)

@[simp] theorem parameterUnit_val (i : Fin 3) : (parameterUnit i : BaseField) = parameter i := rfl

theorem q_ne_zero : q ≠ 0 := parameter_ne_zero 0

theorem one_add_q_ne_zero : 1 + q ≠ 0 := by
  simpa only [pow_one, add_comm] using q_pow_add_one_ne_zero 1 (by decide)

theorem q_noPositivePowerOne : Resolution.NoPositivePowerOne q := by
  intro n hn
  simpa only [add_comm] using q_pow_add_one_ne_zero n hn

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Coordinates_MappedBiproductRow
attribute [-instance] _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit
open CategoryTheory CategoryTheory.Limits
universe u v w v' w'
variable (k : Type u) [CommRing k]
variable {C : Type w} [Category.{v} C] [Preadditive C]
variable {D : Type w'} [Category.{v'} D] [Preadditive D] [Linear k D]
variable (F : C ⥤ D) [F.Additive] (X : D) (Y Z : C) [HasBinaryBiproduct Y Z]

theorem mappedBiproduct_row {W : C} (b : Y ⊞ Z ⟶ W) (v : X ⟶ F.obj (Y ⊞ Z)) :
    v ≫ F.map b =
      (mappedBiproductHomEquiv k F X Y Z v).1 ≫ F.map (biprod.inl ≫ b) +
      (mappedBiproductHomEquiv k F X Y Z v).2 ≫ F.map (biprod.inr ≫ b) := by
  calc
    v ≫ F.map b = v ≫ F.map ((biprod.fst ≫ biprod.inl + biprod.snd ≫ biprod.inr) ≫ b) := by
      rw [biprod.total, Category.id_comp]
    _ = _ := by
      simp only [Functor.map_comp, Functor.map_add, Preadditive.comp_add,
        Preadditive.add_comp, mappedBiproductHomEquiv_fst, mappedBiproductHomEquiv_snd,
        Category.assoc]

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Fibers_FiberProjectionProfile
attribute [-instance] _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.TriangleGradedSequence
open CategoryTheory CategoryTheory.Pretriangulated
universe u v w
variable (k : Type u) [Field k]
variable {C : Type w} [Category.{v} C] [Preadditive C] [Linear k C]
variable [Limits.HasZeroObject C] [HasShift C ℤ]
variable [∀ n : ℤ, (CategoryTheory.shiftFunctor C n).Additive] [Pretriangulated C]
variable (T : Triangle C) (hT : T ∈ distTriang C) (X : C)
include hT

omit hT [Limits.HasZeroObject C] [Pretriangulated C] in

theorem second_surjective_of_top_subsingleton (n : ℤ) [Subsingleton (Top T X n)] :
    Function.Surjective (second k T X n) := by
  intro y
  exact ⟨0, Subsingleton.elim _ _⟩

end ArExplicit.TriangleGradedSequence

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Fibers_FiberProjectionZero
attribute [-instance] _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.TriangleGradedSequence
open CategoryTheory CategoryTheory.Pretriangulated
universe u v w
variable (k : Type u) [Field k] [CharP k 2]
variable {C : Type w} [Category.{v} C] [Preadditive C] [Linear k C]
variable [Limits.HasZeroObject C] [HasShift C ℤ]
variable [∀ n : ℤ, (CategoryTheory.shiftFunctor C n).Additive] [Pretriangulated C]
variable (T : Triangle C) (hT : T ∈ distTriang C) (X : C)
variable (em : Middle T X 0 ≃ₗ[k] k × k) (et : Top T X 0 ≃ₗ[k] k)
variable (c : k) (hc : c ≠ 0)
variable (hrow : ∀ m, et (second k T X 0 m) = c * ((em m).1 + (em m).2))

include hc hrow in
omit [CharP k 2] [Limits.HasZeroObject C] [Pretriangulated C] in
theorem second_zero_surjective : Function.Surjective (second k T X 0) := by
  intro y
  refine ⟨em.symm (c⁻¹ * et y, 0), et.injective ?_⟩
  rw [hrow, em.apply_symm_apply, add_zero, ← mul_assoc, mul_inv_cancel₀ hc, one_mul]

end ArExplicit.TriangleGradedSequence

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Modules_TwistedBimodule
attribute [-instance] _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit

namespace TwistedBimodule

variable {k R : Type*} [CommRing k] [Ring R] [Algebra k R] (σ : R ≃ₐ[k] R)

instance instSMulCommClassMulOpposite_1 : SMulCommClass k Rᵐᵒᵖ (TwistedBimodule k R σ) where
  smul_comm c r x := by ext; exact (smul_mul_assoc c x.value (σ r.unop)).symm

end TwistedBimodule
end ArExplicit

end OAI
end


