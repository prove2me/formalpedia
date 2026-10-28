-- Prove2me | Definitions.Def_OAIQ031A102
-- name    : OAIQ031A102
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T14:38:56.763244+00:00
-- url     : https://prove2.me/theorems/a46aa4ce-a9a3-4f1d-9249-8f0b668f4ee6
-- title:
--   Definitions bundle OAIQ031A102 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 13 declarations of OpenAI's Lean: 8 definitions and 5 theorems. The definitions and types are `OAI.ArExplicit.TriangularInduction.eCochain`, `OAI.ArExplicit.TwoCone.baseCokernelRestrictionEquiv`, `OAI.ArExplicit.TwoCone.baseCokernelTransport`, `OAI.ArExplicit.TwoCone.topCokernelMap`, `OAI.ArExplicit.twistedBarTensorBimoduleEquiv`, `OAI.ArExplicit.twistedBarTensorZeroEquiv`, `OAI.ArExplicit.twistedBarZeroBimoduleEquiv`, `OAI.ArExplicit.twistedBarZeroScalarEquiv`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Bar_TwistedBarTensorRegular`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/TwistedBarTensorRegular.lean), [`AuslanderReiten_Cones_BimoduleTwoCone`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Cones/BimoduleTwoCone.lean), [`AuslanderReiten_Cones_TwoConeBaseRestriction`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Cones/TwoConeBaseRestriction.lean), [`AuslanderReiten_Cones_TwoConeCells`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Cones/TwoConeCells.lean), [`AuslanderReiten_Cones_TwoConeRestriction`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Cones/TwoConeRestriction.lean), [`AuslanderReiten_Cones_TwoConeTopCokernel`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Cones/TwoConeTopCokernel.lean), [`AuslanderReiten_Triangular_TriangularCochain`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Triangular/TriangularCochain.lean).
--
--   **Imports.** It imports the bundles `OAIQ031A078`, `OAIQ031A079`, `OAIQ031A082`, `OAIQ031A083`, `OAIQ031A086`, `OAIQ031A088` and `OAIQ031A089` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ031A115`, `OAIQ031A116` and `OAIQ031A144`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A078
import Definitions.Def_OAIQ031A079
import Definitions.Def_OAIQ031A082
import Definitions.Def_OAIQ031A083
import Definitions.Def_OAIQ031A086
import Definitions.Def_OAIQ031A088
import Definitions.Def_OAIQ031A089

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_TwistedBarTensorRegular
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ExternalTensor.hasHomCochainTotal _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.moduleCatBaseComm _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit
open CategoryTheory
open scoped TensorProduct
universe u
variable (k A B : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
attribute [local instance 2000] moduleCatBaseModule moduleCatBaseTower

def twistedBarZeroScalarEquiv (h : A ≃ₐ[k] A) : AbsoluteBar.twistedObject k A h 0 ≃ₗ[k] A where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' a x := by
    change ((AbsoluteBar.representation k A 0).comp (AbsoluteBar.twistEnveloping k A h).toAlgHom)
      (algebraMap k (AbsoluteBar.Enveloping k A) a) (show A from x) = a • (show A from x)
    rw [AlgHom.commutes]
    rfl

def twistedBarTensorZeroEquiv (hA : A ≃ₐ[k] A) (hB : B ≃ₐ[k] B) :
    ExternalTensor.envelopingObject k A B
      (ExternalTensor.moduleObject k (AbsoluteBar.Enveloping k A) (AbsoluteBar.Enveloping k B)
        (AbsoluteBar.twistedObject k A hA 0) (AbsoluteBar.twistedObject k B hB 0)) ≃ₗ[
          ExternalTensor.EnvelopingProduct k A B]
      AbsoluteBar.twistedObject k (A ⊗[k] B) (Algebra.TensorProduct.congr hA hB) 0 where
  __ := (TensorProduct.congr (twistedBarZeroScalarEquiv k A hA)
    (twistedBarZeroScalarEquiv k B hB)).toAddEquiv
  map_smul' a x := by
    let z : (AbsoluteBar.twistedObject k A hA 0) ⊗[k] (AbsoluteBar.twistedObject k B hB 0) := x
    let e := TensorProduct.congr (twistedBarZeroScalarEquiv k A hA) (twistedBarZeroScalarEquiv k B hB)
    change e (ExternalTensor.representation k (AbsoluteBar.Enveloping k A) (AbsoluteBar.Enveloping k B)
      (AbsoluteBar.twistedObject k A hA 0) (AbsoluteBar.twistedObject k B hB 0)
        ((ExternalTensor.envelopingEquiv k A B).symm a) z) =
      ((AbsoluteBar.representation k (A ⊗[k] B) 0).comp
        (AbsoluteBar.twistEnveloping k (A ⊗[k] B) (Algebra.TensorProduct.congr hA hB)).toAlgHom) a (e z)
    obtain ⟨a, rfl⟩ := (ExternalTensor.envelopingEquiv k A B).surjective a
    rw [AlgEquiv.symm_apply_apply]
    induction a using OAI.tensorInductionOn with
    | add a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb]
    | tmul a b =>
      induction a using OAI.tensorInductionOn with
      | add a c ha hc => simp only [TensorProduct.add_tmul, map_add, LinearMap.add_apply, ha, hc]
      | tmul a c =>
        induction b using OAI.tensorInductionOn with
        | add b d hb hd => simp only [TensorProduct.tmul_add, map_add, LinearMap.add_apply, hb, hd]
        | tmul b d =>
          have he := ExternalTensor.envelopingEquiv_tmul k A B a (MulOpposite.unop c) b (MulOpposite.unop d)
          simp only [MulOpposite.op_unop] at he
          rw [he]
          induction z using OAI.tensorInductionOn with
          | add x y hx hy => simp only [map_add, hx, hy]
          | tmul x y =>
            let xa : A := x
            let yb : B := y
            change (a * (xa * hA (MulOpposite.unop c))) ⊗ₜ[k]
              (b * (yb * hB (MulOpposite.unop d))) =
              (a ⊗ₜ[k] b) * ((xa ⊗ₜ[k] yb) *
                ((hA (MulOpposite.unop c)) ⊗ₜ[k] (hB (MulOpposite.unop d))))
            exact ((congrArg (fun z : A ⊗[k] B => (a ⊗ₜ[k] b) * z)
              (Algebra.TensorProduct.tmul_mul_tmul xa (hA (MulOpposite.unop c)) yb
                (hB (MulOpposite.unop d)))).trans
                (Algebra.TensorProduct.tmul_mul_tmul a (xa * hA (MulOpposite.unop c)) b
                  (yb * hB (MulOpposite.unop d)))).symm

def twistedBarZeroBimoduleEquiv (h : A ≃ₐ[k] A) : AbsoluteBar.twistedObject k A h 0 ≃ₗ[
    AbsoluteBar.Enveloping k A] bimoduleEnvelopingObject k A (TwistedBimodule k A h) where
  toFun x := ⟨x⟩
  invFun x := x.value
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' a x := by
    apply TwistedBimodule.ext
    change (((AbsoluteBar.representation k A 0).comp (AbsoluteBar.twistEnveloping k A h).toAlgHom) a)
      (show A from x) = (bimoduleEnvelopingRepresentation k A (TwistedBimodule k A h) a ⟨x⟩).value
    induction a using OAI.tensorInductionOn with
    | add a b ha hb =>
      simp only [map_add]
      change (((AbsoluteBar.representation k A 0).comp (AbsoluteBar.twistEnveloping k A h).toAlgHom) a) x +
          (((AbsoluteBar.representation k A 0).comp (AbsoluteBar.twistEnveloping k A h).toAlgHom) b) x = _
      rw [ha, hb]
      rfl
    | tmul a b => rfl

def twistedBarTensorBimoduleEquiv (hA : A ≃ₐ[k] A) (hB : B ≃ₐ[k] B) :
    ExternalTensor.envelopingObject k A B
      (ExternalTensor.moduleObject k (AbsoluteBar.Enveloping k A) (AbsoluteBar.Enveloping k B)
        (AbsoluteBar.twistedObject k A hA 0) (AbsoluteBar.twistedObject k B hB 0)) ≃ₗ[
          ExternalTensor.EnvelopingProduct k A B]
      bimoduleEnvelopingObject k (A ⊗[k] B)
        (TwistedBimodule k (A ⊗[k] B) (Algebra.TensorProduct.congr hA hB)) :=
  (twistedBarTensorZeroEquiv k A B hA hB).trans
    (twistedBarZeroBimoduleEquiv k (A ⊗[k] B) (Algebra.TensorProduct.congr hA hB))

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cones_TwoConeRestriction
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory

namespace ArExplicit.TwoCone

universe u
variable {R S : Type u} [Ring R] [Ring S] (j : S →+* R) (D : Data R)

theorem restricted_exact (hex : ∀ n, Function.Exact (D.d (n+1)) (D.d n)) (n : ℕ) :
    Function.Exact ((D.restrict j).d (n+1)) ((D.restrict j).d n) := hex n

end ArExplicit.TwoCone

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cones_BimoduleTwoCone
attribute [-instance] _root_.OAI.ArExplicit.A.instIsTwoSidedAugmentationIdeal _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.Resolution.instIsScalarTowerMulOppositeBaseAlgebraSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.Resolution.simpleRightModule _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.induced_term_projective _root_.OAI.ArExplicit.TrivialInduction.instAdditiveModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instPreservesHomologyModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeQuotient _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.instInjectiveA _root_.OAI.ArExplicit.instInjectiveMulOppositeA _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.T
open CategoryTheory
open scoped TensorProduct
universe u
variable {k : Type u} [Field k] (q : k) [CharP k 2]
local notation "R" => T k q
local notation "Te" => AbsoluteBar.Enveloping k R

theorem product_term_finite (n : ℕ) :
    Module.Finite (Te ⊗[k] Te) ((productTwoConeData q).term n) := by
  let (i : ℕ) : Module.Finite Te ((AbsoluteBar.complex k R).X i) := AbsoluteBar.finite k R i
  exact ExternalTensor.term_finite k Te Te (AbsoluteBar.complex k R)
    (AbsoluteBar.complex k R) n

theorem product_term_projective (n : ℕ) :
    Module.Projective (Te ⊗[k] Te) ((productTwoConeData q).term n) := by
  let (i : ℕ) : Module.Finite Te ((AbsoluteBar.complex k R).X i) := AbsoluteBar.finite k R i
  let (i : ℕ) : Module.Projective Te ((AbsoluteBar.complex k R).X i) :=
    AbsoluteBar.projective k R i
  exact ExternalTensor.term_projective k Te Te (AbsoluteBar.complex k R)
    (AbsoluteBar.complex k R) n

end ArExplicit.T

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cones_TwoConeBaseRestriction
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.TwoCone
open CategoryTheory
universe u
variable {R S : Type u} [Ring R] [Ring S] (j : S →+* R) (D : Data R)

def baseCokernelRestrictionEquiv (n : ℕ) :
    (ModuleCat.restrictScalars j).obj (ModuleCat.of R (BaseCokernel D n)) ≃ₗ[S]
      BaseCokernel (D.restrict j) n where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def baseCokernelTransport (n : ℕ) {M : ModuleCat R} {N : ModuleCat S}
    (e : BaseCokernel D n ≃ₗ[R] M)
    (f : (ModuleCat.restrictScalars j).obj M ≃ₗ[S] N) :
    BaseCokernel (D.restrict j) n ≃ₗ[S] N :=
  (baseCokernelRestrictionEquiv j D n).symm.trans
    ((Iso.toLinearEquiv ((ModuleCat.restrictScalars j).mapIso e.toModuleIso)).trans f)

end ArExplicit.TwoCone

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cones_TwoConeCells
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit.TwoCone

universe u
variable {R : Type u} [Ring R] (D : Data R)

theorem topProjection_comm (n : ℕ) :
    (topProjection D n).comp (d D n) =
      (D.d (n+4)).comp (topProjection D (n+1)) := by
  apply LinearMap.ext
  rintro ⟨⟨a,b⟩,⟨c,e⟩⟩
  change -(-D.d (n+4) e) = D.d (n+4) e
  exact neg_neg _

end ArExplicit.TwoCone

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cones_TwoConeTopCokernel
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.TwoCone
universe u
variable {R : Type u} [Ring R] (D : Data R)

def topCokernelMap (n : ℕ) : Cokernel D n →ₗ[R] BaseCokernel D (n+4) :=
  (LinearMap.range (d D n)).liftQ
    (((LinearMap.range (D.d (n+4))).mkQ).comp (topProjection D n)) (by
      rintro x ⟨y,rfl⟩
      change (LinearMap.range (D.d (n+4))).mkQ (topProjection D n (d D n y)) = 0
      rw [show topProjection D n (d D n y) = D.d (n+4) (topProjection D (n+1) y) from
        LinearMap.congr_fun (topProjection_comm D n) y]
      exact LinearMap.congr_fun (LinearMap.range_mkQ_comp (D.d (n+4))) _)

@[simp] theorem topCokernelMap_mk (n : ℕ) (x : term D n) :
    topCokernelMap D n (Submodule.Quotient.mk x) = Submodule.Quotient.mk (topProjection D n x) := rfl

end ArExplicit.TwoCone

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Triangular_TriangularCochain
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ArExplicit.TriangularInduction

open CategoryTheory

universe u

variable {k R F : Type u} [Field k] [Ring R] [Algebra k R]
variable [AddCommGroup F] [Module k F] [Module R F] [Module Rᵐᵒᵖ F]
variable [SMulCommClass k R F] [SMulCommClass R Rᵐᵒᵖ F]
variable [IsScalarTower k R F] [IsScalarTower k Rᵐᵒᵖ F] [SMulCommClass k Rᵐᵒᵖ F]

attribute [local instance] moduleCatBaseModule moduleCatBaseTower

abbrev eCochain (P : CochainComplex (ModuleCat.{u} R) ℤ) :=
  ((eFunctor k R F).mapHomologicalComplex _).obj P

end ArExplicit.TriangularInduction

end

end OAI
end


