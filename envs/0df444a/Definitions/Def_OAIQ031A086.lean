-- Prove2me | Definitions.Def_OAIQ031A086
-- name    : OAIQ031A086
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T14:27:10.644303+00:00
-- url     : https://prove2.me/theorems/29b2a8e2-2605-4348-ada8-17a5f84ec1b1
-- title:
--   Definitions bundle OAIQ031A086 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 12 declarations of OpenAI's Lean: 4 definitions and 8 theorems. The definitions and types are `OAI.ArExplicit.EnvelopingBimodule.evaluationCoefficientIso`, `OAI.ArExplicit.EnvelopingBimodule.evaluationCoefficientMap`, `OAI.ArExplicit.TwoCone.BaseCokernel`, `OAI.ArExplicit.barTensorZeroEquiv`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Bar_BarTensorRegular`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/BarTensorRegular.lean), [`AuslanderReiten_Bar_BarTensorRegularCoordinates`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/BarTensorRegularCoordinates.lean), [`AuslanderReiten_Cones_TwoConeProjective`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Cones/TwoConeProjective.lean), [`AuslanderReiten_Resolutions_BinaryKoszulDual`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Resolutions/BinaryKoszulDual.lean), [`AuslanderReiten_Tensor_EnvelopingBalancedProduct`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/EnvelopingBalancedProduct.lean), [`AuslanderReiten_Tensor_EnvelopingEvaluationCoefficient`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/EnvelopingEvaluationCoefficient.lean), [`AuslanderReiten_Tensor_EnvelopingStableEvaluation`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/EnvelopingStableEvaluation.lean), [`AuslanderReiten_Tensor_TwistedTensor`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/TwistedTensor.lean), [`AuslanderReiten_Triangular_ConvertedStructure`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Triangular/ConvertedStructure.lean).
--
--   **Imports.** It imports the bundles `OAIQ031A061`, `OAIQ031A062`, `OAIQ031A068`, `OAIQ031A069`, `OAIQ031A070`, `OAIQ031A071` and `OAIQ031A073` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ031A097`, `OAIQ031A098`, `OAIQ031A099`, `OAIQ031A102` and `OAIQ031A103`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A061
import Definitions.Def_OAIQ031A062
import Definitions.Def_OAIQ031A068
import Definitions.Def_OAIQ031A069
import Definitions.Def_OAIQ031A070
import Definitions.Def_OAIQ031A071
import Definitions.Def_OAIQ031A073

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_BarTensorRegular
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ExternalTensor.hasHomCochainTotal _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
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

def barTensorZeroEquiv :
    ExternalTensor.envelopingObject k A B
      (ExternalTensor.moduleObject k (AbsoluteBar.Enveloping k A) (AbsoluteBar.Enveloping k B)
        (AbsoluteBar.moduleObject k A 0) (AbsoluteBar.moduleObject k B 0)) ≃ₗ[
          ExternalTensor.EnvelopingProduct k A B] AbsoluteBar.moduleObject k (A ⊗[k] B) 0 where
  __ := (TensorProduct.congr (barZeroScalarEquiv k A) (barZeroScalarEquiv k B)).toAddEquiv
  map_smul' a x := by
    let z : (AbsoluteBar.moduleObject k A 0) ⊗[k] (AbsoluteBar.moduleObject k B 0) := x
    let e := TensorProduct.congr (barZeroScalarEquiv k A) (barZeroScalarEquiv k B)
    change e (ExternalTensor.representation k (AbsoluteBar.Enveloping k A) (AbsoluteBar.Enveloping k B)
      (AbsoluteBar.moduleObject k A 0) (AbsoluteBar.moduleObject k B 0)
        ((ExternalTensor.envelopingEquiv k A B).symm a) z) =
      AbsoluteBar.representation k (A ⊗[k] B) 0 a (e z)
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
            change (a * (xa * MulOpposite.unop c)) ⊗ₜ[k]
              (b * (yb * MulOpposite.unop d)) =
              (a ⊗ₜ[k] b) * ((xa ⊗ₜ[k] yb) *
                ((MulOpposite.unop c) ⊗ₜ[k] (MulOpposite.unop d)))
            exact ((congrArg (fun z : A ⊗[k] B => (a ⊗ₜ[k] b) * z)
              (Algebra.TensorProduct.tmul_mul_tmul xa (MulOpposite.unop c) yb (MulOpposite.unop d))).trans
                (Algebra.TensorProduct.tmul_mul_tmul a (xa * MulOpposite.unop c) b
                  (yb * MulOpposite.unop d))).symm

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_BarTensorRegularCoordinates
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ExternalTensor.hasHomCochainTotal _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit
open scoped TensorProduct
universe u
variable (k A B : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
attribute [local instance 2000] moduleCatBaseModule moduleCatBaseTower

@[simp] theorem barTensorZeroEquiv_tmul (a : AbsoluteBar.moduleObject k A 0)
    (b : AbsoluteBar.moduleObject k B 0) :
    barTensorZeroEquiv k A B (a ⊗ₜ[k] b) = (show A from a) ⊗ₜ[k] (show B from b) := rfl

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cones_TwoConeProjective
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ArExplicit.TwoCone

universe u

variable {R : Type u} [Ring R] (D : Data R)

abbrev BaseCokernel (n : ℕ) := D.term n ⧸ LinearMap.range (D.d n)

end ArExplicit.TwoCone

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Resolutions_BinaryKoszulDual
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit.BinaryKoszul

universe u

variable (k : Type u) [Field k]

theorem range_dualColumn_eq_ker_dualRow (n : ℕ) :
    LinearMap.range (dualColumn k (n + 1)) = LinearMap.ker (dualRow k n) := by
  apply le_antisymm
  · exact LinearMap.range_le_ker_iff.mpr (dualRow_dualColumn k n)
  · rintro ⟨f, g⟩ h
    let l : Module.Dual k (Piece k (n + 1) × Piece k (n + 1)) := (-g).coprod f
    have hl : l ∈ LinearMap.ker (column k n).dualMap := by
      apply LinearMap.ext
      intro x
      have hx := DFunLike.congr_fun h x
      change f (mulX k n x) + g (mulY k n x) = 0 at hx
      change -g (mulY k n x) + f (-(mulX k n x)) = 0
      rw [map_neg, ← neg_add, add_comm]
      exact neg_eq_zero.mpr hx
    rw [← exact_dual k (column k n) (row k (n + 1))
      (range_column_eq_ker_row k n)] at hl
    obtain ⟨t, ht⟩ := hl
    refine ⟨t, Prod.ext ?_ ?_⟩
    · apply LinearMap.ext
      intro x
      have hx := DFunLike.congr_fun ht (0, x)
      simpa [l, row] using hx
    · apply LinearMap.ext
      intro x
      have hx := DFunLike.congr_fun ht (x, 0)
      have hx' := congrArg Neg.neg hx
      simpa [l, row] using hx'

end ArExplicit.BinaryKoszul

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_EnvelopingBalancedProduct
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.EnvelopingBimodule.regular_projective _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.EnvelopingBimodule
open CategoryTheory
open scoped TensorProduct
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
variable (M N : ModuleCat.{u} (R ⊗[k] Rᵐᵒᵖ))
  [Module k M] [IsScalarTower k (R ⊗[k] Rᵐᵒᵖ) M]
  [Module k N] [IsScalarTower k (R ⊗[k] Rᵐᵒᵖ) N]
variable (X : ModuleCat.{u} R) [Module k X]
local notation "ProdMN" => ModuleCat.of (R ⊗[k] Rᵐᵒᵖ) (M × N)

@[simp] theorem tensorProdMap_tmul (m : EnvelopingBimodule k R ProdMN) (x : X) :
    tensorProdMap M N X (BalancedTensor.tmul (k := k) (R := R) m x) =
      (BalancedTensor.tmul (k := k) (R := R) (⟨m.value.1⟩ : EnvelopingBimodule k R M) x,
       BalancedTensor.tmul (k := k) (R := R) (⟨m.value.2⟩ : EnvelopingBimodule k R N) x) := rfl

end ArExplicit.EnvelopingBimodule

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_EnvelopingEvaluationCoefficient
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.EnvelopingBimodule.regular_projective _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.EnvelopingBimodule
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
universe u
variable (k R : Type u) [Field k] [Ring R] [Algebra k R]
variable {X Y : ModuleCat.{u} R}
variable [Module k X] [IsScalarTower k R X] [Module k Y] [IsScalarTower k R Y]

def evaluationCoefficientMap (f : X ⟶ Y) :
    evaluationFunctor k R X ⟶ evaluationFunctor k R Y where
  app M := ModuleCat.ofHom (BalancedTensor.mapRight (k := k) (S := R)
    (F := EnvelopingBimodule k R M) f.hom)
  naturality {M N} g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    change BalancedTensor.mapRight (k := k) (S := R) f.hom (tensorMap X g z) =
      tensorMap Y g (BalancedTensor.mapRight (k := k) (S := R) f.hom z)
    induction z using BalancedTensor.induction_on with
    | zero => simp
    | add z w hz hw => simp only [_root_.map_add, hz, hw]
    | tmul m x => rfl

def evaluationCoefficientIso (e : X ≅ Y) :
    evaluationFunctor k R X ≅ evaluationFunctor k R Y :=
  NatIso.ofComponents
    (fun M => (BalancedTensor.mapRightEquiv (k := k) (S := R)
      (F := EnvelopingBimodule k R M) e.toLinearEquiv).toModuleIso)
    (fun g => (evaluationCoefficientMap k R e.hom).naturality g)

@[simp] theorem evaluationCoefficientIso_tmul (e : X ≅ Y)
    (M : ModuleCat.{u} (R ⊗[k] Rᵐᵒᵖ)) (m : EnvelopingBimodule k R M) (x : X) :
    (evaluationCoefficientIso k R e).hom.app M (BalancedTensor.tmul m x) =
      BalancedTensor.tmul m (e.hom x) := rfl

end ArExplicit.EnvelopingBimodule

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_EnvelopingStableEvaluation
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra

namespace ArExplicit.EnvelopingBimodule
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R]
variable (X : ModuleCat.{u} R) [Module k X] [IsScalarTower k R X]
variable {M N P : ModuleCat.{u} (R ⊗[k] Rᵐᵒᵖ)}
variable [Module k M] [IsScalarTower k (R ⊗[k] Rᵐᵒᵖ) M]
variable [Module k N] [IsScalarTower k (R ⊗[k] Rᵐᵒᵖ) N]
variable [Module k P] [IsScalarTower k (R ⊗[k] Rᵐᵒᵖ) P]

variable [Module.Finite k R] [Module.Finite k X]

theorem stableEvaluation_comp (f : StableHom (R ⊗[k] Rᵐᵒᵖ) M N)
    (g : StableHom (R ⊗[k] Rᵐᵒᵖ) N P) :
    stableEvaluation X (StableHom.comp g f) =
      StableHom.comp (stableEvaluation X g) (stableEvaluation X f) := by
  obtain ⟨f, rfl⟩ := StableHom.classOf_surjective f
  obtain ⟨g, rfl⟩ := StableHom.classOf_surjective g
  rw [StableHom.comp_classOf, stableEvaluation_classOf, stableEvaluation_classOf,
    stableEvaluation_classOf, StableHom.comp_classOf]
  exact congrArg (StableHom.classOf R _ _)
    (tensorMap_comp X (ModuleCat.ofHom f) (ModuleCat.ofHom g))

end ArExplicit.EnvelopingBimodule

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_TwistedTensor
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.EnvelopingBimodule.regular_projective _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit

namespace TwistedBimodule

variable {k R M : Type*} [CommRing k] [Ring R] [Algebra k R]
variable [AddCommGroup M] [Module k M] [Module R M]
variable [IsScalarTower k R M] [SMulCommClass k R M]
variable (σ : R ≃ₐ[k] R)

@[simp] theorem tensorUntwistMap_tmul (f : TwistedBimodule k R σ) (m : M) :
    tensorUntwistMap σ (BalancedTensor.tmul f m) = ⟨σ.symm f.value • m⟩ := rfl

end TwistedBimodule
end ArExplicit

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Triangular_ConvertedStructure
attribute [-instance] _root_.OAI.ArExplicit.A.instIsTwoSidedAugmentationIdeal _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.Resolution.augmentation_epi _root_.OAI.ArExplicit.Resolution.complex_projective _root_.OAI.ArExplicit.Resolution.complex_scalar _root_.OAI.ArExplicit.Resolution.instFiniteSubtypeBaseAlgebraMemSubmoduleF _root_.OAI.ArExplicit.Resolution.instIsScalarTowerMulOppositeBaseAlgebraSimple _root_.OAI.ArExplicit.Resolution.instIsScalarTowerTSimple _root_.OAI.ArExplicit.Resolution.instModuleTSimple _root_.OAI.ArExplicit.Resolution.instProjectiveBaseAlgebraSubtypeMemSubmoduleE _root_.OAI.ArExplicit.Resolution.instProjectiveBaseAlgebraSubtypeMemSubmoduleF _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.Resolution.simpleRightModule _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.instAdditiveModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instPreservesHomologyModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeQuotient _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit

namespace ConvertedAlgebra

variable {k : Type*} [Field k] (q : k) (F : Type*) [AddCommGroup F]
variable [Module (A k q) F] [Module (A k q)ᵐᵒᵖ F]
variable [SMulCommClass (A k q) (A k q)ᵐᵒᵖ F]

theorem radicalU_mem : radicalU q F ∈ Ring.jacobson (ConvertedAlgebra k q F) := by
  apply Triangular.mem_jacobson_iff _ |>.mpr
  exact ⟨A.radicalU_mem q, Submodule.zero_mem _⟩

theorem radicalT_mem : radicalT q F ∈ Ring.jacobson (ConvertedAlgebra k q F) := by
  apply Triangular.mem_jacobson_iff _ |>.mpr
  exact ⟨A.radicalT_mem q, Submodule.zero_mem _⟩

end ConvertedAlgebra
end ArExplicit

end OAI
end


