-- Prove2me | Definitions.Def_OAIQ031A074
-- name    : OAIQ031A074
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T14:17:40.26032+00:00
-- url     : https://prove2.me/theorems/e3a24236-1099-4376-9bc4-9dd6e2dcaca5
-- title:
--   Definitions bundle OAIQ031A074 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 19 declarations of OpenAI's Lean: 5 definitions and 14 theorems. The definitions and types are `OAI.ArExplicit.FiniteLeftModule.fiberInclusion`, `OAI.ArExplicit.FiniteLeftModule.fiberProjection₁`, `OAI.ArExplicit.FiniteLeftModule.fiberProjection₂`, `OAI.ArExplicit.barZeroLeftEquiv`, `OAI.ArExplicit.barZeroRightEquiv`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Bar_BarTensorRegular`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/BarTensorRegular.lean), [`AuslanderReiten_Complete_TateKoszul`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Complete/TateKoszul.lean), [`AuslanderReiten_Cones_TwoCone`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Cones/TwoCone.lean), [`AuslanderReiten_Cones_TwoConeKoszulCoordinates`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Cones/TwoConeKoszulCoordinates.lean), [`AuslanderReiten_Evaluation_TensorFreeEvaluationCoordinates`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Evaluation/TensorFreeEvaluationCoordinates.lean), [`AuslanderReiten_Fibers_FiniteFiberSides`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Fibers/FiniteFiberSides.lean), [`AuslanderReiten_Resolutions_CoverFullHomAction`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Resolutions/CoverFullHomAction.lean), [`AuslanderReiten_Stable_StableConnecting`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Stable/StableConnecting.lean), [`AuslanderReiten_Tensor_ExternalTensorTransport`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/ExternalTensorTransport.lean).
--
--   **Imports.** It imports the bundles `OAIQ031A044`, `OAIQ031A045`, `OAIQ031A046`, `OAIQ031A050`, `OAIQ031A052`, `OAIQ031A053`, `OAIQ031A055`, `OAIQ031A056`, `OAIQ031A057` and `OAIQ031A058` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ031A087` and `OAIQ031A089`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A044
import Definitions.Def_OAIQ031A045
import Definitions.Def_OAIQ031A046
import Definitions.Def_OAIQ031A050
import Definitions.Def_OAIQ031A052
import Definitions.Def_OAIQ031A053
import Definitions.Def_OAIQ031A055
import Definitions.Def_OAIQ031A056
import Definitions.Def_OAIQ031A057
import Definitions.Def_OAIQ031A058

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_BarTensorRegular
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.EnvelopingBimodule.instFiniteMulOppositeOfCarrierObjModuleCatTensorProductRestrictScalarsTensorRightInclusion _root_.OAI.ArExplicit.EnvelopingBimodule.instFiniteOfCarrierObjModuleCatTensorProductMulOppositeRestrictScalarsTensorLeftInclusion _root_.OAI.ArExplicit.EnvelopingBimodule.instProjectiveMulOppositeOfCarrierObjModuleCatTensorProductRestrictScalarsTensorRightInclusion _root_.OAI.ArExplicit.EnvelopingBimodule.instProjectiveOfCarrierObjModuleCatTensorProductMulOppositeRestrictScalarsTensorLeftInclusion _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
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

def barZeroLeftEquiv :
    ((ModuleCat.restrictScalars (tensorLeftInclusion k A Aᵐᵒᵖ)).obj
      (AbsoluteBar.moduleObject k A 0)) ≃ₗ[A] A where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' a x := by
    change a * ((show A from x) * 1) = a * (show A from x)
    rw [mul_one]

def barZeroRightEquiv :
    ((ModuleCat.restrictScalars (tensorRightInclusion k A Aᵐᵒᵖ)).obj
      (AbsoluteBar.moduleObject k A 0)) ≃ₗ[Aᵐᵒᵖ] Aᵐᵒᵖ where
  toFun x := MulOpposite.op (show A from x)
  invFun x := MulOpposite.unop x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' a x := by
    change MulOpposite.op (1 * ((show A from x) * MulOpposite.unop a)) =
      a * MulOpposite.op (show A from x)
    rw [one_mul]
    rfl

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Complete_TateKoszul
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ArExplicit.TateKoszul

universe u
variable {k : Type u} [Field k]
variable (H : ℤ → Type u) [∀ a, AddCommGroup (H a)] [∀ a, Module k (H a)]

variable {H}

variable {x y : ∀ a : ℤ, H a →ₗ[k] H (a + 3)} (M : Model x y)

theorem positive_row (a : ℤ) (n : ℕ) (ha : a = 3 * (n : ℤ))
    (v : H a × H a) :
    positiveAt M (a + 3) (n + 1) (by omega) (row (x := x) (y := y) a v) =
    BinaryKoszul.row k n
      ((positiveAt M a n ha).prodCongr (positiveAt M a n ha) v) := by
  rcases v with ⟨v, w⟩
  change positiveAt M (a + 3) (n + 1) _ (x a v + y a w) = _
  rw [map_add]
  exact congrArg₂ (· + ·) (M.positive_x a n ha v) (M.positive_y a n ha w)

theorem positive_column (a : ℤ) (n : ℕ) (ha : a = 3 * (n : ℤ))
    (v : H a) :
    ((positiveAt M (a + 3) (n + 1) (by omega)).prodCongr
      (positiveAt M (a + 3) (n + 1) (by omega))) (column (x := x) (y := y) a v) =
    BinaryKoszul.column k n (positiveAt M a n ha v) := by
  apply Prod.ext
  · exact M.positive_y a n ha v
  · change positiveAt M (a + 3) (n + 1) _ (-(x a v)) = _
    rw [map_neg]
    exact congrArg Neg.neg (M.positive_x a n ha v)

theorem negative_row (a : ℤ) (n : ℕ)
    (ha : a = -1 - 3 * ((n + 1 : ℕ) : ℤ)) (v : H a × H a) :
    negativeAt M (a + 3) n (by omega) (row (x := x) (y := y) a v) =
    BinaryKoszul.dualRow k n
      ((negativeAt M a (n + 1) ha).prodCongr (negativeAt M a (n + 1) ha) v) := by
  rcases v with ⟨v, w⟩
  change negativeAt M (a + 3) n _ (x a v + y a w) = _
  rw [map_add]
  exact congrArg₂ (· + ·) (M.negative_x a n ha v) (M.negative_y a n ha w)

theorem negative_column (a : ℤ) (n : ℕ)
    (ha : a = -1 - 3 * ((n + 1 : ℕ) : ℤ)) (v : H a) :
    ((negativeAt M (a + 3) n (by omega)).prodCongr
      (negativeAt M (a + 3) n (by omega))) (column (x := x) (y := y) a v) =
    BinaryKoszul.dualColumn k n (negativeAt M a (n + 1) ha v) := by
  apply Prod.ext
  · exact M.negative_y a n ha v
  · change negativeAt M (a + 3) n _ (-(x a v)) = _
    rw [map_neg]
    exact congrArg Neg.neg (M.negative_x a n ha v)

include M

theorem row_surjective (a : ℤ) (ha : a ≠ -3) :
    Function.Surjective (row (x := x) (y := y) a) := by
  by_cases hp : ∃ n : ℕ, a + 3 = 3 * (n : ℤ)
  · obtain ⟨n, hn⟩ := hp
    cases n with
    | zero => omega
    | succ n =>
      exact surjective_of_chart _ (BinaryKoszul.row k n)
        ((positiveAt M a n (by omega)).prodCongr (positiveAt M a n (by omega)))
        (positiveAt M (a + 3) (n + 1) (by omega))
        (positive_row M a n (by omega)) (BinaryKoszul.row_surjective k n)
  · by_cases hn : ∃ n : ℕ, a + 3 = -1 - 3 * (n : ℤ)
    · obtain ⟨n, hn⟩ := hn
      exact surjective_of_chart _ (BinaryKoszul.dualRow k n)
        ((negativeAt M a (n + 1) (by omega)).prodCongr
          (negativeAt M a (n + 1) (by omega)))
        (negativeAt M (a + 3) n hn) (negative_row M a n (by omega))
        (BinaryKoszul.dualRow_surjective k n)
    · let : Subsingleton (H (a + 3)) := M.outside _
        (fun n h => hp ⟨n, h⟩) (fun n h => hn ⟨n, h⟩)
      intro v
      exact ⟨0, Subsingleton.elim _ _⟩

theorem column_injective (a : ℤ) (ha : a ≠ -1) :
    Function.Injective (column (x := x) (y := y) a) := by
  by_cases hp : ∃ n : ℕ, a = 3 * (n : ℤ)
  · obtain ⟨n, hn⟩ := hp
    exact injective_of_chart _ (BinaryKoszul.column k n)
      (positiveAt M a n hn)
      ((positiveAt M (a + 3) (n + 1) (by omega)).prodCongr
        (positiveAt M (a + 3) (n + 1) (by omega)))
      (positive_column M a n hn) (BinaryKoszul.column_injective k n)
  · by_cases hn : ∃ n : ℕ, a = -1 - 3 * (n : ℤ)
    · obtain ⟨n, hn⟩ := hn
      cases n with
      | zero => omega
      | succ n =>
        exact injective_of_chart _ (BinaryKoszul.dualColumn k n)
          (negativeAt M a (n + 1) (by omega))
          ((negativeAt M (a + 3) n (by omega)).prodCongr
            (negativeAt M (a + 3) n (by omega)))
          (negative_column M a n (by omega)) (BinaryKoszul.dualColumn_injective k n)
    · let : Subsingleton (H a) := M.outside _
        (fun n h => hp ⟨n, h⟩) (fun n h => hn ⟨n, h⟩)
      exact fun _ _ _ => Subsingleton.elim _ _

end ArExplicit.TateKoszul

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cones_TwoCone
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory

namespace ArExplicit.TwoCone

universe u

variable {R : Type u} [Ring R]

variable (D : Data R)

theorem d_square (n : ℕ) : (d D n).comp (d D (n+1)) = 0 :=
  coneBlock_comp_zero _ _ _ _ _ _ (firstD_square D n) (firstD_square D (n+2))
    (secondOnFirst_comm D n)

theorem d_exact (hex : ∀ n, Function.Exact (D.d (n+1)) (D.d n)) (n : ℕ) :
    Function.Exact (d D (n+1)) (d D n) :=
  coneBlock_exact _ _ _ _ _ _ (firstD_exact D hex n) (firstD_exact D hex (n+2))
    (secondOnFirst_comm D n)

end ArExplicit.TwoCone

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cones_TwoConeKoszulCoordinates
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit
universe u
variable {k : Type u} [Field k]
variable {H B D E K W : ℤ → Type u}
variable [∀ n, AddCommGroup (H n)] [∀ n, Module k (H n)]
variable [∀ n, AddCommGroup (B n)] [∀ n, Module k (B n)]
variable [∀ n, AddCommGroup (D n)] [∀ n, Module k (D n)]
variable [∀ n, AddCommGroup (E n)] [∀ n, Module k (E n)]
variable [∀ n, AddCommGroup (K n)] [∀ n, Module k (K n)]
variable [∀ n, AddCommGroup (W n)] [∀ n, Module k (W n)]
variable (F : TwoConeFiltration (k := k) B D E K W)
variable (x y : ∀ a : ℤ, H a →ₗ[k] H (a+3))

namespace TwoConeKoszulCoordinates
variable {F x y}
variable (C : TwoConeKoszulCoordinates F x y) (M : TateKoszul.Model x y)

include C M

theorem row_surjective (n : ℤ) (hn : n ≠ -1) : Function.Surjective (F.row n) := by
  intro v
  let e := TateKoszul.degreeEquiv (k := k) H (show n-2+3=n+1 by omega)
  obtain ⟨w, hw⟩ := TateKoszul.row_surjective M (n-2) (by omega) (e.symm (C.bottom (n+1) v))
  refine ⟨(C.middle n).symm w, (C.bottom (n+1)).injective ?_⟩
  rw [C.row_eq, LinearEquiv.apply_symm_apply, hw]
  exact e.apply_symm_apply _

theorem column_injective (n : ℤ) (hn : n ≠ 3) : Function.Injective (F.column n) := by
  intro v w h
  apply (C.top n).injective
  apply TateKoszul.column_injective M (n-4) (by omega)
  let e := (TateKoszul.degreeEquiv (k := k) H (show n-4+3=n+1-2 by omega)).prodCongr
    (TateKoszul.degreeEquiv (k := k) H (show n-4+3=n+1-2 by omega))
  apply e.injective
  rw [← C.column_eq, ← C.column_eq, h]

end TwoConeKoszulCoordinates
end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Evaluation_TensorFreeEvaluationCoordinates
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.Resolution.instIsScalarTowerMulOppositeBaseAlgebraSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.Resolution.simpleRightModule _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.instAdditiveModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instPreservesHomologyModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeQuotient _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.T
open scoped TensorProduct
universe u
variable {k : Type u} [Field k] (q : k) (hq : 1+q ≠ 0)

 theorem freePair_evaluation (a b c d : T k q) (s t : Resolution.Simple q) :
    ((Resolution.simpleCoordinateEquiv q hq) (b • s) • a) ⊗ₜ[k]
      ((Resolution.simpleCoordinateEquiv q hq) (d • t) • c) =
    A.barZeroCoordinate q (squareEvaluation q s t ((a ⊗ₜ[k] b) ⊗ₜ[k] (c ⊗ₜ[k] d))) := by
  simp only [squareEvaluation, LinearMap.comp_apply, TensorProduct.map_tmul,
    evaluateAtSimple, LinearMap.id_apply, simpleActionAt_apply, LinearEquiv.coe_coe,
    TensorProduct.tensorTensorTensorComm_tmul]
  change (Resolution.simpleCoordinate q (b • s) • a) ⊗ₜ[k]
    (Resolution.simpleCoordinate q (d • t) • c) = _
  erw [A.barZeroCoordinate_tmul, A.simpleCoordinate_tmul]
  exact TensorProduct.smul_tmul_smul (Resolution.simpleCoordinate q (b • s))
    (Resolution.simpleCoordinate q (d • t)) a c

end ArExplicit.T

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Fibers_FiniteFiberSides
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ArExplicit.FiniteLeftModule

open CategoryTheory

universe u

variable {k R S : Type u} [Field k] [Ring R] [Algebra k R] [Module.Finite k R]
variable [Ring S] (j : S →+* R)
variable (U₁ U₂ Y : FiniteLeftModule k R)

variable [Module.Finite S ((ModuleCat.restrictScalars j).obj (ModuleCat.of R R))]
variable [Module.Projective S ((ModuleCat.restrictScalars j).obj (ModuleCat.of R R))]

variable [Module.Finite S ((ModuleCat.restrictScalars j).obj U₁.carrier)]
variable [Module.Projective S ((ModuleCat.restrictScalars j).obj U₁.carrier)]
variable [Module.Finite S ((ModuleCat.restrictScalars j).obj U₂.carrier)]
variable [Module.Projective S ((ModuleCat.restrictScalars j).obj U₂.carrier)]

variable (g₁ : U₁.carrier ⟶ Y.carrier) (g₂ : U₂.carrier ⟶ Y.carrier)

def fiberInclusion : (fiber U₁ U₂ Y g₁ g₂).carrier ⟶ (fiberSource U₁ U₂ Y).carrier :=
  ModuleCat.ofHom (LinearMap.ker (fiberMap U₁ U₂ Y g₁ g₂).hom).subtype

def fiberProjection₁ : (fiber U₁ U₂ Y g₁ g₂).carrier ⟶ U₁.carrier :=
  fiberInclusion U₁ U₂ Y g₁ g₂ ≫ ModuleCat.ofHom (LinearMap.fst R _ _)

def fiberProjection₂ : (fiber U₁ U₂ Y g₁ g₂).carrier ⟶ U₂.carrier :=
  fiberInclusion U₁ U₂ Y g₁ g₂ ≫ ModuleCat.ofHom
    ((LinearMap.fst R _ _).comp (LinearMap.snd R _ _))

end ArExplicit.FiniteLeftModule

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Resolutions_CoverFullHomAction
attribute [-instance] _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit
open CategoryTheory
open CochainComplex CochainComplex.HomComplex CompleteComparison
universe u w
variable (k : Type u) [Field k]
variable {C : Type w} [Category.{u} C] [Preadditive C] [Linear k C]

theorem fullHom_composition_degree {K L M : CochainComplex C ℤ}
    {a b d : ℤ} (h : a+b=d) (x : CohomologyClass K L a) (y : CohomologyClass L M b) :
    (fullHomShiftedHomotopyEquiv k K M d).symm
      (ShiftedHom.comp (fullHomShiftedHomotopyEquiv k K L a x)
        (fullHomShiftedHomotopyEquiv k L M b y) (by omega : b+a=d)) =
      TateKoszul.degreeEquiv (k := k) (fun n => CohomologyClass K M n) h (fullHomProduct x y) := by
  subst d
  apply (fullHomShiftedHomotopyEquiv k K M (a+b)).injective
  simp only [LinearEquiv.apply_symm_apply]
  exact (fullHomShiftedHomotopyEquiv_product k x y).symm

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Stable_StableConnecting
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit
universe u
variable {R S₁ P₀ S₀ M B N : Type u} [Ring R]
variable [AddCommGroup S₁] [Module R S₁] [AddCommGroup P₀] [Module R P₀]
variable [AddCommGroup S₀] [Module R S₀] [AddCommGroup M] [Module R M]
variable [AddCommGroup B] [Module R B] [AddCommGroup N] [Module R N]
variable [Module.Finite R P₀] [Module.Projective R P₀]

theorem stable_connecting_congr (i : S₁ →ₗ[R] P₀) (π : P₀ →ₗ[R] S₀)
    (hπi : π.comp i = 0) (f : M →ₗ[R] B) (g : B →ₗ[R] N)
    (hf : Function.Injective f) (hg : Function.Surjective g)
    (he : LinearMap.range f = LinearMap.ker g)
    (s s' : S₀ →ₗ[R] N) (A A' : P₀ →ₗ[R] B) (t t' : S₁ →ₗ[R] M)
    (hA : g.comp A = s.comp π) (hA' : g.comp A' = s'.comp π)
    (ht : f.comp t = A.comp i) (ht' : f.comp t' = A'.comp i)
    (hs : StableHom.classOf R S₀ N s = StableHom.classOf R S₀ N s') :
    StableHom.classOf R S₁ M t = StableHom.classOf R S₁ M t' := by
  obtain ⟨Q, hQ, hRQ, hfree, hfin, j, v, hv⟩ := (StableHom.classOf_eq_iff s s').mp hs
  obtain ⟨vl, hvl⟩ := Module.projective_lifting_property g v hg
  let A₀ : P₀ →ₗ[R] B := A - A' - vl.comp (j.comp π)
  have hA₀ : g.comp A₀ = 0 := by
    ext z
    change g (A z - A' z - vl (j (π z))) = 0
    rw [map_sub, map_sub,
      show g (A z) = s (π z) from DFunLike.congr_fun hA z,
      show g (A' z) = s' (π z) from DFunLike.congr_fun hA' z,
      show g (vl (j (π z))) = v (j (π z)) from DFunLike.congr_fun hvl (j (π z))]
    change s (π z) - s' (π z) - v (j (π z)) = 0
    rw [show v (j (π z)) = s (π z) - s' (π z) from DFunLike.congr_fun hv (π z)]
    exact sub_self _
  obtain ⟨L, hL⟩ := lift_through_exact f g he A₀ hA₀
  have hdiff : L.comp i = t-t' := by
    ext z
    apply hf
    change f (L (i z)) = f (t z - t' z)
    rw [map_sub,
      show f (L (i z)) = A₀ (i z) from DFunLike.congr_fun hL (i z),
      show f (t z) = A (i z) from DFunLike.congr_fun ht z,
      show f (t' z) = A' (i z) from DFunLike.congr_fun ht' z]
    change A (i z) - A' (i z) - vl (j (π (i z))) = A (i z) - A' (i z)
    rw [show π (i z) = 0 from DFunLike.congr_fun hπi z, map_zero, map_zero, sub_zero]
  apply (StableHom.classOf_eq_iff t t').mpr
  apply (factorsThroughFiniteFree_iff_projective _).mpr
  exact ⟨P₀, inferInstance, inferInstance, inferInstance, inferInstance, i, L, hdiff⟩

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_ExternalTensorTransport
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.moduleCatBaseComm _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
namespace ArExplicit.ExternalTensor
universe u
variable (k A B : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
attribute [local instance] moduleCatBaseModule moduleCatBaseTower
variable (h : A ≃ₐ[k] A) (j : B ≃ₐ[k] B)

local notation "F" => tensorRestriction k A B h j

variable (P : ChainComplex (ModuleCat.{u} A) ℕ) (Q : ChainComplex (ModuleCat.{u} B) ℕ)
variable (e : ∀ n, P.X n →ₗ[k] P.X n) (f : ∀ n, Q.X n →ₗ[k] Q.X n)
variable (he : ∀ n a x, e n (a • x) = h a • e n x)
variable (hf : ∀ n b x, f n (b • x) = j b • f n x)

variable (hdP : ∀ n x, (P.d (n+1) n).hom (e (n+1) x) = e n ((P.d (n+1) n).hom x))
variable (hdQ : ∀ n x, (Q.d (n+1) n).hom (f (n+1) x) = f n ((Q.d (n+1) n).hom x))

include hdQ in
theorem vertical_transport (i j' n : ℕ) (hij : i+j'=n+1) :
    vertical k A B P Q i j' n ≫ transportTerm k A B h j P Q e f he hf n =
      transportSummand k A B h j P Q e f he hf i j' ≫
        (F).map (vertical k A B P Q i j' n) := by
  cases j' with
  | zero => simp only [vertical_zero, Functor.map_zero, zero_comp, comp_zero]
  | succ j' =>
    have hi : i+j'=n := by omega
    rw [vertical_succ k A B P Q i j' n hi, Linear.units_smul_comp,
      Category.assoc, inclusion_transportTerm, Functor.map_units_smul,
      Linear.comp_units_smul, Functor.map_comp, ← Category.assoc, ← Category.assoc]
    apply congrArg (fun t => ((-1 : ℤˣ)^i) • t)
    apply congrArg (fun t => t ≫ (F).map (inclusion k A B P Q i j' n hi))
    exact (tensorSemilinear_natural k A B h j (e i) (e i) (f (j'+1)) (f j')
      (he i) (he i) (hf (j'+1)) (hf j') (𝟙 (P.X i)) (Q.d (j'+1) j')
      (fun _ => rfl) (hdQ j')).symm

end ArExplicit.ExternalTensor

end

end OAI
end


