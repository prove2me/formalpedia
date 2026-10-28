-- Prove2me | Definitions.Def_OAIQ031A089
-- name    : OAIQ031A089
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T14:30:42.595517+00:00
-- url     : https://prove2.me/theorems/0fbe2a88-8fa5-43d8-89cd-6e96e732c44f
-- title:
--   Definitions bundle OAIQ031A089 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 28 declarations of OpenAI's Lean: 10 definitions, 3 instances and 15 theorems. The definitions and types are `OAI.ArExplicit.TriangularE`, `OAI.ArExplicit.TriangularInduction.eFunctor`, `OAI.ArExplicit.TriangularInduction.eHom`, `OAI.ArExplicit.TriangularInduction.eHomEquiv`, `OAI.ArExplicit.TriangularInduction.eMap`, `OAI.ArExplicit.TriangularInduction.jHom`, `OAI.ArExplicit.TriangularInduction.jHomEquiv`, `OAI.ArExplicit.TriangularInduction.jMap`, `OAI.ArExplicit.TriangularJ`, `OAI.ArExplicit.TwoCone.FirstCokernel`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Algebras_FrobeniusOpposite`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Algebras/FrobeniusOpposite.lean), [`AuslanderReiten_Algebras_TSimpleTwist`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Algebras/TSimpleTwist.lean), [`AuslanderReiten_Cones_TwoConeProjective`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Cones/TwoConeProjective.lean), [`AuslanderReiten_Resolutions_CoverFullHomAction`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Resolutions/CoverFullHomAction.lean), [`AuslanderReiten_Triangular_TriangularCategory`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Triangular/TriangularCategory.lean), [`AuslanderReiten_Triangular_TriangularFunctor`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Triangular/TriangularFunctor.lean), [`AuslanderReiten_Triangular_TriangularHom`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Triangular/TriangularHom.lean), [`AuslanderReiten_Triangular_TriangularInduction`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Triangular/TriangularInduction.lean), [`AuslanderReiten_Triangular_TriangularModule`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Triangular/TriangularModule.lean).
--
--   **Imports.** It imports the bundles `OAIQ031A062`, `OAIQ031A068`, `OAIQ031A071`, `OAIQ031A074` and `OAIQ031A075` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ031A102`, `OAIQ031A103` and `OAIQ031A104`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A062
import Definitions.Def_OAIQ031A068
import Definitions.Def_OAIQ031A071
import Definitions.Def_OAIQ031A074
import Definitions.Def_OAIQ031A075

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Algebras_FrobeniusOpposite
attribute [-instance] _root_.OAI.ArExplicit.A.instIsTwoSidedAugmentationIdeal _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.Resolution.augmentation_epi _root_.OAI.ArExplicit.Resolution.complex_projective _root_.OAI.ArExplicit.Resolution.complex_scalar _root_.OAI.ArExplicit.Resolution.instFiniteSubtypeBaseAlgebraMemSubmoduleF _root_.OAI.ArExplicit.Resolution.instIsScalarTowerMulOppositeBaseAlgebraSimple _root_.OAI.ArExplicit.Resolution.instIsScalarTowerTSimple _root_.OAI.ArExplicit.Resolution.instModuleTSimple _root_.OAI.ArExplicit.Resolution.instProjectiveBaseAlgebraSubtypeMemSubmoduleE _root_.OAI.ArExplicit.Resolution.instProjectiveBaseAlgebraSubtypeMemSubmoduleF _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.Resolution.simpleRightModule _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.instAdditiveModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instPreservesHomologyModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeQuotient _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ArExplicit

variable (k : Type*) [Field k] (q : k)

instance instInjectiveMulOppositeA : Module.Injective (A k q)ᵐᵒᵖ (A k q)ᵐᵒᵖ :=
  (AOppositeFrobeniusTrace k q).regular_injective

open scoped TensorProduct

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Algebras_TSimpleTwist
attribute [-instance] _root_.OAI.ArExplicit.A.instIsTwoSidedAugmentationIdeal _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.Resolution.instIsScalarTowerMulOppositeBaseAlgebraSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.Resolution.simpleRightModule _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.instAdditiveModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instIsScalarTowerTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instPreservesHomologyModuleCatTrivialExtensionInflate _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeCoinduced _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionMulOppositeQuotient _root_.OAI.ArExplicit.TrivialInduction.instSMulCommClassTrivialExtensionQuotient _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.instInjectiveA _root_.OAI.ArExplicit.instInjectiveMulOppositeA _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ArExplicit.T

variable {k : Type*} [Field k] (q : k)

theorem p_twist_simple (H : kˣ) (a b c : T k q) (s : Resolution.Simple q) :
    CocycleData.p q (TrivialExtension.twist H a) (TrivialExtension.twist H b)
      (TrivialExtension.twist H c) • s =
      (H : k) • (CocycleData.p q a b c • s) := by
  rw [CocycleData.p_twist, smul_assoc, twist_smul_simple]

theorem p_inverse_twist_simple (H : kˣ) (a b c : T k q) (s : Resolution.Simple q) :
    CocycleData.p q ((TrivialExtension.twist H).symm a) ((TrivialExtension.twist H).symm b)
      ((TrivialExtension.twist H).symm c) • s =
      ((H⁻¹ : kˣ) : k) • (CocycleData.p q a b c • s) := by
  have hi (x : T k q) : (TrivialExtension.twist H).symm x = TrivialExtension.twist H⁻¹ x := rfl
  rw [hi a, hi b, hi c]
  have hp := p_twist_simple q H⁻¹ a b c s
  convert! hp using 1
  all_goals try with_reducible_and_instances rfl

end ArExplicit.T

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cones_TwoConeProjective
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

abbrev FirstCokernel (n : ℕ) := firstTerm D n ⧸ LinearMap.range (firstD D n)

end ArExplicit.TwoCone

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

variable (K : CochainComplex C ℤ)
variable (Y : ℕ → HomotopyCategory C (ComplexShape.up ℤ)) (s : ∀ n, Y n ≅ (Y (n+1))⟦(1 : ℤ)⟧)
variable (u : ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K) ≅ Y 0) (c : ∀ n, Y (n+3) ⟶ Y n)

theorem coverFullHom_action
    (hs : ∀ n, c n ≫ (s n).hom = (s (n+3)).hom ≫ (c (n+1))⟦(1 : ℤ)⟧')
    (p : CohomologyClass K K 3)
    (hp : fullHomShiftedHomotopyEquiv k K K 3 p = coverCubic Y s u c)
    (n : ℕ) (a : ℤ) (v : ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K) ⟶ (Y (n+3))⟦a⟧) :
    coverFullHomEquiv k K Y s u n a (v ≫ (c n)⟦a⟧') =
      TateKoszul.degreeEquiv (k := k) (fun i => CohomologyClass K K i)
        (by omega : (a-((n+3 : ℕ) : ℤ))+3=a-(n : ℤ))
        (fullHomProduct (coverFullHomEquiv k K Y s u (n+3) a v) p) := by
  unfold coverFullHomEquiv
  simp only [LinearEquiv.trans_apply, shiftedNegativeHomEquiv_comp]
  rw [coverCubic_action Y s u c hs n a v, ← hp]
  simpa only [LinearEquiv.apply_symm_apply] using
    (fullHom_composition_degree k (K := K) (L := K) (M := K)
      (a := a-((n+3 : ℕ) : ℤ)) (b := 3) (d := a-(n : ℤ)) (by omega)
      ((fullHomShiftedHomotopyEquiv k K K (a-((n+3 : ℕ) : ℤ))).symm
        (ShiftedHom.comp v
          (negativeShiftIso ((n+3 : ℕ) : ℤ) (basedIteration Y s u (n+3))).hom (by omega))) p)

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Triangular_TriangularModule
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.EnvelopingBimodule.regular_projective _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit

variable (k R F M N : Type*) [CommRing k] [Ring R]
variable [AddCommGroup F] [Module k F] [Module R F] [Module Rᵐᵒᵖ F]
variable [SMulCommClass k R F] [SMulCommClass R Rᵐᵒᵖ F]
variable [AddCommGroup M] [Module k M] [Module R M]
variable [AddCommGroup N] [Module R N]

namespace TriangularModule

variable {k R F M N}
variable (φ : BalancedTensor k R F M →ₗ[R] N)

section Scalars

variable [Module k N]

variable [Algebra k R] [IsScalarTower k R F] [IsScalarTower k Rᵐᵒᵖ F]
variable [SMulCommClass k Rᵐᵒᵖ F]
variable [IsScalarTower k R M] [IsScalarTower k R N]

instance instIsScalarTowerTriangular : IsScalarTower k (Triangular R F) (TriangularModule k R F M N φ) where
  smul_assoc c a x := by
    ext
    · exact smul_assoc c a.top x.top
    · simp only [bottom_smul, Triangular.off_smul, Triangular.bottom_smul,
        bottom_scalar, BalancedTensor.scalar_tmul, LinearMap.map_smul_of_tower, smul_assoc, smul_add]

end Scalars

end TriangularModule
end ArExplicit

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Triangular_TriangularHom
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.EnvelopingBimodule.regular_projective _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit.TriangularModule

variable {k R F M N M' N' : Type*} [CommRing k] [Ring R]
variable [AddCommGroup F] [Module k F] [Module R F] [Module Rᵐᵒᵖ F]
variable [SMulCommClass k R F] [SMulCommClass R Rᵐᵒᵖ F]
variable [AddCommGroup M] [Module k M] [Module R M]
variable [AddCommGroup N] [Module R N]
variable [AddCommGroup M'] [Module k M'] [Module R M']
variable [AddCommGroup N'] [Module R N']
variable {φ : BalancedTensor k R F M →ₗ[R] N}
variable {ψ : BalancedTensor k R F M' →ₗ[R] N'}

variable (g : TriangularModule k R F M N φ →ₗ[Triangular R F] TriangularModule k R F M' N' ψ)

@[ext] theorem hom_ext
    (g' : TriangularModule k R F M N φ →ₗ[Triangular R F] TriangularModule k R F M' N' ψ)
    (ht : topMap g = topMap g') (hb : bottomMap g = bottomMap g') : g = g' := by
  apply LinearMap.ext
  intro x
  ext
  · rw [← top_of_map g x, ← top_of_map g' x]
    exact congrArg (fun a : M →ₗ[R] M' => a x.top) ht
  · rw [← bottom_of_map g x, ← bottom_of_map g' x]
    exact congrArg (fun b : N →ₗ[R] N' => b x.bottom) hb

end ArExplicit.TriangularModule

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Triangular_TriangularInduction
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.EnvelopingBimodule.regular_projective _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit

variable (k R F : Type*) [CommRing k] [Ring R] [Algebra k R]
variable [AddCommGroup F] [Module k F] [Module R F] [Module Rᵐᵒᵖ F]
variable [SMulCommClass k R F] [SMulCommClass R Rᵐᵒᵖ F]
variable (M : Type*) [AddCommGroup M] [Module k M] [Module R M]

abbrev TriangularE := TriangularModule k R F M (BalancedTensor k R F M) LinearMap.id

variable (N : Type*) [AddCommGroup N] [Module R N]

abbrev TriangularJ := TriangularModule k R F PUnit.{1} N 0

namespace TriangularInduction

variable {k R F M N}
variable {M' N' : Type*} [AddCommGroup M'] [Module k M'] [Module R M']
variable [AddCommGroup N'] [Module R N']
variable {ψ : BalancedTensor k R F M' →ₗ[R] N'}
variable [IsScalarTower k R M] [IsScalarTower k R M']

def eHom (a : M →ₗ[R] M') :
    TriangularE k R F M →ₗ[Triangular R F] TriangularModule k R F M' N' ψ :=
  TriangularModule.hom a (ψ.comp (BalancedTensor.mapRight a)) (by intros; rfl)

def jHom (b : N →ₗ[R] N') :
    TriangularJ k R F N →ₗ[Triangular R F] TriangularModule k R F M' N' ψ :=
  TriangularModule.hom 0 b (by intros; simp)

theorem eHom_topMap
    (g : TriangularE k R F M →ₗ[Triangular R F] TriangularModule k R F M' N' ψ) :
    eHom (TriangularModule.topMap g) = g := by
  apply TriangularModule.hom_ext
  · ext m; rfl
  · apply BalancedTensor.leftHom_ext
    intro f m
    exact (TriangularModule.compatibility g f m).symm

omit [Algebra k R] [IsScalarTower k R M'] in
theorem jHom_bottomMap
    (g : TriangularJ k R F N →ₗ[Triangular R F] TriangularModule k R F M' N' ψ) :
    jHom (TriangularModule.bottomMap g) = g := by
  apply TriangularModule.hom_ext
  · apply Subsingleton.elim
  · ext n; rfl

variable [Module k N] [Module k N']
variable [IsScalarTower k R F] [IsScalarTower k Rᵐᵒᵖ F]
variable [SMulCommClass k Rᵐᵒᵖ F]
variable [IsScalarTower k R N] [IsScalarTower k R N']
variable [SMulCommClass k R M'] [SMulCommClass k R N']

def eHomEquiv :
    (TriangularE k R F M →ₗ[Triangular R F] TriangularModule k R F M' N' ψ) ≃ₗ[k]
      (M →ₗ[R] M') where
  toFun := TriangularModule.topMap
  invFun := eHom
  left_inv := eHom_topMap
  right_inv a := by ext m; rfl
  map_add' g h := by ext m; rfl
  map_smul' c g := by ext m; rfl

def jHomEquiv :
    (TriangularJ k R F N →ₗ[Triangular R F] TriangularModule k R F M' N' ψ) ≃ₗ[k]
      (N →ₗ[R] N') where
  toFun := TriangularModule.bottomMap
  invFun := jHom
  left_inv := jHom_bottomMap
  right_inv a := by ext n; rfl
  map_add' g h := by ext n; rfl
  map_smul' c g := by ext n; rfl

end TriangularInduction
end ArExplicit

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Triangular_TriangularFunctor
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.EnvelopingBimodule.regular_projective _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ArExplicit.TriangularInduction

variable {k R F : Type*} [CommRing k] [Ring R] [Algebra k R]
variable [AddCommGroup F] [Module k F] [Module R F] [Module Rᵐᵒᵖ F]
variable [SMulCommClass k R F] [SMulCommClass R Rᵐᵒᵖ F]
variable [IsScalarTower k R F] [IsScalarTower k Rᵐᵒᵖ F] [SMulCommClass k Rᵐᵒᵖ F]
variable {M N L : Type*}
variable [AddCommGroup M] [Module k M] [Module R M] [IsScalarTower k R M]
variable [AddCommGroup N] [Module k N] [Module R N] [IsScalarTower k R N]
variable [AddCommGroup L] [Module k L] [Module R L] [IsScalarTower k R L]

def eMap (f : M →ₗ[R] N) : TriangularE k R F M →ₗ[Triangular R F] TriangularE k R F N := eHom f

def jMap (f : M →ₗ[R] N) : TriangularJ k R F M →ₗ[Triangular R F] TriangularJ k R F N := jHom f

omit [IsScalarTower k R F] [IsScalarTower k Rᵐᵒᵖ F] [SMulCommClass k Rᵐᵒᵖ F] in
@[simp] theorem eMap_top (f : M →ₗ[R] N) (x : TriangularE k R F M) :
    (eMap f x).top = f x.top := rfl

omit [IsScalarTower k R F] [IsScalarTower k Rᵐᵒᵖ F] [SMulCommClass k Rᵐᵒᵖ F] in
@[simp] theorem eMap_bottom (f : M →ₗ[R] N) (x : TriangularE k R F M) :
    (eMap f x).bottom = BalancedTensor.mapRight (S := R) f x.bottom := rfl

omit [Algebra k R] [IsScalarTower k R F] [IsScalarTower k Rᵐᵒᵖ F]
  [SMulCommClass k Rᵐᵒᵖ F] [Module k M] [IsScalarTower k R M]
  [Module k N] [IsScalarTower k R N] in
@[simp] theorem jMap_bottom (f : M →ₗ[R] N) (x : TriangularJ k R F M) :
    (jMap f x).bottom = f x.bottom := rfl

@[simp] theorem eMap_id : eMap (k := k) (F := F) (LinearMap.id : M →ₗ[R] M) = LinearMap.id := by
  apply eHomEquiv.injective
  ext m
  rfl

@[simp] theorem eMap_comp (f : M →ₗ[R] N) (g : N →ₗ[R] L) :
    eMap (k := k) (F := F) (g.comp f) = (eMap g).comp (eMap f) := by
  apply eHomEquiv.injective
  ext m
  rfl

@[simp] theorem jMap_id : jMap (k := k) (F := F) (LinearMap.id : M →ₗ[R] M) = LinearMap.id := by
  apply jHomEquiv.injective
  ext m
  rfl

omit [Module k M] [IsScalarTower k R M] [Module k N] [IsScalarTower k R N] in
@[simp] theorem jMap_comp (f : M →ₗ[R] N) (g : N →ₗ[R] L) :
    jMap (k := k) (F := F) (g.comp f) = (jMap g).comp (jMap f) := by
  apply jHomEquiv.injective
  ext m
  rfl

@[simp] theorem eMap_zero : eMap (k := k) (F := F) (0 : M →ₗ[R] N) = 0 := by
  apply eHomEquiv.injective
  ext m
  rfl

omit [Module k M] [IsScalarTower k R M] in
@[simp] theorem jMap_zero : jMap (k := k) (F := F) (0 : M →ₗ[R] N) = 0 := by
  apply jHomEquiv.injective
  ext m
  rfl

end ArExplicit.TriangularInduction

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Triangular_TriangularCategory
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.EnvelopingBimodule.regular_projective _root_.OAI.ArExplicit.ExternalTensor.hasHomCochainTotal _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ArExplicit.TriangularInduction

open CategoryTheory
open CochainComplex CochainComplex.HomComplex

universe u

variable (k R F : Type u) [Field k] [Ring R] [Algebra k R]
variable [AddCommGroup F] [Module k F] [Module R F] [Module Rᵐᵒᵖ F]
variable [SMulCommClass k R F] [SMulCommClass R Rᵐᵒᵖ F]
variable [IsScalarTower k R F] [IsScalarTower k Rᵐᵒᵖ F] [SMulCommClass k Rᵐᵒᵖ F]

attribute [local instance] moduleCatBaseModule moduleCatBaseTower

def eFunctor : ModuleCat.{u} R ⥤ ModuleCat.{u} (Triangular R F) where
  obj M := ModuleCat.of _ (TriangularE k R F M)
  map f := ModuleCat.ofHom (eMap f.hom)
  map_id M := by apply ModuleCat.hom_ext; exact eMap_id
  map_comp f g := by apply ModuleCat.hom_ext; exact eMap_comp f.hom g.hom

instance instAdditiveModuleCatTriangularEFunctor : (eFunctor k R F).Additive where
  map_add := by
    intro X Y f g
    apply ModuleCat.hom_ext
    apply eHomEquiv.injective
    ext m
    rfl

end ArExplicit.TriangularInduction

end

end OAI
end


