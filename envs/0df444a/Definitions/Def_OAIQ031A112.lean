-- Prove2me | Definitions.Def_OAIQ031A112
-- name    : OAIQ031A112
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T14:48:03.296265+00:00
-- url     : https://prove2.me/theorems/43ad7559-5dac-401f-8511-397c9e11f21f
-- title:
--   Definitions bundle OAIQ031A112 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 8 declarations of OpenAI's Lean: 1 definition and 7 theorems. The definitions and types are `OAI.ArExplicit.FiniteLeftModule.evaluationStableIso`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Bar_ExternalBarFreeAugmentation`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/ExternalBarFreeAugmentation.lean), [`AuslanderReiten_Bar_ExternalBarFreePure`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/ExternalBarFreePure.lean), [`AuslanderReiten_Bar_ModuleBarFreeAugmentation`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/ModuleBarFreeAugmentation.lean), [`AuslanderReiten_Ext_ExternalEvaluationCubic`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Ext/ExternalEvaluationCubic.lean), [`AuslanderReiten_Ext_ExternalEvaluationCubicSquare`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Ext/ExternalEvaluationCubicSquare.lean), [`AuslanderReiten_Modules_FiniteModuleEvaluation`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Modules/FiniteModuleEvaluation.lean), [`AuslanderReiten_Resolutions_FiniteCoverTransport`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Resolutions/FiniteCoverTransport.lean).
--
--   **Imports.** It imports the bundles `OAIQ031A091`, `OAIQ031A093`, `OAIQ031A097`, `OAIQ031A099`, `OAIQ031A100` and `OAIQ031A101` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ031A123` and `OAIQ031A124`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A091
import Definitions.Def_OAIQ031A093
import Definitions.Def_OAIQ031A097
import Definitions.Def_OAIQ031A099
import Definitions.Def_OAIQ031A100
import Definitions.Def_OAIQ031A101

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_ModuleBarFreeAugmentation
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.ModuleBar
open scoped TensorProduct
universe u
variable (k R M : Type u) [Field k] [Ring R] [Algebra k R]
variable [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M]
variable (e : M ≃ₗ[k] k)

theorem freeCoordinate_augmentation :
    (cyclicCover k R M e).comp (freeCoordinate k R M e).toLinearMap =
      differential k R M 0 := by
  apply LinearMap.ext
  intro x
  change cyclicCover k R M e (freeCoordinateScalar k R M e x) = boundary k R M 0 x
  induction x using OAI.tensorInductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]; rfl
  | tmul a m =>
    change cyclicCover k R M e (freeCoordinateScalar k R M e (a ⊗ₜ[k] m)) = a • m
    rw [freeCoordinateScalar_tmul, cyclicCover_apply]
    have hm : e m • e.symm 1 = m := by
      rw [← e.symm.map_smul]
      simp
    rw [smul_assoc, smul_comm, hm]

end ArExplicit.ModuleBar

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_ExternalBarFreeAugmentation
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.ExternalTensor
open CategoryTheory
open scoped TensorProduct

universe u
variable (k A B M N : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
variable [AddCommGroup M] [AddCommGroup N] [Module A M] [Module B N]
variable [Module k M] [Module k N] [IsScalarTower k A M] [IsScalarTower k B N]
variable (e : M ≃ₗ[k] k) (f : N ≃ₗ[k] k)

theorem factor_augmentation (R V : Type u) [Ring R] [Algebra k R]
    [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V]
    (a : V ≃ₗ[k] k) :
    (ModuleBar.freeCoordinate k R V a).toModuleIso.hom ≫
      ModuleCat.ofHom (ModuleBar.cyclicCover k R V a) =
        ModuleCat.ofHom (ModuleBar.differential k R V 0) := by
  apply ModuleCat.hom_ext
  exact ModuleBar.freeCoordinate_augmentation k R V a

end ArExplicit.ExternalTensor

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_ExternalBarFreePure
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.EnvelopingBimodule.regular_projective _root_.OAI.ArExplicit.ExternalTensor.hasHomCochainTotal _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.moduleCatBaseComm _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.ExternalBalanced
open CategoryTheory
open scoped TensorProduct
universe u
variable (k A B M N : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
variable [AddCommGroup M] [AddCommGroup N] [Module A M] [Module B N]
variable [Module k M] [Module k N] [IsScalarTower k A M] [IsScalarTower k B N]
variable (e : M ≃ₗ[k] k) (f : N ≃ₗ[k] k)
attribute [local instance 2000] moduleCatBaseModule moduleCatBaseTower
variable (K : ModuleCat.{u} (A ⊗[k] Aᵐᵒᵖ)) (L : ModuleCat.{u} (B ⊗[k] Bᵐᵒᵖ))
variable (X : ModuleCat.{u} A) (Y : ModuleCat.{u} B)
variable (g : (EnvelopingBimodule.evaluationFunctor k A X).obj K ⟶ ModuleBar.moduleObject k A M 1)
  (h : (EnvelopingBimodule.evaluationFunctor k B Y).obj L ⟶ ModuleBar.moduleObject k B N 1)

theorem postShuffle_barFree_pure (a : EnvelopingBimodule k A K)
    (b : EnvelopingBimodule k B L) (x : X) (y : Y) :
    ((shuffle k A B K L X Y).toModuleIso.hom ≫ ExternalTensor.mapHom k A B g h ≫
      ExternalTensor.barFreeCoordinate k A B M N e f)
      (BalancedTensor.tmul
        ((bimoduleCoordinates k A B K L).symm (a ⊗ₜ[k] b))
        ((ExternalTensor.moduleScalarCoordinates k A B X Y).symm (x ⊗ₜ[k] y))) =
      ((g ≫ (ModuleBar.freeCoordinate k A M e).toModuleIso.hom) (BalancedTensor.tmul a x)) ⊗ₜ[k]
        ((h ≫ (ModuleBar.freeCoordinate k B N f).toModuleIso.hom) (BalancedTensor.tmul b y)) :=
  (postShuffle_pure k A B K L X Y (ModuleBar.moduleObject k A M 1)
    (ModuleBar.moduleObject k B N 1) (ModuleCat.of (A ⊗[k] B) (A ⊗[k] B)) g h
    (ExternalTensor.barFreeCoordinate k A B M N e f) a b x y).trans
      (ExternalTensor.barFreeCoordinate_tmul k A B M N e f
        (g (BalancedTensor.tmul a x)) (h (BalancedTensor.tmul b y)))

theorem postShuffle_barFree_values (a : EnvelopingBimodule k A K)
    (b : EnvelopingBimodule k B L) (x : X) (y : Y) (r : A) (s : B)
    (hg : (g ≫ (ModuleBar.freeCoordinate k A M e).toModuleIso.hom)
      (BalancedTensor.tmul a x) = r)
    (hh : (h ≫ (ModuleBar.freeCoordinate k B N f).toModuleIso.hom)
      (BalancedTensor.tmul b y) = s) :
    ((shuffle k A B K L X Y).toModuleIso.hom ≫ ExternalTensor.mapHom k A B g h ≫
      ExternalTensor.barFreeCoordinate k A B M N e f)
      (BalancedTensor.tmul
        ((bimoduleCoordinates k A B K L).symm (a ⊗ₜ[k] b))
        ((ExternalTensor.moduleScalarCoordinates k A B X Y).symm (x ⊗ₜ[k] y))) =
      r ⊗ₜ[k] s := by
  rw [postShuffle_barFree_pure, hg, hh]

end ArExplicit.ExternalBalanced

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Ext_ExternalEvaluationCubicSquare
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.EnvelopingBimodule.regular_projective _root_.OAI.ArExplicit.ExternalTensor.hasHomCochainTotal _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.moduleCatBaseComm _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.ExternalBalanced
open CategoryTheory
open scoped TensorProduct
universe u
variable (k A B : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
attribute [local instance 2000] moduleCatBaseModule moduleCatBaseTower
variable (X : ModuleCat.{u} A) (Y : ModuleCat.{u} B)
variable (P : ChainComplex (ModuleCat.{u} (A ⊗[k] Aᵐᵒᵖ)) ℕ)
  (Q : ChainComplex (ModuleCat.{u} (B ⊗[k] Bᵐᵒᵖ)) ℕ)
local notation "Ae" => A ⊗[k] Aᵐᵒᵖ
local notation "Be" => B ⊗[k] Bᵐᵒᵖ
local notation "E" => productEvaluation k A B X Y
local notation "PE" => factorEvaluation k X P

theorem secondCubic_summand_natural (i j n : ℕ) (h : i+j=n) (h' : i+(j+3)=n+3)
    (r : Q.X (j+3) ⟶ Q.X j) :
    (E).map (ExternalTensor.mapHom k Ae Be (𝟙 (P.X i)) r) ≫
      (summandEvaluationIso k A B X Y P Q n ⟨(i,j),h⟩).hom =
    (summandEvaluationIso k A B X Y P Q (n+3) ⟨(i,j+3),h'⟩).hom ≫
      ExternalTensor.mapHom k A B (𝟙 ((PE).X i))
        ((EnvelopingBimodule.evaluationFunctor k B Y).map r) := by
  have hs := shuffle_natural_fixed k A B X Y (𝟙 (P.X i)) r
  rw [(EnvelopingBimodule.evaluationFunctor k A X).map_id] at hs
  convert! hs using 1
  all_goals try with_reducible_and_instances rfl

end ArExplicit.ExternalBalanced

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Ext_ExternalEvaluationCubic
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ExternalTensor.hasHomCochainTotal _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.moduleCatBaseComm _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.ExternalBalanced
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u
variable (k A B : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
attribute [local instance 2000] moduleCatBaseModule moduleCatBaseTower
variable (X : ModuleCat.{u} A) (Y : ModuleCat.{u} B)
variable (P : ChainComplex (ModuleCat.{u} (A ⊗[k] Aᵐᵒᵖ)) ℕ)
  (Q : ChainComplex (ModuleCat.{u} (B ⊗[k] Bᵐᵒᵖ)) ℕ)
variable (p : ∀ n, P.X (n+3) ⟶ P.X n) (r : ∀ n, Q.X (n+3) ⟶ Q.X n)
local notation "Ae" => A ⊗[k] Aᵐᵒᵖ
local notation "Be" => B ⊗[k] Bᵐᵒᵖ
local notation "E" => productEvaluation k A B X Y
local notation "PE" => factorEvaluation k X P
local notation "QE" => factorEvaluation k Y Q

theorem secondCubic_totalEvaluation (n : ℕ) :
    (E).map (ModuleCat.ofHom (ExternalTensor.secondCubic k Ae Be P Q r n)) ≫
      (totalEvaluationTermIso k A B X Y P Q n).hom =
    (totalEvaluationTermIso k A B X Y P Q (n+3)).hom ≫
      ModuleCat.ofHom (ExternalTensor.secondCubic k A B PE QE
        (evaluatedSecondComparison k B Y Q r) n) := by
  apply evaluatedTotal_hom_ext k A B X Y P Q
  intro i j hij
  have hpost := post_natural (inclusion_totalEvaluationTermIso k A B X Y P Q i j (n+3) hij)
    (ModuleCat.ofHom (ExternalTensor.secondCubic k A B PE QE (evaluatedSecondComparison k B Y Q r) n))
  erw [hpost, ExternalTensor.inclusion_secondCubic k A B PE QE (evaluatedSecondComparison k B Y Q r) i j n hij]
  erw [← Category.assoc, ← (E).map_comp, ExternalTensor.inclusion_secondCubic k Ae Be P Q r i j n hij]
  by_cases hj : j < 3
  · have hj : j=0 ∨ j=1 ∨ j=2 := by omega
    rcases hj with rfl | rfl | rfl <;>
      change (E).map (0 : _ ⟶ _) ≫ _ = _ ≫ (0 : _ ⟶ _)
    all_goals erw [Functor.map_zero, zero_comp, comp_zero]
  · obtain ⟨a,ha⟩ : ∃ a, j=a+3 := ⟨j-3, by omega⟩
    subst j
    erw [ExternalTensor.secondCubicEntry_high k Ae Be P Q r i a n hij,
      ExternalTensor.secondCubicEntry_high k A B PE QE (evaluatedSecondComparison k B Y Q r) i a n hij,
      (E).map_comp, Category.assoc, inclusion_totalEvaluationTermIso k A B X Y P Q i a n (by omega)]
    erw [← Category.assoc, ← Category.assoc]
    exact congrArg (fun z => z ≫ ExternalTensor.inclusion k A B PE QE i a n (by omega))
      (secondCubic_summand_natural k A B X Y P Q i a n (by omega) hij (r a))

end ArExplicit.ExternalBalanced

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Modules_FiniteModuleEvaluation
attribute [-instance] _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Pretriangulated
open scoped TensorProduct

namespace ArExplicit.FiniteLeftModule
universe u
variable {k R : Type u} [Field k] [Ring R] [Algebra k R] [Module.Finite k R]
variable (X : FiniteLeftModule k R)
variable (M : FiniteLeftModule k (R ⊗[k] Rᵐᵒᵖ))

variable {M N P : FiniteLeftModule k (R ⊗[k] Rᵐᵒᵖ)}

def evaluationStableIso (e : StableIsomorphism (R ⊗[k] Rᵐᵒᵖ) M.carrier N.carrier) :
    StableIsomorphism R (evaluated X M).carrier (evaluated X N).carrier where
  hom := EnvelopingBimodule.stableEvaluation X.carrier e.hom
  inv := EnvelopingBimodule.stableEvaluation X.carrier e.inv
  hom_inv_id := by
    erw [← EnvelopingBimodule.stableEvaluation_comp, e.hom_inv_id]
    exact EnvelopingBimodule.stableEvaluation_id X.carrier
  inv_hom_id := by
    erw [← EnvelopingBimodule.stableEvaluation_comp, e.inv_hom_id]
    exact EnvelopingBimodule.stableEvaluation_id X.carrier

end ArExplicit.FiniteLeftModule

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Resolutions_FiniteCoverTransport
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
universe u v w
section General
variable (k : Type u) [CommRing k]
variable {C : Type w} [Category.{v} C] [Preadditive C] [Linear k C]
variable {K L : CochainComplex C ℤ}

theorem fullHomShiftedHomotopyEquiv_ofHom (f : K ⟶ L) :
    fullHomShiftedHomotopyEquiv k K L 0 (CohomologyClass.mk (Cocycle.ofHom f)) =
      (HomotopyCategory.quotient C _).map f ≫
        (shiftFunctorZero (HomotopyCategory C (ComplexShape.up ℤ)) ℤ).inv.app
          ((HomotopyCategory.quotient C _).obj L) := by
  have h : Cocycle.equivHomShift.symm (Cocycle.ofHom f) =
      ShiftedHom.mk₀ (0 : ℤ) rfl f := by
    apply HomologicalComplex.Hom.ext
    funext i
    simp only [cocycleHom_component, Cocycle.ofHom_coe]
    simp only [ShiftedHom.mk₀, HomologicalComplex.comp_f, CategoryTheory.shiftFunctorZero',
      eqToIso_refl, Iso.trans_inv, Iso.refl_inv,
      CochainComplex.shiftFunctorZero_inv_app_f, Category.comp_id]
    change (Cochain.ofHom f).v i (i+0) rfl =
      f.f i ≫ (L.XIsoOfEq (show i=i+0 by omega)).hom
    simpa only [Cochain.ofHom_v] using
      (Cochain.v_comp_XIsoOfEq_hom (Cochain.ofHom f) i i (i+0) (add_zero i) (by omega)).symm
  rw [fullHomShiftedHomotopyEquiv_mk, h]
  change (ShiftedHom.mk₀ (0 : ℤ) rfl f).map (HomotopyCategory.quotient C _) = _
  rw [ShiftedHom.map_mk₀]
  simp [ShiftedHom.mk₀, CategoryTheory.shiftFunctorZero']
end General

open scoped ModuleCat.Algebra
end ArExplicit

end

end OAI
end


