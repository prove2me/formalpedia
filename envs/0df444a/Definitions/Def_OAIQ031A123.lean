-- Prove2me | Definitions.Def_OAIQ031A123
-- name    : OAIQ031A123
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T15:04:01.13201+00:00
-- url     : https://prove2.me/theorems/960b0fb9-3461-444f-9c93-6b3f9edc3f98
-- title:
--   Definitions bundle OAIQ031A123 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 9 declarations of OpenAI's Lean: 2 definitions and 7 theorems. The definitions and types are `OAI.ArExplicit.ExternalBalanced.barCubic`, `OAI.ArExplicit.ExternalTensor.homKunnethCoordinates`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Bar_ExternalBarCyclicCoordinate`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/ExternalBarCyclicCoordinate.lean), [`AuslanderReiten_Bar_ExternalBarEvaluation`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/ExternalBarEvaluation.lean), [`AuslanderReiten_Bar_ExternalBarFreeAugmentation`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/ExternalBarFreeAugmentation.lean), [`AuslanderReiten_Bar_ExternalBarTotalFree`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Bar/ExternalBarTotalFree.lean), [`AuslanderReiten_Ext_ExtKunnethMap`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Ext/ExtKunnethMap.lean), [`AuslanderReiten_Ext_ExternalEvaluationAugmentation`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Ext/ExternalEvaluationAugmentation.lean), [`AuslanderReiten_Homology_CoefficientComplexValues`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Homology/CoefficientComplexValues.lean).
--
--   **Imports.** It imports the bundles `OAIQ031A108`, `OAIQ031A109`, `OAIQ031A110`, `OAIQ031A111` and `OAIQ031A112` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ031A143`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A108
import Definitions.Def_OAIQ031A109
import Definitions.Def_OAIQ031A110
import Definitions.Def_OAIQ031A111
import Definitions.Def_OAIQ031A112

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_ExternalBarFreeAugmentation
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ExternalTensor.hasHomCochainTotal _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.moduleCatBaseComm _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
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

theorem barFreeCoordinate_augmentation :
    barFreeCoordinate k A B M N e f ≫ barCyclicCover k A B M N e f =
      mapHom k A B (ModuleCat.ofHom (ModuleBar.differential k A M 0))
        (ModuleCat.ofHom (ModuleBar.differential k B N 0)) := by
  have h := iso_cancel_pair
    (mapHom k A B (ModuleBar.freeCoordinate k A M e).toModuleIso.hom
      (ModuleBar.freeCoordinate k B N f).toModuleIso.hom)
    (canonicalTensorIso k A B A B) (regularEquiv k A B).toModuleIso
    (mapHom k A B (ModuleCat.ofHom (ModuleBar.cyclicCover k A M e))
      (ModuleCat.ofHom (ModuleBar.cyclicCover k B N f)))
  have hcomp := (mapHom_comp k A B
    (ModuleBar.freeCoordinate k A M e).toModuleIso.hom
    (ModuleCat.ofHom (ModuleBar.cyclicCover k A M e))
    (ModuleBar.freeCoordinate k B N f).toModuleIso.hom
    (ModuleCat.ofHom (ModuleBar.cyclicCover k B N f))).symm
  exact h.trans (hcomp.trans (congrArg₂ (mapHom k A B)
    (factor_augmentation k A M e) (factor_augmentation k B N f)))

end ArExplicit.ExternalTensor

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_ExternalBarCyclicCoordinate
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ExternalTensor.hasHomCochainTotal _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.moduleCatBaseComm _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
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

theorem barCyclicCover_tmul (a : A) (b : B) :
    barCyclicCover k A B M N e f (a ⊗ₜ[k] b) =
      canonicalTmul k A B M N (a • e.symm 1) (b • f.symm 1) := by
  change (mapHom k A B (ModuleCat.ofHom (ModuleBar.cyclicCover k A M e))
    (ModuleCat.ofHom (ModuleBar.cyclicCover k B N f)))
      ((canonicalTensorIso k A B A B).inv (a ⊗ₜ[k] b)) = _
  rw [canonicalTensorIso_inv_tmul]
  rfl

theorem barCyclicCover_eq :
    barCyclicCover k A B M N e f =
      ModuleCat.ofHom (tensorCyclicCover k A B M N e f) ≫
        (canonicalTensorIso k A B M N).inv := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  induction z using OAI.tensorInductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a b =>
    rw [barCyclicCover_tmul]
    change canonicalTmul k A B M N (a • e.symm 1) (b • f.symm 1) =
      (canonicalTensorIso k A B M N).inv ((a ⊗ₜ[k] b) •
        (show moduleObject k A B M N from e.symm 1 ⊗ₜ[k] f.symm 1))
    change canonicalTmul k A B M N (a • e.symm 1) (b • f.symm 1) =
      (canonicalTensorIso k A B M N).inv ((a • e.symm 1) ⊗ₜ[k] (b • f.symm 1))
    exact (canonicalTensorIso_inv_tmul k A B M N (a • e.symm 1) (b • f.symm 1)).symm

end ArExplicit.ExternalTensor

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_ExternalBarEvaluation
attribute [-instance] _root_.OAI.ArExplicit.AbsoluteBar.twistInvPair _root_.OAI.ArExplicit.AbsoluteBar.twistInvPairSymm _root_.OAI.ArExplicit.AbsoluteBar.twistedBaseModule _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
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
variable [CharP k 2] [AddCommGroup M] [AddCommGroup N] [Module A M] [Module B N]
variable [Module k M] [Module k N] [IsScalarTower k A M] [IsScalarTower k B N]
local notation "P" => AbsoluteBar.complex k A

def barCubic (p : AbsoluteBar.Cochain3 k A) (n : ℕ) : (P).X (n+3) ⟶ (P).X n :=
  ConcreteCategory.ofHom (C := ModuleCat (A ⊗[k] Aᵐᵒᵖ))
    (AbsoluteBar.suffixComparisonMap k A p n)

end ArExplicit.ExternalBalanced

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_ExternalBarTotalFree
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ExternalTensor.hasHomCochainTotal _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.moduleCatBaseComm _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
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
variable [Module k M] [Module k N] [IsScalarTower k A M] [IsScalarTower k B N] [CharP k 2]
variable (e : M ≃ₗ[k] k) (f : N ≃ₗ[k] k)

theorem barTotalFreeCoordinate_augmentation :
    barTotalFreeCoordinate k A B M N e f ≫ barCyclicCover k A B M N e f =
      (augmentation k A B (ModuleBar.nativeResolution k A M)
        (ModuleBar.nativeResolution k B N)).f 0 := by
  apply hom_ext k A B (ModuleBar.nativeResolution k A M).complex
    (ModuleBar.nativeResolution k B N).complex
  intro i j h
  have hi : i=0 := by omega
  have hj : j=0 := by omega
  subst i; subst j
  erw [← Category.assoc, inclusion_barTotalFreeCoordinate,
    barFreeCoordinate_augmentation k A B M N e f, inclusion_augmentation]
  rfl

end ArExplicit.ExternalTensor

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Ext_ExtKunnethMap
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.moduleCatBaseComm _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian HomologicalComplex
open scoped TensorProduct ModuleCat.Algebra
namespace ArExplicit.ExternalTensor
universe u
variable (k : Type u) [Field k]

variable (R : Type u) [Ring R] [Algebra k R]
attribute [local instance] moduleCatBaseModule moduleCatBaseTower
variable {X : ModuleCat.{u} R} (P : ProjectiveResolution X)
variable (U : Type u) [AddCommGroup U] [Module R U] [Module k U] [IsScalarTower k R U]

variable (A B : Type u) [Ring A] [Ring B] [Algebra k A] [Algebra k B]
variable [Module.Finite k A] [Module.Finite k B]
variable {M : ModuleCat.{u} A} {N : ModuleCat.{u} B}
variable (P : ProjectiveResolution M) (Q : ProjectiveResolution N)
variable [∀ n, Module.Finite A (P.complex.X n)] [∀ n, Module.Finite B (Q.complex.X n)]
variable (U : ModuleCat.{u} A) (V : ModuleCat.{u} B)
variable (f : homCochain k A P.complex U ⟶ homCochain k A P.complex U)
variable (g : homCochain k B Q.complex V ⟶ homCochain k B Q.complex V)
local notation "T" => MonoidalCategory.curriedTensor (ModuleCat k)

def homKunnethCoordinates (n : ℕ) :
    (homCochain k (A ⊗[k] B) (complex k A B P.complex Q.complex)
      (moduleObject k A B U V)).homology n ≃ₗ[k]
    (∀ p : Diagonal n, (homCochain k A P.complex U).homology p.val.1 ⊗[k]
      (homCochain k B Q.complex V).homology p.val.2) :=
  (homKunnethEquiv k A B P.complex Q.complex U V n).trans
    DFinsupp.linearEquivFunOnFintype

omit [Module.Finite k A] [Module.Finite k B] in

theorem homKunnethCoordinates_natural (n : ℕ)
    (x : (homCochain k (A ⊗[k] B) (complex k A B P.complex Q.complex)
      (moduleObject k A B U V)).homology n) :
    homKunnethCoordinates k A B P Q U V n
      ((homologyMap (homTensorMap k A B P Q U V f g) n).hom x) =
    VectorCochain.diagonalTermMap k (VectorCochain.gradedMap k f)
      (VectorCochain.gradedMap k g) n (homKunnethCoordinates k A B P Q U V n x) := by
  let e := homCochainTotalIso k A B P.complex Q.complex U V
  change VectorCochain.homologyCoordinates k n
      (((homologyFunctor (ModuleCat.{u} k) (.up ℕ) n).mapIso e).inv.hom
        ((homologyMap (e.inv ≫ mapBifunctorMap f g T (.up ℕ) ≫ e.hom) n).hom x)) = _
  rw [homology_conjugate]
  exact VectorCochain.homologyCoordinates_natural k f g n _

end ArExplicit.ExternalTensor

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Ext_ExternalEvaluationAugmentation
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.EnvelopingBimodule.regular_projective _root_.OAI.ArExplicit.ExternalTensor.hasHomCochainTotal _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.moduleCatBaseComm _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
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
variable {U : ModuleCat.{u} (A ⊗[k] Aᵐᵒᵖ)} {V : ModuleCat.{u} (B ⊗[k] Bᵐᵒᵖ)}
variable (P : ProjectiveResolution U) (Q : ProjectiveResolution V)
variable (P' : ProjectiveResolution X) (Q' : ProjectiveResolution Y)
local notation "Ae" => A ⊗[k] Aᵐᵒᵖ
local notation "Be" => B ⊗[k] Bᵐᵒᵖ
local notation "EA" => EnvelopingBimodule.evaluationFunctor k A X
local notation "EB" => EnvelopingBimodule.evaluationFunctor k B Y
local notation "E" => productEvaluation k A B X Y

theorem totalEvaluation_augmentation
    (a : factorEvaluation k X P.complex ≅ P'.complex)
    (b : factorEvaluation k Y Q.complex ≅ Q'.complex)
    (e : (EA).obj U ⟶ X) (f : (EB).obj V ⟶ Y)
    (ha : a.hom.f 0 ≫ P'.π.f 0 = (EA).map (P.π.f 0) ≫ e)
    (hb : b.hom.f 0 ≫ Q'.π.f 0 = (EB).map (Q.π.f 0) ≫ f) :
    (totalEvaluationIso k A B X Y P.complex Q.complex ≪≫
      ExternalTensor.complexIso k A B a b).hom.f 0 ≫
        (ExternalTensor.augmentation k A B P' Q').f 0 =
    (E).map ((ExternalTensor.augmentation k Ae Be P Q).f 0) ≫
      totalEndpointMap k A B X Y e f := by
  apply evaluatedTotal_hom_ext k A B X Y P.complex Q.complex
  intro i j hij
  have hi : i=0 := by omega
  have hj : j=0 := by omega
  subst i; subst j
  change (E).map (ExternalTensor.inclusion k Ae Be P.complex Q.complex 0 0 0 hij) ≫
      (((totalEvaluationTermIso k A B X Y P.complex Q.complex 0).hom ≫
        (ExternalTensor.complexMap k A B a.hom b.hom).f 0) ≫
          (ExternalTensor.augmentation k A B P' Q').f 0) = _
  erw [Category.assoc, ← Category.assoc,
    inclusion_totalEvaluationTermIso k A B X Y P.complex Q.complex 0 0 0 hij]
  erw [Category.assoc, ExternalTensor.inclusion_complexMap_assoc,
    ExternalTensor.inclusion_augmentation k A B P' Q',
    ← ExternalTensor.mapHom_comp k A B (a.hom.f 0) (P'.π.f 0) (b.hom.f 0) (Q'.π.f 0), ha, hb,
    ExternalTensor.mapHom_comp k A B ((EA).map (P.π.f 0)) e ((EB).map (Q.π.f 0)) f]
  symm
  erw [← Category.assoc, ← (E).map_comp, ExternalTensor.inclusion_augmentation k Ae Be P Q]
  change (E).map (ExternalTensor.mapHom k Ae Be (P.π.f 0) (Q.π.f 0)) ≫
      ((shuffle k A B U V X Y).toModuleIso.hom ≫ ExternalTensor.mapHom k A B e f) = _
  erw [← Category.assoc, shuffle_natural_fixed, Category.assoc]

end ArExplicit.ExternalBalanced

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Homology_CoefficientComplexValues
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.EnvelopingBimodule.regular_projective _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
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
variable (e : X ≅ Y) (P : ChainComplex (ModuleCat.{u} (R ⊗[k] Rᵐᵒᵖ)) ℕ)

theorem coefficientComplexIso_tmul (n : ℕ) (z : EnvelopingBimodule k R (P.X n)) (x : X) :
    (coefficientComplexIso k R e P).hom.f n (BalancedTensor.tmul z x) =
      BalancedTensor.tmul z (e.hom x) := by
  rw [coefficientComplexIso_f]
  exact evaluationCoefficientIso_tmul k R e (P.X n) z x

end ArExplicit.EnvelopingBimodule

end

end OAI
end


