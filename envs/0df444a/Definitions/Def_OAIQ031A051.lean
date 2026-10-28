-- Prove2me | Definitions.Def_OAIQ031A051
-- name    : OAIQ031A051
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T14:06:08.50101+00:00
-- url     : https://prove2.me/theorems/b8c7ee82-b663-4f96-9d89-edfcc88560c8
-- title:
--   Definitions bundle OAIQ031A051 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 27 declarations of OpenAI's Lean: 10 definitions and 17 theorems. The definitions and types are `OAI.ArExplicit.ExternalTensor.coefficientFirst`, `OAI.ArExplicit.ExternalTensor.coefficientSecond`, `OAI.ArExplicit.VectorCochain.cyclesInclusion`, `OAI.ArExplicit.VectorCochain.cyclesInclusionHomotopy`, `OAI.ArExplicit.VectorCochain.cyclesQuotient`, `OAI.ArExplicit.VectorCochain.gradedCycles`, `OAI.ArExplicit.VectorCochain.kunnethIso`, `OAI.ArExplicit.VectorCochain.kunnethLinearEquiv`, `OAI.ArExplicit.VectorCochain.tensorCyclesInclusionHomotopy`, `OAI.ArExplicit.VectorCochain.tensorRepresentativesNaturality`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Algebras_TensorStructure`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Algebras/TensorStructure.lean), [`AuslanderReiten_Ext_TensorExtCoefficients`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Ext/TensorExtCoefficients.lean), [`AuslanderReiten_Homology_VectorCochainKunneth`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Homology/VectorCochainKunneth.lean), [`AuslanderReiten_Homology_VectorCochainKunnethCycles`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Homology/VectorCochainKunnethCycles.lean), [`AuslanderReiten_Homology_VectorCochainKunnethLiteral`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Homology/VectorCochainKunnethLiteral.lean), [`AuslanderReiten_Homology_VectorCochainKunnethNaturality`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Homology/VectorCochainKunnethNaturality.lean), [`AuslanderReiten_Resolutions_ResolutionExtAction`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Resolutions/ResolutionExtAction.lean), [`AuslanderReiten_Resolutions_ResolutionExtIdentity`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Resolutions/ResolutionExtIdentity.lean), [`AuslanderReiten_Resolutions_ResolutionProductCompatibility`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Resolutions/ResolutionProductCompatibility.lean).
--
--   **Imports.** It imports the bundles `OAIQ031A025`, `OAIQ031A031`, `OAIQ031A032`, `OAIQ031A033`, `OAIQ031A034` and `OAIQ031A035` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ031A067`, `OAIQ031A068` and `OAIQ031A073`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A025
import Definitions.Def_OAIQ031A031
import Definitions.Def_OAIQ031A032
import Definitions.Def_OAIQ031A033
import Definitions.Def_OAIQ031A034
import Definitions.Def_OAIQ031A035

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Algebras_TensorStructure
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.Resolution.augmentation_epi _root_.OAI.ArExplicit.Resolution.complex_scalar _root_.OAI.ArExplicit.Resolution.instIsScalarTowerTSimple _root_.OAI.ArExplicit.Resolution.instModuleTSimple _root_.OAI.ArExplicit.Resolution.simpleRightAction _root_.OAI.ArExplicit.TrivialInduction.dualModule _root_.OAI.ArExplicit.TrivialInduction.quotientModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit

open TensorProduct

namespace A

variable {k : Type*} [Field k] (q : k)

theorem left_radical_mem {a : T k q} (ha : a ∈ Ring.jacobson (T k q)) (b : T k q) :
    a ⊗ₜ[k] b ∈ Ring.jacobson (A k q) := by
  apply nilpotentIdeal_le_jacobson
    (leftTensorIdeal (k := k) (S := T k q) (Ring.jacobson (T k q)))
    (leftTensorIdeal_isNilpotent _ (finiteAlgebra_radical_isNilpotent (k := k)))
  exact tmul_mem_leftTensorIdeal _ ha b

end A
end ArExplicit

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Resolutions_ResolutionProductCompatibility
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian
open CochainComplex CochainComplex.HomComplex
namespace ArExplicit.ResolutionProducts
universe u v
variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory C]

omit [HasDerivedCategory C] in
theorem cocycleHom_comp {K L M : CochainComplex C ℤ} {i j l : ℤ} (hl : i+j=l)
    (x : Cocycle K L i) (y : Cocycle L M j) (z : Cocycle K M l)
    (hz : z.val = x.val.comp y.val hl) :
    Cocycle.equivHomShift.symm z =
      ShiftedHom.comp (Cocycle.equivHomShift.symm x) (Cocycle.equivHomShift.symm y) (by omega) := by
  subst l
  have he : z = CompleteComparison.cocycleProduct x y := Subtype.ext hz
  subst z
  exact CompleteComparison.cocycleHom_product x y

end ArExplicit.ResolutionProducts

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Resolutions_ResolutionExtIdentity
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian
open CochainComplex CochainComplex.HomComplex
namespace ArExplicit.ResolutionProducts
universe u v
variable {C : Type u} [Category.{v} C] [Abelian C]

variable [HasDerivedCategory C] [HasExt.{v} C]

theorem endExt_identity {X : C} (P : ProjectiveResolution X) :
    endExt P (Cocycle.ofHom (𝟙 P.cochainComplex)) = Ext.mk₀ (𝟙 X) := by
  apply Ext.homEquiv.injective
  change (endExt P (Cocycle.ofHom (𝟙 P.cochainComplex))).hom = (Ext.mk₀ (𝟙 X)).hom
  rw [endExt_hom, cocycleHom_ofHom, Ext.mk₀_hom]
  erw [ShiftedHom.map_mk₀]
  simp [conjugate, ShiftedHom.mk₀, ← NatTrans.naturality]

end ArExplicit.ResolutionProducts

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Homology_VectorCochainKunneth
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ArExplicit.VectorCochain

open CategoryTheory CategoryTheory.Limits HomologicalComplex

universe u

variable (k : Type u) [Field k]
variable (F : ModuleCat.{u} k ⥤ ModuleCat.{u} k ⥤ ModuleCat.{u} k)
  [F.Additive] [∀ X, (F.obj X).Additive]

variable (P Q : CochainComplex (ModuleCat.{u} k) ℕ)

def kunnethIso (n : ℕ) :
    (mapBifunctor P Q F (ComplexShape.up ℕ)).homology n ≅
    (mapBifunctor (gradedHomology k P) (gradedHomology k Q) F (ComplexShape.up ℕ)).X n :=
  ((tensorSplitting k F P Q).toHomologyIso n).symm ≪≫
    totalZeroHomologyIso k F (fun i => P.homology i) (fun j => Q.homology j) n

theorem tensorSplitting_hom :
    (tensorSplitting k F P Q).hom =
      mapBifunctorMap (representatives k P) (representatives k Q) F (ComplexShape.up ℕ) := by
  simp [tensorSplitting, totalHomotopyEquiv]

theorem kunnethIso_inv (n : ℕ) :
    (kunnethIso k F P Q n).inv =
      (totalZeroHomologyIso k F (fun i => P.homology i) (fun j => Q.homology j) n).inv ≫
        homologyMap (mapBifunctorMap (representatives k P) (representatives k Q) F
          (ComplexShape.up ℕ)) n := by
  change _ ≫ homologyMap (tensorSplitting k F P Q).hom n = _
  rw [tensorSplitting_hom]

def kunnethLinearEquiv (n : ℕ) :
    (mapBifunctor P Q F (ComplexShape.up ℕ)).homology n ≃ₗ[k]
      (Π₀ p : {p : ℕ × ℕ // p.1 + p.2 = n},
        (F.obj (P.homology p.val.1)).obj (Q.homology p.val.2)) :=
  (kunnethIso k F P Q n).toLinearEquiv.trans
    (ModuleCat.coprodIsoDirectSum
      (fun p : {p : ℕ × ℕ // p.1 + p.2 = n} =>
        (F.obj (P.homology p.val.1)).obj (Q.homology p.val.2))).toLinearEquiv

end ArExplicit.VectorCochain

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Ext_TensorExtCoefficients
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian
open scoped TensorProduct ModuleCat.Algebra
namespace ArExplicit.ExternalTensor
universe u
variable (k A B : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
variable (X U : ModuleCat.{u} A) (Y V : ModuleCat.{u} B)

variable (a : Ext X X 3) (b : Ext Y Y 3)

def coefficientFirst (n : ℕ) : extCoefficients k A B X U Y V n →ₗ[k]
    extCoefficients k A B X U Y V (n+3) := by
  classical
  exact ∑ d : Diagonal n,
    (LinearMap.single k (fun e : Diagonal (n+3) => Ext X U e.val.1 ⊗[k] Ext Y V e.val.2)
      (diagonalFirst n d)).comp
      ((TensorProduct.map (Ext.bilinearCompOfLinear k X X U 3 d.val.1 (d.val.1+3) (by omega) a)
        (LinearMap.id : Ext Y V d.val.2 →ₗ[k] Ext Y V d.val.2)).comp (LinearMap.proj d))

def coefficientSecond (n : ℕ) : extCoefficients k A B X U Y V n →ₗ[k]
    extCoefficients k A B X U Y V (n+3) := by
  classical
  exact ∑ d : Diagonal n,
    (LinearMap.single k (fun e : Diagonal (n+3) => Ext X U e.val.1 ⊗[k] Ext Y V e.val.2)
      (diagonalSecond n d)).comp
      ((TensorProduct.map (LinearMap.id : Ext X U d.val.1 →ₗ[k] Ext X U d.val.1)
        (Ext.bilinearCompOfLinear k Y Y V 3 d.val.2 (d.val.2+3) (by omega) b)).comp (LinearMap.proj d))

end ArExplicit.ExternalTensor

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Homology_VectorCochainKunnethNaturality
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.VectorCochain
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable (k : Type u) [Field k]
variable (F : ModuleCat.{u} k ⥤ ModuleCat.{u} k ⥤ ModuleCat.{u} k)
  [F.Additive] [∀ X, (F.obj X).Additive]

@[simp, reassoc] theorem totalZeroHomologyIso_π
    (X Y : ℕ → ModuleCat.{u} k) (n : ℕ) :
    (mapBifunctor (zeroDifferential k X) (zeroDifferential k Y) F (.up ℕ)).homologyπ n ≫
      (totalZeroHomologyIso k F X Y n).hom =
    (mapBifunctor (zeroDifferential k X) (zeroDifferential k Y) F (.up ℕ)).iCycles n := by
  let K := mapBifunctor (zeroDifferential k X) (zeroDifferential k Y) F (.up ℕ)
  let a := K.isoHomologyπ ((ComplexShape.up ℕ).prev n) n rfl
    (total_zero_differential k F X Y _ _)
  let b := K.iCyclesIso n ((ComplexShape.up ℕ).next n) rfl
    (total_zero_differential k F X Y _ _)
  change a.hom ≫ a.inv ≫ b.hom = b.hom
  exact a.hom_inv_id_assoc _

@[reassoc] theorem totalZeroHomologyIso_natural
    {X Y X' Y' : ℕ → ModuleCat.{u} k}
    (f : mapBifunctor (zeroDifferential k X) (zeroDifferential k Y) F (.up ℕ) ⟶
      mapBifunctor (zeroDifferential k X') (zeroDifferential k Y') F (.up ℕ)) (n : ℕ) :
    homologyMap f n ≫ (totalZeroHomologyIso k F X' Y' n).hom =
      (totalZeroHomologyIso k F X Y n).hom ≫ f.f n := by
  apply (cancel_epi ((mapBifunctor (zeroDifferential k X)
    (zeroDifferential k Y) F (.up ℕ)).homologyπ n)).1
  rw [homologyπ_naturality_assoc, totalZeroHomologyIso_π, ← Category.assoc,
    totalZeroHomologyIso_π]
  simp

@[reassoc] theorem totalZeroHomologyIso_inv_natural
    {X Y X' Y' : ℕ → ModuleCat.{u} k}
    (f : mapBifunctor (zeroDifferential k X) (zeroDifferential k Y) F (.up ℕ) ⟶
      mapBifunctor (zeroDifferential k X') (zeroDifferential k Y') F (.up ℕ)) (n : ℕ) :
    (totalZeroHomologyIso k F X Y n).inv ≫ homologyMap f n =
      f.f n ≫ (totalZeroHomologyIso k F X' Y' n).inv := by
  apply (cancel_mono (totalZeroHomologyIso k F X' Y' n).hom).1
  simp only [Category.assoc, totalZeroHomologyIso_natural,
    Iso.inv_hom_id, Category.comp_id, Iso.inv_hom_id_assoc]

variable {P P' Q Q' : CochainComplex (ModuleCat.{u} k) ℕ}

def tensorRepresentativesNaturality (f : P ⟶ P') (g : Q ⟶ Q') :
    Homotopy
      (mapBifunctorMap (representatives k P) (representatives k Q) F (.up ℕ) ≫
        mapBifunctorMap f g F (.up ℕ))
      (mapBifunctorMap (gradedMap k f) (gradedMap k g) F (.up ℕ) ≫
        mapBifunctorMap (representatives k P') (representatives k Q') F (.up ℕ)) :=
  (Homotopy.ofEq (totalMap_comp F _ _ _ _)).trans
    ((mapBifunctorMapHomotopy₁ (representativesNaturality k f)
      (representatives k Q ≫ g) F (.up ℕ)).trans
      ((mapBifunctorMapHomotopy₂ (gradedMap k f ≫ representatives k P')
        (representativesNaturality k g) F (.up ℕ)).trans
        (Homotopy.ofEq (totalMap_comp F _ _ _ _).symm)))

@[reassoc] theorem kunnethIso_inv_natural (f : P ⟶ P') (g : Q ⟶ Q') (n : ℕ) :
    (kunnethIso k F P Q n).inv ≫ homologyMap (mapBifunctorMap f g F (.up ℕ)) n =
      (mapBifunctorMap (gradedMap k f) (gradedMap k g) F (.up ℕ)).f n ≫
        (kunnethIso k F P' Q' n).inv := by
  rw [kunnethIso_inv, kunnethIso_inv]
  rw [Category.assoc, ← homologyMap_comp,
    (tensorRepresentativesNaturality k F f g).homologyMap_eq,
    homologyMap_comp, ← Category.assoc, totalZeroHomologyIso_inv_natural]
  exact Category.assoc _ _ _

@[reassoc] theorem kunnethIso_natural (f : P ⟶ P') (g : Q ⟶ Q') (n : ℕ) :
    homologyMap (mapBifunctorMap f g F (.up ℕ)) n ≫ (kunnethIso k F P' Q' n).hom =
      (kunnethIso k F P Q n).hom ≫
        (mapBifunctorMap (gradedMap k f) (gradedMap k g) F (.up ℕ)).f n := by
  apply (cancel_epi (kunnethIso k F P Q n).inv).1
  simp only [← Category.assoc]
  rw [kunnethIso_inv_natural, Iso.inv_hom_id, Category.id_comp, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]

end ArExplicit.VectorCochain

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Homology_VectorCochainKunnethCycles
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.VectorCochain
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable (k : Type u) [Field k]
variable (P : CochainComplex (ModuleCat.{u} k) ℕ)

abbrev gradedCycles := zeroDifferential k (fun n => P.cycles n)

def cyclesInclusion : gradedCycles k P ⟶ P where
  f n := P.iCycles n
  comm' _ _ _ := by simp [gradedCycles, zeroDifferential]

def cyclesQuotient : gradedCycles k P ⟶ gradedHomology k P where
  f n := P.homologyπ n
  comm' _ _ _ := by simp [gradedCycles, gradedHomology, zeroDifferential]

theorem cyclesMap_cyclesInclusion (n : ℕ) :
    cyclesMap (cyclesInclusion k P) n = (gradedCycles k P).iCycles n := by
  apply (cancel_mono (P.iCycles n)).1
  simp [cyclesInclusion]

theorem homologyMap_cyclesInclusion (n : ℕ) :
    homologyMap (cyclesInclusion k P) n =
      (zeroHomologyIso k (fun i => P.cycles i) n).hom ≫ P.homologyπ n := by
  apply (cancel_epi ((gradedCycles k P).homologyπ n)).1
  rw [homologyπ_naturality, cyclesMap_cyclesInclusion, ← Category.assoc, zeroHomologyIso_π]

theorem cyclesInclusion_comp_splitting_inv :
    cyclesInclusion k P ≫ (splitting k P).inv = cyclesQuotient k P := by
  ext n : 1
  apply (cancel_epi (zeroHomologyIso k (fun i => P.cycles i) n).hom).1
  calc
    (zeroHomologyIso k (fun i => P.cycles i) n).hom ≫
        (cyclesInclusion k P ≫ (splitting k P).inv).f n =
      homologyMap (cyclesInclusion k P ≫ (splitting k P).inv) n ≫
        (zeroHomologyIso k (fun i => P.homology i) n).hom :=
      (zeroHomologyIso_natural k _ n).symm
    _ = (zeroHomologyIso k (fun i => P.cycles i) n).hom ≫ (cyclesQuotient k P).f n := by
      simp only [homologyMap_comp, homologyMap_cyclesInclusion, homologyMap_splitting_inv,
        Category.assoc, Iso.inv_hom_id, Category.comp_id, cyclesQuotient]

def cyclesInclusionHomotopy :
    Homotopy (cyclesInclusion k P) (cyclesQuotient k P ≫ representatives k P) := by
  have hh := ((splitting k P).homotopyInvHomId.compLeftId (cyclesInclusion k P)).symm
  have he : cyclesInclusion k P ≫ ((splitting k P).inv ≫ (splitting k P).hom) =
      cyclesQuotient k P ≫ representatives k P := by
    rw [splitting_hom, ← Category.assoc, cyclesInclusion_comp_splitting_inv]
  exact hh.trans (Homotopy.ofEq he)

variable (F : ModuleCat.{u} k ⥤ ModuleCat.{u} k ⥤ ModuleCat.{u} k)
  [F.Additive] [∀ X, (F.obj X).Additive]
variable (Q : CochainComplex (ModuleCat.{u} k) ℕ)

def tensorCyclesInclusionHomotopy :
    Homotopy (mapBifunctorMap (cyclesInclusion k P) (cyclesInclusion k Q) F (.up ℕ))
      (mapBifunctorMap (cyclesQuotient k P) (cyclesQuotient k Q) F (.up ℕ) ≫
        mapBifunctorMap (representatives k P) (representatives k Q) F (.up ℕ)) :=
  (mapBifunctorMapHomotopy₁ (cyclesInclusionHomotopy k P)
    (cyclesInclusion k Q) F (.up ℕ)).trans
    ((mapBifunctorMapHomotopy₂ (cyclesQuotient k P ≫ representatives k P)
      (cyclesInclusionHomotopy k Q) F (.up ℕ)).trans
      (Homotopy.ofEq (totalMap_comp F _ _ _ _).symm))

@[reassoc] theorem tensorRepresentatives_kunneth (n : ℕ) :
    homologyMap (mapBifunctorMap (representatives k P) (representatives k Q) F (.up ℕ)) n ≫
      (kunnethIso k F P Q n).hom =
        (totalZeroHomologyIso k F (fun i => P.homology i) (fun i => Q.homology i) n).hom := by
  apply (cancel_epi (totalZeroHomologyIso k F
    (fun i => P.homology i) (fun i => Q.homology i) n).inv).1
  rw [← Category.assoc, ← kunnethIso_inv, Iso.inv_hom_id, Iso.inv_hom_id]

@[reassoc] theorem tensorCycles_kunneth (n : ℕ) :
    homologyMap (mapBifunctorMap (cyclesInclusion k P) (cyclesInclusion k Q) F (.up ℕ)) n ≫
      (kunnethIso k F P Q n).hom =
        (totalZeroHomologyIso k F (fun i => P.cycles i) (fun i => Q.cycles i) n).hom ≫
          (mapBifunctorMap (cyclesQuotient k P) (cyclesQuotient k Q) F (.up ℕ)).f n := by
  rw [(tensorCyclesInclusionHomotopy k P F Q).homologyMap_eq,
    homologyMap_comp, Category.assoc, tensorRepresentatives_kunneth,
    totalZeroHomologyIso_natural]

end ArExplicit.VectorCochain

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Homology_VectorCochainKunnethLiteral
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct
namespace ArExplicit.VectorCochain
universe u
variable (k : Type u) [Field k]
variable (F : ModuleCat.{u} k ⥤ ModuleCat.{u} k ⥤ ModuleCat.{u} k)
  [F.Additive] [∀ X, (F.obj X).Additive]

theorem totalZero_literalClass (U V : ℕ → ModuleCat.{u} k) (n : ℕ)
    (z : LinearMap.ker ((mapBifunctor (zeroDifferential k U) (zeroDifferential k V) F
      (.up ℕ)).d n (n+1)).hom) :
    (totalZeroHomologyIso k F U V n).hom.hom
      (literalClass k (mapBifunctor (zeroDifferential k U) (zeroDifferential k V) F (.up ℕ)) n z) = z.val := by
  have h := congrArg (fun f => f.hom ((literalCyclesIso k
    (mapBifunctor (zeroDifferential k U) (zeroDifferential k V) F (.up ℕ)) n).inv.hom z))
      (totalZeroHomologyIso_π k F U V n)
  exact h.trans (literalCyclesIso_inv_iCycles k _ n z)

end ArExplicit.VectorCochain

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Resolutions_ResolutionExtAction
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian
open CochainComplex CochainComplex.HomComplex
namespace ArExplicit.ResolutionProducts
universe u v
variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory C]

variable [HasExt.{v} C]

theorem extOfCocycle_hom {X Y : C} (P : ProjectiveResolution X) {n : ℕ}
    (y : Cocycle P.cochainComplex ((CochainComplex.singleFunctor C 0).obj Y) (n : ℤ)) :
    (extOfCocycle P y).hom = conjugateTo (resolutionIso P)
      ((DerivedCategory.singleFunctorIsoCompQ C 0).symm.app Y)
      (ShiftedHom.map (Cocycle.equivHomShift.symm y) DerivedCategory.Q) := by
  rw [extOfCocycle, P.extEquivCohomologyClass_symm_mk_hom]
  simp only [conjugateTo, resolutionIso, Iso.trans_inv, asIso_inv,
    ShiftedHom.mk₀_comp, ShiftedHom.comp_mk₀, Category.assoc]
  rfl

end ArExplicit.ResolutionProducts

end

end OAI
end


