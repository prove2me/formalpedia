-- Prove2me | Definitions.Def_OAIQ031A033
-- name    : OAIQ031A033
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T13:02:39.57143+00:00
-- url     : https://prove2.me/theorems/dd0b94d2-90f9-4992-a2a0-3a110c2aa749
-- title:
--   Definitions bundle OAIQ031A033 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 30 declarations of OpenAI's Lean: 4 definitions, 2 instances and 24 theorems. The definitions and types are `OAI.ArExplicit.CompleteComparison.fullHomProduct`, `OAI.ArExplicit.Resolution.ellPreimage`, `OAI.ArExplicit.TIndex.source`, `OAI.ArExplicit.concentratedNatDerivedIso`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Algebras_BaseAlgebra`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Algebras/BaseAlgebra.lean), [`AuslanderReiten_Algebras_TensorStructure`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Algebras/TensorStructure.lean), [`AuslanderReiten_Cocycles_CocycleCorners`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Cocycles/CocycleCorners.lean), [`AuslanderReiten_HomComplex_FullHomDegreeProducts`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/HomComplex/FullHomDegreeProducts.lean), [`AuslanderReiten_HomComplex_FullHomProductLinear`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/HomComplex/FullHomProductLinear.lean), [`AuslanderReiten_HomComplex_FullHomProducts`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/HomComplex/FullHomProducts.lean), [`AuslanderReiten_Homology_ConcentratedNatDerived`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Homology/ConcentratedNatDerived.lean), [`AuslanderReiten_Homology_TriangleRecurrence`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Homology/TriangleRecurrence.lean), [`AuslanderReiten_Resolutions_CProjectiveResolution`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Resolutions/CProjectiveResolution.lean), [`AuslanderReiten_Resolutions_Resolution`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Resolutions/Resolution.lean).
--
--   **Imports.** It imports the bundles `OAIQ031A001`, `OAIQ031A006`, `OAIQ031A007`, `OAIQ031A008`, `OAIQ031A009`, `OAIQ031A010` and `OAIQ031A011` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ031A050`, `OAIQ031A051`, `OAIQ031A052`, `OAIQ031A056` and `OAIQ031A057`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A001
import Definitions.Def_OAIQ031A006
import Definitions.Def_OAIQ031A007
import Definitions.Def_OAIQ031A008
import Definitions.Def_OAIQ031A009
import Definitions.Def_OAIQ031A010
import Definitions.Def_OAIQ031A011

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Algebras_BaseAlgebra
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.Resolution.instIsScalarTowerTSimple _root_.OAI.ArExplicit.Resolution.instModuleTSimple _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit

namespace BaseAlgebra

variable {k : Type*} (q : k)

variable [CommRing k]

open Letter

theorem fourfold_product_ne_zero [IsDomain k] (hq : q ≠ 0) (hq1 : 1 + q ≠ 0) :
    ((basisVector q u * basisVector q t) * basisVector q u) * basisVector q t ≠ 0 := by
  rw [fourfold_product]
  intro h
  have hz := congrArg (fun a : BaseAlgebra k q => a.coeff z) h
  simpa using (mul_ne_zero hq hq1) (by simpa using hz)

end BaseAlgebra
end ArExplicit

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Algebras_TensorStructure
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.Resolution.instIsScalarTowerTSimple _root_.OAI.ArExplicit.Resolution.instModuleTSimple _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit

open TensorProduct

namespace A

variable {k : Type*} [Field k] (q : k)

theorem fourfold_product_ne_zero (hq : q ≠ 0) (hq1 : 1 + q ≠ 0) :
    ((radicalU q * radicalT q) * radicalU q) * radicalT q ≠ 0 := by
  intro h
  have h' := congrArg (originalProjection q) h
  simp only [map_mul, originalProjection_radicalU, originalProjection_radicalT, map_zero] at h'
  exact BaseAlgebra.fourfold_product_ne_zero q hq hq1 h'

end A
end ArExplicit

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cocycles_CocycleCorners
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ArExplicit
namespace TIndex

def source (i : TIndex) : Bool := if i.1 then lowerTarget i.2 else lowerSource i.2

end TIndex

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_HomComplex_FullHomProducts
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open CategoryTheory
open CochainComplex CochainComplex.HomComplex

namespace ArExplicit.CompleteComparison

universe u

section Cochains

variable {C : Type*} [Category* C] [Preadditive C]
variable {K L M : CochainComplex C ℤ} {n m : ℤ}

@[simp]
theorem cocycleProduct_coe (x : Cocycle K L n) (y : Cocycle L M m) :
    (cocycleProduct x y).1 = x.1.comp y.1 rfl := rfl

theorem cocycleHom_product (x : Cocycle K L n) (y : Cocycle L M m) :
    Cocycle.equivHomShift.symm (cocycleProduct x y) =
      Cocycle.equivHomShift.symm x ≫ shiftedCocycleHom y n := by
  apply HomologicalComplex.Hom.ext
  funext i
  simp only [HomologicalComplex.comp_f, shiftedCocycleHom, cocycleHom_component,
    shiftFunctor_map_f', shiftFunctorAdd'_inv_app_f']
  change (x.1.comp y.1 rfl).v i (i + (n + m)) rfl =
    x.1.v i (i + n) rfl ≫ y.1.v (i + n) (i + n + m) rfl ≫
      (M.XIsoOfEq (show i + n + m = i + (n + m) by omega)).hom
  rw [cochain_component_transport]
  exact Cochain.comp_v x.1 y.1 rfl i (i + n) (i + (n + m)) rfl (by omega)

theorem cocycleProduct_respects_classes
    (x x' : Cocycle K L n) (y y' : Cocycle L M m)
    (hx : CohomologyClass.mk x = CohomologyClass.mk x')
    (hy : CohomologyClass.mk y = CohomologyClass.mk y') :
    CohomologyClass.mk (cocycleProduct x y) = CohomologyClass.mk (cocycleProduct x' y') := by
  have hx' := congrArg CohomologyClass.toHom hx
  have hy' := congrArg CohomologyClass.toHom hy
  let Hx := HomotopyCategory.homotopyOfEq _ _ hx'
  let Hy := HomotopyCategory.homotopyOfEq _ _ hy'
  apply (CohomologyClass.toHom_bijective K M (n + m)).1
  change (HomotopyCategory.quotient _ _).map
      (Cocycle.equivHomShift.symm (cocycleProduct x y)) =
    (HomotopyCategory.quotient _ _).map (Cocycle.equivHomShift.symm (cocycleProduct x' y'))
  rw [cocycleHom_product, cocycleHom_product]
  exact HomotopyCategory.eq_of_homotopy _ _ (Hx.comp ((Hy.shift n).compRight _))

def fullHomProduct (x : CohomologyClass K L n) (y : CohomologyClass L M m) :
    CohomologyClass K M (n + m) :=
  Quotient.liftOn₂ x y (fun a b => CohomologyClass.mk (cocycleProduct a b)) (by
    intro a b a' b' ha hb
    exact cocycleProduct_respects_classes a a' b b' (Quotient.sound ha) (Quotient.sound hb))

@[simp]
theorem fullHomProduct_mk (x : Cocycle K L n) (y : Cocycle L M m) :
    fullHomProduct (CohomologyClass.mk x) (CohomologyClass.mk y) =
      CohomologyClass.mk (cocycleProduct x y) := rfl

end Cochains

end ArExplicit.CompleteComparison

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_HomComplex_FullHomProductLinear
attribute [-instance] _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open CategoryTheory
open CochainComplex CochainComplex.HomComplex
namespace ArExplicit.CompleteComparison
universe u v
variable {k : Type u} [CommRing k]
variable {C : Type v} [Category* C] [Preadditive C] [Linear k C]
variable {K L M : CochainComplex C ℤ} {n m : ℤ}

theorem fullHomProduct_smul_left (c : k) (x : CohomologyClass K L n)
    (y : CohomologyClass L M m) :
    fullHomProduct (c • x) y = c • fullHomProduct x y := by
  obtain ⟨x,rfl⟩ := CohomologyClass.mk_surjective x
  obtain ⟨y,rfl⟩ := CohomologyClass.mk_surjective y
  rw [← fullHom_mk_smul, fullHomProduct_mk, fullHomProduct_mk, ← fullHom_mk_smul]
  congr 1
  apply Subtype.ext
  exact Cochain.smul_comp c x.val y.val rfl

end ArExplicit.CompleteComparison

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_HomComplex_FullHomDegreeProducts
attribute [-instance] _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory
open CochainComplex CochainComplex.HomComplex
namespace ArExplicit.CompleteComparison
universe u v
variable {k : Type u} [Field k]
variable {C : Type v} [Category.{u} C] [Preadditive C] [Linear k C]
variable {K L M : CochainComplex C ℤ} {n m l : ℤ}

theorem fullHomProduct_degree_mk (h : n+m=l)
    (x : Cocycle K L n) (y : Cocycle L M m) (z : Cocycle K M l)
    (hz : z.val=x.val.comp y.val h) :
    TateKoszul.degreeEquiv (k := k) (CohomologyClass K M) h
      (fullHomProduct (CohomologyClass.mk x) (CohomologyClass.mk y)) = CohomologyClass.mk z := by
  subst l
  change CohomologyClass.mk (cocycleProduct x y) = CohomologyClass.mk z
  congr 1
  exact Subtype.ext hz.symm

theorem fullHomProduct_identity_right (x : CohomologyClass K L n) :
    TateKoszul.degreeEquiv (k := k) (CohomologyClass K L) (add_zero n)
      (fullHomProduct x (fullHomIdentity L)) = x := by
  obtain ⟨x,rfl⟩ := CohomologyClass.mk_surjective x
  apply fullHomProduct_degree_mk
  exact (Cochain.comp_id x.val).symm

theorem fullHomProduct_identity_left (x : CohomologyClass K L n) :
    TateKoszul.degreeEquiv (k := k) (CohomologyClass K L) (zero_add n)
      (fullHomProduct (fullHomIdentity K) x) = x := by
  obtain ⟨x,rfl⟩ := CohomologyClass.mk_surjective x
  apply fullHomProduct_degree_mk
  exact (Cochain.id_comp x.val).symm

end ArExplicit.CompleteComparison

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Homology_ConcentratedNatDerived
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory
namespace ArExplicit
universe u v
variable {C : Type u} [Category.{v} C] [Abelian C]

def concentratedNatDerivedIso [HasDerivedCategory C]
    (K : ChainComplex C ℕ) (n : ℕ) (X : C)
    (hex : ∀ m : ℕ, m ≠ n → K.ExactAt m) (e : K.homology n ≅ X) :
    DerivedCategory.Q.obj (K.extend ComplexShape.embeddingDownNat) ≅
      ((DerivedCategory.singleFunctor C 0).obj X)⟦(n : ℤ)⟧ :=
  derivedSingleIso _ (-(n : ℤ)) (concentratedNat_exact K n hex) ≪≫
    (DerivedCategory.singleFunctor C (-(n : ℤ))).mapIso
      (K.extendHomologyIso ComplexShape.embeddingDownNat (j := n) rfl ≪≫ e) ≪≫
    (((DerivedCategory.singleFunctors C).shiftIso (n : ℤ) (-(n : ℤ)) 0 (by omega)).app X).symm

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Homology_TriangleRecurrence
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Pretriangulated
namespace ArExplicit.TriangleRecurrence

universe v u
variable {C : Type u} [Category.{v} C] [Preadditive C] [Limits.HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

variable (T : Triangle C) (hT : T ∈ distTriang C) (Y : C)
include hT

omit hT in

theorem degreeThreeComposition_bijective (X I : C)
    (a : X⟦(2 : ℤ)⟧ ⟶ I) (b : I ⟶ X) (d : X ⟶ (X⟦(2 : ℤ)⟧)⟦(1 : ℤ)⟧)
    (hd : Triangle.mk a b d ∈ distTriang C) (n : ℤ)
    (h₀ : ∀ f : I ⟶ X⟦n + 3⟧, f = 0)
    (h₁ : ∀ f : I⟦(1 : ℤ)⟧ ⟶ X⟦n + 3⟧, f = 0) :
    Function.Bijective (fun β : ShiftedHom X X n =>
      ShiftedHom.comp (a := (3 : ℤ)) (b := n)
        (d ≫ (shiftFunctorAdd' C (2 : ℤ) 1 3 (by decide)).inv.app X) β rfl) := by
  let e := shiftedMapEquiv X X 3 n (n + 3) rfl
  let e' := ((shiftFunctorAdd' C (2 : ℤ) 1 3 (by decide)).app X).homFromEquiv
    (Z := X⟦n + 3⟧)
  have h := (connecting_bijective (Triangle.mk a b d) hd (X⟦n + 3⟧) h₀ h₁).comp
    (e'.bijective.comp e.bijective)
  convert! h using 1
  all_goals try with_reducible_and_instances rfl
  ext β
  simp only [Function.comp_apply, e, e', shiftedMapEquiv, Equiv.trans_apply,
    ShiftedHom.comp, Category.assoc]
  rfl

end ArExplicit.TriangleRecurrence

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Resolutions_Resolution
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.Resolution.instIsScalarTowerTSimple _root_.OAI.ArExplicit.Resolution.instModuleTSimple _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit.Resolution

open ArExplicit.Letter ArExplicit.BaseAlgebra

variable {k : Type*} [Field k] (q : k)

local notation "C" => BaseAlgebra k q

theorem mul_ell_formula (r : k) (a : E q) : (a : C) * ell q r =
    (a : C).coeff e • ell q r +
    (q * r * (a : C).coeff x + (a : C).coeff y) • basisVector q z +
    ((1 + q ^ 2 * r) * (a : C).coeff t) • basisVector q j := by
  ext i
  cases i <;> simp [product, ell] <;> ring

section CharacteristicTwo

variable [CharP k 2]

theorem mul_u_eq_zero_iff (hq : 1 + q ≠ 0) (a : E q) :
    (a : C) * basisVector q u = 0 ↔
      (a : C).coeff e = 0 ∧ (a : C).coeff t = 0 ∧ (a : C).coeff y = (a : C).coeff x := by
  rw [mul_u_formula]
  constructor
  · intro h
    have he := congrArg (fun b : C => b.coeff u) h
    have ht := congrArg (fun b : C => b.coeff n) h
    have hy := congrArg (fun b : C => b.coeff v) h
    simp only [coeff_add, coeff_smul, coeff_basisVector, coeff_zero] at he ht hy
    simp only [reduceCtorEq, ↓reduceIte, mul_zero, mul_one, add_zero, zero_add] at he ht hy
    exact ⟨he, (mul_eq_zero.mp ht).resolve_left hq, (CharTwo.add_eq_zero.mp hy).symm⟩
  · rintro ⟨he, ht, hy⟩
    simp [he, ht, hy, CharTwo.add_self_eq_zero]

theorem mul_ell_eq_zero_iff (r : k) (hr : 1 + q ^ 2 * r ≠ 0) (a : E q) :
    (a : C) * ell q r = 0 ↔
      (a : C).coeff e = 0 ∧ (a : C).coeff t = 0 ∧
      (a : C).coeff y = q * r * (a : C).coeff x := by
  rw [mul_ell_formula]
  constructor
  · intro h
    have he := congrArg (fun b : C => b.coeff x) h
    have ht := congrArg (fun b : C => b.coeff j) h
    have hy := congrArg (fun b : C => b.coeff z) h
    simp [ell] at he ht hy
    exact ⟨he, ht.resolve_left hr, (CharTwo.add_eq_zero.mp hy).symm⟩
  · rintro ⟨he, ht, hy⟩
    simp [he, ht, hy, CharTwo.add_self_eq_zero]

end CharacteristicTwo

def ellPreimage (r α β γ : k) : E q :=
  ⟨α • basisVector q e + β • basisVector q y + (γ / (1 + q ^ 2 * r)) • basisVector q t, by
    change (_ : C) * basisVector q e = _
    simp [add_mul, basis_mul, multiplicationTable]⟩

theorem ellPreimage_spec (r α β γ : k) (hr : 1 + q ^ 2 * r ≠ 0) :
    (ellPreimage q r α β γ : C) * ell q r =
      α • ell q r + β • basisVector q z + γ • basisVector q j := by
  rw [mul_ell_formula]
  have hγ : (1 + q ^ 2 * r) * (γ / (1 + q ^ 2 * r)) = γ := by
    rw [mul_comm, div_mul_cancel₀ γ hr]
  simp [ellPreimage, hγ]

section Exactness

variable [CharP k 2]

theorem uKernel_expand (hq : 1 + q ≠ 0) (a : E q)
    (ha : (a : C) * basisVector q u = 0) :
    (a : C) = (a : C).coeff x • ell q 1 +
      (a : C).coeff z • basisVector q z + (a : C).coeff j • basisVector q j := by
  obtain ⟨he, ht, hy⟩ := (mul_u_eq_zero_iff q hq a).mp ha
  ext i
  cases i <;> simp [ell, he, ht, hy]

theorem ellKernel_expand (r : k) (hr : 1 + q ^ 2 * r ≠ 0) (a : E q)
    (ha : (a : C) * ell q r = 0) :
    (a : C) = (a : C).coeff x • ell q (q * r) +
      (a : C).coeff z • basisVector q z + (a : C).coeff j • basisVector q j := by
  obtain ⟨he, ht, hy⟩ := (mul_ell_eq_zero_iff q r hr a).mp ha
  ext i
  cases i <;> simp [ell, he, ht, hy]
  ring

theorem exact_dU (hq : 1 + q ≠ 0) (hq2 : 1 + q ^ 2 ≠ 0) :
    Function.Exact (dEll q 1) (dU q) := by
  intro a
  constructor
  · intro ha
    have ha' : (a : C) * basisVector q u = 0 := congrArg Subtype.val ha
    refine ⟨ellPreimage q 1 ((a : C).coeff x) ((a : C).coeff z) ((a : C).coeff j), ?_⟩
    apply Subtype.ext
    change (_ : C) * ell q 1 = (a : C)
    rw [ellPreimage_spec q 1 _ _ _ (by simpa using hq2)]
    exact (uKernel_expand q hq a ha').symm
  · rintro ⟨b, rfl⟩
    exact DFunLike.congr_fun (dU_comp_dEll_one q) b

theorem exact_dEll (r : k) (hr : 1 + q ^ 2 * r ≠ 0)
    (hnext : 1 + q ^ 2 * (q * r) ≠ 0) :
    Function.Exact (dEll q (q * r)) (dEll q r) := by
  intro a
  constructor
  · intro ha
    have ha' : (a : C) * ell q r = 0 := congrArg Subtype.val ha
    refine ⟨ellPreimage q (q * r) ((a : C).coeff x) ((a : C).coeff z) ((a : C).coeff j), ?_⟩
    apply Subtype.ext
    change (_ : C) * ell q (q * r) = (a : C)
    rw [ellPreimage_spec q (q * r) _ _ _ hnext]
    exact (ellKernel_expand q r hr a ha').symm
  · rintro ⟨b, rfl⟩
    exact DFunLike.congr_fun (dEll_comp_successor q r) b

end Exactness

end ArExplicit.Resolution

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Resolutions_CProjectiveResolution
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.ModuleRestriction.preservesHomology _root_.OAI.ArExplicit.Resolution.instIsScalarTowerTSimple _root_.OAI.ArExplicit.Resolution.instModuleTSimple _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.cochainNatTensorSigns _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory

namespace ArExplicit.Resolution

variable {k : Type*} [Field k] [CharP k 2] (q : k)

instance complex_scalar (n : ℕ) : Module k ((complex q).X n) := by
  cases n with
  | zero => exact (inferInstance : Module k (F q))
  | succ n => exact (inferInstance : Module k (E q))

omit [CharP k 2] in
theorem denominator_power_ne (h : NoPositivePowerOne q) (n : ℕ) :
    1 + q ^ 2 * q ^ n ≠ 0 := by
  rw [← pow_add]
  exact h (2 + n) (by omega)

theorem differential_exact (h : NoPositivePowerOne q) (n : ℕ) :
    Function.Exact (differential q (n + 1)) (differential q n) := by
  cases n with
  | zero =>
    change Function.Exact (dEll q (q ^ 0)) (dU q)
    simpa only [pow_zero] using exact_dU q (by simpa using h 1 (by decide)) (h 2 (by decide))
  | succ n =>
    change Function.Exact (dEll q (q ^ (n + 1))) (dEll q (q ^ n))
    simpa only [pow_succ'] using exact_dEll q (q ^ n)
      (denominator_power_ne q h n)
      (by simpa [pow_succ'] using denominator_power_ne q h (n + 1))

theorem complex_exactAt_succ (h : NoPositivePowerOne q) (n : ℕ) :
    (complex q).ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ (n + 1 + 1) (n + 1) n (by simp) (by simp)]
  apply (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr
  simpa [complex, HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor',
    ChainComplex.of_d] using! differential_exact q h n

instance augmentation_epi : Epi (augmentation q) :=
  (ModuleCat.epi_iff_surjective _).mpr (Submodule.mkQ_surjective _)

theorem augmentation_exact :
    (ShortComplex.mk ((complex q).d 1 0) (augmentation q) (differential_augmentation q)).Exact := by
  apply (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr
  change Function.Exact (dU q) (LinearMap.range (dU q)).mkQ
  exact LinearMap.exact_map_mkQ_range (dU q)

theorem toSimple_quasiIso (h : NoPositivePowerOne q) : QuasiIso (toSimple q) := by
  constructor
  intro n
  cases n with
  | zero =>
    rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros']
    · change (ShortComplex.mk ((complex q).d 1 0) ((toSimple q).f 0) _).Exact ∧
        Epi ((toSimple q).f 0)
      simpa only [toSimple_zero, ChainComplex.single₀_obj_zero] using And.intro (augmentation_exact q) (augmentation_epi q)
    · rfl
    · rfl
    · rfl
  | succ n =>
    rw [quasiIsoAt_iff_exactAt']
    · exact complex_exactAt_succ q h n
    · exact ChainComplex.exactAt_succ_single_obj _ _

end ArExplicit.Resolution

end

end OAI
end


