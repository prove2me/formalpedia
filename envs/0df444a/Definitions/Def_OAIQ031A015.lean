-- Prove2me | Definitions.Def_OAIQ031A015
-- name    : OAIQ031A015
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T12:56:53.249688+00:00
-- url     : https://prove2.me/theorems/c037b561-c67a-41b2-a678-caf2c0c98c13
-- title:
--   Definitions bundle OAIQ031A015 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 21 declarations of OpenAI's Lean: 8 definitions and 13 theorems. The definitions and types are `OAI.ArExplicit.BalancedTensor.curryFour`, `OAI.ArExplicit.TateKoszul.row`, `OAI.ArExplicit.fullHomCochainEquiv`, `OAI.ArExplicit.fullHomCocycleMap`, `OAI.ArExplicit.fullHomCohomologyMap`, `OAI.ArExplicit.fullHomPrecomp`, `OAI.ArExplicit.fullHomPrecompCocycle`, `OAI.ArExplicit.mapFullHom`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Cocycles_CocycleFunctor`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Cocycles/CocycleFunctor.lean), [`AuslanderReiten_Complete_CompleteFunctorCokernelAction`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Complete/CompleteFunctorCokernelAction.lean), [`AuslanderReiten_Complete_TateKoszul`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Complete/TateKoszul.lean), [`AuslanderReiten_Ext_ExternalEvaluationTerms`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Ext/ExternalEvaluationTerms.lean), [`AuslanderReiten_HomComplex_FullHomComposition`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/HomComplex/FullHomComposition.lean), [`AuslanderReiten_HomComplex_FullHomFunctor`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/HomComplex/FullHomFunctor.lean), [`AuslanderReiten_HomComplex_FullHomMap`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/HomComplex/FullHomMap.lean), [`AuslanderReiten_Resolutions_MapResolutionExtMk`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Resolutions/MapResolutionExtMk.lean), [`AuslanderReiten_Tensor_BalancedTensorDoubleLift`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/BalancedTensorDoubleLift.lean), [`AuslanderReiten_Tensor_BalancedTensorEquiv`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/BalancedTensorEquiv.lean).
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ031A036`, `OAIQ031A038`, `OAIQ031A042` and `OAIQ031A054`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_HomComplex_FullHomFunctor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ArExplicit

open CategoryTheory
open CochainComplex CochainComplex.HomComplex

variable {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
variable (Φ : C ⥤ D) [Φ.Additive] [Φ.Full] [Φ.Faithful]
variable (K L : CochainComplex C ℤ) (n : ℤ)

def fullHomCochainEquiv : Cochain K L n ≃+
    Cochain ((Φ.mapHomologicalComplex _).obj K) ((Φ.mapHomologicalComplex _).obj L) n where
  toFun x := x.map Φ
  invFun y := Cochain.mk fun p q hpq => Φ.preimage (y.v p q hpq)
  left_inv x := by
    apply Cochain.ext
    intro p q hpq
    exact Φ.preimage_map _
  right_inv y := by
    apply Cochain.ext
    intro p q hpq
    exact Φ.map_preimage _
  map_add' := fun x y => Cochain.map_add x y Φ

theorem fullHomCochainEquiv_differential (m : ℤ) (x : Cochain K L n) :
    δ n m (fullHomCochainEquiv Φ K L n x) = fullHomCochainEquiv Φ K L m (δ n m x) :=
  δ_map n m x Φ

def fullHomCocycleMap : Cocycle K L n →+
    Cocycle ((Φ.mapHomologicalComplex _).obj K) ((Φ.mapHomologicalComplex _).obj L) n where
  toFun x := Cocycle.mk (x.1.map Φ) (n + 1) rfl (by
    rw [δ_map, Cocycle.δ_eq_zero, Cochain.map_zero])
  map_zero' := by apply Cocycle.ext; exact Cochain.map_zero K L n Φ
  map_add' x y := by apply Cocycle.ext; exact Cochain.map_add x.1 y.1 Φ

theorem fullHomCocycleMap_boundary (x : Cocycle K L n) :
    fullHomCocycleMap Φ K L n x ∈
      coboundaries ((Φ.mapHomologicalComplex _).obj K) ((Φ.mapHomologicalComplex _).obj L) n ↔
      x ∈ coboundaries K L n := by
  rw [mem_coboundaries_iff _ (n - 1) (by omega), mem_coboundaries_iff _ (n - 1) (by omega)]
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨(fullHomCochainEquiv Φ K L (n - 1)).symm y, ?_⟩
    apply (fullHomCochainEquiv Φ K L n).injective
    rw [← fullHomCochainEquiv_differential, AddEquiv.apply_symm_apply]
    exact hy
  · rintro ⟨y, hy⟩
    refine ⟨y.map Φ, ?_⟩
    rw [δ_map, hy]
    rfl

def fullHomCohomologyMap : CohomologyClass K L n →+
    CohomologyClass ((Φ.mapHomologicalComplex _).obj K) ((Φ.mapHomologicalComplex _).obj L) n :=
  CohomologyClass.descAddMonoidHom
    ((CohomologyClass.mkAddMonoidHom _ _ _).comp (fullHomCocycleMap Φ K L n)) (by
      intro x hx
      exact (CohomologyClass.mk_eq_zero_iff _).mpr
        ((fullHomCocycleMap_boundary Φ K L n x).mpr hx))

@[simp] theorem fullHomCohomologyMap_mk (x : Cocycle K L n) :
    fullHomCohomologyMap Φ K L n (CohomologyClass.mk x) =
      CohomologyClass.mk (fullHomCocycleMap Φ K L n x) := rfl

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cocycles_CocycleFunctor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CochainComplex CochainComplex.HomComplex
namespace ArExplicit.ResolutionProducts
variable {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
variable (F : C ⥤ D) [F.Additive]
variable {K L : CochainComplex C ℤ} {n : ℤ}

theorem cocycle_map_hom (x : Cocycle K L n) :
    Cocycle.equivHomShift.symm (fullHomCocycleMap F K L n x) =
      ShiftedHom.map (Cocycle.equivHomShift.symm x) (F.mapHomologicalComplex (.up ℤ)) := by
  ext i
  change F.map (x.val.v i (i+n) rfl) ≫ 𝟙 _ =
    F.map (x.val.v i (i+n) rfl ≫ 𝟙 _) ≫ 𝟙 _
  simp

end ArExplicit.ResolutionProducts

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_HomComplex_FullHomComposition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ArExplicit

open CategoryTheory
open CochainComplex CochainComplex.HomComplex

variable {C : Type*} [Category* C] [Preadditive C]
variable {F G K : CochainComplex C ℤ} (φ : F ⟶ G) (n : ℤ)

def fullHomPrecompCocycle : Cocycle G K n →+ Cocycle F K n where
  toFun x := x.precomp φ
  map_zero' := by apply Cocycle.ext; simp
  map_add' x y := by apply Cocycle.ext; simp

def fullHomPrecomp : CohomologyClass G K n →+ CohomologyClass F K n :=
  CohomologyClass.descAddMonoidHom
    ((CohomologyClass.mkAddMonoidHom _ _ _).comp (fullHomPrecompCocycle φ n)) (by
      intro x hx
      apply (CohomologyClass.mk_eq_zero_iff _).mpr
      obtain ⟨m, hm, y, hy⟩ := hx
      refine ⟨m, hm, (Cochain.ofHom φ).comp y (zero_add m), ?_⟩
      simpa [fullHomPrecompCocycle] using congrArg (fun z => (Cochain.ofHom φ).comp z (zero_add n)) hy)

@[simp] theorem fullHomPrecomp_mk (x : Cocycle G K n) :
    fullHomPrecomp φ n (CohomologyClass.mk x) = CohomologyClass.mk (x.precomp φ) := rfl

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_HomComplex_FullHomMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit
open CategoryTheory CochainComplex.HomComplex
variable {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
variable (Φ : C ⥤ D) [Φ.Additive]
variable (K L : CochainComplex C ℤ) (n : ℤ)

def mapFullHom : CohomologyClass K L n →+
    CohomologyClass ((Φ.mapHomologicalComplex _).obj K)
      ((Φ.mapHomologicalComplex _).obj L) n :=
  CohomologyClass.descAddMonoidHom
    ((CohomologyClass.mkAddMonoidHom _ _ _).comp (fullHomCocycleMap Φ K L n)) (by
      intro x hx
      apply (CohomologyClass.mk_eq_zero_iff _).mpr
      obtain ⟨m, hm, y, hy⟩ := hx
      refine ⟨m, hm, y.map Φ, ?_⟩
      rw [δ_map, hy]
      rfl)

@[simp] theorem mapFullHom_mk (x : Cocycle K L n) :
    mapFullHom Φ K L n (CohomologyClass.mk x) =
      CohomologyClass.mk (fullHomCocycleMap Φ K L n x) := rfl

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Resolutions_MapResolutionExtMk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open CochainComplex CochainComplex.HomComplex HomologicalComplex
namespace ArExplicit.ResolutionProducts
universe u v u' v'
variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{v} C]
variable {D : Type u'} [Category.{v'} D] [Abelian D] [HasExt.{v'} D]
variable (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]
  [PreservesFiniteColimits F] [F.PreservesProjectiveObjects]
variable {X Y : C} (P : ProjectiveResolution X) {n : ℕ}

omit [Abelian C] [Abelian D] [HasExt.{v} C] [HasExt.{v'} D] [F.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F] [F.PreservesProjectiveObjects] in
theorem map_eval_cancel {U V W Z : C} {U' Z' : D}
    (a : U' ⟶ F.obj U) (b : U ⟶ V) (f : V ⟶ W) (e : Z ≅ W) (t : Z' ≅ F.obj W) :
    (a ≫ F.map ((b ≫ f) ≫ e.inv) ≫ (F.map e.hom ≫ t.inv)) ≫ t.hom =
      (a ≫ F.map b) ≫ F.map f := by
  simp only [Functor.map_comp, Category.assoc, t.inv_hom_id, Category.comp_id]
  rw [← F.map_comp e.inv e.hom, e.inv_hom_id, F.map_id, Category.comp_id]

end ArExplicit.ResolutionProducts

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Complete_CompleteFunctorCokernelAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits HomologicalComplex
open CochainComplex.HomComplex
open scoped ModuleCat.Algebra
namespace ArExplicit.CompleteComparison
universe u
variable {k R : Type u} [Field k] [CharP k 2] [Ring R] [Algebra k R]
variable [HasDerivedCategory (ModuleCat.{u} R)]
variable (F : ModuleCat.{u} R ⥤ ModuleCat.{u} R) [F.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F] [F.PreservesProjectiveObjects]
variable (K : CochainComplex (ModuleCat.{u} R) ℤ)

theorem endpoint_before {C : Type*} [Category* C]
    {X X' Y Y' Z Z' : C} (d : X ≅ X') (e : Y ≅ Y') (c : Y ≅ Z)
    (f : Z ≅ Z') (E : X' ≅ Z') (a : X ⟶ Y)
    (ha : a ≫ e.hom = d.hom ≫ (E ≪≫ (e.symm ≪≫ c ≪≫ f).symm).hom) :
    a ≫ c.hom = (d ≪≫ E ≪≫ f.symm).hom := by
  have ht := congrArg (fun z => z ≫ e.inv ≫ c.hom) ha
  simpa only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
    Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id, Category.comp_id] using ht

theorem endpoint_after {C : Type*} [Category* C]
    {X X' Y Y' Z Z' : C} (d : X ≅ X') (e : Y ≅ Y') (c : Y ≅ Z)
    (f : Z ≅ Z') (E : X' ≅ Z') (b : Y ⟶ X)
    (hb : b ≫ d.hom = e.hom ≫ (e.symm ≪≫ c ≪≫ f ≪≫ E.symm).hom) :
    c.inv ≫ b = (d ≪≫ E ≪≫ f.symm).inv := by
  apply (cancel_mono d.hom).1
  have ht := congrArg (fun z => c.inv ≫ z) hb
  simpa only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
    Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id,
    Category.comp_id] using ht

end ArExplicit.CompleteComparison

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Complete_TateKoszul
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

variable {x y : ∀ a : ℤ, H a →ₗ[k] H (a + 3)}

def row (a : ℤ) : (H a × H a) →ₗ[k] H (a + 3) := (x a).coprod (y a)

end ArExplicit.TateKoszul

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_BalancedTensorDoubleLift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.BalancedTensor
open scoped TensorProduct
universe u
variable {k A B F G X Y Z : Type u} [CommRing k] [Ring A] [Ring B]
  [AddCommGroup F] [AddCommGroup G] [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
  [Module k F] [Module k G] [Module k X] [Module k Y] [Module k Z]
  [Module Aᵐᵒᵖ F] [Module Bᵐᵒᵖ G] [Module A X] [Module B Y]

def curryFour (f : ((F ⊗[k] X) ⊗[k] (G ⊗[k] Y)) →ₗ[k] Z) :
    F →ₗ[k] X →ₗ[k] G →ₗ[k] Y →ₗ[k] Z :=
  TensorProduct.curry ((TensorProduct.lcurry (RingHom.id k) G Y Z).comp
    (TensorProduct.curry f))

@[simp] theorem curryFour_apply (h : ((F ⊗[k] X) ⊗[k] (G ⊗[k] Y)) →ₗ[k] Z)
    (f : F) (x : X) (g : G) (y : Y) :
    curryFour h f x g y = h ((f ⊗ₜ[k] x) ⊗ₜ[k] (g ⊗ₜ[k] y)) := rfl

end ArExplicit.BalancedTensor

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Ext_ExternalEvaluationTerms
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
variable (X : ModuleCat.{u} A) (Y : ModuleCat.{u} B)

variable (P : ChainComplex (ModuleCat.{u} (A ⊗[k] Aᵐᵒᵖ)) ℕ)
  (Q : ChainComplex (ModuleCat.{u} (B ⊗[k] Bᵐᵒᵖ)) ℕ)

theorem map_coproduct_inclusion
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {ι : Type*} (Z : ι → C) [HasCoproduct Z] [HasCoproduct (fun i => F.obj (Z i))]
    [PreservesColimit (Discrete.functor Z) F] (i : ι) :
    F.map (Sigma.ι Z i) ≫ (PreservesCoproduct.iso F Z).hom =
      Sigma.ι (fun i => F.obj (Z i)) i := by
  apply (cancel_mono (PreservesCoproduct.iso F Z).inv).mp
  rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  simp only [PreservesCoproduct.inv_hom, sigmaComparison, Sigma.ι_desc]

end ArExplicit.ExternalBalanced

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_BalancedTensorEquiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.BalancedTensor
universe u
variable {k R F F' M M' : Type u} [CommRing k] [Ring R]
  [AddCommGroup F] [AddCommGroup F'] [AddCommGroup M] [AddCommGroup M']
  [Module k F] [Module k F'] [Module k M] [Module k M']
  [Module Rᵐᵒᵖ F] [Module Rᵐᵒᵖ F'] [Module R M] [Module R M']
variable (e : F ≃ₗ[k] F') (v : M ≃ₗ[k] M')
  (he : ∀ (r : Rᵐᵒᵖ) x, e (r • x) = r • e x)
  (hv : ∀ (r : R) x, v (r • x) = r • v x)

include he hv

omit hv in
theorem inverse_equivariant_right (r : Rᵐᵒᵖ) (x : F') :
    e.symm (r • x) = r • e.symm x := by
  apply e.injective
  rw [LinearEquiv.apply_symm_apply, he, LinearEquiv.apply_symm_apply]

omit he in
theorem inverse_equivariant_left (r : R) (x : M') :
    v.symm (r • x) = r • v.symm x := by
  apply v.injective
  rw [LinearEquiv.apply_symm_apply, hv, LinearEquiv.apply_symm_apply]

end ArExplicit.BalancedTensor

end

end OAI
end


