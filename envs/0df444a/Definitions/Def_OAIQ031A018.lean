-- Prove2me | Definitions.Def_OAIQ031A018
-- name    : OAIQ031A018
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T12:56:57.043384+00:00
-- url     : https://prove2.me/theorems/b876634a-4847-4af8-8aae-6bd37c12cf6a
-- title:
--   Definitions bundle OAIQ031A018 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 18 declarations of OpenAI's Lean: 5 definitions, 1 inductive type or structure, 1 instance and 11 theorems. The definitions and types are `OAI.ArExplicit.TriangleGradedSequence.Bottom`, `OAI.ArExplicit.TwistedLeftModule`, `OAI.ArExplicit.TwistedLeftModule.coordinates`, `OAI.ArExplicit.cokernelProductMap`, `OAI.ArExplicit.eightCoordinates`, `OAI.ArExplicit.iteratedShiftIso`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: `AuslanderReiten_Bar_ExternalBarEvaluation`, `AuslanderReiten_Bar_ExternalBarFreeAugmentation`, `AuslanderReiten_Cones_CokernelProduct`, `AuslanderReiten_Cones_MappingConeNaturality`, `AuslanderReiten_Coordinates_IteratedShiftNaturality`, `AuslanderReiten_Ext_ExtKunnethMap`, `AuslanderReiten_Ext_ExternalEvaluatedFreeCoordinate`, `AuslanderReiten_Ext_ExternalEvaluatedFreeValues`, `AuslanderReiten_Ext_ExternalEvaluationComparison`, `AuslanderReiten_Ext_ExternalEvaluationCubic`, `AuslanderReiten_HomComplex_FullHomShiftedProducts`, `AuslanderReiten_Homology_SplitQuotient`, `AuslanderReiten_Homology_TriangleGradedSequence`, `AuslanderReiten_Tensor_TwistedTensor`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ031A039`, `OAIQ031A040` and `OAIQ031A041`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Ext_ExternalEvaluationCubic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.ExternalBalanced
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
theorem post_natural {C : Type*} [Category C]
    {A B D A' : C} {f : A ⟶ B} {g : B ⟶ D} {u : A ⟶ A'} {v : A' ⟶ D}
    (h : f ≫ g = u ≫ v) {Z : C} (w : D ⟶ Z) :
    f ≫ (g ≫ w) = u ≫ (v ≫ w) := by
  rw [← Category.assoc, h, Category.assoc]

universe u

end ArExplicit.ExternalBalanced

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_ExternalBarEvaluation
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

theorem compose_squares {C : Type*} [Category C]
    {A B C' A' B' C'' : C} {f : A ⟶ A'} {g : B ⟶ B'} {h : C' ⟶ C''}
    {a : A ⟶ B} {a' : A' ⟶ B'} {b : B ⟶ C'} {b' : B' ⟶ C''}
    (ha : f ≫ a' = a ≫ g) (hb : g ≫ b' = b ≫ h) :
    f ≫ (a' ≫ b') = (a ≫ b) ≫ h := by
  rw [← Category.assoc, ha, Category.assoc, hb, ← Category.assoc]

end ArExplicit.ExternalBalanced

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Bar_ExternalBarFreeAugmentation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit.ExternalTensor
open CategoryTheory
open scoped TensorProduct
theorem iso_cancel_pair {C : Type*} [Category C]
    {P Q R S V : C} (a : P ⟶ Q) (e : Q ≅ R) (f : R ≅ S) (b : Q ⟶ V) :
    (a ≫ e.hom ≫ f.hom) ≫ (f.inv ≫ e.inv ≫ b) = a ≫ b := by
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

universe u

end ArExplicit.ExternalTensor

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cones_CokernelProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit

variable {R M N P Q : Type*} [Ring R]
variable [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
variable [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]

def cokernelProductMap (f : M →ₗ[R] N) (g : P →ₗ[R] Q) :
    (N × Q) ⧸ LinearMap.range (f.prodMap g) →ₗ[R]
      (N ⧸ LinearMap.range f) × (Q ⧸ LinearMap.range g) :=
  (LinearMap.range (f.prodMap g)).liftQ
    (((LinearMap.range f).mkQ).prodMap ((LinearMap.range g).mkQ)) (by
      rintro x ⟨⟨m, p⟩, rfl⟩
      change (Submodule.Quotient.mk (f m), Submodule.Quotient.mk (g p)) = (0, 0)
      exact Prod.ext ((Submodule.Quotient.mk_eq_zero _).mpr ⟨m, rfl⟩)
        ((Submodule.Quotient.mk_eq_zero _).mpr ⟨p, rfl⟩))

@[simp]
theorem cokernelProductMap_mk (f : M →ₗ[R] N) (g : P →ₗ[R] Q) (n : N) (q : Q) :
    cokernelProductMap f g (Submodule.Quotient.mk (n, q)) =
      (Submodule.Quotient.mk n, Submodule.Quotient.mk q) := rfl

theorem cokernelProductMap_bijective (f : M →ₗ[R] N) (g : P →ₗ[R] Q) :
    Function.Bijective (cokernelProductMap f g) := by
  constructor
  · apply (LinearMap.ker_eq_bot).mp
    apply LinearMap.ker_eq_bot'.mpr
    intro x hx
    obtain ⟨⟨n, q⟩, rfl⟩ := (LinearMap.range (f.prodMap g)).mkQ_surjective x
    obtain ⟨m, hm⟩ := (Submodule.Quotient.mk_eq_zero _).mp (congrArg Prod.fst hx)
    obtain ⟨p, hp⟩ := (Submodule.Quotient.mk_eq_zero _).mp (congrArg Prod.snd hx)
    exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨(m, p), Prod.ext hm hp⟩
  · rintro ⟨n, q⟩
    obtain ⟨n, rfl⟩ := (LinearMap.range f).mkQ_surjective n
    obtain ⟨q, rfl⟩ := (LinearMap.range g).mkQ_surjective q
    exact ⟨Submodule.Quotient.mk (n, q), rfl⟩

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cones_MappingConeNaturality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory HomologicalComplex
open CochainComplex CochainComplex.HomComplex

namespace ArExplicit

universe u
variable {R : Type u} [Ring R]
variable {F₁ G₁ F₂ G₂ : CochainComplex (ModuleCat.{u} R) ℤ}
variable {φ₁ : F₁ ⟶ G₁} {φ₂ : F₂ ⟶ G₂} {a : F₁ ⟶ F₂} {b : G₁ ⟶ G₂}
variable (H : Homotopy (φ₁ ≫ b) (a ≫ φ₂)) (hH : H.hom 1 0 = 0)

include hH in

theorem mappingCone_map_snd_zero :
    (mappingCone.mapOfHomotopy H).f 0 ≫ (mappingCone.snd φ₂).v 0 0 (add_zero 0) =
      (mappingCone.snd φ₁).v 0 0 (add_zero 0) ≫ b.f 0 := by
  apply mappingCone.ext_from φ₁ 1 0 (by decide)
  · simp only [mappingCone.mapOfHomotopy, mappingCone.inl_v_desc_f_assoc,
      Cochain.add_v, Cochain.zero_cochain_comp_v, Cochain.ofHom_v,
      Cochain.comp_zero_cochain_v, Preadditive.add_comp, Category.assoc,
      mappingCone.inl_v_snd_v, mappingCone.inr_f_snd_v, Category.comp_id,
      Limits.comp_zero, mappingCone.inl_v_snd_v_assoc, Limits.zero_comp, zero_add]
    change H.hom 1 0 = 0
    exact hH
  · simp [mappingCone.mapOfHomotopy]

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Coordinates_IteratedShiftNaturality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory

namespace ArExplicit

universe v u
variable {C : Type u} [Category.{v} C] [HasShift C ℤ]
variable (Y : ℕ → C) (s : ∀ n, Y n ≅ (Y (n + 1))⟦(1 : ℤ)⟧)

def iteratedShiftIso : ∀ n : ℕ, Y 0 ≅ (Y n)⟦(n : ℤ)⟧
  | 0 => (CategoryTheory.shiftFunctorZero C ℤ).symm.app (Y 0)
  | n + 1 => iteratedShiftIso n ≪≫
      (CategoryTheory.shiftFunctor C (n : ℤ)).mapIso (s n) ≪≫
      (CategoryTheory.shiftFunctorAdd' C (1 : ℤ) (n : ℤ)
        ((n + 1 : ℕ) : ℤ) (by omega)).symm.app (Y (n + 1))

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Ext_ExtKunnethMap
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

theorem homology_conjugate {K L : CochainComplex (ModuleCat.{u} k) ℕ}
    (e : K ≅ L) (f : K ⟶ K) (n : ℕ) (x : L.homology n) :
    ((homologyFunctor (ModuleCat.{u} k) (.up ℕ) n).mapIso e).inv.hom
      ((homologyMap (e.inv ≫ f ≫ e.hom) n).hom x) =
    (homologyMap f n).hom
      (((homologyFunctor (ModuleCat.{u} k) (.up ℕ) n).mapIso e).inv.hom x) := by
  have h : homologyMap (e.inv ≫ f ≫ e.hom) n ≫ homologyMap e.inv n =
      homologyMap e.inv n ≫ homologyMap f n := by
    rw [← homologyMap_comp, Category.assoc, Category.assoc, e.hom_inv_id,
      Category.comp_id, homologyMap_comp]
  exact congrArg (fun a => a.hom x) h

end ArExplicit.ExternalTensor

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Ext_ExternalEvaluationComparison
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
variable (X : ModuleCat.{u} A) (Y : ModuleCat.{u} B)
variable (P : ChainComplex (ModuleCat.{u} (A ⊗[k] Aᵐᵒᵖ)) ℕ)
  (Q : ChainComplex (ModuleCat.{u} (B ⊗[k] Bᵐᵒᵖ)) ℕ)
variable (P' : ChainComplex (ModuleCat.{u} A) ℕ) (Q' : ChainComplex (ModuleCat.{u} B) ℕ)

theorem compose_after {C : Type*} [Category C]
    {U V W X Y Z : C} {a : U ⟶ V} {b : V ⟶ W} {c : W ⟶ X}
    {d : U ⟶ Y} {e : Y ⟶ W} {f : Y ⟶ Z} {g : Z ⟶ X}
    (h₁ : a ≫ b = d ≫ e) (h₂ : e ≫ c = f ≫ g) :
    a ≫ (b ≫ c) = d ≫ (f ≫ g) := by
  rw [← Category.assoc, h₁, Category.assoc, h₂]

end ArExplicit.ExternalBalanced

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Ext_ExternalEvaluatedFreeCoordinate
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
variable (e : M ≃ₗ[k] k) (f : N ≃ₗ[k] k)

theorem postcompose_square {C : Type*} [Category C]
    {U V W V₁ V₂ V₃ : C} {a : U ⟶ V} {b : V ⟶ W} {c : W ⟶ V₁}
    {d : U ⟶ V₂} {h : V₂ ⟶ V₃} {i : V₃ ⟶ W} {j : V₃ ⟶ V₁}
    (h₁ : a ≫ b = d ≫ h ≫ i) (h₂ : i ≫ c = j) :
    a ≫ (b ≫ c) = d ≫ h ≫ j := by
  rw [← Category.assoc, h₁, Category.assoc, Category.assoc, h₂]

end ArExplicit.ExternalBalanced

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Ext_ExternalEvaluatedFreeValues
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
variable (e : M ≃ₗ[k] k) (f : N ≃ₗ[k] k)

theorem valueOfComposite {R : Type*} [Ring R] {U V W : ModuleCat R}
    {inclusion : U ⟶ V} {evaluation : V ⟶ W} {composite : U ⟶ W}
    (equality : inclusion ≫ evaluation = composite) (input : U) :
    evaluation (inclusion input) = composite input := by
  rw [← ModuleCat.comp_apply, equality]

end ArExplicit.ExternalBalanced

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_HomComplex_FullHomShiftedProducts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit
open CategoryTheory
open CochainComplex CochainComplex.HomComplex
universe u v w

section Functor
variable {C D : Type*} [Category* C] [Category* D] [HasShift C ℤ] [HasShift D ℤ]
variable (F : C ⥤ D) [F.CommShift ℤ]
variable {X Y Z : C} {n m : ℤ}

theorem map_shifted_composition (f : X ⟶ Y⟦n⟧) (g : Y ⟶ Z⟦m⟧) :
    F.map (f ≫ g⟦n⟧' ≫ (CategoryTheory.shiftFunctorAdd' C m n (n+m) (add_comm m n)).inv.app Z) ≫
      (F.commShiftIso (n+m)).hom.app Z =
    (F.map f ≫ (F.commShiftIso n).hom.app Y) ≫
      (F.map g ≫ (F.commShiftIso m).hom.app Z)⟦n⟧' ≫
        (CategoryTheory.shiftFunctorAdd' D m n (n+m) (add_comm m n)).inv.app (F.obj Z) := by
  have h := NatTrans.congr_app (congrArg Iso.hom (F.commShiftIso_add' (add_comm m n))) Z
  simp only [Functor.CommShift.isoAdd'_hom_app] at h
  rw [h]
  simp only [Functor.map_comp, Category.assoc]
  rw [← F.map_comp_assoc
    ((CategoryTheory.shiftFunctorAdd' C m n (n+m) (add_comm m n)).inv.app Z)
    ((CategoryTheory.shiftFunctorAdd' C m n (n+m) (add_comm m n)).hom.app Z),
    Iso.inv_hom_id_app, F.map_id, Category.id_comp]
  rw [F.commShiftIso_hom_naturality_assoc g n]

end Functor

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Homology_SplitQuotient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit

def eightCoordinates (k : Type*) [CommSemiring k] :
    (((k × k) × (k × k)) × ((k × k) × (k × k))) ≃ₐ[k] (Fin 8 → k) where
  toFun a := ![a.1.1.1, a.1.1.2, a.1.2.1, a.1.2.2, a.2.1.1, a.2.1.2, a.2.2.1, a.2.2.2]
  invFun a := (((a 0, a 1), (a 2, a 3)), ((a 4, a 5), (a 6, a 7)))
  left_inv a := rfl
  right_inv a := by ext i; fin_cases i <;> rfl
  map_mul' a b := by ext i; fin_cases i <;> rfl
  map_add' a b := by ext i; fin_cases i <;> rfl
  commutes' c := by ext i; fin_cases i <;> rfl

end ArExplicit

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Homology_TriangleGradedSequence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Pretriangulated

namespace ArExplicit.TriangleGradedSequence

universe u v w
variable (k : Type u) [CommRing k]
variable {C : Type w} [Category.{v} C] [Preadditive C] [Linear k C]
variable [Limits.HasZeroObject C] [HasShift C ℤ]
variable [∀ n : ℤ, (CategoryTheory.shiftFunctor C n).Additive] [Pretriangulated C]
variable (T : Triangle C) (X : C)

abbrev Bottom (n : ℤ) := X ⟶ (T⟦n⟧).obj₁

end ArExplicit.TriangleGradedSequence

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_TwistedTensor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit

@[ext] structure TwistedLeftModule (k R : Type*) [CommRing k] [Ring R] [Algebra k R]
    (σ : R ≃ₐ[k] R) (M : Type*) where
  value : M

namespace TwistedLeftModule

variable {k R M : Type*} [CommRing k] [Ring R] [Algebra k R]
variable [AddCommGroup M] [Module k M] [Module R M]
variable [IsScalarTower k R M] [SMulCommClass k R M]
variable (σ : R ≃ₐ[k] R)

def coordinates : TwistedLeftModule k R σ M ≃ M where
  toFun := value
  invFun := TwistedLeftModule.mk
  left_inv _ := rfl
  right_inv _ := rfl

instance instAddCommGroup : AddCommGroup (TwistedLeftModule k R σ M) := (coordinates σ).addCommGroup

end TwistedLeftModule

end ArExplicit

end OAI
end


