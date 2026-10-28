-- Prove2me | Definitions.Def_OAIQ031A010
-- name    : OAIQ031A010
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T12:56:27.122504+00:00
-- url     : https://prove2.me/theorems/40ac2962-3691-4f2d-815c-ef2375e34fbf
-- title:
--   Definitions bundle OAIQ031A010 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 10 declarations of OpenAI's Lean: 5 definitions and 5 theorems. The definitions and types are `OAI.ArExplicit.CompleteComparison.cocycleProduct`, `OAI.ArExplicit.TateKoszul.degreeEquiv`, `OAI.ArExplicit.TriangleRecurrence.shiftedMapEquiv`, `OAI.ArExplicit.derivedSingleIso`, `OAI.ArExplicit.fullCohomologyDerivedEquiv`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Complete_TateKoszul`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Complete/TateKoszul.lean), [`AuslanderReiten_Ext_ExtendShortExact`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Ext/ExtendShortExact.lean), [`AuslanderReiten_HomComplex_FullHomProducts`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/HomComplex/FullHomProducts.lean), [`AuslanderReiten_Homology_DerivedHomVanishing`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Homology/DerivedHomVanishing.lean), [`AuslanderReiten_Homology_DerivedSingle`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Homology/DerivedSingle.lean), [`AuslanderReiten_Homology_TriangleRecurrence`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Homology/TriangleRecurrence.lean).
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ031A033`, `OAIQ031A035` and `OAIQ031A038`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib

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

def degreeEquiv {a b : ℤ} (h : a = b) : H a ≃ₗ[k] H b := by
  subst b
  exact LinearEquiv.refl k (H a)

end ArExplicit.TateKoszul

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Ext_ExtendShortExact
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
variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}

theorem extend_shortExact (e : c.Embedding c')
    (S : ShortComplex (HomologicalComplex C c)) (h : S.ShortExact) :
    (S.map (e.extendFunctor C)).ShortExact := by
  have := h.mono_f
  have := h.epi_g
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro j
  by_cases hj : ∃ i, e.f i = j
  · obtain ⟨i, hi⟩ := hj
    let E : ((S.map (e.extendFunctor C)).map (HomologicalComplex.eval C c' j)) ≅
        S.map (HomologicalComplex.eval C c i) :=
      ShortComplex.isoMk (S.X₁.extendXIso e hi) (S.X₂.extendXIso e hi)
        (S.X₃.extendXIso e hi)
        (by
          change (S.X₁.extendXIso e hi).hom ≫ S.f.f i =
            (HomologicalComplex.extendMap S.f e).f j ≫ (S.X₂.extendXIso e hi).hom
          rw [HomologicalComplex.extendMap_f _ _ hi]
          simp)
        (by
          change (S.X₂.extendXIso e hi).hom ≫ S.g.f i =
            (HomologicalComplex.extendMap S.g e).f j ≫ (S.X₃.extendXIso e hi).hom
          rw [HomologicalComplex.extendMap_f _ _ hi]
          simp)
    exact ShortComplex.shortExact_of_iso E.symm (h.map (HomologicalComplex.eval C c i))
  · have hj' : ∀ i, e.f i ≠ j := by simpa using hj
    have h₁ := S.X₁.isZero_extend_X e j hj'
    have h₂ := S.X₂.isZero_extend_X e j hj'
    have h₃ := S.X₃.isZero_extend_X e j hj'
    exact { exact := ShortComplex.exact_of_isZero_X₂ _ h₂
            mono_f := h₁.mono _
            epi_g := h₃.epi _ }

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_HomComplex_FullHomProducts
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

def cocycleProduct (x : Cocycle K L n) (y : Cocycle L M m) : Cocycle K M (n + m) :=
  Cocycle.mk (x.1.comp y.1 rfl) _ rfl (by
    rw [δ_comp x.1 y.1 rfl (n + 1) (m + 1) (n + m + 1) rfl rfl rfl]
    simp)

end Cochains

end ArExplicit.CompleteComparison

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Homology_DerivedHomVanishing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory
namespace ArExplicit
universe u v
variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory C]
open CochainComplex.HomComplex

def fullCohomologyDerivedEquiv (K L : CochainComplex C ℤ) (n : ℤ) [K.IsKProjective] :
    CohomologyClass K L n ≃ (DerivedCategory.Q.obj K ⟶ (DerivedCategory.Q.obj L)⟦n⟧) :=
  CohomologyClass.homAddEquiv.toEquiv.trans
    ((Equiv.ofBijective DerivedCategory.Qh.map
      (CochainComplex.IsKProjective.Qh_map_bijective K
        ((HomotopyCategory.quotient C _).obj (L⟦n⟧)))).trans
      (Iso.homCongr ((DerivedCategory.quotientCompQhIso C).app K)
        (((DerivedCategory.quotientCompQhIso C).app (L⟦n⟧)) ≪≫
          (DerivedCategory.Q.commShiftIso n).app L)))

theorem derivedHom_zero_of_cochain_zero (K L : CochainComplex C ℤ) (n : ℤ)
    [K.IsKProjective] (h : ∀ a : Cochain K L n, a = 0)
    (f : DerivedCategory.Q.obj K ⟶ (DerivedCategory.Q.obj L)⟦n⟧) : f = 0 := by
  have hc : ∀ a : CohomologyClass K L n, a = 0 := by
    intro a
    obtain ⟨b, rfl⟩ := CohomologyClass.mk_surjective a
    have hb : b = 0 := Subtype.ext (h b.val)
    rw [hb, CohomologyClass.mk_zero]
  have : Subsingleton (CohomologyClass K L n) := ⟨fun a b => (hc a).trans (hc b).symm⟩
  exact (fullCohomologyDerivedEquiv K L n).symm.injective (Subsingleton.elim _ _)

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Homology_DerivedSingle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory
namespace ArExplicit
universe u v w
variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

def derivedSingleIso (K : CochainComplex C ℤ) (n : ℤ)
    (hex : ∀ i : ℤ, i ≠ n → K.ExactAt i) :
    DerivedCategory.Q.obj K ≅ (DerivedCategory.singleFunctor C n).obj (K.homology n) := Classical.choice (by
  let : K.IsGE n := (CochainComplex.isGE_iff K n).mpr (fun i hi => hex i (ne_of_lt hi))
  let : K.IsLE n := (CochainComplex.isLE_iff K n).mpr (fun i hi => hex i (ne_of_gt hi))
  let : (DerivedCategory.Q.obj K).IsGE n := (DerivedCategory.isGE_Q_obj_iff K n).mpr inferInstance
  let : (DerivedCategory.Q.obj K).IsLE n := (DerivedCategory.isLE_Q_obj_iff K n).mpr inferInstance
  obtain ⟨M, ⟨e⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE
    (DerivedCategory.Q.obj K) n
  let h : K.homology n ≅ M :=
    ((DerivedCategory.homologyFunctorFactors C n).app K).symm ≪≫
      (DerivedCategory.homologyFunctor C n).mapIso e ≪≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso C n).app M
  exact ⟨e ≪≫ (DerivedCategory.singleFunctor C n).mapIso h.symm⟩)

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Homology_TriangleRecurrence
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

theorem connecting_surjective (h : ∀ f : T.obj₂ ⟶ Y, f = 0) :
    Function.Surjective (fun f : T.obj₁⟦(1 : ℤ)⟧ ⟶ Y => T.mor₃ ≫ f) := by
  intro f
  obtain ⟨g, hg⟩ := T.yoneda_exact₃ hT f (h _)
  exact ⟨g, hg.symm⟩

theorem connecting_injective (h : ∀ f : T.obj₂⟦(1 : ℤ)⟧ ⟶ Y, f = 0) :
    Function.Injective (fun f : T.obj₁⟦(1 : ℤ)⟧ ⟶ Y => T.mor₃ ≫ f) := by
  intro f g hfg
  change T.mor₃ ≫ f = T.mor₃ ≫ g at hfg
  have hz : T.mor₃ ≫ (f - g) = 0 := by
    rw [Preadditive.comp_sub, hfg, sub_self]
  obtain ⟨a, ha⟩ := T.rotate.rotate.yoneda_exact₂
    (rot_of_distTriang _ (rot_of_distTriang _ hT)) (f - g) hz
  have ha0 : a = 0 := h a
  have hf : f - g = 0 := by
    rw [ha, ha0]
    exact Limits.comp_zero
  exact sub_eq_zero.mp hf

theorem connecting_bijective
    (h₀ : ∀ f : T.obj₂ ⟶ Y, f = 0)
    (h₁ : ∀ f : T.obj₂⟦(1 : ℤ)⟧ ⟶ Y, f = 0) :
    Function.Bijective (fun f : T.obj₁⟦(1 : ℤ)⟧ ⟶ Y => T.mor₃ ≫ f) :=
  ⟨connecting_injective T hT Y h₁, connecting_surjective T hT Y h₀⟩

omit hT in

def shiftedMapEquiv (X Z : C) (a b c : ℤ) (h : b + a = c) :
    ShiftedHom X Z b ≃ (X⟦a⟧ ⟶ Z⟦c⟧) :=
  (Functor.FullyFaithful.ofFullyFaithful (shiftFunctor C a)).homEquiv.trans
    (((shiftFunctorAdd' C b a c h).symm.app Z).homToEquiv)

end ArExplicit.TriangleRecurrence

end

end OAI
end


