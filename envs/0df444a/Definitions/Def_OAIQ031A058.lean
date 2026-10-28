-- Prove2me | Definitions.Def_OAIQ031A058
-- name    : OAIQ031A058
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T14:08:39.631312+00:00
-- url     : https://prove2.me/theorems/82eee94c-f846-49e3-9fa7-40fdff29d641
-- title:
--   Definitions bundle OAIQ031A058 of the split of OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.ArExplicit.Statement.main`, carved from OpenAI's openai/math development (OpenAI, *An explicit counterexample to the Auslander-Reiten conjecture (result family 199)*, OpenAI Math Release, September 23, 2026, result family 199, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 14 declarations of OpenAI's Lean: 1 definition, 1 inductive type or structure, 1 instance and 11 theorems. The definitions and types are `OAI.ArExplicit.TwoConeKoszulCoordinates`, `OAI.ArExplicit.coverFullHomEquiv`.
--
--   **Sources.** They come from these modules of lean/OAI/Algebra, in whole or in part: [`AuslanderReiten_Cones_ConeCohomology`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Cones/ConeCohomology.lean), [`AuslanderReiten_Cones_TwoConeFiltration`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Cones/TwoConeFiltration.lean), [`AuslanderReiten_Cones_TwoConeKoszulCoordinates`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Cones/TwoConeKoszulCoordinates.lean), [`AuslanderReiten_Coordinates_IteratedCubicCoordinates`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Coordinates/IteratedCubicCoordinates.lean), [`AuslanderReiten_Ext_ExactFunctorExtIso`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Ext/ExactFunctorExtIso.lean), [`AuslanderReiten_Ext_ExactFunctorExtNaturality`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Ext/ExactFunctorExtNaturality.lean), [`AuslanderReiten_Homology_TriangleGradedSequence`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Homology/TriangleGradedSequence.lean), [`AuslanderReiten_Resolutions_CoverFullHomAction`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Resolutions/CoverFullHomAction.lean), [`AuslanderReiten_Resolutions_CoverStepFullHom`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Resolutions/CoverStepFullHom.lean), [`AuslanderReiten_Tensor_TwistedTensor`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Algebra/AuslanderReiten/Tensor/TwistedTensor.lean).
--
--   **Imports.** It imports the bundles `OAIQ031A028`, `OAIQ031A035`, `OAIQ031A036`, `OAIQ031A038`, `OAIQ031A040`, `OAIQ031A041` and `OAIQ031A042` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ031A074`, `OAIQ031A075` and `OAIQ031A076`.
-- source:
--   OpenAI, An explicit counterexample to the Auslander-Reiten conjecture (result family 199), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 199; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-explicit-counterexample-to-the-Auslander-Reiten-conjecture-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algebra at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ031A028
import Definitions.Def_OAIQ031A035
import Definitions.Def_OAIQ031A036
import Definitions.Def_OAIQ031A038
import Definitions.Def_OAIQ031A040
import Definitions.Def_OAIQ031A041
import Definitions.Def_OAIQ031A042

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cones_ConeCohomology
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ArExplicit

open CategoryTheory HomologicalComplex
open CochainComplex CochainComplex.HomComplex

variable {C : Type*} [Category* C] [Preadditive C]
variable {F G : CochainComplex C ℤ} (φ : F ⟶ G) (n : ℤ)

variable [HasHomotopyCofiber φ]

theorem coneEnd_cohomology_subsingleton
    (hzero : ∀ m (x : Cochain G F m), x = 0)
    (hinj : Function.Injective (coneComparison φ n))
    (hsurj : Function.Surjective (coneComparison φ (n - 1))) :
    Subsingleton (CohomologyClass (mappingCone φ) (mappingCone φ) n) := by
  apply subsingleton_of_forall_eq 0
  intro x
  obtain ⟨x, rfl⟩ := CohomologyClass.mk_surjective x
  exact (CohomologyClass.mk_eq_zero_iff x).mpr
    (coneEnd_cocycle_is_boundary φ n hzero hinj hsurj x)

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cones_TwoConeFiltration
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit

universe u

variable {k : Type u} [Field k]
variable (B D E K W : ℤ → Type u)
variable [∀ n, AddCommGroup (B n)] [∀ n, Module k (B n)]
variable [∀ n, AddCommGroup (D n)] [∀ n, Module k (D n)]
variable [∀ n, AddCommGroup (E n)] [∀ n, Module k (E n)]
variable [∀ n, AddCommGroup (K n)] [∀ n, Module k (K n)]
variable [∀ n, AddCommGroup (W n)] [∀ n, Module k (W n)]

namespace TwoConeFiltration

variable {B D E K W}
variable (F : TwoConeFiltration (k := k) B D E K W)

variable (hrow : ∀ n : ℤ, n ≠ -1 → Function.Surjective (F.row n))
variable (hcolumn : ∀ n : ℤ, n ≠ 3 → Function.Injective (F.column n))
variable (hKoszul : ∀ n : ℤ,
  LinearMap.range (F.column n) = LinearMap.ker (F.row (n + 1)))

include hrow hcolumn hKoszul in

theorem subsingleton_of_ne (n : ℤ) (h0 : n ≠ 0) (h3 : n ≠ 3) :
    Subsingleton (W n) := by
  apply subsingleton_of_forall_eq 0
  intro w
  have hp : F.projection n w ∈ LinearMap.ker (F.attach n) := by
    rw [← F.projection_attach]
    exact LinearMap.mem_range_self _ w
  have hp0 : F.projection n w = 0 := (F.attach_injective n (hcolumn n h3)).eq_iff.mp
    (by change F.attach n (F.projection n w) = 0 at hp; simpa only [map_zero] using hp)
  have hw : w ∈ LinearMap.range (F.inclusion n) := by
    rw [F.inclusion_projection]
    exact hp0
  obtain ⟨x, rfl⟩ := hw
  rw [F.inclusion_zero hrow hKoszul n h0]
  rfl

end TwoConeFiltration
end ArExplicit

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cones_TwoConeKoszulCoordinates
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
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

structure TwoConeKoszulCoordinates where
  bottom : ∀ n, B n ≃ₗ[k] H n
  middle : ∀ n, D n ≃ₗ[k] (H (n-2) × H (n-2))
  top : ∀ n, E n ≃ₗ[k] H (n-4)
  row_eq : ∀ n v, bottom (n+1) (F.row n v) =
    TateKoszul.degreeEquiv (k := k) H (show n-2+3=n+1 by omega)
      (TateKoszul.row (x := x) (y := y) (n-2) (middle n v))
  column_eq : ∀ n v, middle (n+1) (F.column n v) =
    ((TateKoszul.degreeEquiv (k := k) H (show n-4+3=n+1-2 by omega)).prodCongr
      (TateKoszul.degreeEquiv (k := k) H (show n-4+3=n+1-2 by omega)))
      (TateKoszul.column (x := x) (y := y) (n-4) (top n v))

namespace TwoConeKoszulCoordinates
variable {F x y}
variable (C : TwoConeKoszulCoordinates F x y) (M : TateKoszul.Model x y)

theorem row_zero_reindex {a b : ℤ} (h : a=b) (v : H a × H a) :
    TateKoszul.row (x := x) (y := y) a v = 0 ↔
      TateKoszul.row (x := x) (y := y) b
        (((TateKoszul.degreeEquiv (k := k) H h).prodCongr (TateKoszul.degreeEquiv (k := k) H h)) v) = 0 := by
  subst b
  rfl

include C M

theorem middle_four_subsingleton : Subsingleton (D 4) := by
  let : Subsingleton (H (4-2)) := M.outside _ (fun n h => by omega) (fun n h => by omega)
  exact (C.middle 4).injective.subsingleton

end TwoConeKoszulCoordinates
end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Coordinates_IteratedCubicCoordinates
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace ArExplicit
open CategoryTheory
universe u v
variable {C : Type u} [Category.{v} C] [HasShift C ℤ]
variable (Y : ℕ → C) (s : ∀ n, Y n ≅ (Y (n+1))⟦(1 : ℤ)⟧)

variable {X : C} (u : X ≅ Y 0)

theorem basedIteration_three_hom (n : ℕ) :
    (basedIteration Y s u (n+3)).hom =
      ShiftedHom.comp (basedIteration Y s u 3).hom
        (iteratedShiftIso (fun j => Y (j+3)) (fun j => s (j+3)) n).hom
          (by omega : (n:ℤ)+3=((n+3:ℕ):ℤ)) := by
  change u.hom ≫ (iteratedShiftIso Y s (n+3)).hom = _
  rw [iteratedShiftIso_three_hom]
  simp only [basedIteration, Iso.trans_hom, ShiftedHom.comp, Category.assoc]

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Ext_ExactFunctorExtNaturality
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
namespace ArExplicit.ResolutionProducts
universe u v u' v'
variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{v} C]
variable {D : Type u'} [Category.{v'} D] [Abelian D] [HasExt.{v'} D]
variable (F G : C ⥤ D) [F.Additive] [G.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F] [F.PreservesProjectiveObjects]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G] [G.PreservesProjectiveObjects]
variable (η : F ⟶ G) {X Y : C} (P : ProjectiveResolution X)

include P in
theorem mapExactFunctor_natural (n : ℕ) (x : Ext X Y n) :
    (x.mapExactFunctor F).comp (Ext.mk₀ (η.app Y)) (add_zero n) =
      (Ext.mk₀ (η.app X)).comp (x.mapExactFunctor G) (zero_add n) := by
  obtain ⟨f, hf, rfl⟩ := P.extMk_surjective x (n+1) rfl
  rw [map_extMk, map_extMk]
  erw [ProjectiveResolution.extMk_comp_mk₀,
    ProjectiveResolution.mk₀_comp_extMk _ _ _ _ (mapResolutionNatHom F G η P)]
  congr 1
  exact η.naturality f

end ArExplicit.ResolutionProducts

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Ext_ExactFunctorExtIso
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
namespace ArExplicit.ResolutionProducts
universe u v
variable {k : Type u} [CommRing k]
variable {C : Type v} [Category.{u} C] [Abelian C] [HasExt.{u} C] [Linear k C]
variable (F G : C ⥤ C) [F.Additive] [G.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F] [F.PreservesProjectiveObjects]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G] [G.PreservesProjectiveObjects]
variable (η : F ≅ G) {X : C} (P : ProjectiveResolution X)

include P in
theorem mapExactFunctor_natIso (n : ℕ) (x : Ext X X n) :
    selfExtIso (k := k) (η.app X) n (x.mapExactFunctor F) = x.mapExactFunctor G := by
  rw [selfExtIso_apply, Ext.comp_assoc_of_third_deg_zero]
  simp only [Iso.app_hom, Iso.app_inv]
  rw [mapExactFunctor_natural F G η.hom P]
  simp

include P in
theorem exactFunctor_action_natIso (E : X ≅ G.obj X) (n : ℕ) (x : Ext X X n) :
    selfExtIso (k := k) (E ≪≫ (η.app X).symm).symm n (x.mapExactFunctor F) =
      selfExtIso (k := k) E.symm n (x.mapExactFunctor G) := by
  rw [← mapExactFunctor_natIso (k := k) F G η P, selfExtIso_trans]
  rfl

end ArExplicit.ResolutionProducts

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Homology_TriangleGradedSequence
attribute [-instance] _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
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

variable (hT : T ∈ distTriang C)
include hT

theorem exact_next (n : ℤ) :
    LinearMap.range (connecting k T X n) = LinearMap.ker (first k T X (n + 1)) := by
  ext f
  constructor
  · rintro ⟨g, rfl⟩
    change (g ≫ ((T⟦n⟧).mor₃ ≫ (nextIso T n).inv.hom₁)) ≫ (T⟦n + 1⟧).mor₁ = 0
    erw [Category.assoc g, Category.assoc (T⟦n⟧).mor₃, ← (nextIso T n).inv.comm₁]
    erw [next_first, Preadditive.neg_comp, Preadditive.comp_neg, ← Category.assoc (T⟦n⟧).mor₃,
      comp_distTriang_mor_zero₃₁ _ (T.shift_distinguished hT n)]
    erw [Limits.zero_comp, neg_zero, Limits.comp_zero]
  · intro hf
    have hz : (f ≫ (nextIso T n).hom.hom₁) ≫ ((T⟦n⟧)⟦(1 : ℤ)⟧).mor₁ = 0 := by
      erw [Category.assoc, ← (nextIso T n).hom.comm₁, ← Category.assoc]
      change ((first k T X (n + 1)) f) ≫ _ = 0
      rw [show first k T X (n + 1) f = 0 from hf]
      simp
    erw [next_first, Preadditive.comp_neg, neg_eq_zero] at hz
    obtain ⟨g, hg⟩ := (T⟦n⟧).coyoneda_exact₁ (T.shift_distinguished hT n)
      (f ≫ (nextIso T n).hom.hom₁) hz
    refine ⟨g, ?_⟩
    change g ≫ ((T⟦n⟧).mor₃ ≫ (nextIso T n).inv.hom₁) = f
    erw [← Category.assoc, ← hg, Category.assoc]
    have hi : (nextIso T n).hom.hom₁ ≫ (nextIso T n).inv.hom₁ = 𝟙 _ := by
      exact congrArg (fun m => m.hom₁) (nextIso T n).hom_inv_id
    erw [hi, Category.comp_id]

end ArExplicit.TriangleGradedSequence

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Resolutions_CoverFullHomAction
attribute [-instance] _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
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

def coverFullHomEquiv (n : ℕ) (a : ℤ) :
    (((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K) ⟶ (Y n)⟦a⟧) ≃ₗ[k] CohomologyClass K K (a-(n : ℤ)) :=
  (shiftedNegativeHomEquiv (n : ℤ) (basedIteration Y s u n) k ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K) a).trans
    (fullHomShiftedHomotopyEquiv k K K (a-(n : ℤ))).symm

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Resolutions_CoverStepFullHom
attribute [-instance] _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
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
variable {K : CochainComplex C ℤ}
local notation "HC" => HomotopyCategory C (ComplexShape.up ℤ)
local notation "X₀" => sourceObject K

theorem fullHom_coordinates_degree {a b i j : ℤ} (h : a=b)
    {Y : HC} (x : X₀ ⟶ Y⟦i⟧) (y : Y ⟶ X₀⟦j⟧)
    (ha : j+i=a) (hb : j+i=b) :
    (fullHomShiftedHomotopyEquiv k K K b).symm (ShiftedHom.comp x y hb) =
      TateKoszul.degreeEquiv (k := k) (fun d => CohomologyClass K K d) h
        ((fullHomShiftedHomotopyEquiv k K K a).symm (ShiftedHom.comp x y ha)) := by
  subst b
  rfl

theorem coverStepFullHom (Y Z : HC) (n m : ℤ) (hm : m=n+1)
    (e : X₀ ≅ Y⟦n⟧) (s : Y ≅ Z⟦(1 : ℤ)⟧) (t : X₀ ≅ Z⟦m⟧)
    (ht : t.hom = ShiftedHom.comp e.hom s.hom (by omega : 1+n=m))
    (a : ℤ) (v : X₀ ⟶ Y⟦a⟧) :
    (fullHomShiftedHomotopyEquiv k K K (a+1-m)).symm
      (shiftedNegativeHomEquiv m t k X₀ (a+1)
        (ShiftedHom.comp v s.hom (add_comm 1 a))) =
    TateKoszul.degreeEquiv (k := k) (fun d => CohomologyClass K K d)
      (by omega : a-n=a+1-m)
      ((fullHomShiftedHomotopyEquiv k K K (a-n)).symm
        (shiftedNegativeHomEquiv n e k X₀ a v)) := by
  subst m
  simp only [shiftedNegativeHomEquiv_comp]
  have hh := shiftedNegative_step_at Y Z n e s t ht a (a+1-(n+1)) (by omega) v
  rw [hh]
  exact fullHom_coordinates_degree k (by omega) v (negativeShiftIso n e).hom _ _

end ArExplicit

end

end OAI
end

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Tensor_TwistedTensor
attribute [-instance] _root_.OAI.ArExplicit.CompleteComparison.fullHomModule _root_.OAI.ArExplicit.VectorCochain.vectorSpaceInjective _root_.OAI.ArExplicit.VectorComplex.hasMapBifunctor _root_.OAI.ArExplicit.finitePiProjective _root_.OAI.ArExplicit.BalancedTensor.finitePiProjective _root_.OAI.ArExplicit.EnvelopingBimodule.finitePiProjective _root_.OAI.ArExplicit.TriangularInduction.finitePiProjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit

namespace TwistedLeftModule

variable {k R M : Type*} [CommRing k] [Ring R] [Algebra k R]
variable [AddCommGroup M] [Module k M] [Module R M]
variable [IsScalarTower k R M] [SMulCommClass k R M]
variable (σ : R ≃ₐ[k] R)

instance instFinite [Module.Finite k M] : Module.Finite k (TwistedLeftModule k R σ M) :=
  Module.Finite.equiv (scalarEquiv σ).symm

end TwistedLeftModule

end ArExplicit

end OAI
end


