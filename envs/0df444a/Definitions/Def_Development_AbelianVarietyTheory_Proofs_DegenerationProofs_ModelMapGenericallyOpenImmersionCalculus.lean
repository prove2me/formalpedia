-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ModelMapGenericallyOpenImmersionCalculus
-- name    : Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ModelMapGenericallyOpenImmersionCalculus
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:42:23.914981+00:00
-- url     : https://prove2.me/theorems/32dc2a33-b3ed-46cc-a124-d53dfd58260a
-- title:
--   Model Map Generically Open Immersion Calculus
-- statement:
--   Definitions and structural lemmas for Model Map Generically Open Immersion Calculus, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ModelMapGenericallyOpenImmersionCalculus.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsLiftOfSchemeTheoreticallyDominant
import Theorems.Thm_GlobalTheory_SS_Model_j_hom

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
noncomputable section
namespace GlobalTheory.SS.GI
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] {K : Type} [Field K] [Algebra R K] {A A' A'' B B' : Over (Sp K)}
theorem isPullback_j (M : Model R A) : IsPullback M.j A.hom M.Y.hom (spMap (algebraMap R K)) := by
  refine IsPullback.of_iso (IsPullback.of_hasPullback M.Y.hom (spMap (algebraMap R K)))
    ((Over.forget _).mapIso M.e) (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ (by simp) (by simp)
  · simp [Model.j, ← Over.comp_left_assoc]
  · simpa using (Over.w M.e.hom).symm
theorem prod_j_fst (M : Model R A) (N : Model R A') :
    (M.prod N).j ≫ (fst M.Y N.Y).left = (fst A A').left ≫ M.j := by
  have h : (M.prod N).e.inv ≫ (Over.pullback (spMap (algebraMap R K))).map (fst M.Y N.Y) = fst A A' ≫ M.e.inv := by
    simp [Model.prod]
  have := congr(($h).left ≫ pullback.fst M.Y.hom (spMap (algebraMap R K)))
  simpa [Model.j, pullback.lift_fst] using this
theorem prod_j_snd (M : Model R A) (N : Model R A') :
    (M.prod N).j ≫ (snd M.Y N.Y).left = (snd A A').left ≫ N.j := by
  have h : (M.prod N).e.inv ≫ (Over.pullback (spMap (algebraMap R K))).map (snd M.Y N.Y) = snd A A' ≫ N.e.inv := by
    simp [Model.prod]
  have := congr(($h).left ≫ pullback.fst N.Y.hom (spMap (algebraMap R K)))
  simpa [Model.j, pullback.lift_fst] using this
theorem prod_hom_ext (M : Model R A) (N : Model R A') {T : Scheme.{0}} {a b : T ⟶ (M.prod N).Y.left}
    (h₁ : a ≫ (fst M.Y N.Y).left = b ≫ (fst M.Y N.Y).left)
    (h₂ : a ≫ (snd M.Y N.Y).left = b ≫ (snd M.Y N.Y).left) : a = b :=
  pullback.hom_ext h₁ h₂
def Via (M : Model R A) (N : Model R A') (f : A ⟶ A') {W : Scheme.{0}} (u : W ⟶ M.Y.left) (g : W ⟶ N.Y.left) : Prop :=
  g ≫ N.Y.hom = u ≫ M.Y.hom ∧
    ∀ (T : Scheme.{0}) (w : T ⟶ W) (a : T ⟶ A.left), w ≫ u = a ≫ M.j → w ≫ g = a ≫ f.left ≫ N.j
theorem Via.precomp {M : Model R A} {N : Model R A'} {f : A ⟶ A'} {W W' : Scheme.{0}} {u : W ⟶ M.Y.left}
    {g : W ⟶ N.Y.left} (h : Via M N f u g) (t : W' ⟶ W) : Via M N f (t ≫ u) (t ≫ g) :=
  ⟨by simp [h.1], fun T w a hw => by
    rw [← Category.assoc] at hw ⊢
    exact h.2 T _ a hw⟩
theorem Via.comp {M : Model R A} {N : Model R A'} {P : Model R A''} {f : A ⟶ A'} {f' : A' ⟶ A''}
    {W : Scheme.{0}} {u : W ⟶ M.Y.left} {g : W ⟶ N.Y.left} {g' : W ⟶ P.Y.left}
    (h : Via M N f u g) (h' : Via N P f' g g') : Via M P (f ≫ f') u g' :=
  ⟨h'.1.trans h.1, fun T w a hw => by
    have := h'.2 T w (a ≫ f.left) (by rw [h.2 T w a hw, Category.assoc])
    simpa using this⟩
theorem Via.inv {M : Model R A} {N : Model R A'} {f : A ≅ A'}
    {W : Scheme.{0}} {u : W ⟶ M.Y.left} {g : W ⟶ N.Y.left} (h : Via M N f.hom u g) : Via N M f.inv g u := by
  refine ⟨h.1.symm, fun T w b hw => ?_⟩
  obtain ⟨a, h1, h2⟩ := (isPullback_j M).exists_lift (w ≫ u) (b ≫ A'.hom) (by
    rw [Category.assoc, ← h.1, ← Category.assoc, hw, Category.assoc, N.j_hom, Category.assoc])
  have h3 : a ≫ f.hom.left = b := by
    refine (isPullback_j N).hom_ext ?_ ?_
    · rw [Category.assoc, ← h.2 T w a h1.symm, hw]
    · rw [Category.assoc, Over.w, h2]
  rw [← h1, ← h3]
  simp [← Over.comp_left_assoc]
theorem via_of_hom {M : Model R A} {N : Model R A'} {f : A ⟶ A'} (g : M.Y ⟶ N.Y)
    (h : M.j ≫ g.left = f.left ≫ N.j) : Via M N f (𝟙 _) g.left :=
  ⟨by simp, fun T w a hw => by
    rw [Category.comp_id] at hw
    rw [hw, Category.assoc, h]⟩
theorem via_fst (M : Model R A) (N : Model R A') {W : Scheme.{0}} (u : W ⟶ (M.prod N).Y.left) :
    Via (M.prod N) M (fst A A') u (u ≫ (fst M.Y N.Y).left) := by
  simpa using (via_of_hom (M := M.prod N) (N := M) (fst M.Y N.Y) (prod_j_fst M N)).precomp u
theorem via_snd (M : Model R A) (N : Model R A') {W : Scheme.{0}} (u : W ⟶ (M.prod N).Y.left) :
    Via (M.prod N) N (snd A A') u (u ≫ (snd M.Y N.Y).left) := by
  simpa using (via_of_hom (M := M.prod N) (N := N) (snd M.Y N.Y) (prod_j_snd M N)).precomp u
theorem via_prod {M : Model R A} {P : Model R B} {Q : Model R B'} {f : A ⟶ B ⊗ B'}
    {W : Scheme.{0}} {u : W ⟶ M.Y.left} {g : W ⟶ (P.prod Q).Y.left}
    (h₁ : Via M P (f ≫ fst B B') u (g ≫ (fst P.Y Q.Y).left))
    (h₂ : Via M Q (f ≫ snd B B') u (g ≫ (snd P.Y Q.Y).left)) : Via M (P.prod Q) f u g := by
  refine ⟨?_, fun T w a hw => prod_hom_ext P Q ?_ ?_⟩
  · rw [← h₁.1, Category.assoc, Over.w]; rfl
  · rw [Category.assoc, h₁.2 T w a hw, Category.assoc, Category.assoc, prod_j_fst]; simp
  · rw [Category.assoc, h₂.2 T w a hw, Category.assoc, Category.assoc, prod_j_snd]; simp
def prodMap (M : Model R A) (N : Model R A') {W W' : Scheme.{0}} (s : W ⟶ Sp R) (s' : W' ⟶ Sp R)
    (u : W ⟶ M.Y.left) (u' : W' ⟶ N.Y.left) (h : u ≫ M.Y.hom = s) (h' : u' ≫ N.Y.hom = s') :
    pullback s s' ⟶ (M.prod N).Y.left :=
  pullback.map s s' M.Y.hom N.Y.hom u u' (𝟙 _) (by simp [h]) (by simp [h'])
section
variable (M : Model R A) (N : Model R A') {W W' : Scheme.{0}} (s : W ⟶ Sp R) (s' : W' ⟶ Sp R)
    (u : W ⟶ M.Y.left) (u' : W' ⟶ N.Y.left) (h : u ≫ M.Y.hom = s) (h' : u' ≫ N.Y.hom = s')
theorem prodMap_fst : prodMap M N s s' u u' h h' ≫ (fst M.Y N.Y).left = pullback.fst s s' ≫ u :=
  pullback.lift_fst _ _ _
theorem prodMap_snd : prodMap M N s s' u u' h h' ≫ (snd M.Y N.Y).left = pullback.snd s s' ≫ u' :=
  pullback.lift_snd _ _ _
instance isOpenImmersion_prodMap [IsOpenImmersion u] [IsOpenImmersion u'] :
    IsOpenImmersion (prodMap M N s s' u u' h h') :=
  MorphismProperty.pullbackMap (P := @IsOpenImmersion) ‹_› ‹_› h.symm h'.symm
end
theorem Via.prod {M : Model R A} {N : Model R A'} {P : Model R B} {Q : Model R B'} {f : A ⟶ B} {f' : A' ⟶ B'}
    {W W' : Scheme.{0}} {u : W ⟶ M.Y.left} {g : W ⟶ P.Y.left} {u' : W' ⟶ N.Y.left} {g' : W' ⟶ Q.Y.left}
    (h : Via M P f u g) (h' : Via N Q f' u' g') :
    Via (M.prod N) (P.prod Q) (f ⊗ₘ f') (prodMap M N _ _ u u' rfl rfl) (prodMap P Q _ _ g g' h.1 h'.1) := by
  refine via_prod ?_ ?_
  · rw [tensorHom_fst, prodMap_fst]
    refine (via_fst M N _).comp ?_
    rw [prodMap_fst]
    exact h.precomp _
  · rw [tensorHom_snd, prodMap_snd]
    refine (via_snd M N _).comp ?_
    rw [prodMap_snd]
    exact h'.precomp _
section
variable [IsLocalRing R]
end
end GlobalTheory.SS.GI
end


