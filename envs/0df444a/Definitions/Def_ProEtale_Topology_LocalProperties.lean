-- Prove2me | Definitions.Def_ProEtale_Topology_LocalProperties
-- name    : ProEtale_Topology_LocalProperties
-- status  : Definition
-- author  : @Idealson
-- created : 2026-11-26T17:01:31.305085+00:00
-- url     : https://prove2.me/theorems/20a48853-cf52-4ab9-aaed-e49389fe7f24
-- title:
--   Criteria for cover-dense functors: local verification, invariance under isomorphism, and behaviour under composition
-- statement:
--   Let $F : \mathcal C \to \mathcal D$ be a functor and $J$ a Grothendieck topology on $\mathcal D$. For $Y \in \mathcal D$, the *cover-by-image* sieve on $Y$ consists of the morphisms $Z \to Y$ that factor through an object of the form $F(W)$. $F$ is *cover-dense* for $J$ if this sieve is $J$-covering for every $Y$.
--
--   Principal results:
--
--   1. For $f : X \to Y$, the cover-by-image sieve on $X$ is contained in the pullback along $f$ of the cover-by-image sieve on $Y$.
--   2. Local criterion: suppose the objects $F(X_i)$ cover the terminal object of the topos of $J$, i.e. they cover every object. Suppose also that for each $i$ the induced functor $\mathcal C/X_i \to \mathcal D/F(X_i)$ is cover-dense for the topology on $\mathcal D/F(X_i)$ induced by $J$. Then $F$ is cover-dense for $J$.
--   3. Cover-density is invariant under natural isomorphism: if $F \cong G$, then $F$ is cover-dense iff $G$ is.
--   4. If $G : \mathcal D \to \mathcal E$ is fully faithful and cover-dense for a topology $J$ on $\mathcal E$, then $G \circ F$ is cover-dense for $J$ iff $F$ is cover-dense for the topology induced on $\mathcal D$ by $G$.
--   5. If $F$ is an equivalence, then $G \circ F$ is cover-dense for $J$ iff $G$ is.
--
--   These lemmas are used to show that the affine pro-étale site is cover-dense in the pro-étale site, by reducing to affine pieces of the base.
--
--   **Formalization Note** Main declarations: `Sieve.le_pullback_coverByImage`, `Functor.IsCoverDense.of_coversTop` (the hypothesis is `J.CoversTop (fun i ↦ F.obj (X i))`, and the local hypothesis is cover-density of `Over.post F` for `J.over (F.obj (X i))`), `Functor.IsCoverDense.of_natIso`, `Functor.IsCoverDense.iff_of_natIso`, `Functor.IsCoverDense.comp_iff_of_isCoverDense`, `Functor.IsCoverDense.comp_iff_of_isEquivalence`. The file also declares section variables (a topology `K` and a concrete category `A`) that none of these statements uses.
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014). Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Topology/LocalProperties.lean (declarations needed by the transplanted proofs, unused ones removed).

/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib
import Mathlib.CategoryTheory.NatIso

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false
/-!
# Local properties of sheafs
-/

namespace CategoryTheory

open Limits Opposite

variable {C : Type*} [Category C] (K : GrothendieckTopology C)
variable {A : Type*} [Category A] {FA : A → A → Type*} {CA : A → Type*}
variable [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory A FA]
variable {J : Type*} [Category J]


lemma _root_.CategoryTheory.Sieve.le_pullback_coverByImage {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D)
    {X Y : D} (f : X ⟶ Y) :
    Sieve.coverByImage F X ≤ Sieve.pullback f (Sieve.coverByImage F Y) := by
  simp only [Sieve.coverByImage]
  intro Z g
  rintro ⟨⟨W, b, c, heq⟩⟩
  refine ⟨⟨?_, ?_, ?_, ?_⟩⟩
  · use W
  · use b
  · use c ≫ f
  · rw [reassoc_of% heq]

lemma _root_.CategoryTheory.Functor.IsCoverDense.of_coversTop {C D : Type*} [Category* C]
    [Category* D] (F : C ⥤ D) (J : GrothendieckTopology D) {ι : Type*} (X : ι → C)
    (hX : J.CoversTop (fun i ↦ F.obj (X i)))
    (H : ∀ i, (Over.post (X := X i) F).IsCoverDense (J.over _)) :
    F.IsCoverDense J := by
  constructor
  intro U
  let S := hX.cover U
  refine J.transitive S.2 _ ?_
  rintro Y f ⟨i, ⟨g⟩⟩
  refine J.superset_covering (CategoryTheory.Sieve.le_pullback_coverByImage _ _) ?_
  have := (H i).is_cover (Over.mk g)
  rw [GrothendieckTopology.mem_over_iff] at this
  dsimp at this
  refine J.superset_covering ?_ this
  intro W a ha
  rw [dsimp% Sieve.overEquiv_iff (Y := Over.mk g) _ a] at ha
  obtain ⟨⟨Z, v, w, huv⟩⟩ := ha
  refine ⟨⟨?_, ?_, ?_, ?_⟩⟩
  · use Z.left
  · use v.left
  · use w.left
  · exact congr($(huv).left)

lemma _root_.CategoryTheory.Functor.IsCoverDense.of_natIso {C D : Type*} [Category* C]
    [Category* D] {F G : C ⥤ D} {J : GrothendieckTopology D} (e : F ≅ G)
    [F.IsCoverDense J] : G.IsCoverDense J := by
  obtain ⟨hF⟩ := ‹F.IsCoverDense J›
  refine ⟨fun U => J.superset_covering ?_ (hF U)⟩
  rintro Y f ⟨⟨Z, ℓ, k, hfg⟩⟩
  refine ⟨⟨Z, ℓ ≫ e.hom.app Z, e.inv.app Z ≫ k, ?_⟩⟩
  simp [hfg]

lemma _root_.CategoryTheory.Functor.IsCoverDense.iff_of_natIso {C D : Type*} [Category* C]
    [Category* D] {F G : C ⥤ D} {J : GrothendieckTopology D} (e : F ≅ G) :
    F.IsCoverDense J ↔ G.IsCoverDense J :=
  ⟨fun _ => .of_natIso e, fun _ => .of_natIso e.symm⟩

lemma _root_.CategoryTheory.Functor.IsCoverDense.comp_iff_of_isCoverDense {C D E : Type*}
    [Category* C] [Category* D] [Category* E] {F : C ⥤ D} {G : D ⥤ E} {J : GrothendieckTopology E}
    [G.IsCoverDense J] [G.Full] [G.Faithful] :
    (F ⋙ G).IsCoverDense J ↔ F.IsCoverDense (G.inducedTopology J) := by
  refine ⟨fun ⟨h⟩ => ⟨fun U => (G.mem_inducedTopology_iff_of_isCoverDense J _).2
      (J.superset_covering ?_ (h (G.obj U)))⟩,
    fun ⟨h⟩ => ⟨fun U => ?_⟩⟩
  · -- forward direction
    rintro Y f ⟨⟨Z, lift, map, rfl⟩⟩
    refine ⟨F.obj Z, G.preimage map, lift, ⟨⟨Z, 𝟙 _, G.preimage map, ?_⟩⟩, by simp⟩
    simp
  · -- reverse direction: F cover-dense in induced ⟹ F⋙G cover-dense in J
    apply J.transitive (G.is_cover_of_isCoverDense J U)
    rintro Y _ ⟨⟨X, lift_b, map_b, rfl⟩⟩
    refine J.superset_covering ?_
      (J.pullback_stable lift_b ((G.mem_inducedTopology_iff_of_isCoverDense J _).1 (h X)))
    rintro V c ⟨T, k, h_c, ⟨⟨W, lift_a, map_a, hfac⟩⟩, hac⟩
    refine ⟨⟨W, h_c ≫ G.map lift_a, G.map map_a ≫ map_b, ?_⟩⟩
    rw [reassoc_of% hac, ← hfac, G.map_comp]
    simp

lemma _root_.CategoryTheory.Functor.IsCoverDense.comp_iff_of_isEquivalence {C D E : Type*}
    [Category* C] [Category* D] [Category* E] {F : C ⥤ D} {G : D ⥤ E}
    {J : GrothendieckTopology E} [F.IsEquivalence] :
    (F ⋙ G).IsCoverDense J ↔ G.IsCoverDense J := by
  refine ⟨fun ⟨h⟩ => ⟨fun U => J.superset_covering ?_ (h U)⟩,
    fun ⟨h⟩ => ⟨fun U => J.superset_covering ?_ (h U)⟩⟩
  · rintro Y f ⟨⟨Z, ℓ, k, hfg⟩⟩
    exact ⟨⟨F.obj Z, ℓ, k, hfg⟩⟩
  · rintro Y f ⟨⟨Z, ℓ, k, hfg⟩⟩
    refine ⟨⟨F.objPreimage Z, ℓ ≫ G.map (F.objObjPreimageIso Z).inv,
      G.map (F.objObjPreimageIso Z).hom ≫ k, ?_⟩⟩
    simp [← G.map_comp_assoc, hfg]

end CategoryTheory


