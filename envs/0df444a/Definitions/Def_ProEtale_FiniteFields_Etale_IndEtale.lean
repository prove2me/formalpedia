-- Prove2me | Definitions.Def_ProEtale_FiniteFields_Etale_IndEtale
-- name    : ProEtale_FiniteFields_Etale_IndEtale
-- status  : Definition
-- author  : @Idealson
-- created : 2026-11-26T16:56:31.884027+00:00
-- url     : https://prove2.me/theorems/caae3cc4-61af-5b82-af08-3ab25568c2cf
-- title:
--   Explicit filtered-colimit presentations of ring maps by étale algebras
-- statement:
--   Let $f : A \to B$ be a homomorphism of commutative rings, and regard $B$ as an $A$-algebra via $f$. An *ind-étale presentation* of $f$ consists of:
--
--   - a small filtered category $I$;
--   - a diagram $D : I \to \mathrm{CAlg}_A$ of commutative $A$-algebras such that every $D_i$ is étale over $A$;
--   - a colimit cocone over $D$;
--   - an isomorphism of $A$-algebras between the colimit and $B$.
--
--   Thus $B \cong \operatorname{colim}_{i \in I} D_i$ as $A$-algebras, with étale stages. The isomorphism is one of $A$-algebras, so it identifies the colimit with $B$ together with the map $f$, not just as a ring.
--
--   The file also proves, as private auxiliary facts about the class of étale ring maps in the category of commutative rings:
--
--   1. étale ring maps are stable under cobase change;
--   2. étale ring maps pre-ind-spread: if $C = \operatorname{colim}_j D_j$ is a filtered colimit of commutative rings and $C \to T$ is étale, then there are an index $j$ and an étale map $D_j \to T'$ such that $C \to T$ is its base change along $D_j \to C$. The proof descends the étale algebra to a finitely generated $\mathbb Z$-subalgebra;
--   3. étale ring maps are stable under composition.
--
--   This structure gives a concrete, data-carrying form of ind-étaleness, used in the finite-field part of the project.
--
--   **Formalization Note** All rings and the index category live in a single universe `u`. Main declaration: the structure `FiniteFields.Etale.IndEtalePresentation f`, with fields `Index`, `diagram`, `etale`, `cocone`, `isColimit` and `targetIso`. The target isomorphism is `cocone.pt ≅ CommAlgCat.of A B` with the algebra structure `f.toAlgebra`. Items 1–3 are `private` declarations (`etaleMorphismProperty` and its instances, `etalePreIndSpreads`), so they cannot be used outside this file.
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014). Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/FiniteFields/Etale/IndEtale.lean (declarations needed by the transplanted proofs, unused ones removed).

/-
Copyright (c) 2026 The Weil Conjectures formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Weil Conjectures formalization contributors
-/
-- Ported from finite_fields (`WeilConjectures.Etale.IndEtale`, Lean 4.31) to Lean 4.33.1 / Mathlib 0df444a.
import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.Algebra.Category.Ring.FinitePresentation
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.Limits.Connected
import Mathlib.CategoryTheory.MorphismProperty.Ind
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.RingHom.Etale
import Mathlib.RingTheory.Smooth.NoetherianDescent

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false
universe u


/-!
# Ind-etale algebra maps

This module records the literal filtered-colimit meaning of an ind-etale map.  The presentation is
kept explicit: its stages are commutative algebras over the source, every stage is etale, and the
specified target algebra is isomorphic to the colimit in `CommAlgCat`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace FiniteFields
namespace Etale


variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]

/-- A literal filtered presentation of a ring map as a colimit of etale algebras.

The algebra structure on the target is the one induced by `f`; consequently `targetIso` identifies
the colimit as an `A`-algebra with the actual map `f`, rather than merely identifying its underlying
commutative ring. -/
structure IndEtalePresentation (f : A →+* B) where
  /-- The filtered indexing category. -/
  Index : Type u
  [categoryIndex : SmallCategory Index]
  [filteredIndex : IsFiltered Index]
  /-- The diagram of etale source algebras. -/
  diagram : Index ⥤ CommAlgCat.{u} A
  /-- Every algebra in the diagram is etale over the source. -/
  etale : ∀ j, Algebra.Etale A (diagram.obj j)
  /-- A chosen colimit cocone. -/
  cocone : Cocone diagram
  /-- The cocone is colimiting. -/
  isColimit : IsColimit cocone
  /-- The colimit is the target with algebra structure induced by `f`. -/
  targetIso : letI := f.toAlgebra; cocone.pt ≅ CommAlgCat.of A B

attribute [instance] IndEtalePresentation.categoryIndex IndEtalePresentation.filteredIndex

namespace IndEtalePresentation

private def etaleMorphismProperty : MorphismProperty CommRingCat.{u} :=
  RingHom.toMorphismProperty RingHom.Etale


private instance inst_FiniteFieldsEtaleIndEtale_L99 : etaleMorphismProperty.IsStableUnderCobaseChange :=
  (RingHom.isStableUnderCobaseChange_toMorphismProperty_iff (P := RingHom.Etale)).mpr
    RingHom.Etale.isStableUnderBaseChange

private theorem etalePreIndSpreads :
    MorphismProperty.PreIndSpreads.{u} etaleMorphismProperty.{u} := by
  constructor
  intro J _ _ D c hc T f hf
  letI : Algebra c.pt T := f.hom.toAlgebra
  letI : Algebra.Etale c.pt T := hf
  let R₀ : CommRingCat.{u} := CommRingCat.of (ULift.{u} ℤ)
  letI : Algebra R₀ c.pt := (CommRingCat.isInitial.to c.pt).hom.toAlgebra
  letI : IsNoetherianRing R₀ := by
    dsimp [R₀]
    exact isNoetherianRing_of_ringEquiv ℤ
      (ULift.ringEquiv.{0, u} (R := ℤ)).symm
  obtain ⟨A₀, T₀, _, _, hA₀, hT₀, ⟨e⟩⟩ :=
    Algebra.Etale.exists_subalgebra_fg R₀ c.pt T
  let zA₀ : R₀ ⟶ CommRingCat.of A₀ := CommRingCat.isInitial.to _
  let α : (Functor.const J).obj R₀ ⟶ D :=
    { app := fun j ↦ CommRingCat.isInitial.to _
      naturality := by
        intro i j q
        exact CommRingCat.isInitial.hom_ext _ _ }
  have hfpAlg : Algebra.FinitePresentation R₀ A₀ :=
    Algebra.FinitePresentation.of_finiteType.mp
      ((Subalgebra.fg_iff_finiteType A₀).mp hA₀)
  have hfp : zA₀.hom.FinitePresentation :=
    RingHom.finitePresentation_algebraMap.mpr hfpAlg
  obtain ⟨j, k, hk₀, hk⟩ :=
    RingHom.EssFiniteType.exists_eq_comp_ι_app_of_isColimit
      (R := R₀) (F := D) (α := α) (f := zA₀) (c := c) hc hfp
      (CommRingCat.ofHom A₀.val.toRingHom) (by
        intro i
        exact CommRingCat.isInitial.hom_ext _ _)
  letI : Algebra A₀ (D.obj j) := k.hom.toAlgebra
  let djToTarget : D.obj j →ₐ[A₀] c.pt :=
    { (c.ι.app j).hom with
      commutes' := fun x ↦ by
        exact congrArg (fun q : CommRingCat.of A₀ ⟶ c.pt ↦ q x) hk.symm }
  let T' := (D.obj j) ⊗[A₀] T₀
  let gAlg : T' →ₐ[A₀] T :=
    (e.symm.restrictScalars A₀).toAlgHom.comp
      (Algebra.TensorProduct.map djToTarget (AlgHom.id A₀ T₀))
  letI : Algebra (D.obj j) c.pt := (c.ι.app j).hom.toAlgebra
  letI : Algebra (D.obj j) T := (f.hom.comp (c.ι.app j).hom).toAlgebra
  let t₀ToT : T₀ →ₐ[A₀] T :=
    { toRingHom := e.symm.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom
      commutes' := fun x ↦ by
        change e.symm (1 ⊗ₜ[A₀] algebraMap A₀ T₀ x) = f.hom (A₀.val x)
        rw [← Algebra.TensorProduct.algebraMap_apply']
        exact e.symm.commutes (A₀.val x) }
  letI : Algebra T₀ T := t₀ToT.toRingHom.toAlgebra
  letI : Algebra T₀ T' := Algebra.TensorProduct.rightAlgebra
  letI : Algebra T' T := gAlg.toRingHom.toAlgebra
  haveI : IsScalarTower A₀ (D.obj j) c.pt :=
    IsScalarTower.of_algebraMap_eq fun x ↦ by
      exact congrArg (fun q : CommRingCat.of A₀ ⟶ c.pt ↦ q x) hk
  haveI : IsScalarTower (D.obj j) c.pt T :=
    IsScalarTower.of_algebraMap_eq fun x ↦ rfl
  haveI : IsScalarTower A₀ T₀ T :=
    IsScalarTower.of_algebraMap_eq fun x ↦ by
      exact (t₀ToT.commutes x).symm
  have hBig : Algebra.IsPushout A₀ c.pt T₀ T := by
    constructor
    exact IsBaseChange.of_equiv e.symm.toLinearEquiv (fun _ ↦ rfl)
  haveI : IsScalarTower A₀ (D.obj j) T' := inferInstance
  haveI : IsScalarTower A₀ T₀ T' := inferInstance
  haveI : IsScalarTower (D.obj j) T' T :=
    IsScalarTower.of_algebraMap_eq fun x ↦ by
      change f.hom ((c.ι.app j).hom x) =
        e.symm (Algebra.TensorProduct.map djToTarget (AlgHom.id A₀ T₀) (x ⊗ₜ[A₀] 1))
      rw [Algebra.TensorProduct.map_tmul]
      exact (e.symm.commutes ((c.ι.app j).hom x)).symm
  haveI : IsScalarTower T₀ T' T :=
    IsScalarTower.of_algebraMap_eq fun x ↦ by
      change e.symm (1 ⊗ₜ[A₀] x) =
        e.symm (Algebra.TensorProduct.map djToTarget (AlgHom.id A₀ T₀) (1 ⊗ₜ[A₀] x))
      rw [Algebra.TensorProduct.map_tmul]
      simp
  haveI : IsScalarTower A₀ T' T :=
    IsScalarTower.of_algebraMap_eq fun x ↦ (gAlg.commutes x).symm
  haveI : Algebra.IsPushout A₀ (D.obj j) T₀ T' := inferInstance
  have hRight : Algebra.IsPushout (D.obj j) c.pt T' T :=
    (Algebra.IsPushout.comp_iff (T := c.pt) A₀ (D.obj j) T₀
      (S' := T') (T' := T)).mp hBig
  letI : Algebra.IsPushout (D.obj j) c.pt T' T := hRight
  refine ⟨j, CommRingCat.of T',
    CommRingCat.ofHom (algebraMap (D.obj j) T'), CommRingCat.ofHom gAlg.toRingHom, ?_, ?_⟩
  · change IsPushout (CommRingCat.ofHom (algebraMap (D.obj j) c.pt))
      (CommRingCat.ofHom (algebraMap (D.obj j) T')) f (CommRingCat.ofHom gAlg.toRingHom)
    exact CommRingCat.isPushout_of_isPushout (D.obj j) c.pt T' T
  · change RingHom.Etale (algebraMap (D.obj j) T')
    exact (RingHom.etale_algebraMap (R := D.obj j) (S := T')).mpr
      (Algebra.Etale.baseChange A₀ T₀ (D.obj j))

private instance inst_FiniteFieldsEtaleIndEtale_L195 : MorphismProperty.PreIndSpreads.{u} etaleMorphismProperty.{u} :=
  etalePreIndSpreads

private instance inst_FiniteFieldsEtaleIndEtale_L198 : etaleMorphismProperty.IsStableUnderComposition where
  comp_mem f g hf hg := RingHom.Etale.stableUnderComposition f.hom g.hom hf hg


end IndEtalePresentation

end Etale
end FiniteFields


