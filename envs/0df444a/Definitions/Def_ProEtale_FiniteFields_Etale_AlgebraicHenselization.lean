-- Prove2me | Definitions.Def_ProEtale_FiniteFields_Etale_AlgebraicHenselization
-- name    : ProEtale_FiniteFields_Etale_AlgebraicHenselization
-- status  : Definition
-- author  : @Idealson
-- created : 2026-11-26T17:39:11.286767+00:00
-- url     : https://prove2.me/theorems/baea4c8a-a527-4e83-8de5-075d0a19e548
-- title:
--   Index category for the algebraic henselization: étale A-algebras mapping to a target ring form a filtered category
-- statement:
--   For a ring homomorphism $f : A \to C$, Bhatt–Scholze's algebraic henselization of $C$ over $A$ is the filtered colimit of all étale $A$-algebras $E$ equipped with an $A$-algebra map $E \to C$. This file contains only the infrastructure for the index category of that colimit; the henselization itself and its universal property are defined later in the same module.
--
--   Let $\mathcal E_A$ be the category of étale $A$-algebras (commutative rings under $A$ with étale structure map, all morphisms of $A$-algebras). The file establishes, as private declarations:
--
--   1. the property "étale" on morphisms of commutative rings is stable under composition and cobase change, contains identities, respects isomorphisms, and satisfies cancellation (if $E \to F$ and $A \to E$ composed are étale and $A\to E$ is étale, then $E \to F$ is étale);
--   2. $\mathcal E_A$ is essentially small and has finite colimits, and the forgetful functor to rings under $A$ preserves finite colimits;
--   3. the category of pairs $(E, E \to C)$, with $E \in \mathcal E_A$ and $E \to C$ an $A$-algebra map (the comma category over $C$ viewed under $A$ via $f$), is essentially small, has an initial object and pushouts, hence finite colimits, and is therefore filtered;
--   4. a small model of this category, which is again filtered.
--
--   The filtered small index category is what the algebraic henselization is defined as a colimit over; that construction is used to build henselian pairs and w-strictly local rings.
--
--   **Formalization Note** All declarations in this file are `private` (in namespace `FiniteFields.Etale`), so the file exposes no public names: `etaleProperty`, `EtaleAlg`, `etaleForget`, `targetUnder`, `LargeIndex`, `SmallIndex` and their instances. Rings live in universe `u`. The file is ported from a Weil-conjectures formalization. The public interface (`algebraicHenselization`, `algebraicHenselizationHomEquiv`, the counit and its kernel for $A \to A/I$) is described only in a trailing comment and not included here.
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014). Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/FiniteFields/Etale/AlgebraicHenselization.lean (declarations needed by the transplanted proofs, unused ones removed).

/-
Copyright (c) 2026 The Weil Conjectures formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Weil Conjectures formalization contributors
-/
-- Ported from finite_fields (`WeilConjectures.Etale.AlgebraicHenselization`, Lean 4.31) to Lean 4.33.1 / Mathlib 0df444a.
import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.Algebra.Category.CommAlgCat.FiniteType
import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.Algebra.Category.Ring.FinitePresentation
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.Limits.Connected
import Mathlib.CategoryTheory.Limits.MorphismProperty
import Mathlib.CategoryTheory.MorphismProperty.Ind
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Flat.EquationalCriterion
import Mathlib.RingTheory.RingHom.Etale
import Mathlib.RingTheory.Smooth.NoetherianDescent
import Mathlib.RingTheory.Smooth.StandardSmoothOfFree
import Mathlib.RingTheory.TensorProduct.Quotient
import Definitions.Def_ProEtale_FiniteFields_Etale_IndEtale
import Definitions.Def_ProEtale_FiniteFields_Etale_IndEtaleStructural

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false
universe u


/-!
# Algebraic henselization

Bhatt--Scholze's algebraic henselization as the literal filtered colimit of étale
algebras over the base equipped with a map to the target.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace FiniteFields
namespace Etale


private def etaleProperty : MorphismProperty CommRingCat.{u} :=
  RingHom.toMorphismProperty RingHom.Etale

private abbrev EtaleAlg (A : Type u) [CommRing A] :=
  etaleProperty.Under ⊤ (CommRingCat.of A)

private theorem etale_right_of_comp
    {A E F : Type u} [CommRing A] [CommRing E] [CommRing F]
    (f : A →+* E) (g : E →+* F) (hf : f.Etale) (hgf : (g.comp f).Etale) : g.Etale := by
  algebraize [f, g, g.comp f]
  exact Algebra.Etale.of_restrictScalars A E F

private instance inst_FiniteFieldsEtaleAlgebraicHenselization_L51 : etaleProperty.IsStableUnderComposition where
  comp_mem f g hf hg := RingHom.Etale.stableUnderComposition f.hom g.hom hf hg

private instance inst_FiniteFieldsEtaleAlgebraicHenselization_L54 : etaleProperty.IsStableUnderCobaseChange :=
  RingHom.isStableUnderCobaseChange_toMorphismProperty_iff.mpr
    RingHom.Etale.isStableUnderBaseChange

private instance inst_FiniteFieldsEtaleAlgebraicHenselization_L58 : etaleProperty.ContainsIdentities where
  id_mem X := RingHom.Etale.containsIdentities X

private instance inst_FiniteFieldsEtaleAlgebraicHenselization_L61 : etaleProperty.RespectsIso :=
  RingHom.toMorphismProperty_respectsIso_iff.mp RingHom.Etale.respectsIso

private instance inst_FiniteFieldsEtaleAlgebraicHenselization_L64 : etaleProperty.HasOfPrecompProperty etaleProperty where
  of_precomp f g hf hfg := etale_right_of_comp f.hom g.hom hf hfg

private instance etaleAlg_essentiallySmall (A : Type u) [CommRing A] :
    EssentiallySmall.{u} (EtaleAlg A) :=
  essentiallySmall_of_le
    (fun _ _ f hf ↦ RingHom.FiniteType.of_finitePresentation
      ((RingHom.Etale.iff_flat_and_formallyUnramified (f := f.hom)).mp hf).2.2)
    (CommRingCat.of A)

private instance etaleAlg_hasFiniteColimits (A : Type u) [CommRing A] :
    HasFiniteColimits (EtaleAlg A) := by
  infer_instance

private abbrev etaleForget (A : Type u) [CommRing A] :
    EtaleAlg A ⥤ Under (CommRingCat.of A) :=
  MorphismProperty.Under.forget etaleProperty ⊤ (CommRingCat.of A)

private instance etaleForget_preservesFiniteColimits (A : Type u) [CommRing A] :
    PreservesFiniteColimits (etaleForget A) := by
  infer_instance

variable {A C : Type u} [CommRing A] [CommRing C]

private def targetUnder (f : A →+* C) : Under (CommRingCat.of A) :=
  Under.mk (CommRingCat.ofHom f)

private abbrev LargeIndex (f : A →+* C) :=
  CostructuredArrow (etaleForget A) (targetUnder f)

private instance largeIndex_essentiallySmall (f : A →+* C) :
    EssentiallySmall.{u} (LargeIndex f) := by
  infer_instance

private instance largeIndex_hasInitial (f : A →+* C) : HasInitial (LargeIndex f) := by
  infer_instance

private instance largeIndex_hasPushouts (f : A →+* C) : HasPushouts (LargeIndex f) := by
  infer_instance

private instance largeIndex_hasFiniteColimits (f : A →+* C) :
    HasFiniteColimits (LargeIndex f) :=
  hasFiniteColimits_of_hasInitial_and_pushouts

private instance largeIndex_filtered (f : A →+* C) : IsFiltered (LargeIndex f) :=
  IsFiltered.of_hasFiniteColimits _

private abbrev SmallIndex (f : A →+* C) : Type u := SmallModel (LargeIndex f)

private instance smallIndex_filtered (f : A →+* C) : IsFiltered (SmallIndex f) :=
  IsFiltered.of_equivalence (equivSmallModel (LargeIndex f))


variable {D : Type u} [CommRing D]


/-! ## Literal base-change and two-sided consumer shapes -/

variable {B : Type u} [CommRing B]


/-! ## Quotient comparison and full faithfulness -/


end Etale
end FiniteFields


/-! ## Public interface (added for the henselian pair property)

The universal property of the algebraic henselization, stated with ring homomorphisms into the
target so that no algebra structure on the target is fixed: for an ind-étale `A`-algebra `D`, the
`A`-algebra maps `D → algebraicHenselization f` correspond, through the counit, to the ring maps
`D → C` restricting to `f` on `A`. For `f = A → A ⧸ I` the counit is surjective with kernel
`I · algebraicHenselization f`. -/


