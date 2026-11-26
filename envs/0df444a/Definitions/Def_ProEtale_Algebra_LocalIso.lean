-- Prove2me | Definitions.Def_ProEtale_Algebra_LocalIso
-- name    : ProEtale_Algebra_LocalIso
-- status  : Definition
-- author  : @Idealson
-- created : 2026-11-26T16:56:11.643824+00:00
-- url     : https://prove2.me/theorems/3d7427d0-6fe7-5aef-bb28-cec80f4dcc97
-- title:
--   Local isomorphisms of rings: flatness, bijective maps, composition, base change
-- statement:
--   An $R$-algebra $S$ is a **local isomorphism** if, locally on $\operatorname{Spec} S$, it is a standard open immersion: $S$ is covered by principal opens $D(g)$, $g \in S$, such that each $S_g$ is a standard open immersion over $R$, i.e. isomorphic to a localization $R_r$ for some $r \in R$. This is Mathlib's notion. The file defines the corresponding property of ring homomorphisms: $f\colon R \to S$ is a local isomorphism if $S$, viewed as an $R$-algebra via $f$, is one (Stacks 096E (1)).
--
--   Principal results:
--
--   1. $R$ is a local isomorphism over itself, a standard open immersion is flat, and every local isomorphism is flat.
--   2. A bijective ring homomorphism is a local isomorphism.
--   3. If $f\colon R \to S$ and $g\colon S \to T$ are local isomorphisms, so is $g \circ f$. Hence local isomorphisms are stable under composition and respect isomorphisms.
--   4. Local isomorphisms are stable under base change. The associated class of morphisms in the category of commutative rings is stable under cobase change and under composition.
--
--   Local isomorphisms are the building blocks of ind-Zariski algebras, which are filtered colimits of local isomorphisms.
--
--   **Formalization Note** The underlying algebra notion is Mathlib's `Algebra.IsLocalIso` (with `Algebra.IsStandardOpenImmersion`); its description above comes from my knowledge of Mathlib. The new definition is `RingHom.IsLocalIso`, stated for commutative semirings. The results are `Algebra.IsLocalIso.refl`, `Module.Flat.of_isStandardOpenImmersion`, `Algebra.IsLocalIso.flat` (for commutative rings, possibly in different universes `v`, `w`), `RingHom.isLocalIso_algebraMap`, `RingHom.IsLocalIso.of_bijective`, `comp`, `stableUnderComposition`, `respectsIso`, `isStableUnderBaseChange`, and the instances `MorphismProperty.isLocalIso_isStableUnderCobaseChange` and `isLocalIso_isStableUnderComposition`.
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014); cited in the code: Stacks Project, Tag 096E (1). Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Algebra/LocalIso.lean (declarations needed by the transplanted proofs, unused ones removed).

/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.LocalIso
import Mathlib.RingTheory.RingHom.OpenImmersion
import Mathlib.RingTheory.RingHomProperties
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Tactic.Algebraize
import Mathlib.Tactic.DepRewrite

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false
/-!
# Local isomorphisms

A ring homomorphism is a local isomorphism if source locally (in the geometric sense)
it is a standard open immersion.
-/

variable (R S : Type*) [CommSemiring R] [CommSemiring S] [Algebra R S]

namespace Algebra
namespace IsLocalIso

instance refl : IsLocalIso R R := inferInstance

end IsLocalIso
end Algebra

section Flat

universe v w

/-- A standard open immersion is flat, since it is a localization. -/
lemma Module.Flat.of_isStandardOpenImmersion
    (R : Type v) (S : Type w) [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.IsStandardOpenImmersion R S] : Module.Flat R S := by
  obtain ⟨r, _⟩ := Algebra.IsStandardOpenImmersion.exists_away R S
  exact IsLocalization.flat S (Submonoid.powers r)

/-- A local isomorphism is flat, since it is locally a localization. -/
lemma Algebra.IsLocalIso.flat
    (R : Type v) (S : Type w) [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.IsLocalIso R S] : Module.Flat R S := by
  refine Module.flat_of_isLocalized_span S S
    {g | Algebra.IsStandardOpenImmersion R (Localization.Away g)}
    (Algebra.IsLocalIso.span_isStandardOpenImmersion_eq_top _ _)
    (fun g ↦ Localization.Away g.1)
    (fun g ↦ Algebra.linearMap S (Localization.Away g.1)) fun ⟨g, hg⟩ ↦ by
      letI : Algebra.IsStandardOpenImmersion R (Localization.Away g) := hg
      exact Module.Flat.of_isStandardOpenImmersion R (Localization.Away g)

end Flat

/-- A ring homomorphism is a local isomorphism if source locally (in the geometric sense),
it is a standard open immersion. -/
@[stacks 096E "(1)", algebraize]
def RingHom.IsLocalIso {R S : Type*} [CommSemiring R] [CommSemiring S] (f : R →+* S) : Prop :=
  letI := f.toAlgebra
  Algebra.IsLocalIso R S

variable {R S : Type*} [CommSemiring R] [CommSemiring S] {f : R →+* S}

lemma RingHom.isLocalIso_algebraMap [Algebra R S] :
    (algebraMap R S).IsLocalIso ↔ Algebra.IsLocalIso R S := by
  rw [RingHom.IsLocalIso, toAlgebra_algebraMap]

namespace RingHom
namespace IsLocalIso

/-- A bijective ring homomorphism is a local isomorphism. -/
lemma of_bijective (hf : Function.Bijective f) : f.IsLocalIso := by
  algebraize [f]
  haveI := Algebra.IsStandardOpenImmersion.of_bijective hf
  change Algebra.IsLocalIso R S
  infer_instance

/-- The composition of local isomorphisms is a local isomorphism. -/
lemma comp {T : Type*} [CommSemiring T] {g : S →+* T} (hg : g.IsLocalIso) (hf : f.IsLocalIso) :
    (g.comp f).IsLocalIso := by
  algebraize [f, g, g.comp f]
  exact Algebra.IsLocalIso.trans R S T

lemma stableUnderComposition : StableUnderComposition IsLocalIso :=
  fun _ _ _ _ _ _ _ _ hf hg ↦ hg.comp hf

lemma respectsIso : RespectsIso IsLocalIso :=
  stableUnderComposition.respectsIso fun e ↦ .of_bijective e.bijective

end IsLocalIso
end RingHom

/-- `RingHom.IsLocalIso` is stable under base change. -/
lemma RingHom.IsLocalIso.isStableUnderBaseChange :
    RingHom.IsStableUnderBaseChange RingHom.IsLocalIso := by
  refine RingHom.IsStableUnderBaseChange.mk RingHom.IsLocalIso.respectsIso ?_
  intro R S T _ _ _ _ _ hRT
  rw [RingHom.isLocalIso_algebraMap] at hRT ⊢
  infer_instance

namespace CategoryTheory
namespace MorphismProperty

/-- The `MorphismProperty` on `CommRingCat` associated to `RingHom.IsLocalIso` is stable
under cobase change. -/
instance isLocalIso_isStableUnderCobaseChange :
    (RingHom.toMorphismProperty RingHom.IsLocalIso).IsStableUnderCobaseChange := by
  rw [RingHom.isStableUnderCobaseChange_toMorphismProperty_iff]
  exact RingHom.IsLocalIso.isStableUnderBaseChange

/-- The `MorphismProperty` on `CommRingCat` associated to `RingHom.IsLocalIso` is stable
under composition. -/
instance isLocalIso_isStableUnderComposition :
    (RingHom.toMorphismProperty RingHom.IsLocalIso).IsStableUnderComposition where
  comp_mem _ _ hf hg := hg.comp hf

end MorphismProperty
end CategoryTheory


