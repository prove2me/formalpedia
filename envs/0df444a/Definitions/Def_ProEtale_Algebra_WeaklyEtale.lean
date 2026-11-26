-- Prove2me | Definitions.Def_ProEtale_Algebra_WeaklyEtale
-- name    : ProEtale_Algebra_WeaklyEtale
-- status  : Definition
-- author  : @Idealson
-- created : 2026-11-26T11:14:41.563129+00:00
-- url     : https://prove2.me/theorems/f06b7280-5404-502c-bf52-5a463084a382
-- title:
--   Weakly étale ring homomorphisms
-- statement:
--   The property `RingHom.WeaklyEtale` of ring homomorphisms corresponding to Mathlib's weakly étale algebras ($S$ flat over $R$ and over $S \otimes_R S$), with a criterion for flatness of the multiplication map $S \otimes_R S \to S$ in terms of purity of its kernel.
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014), Definition 2.3.1. Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Algebra/WeaklyEtale.lean (declarations kept unchanged, unused ones removed).

/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib
import Definitions.Def_ProEtale_Mathlib_RingTheory_Ideal_Pure

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false
/-!
# Weakly étale algebras

-/

universe u u₁ u₂ u₃ u₄ u₅

open TensorProduct


open CategoryTheory Limits

-- `(S ⊗[R] S) (T ⊗[R] A) S (T ⊗[S] A)`


namespace Algebra


variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- The multiplication map `S ⊗[R] S → S` is flat iff the kernel of the multiplication map
(i.e. `KaehlerDifferential.ideal R S`) is a pure ideal in `S ⊗[R] S`. -/
lemma flat_lmul'_iff_kaehlerDifferential_ideal_pure :
    (TensorProduct.lmul' (S := S) R).toRingHom.Flat ↔ (KaehlerDifferential.ideal R S).Pure :=
  RingHom.flat_iff_pure_ker_of_surjective (fun x ↦ ⟨1 ⊗ₜ x, by simp⟩)


end Algebra

namespace RingHom

@[algebraize]
def WeaklyEtale {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) : Prop :=
  letI := f.toAlgebra
  Algebra.WeaklyEtale R S

variable {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)

lemma weaklyEtale_algebraMap_iff [Algebra R S] :
    (algebraMap R S).WeaklyEtale ↔ Algebra.WeaklyEtale R S := by
  rw [WeaklyEtale, toAlgebra_algebraMap]


end RingHom


