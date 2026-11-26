-- Prove2me | Definitions.Def_ProEtale_Mathlib_RingTheory_RingHom_Etale
-- name    : ProEtale_Mathlib_RingTheory_RingHom_Etale
-- status  : Definition
-- author  : @Idealson
-- created : 2026-11-26T17:00:25.648641+00:00
-- url     : https://prove2.me/theorems/38b18282-3731-5ec9-8de1-20e08c2d9baf
-- title:
--   Étale ring homomorphisms cancel on the left: if $f$ and $g \circ f$ are étale, so is $g$
-- statement:
--   Let $R, S, T$ be commutative rings and $f : R \to S$, $g : S \to T$ ring homomorphisms. If $f$ is étale and the composite $g \circ f : R \to T$ is étale, then $g$ is étale:
--   $$f \text{ étale},\ g \circ f \text{ étale} \;\Longrightarrow\; g \text{ étale}.$$
--
--   $g$ is of finite presentation because $g \circ f$ is of finite presentation and $f$ is of finite type, and formal étaleness descends along the scalar tower. This lets one compare étale algebras over a fixed base, e.g. to show that morphisms in the category of étale $R$-algebras are themselves étale.
--
--   **Formalization Note** The lemma is `RingHom.Etale.of_comp`, stated for `RingHom.Etale`, the ring-homomorphism form of `Algebra.Etale`: formally étale and of finite presentation.
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014). Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Mathlib/RingTheory/RingHom/Etale.lean (declarations needed by the transplanted proofs, unused ones removed).

/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.RingTheory.RingHom.Etale

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false
/-!
# Étale ring homomorphisms cancel from the left

We show `RingHom.Etale.of_comp`: if `f : R →+* S` and `g ∘ f : R →+* T` are étale, then so
is `g : S →+* T`.
-/

namespace RingHom

/-- Étale ring maps cancel from the left: if `f : R →+* S` and `g ∘ f : R →+* T` are
étale, then so is `g : S →+* T`. -/
lemma Etale.of_comp {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    {f : R →+* S} {g : S →+* T} (hf : f.Etale) (hgf : (g.comp f).Etale) :
    g.Etale := by
  have hfp : g.FinitePresentation :=
    FinitePresentation.of_comp_finiteType f
      (Etale.iff_flat_and_formallyUnramified.mp hgf).2.2
      (FiniteType.of_finitePresentation (Etale.iff_flat_and_formallyUnramified.mp hf).2.2)
  algebraize [f, g, g.comp f]
  exact ⟨Algebra.FormallyEtale.of_restrictScalars (R := R), hfp⟩

end RingHom


