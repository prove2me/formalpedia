-- Prove2me | Definitions.Def_ProEtale_Mathlib_RingTheory_WeaklyEtale_Localization
-- name    : ProEtale_Mathlib_RingTheory_WeaklyEtale_Localization
-- status  : Definition
-- author  : @Idealson
-- created : 2026-11-26T17:01:01.030974+00:00
-- url     : https://prove2.me/theorems/6a87aa7a-4b80-51fc-b02a-8dbe0d9db305
-- title:
--   Localization maps are weakly étale
-- statement:
--   Recall that an $R$-algebra $T$ is weakly étale if both $R \to T$ and the multiplication map $T \otimes_R T \to T$ are flat.
--
--   The file proves: if $T$ is the localization $S^{-1}R$ of a commutative ring $R$ at a submonoid $S$, then $T$ is a weakly étale $R$-algebra. Indeed $T$ is flat over $R$, and the multiplication map $T \otimes_R T \to T$ is an isomorphism, hence flat. In particular the canonical localization $R \to S^{-1}R$ is weakly étale (registered as an instance).
--
--   This is the localization clause of Stacks, Tag 092J (1), and supplies weakly étale maps such as $R \to R_f$ and $R \to R_{\mathfrak p}$ used throughout.
--
--   **Formalization Note** Rings are in arbitrary universes (`Type*`). The declarations are `Algebra.WeaklyEtale.of_isLocalization` (for any `T` with `[IsLocalization S T]`) and the instance `Algebra.WeaklyEtale.localization` for `Localization S`; `Algebra.WeaklyEtale` is Mathlib's class.
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014); cited in the code: Stacks Project, Tag 092J. Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Mathlib/RingTheory/WeaklyEtale/Localization.lean (declarations needed by the transplanted proofs, unused ones removed).

/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Flat.Localization

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false
/-!
# Localization maps are weakly étale

This file records the fact that any localization map `R → S⁻¹R` is weakly étale,
which is item (1) of Stacks
[092J](https://stacks.math.columbia.edu/tag/092J).

## Main results

* `Algebra.WeaklyEtale.of_isLocalization` — if `T` is the localization of `R` at a
  submonoid `S`, then `T` is a weakly étale `R`-algebra.
* `Algebra.WeaklyEtale.localization` — the canonical instance for `Localization S`.
-/

namespace Algebra
namespace WeaklyEtale

/-- **Stacks [092J], localization clause.**

If `T` is the localization of `R` at a submonoid `S`, then `T` is weakly étale over `R`. -/
@[stacks 092J "(1)"]
theorem of_isLocalization (R : Type*) [CommRing R] (S : Submonoid R)
    (T : Type*) [CommRing T] [Algebra R T] [IsLocalization S T] :
    Algebra.WeaklyEtale R T where
  flat := IsLocalization.flat T S
  flat_lmul' :=
    RingHom.Flat.of_bijective
      (f := (Algebra.TensorProduct.lmul' R (S := T)).toRingHom)
      (IsLocalization.bijective_linearMap_mul' (R := R) (A := T) S)

/-- The canonical localization `R → Localization S` is weakly étale. -/
instance localization (R : Type*) [CommRing R] (S : Submonoid R) :
    Algebra.WeaklyEtale R (Localization S) :=
  of_isLocalization R S _

end WeaklyEtale
end Algebra


