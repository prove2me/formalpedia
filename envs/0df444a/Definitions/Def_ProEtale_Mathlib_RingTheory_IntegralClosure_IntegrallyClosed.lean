-- Prove2me | Definitions.Def_ProEtale_Mathlib_RingTheory_IntegralClosure_IntegrallyClosed
-- name    : ProEtale_Mathlib_RingTheory_IntegralClosure_IntegrallyClosed
-- status  : Definition
-- author  : @Idealson
-- created : 2026-11-26T17:00:18.21811+00:00
-- url     : https://prove2.me/theorems/381c4dbd-3f46-52a6-9bce-a013c5b02bed
-- title:
--   The image of a ring integrally closed in $L$ is an integrally closed subring of $L$
-- statement:
--   Let $A$ and $L$ be commutative rings and $A \to L$ an injective ring map. Assume $A$ is integrally closed in $L$: every element of $L$ that is integral over $A$ lies in the image of $A$. Then the subring $\operatorname{im}(A \to L) \subseteq L$ is integrally closed in $L$.
--
--   This lets one replace an abstract ring integrally closed in $L$ by an honest subring of $L$, for instance when working with domains integrally closed in a field extension.
--
--   **Formalization Note** The theorem is `IsIntegrallyClosedIn.algebraMap_range`, with hypotheses `[FaithfulSMul A L]` (injectivity of `algebraMap A L`) and `[IsIntegrallyClosedIn A L]`. The conclusion is `IsIntegrallyClosedIn (algebraMap A L).range L`.
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014). Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Mathlib/RingTheory/IntegralClosure/IntegrallyClosed.lean (declarations needed by the transplanted proofs, unused ones removed).

/-
Copyright (c) 2026 Christian Merten, Jingting Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten, Jingting Wang
-/
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false
/-!
# The image of an integrally closed subring

If `A` is integrally closed in `L` and `A → L` is injective, then the image of `A` in `L`
is integrally closed in `L`.

## Main results

- `IsIntegrallyClosedIn.algebraMap_range`: the range of `algebraMap A L` is integrally closed
  in `L`, when `A` is integrally closed in `L` and `A → L` is injective.
-/

/-- If `A` is integrally closed in `L` and `algebraMap A L` is injective, then the range of
`algebraMap A L` is integrally closed in `L`. -/
theorem IsIntegrallyClosedIn.algebraMap_range {A L : Type*} [CommRing A] [CommRing L]
    [Algebra A L] [FaithfulSMul A L] [IsIntegrallyClosedIn A L] :
    IsIntegrallyClosedIn (algebraMap A L).range L := by
  rw [Subring.isIntegrallyClosedIn_iff]
  intro x hx
  obtain ⟨p, hp, hpe⟩ := hx
  let e : A ≃+* (algebraMap A L).range :=
    RingEquiv.ofBijective (algebraMap A L).rangeRestrict
      ⟨fun a b h ↦ FaithfulSMul.algebraMap_injective A L (congrArg Subtype.val h),
        (algebraMap A L).rangeRestrict_surjective⟩
  have ha : IsIntegral A x := by
    refine ⟨p.map e.symm.toRingHom, hp.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    have hcomp : (algebraMap A L).comp e.symm.toRingHom =
        algebraMap (algebraMap A L).range L := by
      ext y
      exact congrArg Subtype.val (e.apply_symm_apply y)
    rw [hcomp]
    exact hpe
  exact IsIntegrallyClosedIn.isIntegral_iff.mp ha


