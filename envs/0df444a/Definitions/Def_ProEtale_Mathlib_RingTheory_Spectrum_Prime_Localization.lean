-- Prove2me | Definitions.Def_ProEtale_Mathlib_RingTheory_Spectrum_Prime_Localization
-- name    : ProEtale_Mathlib_RingTheory_Spectrum_Prime_Localization
-- status  : Definition
-- author  : @Idealson
-- created : 2026-11-26T17:00:32.441796+00:00
-- url     : https://prove2.me/theorems/24bc3a13-4811-5015-93d5-dbe3142001f0
-- title:
--   An element of a commutative ring is determined by its images in all localizations at prime ideals
-- statement:
--   **Theorem.** Let $R$ be a commutative ring and $x, y \in R$. If for every prime ideal $\mathfrak p \subset R$ the images of $x$ and $y$ in the localization $R_{\mathfrak p}$ agree,
--   $$\frac{x}{1} = \frac{y}{1} \quad \text{in } R_{\mathfrak p} \text{ for all } \mathfrak p \in \operatorname{Spec} R,$$
--   then $x = y$.
--
--   This is the injectivity of $R \to \prod_{\mathfrak p} R_{\mathfrak p}$, stated in a form convenient for checking equalities locally.
--
--   **Formalization Note** The theorem is `PrimeSpectrum.eq_of_localizationAtPrime_eq`. Primes are indexed by `PrimeSpectrum R`, and the localization is `Localization.AtPrime p.asIdeal`. It is a direct consequence of `PrimeSpectrum.toPiLocalization_injective`.
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014). Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Mathlib/RingTheory/Spectrum/Prime/Localization.lean (declarations needed by the transplanted proofs, unused ones removed).

import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false
/-!
# Testing equality of ring elements on localizations at primes

An element of a commutative ring is determined by its images in all localizations at
prime ideals. This is a direct consequence of
`PrimeSpectrum.toPiLocalization_injective`.
-/

namespace PrimeSpectrum

/-- Two elements of a commutative ring agreeing in every localization at a prime are
equal. -/
theorem eq_of_localizationAtPrime_eq {R : Type*} [CommRing R] {x y : R}
    (h : ∀ p : PrimeSpectrum R,
      algebraMap R (Localization.AtPrime p.asIdeal) x =
        algebraMap R (Localization.AtPrime p.asIdeal) y) : x = y :=
  PrimeSpectrum.toPiLocalization_injective R <| funext fun p ↦ h p

end PrimeSpectrum


