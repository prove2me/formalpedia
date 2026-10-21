-- Prove2me | Definitions.Def_InconsistentDR_Shadow_Optimization
-- name    : InconsistentDR_Shadow_Optimization
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T04:58:31.911422+00:00
-- url     : https://prove2.me/theorems/8b781080-29f2-40de-8942-7c470fd5bdcb
-- title:
--   (6), p. 3, and §6 — effective domain dom f and domain of the conjugate dom f*
-- statement:
--   For a function $f : X \to\, ]-\infty, +\infty]$ on a real inner product space $X$:
--
--   1. the **effective domain** is $\operatorname{dom} f = \{x \in X \mid f(x) < +\infty\}$;
--   2. the **domain of the conjugate** is $\operatorname{dom} f^* = \{u \in X \mid f^*(u) < +\infty\}$, where $f^*(u) = \sup_{x\in X}(\langle x, u\rangle - f(x))$ is the Fenchel conjugate.
--
--   These sets enter Lemma 6.3 ($y \in \operatorname{dom}f \cap (v + \operatorname{dom}g)$) and the main Theorem 6.9 (the hypothesis $0 \in \operatorname{dom}f^* + \operatorname{dom}g^*$).
--
--   **Formalization Note** Functions take values in `EReal`; the conjugate is the published `MoreauProx.Characterization.conj`, computed as an `EReal` supremum.
-- source:
--   Bauschke & Moursi, On the Douglas–Rachford algorithm for solving possibly inconsistent optimization problems, arXiv:2106.11547v1 (22 Jun 2021), p. 3 (6), p. 22, p. 28 (Theorem 6.9)

import Mathlib
import Definitions.Def_MoreauProx_Characterization_GammaZero

namespace InconsistentDR.Shadow

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]

/-- The effective domain `dom f := {x | f x < +∞}` of `f : X → ]−∞, +∞]`. -/
def edom (f : X → EReal) : Set X := {x | f x ≠ ⊤}

/-- The effective domain of the conjugate, `dom f* := {u | f*(u) < +∞}`. -/
def domConj (f : X → EReal) : Set X := {u | MoreauProx.Characterization.conj f u ≠ ⊤}

end InconsistentDR.Shadow


