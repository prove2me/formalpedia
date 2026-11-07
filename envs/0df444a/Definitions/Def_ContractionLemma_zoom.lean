-- Prove2me | Definitions.Def_ContractionLemma_zoom
-- name    : ContractionLemma_zoom
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T20:57:20.782999+00:00
-- url     : https://prove2.me/theorems/91c374ed-d79f-46ad-a926-f9b0c4ec1748
-- title:
--   Zooming in: $z\mapsto F(t+\alpha z)$, $\alpha=2L$, and $\pi(z)$
-- statement:
--   Put $\alpha=2L=2^{a+1}$. For a polynomial $F$ over $\mathbb Q$ and a grid point $t$, zooming in at $t$ gives the polynomial $z\mapsto F(t+\alpha z)$, whose coefficients are the Taylor coefficients of $F$ at $t$ up to known powers of $\alpha$. The module also defines
--
--   $$
--   \pi(z)=\prod_{s\in S\setminus\{t\}}\Big(1+\frac{\alpha z}{t-s}\Big).
--   $$
-- source:
--   Gajulapalli, The Contraction Lemma Beyond ETH (manuscript, sha256 049caea1…), App. A.5.2, pp.63–64

import Mathlib
import Definitions.Def_ContractionLemma_kernel

set_option autoImplicit false

namespace ContractionLemma

open Polynomial

/-- `α = 2L = 2^{a+1}` (App. A.5.2, p.63). -/
noncomputable def alpha (a : ℕ) : ℚ := 2 ^ (a + 1)

/-- **Zooming in at `t`** (App. A.5.2, p.63) — Gajulapalli, *The Contraction Lemma Beyond ETH*
(manuscript, sha256 049caea1…): the polynomial `z ↦ F(t + αz)`. -/
noncomputable def zoom (a : ℕ) (t : ℤ) (F : ℚ[X]) : ℚ[X] :=
  F.comp (C (t : ℚ) + C (alpha a) * X)

/-- `π(z) = ∏_{s ∈ S \ {t}} (1 + αz/(t − s))` (Lemma A.11(c), p.64). -/
noncomputable def piPoly (a : ℕ) (t : ℤ) : ℚ[X] :=
  ∏ s ∈ (gridS a).erase t, (1 + C (alpha a / ((t : ℚ) - s)) * X)

end ContractionLemma


