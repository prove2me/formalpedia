-- Prove2me | Definitions.Def_SponsoredAssort_pointEps
-- name    : SponsoredAssort_pointEps
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:49:53.462329+00:00
-- url     : https://prove2.me/theorems/6558842e-7b8d-4d5b-b5db-95c0fc170e07
-- title:
--   The profile $v(\epsilon)=(\epsilon,(r_1/r_2)\epsilon,\dots,(r_1/r_n)\epsilon)$
-- statement:
--   For $\epsilon>0$ let
--
--   $$
--   v(\epsilon)=\Big(\epsilon,\ \frac{r_1}{r_2}\epsilon,\ \dots,\ \frac{r_1}{r_n}\epsilon\Big).
--   $$
--
--   At this profile every single seller yields the same welfare to first order, $R(\{i\},v(\epsilon))=r_1\epsilon/(1+(r_1/r_i)\epsilon)$, which is the starting point of the upper bound in Proposition 5.4.
--
--   **Formalization Note** $\epsilon\in\mathbb R_{\ge0}$, and the coordinates are truncated at $0$, which changes nothing for positive revenues.
-- source:
--   Balseiro, Désir, Incentive-Compatible Assortment Optimization for Sponsored Products, SSRN 3821382 (Feb. 21, 2022), Appendix G.3, OA p.38

import Mathlib
import Definitions.Def_SponsoredAssort_Attr

open scoped NNReal

namespace SponsoredAssort

/-- The profile `v(ε) = (ε, (r₁/r₂)ε, …, (r₁/rₙ)ε)` (Balseiro, Désir, SSRN 3821382
(Feb. 21, 2022), Appendix G.3, OA p.38), at which every seller has the same single-seller welfare
`R({i}, v(ε)) = r₁ε / (1 + (r₁/rᵢ)ε)`.

**Formalization Note.** `ε : ℝ≥0`; `r₁` is `r 0` (0-based sellers, `n ≥ 1`). Coordinates are
`Real.toNNReal ((r₁/rₖ)·ε)`, which is exactly `(r₁/rₖ)·ε` for positive revenues. -/
noncomputable def pointEps {n : ℕ} [NeZero n] (r : Fin n → ℝ) (ε : ℝ≥0) : Attr n :=
  fun k => Real.toNNReal (r 0 / r k * ε)

end SponsoredAssort


