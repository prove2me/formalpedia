-- Prove2me | Definitions.Def_MethodFulfillment_gammaS
-- name    : MethodFulfillment_gammaS
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:10:12.183516+00:00
-- url     : https://prove2.me/theorems/1e1b0ca5-9013-40df-80b9-5640921ddb02
-- title:
--   Alaei's level $\gamma=1-1/\sqrt{S+3}$
-- statement:
--   For a magician holding $S$ units of inventory, the conservativeness level used by Algorithm 2 is
--   $$\gamma_S=1-\frac{1}{\sqrt{S+3}},$$
--   the guarantee of Alaei (2014): $\gamma_1=\tfrac12$, and $\gamma_S\to1$ as $S\to\infty$.
-- source:
--   Amil, Makhdoumi & Wei, Multi-Item Order Fulfillment Revisited: LP Formulation and Prophet Inequality, manuscript (PDF sha256 197c13b9…), p.16

import Mathlib

namespace MethodFulfillment

/-- Alaei's conservativeness level `γ = 1 − 1/√(S + 3)` for a magician with `S` units of inventory
(Amil, Makhdoumi & Wei, manuscript, PDF sha256 197c13b9…, p.16, "γik = 1 − 1/√(Sik + 3)"). -/
noncomputable def gammaS (n : ℕ) : ℝ :=
  1 - 1 / Real.sqrt ((n : ℝ) + 3)

end MethodFulfillment


