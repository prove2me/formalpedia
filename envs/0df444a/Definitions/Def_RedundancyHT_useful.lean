-- Prove2me | Definitions.Def_RedundancyHT_useful
-- name    : RedundancyHT_useful
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:23:52.425842+00:00
-- url     : https://prove2.me/theorems/759ac6c0-b04a-4b01-a8e7-5888a4e7786c
-- title:
--   Useful servers
-- statement:
--   A server is useful if at least one job type is compatible with it.
--
--   **Formalization Note** The paper does not use this term. A server that is not useful never receives a job, and if it were counted in the idle vector of (5) the denominator $\lambda_{\mathcal C(u_1,\dots,u_l)}$ could vanish.
-- source:
--   Cardinaels, Borst & van Leeuwaarden, Heavy-Traffic Universality of Redundancy Systems with Assignment Constraints, arXiv:2005.14566v5, §2.3.2, display (5), p.8

import Definitions.Def_BipartiteMatchingHT_Delay_Primitives

set_option autoImplicit false

open MeasureTheory Filter Topology BipartiteMatchingHT.Delay
open scoped BigOperators ENNReal BoundedContinuousFunction

noncomputable section

namespace RedundancyHT

/-- **A useful server**: one compatible with at least one job type.

**Formalization Note.** The paper does not name this. Its graph is arbitrary, so a server may be
compatible with no type. Such a server never works, and it makes `λ_{𝒞(u₁,…,u_l)}` vanish in (5)
(arXiv:2005.14566v5, p.8) when it heads the idle list. -/
def useful {n m : ℕ} (D : Model n m) (j : Fin m) : Prop :=
  ∃ i, D.compatible i j = true

end RedundancyHT


