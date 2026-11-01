-- Prove2me | Definitions.Def_RedundancyHT_lamC
-- name    : RedundancyHT_lamC
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:26:37.957557+00:00
-- url     : https://prove2.me/theorems/0ac5f76a-d64c-4706-b690-4362d8a3e325
-- title:
--   The arrival rate $\lambda_{\mathcal C(u_1,\dots,u_l)}$ of jobs compatible with a set of servers
-- statement:
--   For a set $U=\{u_1,\dots,u_l\}$ of servers,
--   $$\lambda_{\mathcal C(u_1,\dots,u_l)}=N\lambda\sum_{S:\,S\cap\{u_1,\dots,u_l\}\ne\emptyset}p_S$$
--   is the arrival rate of jobs compatible with at least one of these servers.
-- source:
--   Cardinaels, Borst & van Leeuwaarden, Heavy-Traffic Universality of Redundancy Systems with Assignment Constraints, arXiv:2005.14566v5, §2.3.2, p.8

import Definitions.Def_BipartiteMatchingHT_Delay_Primitives
import Definitions.Def_RedundancyHT_pSet

set_option autoImplicit false

open MeasureTheory Filter Topology BipartiteMatchingHT.Delay
open scoped BigOperators ENNReal BoundedContinuousFunction

noncomputable section

namespace RedundancyHT

/-- **`λ_{𝒞(u₁,…,u_l)} = N λ Σ_{S:S∩{u₁,…,u_l}≠∅} p_S`** for the server set `U`
(arXiv:2005.14566v5, p.8). The published `someClasses D.edge U` is the set of types compatible with
at least one server in `U`. -/
def lamC {n m : ℕ} (D : Model n m) (lam : ℝ) (U : Finset (Fin m)) : ℝ :=
  (m : ℝ) * lam * pSet D (someClasses D.edge U)

end RedundancyHT


