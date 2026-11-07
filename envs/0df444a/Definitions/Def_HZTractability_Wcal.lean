-- Prove2me | Definitions.Def_HZTractability_Wcal
-- name    : HZTractability_Wcal
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T04:05:51.096244+00:00
-- url     : https://prove2.me/theorems/16cd1ec4-3195-4669-8f28-97cd5aa94970
-- title:
--   Total unapproved expenditure $\mathcal W$
-- statement:
--   In an HZ market with utilities $u_{ij}$, allocation $x$ and prices $p$, the **total unapproved expenditure** is the expenditure of all buyers on goods they value at zero:
--   $$
--   \mathcal W=\sum_i\sum_{j:\,u_{ij}=0}p_jx_{ij}.
--   $$
--   Lemma 4.9 bounds $\mathcal W$ by $C_aN\varepsilon$, and Lemma 4.10 decodes correctly when $\mathcal W$ is small.
--
--   **Formalization Note** Defined for any finite market. The script $\mathcal W$ is distinct from the floor buyers' approved target expenditure $W_v$.
-- source:
--   Panageas, Shein, Taherijam, Vazirani, Exploring the Tractability Frontier of Hylland–Zeckhauser Models, arXiv:2610.35848 (held version, sha256 74b7bf9f…), §4.5, p.17 (PDF p.19)

import Mathlib

namespace HZTractability

/-- **Total unapproved expenditure** `𝒲` (Panageas–Shein–Taherijam–Vazirani, arXiv:2610.35848,
held version, sha256 74b7bf9f…, §4.5, p.17 (PDF 19): "𝒲 = ∑_i ∑_{j : u_ij = 0} p_j x_ij").

The total expenditure of all buyers on goods they value at zero.

**Formalization Note** Defined for any finite market; the paper uses it for the market
`M(G; a, τ, K)` after equalizing group prices. Script `𝒲` is distinct from the floor buyers'
target expenditure `W_v` (`floorTargetExp`). -/
noncomputable def Wcal {B G : Type} [Fintype B] [Fintype G] (u : B → G → ℝ) (x : B → G → ℝ)
    (p : G → ℝ) : ℝ :=
  ∑ i, ∑ j, if u i j = 0 then p j * x i j else 0

end HZTractability


