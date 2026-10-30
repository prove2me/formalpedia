-- Prove2me | Definitions.Def_HuangYin_vHL
-- name    : HuangYin_vHL
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:33:48.252762+00:00
-- url     : https://prove2.me/theorems/321b5112-9ee6-4a23-b0d8-fb10d2426e74
-- title:
--   The intermediate price $v_{HL}$
-- statement:
--   The intermediate price is
--
--   $$v_{HL} \equiv \frac{v_H-v_L}{2}+v_L .$$
--
--   It is the expected valuation of a customer whose single anecdote reveals product $H$, and for one anecdote it is the second of the two price candidates $v_L$ and $v_{HL}$ of the paper's Lemma 1. Every closed form of Proposition 1 is written through $v_{HL}-c_L$.
-- source:
--   Huang and Yin, Dynamic Probabilistic Selling When Customers Have Boundedly Rational Expectations, SSRN manuscript 3627927 (2020), §4, p. 11 (definition of vHL)

import Mathlib
import Definitions.Def_HuangYin_Params

namespace HuangYin

/-- **The intermediate price** `vHL ≡ (vH − vL)/2 + vL` (§4, p. 11; unnumbered).
Huang and Yin, *Dynamic Probabilistic Selling When Customers Have Boundedly Rational
Expectations*, SSRN manuscript 3627927 (2020), §4, p. 11: "For ease of exposition, we define vHL ≡ (vH−vL)/2 + vL hereafter."
It is the price `p^(1)` of Lemma 1 for `K = 1`: the expected valuation of a customer whose single
anecdote is `H`. -/
noncomputable def vHL (P : Params) : ℝ := (P.vH - P.vL) / 2 + P.vL

end HuangYin


