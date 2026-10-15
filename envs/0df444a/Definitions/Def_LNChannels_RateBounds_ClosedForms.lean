-- Prove2me | Definitions.Def_LNChannels_RateBounds_ClosedForms
-- name    : LNChannels_RateBounds_ClosedForms
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T09:02:36.000001+00:00
-- url     : https://prove2.me/theorems/ef7e1ec5-e914-40c8-9105-2c6fe2baa987
-- title:
--   (3), p. 6 — the closed-form cost $c^{l_1,l_2}(\lambda_1,\lambda_2)$ of a bidirectional channel for real sizes
-- statement:
--   Two nodes of the Lightning Network share a payment channel. Node 1 pays node 2 one unit at the jumps of a Poisson process with rate $\lambda_1$, node 2 pays node 1 one unit at the jumps of an independent Poisson process with rate $\lambda_2$. Capital is discounted at the continuously compounded rate $r$, and every reset of the channel (an on-chain transaction that closes and reopens it) costs $B$. Node $i$ commits the amount $l_i$ to the channel.
--
--   Let $\alpha_\pm$ be the two roots (4) of $\lambda_2\alpha^2-(\lambda_1+\lambda_2+r)\alpha+\lambda_1=0$ (the definitions `LNChannels.Exact.alphaPlus` and `LNChannels.Exact.alphaMinus`). For real sizes $l_1,l_2$ set
--
--   $$N=\alpha_-^{l_1}\bigl(1-\alpha_+^{l_1+l_2}\bigr)-\alpha_+^{l_1}\bigl(1-\alpha_-^{l_1+l_2}\bigr)$$
--
--   and define the bidirectional cost expression of (3),
--
--   $$c^{l_1,l_2}(\lambda_1,\lambda_2) = l_1+l_2 - B\,\frac{N}{N+\alpha_+^{l_1+l_2}-\alpha_-^{l_1+l_2}}.$$
--
--   Theorem 1 (ii) of the paper states that at natural sizes this is the expected discounted total cost (capital cost plus reset costs) of keeping the channel open forever. Theorems 2 and 3 minimize it over real sizes $l_1,l_2>0$ and compare the minimum with the cost of settling every payment on chain.
--
--   **Formalization Note** The module defines only `biCost`; it imports the shared definitions of $\alpha_\pm$ and of the unidirectional cost expression (1) (`LNChannels.Exact.uniCost`), which the theorems of the same missions use alongside it. The sizes are real numbers and the powers are real powers (`Real.rpow`), because the paper's proofs minimize over real sizes ("$\inf_{m>0}$", p. 11). At natural sizes the expression agrees with the integer-lattice cost of Theorem 1, which is a theorem of the mission *Channels I*, not part of this definition. When $\lambda_1,\lambda_2,r>0$ one has $0<\alpha_-<1<\alpha_+$, so the real powers have positive bases, and the denominator $N+\alpha_+^{l_1+l_2}-\alpha_-^{l_1+l_2}$ is positive for all real $l_1,l_2>0$. The definition places no sign conditions on the parameters; every theorem using it states them.
-- source:
--   Guasoni, Huberman & Shikhelman, Lightning Network Economics: Channels, Management Science (Articles in Advance, Nov. 6, 2023), DOI 10.1287/mnsc.2022.01664, p. 6 (PDF p. 7), Theorem 1, eqs. (1), (3), (4)

import Mathlib
import Definitions.Def_LNChannels_Exact_alphaPlus
import Definitions.Def_LNChannels_Exact_uniCost
import Definitions.Def_LNChannels_Exact_alphaMinus

namespace LNChannels.RateBounds

/-- The cost (3) of a bidirectional channel with rates `lam₁, lam₂` and (real) sizes `l₁, l₂`:
`l₁ + l₂ − B N / (N + α₊^{l₁+l₂} − α₋^{l₁+l₂})` with
`N = α₋^{l₁}(1 − α₊^{l₁+l₂}) − α₊^{l₁}(1 − α₋^{l₁+l₂})`. The powers are `Real.rpow`. -/
noncomputable def biCost (lam₁ lam₂ r B l₁ l₂ : ℝ) : ℝ :=
  let a := LNChannels.Exact.alphaMinus lam₁ lam₂ r
  let b := LNChannels.Exact.alphaPlus lam₁ lam₂ r
  let N := a ^ l₁ * (1 - b ^ (l₁ + l₂)) - b ^ l₁ * (1 - a ^ (l₁ + l₂))
  l₁ + l₂ - B * N / (N + b ^ (l₁ + l₂) - a ^ (l₁ + l₂))

end LNChannels.RateBounds


