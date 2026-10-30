-- Prove2me | Definitions.Def_ICOTheory_Signaling_SignalingAdvantage
-- name    : ICOTheory_Signaling_SignalingAdvantage
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:04:39.787072+00:00
-- url     : https://prove2.me/theorems/e9d7568d-b29a-45ff-a8cb-4d73f7e76ce2
-- title:
--   Tokens have a signaling advantage over equity: $\bar\alpha^T_H\le\alpha^*<\bar\alpha^E_H$
-- statement:
--   With $\alpha^*$ the threshold (25) and $\bar\alpha^T_H$, $\bar\alpha^E_H$ the minimal token and equity shares (21) of a venture believed to be of high quality, **tokens have a signaling advantage over equity** when
--
--   $$
--   \bar\alpha^T_H\le\alpha^*<\bar\alpha^E_H .
--   $$
--
--   By Proposition 5 a least-cost separating equilibrium exists under financing $i\in\{E,T\}$ exactly when $\bar\alpha^i_H\le\alpha^*$; so under this inequality separation is feasible with tokens but not with equity (p. 21, Corollary 1(ii)). Proposition 6 defines the advantage by this inequality ("i.e.").
--
--   **Formalization Note** The advantage is the inequality itself, as in the paper's "i.e."; the signaling game of Proposition 5 is not formalized.
-- source:
--   Chod, Lyandres, A Theory of ICOs: Diversification, Agency, and Information Asymmetry, SSRN 3159528 (December 14, 2019), Proposition 6, p. 22 ("tokens have a signaling advantage over equity, i.e., ᾱT_H ≤ α∗ < ᾱE_H"); p. 21

import Mathlib
import Definitions.Def_ICOTheory_Signaling_alphaStar
import Definitions.Def_ICOTheory_Signaling_alphaBarT
import Definitions.Def_ICOTheory_Signaling_alphaBarE

namespace ICOTheory.Signaling

/-- **Tokens have a signaling advantage over equity: `ᾱ^T_H ≤ α* < ᾱ^E_H`.**
Chod, Lyandres, *A Theory of ICOs: Diversification, Agency, and Information Asymmetry*,
SSRN 3159528 (December 14, 2019), Proposition 6, p. 22: "tokens have a signaling advantage
over equity, i.e., `ᾱ^T_H ≤ α* < ᾱ^E_H`"; p. 21: "if `ᾱ^T_H ≤ α* < ᾱ^E_H`, separation is
feasible under token financing, but not under equity financing" (Proposition 5, p. 20: a
least-cost separating equilibrium exists under financing `i` iff `ᾱ^i_H ≤ α*`; Corollary 1(ii),
p. 21).

`SignalingAdvantage μH μL σ γ I C` is the inequality
`alphaBarT I μH ≤ alphaStar μH μL σ γ < alphaBarE I C μH`.

**Formalization Note.** Following the paper's "i.e.", the advantage is the inequality itself;
the signaling game of Proposition 5 is not formalized. `𝔼R_H = μ_H/4` (p. 18). -/
def SignalingAdvantage (μH μL σ γ I C : ℝ) : Prop :=
  alphaBarT I μH ≤ alphaStar μH μL σ γ ∧ alphaStar μH μL σ γ < alphaBarE I C μH

end ICOTheory.Signaling


