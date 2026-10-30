-- Prove2me | Definitions.Def_PermBlockchain_Transfers_feeGain
-- name    : PermBlockchain_Transfers_feeGain
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:11:24.565825+00:00
-- url     : https://prove2.me/theorems/5e7fbf38-68a4-4ae7-9a28-e3a642b3fecc
-- title:
--   The fee gain $h(\phi_k;\phi)$ of Lemma B.1
-- statement:
--   In the supply-chain model of Iyengar, Saleh, Sethuraman and Wang, two vendors $h,l$ supply $4m$ manufacturers, each of a type $(q_i,\xi_i)\in\{A,B\}\times\{h,l\}$, and a unit mass of consumers buys from the manufacturers or takes an outside option.
--
--   For a candidate threshold $\phi$ and the fee $\kappa=X/G(\phi)$ with $X=\sum_i\chi_i$, the gain from paying is
--   $$h(\phi_k;\phi)=\max\{\Delta+L+h-\gamma,\ \phi_k\}-\frac{X}{G(\phi)}-\max\Bigl\{\frac{\Delta}{2}+L+h-\gamma,\ \phi_k\Bigr\},$$
--   the closed form in the first display of the proof of Lemma B.1, where $\Delta=H-L$.
--
--   **Formalization Note** That this equals $g(1,\phi_k;\phi)-g(0,\phi_k;\phi)$ at the paper's profile is the first milestone. If $G(\phi)=0$ Lean gives $X/0=0$; statements using the value carry a hypothesis implying $G(\phi)>0$.
-- source:
--   Iyengar, Saleh, Sethuraman, Wang, Economics of Permissioned Blockchain Adoption, SSRN 3602376 (version of 2022-08-19), Appendix B, proof of Lemma B.1, first display, p. 38 (PDF p. 39)

import Mathlib

namespace PermBlockchain.Transfers

/-- **The gain from paying the fee, `h(φ_k; φ) = g(1, φ_k; φ) − g(0, φ_k; φ)`, Lemma B.1.**
Iyengar, Saleh, Sethuraman, Wang, *Economics of Permissioned Blockchain Adoption*,
SSRN 3602376 (version of 2022-08-19), Appendix B, p. 38 (PDF p. 39), proof of Lemma B.1, first display:
`h(φ_k; φ) = max{∆ + L + h − γ, φ_k} − Σ_{i:i∈M} χ_i / G(φ) − max{∆/2 + L + h − γ, φ_k}`.

`feeGain Δ L h γ X G φk φ` is this expression with `X = Σ_i χ_i` and `G` the distribution function
of the outside option.

**Formalization Note.** The closed form is a definition; that it equals `g(1) − g(0)` at the
paper's full-adoption profile (with `κ = X / G(φ)`) is the milestone
`proof_prop_4_9_fee_stage_values`. For `G φ = 0` Lean's `X / 0 = 0`; statements that use the
value carry `0 < G φ` or a hypothesis implying it. -/
noncomputable def feeGain (Δ L h γ X : ℝ) (G : ℝ → ℝ) (φk φ : ℝ) : ℝ :=
  max (Δ + L + h - γ) φk - X / G φ - max (Δ / 2 + L + h - γ) φk

end PermBlockchain.Transfers


