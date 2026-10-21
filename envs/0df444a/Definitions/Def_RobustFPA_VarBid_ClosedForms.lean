-- Prove2me | Definitions.Def_RobustFPA_VarBid_ClosedForms
-- name    : RobustFPA_VarBid_ClosedForms
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T09:19:00.988973+00:00
-- url     : https://prove2.me/theorems/7eeaa7f8-4d9b-4583-af6b-9c758f35799b
-- title:
--   Closed forms for $G$ uniform: $u^+$, $u^-$, $\tilde b$, the maximal losses of bidding too high / too low, the set $X$ and Equation (3) (pp. 22–23, 49)
-- statement:
--   This file collects the explicit functions of §6.2 for $G$ uniform on $[L, v_1]$. Write $v = v_1$ and $p(b) = (b - L)/(v - L)$.
--
--   1. Utility when bidding above the common bid of the unconstrained opponents:
--   $$u^+(b) = \sum_{k=0}^{n-1}\binom{n-1}{k}\tau^k(1-\tau)^{n-1-k}p(b)^k(v-b) = (v-b)\,\bigl(1-\tau+\tau p(b)\bigr)^{n-1}.$$
--   2. Utility when bidding below it: $u^-(b) = \tau^{n-1}p(b)^{n-1}(v-b)$.
--   3. The interior maximiser $\tilde b = v - \dfrac{v-L}{n\tau}$, and the peak bid $\max\{L, \tilde b\}$.
--   4. The maximal loss of bidding too high, $\sup_{\hat h \in [L,b]} u^+(\hat h) - u^+(b)$, and of bidding too low, $\sup_{\hat h > b} u^+(\hat h) - u^-(b)$.
--   5. The set $X = \{b \in [L, v] : \text{too-high}(b) = \text{too-low}(b)\}$ of Proposition 3.
--   6. Equation (3): $u^+(\max\{L,\tilde b\}) - u^+(b) = u^+(b) - u^-(b)$.
--
--   These are the quantities in which Propositions 3 and 4 are stated; none of them is the definition of the minimax loss bid, which comes from the loss (see the Model file).
--
--   **Formalization Note.** $u^+$ is written in the product form of p. 49 (equal to the binomial sum of p. 23 by the binomial theorem), as a polynomial in $b$ on all of $\mathbb R$; on $[L, v]$ it is the paper's function. The suprema are real `sSup`s; on the sets used ($[L,b]$ with $L \le b$, and $(b,\infty)$) the image of $u^+$ is nonempty and bounded above, because $u^+$ is continuous and negative beyond $v$. $n$ is a natural number and the exponent $n-1$ is natural-number subtraction, meaningful for $n \ge 2$ as assumed in every theorem.
-- source:
--   Kasberger & Schlag, Robust Bidding in First-Price Auctions, SSRN 3044438 (version of 3 Sep 2022), p. 22 (u⁺, u⁻, maximal losses, Proposition 3's X), p. 23 (G uniform, b̃, Equation (3)), p. 49 (product form of u⁺)

import Mathlib

namespace RobustFPA.VarBid

/-- `u⁺(b) = (v - b) (1 - τ + τ p(b))^{n-1}` with `p(b) = (b - L)/(v - L)` (pp. 23, 49): bidder 1's
expected utility when bidding above the common bid of the unconstrained opponents, `G` uniform. -/
noncomputable def uPlus (n : ℕ) (τ L v b : ℝ) : ℝ :=
  (v - b) * (1 - τ + τ * ((b - L) / (v - L))) ^ (n - 1)

/-- `u⁻(b) = (τ p(b))^{n-1} (v - b)` (p. 23): expected utility when bidding below the common bid of
the unconstrained opponents, `G` uniform. -/
noncomputable def uMinus (n : ℕ) (τ L v b : ℝ) : ℝ :=
  (τ * ((b - L) / (v - L))) ^ (n - 1) * (v - b)

/-- `b̃ = v - (v - L)/(n τ)` (p. 23). -/
noncomputable def bTilde (n : ℕ) (τ L v : ℝ) : ℝ :=
  v - (v - L) / ((n : ℝ) * τ)

/-- `max{L, b̃}`, the maximiser of `u⁺` on `[L, ∞)` (Lemma 2). -/
noncomputable def peakBid (n : ℕ) (τ L v : ℝ) : ℝ :=
  max L (bTilde n τ L v)

/-- Maximal loss of bidding too high, `sup_{ĥ ∈ [L, b]} u⁺(ĥ) − u⁺(b)` (Proposition 3, p. 22). -/
noncomputable def tooHigh (n : ℕ) (τ L v b : ℝ) : ℝ :=
  sSup (uPlus n τ L v '' Set.Icc L b) - uPlus n τ L v b

/-- Maximal loss of bidding too low, `sup_{ĥ > b} u⁺(ĥ) − u⁻(b)` (Proposition 3, p. 22). -/
noncomputable def tooLow (n : ℕ) (τ L v b : ℝ) : ℝ :=
  sSup (uPlus n τ L v '' Set.Ioi b) - uMinus n τ L v b

/-- The set `X = {b ∈ [L, v] : tooHigh(b) = tooLow(b)}` of Proposition 3 (p. 22). -/
def equalizerSet (n : ℕ) (τ L v : ℝ) : Set ℝ :=
  {b | b ∈ Set.Icc L v ∧ tooHigh n τ L v b = tooLow n τ L v b}

/-- Equation (3) (p. 23): `u⁺(max{L, b̃}) − u⁺(b) = u⁺(b) − u⁻(b)`. -/
def Equation3 (n : ℕ) (τ L v b : ℝ) : Prop :=
  uPlus n τ L v (peakBid n τ L v) - uPlus n τ L v b = uPlus n τ L v b - uMinus n τ L v b

end RobustFPA.VarBid


