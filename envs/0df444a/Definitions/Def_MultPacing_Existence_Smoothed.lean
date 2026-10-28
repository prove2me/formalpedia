-- Prove2me | Definitions.Def_MultPacing_Existence_Smoothed
-- name    : MultPacing_Existence_Smoothed
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-24T09:28:52.590081+00:00
-- url     : https://prove2.me/theorems/5a4a0c2d-b6ab-450d-9763-bfe9f8f4718a
-- title:
--   Definition 3, p. 11 — the (ϵ,H)-smoothed pacing game: reserve bid, band allocation, prices, artificial good, utility, pure Nash equilibrium
-- statement:
--   Fix a pacing game (valuations $v_{ij}\ge0$, budgets $B_i>0$), a smoothing parameter $\epsilon>0$ and a penalty $H$. For a profile of pacing multipliers $\alpha$ the $(\epsilon,H)$-smoothed pacing game computes allocations and payments as follows.
--
--   1. **Reserve bid.** On every good there is an artificial bid $2\epsilon$, treated as one more bidder. The bidders on good $j$ are the buyers, bidding $\alpha_i v_{ij}$, and the reserve, bidding $2\epsilon$.
--   2. **Allocation.** Let $b^*_j=\max\{2\epsilon,\ \max_i\alpha_i v_{ij}\}$ be the highest bid and $S_j$ the bidders whose bid is at least $b^*_j-\epsilon$. Each bidder $k$ has the band weight $w_{kj}=\max\{0,\ b_{kj}-(b^*_j-\epsilon)\}$, which is $0$ outside $S_j$, and buyer $i$ wins the fraction
--   $$
--   x_{ij}=\frac{w_{ij}}{\sum_{k} w_{kj}},
--   $$
--   the sum ranging over all bidders, the reserve included.
--   3. **Prices.** Buyer $i$ pays $p_{ij}$ per unit of good $j$, the highest bid on $j$ among the bidders other than $i$ (the reserve included) minus $\epsilon$, so $s_{ij}=x_{ij}p_{ij}$.
--   4. **Artificial good.** Buyer $i$ receives $\alpha_i$ units of an artificial good worth $2\epsilon$ per unit and pays $\alpha_i\epsilon$ for it. Her total spend is $\sigma_i(\alpha)=\alpha_i\epsilon+\sum_j s_{ij}$.
--   5. **Utility.**
--   $$
--   u_i(\alpha)=\varphi_H\bigl(B_i-\sigma_i(\alpha)\bigr)+2\alpha_i\epsilon+\sum_j x_{ij}v_{ij},\qquad \varphi_H(y)=\begin{cases}y,& y\ge0,\\ H y,& y<0,\end{cases}
--   $$
--   so the leftover budget counts once if she does not exceed her budget and $H$ times if she exceeds it.
--
--   A **pure-strategy Nash equilibrium** of the smoothed game is a profile $\alpha\in[0,1]^N$ such that no buyer $i$ can raise $u_i$ by replacing $\alpha_i$ with any other $a\in[0,1]$.
--
--   The smoothed game has continuous allocations and payments, which is what makes a Nash equilibrium existence theorem applicable (Theorem 2); its equilibria converge to a pacing equilibrium as $\epsilon\to0$, $H\to\infty$.
--
--   **Formalization Note** The bidders on a good are `Option N`, with `none` the reserve bidder. The band weights sum to at least $\epsilon$ (the top bidder has weight $\epsilon$), so the division defining $x_{ij}$ never divides by zero when $\epsilon>0$. The paper prints the denominator as $\sum_{i'\in S_j}[\alpha_i v_{ij}-(b^*_j-\epsilon)]$; it is read with $i'$ in place of $i$ inside the sum. The price is per buyer, $p_{ij}$, because the paper's $p_j$ is "the highest bid on $j$ among buyers other than $i$".
-- source:
--   Conitzer, Kroer, Sodomka & Stier-Moses, Multiplicative Pacing Equilibria in Auction Markets, arXiv:1706.07151v5, p. 11 (PDF 11), Definition 3

import Mathlib
import Definitions.Def_MultPacing_Existence_Model

namespace MultPacing.Existence

variable {N G : Type*} [Fintype N] [DecidableEq N] [Fintype G]

/-- Bids on good `j` in the `ε`-smoothed game (Definition 3, p. 11). The bidders are `Option N`:
`some i` is buyer `i`, bidding `α_i v_ij`, and `none` is the artificial reserve bidder, bidding `2ε`
("treated as one of the buyers"). -/
def smBid (P : PacingGame N G) (ε : ℝ) (α : N → ℝ) (j : G) : Option N → ℝ
  | none => 2 * ε
  | some i => α i * P.v i j

/-- The highest bid `b*_j` on good `j`, the reserve bid included. -/
noncomputable def topBid (P : PacingGame N G) (ε : ℝ) (α : N → ℝ) (j : G) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (smBid P ε α j)

/-- The band weight `max(0, b_k − (b*_j − ε))` of bidder `k` on good `j`; it is positive exactly for
the bidders strictly inside the band `S_j = {k : b_k ≥ b*_j − ε}` and `0` outside `S_j`. -/
noncomputable def bandWeight (P : PacingGame N G) (ε : ℝ) (α : N → ℝ) (j : G) (k : Option N) : ℝ :=
  max 0 (smBid P ε α j k - (topBid P ε α j - ε))

/-- The fraction `x_ij` of good `j` won by buyer `i` in the smoothed game: its band weight divided by
the sum of the band weights of all bidders in `S_j`, the reserve bidder included. -/
noncomputable def smAlloc (P : PacingGame N G) (ε : ℝ) (α : N → ℝ) (i : N) (j : G) : ℝ :=
  bandWeight P ε α j (some i) / ∑ k : Option N, bandWeight P ε α j k

/-- The per-unit price `p_ij` buyer `i` pays for good `j` in the smoothed game: the highest bid on
`j` among the bidders other than `i` (the reserve bidder included), minus `ε`. -/
noncomputable def smPrice (P : PacingGame N G) (ε : ℝ) (α : N → ℝ) (i : N) (j : G) : ℝ :=
  (Finset.univ.erase (some i)).sup' ⟨none, by simp⟩ (smBid P ε α j) - ε

/-- The payment `s_ij = x_ij p_ij` of buyer `i` for good `j` in the smoothed game. -/
noncomputable def smPay (P : PacingGame N G) (ε : ℝ) (α : N → ℝ) (i : N) (j : G) : ℝ :=
  smAlloc P ε α i j * smPrice P ε α i j

/-- Total spend `α_i ε + ∑_j s_ij` of buyer `i`, the artificial good included. -/
noncomputable def smSpend (P : PacingGame N G) (ε : ℝ) (α : N → ℝ) (i : N) : ℝ :=
  α i * ε + ∑ j, smPay P ε α i j

/-- The leftover-budget term of the smoothed utility: `y` if `y ≥ 0` (budget not exceeded) and
`H y` if `y < 0` (budget exceeded). -/
noncomputable def budgetTerm (H y : ℝ) : ℝ :=
  if 0 ≤ y then y else H * y

/-- Utility of buyer `i` in the `(ε, H)`-smoothed pacing game:
`(B_i − α_i ε − ∑_j s_ij) + 2 α_i ε + ∑_j x_ij v_ij` if she does not exceed her budget, and
`H (B_i − α_i ε − ∑_j s_ij) + 2 α_i ε + ∑_j x_ij v_ij` if she exceeds it. -/
noncomputable def smUtility (P : PacingGame N G) (ε H : ℝ) (α : N → ℝ) (i : N) : ℝ :=
  budgetTerm H (P.B i - smSpend P ε α i) + 2 * α i * ε + ∑ j, smAlloc P ε α i j * P.v i j

/-- A pure-strategy Nash equilibrium of the `(ε, H)`-smoothed pacing game: every multiplier lies in
`[0,1]` and no buyer gains by changing her own multiplier within `[0,1]`. -/
def IsSmoothedPNE (P : PacingGame N G) (ε H : ℝ) (α : N → ℝ) : Prop :=
  (∀ i, α i ∈ Set.Icc (0 : ℝ) 1) ∧
    ∀ i, ∀ a ∈ Set.Icc (0 : ℝ) 1, smUtility P ε H (Function.update α i a) i ≤ smUtility P ε H α i

end MultPacing.Existence


