-- Prove2me | Definitions.Def_MoneyBurningTrade_IndependentSurplus_Thresholds
-- name    : MoneyBurningTrade_IndependentSurplus_Thresholds
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T20:44:11.230908+00:00
-- url     : https://prove2.me/theorems/38476a4d-f521-43dc-8ef6-335bfde746e1
-- title:
--   Lemma 4.3 — shifted thresholds and rounding indices
-- statement:
--   For a normalized grid and slack $\tau$, set $s_0=b_0=0$, $s_n=b_n=1$, and $s_i=q_i+\tau$, $b_i=q_i-\tau$ for $1\le i<n$. The rounding indices are
--
--   $$\iota_S(s)=\min\{r\in\{0,\ldots,n\}:s\le s_r\},\quad\iota_B(b)=\max\{r\in\{0,\ldots,n\}:b_r\le b\}.$$
--
--   Thus threshold ties use weak inequalities on both sides. For reports in $[0,1]$ the finite candidate sets are nonempty. These indices drive the construction without restricting reports to the prior supports.
-- source:
--   Moshe Babaioff, Noam Nisan, Ariel Shaulker, STOC 2027 submission #303 (October 2026), Lemma 4.3, after equation (16), printed p. 24 (PDF p. 25); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/303.pdf

import Definitions.Def_MoneyBurningTrade_IndependentSurplus_Grid

open MeasureTheory

set_option autoImplicit false

namespace MoneyBurningTrade.IndependentSurplus

/-- Seller thresholds in Lemma 4.3; endpoint thresholds are not shifted. -/
def sellerThreshold (G : Grid) (τ : ℝ) (i : ℕ) : ℝ :=
  if i = 0 then 0 else if i = G.n then 1 else G.q i + τ

/-- Buyer thresholds in Lemma 4.3. -/
def buyerThreshold (G : Grid) (τ : ℝ) (i : ℕ) : ℝ :=
  if i = 0 then 0 else if i = G.n then 1 else G.q i - τ

/-- Upward rounding with the weak threshold tie s ≤ s_r. The minimum exists
for reports in [0,1], since r=n qualifies. Off-domain empty sets return 0. -/
noncomputable def sellerIndex (G : Grid) (τ s : ℝ) : ℕ :=
  sInf {r : ℕ | r ≤ G.n ∧ s ≤ sellerThreshold G τ r}

/-- Downward rounding with the weak tie b_r ≤ b. The candidate set lies in
{0,...,n}; it is nonempty for reports in [0,1]. -/
noncomputable def buyerIndex (G : Grid) (τ b : ℝ) : ℕ :=
  sSup {r : ℕ | r ≤ G.n ∧ buyerThreshold G τ r ≤ b}

end MoneyBurningTrade.IndependentSurplus


