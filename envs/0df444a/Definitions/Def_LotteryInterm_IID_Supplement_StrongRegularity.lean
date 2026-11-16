-- Prove2me | Definitions.Def_LotteryInterm_IID_Supplement_StrongRegularity
-- name    : LotteryInterm_IID_Supplement_StrongRegularity
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T20:05:51.226733+00:00
-- url     : https://prove2.me/theorems/443cc50b-8d3a-40e7-a467-8e840e47e681
-- title:
--   α-strong regularity, $c_\alpha$, anonymous posted-price revenue and monopoly reserves
-- statement:
--   These definitions extend the published value laws $D$ (density on $[a,b)$, optional terminal atom at a finite $b$, virtual value $\phi(t)=t-S(t)/f(t)$ with $S(t)=\Pr[V>t]$, and $\phi(b)=b$).
--
--   1. **α-strong regularity** (Definition A.2). For $\alpha\ge0$, $D$ is α-strongly regular if
--   $$\phi(y)-\phi(x)\ge\alpha\,(y-x)\qquad\text{for all } a<x\le y\le b .$$
--   For $\alpha=0$ this is exactly the published regularity; $\alpha=1$ is the monotone hazard rate condition.
--   2. **The constant** $c_\alpha=\alpha^{1/(1-\alpha)}$ for $\alpha<1$ and $c_1=1/e$, defined by cases.
--   3. **Anonymous posted-price revenue.** For independent bidders with laws $D_1,\dots,D_n$ and a price $p$, the revenue of selling at price $p$ to a bidder with value at least $p$ is $p\Pr[\exists i,\ v_i\ge p]$. $\mathrm{APRev}$ is its supremum over $p\ge0$ (an extended real), and an optimal anonymous price $\mathrm{AP}^*$ is a $p\ge0$ attaining it.
--   4. **Monopoly reserve.** A price $r\ge0$ maximizing $t\Pr[v\ge t]$ over $t\ge0$.
--
--   They are used by the strong-regularity results of §4.2.1 and §6.2.3 and by Lemma A.7.
--
--   **Formalization Note** Strong regularity is imposed on the same set $(a,b]$ as the published `Regular`, so a zero density at the lowest support point (a null type) is allowed.
-- source:
--   Jingyi Liu, Aviad Rubinstein, Ertem Nusret Tas, Matt Weinberg, Qianfan Zhang, STOC 2027 submission #623 (October 2026), Definition A.2 and Lemma A.3, p.37 (PDF p.38); §3.1, p.9 (PDF p.10); APRev before Theorem A.10, p.40 (PDF p.41); Lemma A.7, p.39 (PDF p.40); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/623.pdf

import Definitions.Def_LotteryInterm_IID_ValueDist

open MeasureTheory

namespace LotteryInterm.IID.Supplement

/-- Definition A.2 on the published value laws: on the set where the published
`Regular` asks monotonicity, the virtual value grows at least at slope `α`.
With `α = 0` this is exactly `Regular`; `α = 1` is MHR. -/
def StronglyRegular (α : ℝ) (D : ValueDist) : Prop :=
  ∀ x y : ℝ, D.lo < x → (y : WithTop ℝ) ≤ D.hi → x ≤ y →
    α * (y - x) ≤ virtualValue D y - virtualValue D x

/-- `c_α = α^{1/(1-α)}` for `α < 1` and `c_1 = 1/e`, by cases (no limit). -/
noncomputable def cAlpha (α : ℝ) : ℝ :=
  if α < 1 then α ^ (1 / (1 - α)) else Real.exp (-1)

/-- Revenue of the anonymous posted price `p` without an intermediary: the item is
sold at price `p` whenever some bidder has value at least `p`. -/
noncomputable def anonymousPriceRevenue {n : ℕ} (D : Fin n → ValueDist) (p : ℝ) : ℝ :=
  p * ((prior D) {v | ∃ i, p ≤ v i}).toReal

/-- `APRev`: the best anonymous posted-price revenue without an intermediary. -/
noncomputable def APRev {n : ℕ} (D : Fin n → ValueDist) : EReal :=
  ⨆ (p : ℝ) (_ : 0 ≤ p), ((anonymousPriceRevenue D p : ℝ) : EReal)

/-- An optimal anonymous posted price `AP*`: a nonnegative price attaining `APRev`. -/
def IsOptimalAnonymousPrice {n : ℕ} (D : Fin n → ValueDist) (p : ℝ) : Prop :=
  0 ≤ p ∧ ((anonymousPriceRevenue D p : ℝ) : EReal) = APRev D

/-- A monopoly reserve: a nonnegative price maximizing `t · Pr[v ≥ t]` over `t ≥ 0`. -/
def IsMonopolyReserve (D : ValueDist) (r : ℝ) : Prop :=
  0 ≤ r ∧ ∀ t : ℝ, 0 ≤ t → t * (D.law (Set.Ici t)).toReal ≤ r * (D.law (Set.Ici r)).toReal

end LotteryInterm.IID.Supplement


