-- Prove2me | Definitions.Def_RandomPromo_TwoPoint_Setting
-- name    : RandomPromo_TwoPoint_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T06:42:57.98001+00:00
-- url     : https://prove2.me/theorems/64a10638-346f-44eb-889e-7078a0d28aea
-- title:
--   §3, §3.2 — two customer segments, finitely supported price distributions, F, E[P|P ≤ x], E[(v − P)+], the threshold p^L, problems (2)–(3), Δ_R, U1, U2 and the two-point law
-- statement:
--   This file sets up the randomized-pricing model of Chen, Hu and Wu (§3 and §3.2.2) and the two optimization problems (2) and (3) over price distributions.
--
--   **Customers.** A fraction $\alpha$ of customers (low type) value the product at $v_L$ and pay a one-period waiting cost $c_L$; the remaining fraction $1-\alpha$ (high type) value it at $v_H$ and pay $c_H$. The **standing assumptions** are Assumption (S), $0<c_L<v_L$ and $0<c_H<v_H$; the printed ordering $v_L<v_H$; and $0<\alpha<1$.
--
--   **Price distributions.** The firm commits to a distribution of a random price $P$ with finite support (p. 9). It is represented by a mass function $f$ on $\mathbb R$ with finitely many nonzero values, $f(p)\ge 0$ and $\sum_p f(p)=1$. Prices may be of either sign. For such a law write
--   $$F(x)=\sum_{p\le x} f(p),\qquad F(x)\,\mathbb E[P\mid P\le x]=\sum_{p\le x} f(p)\,p,\qquad \mathbb E[(v-P)^+]=\sum_p f(p)\max(v-p,0),$$
--   and $\mathbb E[P\mid P\le x]$ for the quotient of the partial expectation by $F(x)$. The low type's purchase threshold is
--   $$\underline p^L=\max\{v' \mid \mathbb E[(v'-P)^+]\le c_L\}.$$
--
--   **Problems (2) and (3).** A law is *feasible* when $\mathbb E[(v_L-P)^+]>c_L$ (low types wait) and $\mathbb E[(v_H-P)^+]\le c_H$ (high types do not). Problem (2) maximizes
--   $$\alpha\,\mathbb E[P\mid P\le \underline p^L]+(1-\alpha)F(v_H)\,\mathbb E[P\mid P\le v_H]$$
--   over feasible laws, and its relaxation (3) maximizes $\alpha\,\mathbb E[P\mid P\le v_L]+(1-\alpha)F(v_H)\,\mathbb E[P\mid P\le v_H]$ over the same set.
--
--   **Constants.** With
--   $$\Delta_R=\sqrt{\frac{\alpha c_L}{(1-\alpha)(v_H-v_L)}},$$
--   the bounds of Lemma 6 are $U_1=\alpha v_L+(1-\alpha)v_H-(1-\alpha)c_L-2(1-\alpha)(v_H-v_L)\Delta_R$ and $U_2=\alpha v_L+(1-\alpha)v_H-(1-\alpha)c_H-\alpha c_L\frac{v_H-v_L}{c_H-c_L}$.
--
--   **The two-point law.** For $\delta,\eta\in\mathbb R$ put $\beta^*=\min\{\Delta_R,\frac{c_H-c_L}{v_H-v_L}-\delta\}$ and $\underline p^*=v_L-c_L/\beta^*-\eta$. The two-point mass function puts mass $\beta^*$ at $\underline p^*$ and mass $1-\beta^*$ at $v_H$ (Proposition 3).
--
--   These objects are the vocabulary of every statement of the mission.
--
--   **Formalization Note** A price distribution is a finitely supported function `w : ℝ →₀ ℝ` with `IsPriceDist w` (nonnegative masses, total mass one). `cdf`, `pexp`, `condExp`, `gain` are finite sums over the support; `condExp w x` is `pexp w x / cdf w x`, which Lean evaluates to $0$ when $F(x)=0$. That value never enters the statements on feasible laws, where $F(\underline p^L)>0$ and $F(v_L)>0$. `thresh w c` is the real supremum `sSup` of $\{v' \mid \mathbb E[(v'-P)^+]\le c\}$. For a price distribution and $c\ge 0$ this set is nonempty, closed and bounded above, so the supremum is the paper's maximum. Problem (2)'s first constraint is the definition of $\underline p^L$, so `Feas` holds only the two inequalities. The objectives keep the printed product $F(v_H)\cdot\mathbb E[P\mid P\le v_H]$. `twoPoint δ η` is defined for every real $\delta,\eta$; it is a probability law only when $0\le\beta^*\le1$. The Lean names are `vL vH cL cH α`, `ΔR`, `bnd` $=(c_H-c_L)/(v_H-v_L)$, `U1`, `U2`, `βstar`, `pstar`, `twoPoint`. The hypothesis $0<\alpha<1$ is not printed and is added: "a fraction α" of each segment, and $\Delta_R$ divides by $1-\alpha$.
-- source:
--   Chen, Hu, Wu, Intertemporal Price Discrimination via Randomized Promotions, SSRN preprint 3223844 (revision of 2022-11-16), pp. 9–16, §3 (p. 9), Assumption (S) (p. 10), p^i (p. 12), (2), (3) (p. 14), Lemma 6 (p. 15), Proposition 3 (p. 16)

import Mathlib

namespace RandomPromo.TwoPoint

/-- The primitives of the two-segment model (§3, p. 9): a fraction `α` of low-valuation customers
with valuation `vL` and one-period waiting cost `cL`, and a fraction `1 - α` of high-valuation
customers with valuation `vH` and waiting cost `cH`. -/
structure Params where
  vL : ℝ
  vH : ℝ
  cL : ℝ
  cH : ℝ
  α : ℝ

/-- The standing assumptions of §3: Assumption (S) (p. 10) `0 < cL < vL`, `0 < cH < vH`; the
printed `vH > vL` (p. 9); and `0 < α < 1` (a fraction of customers of each segment; `Δ_R` divides
by `1 - α`). -/
def Params.Standing (M : Params) : Prop :=
  0 < M.cL ∧ M.cL < M.vL ∧ 0 < M.cH ∧ M.cH < M.vH ∧ M.vL < M.vH ∧ 0 < M.α ∧ M.α < 1

/-- A price distribution (§3, p. 9: "we just consider the support of P to be finite"): a finitely
supported mass function `w` on the real line, with nonnegative masses summing to one. Prices may
have either sign. -/
def IsPriceDist (w : ℝ →₀ ℝ) : Prop :=
  (∀ p, 0 ≤ w p) ∧ (w.sum fun _ m => m) = 1

/-- The cumulative distribution function `F(x) = P(P ≤ x)`. -/
noncomputable def cdf (w : ℝ →₀ ℝ) (x : ℝ) : ℝ :=
  ∑ p ∈ w.support with p ≤ x, w p

/-- The partial expectation `F(x) E[P | P ≤ x] = E[P ; P ≤ x]`. -/
noncomputable def pexp (w : ℝ →₀ ℝ) (x : ℝ) : ℝ :=
  ∑ p ∈ w.support with p ≤ x, w p * p

/-- The conditional expectation `E[P | P ≤ x] = E[P ; P ≤ x] / F(x)`. When `F(x) = 0` Lean's
division returns `0`; this value is never used on laws feasible for (2)–(3). -/
noncomputable def condExp (w : ℝ →₀ ℝ) (x : ℝ) : ℝ :=
  pexp w x / cdf w x

/-- The expected surplus `E[(v - P)^+]` of a customer with valuation `v` who buys at a price `P`
drawn from `w`. -/
noncomputable def gain (w : ℝ →₀ ℝ) (v : ℝ) : ℝ :=
  ∑ p ∈ w.support, w p * max (v - p) 0

/-- The purchase threshold `p̲ = max {v' | E[(v' - P)^+] ≤ c}` (p. 12), taken as the supremum of
that set. -/
noncomputable def thresh (w : ℝ →₀ ℝ) (c : ℝ) : ℝ :=
  sSup {v' : ℝ | gain w v' ≤ c}

/-- The constraints of problems (2) and (3) (p. 14): low-valuation customers wait,
`E[(vL - P)^+] > cL`, and high-valuation customers do not, `E[(vH - P)^+] ≤ cH`. -/
def Params.Feas (M : Params) (w : ℝ →₀ ℝ) : Prop :=
  M.cL < gain w M.vL ∧ gain w M.vH ≤ M.cH

/-- The objective of problem (2) (p. 14):
`α E[P | P ≤ p̲^L] + (1 - α) F(vH) E[P | P ≤ vH]`, with `p̲^L = thresh w cL`. -/
noncomputable def Params.obj2 (M : Params) (w : ℝ →₀ ℝ) : ℝ :=
  M.α * condExp w (thresh w M.cL) + (1 - M.α) * cdf w M.vH * condExp w M.vH

/-- The objective of the relaxation (3) (p. 14):
`α E[P | P ≤ vL] + (1 - α) F(vH) E[P | P ≤ vH]`. -/
noncomputable def Params.obj3 (M : Params) (w : ℝ →₀ ℝ) : ℝ :=
  M.α * condExp w M.vL + (1 - M.α) * cdf w M.vH * condExp w M.vH

/-- `Δ_R = √(α cL / ((1 - α)(vH - vL)))` (Lemma 6, Proposition 3). -/
noncomputable def Params.ΔR (M : Params) : ℝ :=
  Real.sqrt (M.α * M.cL / ((1 - M.α) * (M.vH - M.vL)))

/-- The threshold `(cH - cL)/(vH - vL)` (p. 14, Lemma 6(ii), Proposition 3). -/
noncomputable def Params.bnd (M : Params) : ℝ :=
  (M.cH - M.cL) / (M.vH - M.vL)

/-- `U1 = α vL + (1 - α) vH - (1 - α) cL - 2 (1 - α)(vH - vL) Δ_R` (Lemma 6(ii)(a)). -/
noncomputable def Params.U1 (M : Params) : ℝ :=
  M.α * M.vL + (1 - M.α) * M.vH - (1 - M.α) * M.cL - 2 * (1 - M.α) * (M.vH - M.vL) * M.ΔR

/-- `U2 = α vL + (1 - α) vH - (1 - α) cH - α cL (vH - vL)/(cH - cL)` (Lemma 6(ii)(b)). -/
noncomputable def Params.U2 (M : Params) : ℝ :=
  M.α * M.vL + (1 - M.α) * M.vH - (1 - M.α) * M.cH - M.α * M.cL * ((M.vH - M.vL) / (M.cH - M.cL))

/-- `β* = min {Δ_R, (cH - cL)/(vH - vL) - δ}` (Proposition 3). -/
noncomputable def Params.βstar (M : Params) (δ : ℝ) : ℝ :=
  min M.ΔR (M.bnd - δ)

/-- The low price `p̲* = vL - cL/β* - η` of Proposition 3. -/
noncomputable def Params.pstar (M : Params) (δ η : ℝ) : ℝ :=
  M.vL - M.cL / M.βstar δ - η

/-- The two-point mass function of Proposition 3: mass `β*` at `p̲* = vL - cL/β* - η` and mass
`1 - β*` at `vH`. -/
noncomputable def Params.twoPoint (M : Params) (δ η : ℝ) : ℝ →₀ ℝ :=
  Finsupp.single (M.pstar δ η) (M.βstar δ) + Finsupp.single M.vH (1 - M.βstar δ)

end RandomPromo.TwoPoint


