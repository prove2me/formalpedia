-- Prove2me | Definitions.Def_AdvanceSales_Pricing_Setting
-- name    : AdvanceSales_Pricing_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T06:44:07.756693+00:00
-- url     : https://prove2.me/theorems/9b2cd6aa-d382-4103-8b3f-eea3a1adeea2
-- title:
--   The high-demand advance-sales game, equilibrium, profit, and price thresholds
-- statement:
--   Consider one unit sold at one fixed price over two periods. Monetary values are divided by the arrival cost: $v$ is the late value, $k>0$ the early-purchase penalty, and $p\ge0$ the price. Write $x$ and $y$ for the two Poisson arrival rates. Define $\phi(0)=1$ and $\phi(z)=(1-e^{-z})/z$ for $z\ne0$. The normalized arrival utilities and seller profit are
--
--   $$u_1=-1+(v-p-k)\phi(x),\qquad u_2=-1+e^{-x}(v-p)\phi(y),\qquad \pi=p(1-e^{-(x+y)}).$$
--
--   An equilibrium has $x,y\ge0$; at a positive rate its corresponding utility is zero, while at a zero rate the utility is nonpositive. The set of attainable profits ranges over every $p\ge0$ and every equilibrium at that price. The definitions also introduce the principal Lambert function $W[a]$, $R(a)=W[-ae^{-a}]$, the paper's $A$, $W=W[-(k+1)e^{-(k+1)}]$, $f(v)=(1-v/(k+1))W-\ln(v-k)$, its larger root $v_f$, the regional border $v(k)$, and the printed candidate prices and profits $p_i,\pi_i$ for $i=2,3,4$.
--
--   This is the shared model for the mission's equilibrium and optimization theorems. It represents the paper's high-demand limit, where only equilibrium types 1–4 occur.
--
--   **Formalization Note** The principal branch, $v_f$, and $v(k)$ are chosen from their defining characterizations; the unused value of each partial characterization is zero. Every theorem using them restricts to the paper's domain. The limit value $\phi(0)=1$ is explicit.
-- source:
--   Glazer, Hassin, Nowik, How Advance Sales Can Reduce Profits, arXiv:1912.02869v2, pp. 7–14, 26–27, 38, 42–43, (4)–(6), Table 1, Definitions 11–13, 19, 24, 26

import Mathlib

namespace AdvanceSales.Pricing

noncomputable def phi (x : ℝ) : ℝ :=
  if x = 0 then 1 else (1 - Real.exp (-x)) / x

noncomputable def u1 (v k p x : ℝ) : ℝ :=
  -1 + (v - p - k) * phi x

noncomputable def u2 (v p x y : ℝ) : ℝ :=
  -1 + Real.exp (-x) * (v - p) * phi y

def IsEq (v k p x y : ℝ) : Prop :=
  0 ≤ x ∧ 0 ≤ y ∧
  (x = 0 → u1 v k p x ≤ 0) ∧ (0 < x → u1 v k p x = 0) ∧
  (y = 0 → u2 v p x y ≤ 0) ∧ (0 < y → u2 v p x y = 0)

noncomputable def profit (p x y : ℝ) : ℝ :=
  p * (1 - Real.exp (-(x + y)))

def Profits (v k : ℝ) : Set ℝ :=
  {z | ∃ p x y : ℝ, 0 ≤ p ∧ IsEq v k p x y ∧ z = profit p x y}

noncomputable def lambertW (a : ℝ) : ℝ :=
  by classical exact if h : ∃ w : ℝ, -1 ≤ w ∧ w * Real.exp w = a then Classical.choose h else 0

noncomputable def R (a : ℝ) : ℝ :=
  lambertW (-a * Real.exp (-a))

noncomputable def A (v k p : ℝ) : ℝ :=
  -(v - p - k + k) * Real.exp (-(v - p - k) + k / (v - p - k) * R (v - p - k))

noncomputable def Wk (k : ℝ) : ℝ :=
  lambertW (-(k + 1) * Real.exp (-(k + 1)))

noncomputable def f (k v : ℝ) : ℝ :=
  (1 - v / (k + 1)) * Wk k - Real.log (v - k)

noncomputable def vf (k : ℝ) : ℝ :=
  by classical exact if h : ∃ v : ℝ, k + 1 < v ∧ f k v = 0 then Classical.choose h else 0

noncomputable def vOf (k : ℝ) : ℝ :=
  by classical exact if h : ∃ v : ℝ, 1 < v ∧ k = v - Real.log v / (1 - 1 / v)
    then Classical.choose h else 0

noncomputable def p2 (v : ℝ) : ℝ := v - Real.log v / (1 - 1 / v)
noncomputable def p3 (v k : ℝ) : ℝ := v - k - 1
noncomputable def p4 (v k : ℝ) : ℝ :=
  v - k - Real.log (v - k) / (1 - 1 / (v - k))
noncomputable def pi2 (v : ℝ) : ℝ := v - 1 - Real.log v
noncomputable def pi3 (v k : ℝ) : ℝ :=
  (v - k - 1) * (1 - Real.exp (-(Wk k + k + 1)))
noncomputable def pi4 (v k : ℝ) : ℝ := v - k - 1 - Real.log (v - k)

end AdvanceSales.Pricing


