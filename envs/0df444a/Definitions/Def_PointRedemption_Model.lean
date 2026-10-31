-- Prove2me | Definitions.Def_PointRedemption_Model
-- name    : PointRedemption_Model
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:12:50.569933+00:00
-- url     : https://prove2.me/theorems/26ee446b-1663-40d4-a755-f74cc391b49b
-- title:
--   The point-redemption pricing model: parameters, $\bar F$, $\bar G$, $I(p)$, $J_t(p,y)$ (1), $V_t(y)$, $\Delta_t(y)$, the blackout objective (3), A1–A3 and regularity
-- statement:
--   This module defines the dynamic pricing model with point redemption of Chung, Ahn and Chun (§3.1–§3.2).
--
--   **Setting** (pp. 7–12). A seller has $y$ units and $t$ periods to go. In each period one consumer arrives with probability $\lambda\in(0,1)$. She has a reservation price $V$ with distribution $F$ and density $f$, and values one point at $\Theta\ge 0$ with distribution $G$ and density $g$; $V$, $\Theta$ and the point balance are independent. With probability $\bar\beta\in[0,1]$ she has at least the point requirement $q>0$ (a *reward consumer*); write $\beta=1-\bar\beta$. A cash sale earns the price $p$, a reward sale earns the reimbursement $R\ge 0$. Write $\bar F=1-F$ and $\bar G=1-G$.
--
--   **Derived quantities.**
--
--   1. The point-purchase probability of a reward consumer, $I(p)=\int_0^{p/q}\bar F(qx)\,dG(x)$.
--   2. The optimality equations (1): $V_0(y)=0$, $V_t(0)=0$, and for $t\ge1$, $y\ge1$, $V_t(y)=\max_{p\ge0}J_t(p,y)$ with
--   $$\begin{aligned}J_t(p,y)={}&\lambda\bar\beta\Big[\bar F(p)\bar G(p/q)\big(p+V_{t-1}(y-1)\big)+I(p)\big(R+V_{t-1}(y-1)\big)+\big(1-\bar F(p)\bar G(p/q)-I(p)\big)V_{t-1}(y)\Big]\\&+\lambda\beta\Big[\bar F(p)\big(p+V_{t-1}(y-1)\big)+F(p)V_{t-1}(y)\Big]+(1-\lambda)V_{t-1}(y).\end{aligned}$$
--   3. The marginal value of inventory $\Delta_t(y)=V_t(y)-V_t(y-1)$.
--   4. The blackout objective of (3): $J^c_t(p,y)=\lambda\bar F(p)\big(p+V_{t-1}(y-1)\big)+\big(1-\lambda\bar F(p)\big)V_{t-1}(y)$, maximized over all real $p$; its maximizers are the one-period blackout prices $p^c_t(y)$.
--
--   **Assumptions of Theorem 1** (p. 13).
--
--   1. A1: $F$ and $G$ have an increasing failure rate.
--   2. A2: for every $p\ge0$ with $\bar F(p)>0$, $\bar G(p/q)>0$ and $\dfrac{g(p/q)}{q\,\bar G(p/q)}\le\dfrac{f(p)}{\bar F(p)}$.
--   3. A3: $p\mapsto \dfrac{f(p)/\bar F(p)}{(\bar\beta g(p/q)/q)/(1-\bar\beta G(p/q))}$ is non-decreasing on $\{p>0:\bar F(p)>0,\ g(p/q)>0\}$.
--   4. Regularity: $f$ is differentiable at every $p>0$ with $\bar F(p)>0$, and $g$ at every $x>0$ with $\bar G(x)>0$.
--
--   These objects carry every statement of the mission: the marginal-value form (2), the derivative (7), Theorem 1, the blackout first-order condition (22) and Proposition 1.
--
--   **Formalization Note** `lam` stands for $\lambda$. The laws are probability measures `μV`, `μΘ` equal to `volume.withDensity` of the nonnegative densities `f`, `g`; $\Theta\ge0$ is `μΘ (Iio 0) = 0`. $\bar F$, $\bar G$ and the IFR property are the published `LariviereIGFR.Char.survival` and `IsIFR`. $I(p)$ is the integral of $x\mapsto\bar F(qx)$ against `μΘ` over $[0,p/q]$ (zero for $p<0$). `J t p y` uses the continuation value `V (t-1)`; statements use it for $t\ge1$, $y\ge1$. $V_t(y)$ is the supremum `⨆` over $p\in[0,\infty)$ of $J_t(p,y)$ (that it is attained is part of Theorem 1). A2 carries the factor $1/q$ of the hazard of $q\Theta$ and the clause $\bar G(p/q)>0$, so that Lean's $x/0=0$ cannot make it hold where the paper's hazard is $+\infty$. Optimal and blackout prices are never defined as functions: statements quantify over maximizers.
-- source:
--   Chung–Ahn–Chun, Dynamic Pricing with Point Redemption, SSRN 3426903 (KAIST WP KCB-WP-2019-013); MSOM (2022), doi:10.1287/msom.2021.1067, §3.1–§3.2 pp. 7–12 (PDF 8–13): model p. 7–8, Lemma 1 p. 9 (I(p)), optimality equations (1) p. 12, Δ_t(y) p. 12; A1–A3 Theorem 1 p. 13 (PDF 14); blackout problem (3) p. 14 (PDF 15); f′, g′ in (8) App. p. 1 (PDF 36)

import Mathlib
import Definitions.Def_LariviereIGFR_Char_Setting

namespace PointRedemption

open MeasureTheory ProbabilityTheory LariviereIGFR.Char

/-- **Parameters of the point-redemption pricing model**, Chung–Ahn–Chun, *Dynamic Pricing with
Point Redemption*, SSRN 3426903 (KAIST WP KCB-WP-2019-013); MSOM (2022),
doi:10.1287/msom.2021.1067, §3.1–§3.2, pp. 7–12 (PDF 8–13).

* `lam` is the arrival probability `λ ∈ (0,1)` of one consumer per period (p. 7).
* `q > 0` is the fixed point requirement; `R` is the reimbursement per reward sale (p. 7).
* `βbar` is `β̄(q)`, the fraction of reward consumers at the fixed `q` (p. 8); `β = 1 − β̄`.
* `μV` is the law of the reservation price `V`, with density `f` (p. 7).
* `μΘ` is the law of the perceived point value `Θ ≥ 0`, with density `g` (p. 8).

**Formalization Note.** `lam` stands for `λ`, which is reserved in Lean. At the fixed `q` the
paper writes `β`, `β̄` for `β(q)`, `β̄(q)` (p. 11), so `βbar` is a number in `[0,1]`. Each law is a
probability measure equal to `volume.withDensity (ofReal ∘ density)` of a nonnegative density.
`Θ ≥ 0` is `μΘ (Iio 0) = 0`; `V` is not restricted in sign, as in the paper. `R ≥ 0` is a reading
(a reimbursement is revenue). The independence of `V`, `W`, `Θ` (p. 8) is built into formula
(1), which multiplies their probabilities, so no joint law is modelled. -/
structure Params where
  lam : ℝ
  q : ℝ
  βbar : ℝ
  R : ℝ
  μV : Measure ℝ
  f : ℝ → ℝ
  μΘ : Measure ℝ
  g : ℝ → ℝ
  lam_pos : 0 < lam
  lam_lt_one : lam < 1
  q_pos : 0 < q
  βbar_nonneg : 0 ≤ βbar
  βbar_le_one : βbar ≤ 1
  R_nonneg : 0 ≤ R
  f_nonneg : ∀ x, 0 ≤ f x
  g_nonneg : ∀ x, 0 ≤ g x
  μV_isProb : IsProbabilityMeasure μV
  μΘ_isProb : IsProbabilityMeasure μΘ
  μV_eq : μV = volume.withDensity (fun x => ENNReal.ofReal (f x))
  μΘ_eq : μΘ = volume.withDensity (fun x => ENNReal.ofReal (g x))
  Θ_nonneg : μΘ (Set.Iio 0) = 0

namespace Params

variable (P : Params)

/-- `β = β(q) = 1 − β̄(q)`, the fraction of cash-only consumers (p. 8, p. 11). -/
def β : ℝ := 1 - P.βbar

/-- `F(p)`, the cdf of the reservation price (p. 7). -/
noncomputable def F (p : ℝ) : ℝ := cdf P.μV p

/-- `F̄(p) = 1 − F(p)` (p. 8), the published `LariviereIGFR.Char.survival`. -/
noncomputable def Fbar (p : ℝ) : ℝ := survival P.μV p

/-- `G(x)`, the cdf of the point value `Θ` (p. 8). -/
noncomputable def G (x : ℝ) : ℝ := cdf P.μΘ x

/-- `Ḡ(x) = 1 − G(x)`. -/
noncomputable def Gbar (x : ℝ) : ℝ := survival P.μΘ x

/-- The point-purchase probability of a reward consumer (Lemma 1, p. 9; inside (1), p. 12):
`I(p) = ∫_0^{p/q} F̄(qx) dG(x)`, the Stieltjes integral against the law of `Θ`.

**Formalization Note.** Written as the integral of `x ↦ F̄(qx)` against `μΘ` over `[0, p/q]`;
since `μΘ` has a density, this equals `∫_0^{p/q} F̄(qx) g(x) dx` and the endpoints carry no mass.
For `p < 0` the interval is empty and `I(p) = 0`. -/
noncomputable def I (p : ℝ) : ℝ := ∫ x in Set.Icc 0 (p / P.q), P.Fbar (P.q * x) ∂P.μΘ

/-- The right-hand side `J_t(p, y)` of the optimality equations (1), p. 12, with the
continuation value `W = V_{t−1}` passed as a function of the inventory:

`λβ̄[F̄(p)Ḡ(p/q)(p + W(y−1)) + I(p)(R + W(y−1)) + (1 − F̄(p)Ḡ(p/q) − I(p))W(y)]`
`+ λβ[F̄(p)(p + W(y−1)) + F(p)W(y)] + (1 − λ)W(y)`. -/
noncomputable def Jstep (W : ℕ → ℝ) (p : ℝ) (y : ℕ) : ℝ :=
  P.lam * P.βbar *
      (P.Fbar p * P.Gbar (p / P.q) * (p + W (y - 1)) + P.I p * (P.R + W (y - 1)) +
        (1 - P.Fbar p * P.Gbar (p / P.q) - P.I p) * W y) +
    P.lam * P.β * (P.Fbar p * (p + W (y - 1)) + P.F p * W y) +
    (1 - P.lam) * W y

/-- The value function `V_t(y)` of the optimality equations (1), p. 12: `V_0(y) = 0`,
`V_t(0) = 0`, and `V_t(y) = max_{p ≥ 0} J_t(p, y)` for `y > 0`, `t ≥ 1`.

**Formalization Note.** `t` is the number of periods to go; the horizon `T` only bounds `t`, so
`V` is defined for every `t`. The paper's `max` is the supremum `⨆` over `p ∈ [0, ∞)`; that it is
attained is part of Theorem 1. -/
noncomputable def V : ℕ → ℕ → ℝ
  | 0, _ => 0
  | _ + 1, 0 => 0
  | t + 1, y + 1 => ⨆ p : Set.Ici (0 : ℝ), P.Jstep (V t) (p : ℝ) (y + 1)

/-- `J_t(p, y)` of (1), p. 12: the period-`t` objective with continuation value `V_{t−1}`.
Used only for `t ≥ 1`, `y ≥ 1`. -/
noncomputable def J (t : ℕ) (p : ℝ) (y : ℕ) : ℝ := P.Jstep (P.V (t - 1)) p y

/-- The marginal value of inventory `Δ_t(y) = V_t(y) − V_t(y − 1)` (p. 12), for `y ≥ 1`. -/
noncomputable def Δ (t y : ℕ) : ℝ := P.V t y - P.V t (y - 1)

/-- The blackout objective of (3), p. 14:
`λF̄(p)(p + V_{t−1}(y−1)) + (1 − λF̄(p))V_{t−1}(y)`, maximized over all real `p` (as printed,
`max_p`). Its maximizers are the one-period blackout prices `p^c_t(y)`. -/
noncomputable def Jc (t : ℕ) (p : ℝ) (y : ℕ) : ℝ :=
  P.lam * P.Fbar p * (p + P.V (t - 1) (y - 1)) + (1 - P.lam * P.Fbar p) * P.V (t - 1) y

/-- **A1** (Theorem 1, p. 13): `F` and `G` have an increasing failure rate (the published
`LariviereIGFR.Char.IsIFR`: the hazard is weakly increasing on `{cdf < 1}`). -/
def A1 : Prop := IsIFR P.μV P.f ∧ IsIFR P.μΘ P.g

/-- **A2** (Theorem 1, p. 13), read with the hazard of the `q`-point worth `qΘ`: for every
`p ≥ 0` with `F̄(p) > 0`, `Ḡ(p/q) > 0` and `g(p/q)/(q Ḡ(p/q)) ≤ f(p)/F̄(p)`.

**Formalization Note.** The printed A2 omits the `1/q`; the proof (App. p. 2), Corollary 1 and
the paper's own examples use the hazard of `qΘ`. Where `Ḡ(p/q) = 0` that hazard is `+∞`, so the
inequality requires `Ḡ(p/q) > 0` (otherwise Lean's `x / 0 = 0` would make it hold vacuously). -/
def A2 : Prop :=
  ∀ p : ℝ, 0 ≤ p → 0 < P.Fbar p →
    0 < P.Gbar (p / P.q) ∧ P.g (p / P.q) / (P.q * P.Gbar (p / P.q)) ≤ P.f p / P.Fbar p

/-- The set of prices on which the ratio of A3 is a finite positive real:
`p > 0`, `F̄(p) > 0` and `g(p/q) > 0`. -/
def A3Dom : Set ℝ := {p | 0 < p ∧ 0 < P.Fbar p ∧ 0 < P.g (p / P.q)}

/-- **A3** (Theorem 1, p. 13): `(f(p)/F̄(p)) / ((β̄ g(p/q)/q)/(1 − β̄ G(p/q)))` is non-decreasing
in `p`, on the set `A3Dom` where it is a finite positive real. The constant factor `1/q` does not
affect monotonicity; it matches the derivative (21). -/
def A3 : Prop :=
  MonotoneOn
    (fun p => (P.f p / P.Fbar p) / ((P.βbar * P.g (p / P.q) / P.q) / (1 - P.βbar * P.G (p / P.q))))
    P.A3Dom

/-- Regularity of `f` (reading of the paper's use of `f′` in (8), App. p. 1): `f` is
differentiable at every `p > 0` with `F̄(p) > 0`. -/
def RegF : Prop := ∀ p : ℝ, 0 < p → 0 < P.Fbar p → DifferentiableAt ℝ P.f p

/-- Regularity of `g` (reading of the paper's use of `g′` in (8), App. p. 1): `g` is
differentiable at every `x > 0` with `Ḡ(x) > 0`. -/
def RegG : Prop := ∀ x : ℝ, 0 < x → 0 < P.Gbar x → DifferentiableAt ℝ P.g x

/-- Both densities are regular in the sense of `RegF` and `RegG`. -/
def Regular : Prop := P.RegF ∧ P.RegG

end Params

end PointRedemption


