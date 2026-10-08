-- Prove2me | Definitions.Def_ZipkinLostSales_Variability_Model
-- name    : ZipkinLostSales_Variability_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T19:24:31.665377+00:00
-- url     : https://prove2.me/theorems/62734ad5-3eaa-4c96-9661-6d6bc95426e5
-- title:
--   §2–§3, (1)–(5), pp. 937–939: the lost-sales recursion in the transformed state v, with the demand law μ as a parameter
-- statement:
--   This file sets up the single-item, periodic-review inventory model with lost sales of Zipkin (2008), in the transformed state of §3, with the law of demand kept as an explicit parameter so that the parametric analysis of §5 can compare different demand distributions.
--
--   **Data.** The order lead time is a positive integer $L$. The cost factors are the unit procurement cost $c$, the unit holding cost $\hat h$, the unit lost-sales penalty $p$, and the discount factor $\gamma$. One period's demand $d$ has law $\mu$, a measure on $\mathbb R$; the data are stationary and the demands are independent, so the same $\mu$ is used in every period.
--
--   **State space.** A state is a vector $v=(v_0,\dots,v_{L-1})\in\mathbb R^L$, and we use the convention $v_L=0$. The state space is
--   $$V=\{v\in\mathbb R^L:\ v_0\ge v_1\ge\dots\ge v_{L-1}\ge 0\},$$
--   the nonnegative vectors with nonincreasing components (equivalently $Jv\ge 0$ for the upper-triangular difference matrix $J$). Here $v_l$ is the sum of the inventory on hand and the orders arriving $l$ or more periods hence, so $v_0-v_1$ is the inventory on hand.
--
--   **Transition.** The action is $\zeta=-z\le 0$, where $z\ge0$ is the order quantity. Given the state $v$, the action $\zeta$ and the demand $d$, the next state is
--   $$v_+=\big([v_0-v_1-d]^++v_1,\ v_2,\ \dots,\ v_{L-1},\ 0\big)-\zeta e,$$
--   where $e$ is the vector of ones.
--
--   **Costs.** The end-of-period holding-penalty cost is $\hat q(u)=\hat h u^++p u^-$, and the expected one-period cost given on-hand inventory $y$ is $\hat q^0(y)=E[\hat q(y-d)]$, with $d\sim\mu$.
--
--   **Optimal costs.** Let $k$ be the number of periods to go. The optimal cost functions are defined by $\bar f(v;\mu)=0$ with $k=0$ periods to go (condition (2)), and, writing $\bar f_{t+1}$ for the cost with $k$ periods to go and $\bar f_t$, $\bar g_t$ for the period with $k+1$ periods to go,
--   $$\bar g_t(v,\zeta;\mu)=-\gamma^L c\zeta+\hat q^0(v_0-v_1)+\gamma\,E\big[\bar f_{t+1}(v_+;\mu)\big],\qquad \bar f_t(v;\mu)=\inf_{\zeta\le0}\bar g_t(v,\zeta;\mu).$$
--   This is recursion (1) written in the state $v$, since $\bar f_t(v)=\hat f_t(Jv)$ and $\bar g_t(v,\zeta)=\hat g_t(Jv,-\zeta)$.
--
--   **Program (4).** For a continuation function $F$ on $V$ (standing for $\bar f_{t+1}$), a demand $d$, a state $v$ and an action $\zeta$, let
--   $$\psi(v_+,v,\zeta)=\hat h(v_+-v_1)+p(v_+-v_0+d)+\gamma F\big[(v_+,v_2,\dots,v_{L-1},0)-\zeta e\big],$$
--   $$\bar\kappa(v,\zeta\mid d)=\inf\big\{\psi(v_+,v,\zeta):\ -d\le v_+-v_0\le 0,\ v_+-v_1\ge0\big\}.$$
--   Program (3) of the paper is the same program before the substitution $v_+=w+v_1$, where $w$ is the inventory carried over and $a=v_0-v_1-w$ the sales.
--
--   These are the objects of the paper's §5: the optimal cost $\bar f_t(v;\phi)$ there is $\bar f_t(v;\mu_\phi)$ here, for a demand law $\mu_\phi$ depending on a parameter $\phi$.
--
--   **Formalization Note** States are `Fin L → ℝ`, indexed from $0$ as in the paper, and `vext v l` returns $v_l$ for $l<L$ and $0$ otherwise (the paper's $v_L=0$). Time is indexed by the number of periods to go $k$ (the paper's $t=T+L+1-k$), because the data are stationary: `fbar … μ 0 = 0` is (2), `gbar … μ k` is $\bar g_t$ with continuation `fbar … μ k`, and `fbar … μ (k+1) v` is the infimum of `gbar … μ k v ζ` over $\zeta\le0$; so the paper's "for all $t$" is "for all $k$". The paper's "min" is an infimum over $\zeta\in(-\infty,0]$ (and over the interval $[\max(v_0-d,v_1),v_0]$ in $\bar\kappa$); Lean's infimum of a set that is not bounded below, or of the empty set, is $0$, so these infima are genuine only when the terms are bounded below, which holds under the nonnegative costs and nonnegative demand assumed by every theorem of the mission, and the interval in $\bar\kappa$ is nonempty only for $v\in V$, $d\ge0$. Expectations are Bochner integrals. No hypothesis is bundled into the definitions: the conditions on costs and demand are stated in each theorem. The file also records two definitional unfolding lemmas for $\bar f$.
-- source:
--   Zipkin, On the Structure of Lost-Sales Inventory Models, Oper. Res. 56 (2008), pp. 937–939 (PDF pp. 2–4): §2 model, q̂, q̂⁰, recursion (1), terminal condition (2); §3 state space V, transition of v, f̄_t, ḡ_t; programs (3)–(5); §5 p. 941 (PDF p. 6) for the dependence on the demand law

import Mathlib
import Definitions.Def_ZipkinLostSales_LNatural_Model

namespace ZipkinLostSales.Variability

open MeasureTheory

/-!
# Zipkin (2008), §2–§3: the lost-sales recursion in the transformed state `v`, with the demand
law as a parameter

Conventions (Zipkin, *On the Structure of Lost-Sales Inventory Models*, Oper. Res. 56 (2008),
pp. 937–939):

* `L : ℕ` is the lead time; states are `v : Fin L → ℝ`, indexed `0, …, L-1` as in the paper, and
  `vext v l` extends `v` by the paper's convention `v_L = 0` (and `0` beyond).
* Costs: `c` (procurement), `hh` (= ĥ, holding), `p` (lost-sales penalty), `γ` (discount factor).
* `μ : Measure ℝ` is the law of one period's demand `d` (data are stationary and the demands are
  independent, so one law serves every period). Every object below that involves an expectation
  takes `μ` as an explicit argument, so that the paper's `f̄_t(v; φ)` of §5 is `fbar … (μ φ) k v`.
* Time is indexed by the number of periods to go `k : ℕ`: `fbar … 0 = 0` is (2), and `gbar … k`
  is the paper's `ḡ_t` for the period `t` with `k + 1` periods to go, whose continuation is
  `fbar … k` (the paper's `f̄_{t+1}`); `fbar … (k+1) v = ⨅_{ζ ≤ 0} ZipkinLostSales.LNatural.gbar … k v ζ` is (1). By
  stationarity "for all t" is "for all k".
* The paper's "min" is the infimum `⨅ ζ : Set.Iic (0:ℝ)`. Under nonnegative costs and nonnegative
  demand every term of `gbar` is `≥ 0`, so the infimum is over a set bounded below and is not
  Lean's junk value; this is not proved here.
-/

/-- `fbar … (k+1)` unfolds to the infimum of `gbar … k` over `ζ ≤ 0` (definitional). -/
theorem fbar_succ {L : ℕ} (c hh p γ : ℝ) (μ : Measure ℝ) (k : ℕ) (v : Fin L → ℝ) :
    ZipkinLostSales.LNatural.fbar c hh p γ μ (k + 1) v = ⨅ ζ : Set.Iic (0 : ℝ), ZipkinLostSales.LNatural.gbar c hh p γ μ k v ζ := rfl

/-- `fbar … 0 = 0`, condition (2) (definitional). -/
theorem fbar_zero {L : ℕ} (c hh p γ : ℝ) (μ : Measure ℝ) (v : Fin L → ℝ) :
    ZipkinLostSales.LNatural.fbar c hh p γ μ 0 v = 0 := rfl

end ZipkinLostSales.Variability


