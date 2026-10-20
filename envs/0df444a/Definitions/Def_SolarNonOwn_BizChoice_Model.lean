-- Prove2me | Definitions.Def_SolarNonOwn_BizChoice_Model
-- name    : SolarNonOwn_BizChoice_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T02:16:21.746486+00:00
-- url     : https://prove2.me/theorems/5f58d4c2-be29-4157-b3f5-93c10c9b863f
-- title:
--   §§3.4–3.7, pp. 9–13 — customer choices, adoption, generation and company profit
-- statement:
--   A solar power company posts a sales price $s$, a lease fee $l$, and a per-unit power purchase agreement price $p$. A customer has expected monthly generation $\eta$ and expected electricity demand $d$. The available choices are sale $S$, lease $L$, power purchase agreement $P$, and utility supply $U$. Their expected costs are
--
--   $$C_S=(1-\alpha)s+r(d-\eta)-\beta\eta,\quad C_L=l+r(d-\eta),\quad C_P=p\eta+r(d-\eta),\quad C_U=rd.$$
--
--   The customer chooses a cheapest option. The utility is chosen only when strictly cheaper than all solar options; solar ties use the fixed order $S,L,P$. Expected generation $\eta$ is uniform on $[0,g]$ and independent of a positive expected-demand law $h$. For option $i$, $N^i$ is its population share and $G^i$ is the population's total generation under it. The company's expected monthly profit is
--
--   $$\Pi=(s-c)N^S+\bigl(l-(1-\alpha)c\bigr)N^L+\beta G^L+(p+\beta-t)G^P-(1-\alpha)cN^P.$$
--
--   The sales-only benchmark uses the same customer costs with only $S$ and $U$ available, giving $\Pi_0(s)=(s-c)N_0^S(s)$. An offer is counted when its customer share is positive. These definitions make the equilibrium claim a statement about actual customer choices.
--
--   **Formalization Note** The demand law is an arbitrary probability measure supported on $(0,\infty)$; the paper gives it a density, but none of these results uses that density. Population shares use finite-measure conversion to real numbers. The $N^i\ge0$ constraints in (1) hold by construction. The tie convention makes the paper's $p=r$ allocation explicit. `ModelAssumptions` collects the assumptions of §3: $\alpha>0$, $\beta>0$ (p. 8), $0<t<r$ (pp. 9–10), and $g>0$ for the uniform support (p. 12).
-- source:
--   Agrawal, Toktay & Yücel, Non-Ownership Business Models for Solar Energy, authors' manuscript of 18 Sep 2021 (MSOM, doi:10.1287/msom.2021.1049), pp. 9–13, §§3.4–3.7, equation (1); p. 14, Lemma 2

import Mathlib
import Definitions.Def_SolarNonOwn_BizChoice_Utility

noncomputable section
open MeasureTheory

namespace SolarNonOwn.BizChoice

structure Params where
  alpha : ℝ
  beta : ℝ
  r : ℝ
  t : ℝ
  g : ℝ

/-- Model assumptions of §§3.3–3.6, pp. 8–12: positive subsidies `α > 0`, `β > 0`
(p. 8), transaction cost `0 < t < r` (pp. 9–10), and generation support `[0, g]`
with `g > 0` (p. 12). -/
def ModelAssumptions (prm : Params) : Prop :=
  0 < prm.alpha ∧ 0 < prm.beta ∧ 0 < prm.t ∧ prm.t < prm.r ∧ 0 < prm.g

structure Prices where
  s : ℝ
  l : ℝ
  p : ℝ

inductive BizOpt where
  | S | L | P | U
  deriving DecidableEq

instance : Fintype BizOpt :=
  ⟨{.S, .L, .P, .U}, by intro i; cases i <;> simp⟩

/-- §§3.4–3.5, pp. 10–11: realized monthly cost at usage `q` and generation `n`. -/
def monthlyCost (prm : Params) (x : Prices) (q n : ℝ) : BizOpt → ℝ
  | .S => (1 - prm.alpha) * x.s + prm.r * (q - n) - prm.beta * n
  | .L => x.l + prm.r * (q - n)
  | .P => x.p * n + prm.r * (q - n)
  | .U => prm.r * q

/-- §3.5, p. 11: expected monthly customer costs, with `η = E[n]` and `d = E[q]`. -/
def cost (prm : Params) (x : Prices) (η d : ℝ) : BizOpt → ℝ
  | .S => (1 - prm.alpha) * x.s + prm.r * (d - η) - prm.beta * η
  | .L => x.l + prm.r * (d - η)
  | .P => x.p * η + prm.r * (d - η)
  | .U => prm.r * d

/-- §3.5 and Lemma 2: utility only wins a strict cost comparison; ties among solar
options use the fixed order S, L, P. -/
def choice (prm : Params) (x : Prices) (η d : ℝ) : BizOpt :=
  if cost prm x η d .U < cost prm x η d .S ∧
     cost prm x η d .U < cost prm x η d .L ∧
     cost prm x η d .U < cost prm x η d .P then .U
  else if cost prm x η d .S ≤ cost prm x η d .L ∧
          cost prm x η d .S ≤ cost prm x η d .P then .S
  else if cost prm x η d .L ≤ cost prm x η d .P then .L
  else .P

/-- §3.6, p. 12: uniform generation on `[0,g]` and an independent demand law. -/
def population (prm : Params) (h : Measure ℝ) : Measure (ℝ × ℝ) :=
  ((ENNReal.ofReal (1 / prm.g)) • volume.restrict (Set.Icc 0 prm.g)).prod h

/-- §3.7, pp. 12–13: population mass choosing an option. -/
def adoption (prm : Params) (h : Measure ℝ) (x : Prices) (i : BizOpt) : ℝ :=
  ((population prm h) {z | choice prm x z.1 z.2 = i}).toReal

/-- §3.7, pp. 12–13: total expected generation of customers choosing an option. -/
def generation (prm : Params) (h : Measure ℝ) (x : Prices) (i : BizOpt) : ℝ :=
  ∫ z in {z | choice prm x z.1 z.2 = i}, z.1 ∂population prm h

/-- Equation (1), p. 13, expressed directly using actual customer choices. -/
def profit (prm : Params) (h : Measure ℝ) (c : ℝ) (x : Prices) : ℝ :=
  (x.s - c) * adoption prm h x .S +
  (x.l - (1 - prm.alpha) * c) * adoption prm h x .L +
  prm.beta * generation prm h x .L +
  (x.p + prm.beta - prm.t) * generation prm h x .P -
  (1 - prm.alpha) * c * adoption prm h x .P

/-- Business models with positive adoption, as used in Proposition 1. -/
def offers (prm : Params) (h : Measure ℝ) (x : Prices) : Finset BizOpt :=
  Finset.univ.filter (fun i => i ≠ .U ∧ 0 < adoption prm h x i)

/-- Appendix A, p. OA1: customers in the sales-only benchmark. -/
def choice0 (prm : Params) (s η d : ℝ) : BizOpt :=
  if cost prm ⟨s, 0, 0⟩ η d .U < cost prm ⟨s, 0, 0⟩ η d .S then .U else .S

def adoption0 (prm : Params) (h : Measure ℝ) (s : ℝ) : ℝ :=
  ((population prm h) {z | choice0 prm s z.1 z.2 = .S}).toReal

/-- Appendix A, p. OA1: sales-only expected profit. -/
def profit0 (prm : Params) (h : Measure ℝ) (c s : ℝ) : ℝ :=
  (s - c) * adoption0 prm h s

end SolarNonOwn.BizChoice


