-- Prove2me | Definitions.Def_ZipkinLostSales_Bounds_Model
-- name    : ZipkinLostSales_Bounds_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T19:24:06.557569+00:00
-- url     : https://prove2.me/theorems/9459f4c0-5a4e-4eb3-9f7d-fd272c2159c8
-- title:
--   §2–§4, pp. 937–938, 940: the re-accounted lost-sales recursion f_t, the cost q(v, z), the fractiles (6), V(s̄) and Z(s̄)
-- statement:
--   This file sets up the lost-sales inventory model of Zipkin (2008) in the re-accounted form of its §4, together with the bounds of Karlin–Scarf and Morton.
--
--   **Model.** A single item is reviewed in discrete periods with a lead time $L\ge 1$ (an integer). In each period the order due arrives, a new order $z\ge 0$ is placed, and demand occurs; unmet demand is lost. Demands are independent, identically distributed and nonnegative, with law $\mu$ on $\mathbb R$. The cost factors are the unit procurement cost $c$, the unit holding cost $\hat h$, the unit lost-sales penalty $p$ and the discount factor $\gamma$; set $h=\hat h-\gamma c$. The **state** is $v=(v_0,\dots,v_{L-1})$, where $v_l=\sum_{k\ge l}x_k$ is a partial sum of the pipeline $x=(x_0,\dots,x_{L-1})$, $x_0=y$ being the inventory on hand; equivalently $x_l=v_l-v_{l+1}$ with $v_L=0$. The state space is the cone
--   $$V=\{v\in\mathbb R^L:\ v_0\ge v_1\ge\dots\ge v_{L-1}\ge 0\}.$$
--   Given demand $d$ and order $z$, the next state is
--   $$v_+=\big([v_0-v_1-d]^+ + v_1,\ v_2,\ \dots,\ v_{L-1},\ 0\big)+z\,e .$$
--
--   **The inventory when the order arrives.** With demands $d_t,\dots,d_{t+L-1}$ and on-hand dynamics $y_{t+j+1}=[y_{t+j}-d_{t+j}]^+ + x_j$ (the order placed at $t$ arriving as $x_L=z$), $y_{+L}=y_{t+L}$ is the inventory on hand when the current order arrives; it depends only on $v$, $z$ and these $L$ demands.
--
--   **Costs and recursion.** Let
--   $$q^0(y)=cy+h\,E\big[[y-d]^+\big]+p\,E\big[[y-d]^-\big],\qquad q(v,z)=\gamma^L E\big[q^0(y_{+L})\big],$$
--   and define the optimal costs $f_t$ and the function $g_t$ by
--   $$g_t(v,z)=q(v,z)+\gamma E\big[f_{t+1}(v_+)\big],\qquad f_t(v)=\inf_{z\ge0} g_t(v,z),\qquad f_{T+1}=0 .$$
--   The **optimal policy** $\bar z_t(v)$ is the smallest minimizer of $g_t(v,\cdot)$ over $z\ge 0$.
--
--   **Bounds.** Let $\bar\theta=(c+h)/(p+h)$, and let $d_{[l,L]}$ be the sum of the demands of periods $t+l,\dots,t+L$ ($L-l+1$ independent demands). The fractiles are
--   $$\bar s_l=\min\{s:\ \Pr\{d_{[l,L]}>s\}\le\bar\theta\},\qquad l=0,\dots,L. \tag{6}$$
--   Let $V(\bar s)=\{v\in V: v_l\le \bar s_l,\ l=0,\dots,L-1\}$, and let $Z(\bar s)$ be the set of policies $z(\cdot)$ with $z(v)=0$ for $v\notin V(\bar s)$, and, for $v\in V(\bar s)$, $z(v)\le\bar s_L$ and $v_l+z(v)\le\bar s_l$ for $l=0,\dots,L-1$.
--
--   **Standing assumptions.** $\mu$ is a probability measure on $[0,\infty)$ with finite mean; $c,\hat h,p\ge0$; $0<\gamma\le1$; and $0<c+h<p+h$ (§4's assumption, under which $0<\bar\theta<1$).
--
--   These objects are shared by every statement of the mission: the last-period bound (Lemma 6), the monotonicity of the optimal costs (Lemma 7, Theorem 8) and the bounds for every period (Corollary 9).
--
--   **Formalization Note** Periods are indexed by the number of periods to go $k=T+1-t$: `fB M 0` is $f_{T+1}=0$, `gB M k` is $g_{T-k}$ and `fB M (k+1)` is $f_{T-k}$; by stationarity "for all $t\le T$" becomes "for all $k$", and $t=T$ is $k=0$. Vectors are indexed $0,\dots,L-1$ (`Fin L`) with the paper's $v_L=0$ (`vext`), and $\bar s$ by $0,\dots,L$ (`Fin (L+1)`). The paper's $\min_{z\ge0}$ is the infimum over $z\ge0$; under the assumptions every $q(v,z)$ with $z\ge 0$ is nonnegative, so this infimum is genuine. The minimum in (6) is an `sInf`: under the assumptions the set is nonempty and bounded below, and the infimum is attained. "The optimal policy" is the least minimizer, stated with `IsLeast` ("In case of a tie, choose the smallest optimal z", p. 938). $y_{+L}$ is defined by iterating the on-hand dynamics, not by (7), which is a theorem. The data are bundled in `Data` and the assumptions in `Assumptions`; the finite mean of demand and the readings of "unit cost" and "discount rate" as $c,\hat h,p\ge0$, $\gamma\in(0,1]$ are added (the paper leaves them implicit). The paper derives §4's recursion from §2's by "some algebra"; that identification is not formalized, and everything is stated for §4's recursion.
-- source:
--   Zipkin, On the Structure of Lost-Sales Inventory Models, Oper. Res. 56 (2008), pp. 937–938 (§2–§3: events, costs, V, transition) and p. 940 (§4: recursion for f_t, q(v, z), q⁰, h, θ̄, (6), V(s̄), Z(s̄)); PDF pp. 2–3, 5; DOI 10.1287/opre.1070.0482

import Mathlib
import Definitions.Def_ZipkinLostSales_LNatural_Model

namespace ZipkinLostSales.Bounds

open MeasureTheory

/-!
# Zipkin (2008), §2–§4: the re-accounted lost-sales recursion of §4 and the Karlin–Scarf–Morton
bounds `Z(s̄)`

Source: P. Zipkin, *On the Structure of Lost-Sales Inventory Models*, Oper. Res. 56 (2008),
pp. 937–938 (§2–§3: events, costs, the cone `V`, the transition of `v`) and p. 940 (§4: the
recursion for `f_t`, the cost `q(v, z)`, the fractiles (6), `V(s̄)` and `Z(s̄)`).

Conventions.

* `L : ℕ` is the lead time; states are `v : Fin L → ℝ`, indexed `0, …, L-1` as in the paper, and
  `vext v l` extends `v` by the paper's convention `v_L = 0` (and `0` beyond).
* `M : Data` carries the demand law `μ` of one period's demand (data are stationary and the demands
  independent, so one law serves every period) and the cost factors `c` (procurement), `hh` (= ĥ,
  holding), `p` (lost-sales penalty), `γ` (discount factor). The hypotheses are bundled separately
  in `Assumptions`.
* Time is indexed by the number of periods to go `k : ℕ` (`k = T + 1 − t`): `fB M 0 = 0` is
  `f_{T+1} = 0`, `gB M k` is the paper's `g_t` with `t = T − k` (its continuation is `fB M k`, the
  paper's `f_{t+1}`), and `fB M (k+1) = inf_{z ≥ 0} gB M k` is `f_t`. "For all t ≤ T" is "for all
  k". "t = T" is `k = 0`, where `gB M 0 = q`.
* The paper's `min_{z ≥ 0}` is the infimum `⨅ z : Set.Ici (0:ℝ)`. Under `Assumptions` every
  `q(v, z)` with `z ≥ 0` is `≥ 0` (because `y_{+L} ≥ z ≥ 0` and `c ≥ 0`, `c + h > 0`, `p ≥ 0`),
  hence so is every value function, and the infimum is over a set bounded below, not Lean's junk
  value. This is not proved here.
* "The optimal policy" `z̄_t(v)` is the least minimizer ("In case of a tie, choose the smallest
  optimal z", p. 938): `IsOptOrder`, stated with `IsLeast`, not with `sInf` of the argmin set.
* The paper obtains §4's recursion from §2's by "some algebra" (p. 940); that identification is not
  formalized: everything here is stated for §4's recursion.
-/

/-- The data of the model: the law `μ` of one period's demand and the cost factors
`c` (unit procurement cost), `hh` (= ĥ, unit holding cost), `p` (unit lost-sales penalty) and
`γ` (discount factor) (pp. 937–938). -/
structure Data where
  μ : Measure ℝ
  c : ℝ
  hh : ℝ
  p : ℝ
  γ : ℝ

/-- `h = ĥ − γc` (p. 940). It may be negative. -/
def Data.h (M : Data) : ℝ := M.hh - M.γ * M.c

/-- The standing assumptions for lead time `L` and data `M`:
* `L` is a positive integer (p. 937);
* the demands are independent, identically distributed (stationary data, p. 938) with law `μ`, a
  probability measure, nonnegative (p. 937) and with finite mean (added: it makes `q⁰` finite);
* the cost factors are nonnegative and `γ ∈ (0, 1]` (the reading of "unit cost", "discount rate",
  p. 938);
* `0 < c + h < p + h`, §4's own assumption (p. 940). -/
structure Assumptions (L : ℕ) (M : Data) : Prop where
  hL : 0 < L
  prob : IsProbabilityMeasure M.μ
  demand_nonneg : M.μ (Set.Iio 0) = 0
  integrable : Integrable id M.μ
  hc : 0 ≤ M.c
  hhh : 0 ≤ M.hh
  hp : 0 ≤ M.p
  hγ0 : 0 < M.γ
  hγ1 : M.γ ≤ 1
  hch : 0 < M.c + M.h
  hph : M.c + M.h < M.p + M.h

/-- The transition of the transformed state with order `z` (p. 938):
`v₊ = ([v₀ − v₁ − d]⁺ + v₁, v₂, …, v_{L−1}, 0) + ze`. -/
def nextZ {L : ℕ} (v : Fin L → ℝ) (d z : ℝ) : Fin L → ℝ := fun l =>
  (if (l : ℕ) = 0 then max (ZipkinLostSales.LNatural.vext v 0 - ZipkinLostSales.LNatural.vext v 1 - d) 0 else 0) + ZipkinLostSales.LNatural.vext v ((l : ℕ) + 1) + z

/-- The pipeline `x_l = v_l − v_{l+1}` (p. 938, `v_l = Σ_{k ≥ l} x_k`); `x_0 = y` is the inventory
on hand. -/
def xext {L : ℕ} (v : Fin L → ℝ) (l : ℕ) : ℝ := ZipkinLostSales.LNatural.vext v l - ZipkinLostSales.LNatural.vext v (l + 1)

/-- What arrives in period `t + j`, seen from period `t` with state `v` and current order `z`:
`x_j` for `j < L` (`x_0 = y_t`), and the current order `z` at `j = L`. -/
def arrival {L : ℕ} (v : Fin L → ℝ) (z : ℝ) (j : ℕ) : ℝ := if j < L then xext v j else z

/-- On-hand inventory `y_{t+j}` (after the arrival due at `t + j`), from the dynamics of p. 937
`y_{t+1} = [y_t − d_t]⁺ + x_{1t}`, given the state `v`, the order `z` and the demands
`D j = d_{t+j}`, `j = 0, …, L − 1` (`vext D j`). Only `j ≤ L` is meaningful. -/
def onHand {L : ℕ} (v : Fin L → ℝ) (z : ℝ) (D : Fin L → ℝ) : ℕ → ℝ
  | 0 => arrival v z 0
  | j + 1 => max (onHand v z D j - ZipkinLostSales.LNatural.vext D j) 0 + arrival v z (j + 1)

/-- `y_{+L} = y_{t+L}`, the inventory on hand when the current order `z` arrives (p. 940). It
depends only on `v`, `z` and the demands of periods `t, …, t + L − 1`. -/
def yPlusL {L : ℕ} (v : Fin L → ℝ) (z : ℝ) (D : Fin L → ℝ) : ℝ := onHand v z D L

/-- `q⁰(y) = cy + hE[[y − d]⁺] + pE[[y − d]⁻]` with `h = ĥ − γc` (p. 940); `[u]⁻ = max (−u) 0`. -/
noncomputable def q0 (M : Data) (y : ℝ) : ℝ :=
  M.c * y + M.h * ∫ d, max (y - d) 0 ∂M.μ + M.p * ∫ d, max (d - y) 0 ∂M.μ

/-- `q(v, z) = γ^L E[q⁰(y_{+L})]` (p. 940): the expectation is over the i.i.d. demands of periods
`t, …, t + L − 1`; the demand of period `t + L` is the one inside `q⁰`. -/
noncomputable def q {L : ℕ} (M : Data) (v : Fin L → ℝ) (z : ℝ) : ℝ :=
  M.γ ^ L * ∫ D, q0 M (yPlusL v z D) ∂(Measure.pi fun _ : Fin L => M.μ)

/-- One step of §4's recursion for a continuation `F` (standing for `f_{t+1}`):
`q(v, z) + γE[F(v₊)]` (p. 940). -/
noncomputable def gstep {L : ℕ} (M : Data) (F : (Fin L → ℝ) → ℝ) (v : Fin L → ℝ) (z : ℝ) : ℝ :=
  q M v z + M.γ * ∫ d, F (nextZ v d z) ∂M.μ

/-- The optimal cost `f_t(v)` of §4 with `k` periods to go (`k = T + 1 − t`, p. 940):
`fB M 0 = 0` is `f_{T+1} = 0`, and `fB M (k+1) v = inf_{z ≥ 0} {q(v, z) + γE[fB M k (v₊)]}`. -/
noncomputable def fB {L : ℕ} (M : Data) : ℕ → (Fin L → ℝ) → ℝ
  | 0 => fun _ => 0
  | k + 1 => fun v => ⨅ z : Set.Ici (0 : ℝ), gstep M (fB M k) v z

/-- `g_t(v, z) = q(v, z) + γE[f_{t+1}(v₊)]` with `t = T − k` (p. 940); `gB M 0 = q` up to the zero
continuation. -/
noncomputable def gB {L : ℕ} (M : Data) (k : ℕ) (v : Fin L → ℝ) (z : ℝ) : ℝ :=
  gstep M (fB M k) v z

/-- `z` is `z̄_t(v)` (`t = T − k`): the smallest minimizer of `gB M k v` over `z ≥ 0`
("In case of a tie, choose the smallest optimal z", p. 938). -/
def IsOptOrder {L : ℕ} (M : Data) (k : ℕ) (v : Fin L → ℝ) (z : ℝ) : Prop :=
  IsLeast {z : ℝ | 0 ≤ z ∧ ∀ z' : ℝ, 0 ≤ z' → gB M k v z ≤ gB M k v z'} z

/-- `θ̄ = (c + h)/(p + h)` (p. 940). -/
noncomputable def θbar (M : Data) : ℝ := (M.c + M.h) / (M.p + M.h)

/-- The fractiles (6) (p. 940): `s̄_l = min {s : Pr{d_{[l,L]} > s} ≤ θ̄}`, `l = 0, …, L`, where
`d_{[l,L]}` is the sum of the demands of periods `t + l, …, t + L`, i.e. of `L − l + 1` i.i.d.
demands (coordinates `j ≥ l` of `L + 1` i.i.d. demands). Under `Assumptions`, `0 < θ̄ < 1` and
demand is `≥ 0`, so the set is nonempty and bounded below and its `sInf` is the paper's minimum
(attained by right-continuity of the tail); it is not Lean's junk value. -/
noncomputable def sbar (L : ℕ) (M : Data) (l : Fin (L + 1)) : ℝ :=
  sInf {s : ℝ | ((Measure.pi fun _ : Fin (L + 1) => M.μ)
    {D | s < ∑ j ∈ Finset.Ici l, D j}).toReal ≤ θbar M}

/-- `V(s̄) = {v ∈ ZipkinLostSales.LNatural.V : v_l ≤ s̄_l, l = 0, …, L − 1}` (p. 940). -/
def Vs (L : ℕ) (M : Data) : Set (Fin L → ℝ) :=
  {v | v ∈ ZipkinLostSales.LNatural.V L ∧ ∀ l : Fin L, v l ≤ sbar L M l.castSucc}

/-- The bounds of `Z(s̄)` at the state `v` for the order `z` (p. 940): `z = 0` if `v ∉ ZipkinLostSales.LNatural.V(s̄)`, and
`z ≤ s̄_L`, `v_l + z ≤ s̄_l` (`l = 0, …, L − 1`) if `v ∈ ZipkinLostSales.LNatural.V(s̄)`. A policy `z(·)` is in `Z(s̄)` iff
`InZ L M v (z v)` for every `v ∈ ZipkinLostSales.LNatural.V`. -/
def InZ (L : ℕ) (M : Data) (v : Fin L → ℝ) (z : ℝ) : Prop :=
  (v ∉ Vs L M → z = 0) ∧
    (v ∈ Vs L M → z ≤ sbar L M (Fin.last L) ∧ ∀ l : Fin L, v l + z ≤ sbar L M l.castSucc)

/-- `fB M (k+1)` unfolds to the infimum of `gB M k` over `z ≥ 0` (definitional). -/
theorem fB_succ {L : ℕ} (M : Data) (k : ℕ) (v : Fin L → ℝ) :
    fB M (k + 1) v = ⨅ z : Set.Ici (0 : ℝ), gB M k v z := rfl

/-- `fB M 0 = 0`, i.e. `f_{T+1} = 0` (definitional). -/
theorem fB_zero {L : ℕ} (M : Data) (v : Fin L → ℝ) : fB M 0 v = 0 := rfl

end ZipkinLostSales.Bounds


