-- Prove2me | Definitions.Def_EcoOffset_Subgame_Model
-- name    : EcoOffset_Subgame_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T00:26:22.399987+00:00
-- url     : https://prove2.me/theorems/93d1f51f-5cab-4663-a82c-32c9931011a7
-- title:
--   §3, pp. 6–12; Online Supplement I, p. 1 — firm with abatement and offsets, eco-conscious demand (2), profit (3), best response, segment-optimal emission
-- statement:
--   This file fixes the model of Gao and Souza's subgame between a firm and its consumers, given the price $g$ of carbon offsets.
--
--   **Primitives.** There are $m$ consumers. A firm chooses a controllable emission level $e\in[0,\bar e]$ per unit of product, which determines a unit production cost $c(e)$ and a fixed cost $f(e)$; every unit also carries uncontrollable supply-chain emissions $e_o\ge 0$. The firm may offset $t\in[0,e+e_o]$ units of emissions per unit of product at the price $g$, and it discloses the **product carbon footprint**
--   $$\mathcal E = e+e_o-t.$$
--   A consumer with valuation $V$ and environmental disutility $\Xi$ has utility $u = V-\Xi\mathcal E-p$ at the price $p$. A share $\alpha\in[0,1]$ of consumers is eco-conscious ($\Xi=\xi>0$), the rest are eco-unconscious ($\Xi=0$). Within the eco-conscious group a share $\beta_c\in[0,1]$ has the high valuation $v_h$ and the rest the low valuation $v_l$; within the eco-unconscious group the high share is $\beta_u\in[0,1]$.
--
--   **Standing assumptions** (§3): $m>0$, $\bar e>0$, $e_o\ge0$, $\xi>0$, $\alpha,\beta_c,\beta_u\in[0,1]$, $0\le v_l$, $c(\bar e)<v_l<v_h$, and $c,f$ are twice continuously differentiable with $c'<0$, $c''>0$, $f'<0$, $f''>0$ on $[0,\bar e]$ and $f(\bar e)=0$.
--
--   **Demand and profit.** A consumer buys if and only if her utility is nonnegative, so the demand (2) is
--   $$d(p,e,t)=d_c+d_u=\alpha\beta_c m\,\mathbb 1\{u_{c,h}\ge0\}+\alpha(1-\beta_c)m\,\mathbb 1\{u_{c,l}\ge0\}+(1-\alpha)\beta_u m\,\mathbb 1\{u_{u,h}\ge0\}+(1-\alpha)(1-\beta_u)m\,\mathbb 1\{u_{u,l}\ge0\},$$
--   with $u_{c,h}=v_h-\xi\mathcal E-p$, $u_{c,l}=v_l-\xi\mathcal E-p$, $u_{u,h}=v_h-p$, $u_{u,l}=v_l-p$. The firm's profit (3) is
--   $$\pi(p,e,t\mid g)=(p-c(e)-gt)\,d(p,e,t)-f(e).$$
--   A **best response** to $g$ is a feasible $(p,e,t)$ (any real price $p$) that maximizes $\pi(\cdot\mid g)$ over all feasible decisions.
--
--   **Segment-optimal emission.** For a segment size $a$ and a marginal offset cost $x$, $e_{x,a}$ is the maximizer over $[0,\bar e]$ of $-(c(e)+xe)\,a\,m-f(e)$ (Online Supplement I; the paper writes the segment size as $\alpha$, which is renamed $a$ here to keep it apart from the eco-conscious share).
--
--   **Profile values.** With $a_N = 1-\alpha+\alpha\beta_c$ (Case N) and $a_P=\alpha+(1-\alpha)\beta_u$ (Case P):
--   1. $\pi(v_h,\bar e,0)=(v_h-c(\bar e))(1-\alpha)\beta_u m$ and $\pi(v_l,\bar e,0)=(v_l-c(\bar e))(1-\alpha)m$;
--   2. $\pi(v_h,e_{g,a},e_{g,a}+e_o\mid g)=(v_h-c(e_{g,a})-ge_{g,a}-ge_o)\,a\,m-f(e_{g,a})$ for $a=a_N,a_P$;
--   3. $\pi(v_l,e_{g,1},e_{g,1}+e_o\mid g)=(v_l-c(e_{g,1})-ge_{g,1}-ge_o)m-f(e_{g,1})$ (Case N);
--   4. $\pi(v_l,e_{g,1},e_{g,1}+e_o-\tfrac{v_h-v_l}{\xi}\mid g)=(v_l-c(e_{g,1})-g\tfrac{v_l-v_h}{\xi}-ge_{g,1}-ge_o)m-f(e_{g,1})$ (Case P).
--
--   The functions $h$ of the proof of Proposition 1 are the differences of the last two pairs: $h_N(g)$ is item 3 minus item 2 at $a_N$, and $h_P(g)$ is item 4 minus item 2 at $a_P$. The thresholds are
--   $$B_2=\frac{\frac{v_l-c(\bar e)}{v_h-c(\bar e)}-1+\alpha}{\alpha},\qquad \tilde B_2=\min\Big(\frac{(v_l-c(\bar e))-(v_h-c(\bar e))\alpha}{(v_h-c(\bar e))(1-\alpha)},\ \frac{\xi e_o(1-\alpha)-(v_h-v_l)}{\xi e_o(1-\alpha)}\Big).$$
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** The cost functions are required to be $C^2$ on all of $\mathbb R$ (the paper only uses them on $[0,\bar e]$); this is a mild added regularity. The sign conditions on $c',c'',f',f''$ are imposed on the closed interval $[0,\bar e]$, as on the page. Indicators use $\ge 0$ (buy at zero utility). `segOpt` is defined through `Classical.choose` with the fallback $\bar e$ when no maximizer exists; the milestone `segOpt_spec` shows the maximizer exists and is unique for $a\in[0,1]$, so the fallback never matters. `B2` divides by $\alpha$ and `B2P` by $1-\alpha$ and $\xi e_o$; every statement using them assumes $\alpha>0$, resp. $\alpha<1$ and $v_h-v_l<\xi e_o$.
-- source:
--   Gao & Souza, Carbon Offsetting with Eco-Conscious Consumers, SSRN 3440652 (copy held, sha256 e7d7f85a…7306), pp. 6–12 (PDF 7–13), §3, (1)–(3), Tables 2–3; p. 13 (PDF 14), Cases N and P; Online Supplement p. 1 (PDF 34), e_{x,α}; Online Supplement pp. 24–25 (PDF 57–58), h, B2, ˜B2

import Mathlib

namespace EcoOffset.Subgame

noncomputable section

/-- The primitives of the model of Gao & Souza (§3): market size `m`, maximal controllable
emissions `ebar` (¯e), uncontrollable emissions `eo`, eco-conscious disutility `ξ` per unit of
footprint, share `α` of eco-conscious consumers, shares `βc`, `βu` of high-value consumers in
the eco-conscious and eco-unconscious segments, valuations `vl < vh`, unit cost `c` and fixed
cost `f` as functions of the controllable emissions level. -/
structure Params where
  m : ℝ
  ebar : ℝ
  eo : ℝ
  ξ : ℝ
  α : ℝ
  βc : ℝ
  βu : ℝ
  vl : ℝ
  vh : ℝ
  c : ℝ → ℝ
  f : ℝ → ℝ

/-- The standing assumptions of §3 (pp. 7–9): `m > 0`, `¯e > 0`, `eo ≥ 0`, `ξ > 0`,
`α, βc, βu ∈ [0, 1]`, `0 ≤ vl` (consumer valuations are nonnegative), `c(¯e) < vl < vh`, `c` and `f` twice continuously differentiable with
`c' < 0`, `c'' > 0`, `f' < 0`, `f'' > 0` on `[0, ¯e]`, and `f(¯e) = 0`. -/
def Params.Standing (P : Params) : Prop :=
  0 < P.m ∧ 0 < P.ebar ∧ 0 ≤ P.eo ∧ 0 < P.ξ ∧
  0 ≤ P.α ∧ P.α ≤ 1 ∧ 0 ≤ P.βc ∧ P.βc ≤ 1 ∧ 0 ≤ P.βu ∧ P.βu ≤ 1 ∧
  0 ≤ P.vl ∧ P.c P.ebar < P.vl ∧ P.vl < P.vh ∧
  ContDiff ℝ 2 P.c ∧ ContDiff ℝ 2 P.f ∧ P.f P.ebar = 0 ∧
  ∀ e ∈ Set.Icc 0 P.ebar, deriv P.c e < 0 ∧ 0 < deriv (deriv P.c) e ∧
    deriv P.f e < 0 ∧ 0 < deriv (deriv P.f) e

/-- Feasible decisions: controllable emissions `e ∈ [0, ¯e]` and offsets `t ∈ [0, e + eo]`. -/
def Feasible (P : Params) (e t : ℝ) : Prop :=
  e ∈ Set.Icc 0 P.ebar ∧ t ∈ Set.Icc 0 (e + P.eo)

/-- The product carbon footprint `ℰ = e + eo − t`. -/
def footprint (P : Params) (e t : ℝ) : ℝ := e + P.eo - t

/-- Demand from the eco-conscious segment, the first two terms of (2). A consumer buys iff her
utility (1) is nonnegative. -/
def demandC (P : Params) (p e t : ℝ) : ℝ :=
  P.α * P.βc * P.m * (if 0 ≤ P.vh - P.ξ * footprint P e t - p then 1 else 0) +
  P.α * (1 - P.βc) * P.m * (if 0 ≤ P.vl - P.ξ * footprint P e t - p then 1 else 0)

/-- Demand from the eco-unconscious segment, the last two terms of (2). -/
def demandU (P : Params) (p e t : ℝ) : ℝ :=
  (1 - P.α) * P.βu * P.m * (if 0 ≤ P.vh - p then 1 else 0) +
  (1 - P.α) * (1 - P.βu) * P.m * (if 0 ≤ P.vl - p then 1 else 0)

/-- Total demand `d(p, e, t)`, equation (2). -/
def demand (P : Params) (p e t : ℝ) : ℝ := demandC P p e t + demandU P p e t

/-- The firm's profit `π(p, e, t | g) = (p − c(e) − g t) d(p, e, t) − f(e)`, equation (3). -/
def profit (P : Params) (g p e t : ℝ) : ℝ :=
  (p - P.c e - g * t) * demand P p e t - P.f e

/-- `(p, e, t)` is a best response of the firm to the offset price `g`: it is feasible and no
feasible decision (at any price `p' ∈ ℝ`) earns a strictly higher profit. -/
def IsBestResponse (P : Params) (g p e t : ℝ) : Prop :=
  Feasible P e t ∧ ∀ p' e' t', Feasible P e' t' → profit P g p' e' t' ≤ profit P g p e t

/-- The objective `−(c(e) + x e) a m − f(e)` whose maximizer over `[0, ¯e]` is the
segment-optimal emission `e_{x,a}` of Online Supplement I. -/
def segObj (P : Params) (x a e : ℝ) : ℝ := -(P.c e + x * e) * a * P.m - P.f e

/-- `e` maximizes `segObj P x a` over `[0, ¯e]`. -/
def IsSegOpt (P : Params) (x a e : ℝ) : Prop :=
  e ∈ Set.Icc 0 P.ebar ∧ ∀ e' ∈ Set.Icc 0 P.ebar, segObj P x a e' ≤ segObj P x a e

open Classical in
/-- The segment-optimal emission `e_{x,a}`: a maximizer of `segObj P x a` over `[0, ¯e]`
(unique under the standing assumptions for `a ∈ [0, 1]`); the fallback `¯e` is never used
under the standing assumptions. -/
def segOpt (P : Params) (x a : ℝ) : ℝ :=
  if h : ∃ e, IsSegOpt P x a e then h.choose else P.ebar

/-! ### Case N (`βu = 1`) -/

/-- Segment size `1 − α + αβc` served at the price `vh` with full offsets in Case N. -/
def aN (P : Params) : ℝ := 1 - P.α + P.α * P.βc

/-- `π(vh, ¯e, 0 | g) = (vh − c(¯e))(1 − α) βu m`: sell to high-value eco-unconscious consumers
alone, without offsets (option 1 of Online Supplement I1). -/
def valOne (P : Params) : ℝ := (P.vh - P.c P.ebar) * (1 - P.α) * P.βu * P.m

/-- `π(vh, e_{g,aN}, e_{g,aN} + eo | g)`: price `vh`, full offsets, emissions `e_{g,aN}`. -/
def valTwoN (P : Params) (g : ℝ) : ℝ :=
  (P.vh - P.c (segOpt P g (aN P)) - g * segOpt P g (aN P) - g * P.eo) * aN P * P.m -
    P.f (segOpt P g (aN P))

/-- `π(vl, e_{g,1}, e_{g,1} + eo | g)`: sell to all consumers at `vl` with full offsets
(option 6 of Online Supplement I1). -/
def valAll (P : Params) (g : ℝ) : ℝ :=
  (P.vl - P.c (segOpt P g 1) - g * segOpt P g 1 - g * P.eo) * P.m - P.f (segOpt P g 1)

/-- `h(g)` of the proof of Proposition 1, Case N. -/
def hN (P : Params) (g : ℝ) : ℝ := valAll P g - valTwoN P g

/-- `B2 = ((vl − c(¯e))/(vh − c(¯e)) − 1 + α)/α`. -/
def B2 (P : Params) : ℝ :=
  ((P.vl - P.c P.ebar) / (P.vh - P.c P.ebar) - 1 + P.α) / P.α

/-! ### Case P (`βc = 1`) -/

/-- Segment size `α + (1 − α)βu` served at the price `vh` with full offsets in Case P. -/
def aP (P : Params) : ℝ := P.α + (1 - P.α) * P.βu

/-- `π(vh, e_{g,aP}, e_{g,aP} + eo | g)`. -/
def valTwoP (P : Params) (g : ℝ) : ℝ :=
  (P.vh - P.c (segOpt P g (aP P)) - g * segOpt P g (aP P) - g * P.eo) * aP P * P.m -
    P.f (segOpt P g (aP P))

/-- `π(vl, e_{g,1}, e_{g,1} + eo − (vh − vl)/ξ | g)`. -/
def valAllP (P : Params) (g : ℝ) : ℝ :=
  (P.vl - P.c (segOpt P g 1) - g * (P.vl - P.vh) / P.ξ - g * segOpt P g 1 - g * P.eo) * P.m -
    P.f (segOpt P g 1)

/-- `π(vl, ¯e, 0 | g) = (vl − c(¯e))(1 − α) m`. -/
def valThree (P : Params) : ℝ := (P.vl - P.c P.ebar) * (1 - P.α) * P.m

/-- `h(g)` of the proof of Proposition 1, Case P. -/
def hP (P : Params) (g : ℝ) : ℝ := valAllP P g - valTwoP P g

/-- `˜B2 = min( ((vl − c(¯e)) − (vh − c(¯e))α)/((vh − c(¯e))(1 − α)),
(ξ eo (1 − α) − (vh − vl))/(ξ eo (1 − α)) )`. -/
def B2P (P : Params) : ℝ :=
  min (((P.vl - P.c P.ebar) - (P.vh - P.c P.ebar) * P.α) / ((P.vh - P.c P.ebar) * (1 - P.α)))
    ((P.ξ * P.eo * (1 - P.α) - (P.vh - P.vl)) / (P.ξ * P.eo * (1 - P.α)))

end

end EcoOffset.Subgame


