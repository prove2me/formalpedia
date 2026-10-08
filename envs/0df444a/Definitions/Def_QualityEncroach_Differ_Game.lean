-- Prove2me | Definitions.Def_QualityEncroach_Differ_Game
-- name    : QualityEncroach_Differ_Game
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T00:22:29.107985+00:00
-- url     : https://prove2.me/theorems/8d9291f8-dd53-4c6d-8e4a-80fbcf8fe438
-- title:
--   §3.1, §5, pp. 7–8, 15 — the encroachment game with quality differentiation: inverse demands, payoffs, strategy profiles and subgame-perfect equilibria
-- statement:
--   This file sets up the encroachment game of Ha, Long & Nasiry (§3.1 and §5). A manufacturer (she) sells through a retailer (he) and through her own direct channel. Consumers have types $\theta$ uniformly distributed on $[0,1]$ (market size $1$); a consumer of type $\theta$ obtains surplus $\theta v - p$ from a product of quality $v$ sold at price $p$.
--
--   The manufacturer sells a product of quality $u>0$ directly and a product of quality $tu$, $t>0$, through the retailer. Given the quantities $q_M$ (direct) and $q_R$ (retailer), the market-clearing prices are
--
--   $$
--   p_M = \begin{cases} u(1-q_M-t\,q_R), & t\le 1,\\ u(1-q_M-q_R), & t>1,\end{cases}
--   \qquad
--   p_R = \begin{cases} tu(1-q_M-q_R), & t\le 1,\\ tu(1-q_R)-u\,q_M, & t>1.\end{cases}
--   $$
--
--   Making one unit of quality $v$ costs the manufacturer $kv^2$ ($k>0$); every unit sold directly costs her a further $c\ge 0$; the retailer's selling cost is $0$. An **outcome** is $(w,u,t,q_R,q_M)$, and the profits are
--
--   $$
--   \Pi_R = (p_R - w)\,q_R,
--   \qquad
--   \Pi_M = \bigl(w - k(tu)^2\bigr)q_R + \bigl(p_M - c - ku^2\bigr)q_M .
--   $$
--
--   The timeline is: (i) the manufacturer chooses the wholesale price $w$, the quality $u$ and the ratio $t$; (ii) having observed them, the retailer orders $q_R$; (iii) having observed everything, the manufacturer chooses $q_M$. A **strategy profile** $\sigma$ consists of the manufacturer's stage-1 choice $(w,u,t)$, the retailer's rule $(w,u,t)\mapsto q_R$ and the manufacturer's stage-3 rule $(w,u,t,q_R)\mapsto q_M$; its **path** is the outcome it generates.
--
--   Given a set $T$ of admissible ratios, $\sigma$ is a **subgame-perfect equilibrium** when at every history (on or off the path) the mover's rule picks a feasible action and no feasible alternative, followed by play according to $\sigma$, gives the mover a strictly higher profit. Feasible actions: $w\in\mathbb R$, $u>0$, $t\in T$, $q_R\ge 0$, $q_M\ge 0$. With $T=(0,\infty)$ this is the game of §5 (encroachment with quality differentiation); with $T=\{1\}$ it is the game of §4.1 (encroachment with uniform quality), in which both prices equal $u(1-q_M-q_R)$.
--
--   Every statement of the mission about equilibria refers to these objects. "Encroachment" means $q_M>0$ on the equilibrium path (p. 11).
--
--   **Formalization Note.** The page derives the prices for $0<t\le 1$ and says the case $t\ge 1$ "can be derived similarly"; the $t>1$ formulas above are that derivation, and they are the ones the paper's own expressions for $t\ge1$ (the wholesale price $w(t,u)$ and the profit (14), p. 33) evaluate. Both branches agree at $t=1$. As in the paper, the price formulas are used for all nonnegative quantities. The wholesale price carries no sign restriction, since the paper states none. The equilibrium is written in one-shot-deviation form, which coincides with subgame perfection in this finite game.
-- source:
--   Ha, Long & Nasiry, Quality in Supply Chain Encroachment, authors' manuscript, SSRN 3970373, pp. 7–8, §3.1 (consumers, costs, timeline, quality differentiation), p. 15, §5 (inverse demand functions), p. 11 (definition of encroachment)

import Mathlib

namespace QualityEncroach.Differ

/-!
# Ha, Long & Nasiry, *Quality in Supply Chain Encroachment*: the encroachment game with
quality differentiation (§3.1, pp. 7–8; §5, p. 15)

A manufacturer sells a product of quality `u > 0` through her direct channel and a product of
quality `t * u` (`t > 0`) through a retailer. Consumer types `θ` are uniform on `[0, 1]` and a
consumer of type `θ` gets surplus `θ v − p` from quality `v` at price `p`. Production of one
unit of quality `v` costs the manufacturer `k v²`; each unit sold directly costs her a further
`c`. The retailer's selling cost is zero.

Timeline: (i) the manufacturer chooses `w`, `u`, `t`; (ii) the retailer orders `q_R`;
(iii) the manufacturer sells `q_M` directly.
-/

/-- Market-clearing price of the direct-channel product (quality `u`), p. 15. For `t ≤ 1`
(direct channel high): `p_M = u (1 − q_M − t q_R)`. For `t > 1` (retailer high):
`p_M = u (1 − q_M − q_R)`. -/
noncomputable def priceM (u t qM qR : ℝ) : ℝ :=
  if t ≤ 1 then u * (1 - qM - t * qR) else u * (1 - qM - qR)

/-- Market-clearing price of the retailer-channel product (quality `t u`), p. 15. For `t ≤ 1`:
`p_R = t u (1 − q_M − q_R)`. For `t > 1`: `p_R = t u (1 − q_R) − u q_M`. -/
noncomputable def priceR (u t qM qR : ℝ) : ℝ :=
  if t ≤ 1 then t * u * (1 - qM - qR) else t * u * (1 - qR) - u * qM

/-- An outcome (terminal history): wholesale price `w`, direct quality `u`, ratio `t`
(retailer quality `t u`), retailer order `qR`, direct quantity `qM`. -/
structure Outcome where
  w : ℝ
  u : ℝ
  t : ℝ
  qR : ℝ
  qM : ℝ

/-- The retailer's profit `(p_R − w) q_R`. -/
noncomputable def retailerPayoff (o : Outcome) : ℝ :=
  (priceR o.u o.t o.qM o.qR - o.w) * o.qR

/-- The manufacturer's profit `(w − k (t u)²) q_R + (p_M − c − k u²) q_M`. -/
noncomputable def mfrPayoff (k c : ℝ) (o : Outcome) : ℝ :=
  (o.w - k * (o.t * o.u) ^ 2) * o.qR + (priceM o.u o.t o.qM o.qR - c - k * o.u ^ 2) * o.qM

/-- A pure strategy profile: the manufacturer's stage-1 choice `(w, u, t)`, the retailer's rule
`order w u t = q_R`, and the manufacturer's stage-3 rule `direct w u t q_R = q_M`. -/
structure Profile where
  w : ℝ
  u : ℝ
  t : ℝ
  order : ℝ → ℝ → ℝ → ℝ
  direct : ℝ → ℝ → ℝ → ℝ → ℝ

/-- The outcome after the history `(w, u, t, q_R)` when the manufacturer then follows `σ`. -/
def Profile.outcomeAtDirect (σ : Profile) (w u t qR : ℝ) : Outcome :=
  ⟨w, u, t, qR, σ.direct w u t qR⟩

/-- The outcome after the history `(w, u, t)` when play then follows `σ`. -/
def Profile.outcomeAtOrder (σ : Profile) (w u t : ℝ) : Outcome :=
  σ.outcomeAtDirect w u t (σ.order w u t)

/-- The equilibrium path of `σ`. -/
def Profile.path (σ : Profile) : Outcome :=
  σ.outcomeAtOrder σ.w σ.u σ.t

/-- `σ` is a subgame-perfect equilibrium of the game in which the admissible quality ratios are
`T` (`T = Set.Ioi 0`: §5's game with quality differentiation; `T = {1}`: §4.1's game with uniform
quality). Action sets: `w ∈ ℝ`, `u > 0`, `t ∈ T`, `q_R ≥ 0`, `q_M ≥ 0`. At every history the
mover's rule picks a feasible action and no feasible alternative, followed by play according to
`σ`, gives the mover a strictly higher payoff. -/
def IsSPE (k c : ℝ) (T : Set ℝ) (σ : Profile) : Prop :=
  -- stage 3: the manufacturer's direct quantity
  (∀ w u t qR : ℝ, 0 < u → t ∈ T → 0 ≤ qR →
      0 ≤ σ.direct w u t qR ∧
      ∀ qM : ℝ, 0 ≤ qM →
        mfrPayoff k c ⟨w, u, t, qR, qM⟩ ≤ mfrPayoff k c (σ.outcomeAtDirect w u t qR)) ∧
  -- stage 2: the retailer's order
  (∀ w u t : ℝ, 0 < u → t ∈ T →
      0 ≤ σ.order w u t ∧
      ∀ qR : ℝ, 0 ≤ qR →
        retailerPayoff (σ.outcomeAtDirect w u t qR) ≤ retailerPayoff (σ.outcomeAtOrder w u t)) ∧
  -- stage 1: the manufacturer's wholesale price and qualities
  (0 < σ.u ∧ σ.t ∈ T ∧
      ∀ w u t : ℝ, 0 < u → t ∈ T →
        mfrPayoff k c (σ.outcomeAtOrder w u t) ≤ mfrPayoff k c σ.path)

end QualityEncroach.Differ


