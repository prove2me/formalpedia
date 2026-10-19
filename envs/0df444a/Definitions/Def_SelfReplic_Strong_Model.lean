-- Prove2me | Definitions.Def_SelfReplic_Strong_Model
-- name    : SelfReplic_Strong_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T01:21:19.036985+00:00
-- url     : https://prove2.me/theorems/c5cfe564-90bb-4bcd-b83b-bc96e130b041
-- title:
--   §3, pp. 6–10 — Problem (1): self-replicating inventory, Bass demand with adjusted cumulative sales, admissible trajectories, discounted profit, Strong Replicability (2)
-- statement:
--   This file sets up the base model of Hu and Sun (Problem (1), §3).
--
--   **Parameters.** A good can only be produced by replicating itself. The parameters are the market size $m$, the retail price $\pi$, the unit replication cost $c$, the holding cost $h$ per unit good-time, the replication rate $r$, the coefficient of innovation $\alpha$, the coefficient of imitation $\beta$, the discount rate $\rho$, the diminishing rate $w$ of word-of-mouth, the life cycle $T$ and the launch inventory $I_L$. The **standing assumptions** are those of the paper, $I_L>0$, $\pi>c$, $r>\rho\ge 0$, $w\ge 0$, together with the sign conditions $m>0$, $T>0$, $\alpha>0$, $\beta\ge0$, $c\ge0$, $h\ge0$.
--
--   **Trajectories.** A trajectory consists of the cumulative demand $D(t)$, the adjusted cumulative sales $S(t)$, the inventory $I(t)$, the production rate $p(t)$ and the sales rate $s(t)$. The demand rate is
--   $$d(t)=\Big[\alpha+\frac{\beta S(t)}{m}\Big]\big[m-D(t)\big].$$
--   A trajectory is **admissible** if $p,s$ are integrable on $[0,T]$, $D,S,I$ are continuous on $[0,T]$, and for every $t\in[0,T]$
--   $$D(t)=\int_0^t d(u)\,du,\qquad S(t)=\int_0^t\big[s(u)-wS(u)\big]du,\qquad I(t)=I_L+\int_0^t\big[p(u)-s(u)\big]du,$$
--   $$0\le p(t)\le rI(t),\qquad 0\le s(t)\le d(t),$$
--   and $I(T)\ge 0$. These are the ODEs $D'=d$, $S'=s-wS$, $I'=p-s$ with $D(0)=S(0)=0$, $I(0)=I_L$.
--
--   **Objective and optimality.** The profit of a trajectory is
--   $$\int_0^T\big[\pi s(t)-cp(t)-hI(t)\big]e^{-\rho t}\,dt,$$
--   and a trajectory is **optimal** if it is admissible and its profit is at least that of every admissible trajectory with the same parameters.
--
--   **Policy shapes.** Production is *on* when $p(t)=rI(t)$ and *off* when $p(t)=0$; sales are *on* when $s(t)=d(t)$ and *off* when $s(t)=0$. The file defines: production always on, always off, or off before a time $t_p$ and on from $t_p$; sales always on, or off before a time $t_s$ and on from $t_s$; and "the inventory is depleted exactly at $T$", meaning $I(T)=0$ and $I(t)>0$ for $0\le t<T$.
--
--   **Thresholds.** A level $J$ is the threshold $\underline I$ if, with launch inventory $J$ and all other parameters unchanged, some admissible trajectory with production and sales always on depletes the inventory exactly at $T$. It is the threshold $\overline I$ if the same holds with production always off and sales always on.
--
--   **Strong Replicability** is condition (2): $(r-\rho)\pi>cr+h$.
--
--   These objects are the vocabulary of Theorem 1 and of Propositions 1 and 2.
--
--   **Formalization Note** The ODEs are imposed in integral form because bang-bang controls are discontinuous. Continuity of the states and integrability of the controls make every integrand integrable, so no integral takes Lean's default value $0$. The constraints are imposed at every $t\in[0,T]$ rather than almost everywhere; changing a control on a null set changes neither the states nor the profit. The constraint $I\ge0$ is not imposed: it follows from $0\le p\le rI$ and $r>0$. The sign conditions $m>0$, $T>0$, $\alpha>0$, $\beta\ge0$, $c\ge0$, $h\ge0$ are used by the paper without being stated. At a switch time the policy counts as already switched on, which is a null set. Functions are on $\mathbb R$, and their values outside $[0,T]$ play no role.
-- source:
--   Hu & Sun, Managing self-replicating innovative goods, authors' manuscript of 2020-10-18 (Management Science, doi:10.1287/mnsc.2020.3936), pp. 6–10, §3, Problem (1), condition (2), Theorem 1 (definitions of the thresholds)

import Mathlib

namespace SelfReplic.Strong

open MeasureTheory

/-- The parameters of Problem (1) (Hu & Sun, §3, pp. 6–8). `price` is the retail price π,
`alpha`/`beta` the Bass coefficients of innovation/imitation, `rho` the discount rate ρ,
`w` the word-of-mouth decay, `IL` the launch inventory I_L. -/
structure Params where
  /-- market size -/
  m : ℝ
  /-- retail price π -/
  price : ℝ
  /-- unit replication cost -/
  c : ℝ
  /-- holding cost per unit good-time -/
  h : ℝ
  /-- replication rate -/
  r : ℝ
  /-- coefficient of innovation α -/
  alpha : ℝ
  /-- coefficient of imitation β -/
  beta : ℝ
  /-- continuous discount rate ρ -/
  rho : ℝ
  /-- diminishing rate of word-of-mouth -/
  w : ℝ
  /-- maximum life cycle -/
  T : ℝ
  /-- initial launch inventory I_L -/
  IL : ℝ

/-- Standing assumptions. On the page (pp. 6–8): `I_L > 0`, `π > c`, `r > ρ`, `ρ ≥ 0`, `w ≥ 0`.
Added and disclosed (never stated, used throughout): `m > 0`, `T > 0`, `α > 0`, `β ≥ 0`,
`c ≥ 0`, `h ≥ 0`. -/
def Params.Standing (P : Params) : Prop :=
  0 < P.IL ∧ P.c < P.price ∧ P.rho < P.r ∧ 0 ≤ P.rho ∧ 0 ≤ P.w ∧
  0 < P.m ∧ 0 < P.T ∧ 0 < P.alpha ∧ 0 ≤ P.beta ∧ 0 ≤ P.c ∧ 0 ≤ P.h

/-- Strong Replicability, condition (2): `(r − ρ)π > cr + h`. -/
def Params.StrongRepl (P : Params) : Prop :=
  P.c * P.r + P.h < (P.r - P.rho) * P.price

/-- The same parameters with launch inventory `J` in place of `I_L`. -/
def Params.withIL (P : Params) (J : ℝ) : Params := { P with IL := J }

/-- The demand rate `d = [α + βS/m][m − D]`. -/
noncomputable def demandRate (P : Params) (D S : ℝ) : ℝ :=
  (P.alpha + P.beta * S / P.m) * (P.m - D)

/-- A trajectory: states `D` (cumulative demand), `S` (adjusted cumulative sales), `I`
(inventory) and controls `p` (production rate), `s` (sales rate), as functions of time. -/
structure Traj where
  D : ℝ → ℝ
  S : ℝ → ℝ
  I : ℝ → ℝ
  p : ℝ → ℝ
  s : ℝ → ℝ

/-- The demand rate along a trajectory, `d(t) = [α + βS(t)/m][m − D(t)]`. -/
noncomputable def Traj.d (P : Params) (x : Traj) (t : ℝ) : ℝ := demandRate P (x.D t) (x.S t)

/-- Admissible trajectories of Problem (1): integrable controls, continuous states satisfying the
ODEs `D' = d`, `S' = s − wS`, `I' = p − s` with `D(0) = S(0) = 0`, `I(0) = I_L` in integral form on
`[0, T]`, the constraints `0 ≤ p ≤ rI`, `0 ≤ s ≤ d` at every `t ∈ [0, T]`, and `I(T) ≥ 0`. -/
def IsAdmissible (P : Params) (x : Traj) : Prop :=
  IntegrableOn x.p (Set.Icc 0 P.T) ∧ IntegrableOn x.s (Set.Icc 0 P.T) ∧
  ContinuousOn x.D (Set.Icc 0 P.T) ∧ ContinuousOn x.S (Set.Icc 0 P.T) ∧
  ContinuousOn x.I (Set.Icc 0 P.T) ∧
  (∀ t ∈ Set.Icc 0 P.T,
      x.D t = ∫ u in (0:ℝ)..t, x.d P u ∧
      x.S t = ∫ u in (0:ℝ)..t, (x.s u - P.w * x.S u) ∧
      x.I t = P.IL + ∫ u in (0:ℝ)..t, (x.p u - x.s u)) ∧
  (∀ t ∈ Set.Icc 0 P.T,
      0 ≤ x.p t ∧ x.p t ≤ P.r * x.I t ∧ 0 ≤ x.s t ∧ x.s t ≤ x.d P t) ∧
  0 ≤ x.I P.T

/-- The objective of Problem (1): `∫_0^T [πs(t) − cp(t) − hI(t)] e^{−ρt} dt`. -/
noncomputable def profit (P : Params) (x : Traj) : ℝ :=
  ∫ t in (0:ℝ)..P.T, (P.price * x.s t - P.c * x.p t - P.h * x.I t) * Real.exp (-(P.rho * t))

/-- `x` solves Problem (1): it is admissible and its profit is at least that of every admissible
trajectory with the same parameters. -/
def IsOptimal (P : Params) (x : Traj) : Prop :=
  IsAdmissible P x ∧ ∀ y : Traj, IsAdmissible P y → profit P y ≤ profit P x

/-- Production always on: `p(t) = rI(t)` on `[0, T]`. -/
def ProdAlwaysOn (P : Params) (x : Traj) : Prop := ∀ t ∈ Set.Icc 0 P.T, x.p t = P.r * x.I t

/-- Production always off: `p(t) = 0` on `[0, T]`. -/
def ProdAlwaysOff (P : Params) (x : Traj) : Prop := ∀ t ∈ Set.Icc 0 P.T, x.p t = 0

/-- Production off before `tp` and on from `tp` to `T`. -/
def ProdOnFrom (P : Params) (x : Traj) (tp : ℝ) : Prop :=
  ∀ t ∈ Set.Icc 0 P.T, x.p t = if t < tp then 0 else P.r * x.I t

/-- Sales always on: `s(t) = d(t)` on `[0, T]`. -/
def SalesAlwaysOn (P : Params) (x : Traj) : Prop := ∀ t ∈ Set.Icc 0 P.T, x.s t = x.d P t

/-- Sales off before `ts` and on from `ts` to `T`. -/
def SalesOnFrom (P : Params) (x : Traj) (ts : ℝ) : Prop :=
  ∀ t ∈ Set.Icc 0 P.T, x.s t = if t < ts then 0 else x.d P t

/-- The inventory is depleted exactly at `T`: `I(T) = 0` and `I(t) > 0` for `t ∈ [0, T)`. -/
def DepletedExactlyAtT (P : Params) (x : Traj) : Prop :=
  x.I P.T = 0 ∧ ∀ t ∈ Set.Ico 0 P.T, 0 < x.I t

/-- `J` is the level I̲ of Theorem 1: with launch inventory `J` (all other parameters unchanged),
always keeping production and sales on leads to inventory depletion at exactly `T`. -/
def IsLowLevel (P : Params) (J : ℝ) : Prop :=
  ∃ x : Traj, IsAdmissible (P.withIL J) x ∧ ProdAlwaysOn (P.withIL J) x ∧
    SalesAlwaysOn (P.withIL J) x ∧ DepletedExactlyAtT (P.withIL J) x

/-- `J` is the level Ī of Theorem 1: with launch inventory `J` (all other parameters unchanged),
always keeping production off and sales on leads to inventory depletion at exactly `T`. -/
def IsHighLevel (P : Params) (J : ℝ) : Prop :=
  ∃ x : Traj, IsAdmissible (P.withIL J) x ∧ ProdAlwaysOff (P.withIL J) x ∧
    SalesAlwaysOn (P.withIL J) x ∧ DepletedExactlyAtT (P.withIL J) x

end SelfReplic.Strong


