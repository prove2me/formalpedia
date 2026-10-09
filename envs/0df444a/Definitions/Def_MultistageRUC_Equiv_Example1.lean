-- Prove2me | Definitions.Def_MultistageRUC_Equiv_Example1
-- name    : MultistageRUC_Equiv_Example1
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T08:15:23.434028+00:00
-- url     : https://prove2.me/theorems/a68d8d42-055c-4ca2-9856-cc92ee7f0a58
-- title:
--   Example 1, pp. 7–8 — the two-bus, two-period system, its uncertainty sets, dispatch constraints and the policy (4)
-- statement:
--   The data of Example 1, a two-bus, two-period system that shows the limitation of non-causal UC models.
--
--   Buses $A$ and $B$ each have one generator, joined by a line with flow limit $f^{\max}=1$. The ramp rates are $R_A=R_B=1$ and the initial generation levels are $p_A^0=p_B^0=12$. The net-load uncertainty sets are
--   $$\mathcal D^1=\{(d_A^1,d_B^1)=(12,12)\},\qquad \mathcal D^2=\{(d_A^2,d_B^2):d_A^2\in[10,15],\ d_B^2\in[10,15],\ d_A^2+d_B^2=25\},$$
--   and $\mathcal D=\mathcal D^1\times\mathcal D^2$.
--
--   Under the commitment $x^*_{2S}=((1,1),(1,1))$ (both units on in both periods), a dispatch $p^t$ after $p^{t-1}$ with loads $d^t$ is feasible when
--   1. $p_A^t+p_B^t=d_A^t+d_B^t$ (energy balance);
--   2. $|p_b^t-p_b^{t-1}|\le 1$ for $b\in\{A,B\}$ (ramping);
--   3. $|p_A^t-d_A^t|\le 1$ (line limit on the flow from $A$ to $B$).
--
--   A two-period policy $p(\cdot)$ is **causal** when $p^1(d)$ does not depend on $d^2$. The policy (4) of the proof of Proposition 1 is
--   $$p_A^1(d)=12+\tfrac25(d_A^2-12.5),\quad p_B^1(d)=12-\tfrac25(d_A^2-12.5),\quad p_A^2(d)=12.5+\tfrac35(d_A^2-12.5),\quad p_B^2(d)=12.5-\tfrac35(d_A^2-12.5).$$
--
--   These objects carry Propositions 1 and 2: with ramping, the two-stage model is feasible while no causal dispatch exists.
--
--   **Formalization Note** Lean period $0$ is the paper's $t=1$. The flow on the line is the net injection $p_A^t-d_A^t$ at bus $A$. Example 1 gives no costs and no capacity limits, so none are imposed. With both units on throughout, $u=v=0$ and the start-up/shut-down terms of (1i) vanish, leaving the ramp bounds $\pm1$.
-- source:
--   Lorca, Sun, Litvinov, Zheng, Multistage adaptive robust optimization for the unit commitment problem, Oper. Res. (2016), doi:10.1287/opre.2015.1456, manuscript of Sept. 29, 2014, pp. 7–8, Example 1, Figure 1, (4)

import Mathlib

namespace MultistageRUC.Equiv.Example1

/-- The two buses `A` and `B` of Example 1 (p. 7), each with one generator. -/
inductive Bus
  | A
  | B
  deriving DecidableEq

open Bus

/-- `𝒟¹ = {(d_A^1, d_B^1) = (12, 12)}` (p. 8). -/
def D1 : Set (Bus → ℝ) := {e | e A = 12 ∧ e B = 12}

/-- `𝒟² = {(d_A^2, d_B^2) : d_A^2 ∈ [10, 15], d_B^2 ∈ [10, 15], d_A^2 + d_B^2 = 25}` (p. 8). -/
def D2 : Set (Bus → ℝ) := {e | e A ∈ Set.Icc 10 15 ∧ e B ∈ Set.Icc 10 15 ∧ e A + e B = 25}

/-- `𝒟 = 𝒟¹ × 𝒟²`: net-load trajectories over the two periods (Lean period `0` is the paper's
`t = 1`, period `1` is `t = 2`). -/
def Dex : Set (Fin 2 → Bus → ℝ) := {d | d 0 ∈ D1 ∧ d 1 ∈ D2}

/-- The initial generation levels `p_A^0 = p_B^0 = 12`. -/
def p0 : Bus → ℝ := fun _ => 12

/-- The constraints of one period under the commitment `x*_2S = ((1,1),(1,1))` (both units on in
both periods): dispatch `q` after dispatch `qprev`, with net loads `e`:
energy balance; ramping with `R_A = R_B = 1`; and the line limit `f^max = 1` on the flow from `A`
to `B`, which is the net injection `q_A − e_A` at bus `A`. -/
def stepOK (qprev q e : Bus → ℝ) : Prop :=
  q A + q B = e A + e B ∧
  (∀ b, -1 ≤ q b - qprev b ∧ q b - qprev b ≤ 1) ∧
  (-1 ≤ q A - e A ∧ q A - e A ≤ 1)

/-- A dispatch policy over the two periods: `π t d` is the dispatch at period `t` when the
net-load trajectory is `d`. -/
abbrev ExPolicy := Fin 2 → (Fin 2 → Bus → ℝ) → Bus → ℝ

/-- The policy `π` is feasible at the trajectory `d`. -/
def policyOK (π : ExPolicy) (d : Fin 2 → Bus → ℝ) : Prop :=
  stepOK p0 (π 0 d) (d 0) ∧ stepOK (π 0 d) (π 1 d) (d 1)

/-- Time causality: the first-period dispatch `p¹(·)` does not depend on `d²`. -/
def Causal (π : ExPolicy) : Prop :=
  ∀ d d' : Fin 2 → Bus → ℝ, d 0 = d' 0 → π 0 d = π 0 d'

/-- The dispatch policy (4) of the proof of Proposition 1 (p. 8). -/
noncomputable def pi4 : ExPolicy := fun t d b =>
  if t = 0 then
    (match b with
     | A => 12 + (2 / 5) * (d 1 A - 12.5)
     | B => 12 - (2 / 5) * (d 1 A - 12.5))
  else
    (match b with
     | A => 12.5 + (3 / 5) * (d 1 A - 12.5)
     | B => 12.5 - (3 / 5) * (d 1 A - 12.5))

end MultistageRUC.Equiv.Example1


