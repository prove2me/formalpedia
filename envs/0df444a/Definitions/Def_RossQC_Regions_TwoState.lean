-- Prove2me | Definitions.Def_RossQC_Regions_TwoState
-- name    : RossQC_Regions_TwoState
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T15:17:14.238333+00:00
-- url     : https://prove2.me/theorems/48d16ea5-6db8-48d6-abe6-e3666c0638f2
-- title:
--   §3 two-state instance: P₀₀ = 1 − π, P₁₁ = 1, C₀ = 0, C₁ = C, I, R; scalar belief, TP = P + π − πP, right side of (3), regions, optimal rules, four-region rule
-- statement:
--   This module obtains Ross's two-state production process (§3) as an instance of the general model.
--
--   1. **Instance.** States $0$ (good) and $1$ (bad); $P_{00}=1-\pi$, $P_{01}=\pi$, $P_{10}=0$, $P_{11}=1$; $C_0=0$, $C_1=C$; $I_0=I_1=I$; $R_0=R_1=R$; discount $\beta$; a revision leads to state $0$.
--   2. **Scalar belief.** The number $P\in[0,1]$ stands for the belief $(1-P,P)$: $P$ is the probability that the process is in the bad state. The two-state optimal cost $V_\beta(P)$ is the general $V_\beta$ of the instance at $(1-P,P)$.
--   3. **Update and equation (3).** $TP=P+\pi-\pi P$, and the right side of (3) at $P$ for produce, inspect and revise is
--   $$
--   CP+\beta V(TP),\qquad I+\beta PV(1)+\beta(1-P)V(\pi),\qquad R+\beta V(\pi).
--   $$
--   4. **Regions and rules.** The $\beta$-optimal region of an action is the set of $P\in[0,1]$ where $V_\beta(P)$ equals that action's term of (3). A stationary rule $\delta:[0,1]\to\{\text{produce},\text{inspect},\text{revise}\}$ is **$\beta$-optimal** if $\delta(P)$ attains the minimum in (3) at every $P\in[0,1]$.
--   5. **Four-region rule.** For thresholds $P_1,P_2,P_3$, the rule produces for $P<P_1$, inspects for $P_1\le P<P_2$, produces for $P_2\le P<P_3$ and revises for $P\ge P_3$.
--
--   Because the two-state quantities are defined through the general model, the general results (the optimality equation, concavity, convexity of regions) apply to them literally.
--
--   **Formalization Note** "$\beta$-optimal rule" follows the paper's criterion quoted from Blackwell on p. 588: a rule selecting a minimizer of the right side of the optimality equation is $\beta$-optimal. The standing hypotheses $0<\beta<1$, $0\le\pi\le1$, $0<C<I<R$ are hypotheses of the theorems, not part of the data.
-- source:
--   Ross, Quality Control under Markovian Deterioration, Management Science 17(9):587–596 (1971), DOI 10.1287/mnsc.17.9.587, p. 590, §3: the two-state process, TP = P + π − πP and (3); Theorem 3.3 (the threshold rule)

import Mathlib
import Definitions.Def_RossQC_Regions_Model

namespace RossQC.Regions

/-- Ross, *Quality Control under Markovian Deterioration*, Management Science 17(9):587–596 (1971),
DOI 10.1287/mnsc.17.9.587, §3, p. 590: the two-state production process as an instance of the
general model of §2. State `0` is good, state `1` is bad; revising leads to state `0`.

* `P₀₀ = 1 − π`, `P₀₁ = π`, `P₁₀ = 0`, `P₁₁ = 1`;
* `C₀ = 0`, `C₁ = C`; `I₀ = I₁ = I`; `R₀ = R₁ = R`;
* the discount factor is `β`.

The paper's standing assumption `C < I < R` (and `0 < β < 1`, `0 ≤ π ≤ 1`, `0 < C`) are hypotheses
of the theorems, not part of this data. -/
def twoState (β π C I R : ℝ) : Model (Fin 2) where
  i₀ := 0
  Pm := ![![1 - π, π], ![0, 1]]
  C := ![0, C]
  I := ![I, I]
  R := ![R, R]
  β := β

/-- The belief `(1 − P, P)` that puts probability `P` on the bad state; §3 identifies it with the
number `P ∈ [0, 1]` ("we say that `X_t = P` if `P` is the probability that at the beginning of
period `t` the underlying process is in the bad state", p. 590). -/
def belief (P : ℝ) : Fin 2 → ℝ := ![1 - P, P]

/-- The two-state optimal cost `V_β(P)` of §3: the general `V_β` of the two-state instance,
evaluated at the belief `(1 − P, P)`. -/
noncomputable def V2 (β π C I R : ℝ) (P : ℝ) : ℝ :=
  (twoState β π C I R).Vβ (belief P)

/-- The scalar belief update `TP = P + π − πP` of §3, p. 590. -/
def T2 (π P : ℝ) : ℝ := P + π - π * P

/-- The right side of (3), p. 590, for a function `V` on `[0, 1]`, at the belief `P` and the action
`a`:

* produce: `CP + βV(TP)`;
* inspect: `I + βPV(1) + β(1 − P)V(π)`;
* revise: `R + βV(π)`. -/
def rhs3 (β π C I R : ℝ) (V : ℝ → ℝ) (P : ℝ) : Action → ℝ
  | .produce => C * P + β * V (T2 π P)
  | .inspect => I + β * P * V 1 + β * (1 - P) * V π
  | .revise => R + β * V π

/-- The β-optimal region of the action `a` in the two-state model: the `P ∈ [0, 1]` at which `a`
attains the minimum in (3), i.e. `V_β(P)` equals the right side of (3) for `a`. -/
noncomputable def region2 (β π C I R : ℝ) (a : Action) : Set ℝ :=
  {P | P ∈ Set.Icc (0 : ℝ) 1 ∧ V2 β π C I R P = rhs3 β π C I R (V2 β π C I R) P a}

/-- A stationary rule `δ : [0, 1] → {produce, inspect, revise}` is β-optimal if at every belief
`P ∈ [0, 1]` it selects an action minimizing the right side of (3) (the paper's criterion on p. 588,
quoted from Blackwell [1]: "any rule `R_β` which when in state `P` selects an action which minimizes
the right side of (1) is β-optimal"). -/
noncomputable def IsOptimalRule (β π C I R : ℝ) (δ : ℝ → Action) : Prop :=
  ∀ P ∈ Set.Icc (0 : ℝ) 1, rhs3 β π C I R (V2 β π C I R) P (δ P) = V2 β π C I R P

/-- The four-region rule of Theorem 3.3, p. 590: produce for `P < P₁`, inspect for `P₁ ≤ P < P₂`,
produce for `P₂ ≤ P < P₃`, revise for `P ≥ P₃`. -/
noncomputable def fourRegion (P₁ P₂ P₃ : ℝ) (P : ℝ) : Action :=
  if P < P₁ then .produce
  else if P < P₂ then .inspect
  else if P < P₃ then .produce
  else .revise

end RossQC.Regions


