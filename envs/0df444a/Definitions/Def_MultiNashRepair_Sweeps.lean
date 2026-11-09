-- Prove2me | Definitions.Def_MultiNashRepair_Sweeps
-- name    : MultiNashRepair_Sweeps
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:29:43.61237+00:00
-- url     : https://prove2.me/theorems/cf28f65e-3033-4a5c-a59e-32314e298c43
-- title:
--   The profile updates: descent (3.2), activation (3.7), reverse sweep (3.8), correction (3.9)–(3.10)
-- statement:
--   Players are processed with index $0$ standing for the paper's player $1$.
--
--   1. **Descent** (3.2): $x^+_j=(1-\eta Z_j)x_j+\eta\sum_b z_{j,b}e_b$ with $Z_j=\sum_b z_{j,b}$, and the all-base factor $P=\prod_j(1-\eta Z_j)$.
--   2. **Activation** (3.7): $y_i=(1-t\gamma_i)x_i+t\gamma_ib_i$.
--   3. **Reverse sweep** (3.8): with $P_{i-1}=1-\sum_{j<i}\delta_j$ and $p_i=\delta_i/P_{i-1}$, $\tilde x_j=(1-p_j)y_j+p_je_{a^{\mathrm{rev}}_j}$, where, processing players $m,\dots,1$, $a^{\mathrm{rev}}_i$ is a pure best response of player $i$ to $y_j$ for $j<i$ and to the already updated $\tilde x_j$ for $j>i$.
--   4. **Frozen deficits** (3.9): $e_i=\bigl((C_{\mathrm{raw}}\varsigma+D)/m-q_i(\tilde x)\bigr)_+$.
--   5. **Forward correction** (3.10): $\theta_i=e_i/(1+\sum_{j\le i}e_j)$ and $x^+_j=(1-\theta_j)\tilde x_j+\theta_je_{a^{\mathrm{cor}}_j}$, where, processing players $1,\dots,m$, $a^{\mathrm{cor}}_i$ is a pure best response of player $i$ to $x^+_j$ for $j<i$ and to $\tilde x_j$ for $j>i$.
--
--   **Formalization Note** The sequential sweeps are written in closed form: the best-response conditions refer to the final profiles of earlier-processed players, which is what the sequential description computes. A player's own coordinate does not enter her pure-action payoffs. Division is total ($x/0=0$); positivity of every denominator is a conclusion of the milestones, never an assumption.
-- source:
--   J. Tang, S. Ding, C. Fang, Breaking the One-Player Extension Barrier: History-Aware Repair for Multiplayer Approximate Nash Equilibria, arXiv:2611.06076 (preprint; held version, sha256 34b911ed…5c14), (3.2), p.7; (3.7)–(3.9), p.9; (3.10), p.10

import Mathlib
import Definitions.Def_MultiNashRepair_Regret

open NashAmplification.Filtering (Mixed Utility Tuple)
open Finset

noncomputable section

namespace MultiNashRepair

variable {m : ℕ} {n : Fin m → ℕ}

/-- **The profile updates of Algorithm 1** (Tang, Ding, Fang, arXiv:2611.06076, (3.2), (3.7),
(3.8), (3.9), (3.10), pp.7–10).

The descent profile (3.2): `x⁺_j = (1 − η Z_j) x_j + η Σ_b z_{j,b} e_b` with `Z_j = Σ_b z_{j,b}`. -/
def descentProfile (x : Mixed n) (η : ℝ) (z : (j : Fin m) → Fin (n j) → ℝ) : Mixed n :=
  fun j => (1 - η * ∑ b, z j b) • x j + η • ∑ b, z j b • ePure b

/-- The all-base factor `P = Π_j (1 − η Z_j)` of a descent ((3.2), p.7). -/
def descentFactor (η : ℝ) (z : (j : Fin m) → Fin (n j) → ℝ) : ℝ :=
  ∏ j, (1 - η * ∑ b, z j b)

/-- Activation (3.7): `y_i = (1 − t γ_i) x_i + t γ_i b_i`. -/
def actY (x b : Mixed n) (t : ℝ) (γ : Fin m → ℝ) : Mixed n :=
  fun i => (1 - t * γ i) • x i + (t * γ i) • b i

/-- The reverse-sweep mixing probability `p_i = δ_i / P_{i−1}`, `P_{i−1} = 1 − Σ_{j<i} δ_j`
((3.8), p.9). Players are `Fin m`; index `0` is the paper's player 1. -/
def revProb (δ : Fin m → ℝ) (i : Fin m) : ℝ :=
  δ i / (1 - ∑ j ∈ univ.filter (· < i), δ j)

/-- The raw profile of the reverse sweep: `x̃_j = (1 − p_j) y_j + p_j e_{a^{rev}_j}` ((3.8)). -/
def revSweep (y : Mixed n) (δ : Fin m → ℝ) (arev : (i : Fin m) → Fin (n i)) : Mixed n :=
  fun j => (1 - revProb δ j) • y j + revProb δ j • ePure (arev j)

/-- The reverse-sweep actions are pure best responses as the sweep requires: processing players
`m, m − 1, …, 1`, player `i`'s action `a^{rev}_i` maximizes her payoff against `y_j` for `j < i`
and against the already updated `x̃_j` for `j > i` (p.9; p.24). Her own coordinate does not
enter `purePayoff`. -/
def IsRevBR (u : Utility n) (y : Mixed n) (δ : Fin m → ℝ) (arev : (i : Fin m) → Fin (n i)) :
    Prop :=
  ∀ (i : Fin m) (a : Fin (n i)),
    DGPNash.NashMap.purePayoff u (fun j => if j < i then y j else revSweep y δ arev j) i a ≤
      DGPNash.NashMap.purePayoff u (fun j => if j < i then y j else revSweep y δ arev j) i
        (arev i)

/-- The frozen correction deficit `e_i = ((C_raw ς + D)/m − q_i(x̃))_+` ((3.9), p.9). -/
def corrDef (u : Utility n) (ς Craw D : ℝ) (xt : Mixed n) (i : Fin m) : ℝ :=
  max 0 ((Craw * ς + D) / m - qi u xt i)

/-- The forward-correction probability `θ_i = e_i / (1 + Σ_{j ≤ i} e_j)` ((3.10), p.10). -/
def fwdProb (e : Fin m → ℝ) (i : Fin m) : ℝ :=
  e i / (1 + ∑ j ∈ univ.filter (· ≤ i), e j)

/-- The corrected profile: `x⁺_j = (1 − θ_j) x̃_j + θ_j e_{a^{cor}_j}` ((3.10), p.10). -/
def fwdSweep (xt : Mixed n) (e : Fin m → ℝ) (acor : (i : Fin m) → Fin (n i)) : Mixed n :=
  fun j => (1 - fwdProb e j) • xt j + fwdProb e j • ePure (acor j)

/-- The forward-sweep actions are pure best responses to the current opponents: processing
players `1, …, m`, player `i`'s action `a^{cor}_i` maximizes her payoff against the corrected
`x⁺_j` for `j < i` and the raw `x̃_j` for `j > i` (p.10). -/
def IsFwdBR (u : Utility n) (xt : Mixed n) (e : Fin m → ℝ) (acor : (i : Fin m) → Fin (n i)) :
    Prop :=
  ∀ (i : Fin m) (a : Fin (n i)),
    DGPNash.NashMap.purePayoff u (fun j => if j < i then fwdSweep xt e acor j else xt j) i a ≤
      DGPNash.NashMap.purePayoff u (fun j => if j < i then fwdSweep xt e acor j else xt j) i
        (acor i)

end MultiNashRepair


