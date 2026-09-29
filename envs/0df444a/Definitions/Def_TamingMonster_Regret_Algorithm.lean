-- Prove2me | Definitions.Def_TamingMonster_Regret_Algorithm
-- name    : TamingMonster_Regret_Algorithm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T08:19:39.169815+00:00
-- url     : https://prove2.me/theorems/783c98a5-8355-47f9-a62d-7b8427f5033b
-- title:
--   ILOVETOCONBANDITS (Algorithm 1) as a process, and its regret after $T$ rounds
-- statement:
--   This file defines a run of ILOVETOCONBANDITS (Algorithm 1 of Agarwal et al. 2014) and its empirical cumulative regret.
--
--   The algorithm's parameters are a finite policy class $\Pi$, a failure probability $\delta$, an epoch schedule $0=\tau_0<\tau_1<\cdots$, and two free rules that see only the observable history:
--
--   1. a **tie-breaking rule** returning $\pi_t\in\arg\max_{\pi\in\Pi}\widehat{\mathcal R}_t(\pi)$ from $H_t$ (on the empty history every policy is a maximizer, so $\pi_0$ is arbitrary);
--   2. a **selection rule** returning, from $H_{\tau_m}$, the weights $Q_m$ used as "a solution to (OP) with history $H_{\tau_m}$ and minimum probability $\mu_m$" ($Q_0=0$).
--
--   The randomness is a sequence $(x_t,r_t)$, $t=1,2,\dots$, of context/reward-vector pairs and a sequence $u_t\in[0,1]$. In round $t$, in epoch $m=m(t)$, the algorithm forms
--   $$\widetilde Q_{m-1}=Q_{m-1}+\Bigl(1-\sum_{\pi}Q_{m-1}(\pi)\Bigr)\mathbb 1_{\pi_{\tau_{m-1}}},$$
--   draws $a_t$ from $\widetilde Q_{m-1}^{\mu_{m-1}}(\cdot\mid x_t)$ by the inverse distribution function evaluated at $u_t$, and appends the record $(x_t,a_t,r_t(a_t),\widetilde Q_{m-1}^{\mu_{m-1}}(a_t\mid x_t))$ to the history. The **regret after $T$ rounds** is
--   $$\sum_{t=1}^T\bigl(r_t(\pi_\star(x_t))-r_t(a_t)\bigr)$$
--   for a policy $\pi_\star$. The definitions also expose the completed weights $\widetilde Q_m$ of every epoch, as used in §B.3.
--
--   The file also names the three standing conditions on the rules: the tie-breaking rule returns an empirical maximizer on every history; the selection rule solves (OP) with $\mu_m$ on every history of length $\tau_m$, $m\ge1$; and both rules are measurable functions of a history of fixed length.
--
--   **Formalization Note** "Randomly draw $\bar a$ from $\widetilde Q^\mu(\cdot\mid x)$" (Algorithm 4) is implemented with the inverse distribution function: $a$ is the number of actions $b$ with $\sum_{c\le b}\widetilde Q^\mu(c\mid x)<u$, capped at $K-1$. When $u$ is uniform on $[0,1]$ and independent of everything else, $a$ has law $\widetilde Q^{\mu}(\cdot\mid x)$ and is independent of $r_t$ given the past and $x_t$. Theorem 2's hypothesis "(OP) can be solved whenever required" becomes the selection rule, and results are stated for every admissible rule.
-- source:
--   Agarwal, Hsu, Kale, Langford, Li, Schapire, Taming the Monster: A Fast and Simple Algorithm for Contextual Bandits, arXiv:1402.0555v2, p. 3 (§2.1, regret), p. 5 (Algorithm 1), p. 14 (Algorithm 4), p. 15 (§B.3)

import Mathlib
import Definitions.Def_TamingMonster_Regret_Setting

namespace TamingMonster.Regret

open MeasureTheory

variable {X : Type*} {K : ℕ}

/-- The inputs and the free choices of ILOVETOCONBANDITS (Algorithm 1, p. 5):
* `Pi` — the finite policy class `Π ⊆ A^X`;
* `δ` — the allowed failure probability;
* `τ` — the epoch schedule `0 = τ_0 < τ_1 < τ_2 < ⋯`;
* `pick` — the tie-breaking rule for `π_t := argmax_{π ∈ Π} R̂_t(π)`, applied to the observed
  history `H_t` (on the empty history every policy is a maximizer, so `π_0` is arbitrary);
* `sel` — `sel m H` is the weight vector `Q_m` that the algorithm takes as "a solution to (OP)
  with history `H = H_{τ_m}` and minimum probability `μ_m`".
Both rules see only the observable history (a list of records `(x, a, r(a), p(a))`). -/
structure AlgoParams (X : Type*) (K : ℕ) where
  Pi : Finset (X → Fin K)
  δ : ℝ
  τ : ℕ → ℕ
  pick : List (Rec X K) → Pi
  sel : ℕ → List (Rec X K) → Pi → ℝ

/-- `pick` returns an empirical maximizer: `pick H ∈ argmax_{π ∈ Π} R̂(π)` for every history. -/
def AlgoParams.PickIsArgmax (A : AlgoParams X K) : Prop :=
  ∀ h : List (Rec X K), ∀ π : A.Pi,
    ipsEst h (π : X → Fin K) ≤ ipsEst h ((A.pick h : A.Pi) : X → Fin K)

/-- "`Q_m` is a solution to (OP) with history `H_{τ_m}` and minimum probability `μ_m`"
(Algorithm 1, line 7): for every epoch `m ≥ 1` and every history of length `τ_m`,
`sel m H` solves (OP). -/
def AlgoParams.SelSolvesOP (A : AlgoParams X K) : Prop :=
  ∀ m : ℕ, 1 ≤ m → ∀ h : List (Rec X K), h.length = A.τ m →
    IsOPSolution A.Pi (muM A.Pi A.δ A.τ m) h (A.sel m h)

/-- Measurability of the two rules as functions of a history of any fixed length `n`
(histories of length `n` are identified with `Fin n → X × Fin K × ℝ × ℝ`). -/
def AlgoParams.RulesMeasurable [MeasurableSpace X] (A : AlgoParams X K) : Prop :=
  (∀ n : ℕ, ∀ π : A.Pi,
    MeasurableSet {h : Fin n → Rec X K | A.pick (List.ofFn h) = π}) ∧
  (∀ m n : ℕ, ∀ π : A.Pi, Measurable (fun h : Fin n → Rec X K => A.sel m (List.ofFn h) π))

/-- Draw an action from a distribution `p` on `Fin K` using a number `u ∈ [0,1]`, by the inverse
CDF: the action is the number of `b` with `∑_{c ≤ b} p(c) < u` (capped at `K − 1`). When `p` is a
probability vector and `u` is uniform on `[0,1]`, the result `a` has probability `p(a)`. -/
noncomputable def drawAction [NeZero K] (p : Fin K → ℝ) (u : ℝ) : Fin K :=
  ⟨min (Finset.univ.filter (fun b : Fin K => ∑ c ∈ Finset.Iic b, p c < u)).card (K - 1), by
    have := NeZero.pos K
    omega⟩

/-- Weights `Q_m` computed at the end of epoch `m` from the history `H_{τ_m}`:
`Q_0 = 0` and `Q_m = sel m H_{τ_m}` for `m ≥ 1` (Algorithm 1, lines 1 and 7). -/
def AlgoParams.weights (A : AlgoParams X K) (m : ℕ) (h : List (Rec X K)) : A.Pi → ℝ :=
  if m = 0 then 0 else A.sel m h

/-- The record of round `t + 1` of ILOVETOCONBANDITS (Algorithm 1, lines 3–5, with Sample,
Algorithm 4), given the history `h = H_t` of the first `t` rounds, the context/reward pair
`z = (x_{t+1}, r_{t+1})` and the uniform number `u` used for the action draw.
With `m := m(t+1)` the current epoch, it uses `Q_{m−1}`, the default policy `π_{τ_{m−1}}`
(both computed from `H_{τ_{m−1}}`, the first `τ_{m−1}` records of `h`) and `μ_{m−1}`; it forms
`Q̃ = Q_{m−1} + (1 − ∑ Q_{m−1}) 1_{π_{τ_{m−1}}}`, draws `a ∼ Q̃^{μ_{m−1}}(·|x)`, and records
`(x, a, r(a), Q̃^{μ_{m−1}}(a|x))`. -/
noncomputable def AlgoParams.roundRecord [NeZero K] (A : AlgoParams X K) (h : List (Rec X K))
    (t : ℕ) (z : X × (Fin K → ℝ)) (u : ℝ) : Rec X K :=
  let m := epochOf A.τ (t + 1) - 1
  let H := h.take (A.τ m)
  let p : Fin K → ℝ :=
    smoothProj A.Pi (complete A.Pi (A.weights m H) (A.pick H)) (muM A.Pi A.δ A.τ m) z.1
  let a := drawAction p u
  (z.1, a, z.2 a, p a)

/-- The history `H_t` of ILOVETOCONBANDITS after `t` rounds, on the outcome `ω`: round `s`
(`s = 1, 2, …`) uses the context/reward pair `Z s ω = (x_s, r_s)` and the uniform number
`U s ω`. -/
noncomputable def AlgoParams.history [NeZero K] {Ω : Type*} (A : AlgoParams X K)
    (Z : ℕ → Ω → X × (Fin K → ℝ)) (U : ℕ → Ω → ℝ) (ω : Ω) : ℕ → List (Rec X K)
  | 0 => []
  | t + 1 =>
      A.history Z U ω t ++ [A.roundRecord (A.history Z U ω t) t (Z (t + 1) ω) (U (t + 1) ω)]

/-- The action `a_t` chosen by ILOVETOCONBANDITS in round `t ≥ 1`. -/
noncomputable def AlgoParams.action [NeZero K] {Ω : Type*} (A : AlgoParams X K)
    (Z : ℕ → Ω → X × (Fin K → ℝ)) (U : ℕ → Ω → ℝ) (ω : Ω) (t : ℕ) : Fin K :=
  (A.roundRecord (A.history Z U ω (t - 1)) (t - 1) (Z t ω) (U t ω)).act

/-- The (empirical cumulative) regret after `T` rounds (§2.1, p. 3):
`∑_{t=1}^T (r_t(π⋆(x_t)) − r_t(a_t))`, where `(x_t, r_t) = Z t ω`. -/
noncomputable def AlgoParams.cumRegret [NeZero K] {Ω : Type*} (A : AlgoParams X K)
    (Z : ℕ → Ω → X × (Fin K → ℝ)) (U : ℕ → Ω → ℝ) (πstar : X → Fin K) (ω : Ω) (T : ℕ) : ℝ :=
  ∑ t ∈ Finset.Icc 1 T, ((Z t ω).2 (πstar (Z t ω).1) - (Z t ω).2 (A.action Z U ω t))

/-- The completed weights `Q̃_m = Q_m + (1 − ∑_π Q_m(π)) 1_{π_{τ_m}}` of epoch `m` on the
outcome `ω` (Algorithm 4, step 1; §B.3, p. 15), a probability distribution over `Π`. -/
noncomputable def AlgoParams.Qtilde [NeZero K] {Ω : Type*} (A : AlgoParams X K)
    (Z : ℕ → Ω → X × (Fin K → ℝ)) (U : ℕ → Ω → ℝ) (ω : Ω) (m : ℕ) : A.Pi → ℝ :=
  complete A.Pi (A.weights m (A.history Z U ω (A.τ m))) (A.pick (A.history Z U ω (A.τ m)))

end TamingMonster.Regret


