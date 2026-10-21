-- Prove2me | Definitions.Def_MatrixAnalytic_FirstPassage_Chain
-- name    : MatrixAnalytic_FirstPassage_Chain
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-20T15:45:30.290201+00:00
-- url     : https://prove2.me/theorems/75933e29-5f3a-4140-a40e-b08a346af08c
-- title:
--   Taboo path sums of a Markov chain — trajectory weights, avoidance tails, expected hitting times, hitting distributions, irreducibility
-- statement:
--   Let $V$ be a set of states and $P=(P_{xy})_{x,y\in V}$ a real matrix, read as the one-step transition probabilities of a discrete-time Markov chain $(X_k)_{k\ge0}$. For a set of states $A$ let $\tau_A=\inf\{k>0 : X_k\in A\}$ be its hitting time (first visit after time $0$, as in the book's $\tau(M)=\inf\{k>0 : X_k\in\ell(M)\}$). All quantities below take values in $[0,\infty]$, so an infinite expectation is $\infty$.
--
--   1. The **weight** of a trajectory $\omega=(\omega_0,\dots,\omega_t)$ is $P_{\omega_0\omega_1}\cdots P_{\omega_{t-1}\omega_t}$, the probability, starting from $\omega_0$, of following it.
--   2. The **avoidance tail** $\mathrm P[\tau_A>t\mid X_0=x]$ is the total weight of the trajectories of length $t$ starting at $x$ whose states at times $1,\dots,t$ all lie outside $A$ (it equals $1$ for $t=0$).
--   3. The **expected hitting time** is the tail sum
--   $$\mathrm E[\tau_A\mid X_0=x]=\sum_{t\ge0}\mathrm P[\tau_A>t\mid X_0=x].$$
--   4. The **hitting distribution** $\mathrm P[\tau_A<\infty,\ X_{\tau_A}=y\mid X_0=x]$ is the total weight of the trajectories $x=\omega_0,\omega_1,\dots,\omega_{t+1}=y$, $t\ge0$, with $y\in A$ and $\omega_1,\dots,\omega_t\notin A$.
--   5. $P$ is **irreducible on** a set $S$ of states if between any two states of $S$ there is a finite trajectory of positive weight.
--
--   These are the probabilistic objects of Chapter 11: first passage times and first passage probabilities between levels are expected hitting times and hitting distributions of sets of states.
--
--   **Formalization Note** Values are in `ℝ≥0∞` (each one-step probability enters through `ENNReal.ofReal`), so every series exists and no expectation takes a junk value. The bodies follow the platform definition `mm_countable` (`pathWeightC`, `setAvoidTailC`), restated locally because that module is not importable in this environment.
-- source:
--   Latouche & Ramaswami, Introduction to Matrix Analytic Methods in Stochastic Modeling, SIAM 1999, p. 240 (Section 11.1: τ(M) = inf{k > 0 : X_k ∈ ℓ(M)}), p. 242 (t_{n→k}, Γ_{n→k}), p. 245 (θ^{(n)}); restates the path-sum encoding of the platform definition mm_countable

import Mathlib

namespace MatrixAnalytic.FirstPassage

noncomputable section

open scoped ENNReal

/-!
Taboo probabilities and expected hitting times of a discrete-time Markov chain with transition
matrix `P` on a state space `V`, as used in Chapter 11 of Latouche & Ramaswami (pp. 239–248).
Every probability is a sum, over finite trajectories, of products of one-step transition
probabilities, and every expected time is the tail sum `E[τ] = Σ_{t ≥ 0} P[τ > t]`; all values
are in `ℝ≥0∞`, so an infinite expectation is `⊤` and never a junk value. Hitting times are
`τ_A = inf{k > 0 : X_k ∈ A}` (p. 240). These follow the path-sum encoding of the platform
definitions `mm_countable` (`pathWeightC`, `setAvoidTailC`).
-/

variable {V : Type*}

/-- The weight `P_{ω₀ω₁} ⋯ P_{ω_{t-1}ω_t}` of a trajectory of length `t`, in `ℝ≥0∞`: the
probability, starting from `ω₀`, that `X₁ = ω₁, …, X_t = ω_t`. -/
def pathWeight (P : V → V → ℝ) {t : ℕ} (ω : Fin (t + 1) → V) : ℝ≥0∞ :=
  ∏ m : Fin t, ENNReal.ofReal (P (ω m.castSucc) (ω m.succ))

open Classical in
/-- `P[X₁ ∉ A, …, X_t ∉ A | X₀ = x] = P[τ_A > t | X₀ = x]` with `τ_A = inf{k > 0 : X_k ∈ A}`
(equal to `1` for `t = 0`). -/
def avoidTail (P : V → V → ℝ) (A : Set V) (x : V) (t : ℕ) : ℝ≥0∞ :=
  ∑' ω : Fin (t + 1) → V,
    if ω 0 = x ∧ ∀ m : Fin (t + 1), m ≠ 0 → ω m ∉ A then pathWeight P ω else 0

/-- The expected hitting time `E[τ_A | X₀ = x]`, `τ_A = inf{k > 0 : X_k ∈ A}`, as the tail sum
`Σ_{t ≥ 0} P[τ_A > t | X₀ = x]` (it is `⊤` when the expectation is infinite, in particular when
`A` is missed with positive probability). -/
def expHitTime (P : V → V → ℝ) (A : Set V) (x : V) : ℝ≥0∞ :=
  ∑' t : ℕ, avoidTail P A x t

open Classical in
/-- The hitting distribution `P[τ_A < ∞ and X_{τ_A} = y | X₀ = x]`: the sum over `t ≥ 0` of the
probabilities of the trajectories `x = ω₀, ω₁, …, ω_{t+1} = y` with `y ∈ A` and
`ω₁, …, ω_t ∉ A`. -/
def hitDist (P : V → V → ℝ) (A : Set V) (x y : V) : ℝ≥0∞ :=
  ∑' t : ℕ, ∑' ω : Fin (t + 2) → V,
    if ω 0 = x ∧ ω (Fin.last (t + 1)) = y ∧ y ∈ A ∧
        ∀ m : Fin (t + 2), m ≠ 0 → m ≠ Fin.last (t + 1) → ω m ∉ A
    then pathWeight P ω else 0

/-- Irreducibility of `P` on the set of states `S`: from every state of `S` there is a finite
trajectory of positive probability to every state of `S`. -/
def IrreducibleOn (P : V → V → ℝ) (S : Set V) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, ∃ t : ℕ, ∃ ω : Fin (t + 1) → V,
    ω 0 = x ∧ ω (Fin.last t) = y ∧ pathWeight P ω ≠ 0

end

end MatrixAnalytic.FirstPassage


