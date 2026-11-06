-- Prove2me | Definitions.Def_FullPathSCC_Model_fullPathUtility
-- name    : FullPathSCC_Model_fullPathUtility
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:22:19.199831+00:00
-- url     : https://prove2.me/theorems/b0546e50-157b-4ef0-819b-d50f4d14b756
-- title:
--   (6), (A.5) — plans, the state process along disaster paths, and the full-path utility $J_t^\pi(x)$
-- statement:
--   A **plan** started at time $t$ in a state $x$ is a deterministic rule that chooses the action $(C_n,\mu_n)$ at step $n$ (calendar time $t+n$) as a function of the disaster states $\omega_0,\dots,\omega_{n-1}$ realized so far. Along a disaster path $\omega=(\omega_0,\dots,\omega_{N-t-1})\in\mathcal S^{N-t}$ the plan generates the states $X_0=x$ and
--
--   $$
--   X_{n+1}=\bigl(g_{K,t+n}(K_n,T_n,\vartheta_n,C_n,\mu_n),\ g_{T,t+n}(K_n,T_n,\mu_n),\ \omega_n\bigr),\qquad X_n=(K_n,T_n,\vartheta_n).
--   $$
--
--   The plan is **admissible** from $(t,x)$ if along every history each action satisfies $0\le C_n\le K_n$, $0\le\mu_n\le1$. The path has probability $P(\omega)=\prod_{n<N-t}p_{\vartheta_n,\omega_n}(T_n)$, and the **full-path utility** of the plan $\pi$ is
--
--   $$
--   J_t^\pi(x)=-\frac1{k\beta^t}\ln\sum_{\omega\in\mathcal S^{N-t}}P(\omega)\exp\Bigl(-k\beta^t\Bigl(\sum_{n=0}^{N-t-1}\beta^nU_{t+n}(C_n)+\beta^{N-t}h(X_{N-t})\Bigr)\Bigr).
--   $$
--
--   At $t=0$ this is the right side of (A.5); in general it is (6) with the terminal value in place of the last utility. The definition also provides the plan induced by a Markov policy $\varphi_t(K,T,\vartheta)$ (take $\varphi_{t+n}(X_n)$ at step $n$) and the continuation $\pi_j$ of a plan after a first transition to $j$.
--
--   **Formalization Note** The expectation is written as the explicit finite sum over disaster paths, not through the recursion of Proposition A.1. Capital and temperature are deterministic functions of the start state and the disaster history, so plans are functions of that history.
-- source:
--   Zhao, Basu, Lontzek & Schmedders, The Social Cost of Carbon When We Wish for Full-Path Robustness, Management Science 69(12) (2023), doi:10.1287/mnsc.2023.4736, (6), p.7589; (A.5), p.7601; (A.10), p.7602

import Mathlib
import Definitions.Def_FullPathSCC_Model

namespace FullPathSCC

/-- A deterministic, history-dependent consumption–abatement plan, started at some time `t` from a
fixed state: `π n ω` is the action `(C, μ)` taken at step `n` (calendar time `t + n`) after the
disaster states `ω 0, …, ω (n−1)` (the paper's `ϑ_{t+1}, …, ϑ_{t+n}`) have been realized
(Management Science 69(12) (2023), (A.10), p.7602: the maximum over `{(C_t, μ_t)}_{0≤t≤N−1}`).

**Formalization Note** Capital and temperature are deterministic functions of the start state and
the realized disaster states, so a history of disaster states determines the whole history of the
state process. -/
def Plan (S : Type*) := (n : ℕ) → (Fin n → S) → ℝ × ℝ

namespace Model

variable {S : Type*}

/-- The first `n` disaster states `ω 0, …, ω (n−1)` of a path `ω` of length `m ≥ n`. -/
def pathPrefix {m : ℕ} (ω : Fin m → S) (n : ℕ) (hn : n ≤ m) : Fin n → S :=
  fun i => ω (Fin.castLE hn i)

/-- The state `X_n = (K_{t+n}, T_{t+n}, ϑ_{t+n})` reached after `n` steps from the state `x` at time
`t` under the plan `π`, along the realized disaster states `ω` (Management Science 69(12) (2023),
(8), p.7591): `X_0 = x` and
`X_{n+1} = (g_{K,t+n}(K_n, T_n, ϑ_n, C_n, μ_n), g_{T,t+n}(K_n, T_n, μ_n), ω n)`. -/
def trajectory (M : Model S) (t : ℕ) (x : State S) (π : Plan S) :
    (n : ℕ) → (Fin n → S) → State S
  | 0, _ => x
  | n + 1, ω => M.next (t + n) (trajectory M t x π n (Fin.init ω)) (π n (Fin.init ω))
      (ω (Fin.last n))

/-- A plan is admissible from the state `x` at time `t` when along every history of disaster
states every action is admissible (`C ∈ [0, K]`, `μ ∈ [0, 1]`) at the state where it is taken,
for the steps `n < N − t` (Management Science 69(12) (2023), §3.1, p.7591, and (A.10), p.7602). -/
def PlanAdmissible (M : Model S) (t : ℕ) (x : State S) (π : Plan S) : Prop :=
  ∀ n, n < M.N - t → ∀ ω : Fin n → S, AdmissibleAction (M.trajectory t x π n ω) (π n ω)

/-- The probability `∏_{n < N−t} p_{ϑ_n, ω n}(T_n)` of the disaster path `ω` from the state `x` at
time `t` under `π` (Management Science 69(12) (2023), (7), p.7591, and (A.6), p.7601). -/
noncomputable def pathProb (M : Model S) (t : ℕ) (x : State S) (π : Plan S)
    (ω : Fin (M.N - t) → S) : ℝ :=
  ∏ n : Fin (M.N - t),
    M.p (M.trajectory t x π n (pathPrefix ω n n.isLt.le)).2.2 (ω n)
      (M.trajectory t x π n (pathPrefix ω n n.isLt.le)).2.1

/-- The discounted path utility `Σ_{n<N−t} β^n U_{t+n}(C_n) + β^{N−t} h(X_{N−t})` along the
disaster path `ω` (Management Science 69(12) (2023), (6), p.7589, and (A.5), p.7601). -/
noncomputable def pathUtility (M : Model S) (t : ℕ) (x : State S) (π : Plan S)
    (ω : Fin (M.N - t) → S) : ℝ :=
  (∑ n : Fin (M.N - t), M.β ^ (n : ℕ) * M.U (t + n) (π n (pathPrefix ω n n.isLt.le)).1) +
    M.β ^ (M.N - t) * M.h (M.trajectory t x π (M.N - t) ω).1
      (M.trajectory t x π (M.N - t) ω).2.1 (M.trajectory t x π (M.N - t) ω).2.2

/-- The full-path utility of the plan `π` from the state `x` at time `t`
(Management Science 69(12) (2023), (6), p.7589, and (A.5), p.7601):
`J_t^π(x) = −(1/(kβ^t)) ln Σ_{ω ∈ 𝒮^{N−t}} P(ω) exp(−kβ^t (Σ_{n<N−t} β^n U_{t+n}(C_n) + β^{N−t} h(X_{N−t})))`,
where `P(ω)` is `pathProb`. At `t = 0` this is the right side of (A.5).

**Formalization Note** The expectation is the explicit finite sum over the `|𝒮|^{N−t}` disaster
paths, each weighted by the product of its transition probabilities; it is not defined through the
recursion of Proposition A.1. The terminal term is `h` at the terminal state (the paper's
`β^N h(C_N)`). -/
noncomputable def fullPathUtility [Fintype S] (M : Model S) (t : ℕ) (x : State S)
    (π : Plan S) : ℝ :=
  -(1 / M.kt t) * Real.log (∑ ω : Fin (M.N - t) → S,
    M.pathProb t x π ω * Real.exp (-(M.kt t) * M.pathUtility t x π ω))

/-- The state process under a (nonstationary) Markov policy `φ_t(K, T, ϑ)` started at the state `x`
at time `t`, along the realized disaster states (Management Science 69(12) (2023), Theorem A.2,
p.7601). -/
def markovTrajectory (M : Model S) (t : ℕ) (x : State S) (φ : ℕ → State S → ℝ × ℝ) :
    (n : ℕ) → (Fin n → S) → State S
  | 0, _ => x
  | n + 1, ω =>
      M.next (t + n) (markovTrajectory M t x φ n (Fin.init ω))
        (φ (t + n) (markovTrajectory M t x φ n (Fin.init ω))) (ω (Fin.last n))

/-- The plan induced by the Markov policy `φ` from the state `x` at time `t`: at step `n` take
`φ_{t+n}(X_n)` (Management Science 69(12) (2023), Theorem A.2, p.7601). -/
def markovPlan (M : Model S) (t : ℕ) (x : State S) (φ : ℕ → State S → ℝ × ℝ) : Plan S :=
  fun n ω => φ (t + n) (M.markovTrajectory t x φ n ω)

/-- The continuation of the plan `π` after the first disaster transition to `j`:
`π_j n ω' = π (n+1) (j, ω')` (used in Proposition A.1, Management Science 69(12) (2023), p.7600). -/
def shiftPlan (π : Plan S) (j : S) : Plan S :=
  fun n ω => π (n + 1) (Fin.cons j ω)

end Model

end FullPathSCC


