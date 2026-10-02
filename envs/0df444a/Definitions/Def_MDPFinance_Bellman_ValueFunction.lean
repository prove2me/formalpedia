-- Prove2me | Definitions.Def_MDPFinance_Bellman_ValueFunction
-- name    : MDPFinance_Bellman_ValueFunction
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T20:10:58.304128+00:00
-- url     : https://prove2.me/theorems/d2bbb354-e883-4f3c-8f1d-19befdf7d325
-- title:
--   The value of a policy and the value function
-- statement:
--   For an $N$-stage policy $\pi = (f_0,\dots,f_{N-1})$, time $n$, and state $x$, the **value of
--   $\pi$ from $(n,x)$** is the expected total reward accrued by following $\pi$ from state $x$ at
--   time $n$ to the terminal time $N$:
--
--   $$
--   V_n^\pi(x) := \mathbb{E}^\pi_{n,x}\!\left[\sum_{k=n}^{N-1} r_k\bigl(X_k, f_k(X_k)\bigr) +
--   g_N(X_N)\right].
--   $$
--
--   The **value function** is $V_n(x) := \sup_\pi V_n^\pi(x)$, the maximal expected total reward
--   attainable from $(n,x)$ over every $N$-stage policy. A policy $\pi$ is **optimal** if
--   $V_0^\pi = V_0$.
--
--   This mission does not construct the canonical path measure $\mathbb{P}^\pi_x$ on the full
--   trajectory space $\Omega = E^{N+1}$ (via the Ionescu–Tulcea theorem, as the book does); instead
--   $V_n^\pi$ is built directly as an explicit backward recursion over the one-step kernels $Q_k$,
--   carrying the reward accrued so far as an accumulator that is only added into the total at the
--   very end. This computes exactly the same quantity — by the tower property of conditional
--   expectation, the two constructions agree — while remaining independent enough of the operators
--   $T_n^{f}$ for Theorem 2.3.4 (the Reward Iteration) to be a genuine, non-definitional theorem
--   about it. A companion auxiliary, `stepKernel`, gives the law of $X_m$ given $X_n = x$ under a
--   fixed policy, used to state the almost-sure conclusion of Theorem 2.3.12 without the full path
--   measure.
--
--   **Formalization Note.** `EFromToAcc` implements the accumulator recursion described above;
--   `Vpi`, `V` are the specializations to the terminal time $N$ with terminal payoff $g_N$. `TChain`
--   and `TfChain` are the $k$-fold compositions of $T_n$, respectively $T_n^{f_n}$, used to state
--   part (b) of Theorem 2.3.4 and Theorem 2.3.8.
--
--   **Integrability Assumption (AN)** (p. 17). For $n = 0,\dots,N$ and $x\in E$,
--   $$\delta_n^N(x) := \sup_\pi \mathbb{E}^\pi_{n,x}\Big[\sum_{k=n}^{N-1} r_k^+(X_k, f_k(X_k)) +
--   g_N^+(X_N)\Big] < \infty .$$
--   The book assumes (AN) for the $N$-stage problems throughout; it is what makes every
--   expectation $V_n^\pi(x)$ well defined and keeps $V_n^\pi(x) \le V_n(x) \le \delta_n^N(x) <
--   \infty$. `IntegrabilityAssumption M` states it with `deltaN`, the value of the model
--   `M.posPart` whose rewards are the positive parts $r_n^+$, $g_N^+$; the results of Section 2.3
--   carry it as an explicit hypothesis.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 18, unnumbered display defining $V_n^\pi$ and $V_n$

import Mathlib
import Definitions.Def_MDPFinance_Bellman_Model
import Definitions.Def_MDPFinance_Bellman_Policy
import Definitions.Def_MDPFinance_Bellman_Operators

open MeasureTheory ProbabilityTheory

namespace MDPFinance.Bellman

variable {E A : Type*} [MeasurableSpace E] [MeasurableSpace A] {N : ℕ}

/-- Auxiliary accumulator for the expected reward-to-go under a fixed policy `π`
(Bäuerle–Rieder, p. 18, PDF 33, unnumbered display defining `V_n^π`): starting at time `n` in
state `x` with reward already accrued `acc`, and running for `k` more stages toward a terminal
payoff `term`, `EFromToAcc M π term k n x acc` computes
`acc + 𝔼^π_{n,x}[Σ_{j=0}^{k-1} r_{n+j}(X_{n+j}, f_{n+j}(X_{n+j})) + term(X_{n+k})]`.
The accumulator carries the reward-so-far *outside* every integral rather than folding it into a
recursively-defined value (which would make `Theorem 2.3.4`'s recursion true by unfolding): the
accumulator is only consumed once, at `k = 0`, so recovering the one-step recursion for
`k = m - n` requires the (short but genuine) fact that the accumulator enters linearly. -/
noncomputable def EFromToAcc (M : MarkovDecisionModel E A N) (π : Policy M) (term : E → EReal) :
    (k : ℕ) → (n : ℕ) → (x : E) → (acc : EReal) → EReal
  | 0, _, x, acc => acc + term x
  | (k + 1), n, x, acc =>
      erealIntegral (M.Q n (x, π.1 n x))
        (fun x' => EFromToAcc M π term k (n + 1) x' (acc + (M.r n (x, π.1 n x) : EReal)))

/-- The expected reward-to-go `𝔼^π_{n,x}[Σ_{k=n}^{m-1} r_k(X_k, f_k(X_k)) + term(X_m)]` under a
fixed policy `π`, from time `n` to time `m ≥ n`, with terminal payoff `term` at time `m`. -/
noncomputable def EFromTo (M : MarkovDecisionModel E A N) (π : Policy M) (n m : ℕ) (x : E)
    (term : E → EReal) : EReal :=
  EFromToAcc M π term (m - n) n x 0

/-- The value `V_n^π(x)` of policy `π` from time `n` in state `x` (Bäuerle–Rieder, p. 18, PDF 33,
unnumbered display): `V_n^π(x) := 𝔼^π_{n,x}[Σ_{k=n}^{N-1} r_k(X_k,f_k(X_k)) + g_N(X_N)]`. -/
noncomputable def Vpi (M : MarkovDecisionModel E A N) (π : Policy M) (n : ℕ) (x : E) : EReal :=
  EFromTo M π n N x (fun x => (M.g x : EReal))

/-- The value function `V_n(x) := sup_π V_n^π(x)` (Bäuerle–Rieder, p. 18, PDF 33, unnumbered
display), the maximal expected total reward from time `n` in state `x`. -/
noncomputable def V (M : MarkovDecisionModel E A N) (n : ℕ) (x : E) : EReal :=
  ⨆ π : Policy M, Vpi M π n x

/-- Auxiliary for Theorem 2.3.8b: `T_n T_{n+1} ⋯ T_{n+k-1}` applied to a terminal function,
i.e. `k` applications of the maximal-reward operator starting at time `n`, innermost first. -/
noncomputable def TChain (M : MarkovDecisionModel E A N) : (k : ℕ) → (n : ℕ) → (E → EReal) →
    (E → EReal)
  | 0, _, v => v
  | (k + 1), n, v => T M n (TChain M k (n + 1) v)

/-- Auxiliary for Theorem 2.3.4b: `T_n^{f_n} T_{n+1}^{f_{n+1}} ⋯ T_{n+k-1}^{f_{n+k-1}}` applied to
a terminal function, under a fixed policy `π`. -/
noncomputable def TfChain (M : MarkovDecisionModel E A N) (π : Policy M) : (k : ℕ) → (n : ℕ) →
    (E → EReal) → (E → EReal)
  | 0, _, v => v
  | (k + 1), n, v => Tf M n (TfChain M π k (n + 1) v) (π.1 n)

/-- The one-step transition kernel of the state process under a fixed policy `π` at time `n`:
`Q_n(·|x, f_n(x))`, pulled back along `x ↦ (x, f_n(x))`. -/
noncomputable def oneStepKernel (M : MarkovDecisionModel E A N) (π : Policy M) (n : ℕ) :
    Kernel E E :=
  (M.Q n).comap (fun x => (x, π.1 n x)) ((measurable_id.prodMk (π.2.1 n)))

/-- The `k`-step transition kernel of the state process under `π`, starting at time `n`: the law
of `X_{n+k}` given `X_n`. Used to state Theorem 2.3.12's `ℙ^{π}_{n,x}`-almost-sure conclusion
without constructing the full canonical path measure on `Ω = E^{N+1}`. -/
noncomputable def stepKernelAux (M : MarkovDecisionModel E A N) (π : Policy M) : (k : ℕ) →
    (n : ℕ) → Kernel E E
  | 0, _ => Kernel.id
  | (k + 1), n => Kernel.comp (stepKernelAux M π k (n + 1)) (oneStepKernel M π n)

/-- `stepKernel M π n m`: the law of `X_m` given `X_n = x` under policy `π`, for `n ≤ m`. -/
noncomputable def stepKernel (M : MarkovDecisionModel E A N) (π : Policy M) (n m : ℕ) :
    Kernel E E :=
  stepKernelAux M π (m - n) n

/-- The model with the one-stage and terminal rewards replaced by their positive parts `r_n^+`,
`g_N^+` (same `D_n`, `Q_n`), used to state the Integrability Assumption (AN). -/
noncomputable def MarkovDecisionModel.posPart (M : MarkovDecisionModel E A N) :
    MarkovDecisionModel E A N :=
  { M with
    r := fun n xa => max (M.r n xa) 0
    hr_meas := fun n hn => (M.hr_meas n hn).max measurable_const
    g := fun x => max (M.g x) 0
    hg_meas := M.hg_meas.max measurable_const }

/-- `δ_n^N(x) := sup_π 𝔼^π_{n,x}[Σ_{k=n}^{N-1} r_k^+(X_k, f_k(X_k)) + g_N^+(X_N)]` (Bäuerle–Rieder,
p. 17, PDF 32): the maximal expected total *positive* reward from `(n,x)`. -/
noncomputable def deltaN (M : MarkovDecisionModel E A N) (n : ℕ) (x : E) : EReal :=
  ⨆ π : Policy M, EFromTo M.posPart ⟨π.1, π.2⟩ n N x (fun x => ((max (M.g x) 0 : ℝ) : EReal))

/-- The Integrability Assumption (AN) (Bäuerle–Rieder, p. 17, PDF 32): `δ_n^N(x) < ∞` for all
`n = 0, …, N` and `x ∈ E`. The book assumes (AN) "for the N-stage Markov Decision Problems
throughout the following chapters"; it is what makes every expectation `V_n^π(x)` well defined
and keeps `V_n^π`, `V_n` in `[-∞, ∞)`. -/
def IntegrabilityAssumption (M : MarkovDecisionModel E A N) : Prop :=
  ∀ n ≤ N, ∀ x, deltaN M n x < ⊤

end MDPFinance.Bellman


