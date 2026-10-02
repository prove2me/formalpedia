-- Prove2me | Definitions.Def_MDPFinance_Stationary_ValueFunction
-- name    : MDPFinance_Stationary_ValueFunction
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T21:44:30.107834+00:00
-- url     : https://prove2.me/theorems/683ce651-c777-470b-9cc9-7c46d573031e
-- title:
--   The stationary value function $J_n$ and reward-iteration machinery
-- statement:
--   Under policy sequence $\pi = (f_0,\dots,f_{n-1})$, $J_n^\pi(x) := \mathbb{E}^\pi_x\bigl[
--   \sum_{k=0}^{n-1} \beta^k r(X_k,f_k(X_k)) + \beta^n g(X_n)\bigr]$; the **value function** is
--   $J_n(x) := \sup_{\pi \in F^n} J_n^\pi(x)$.
--
--   **Formalization Note.** $J_n^\pi$ is built from an explicit accumulator carrying the reward
--   accrued so far and the current discount factor (initialized to $1$, multiplied by $\beta$ at
--   each step) — an independent, expectation-based definition, deliberately *not* defined via the
--   operator composition of Theorem 2.5.3, so that theorem remains non-trivial content rather
--   than a restatement of this definition. `TfComposeChain`/`TChain` are the operator-composition
--   helpers Theorem 2.5.3/2.5.4 equate $J_n^\pi$/$J_n$ with.
--
--   **Integrability Assumption (AN)** (p. 39). For the stationary $N$-stage model,
--   $$\delta_N(x) := \sup_\pi \mathbb{E}^\pi_x\Big[\sum_{k=0}^{N-1}\beta^k r^+(X_k,f_k(X_k)) +
--   \beta^N g^+(X_N)\Big] < \infty, \qquad x\in E,$$
--   the book's standing assumption ("in order to obtain a well-defined stochastic optimization
--   problem"), stated as `IntegrabilityAssumption M N` through `deltaN` and the model `M.posPart`
--   with rewards $r^+$, $g^+$; Theorems 2.5.3 and 2.5.4 carry it explicitly.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 39, PDF 54, §2.5 introduction (unnumbered displays)

import Mathlib
import Definitions.Def_MDPFinance_Stationary_Model
import Definitions.Def_MDPFinance_Stationary_Policy
import Definitions.Def_MDPFinance_Stationary_Operators

open MeasureTheory ProbabilityTheory

namespace MDPFinance.Stationary

variable {E A : Type*} [MeasurableSpace E] [MeasurableSpace A]

/-- Auxiliary accumulator for the expected discounted reward-to-go under a fixed policy sequence
`π` (Bäuerle–Rieder, p. 39, PDF 54, unnumbered display defining `J_n^π`): starting in state `x`
with reward already accrued `acc` and current discount factor `disc` (`= β^{\text{steps so
far}}`), and running for `k` more stages toward terminal payoff `term`, computes
`acc + 𝔼^π_x[Σ_{j=0}^{k-1} disc·β^j r(X_j, π_j(X_j)) + disc·β^k term(X_k)]`. Restated in the
stationary style of `MDPFinance.Bellman.EFromToAcc` (chunk `02a`), with the extra `disc`
argument carrying the accumulated discount factor explicitly (`β` is the same operator at every
step, unlike the non-stationary case). -/
noncomputable def EFromToAcc (M : StationaryMarkovDecisionModel E A) (π : ℕ → E → A)
    (term : E → EReal) : (k : ℕ) → (x : E) → (acc : EReal) → (disc : ℝ) → EReal
  | 0, x, acc, disc => acc + (disc : EReal) * term x
  | (k + 1), x, acc, disc =>
      erealIntegral (M.Q (x, π 0 x))
        (fun x' => EFromToAcc M (fun j => π (j + 1)) term k x'
          (acc + (disc : EReal) * (M.r (x, π 0 x) : EReal)) (disc * M.β))

/-- The value `J_n^π(x)` of policy sequence `π` over `n` stages, from state `x`
(Bäuerle–Rieder, p. 39, PDF 54): `J_n^π(x) := 𝔼^π_x[Σ_{k=0}^{n-1} β^k r(X_k,f_k(X_k)) +
β^n g(X_n)]`. -/
noncomputable def Jpi (M : StationaryMarkovDecisionModel E A) (π : ℕ → E → A) (n : ℕ) (x : E) :
    EReal :=
  EFromToAcc M π (fun x => (M.g x : EReal)) n x 0 1

/-- The value function `J_n(x) := sup_{π ∈ F^n} J_n^π(x)` (Bäuerle–Rieder, p. 39, PDF 54), the
maximal expected total discounted reward over `n` stages from state `x`. -/
noncomputable def J (M : StationaryMarkovDecisionModel E A) (n : ℕ) (x : E) : EReal :=
  ⨆ π ∈ {π : ℕ → E → A | IsPolicySeq M n π}, Jpi M π n x

/-- Auxiliary for Theorem 2.5.3: `T^{f_0} T^{f_1} ⋯ T^{f_{n-1}}` applied to a terminal function,
outermost (`f_0`) first — the operator-composition side of the Reward Iteration theorem. -/
noncomputable def TfComposeChain (M : StationaryMarkovDecisionModel E A) (π : ℕ → E → A) :
    (n : ℕ) → (E → EReal) → (E → EReal)
  | 0, v => v
  | (n + 1), v => Tf M (TfComposeChain M (fun j => π (j + 1)) n v) (π 0)

/-- Auxiliary for Theorem 2.5.4: `n` applications of the maximal-reward operator `T` to a
terminal function, i.e. `T^n g`. -/
noncomputable def TChain (M : StationaryMarkovDecisionModel E A) : (n : ℕ) → (E → EReal) →
    (E → EReal)
  | 0, v => v
  | (n + 1), v => T M (TChain M n v)

/-- The stationary model with the rewards `r`, `g` replaced by their positive parts `r^+`, `g^+`
(same `D`, `Q`, `β`), used to state the Integrability Assumption (AN). -/
noncomputable def StationaryMarkovDecisionModel.posPart (M : StationaryMarkovDecisionModel E A) :
    StationaryMarkovDecisionModel E A :=
  { M with
    r := fun xa => max (M.r xa) 0
    hr_meas := M.hr_meas.max measurable_const
    g := fun x => max (M.g x) 0
    hg_meas := M.hg_meas.max measurable_const }

/-- `δ_N(x) := sup_π 𝔼^π_x[Σ_{k=0}^{N-1} β^k r^+(X_k, f_k(X_k)) + β^N g^+(X_N)]` (Bäuerle–Rieder,
p. 39, PDF 54). -/
noncomputable def deltaN (M : StationaryMarkovDecisionModel E A) (N : ℕ) (x : E) : EReal :=
  ⨆ π ∈ {π : ℕ → E → A | IsPolicySeq M N π},
    EFromToAcc M.posPart π (fun x => ((max (M.g x) 0 : ℝ) : EReal)) N x 0 1

/-- The Integrability Assumption (AN) for the stationary `N`-stage model (Bäuerle–Rieder, p. 39,
PDF 54): `δ_N(x) < ∞` for all `x ∈ E`; the book's standing assumption, needed for the expected
discounted rewards `J_n^π` to be well defined (and equivalent to Section 2.2's (AN) for the
stationary model, Remark 2.5.1). -/
def IntegrabilityAssumption (M : StationaryMarkovDecisionModel E A) (N : ℕ) : Prop :=
  ∀ x, deltaN M N x < ⊤

end MDPFinance.Stationary


