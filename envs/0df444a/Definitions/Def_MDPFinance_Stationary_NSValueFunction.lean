-- Prove2me | Definitions.Def_MDPFinance_Stationary_NSValueFunction
-- name    : MDPFinance_Stationary_NSValueFunction
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T21:41:16.050683+00:00
-- url     : https://prove2.me/theorems/e52a6744-439b-4841-b9d5-a1a2eb9c09ce
-- title:
--   The non-stationary model and value function (for the LQ example)
-- statement:
--   The **non-stationary** value function $V_n$ used only by Theorem 2.6.3 (the book's own §2.6.3
--   LQ example is explicitly non-stationary), given via the Bellman recursion $V_N = g_N$, $V_n =
--   T_n V_{n+1}$ (equivalently $V_n = T_n \cdots T_{N-1} g_N$).
--
--   **Formalization Note.** Identical restatement of `MDPFinance.Bellman`'s non-stationary model
--   and operators (chunk `02a`), prefixed `NS` to avoid colliding with this chunk's own primary
--   *stationary* `StationaryMarkovDecisionModel`/`J`. $V_n$ is given via its recursive
--   characterization (Theorem 2.3.8) rather than the sup-over-policies primitive, matching the
--   same simplification made for `MDPFinance.StructuredModels.V` in chunk `02c`.
--
--   `NSVpi M π n x` is the value $V_n^\pi(x) = \mathbb{E}^\pi_{n,x}[\sum_{k=n}^{N-1}
--   r_k(X_k,f_k(X_k)) + g_N(X_N)]$ of a policy $\pi$ (chunk `02a`'s accumulator construction,
--   restated), and `NSIsPolicy` says $\pi$ is an $N$-stage policy; these let Theorem 2.6.3 state
--   that its linear policy is optimal, $V_0^{\pi^*} = V_0$.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 14, Definition 2.1.1 and p. 22, Theorem 2.3.8 (restated for the non-stationary LQ example of §2.6.3)

import Mathlib

open MeasureTheory ProbabilityTheory

namespace MDPFinance.Stationary

/-- A (non-stationary) Markov Decision Model with planning horizon `N` (Bäuerle–Rieder,
Definition 2.1.1, p. 14, PDF 29), restated here (in addition to this chunk's own *stationary*
model) because Theorem 2.6.3's stochastic LQ problem is explicitly non-stationary (p. 51, PDF
66: "Obviously we obtain a non-stationary problem") and needs the genuinely time-indexed value
function `V_n`, not this chunk's `J_n`. Identical to `MDPFinance.Bellman.MarkovDecisionModel`
(chunk `02a`); prefixed `NS` in this chunk to avoid colliding with `StationaryMarkovDecisionModel`
above. -/
structure NSMarkovDecisionModel (E A : Type*) [MeasurableSpace E] [MeasurableSpace A] (N : ℕ) where
  D : ℕ → Set (E × A)
  hD_meas : ∀ n < N, MeasurableSet (D n)
  hD_sel : ∀ n < N, ∃ f : E → A, Measurable f ∧ ∀ x, (x, f x) ∈ D n
  Q : ℕ → Kernel (E × A) E
  hQ_prob : ∀ n < N, ∀ xa, IsProbabilityMeasure (Q n xa)
  r : ℕ → E × A → ℝ
  hr_meas : ∀ n < N, Measurable (r n)
  g : E → ℝ
  hg_meas : Measurable g

variable {E A : Type*} [MeasurableSpace E] [MeasurableSpace A] {N : ℕ}

def NSMarkovDecisionModel.Dx (M : NSMarkovDecisionModel E A N) (n : ℕ) (x : E) : Set A :=
  {a | (x, a) ∈ M.D n}

/-- `IM E`, restated identically to `MDPFinance.Bellman.IM` (chunk `02a`). -/
def NSIM (E : Type*) [MeasurableSpace E] : Set (E → EReal) :=
  {v | Measurable v ∧ ∀ x, v x ≠ ⊤}

/-- The `EReal`-valued integral, restated identically to `MDPFinance.Bellman.erealIntegral`
(chunk `02a`). -/
noncomputable def NSErealIntegral {E : Type*} [MeasurableSpace E] (μ : Measure E)
    (v : E → EReal) : EReal :=
  (↑(∫⁻ x, (v x ⊔ 0).toENNReal ∂μ) : EReal) + (-(↑(∫⁻ x, ((-v x) ⊔ 0).toENNReal ∂μ) : EReal))

/-- The operator `L_n`, restated identically to `MDPFinance.Bellman.L` (chunk `02a`). -/
noncomputable def NSL (M : NSMarkovDecisionModel E A N) (n : ℕ) (v : E → EReal) (xa : E × A) :
    EReal :=
  (M.r n xa : EReal) + NSErealIntegral (M.Q n xa) v

/-- The maximal reward operator `T_n`, restated identically to `MDPFinance.Bellman.T`
(chunk `02a`). -/
noncomputable def NST (M : NSMarkovDecisionModel E A N) (n : ℕ) (v : E → EReal) (x : E) : EReal :=
  ⨆ a ∈ M.Dx n x, NSL M n v (x, a)

/-- `k` applications of `T_n` starting at time `n`, innermost first — restated identically to
`MDPFinance.Bellman.TChain` (chunk `02a`, "Auxiliary for Theorem 2.3.8b"). -/
noncomputable def NSTChain (M : NSMarkovDecisionModel E A N) : (k : ℕ) → (n : ℕ) → (E → EReal) →
    (E → EReal)
  | 0, _, v => v
  | (k + 1), n, v => NST M n (NSTChain M k (n + 1) v)

/-- The non-stationary value function `V_n`, given via its recursive characterization
(`V_N = g_N`, `V_n = T_n V_{n+1}`), established as Theorem 2.3.8 (chunk `02a`) — used directly
here (rather than re-deriving the sup-over-policies primitive definition and its supporting
history/policy machinery) since Theorem 2.6.3 (the only result needing `V_n` in this chunk) only
needs the recursion. Same simplification, for the same reason, as
`MDPFinance.StructuredModels.V` in chunk `02c`. -/
noncomputable def NSV (M : NSMarkovDecisionModel E A N) (n : ℕ) : E → EReal :=
  NSTChain M (N - n) n (fun x => (M.g x : EReal))

/-- Auxiliary accumulator for the expected reward-to-go of the non-stationary model under a
fixed policy `π : ℕ → E → A` (restated in shape from `MDPFinance.Bellman.EFromToAcc`, chunk
`02a`): from time `n` in state `x` with reward already accrued `acc`, running `k` more stages
toward the terminal payoff `term`. -/
noncomputable def NSEFromToAcc (M : NSMarkovDecisionModel E A N) (π : ℕ → E → A)
    (term : E → EReal) : (k : ℕ) → (n : ℕ) → (x : E) → (acc : EReal) → EReal
  | 0, _, x, acc => acc + term x
  | (k + 1), n, x, acc =>
      NSErealIntegral (M.Q n (x, π n x))
        (fun x' => NSEFromToAcc M π term k (n + 1) x' (acc + (M.r n (x, π n x) : EReal)))

/-- `V_n^π(x) := 𝔼^π_{n,x}[Σ_{k=n}^{N-1} r_k(X_k, f_k(X_k)) + g_N(X_N)]`, the value of the policy
`π` from time `n` in state `x` (Bäuerle–Rieder, p. 18, PDF 33; restated from
`MDPFinance.Bellman.Vpi`, chunk `02a`); a policy is optimal when `V_0^π = V_0`. -/
noncomputable def NSVpi (M : NSMarkovDecisionModel E A N) (π : ℕ → E → A) (n : ℕ) (x : E) :
    EReal :=
  NSEFromToAcc M π (fun x => (M.g x : EReal)) (N - n) n x 0

/-- `π` is an `N`-stage policy of the non-stationary model: `π n` is a decision rule at each
time `n < N` (Bäuerle–Rieder, Definition 2.1.5). -/
def NSIsPolicy (M : NSMarkovDecisionModel E A N) (π : ℕ → E → A) : Prop :=
  ∀ n < N, Measurable (π n) ∧ ∀ x, (x, π n x) ∈ M.D n

end MDPFinance.Stationary


