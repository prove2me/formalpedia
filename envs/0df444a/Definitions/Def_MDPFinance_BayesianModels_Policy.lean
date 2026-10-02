-- Prove2me | Definitions.Def_MDPFinance_BayesianModels_Policy
-- name    : MDPFinance_BayesianModels_Policy
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T22:20:02.563173+00:00
-- url     : https://prove2.me/theorems/182bb822-85c7-45cd-9970-fbebe8541ae3
-- title:
--   History-dependent policies for the Bayesian Model
-- statement:
--   A **decision rule** at stage $n$ of a Bayesian Model is a function of the full observable
--   history so far, $\tilde h_n = (x_0,a_0,z_1,x_1,\dots,a_{n-1},z_n,x_n)$ — represented here as a
--   triple `(xs,as,zs)` of ($\mathbb N$-indexed, junk-padded) sequences, since the decision maker
--   observes not only the state trajectory but also the realized disturbances. A decision rule must
--   be measurable, depend only on the history up to stage $n$ (the non-anticipating condition), and
--   choose a feasible action, $f_n(\tilde h_n) \in D(x_n)$.
--
--   A **policy** $\pi = (f_0,f_1,\dots)$ is a sequence of such rules; it is an **$N$-stage policy** if
--   $f_n$ is a valid decision rule for every $n < N$.
--
--   **Formalization Note.** `zs 0` is unused (disturbance indices start at $1$), matching the
--   convention already used for `xs`/`as` in earlier chunks of this series (e.g.
--   `MDPFinance.POMDP.Policy`, chunk `05a`).
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 149-151, Definition 5.1.3 (specialized)

import Mathlib
import Definitions.Def_MDPFinance_BayesianModels_Model

open MeasureTheory ProbabilityTheory

namespace MDPFinance.BayesianModels

variable {EX Θ A Z : Type*} [MeasurableSpace EX] [MeasurableSpace Θ] [MeasurableSpace A]
  [MeasurableSpace Z]

/-- A decision rule at stage `n` is a function of the full observable history so far,
`h̃_n = (x_0,a_0,z_1,x_1,\dots,a_{n-1},z_n,x_n)` (Bäuerle–Rieder, p. 149-151, PDF 162-164),
represented as a triple `(xs,as,zs)` of (junk-padded) sequences `ℕ → E_X`, `ℕ → A`, `ℕ → Z`
(`zs 0` is unused junk since `z`-indices start at `1`); a *policy* is a sequence of such rules. -/
def Policy (EX A Z : Type*) := (n : ℕ) → (ℕ → EX) → (ℕ → A) → (ℕ → Z) → A

/-- `f` is a decision rule at stage `n`: measurable, depends only on `h̃_n` (not on later
coordinates), and feasible, `f(h̃_n) ∈ D(x_n)` (Bäuerle–Rieder, Definition 5.1.3a specialized to
the Bayesian Model, p. 150, PDF 163). -/
def BayesModel.IsDecisionRule (M : BayesModel EX Θ A Z) (n : ℕ)
    (f : (ℕ → EX) → (ℕ → A) → (ℕ → Z) → A) : Prop :=
  Measurable (fun p : (ℕ → EX) × (ℕ → A) × (ℕ → Z) => f p.1 p.2.1 p.2.2) ∧
    (∀ xs xs' as as' zs zs', (∀ i ≤ n, xs i = xs' i) → (∀ i < n, as i = as' i) →
      (∀ i, 1 ≤ i → i ≤ n → zs i = zs' i) → f xs as zs = f xs' as' zs') ∧
    ∀ xs as zs, f xs as zs ∈ M.Dx (xs n)

/-- `π` is an `N`-stage policy: `π n` is a decision rule at stage `n` for every `n < N`
(Bäuerle–Rieder, Definition 5.1.3b, p. 150, PDF 163). -/
def BayesModel.IsPolicy (M : BayesModel EX Θ A Z) (N : ℕ) (π : Policy EX A Z) : Prop :=
  ∀ n < N, M.IsDecisionRule n (π n)

end MDPFinance.BayesianModels


