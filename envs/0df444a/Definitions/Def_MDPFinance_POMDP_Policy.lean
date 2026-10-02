-- Prove2me | Definitions.Def_MDPFinance_POMDP_Policy
-- name    : MDPFinance_POMDP_Policy
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T22:13:10.115987+00:00
-- url     : https://prove2.me/theorems/2eb48554-9c73-4945-bdd0-4bb2c1875101
-- title:
--   Definition 5.1.3(a,b) — decision rules and N-stage policies
-- statement:
--   The observable history up to time $n$ is $H_n=(x_0,a_0,\dots,x_n)$, represented as a
--   pair of (junk-padded) sequences $(xs,as):(\mathbb{N}\to E_X)\times(\mathbb{N}\to A)$. A
--   **decision rule** at stage $n$ is a measurable $f_n:H_n\to A$ with $f_n(h_n)\in D(x_n)$; an
--   **$N$-stage policy** is a sequence $\pi=(f_0,\dots,f_{N-1})$ of decision rules, one per stage.
--
--   Policies are exactly what "partially observable" restricts: $f_n$ may depend on everything
--   observed so far, but never on any unobservable $y_k$.
--
--   **Formalization Note.** `IsDecisionRule` states $f_n$'s dependence on $H_n$ alone as an explicit
--   locality condition (agreement of $f$ on any two histories with the same first $n{+}1$/$n$
--   coordinates), rather than by typing $f_n$ over a literal finite-tuple domain, since this avoids
--   the `Fin`-indexed-tuple bookkeeping while remaining exactly equivalent to $f_n:H_n\to A$ — the
--   chunk's own flagged pitfall (non-anticipation) is enforced here explicitly, not left implicit.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 149-150, PDF 162-163, Definition 5.1.3(a,b)

import Mathlib
import Definitions.Def_MDPFinance_POMDP_Model

open MeasureTheory ProbabilityTheory

namespace MDPFinance.POMDP

variable {EX EY A : Type*} [MeasurableSpace EX] [MeasurableSpace EY] [MeasurableSpace A]

/-- A decision rule at stage `n` is a function of the observable history so far, represented as
a pair `(xs, as)` of (junk-padded) sequences `ℕ → E_X`, `ℕ → A`, matching `H_n = (x_0,a_0,…,x_n)`
(Bäuerle–Rieder, p. 149-150, PDF 162-163); a *policy* is a sequence of such rules. -/
def Policy (EX A : Type*) := (n : ℕ) → (ℕ → EX) → (ℕ → A) → A

/-- Definition 5.1.3a. `f` is a decision rule at stage `n`: it is measurable, depends only on
`H_n = (x_0,a_0,…,x_n)` (not on later coordinates — the *non-anticipating* condition implicit in
`f_n : H_n → A`), and `f_n(h_n) ∈ D(x_n)` (Bäuerle–Rieder, p. 150, PDF 163). -/
def PartiallyObservableMDM.IsDecisionRule (M : PartiallyObservableMDM EX EY A) (n : ℕ)
    (f : (ℕ → EX) → (ℕ → A) → A) : Prop :=
  Measurable (fun p : (ℕ → EX) × (ℕ → A) => f p.1 p.2) ∧
    (∀ xs xs' as as', (∀ i ≤ n, xs i = xs' i) → (∀ i < n, as i = as' i) → f xs as = f xs' as') ∧
    ∀ xs as, f xs as ∈ M.Dx (xs n)

/-- Definition 5.1.3b. `π` is an `N`-stage policy: `π n` is a decision rule at stage `n` for
every `n < N` (Bäuerle–Rieder, p. 150, PDF 163). -/
def PartiallyObservableMDM.IsPolicy (M : PartiallyObservableMDM EX EY A) (N : ℕ)
    (π : Policy EX A) : Prop :=
  ∀ n < N, M.IsDecisionRule n (π n)

end MDPFinance.POMDP


