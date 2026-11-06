-- Prove2me | Definitions.Def_MethodFulfillment_IsConservative
-- name    : MethodFulfillment_IsConservative
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:13:54.377785+00:00
-- url     : https://prove2.me/theorems/821c4e7f-3120-4e1f-bdb1-8a041b8985b6
-- title:
--   $\gamma$-conservative method-acceptance strategy (Definition 3)
-- statement:
--   A method-acceptance strategy is **$\gamma$-conservative** when, for every period $t$, order type $q$ and method $m\in M(q)$,
--   $$\gamma\cdot\Pr(q\text{ arrives at }t,\ m\text{ is drawn})\le\Pr(q\text{ arrives at }t,\ m\text{ is drawn},\ m\text{ is accepted}),$$
--   where $m$ is accepted when all its pairs are made available. When the method can be drawn, this says that $\Pr(\text{accepting the method at }t\mid\text{the method is of type }m)\ge\gamma$, as in Definition 3.
--
--   **Formalization Note** Definition 3's conditional probability is multiplied out, so a method that is never drawn imposes $0\le0$ instead of an undefined condition.
-- source:
--   Amil, Makhdoumi & Wei, Multi-Item Order Fulfillment Revisited: LP Formulation and Prophet Inequality, manuscript (PDF sha256 197c13b9…), Definition 3, p.14

import Mathlib
import Definitions.Def_MethodFulfillment_runProb

namespace MethodFulfillment

/-- `σ` is a `γ`-conservative method-acceptance strategy (Amil, Makhdoumi & Wei, manuscript, PDF
sha256 197c13b9…, Definition 3, p.14): for every period `t`, order type `q` and method `m ∈ M(q)`,

  `γ · P(q arrives at t and m is drawn) ≤ P(q arrives at t, m is drawn, and m is accepted)`,

where "accepted" means `m ⊆ A`.

**Formalization Note.** Definition 3 asks `P(accepting the method at t | the method is of type m)
≥ γ`; it is stated here cross-multiplied, so a method that is never drawn imposes `0 ≤ 0` instead
of an undefined conditional probability. Whenever the conditioning event has positive probability
the two are equivalent. -/
def IsConservative {I K Q : Type} [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K]
    [Fintype Q] [DecidableEq Q] {T : ℕ} (P : Instance I K Q T) (y : Q → Finset (I × K) → ℝ)
    (σ : Fin T → Run I K Q T → Option Q → Finset (I × K) → Finset (I × K) → ℝ) (γ : ℝ) : Prop :=
  ∀ (t : Fin T) (q : Q), ∀ m ∈ P.methods q,
    γ * ∑ r, runProb P y σ r * (if (r t).1 = some q ∧ (r t).2.1 = m then 1 else 0) ≤
      ∑ r, runProb P y σ r *
        (if (r t).1 = some q ∧ (r t).2.1 = m ∧ m ⊆ (r t).2.2 then 1 else 0)

end MethodFulfillment


