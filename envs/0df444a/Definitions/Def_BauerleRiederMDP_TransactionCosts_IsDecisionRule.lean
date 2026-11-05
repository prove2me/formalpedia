-- Prove2me | Definitions.Def_BauerleRiederMDP_TransactionCosts_IsDecisionRule
-- name    : BauerleRiederMDP_TransactionCosts_IsDecisionRule
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:25:31.895622+00:00
-- url     : https://prove2.me/theorems/1b99038c-ce0f-4b36-90fe-458dd4a621c4
-- title:
--   Decision rules of the transaction cost model
-- statement:
--   A decision rule is a measurable map $f:E\to\mathbb R_+^2$ with $f(x)\in D(x)$ for all $x\in E$; $f(x)=(a_0,a_1)$ are the bond and stock holdings chosen after transaction in state $x$. The set of decision rules is the book's $F_n$, the same for every $n$ in this model.
--
--   **Formalization Note** $f$ is a measurable map on $\mathbb R\times\mathbb R$; every measurable map on $E$ extends to one, and values off $E$ are not used.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Definition 2.1.5 a), p.16 (PDF 31)

import Mathlib
import Definitions.Def_BauerleRiederMDP_TransactionCosts_stateSpace
import Definitions.Def_BauerleRiederMDP_TransactionCosts_admissibleSet

namespace BauerleRiederMDP.TransactionCosts

/-- A decision rule of the transaction cost model (Bäuerle & Rieder 2011, Definition 2.1.5,
p.16, PDF 31, for the data of §4.5, p.106, PDF 120): a measurable map `f : E → A` with
`f(x) ∈ D(x)` for all `x ∈ E`; `f(x) = (a₀, a₁)` are the bond and stock holdings after
transaction. The set of decision rules is the book's `F_n` (the same for every `n`).

**Formalization Note.** `f` is a measurable map on `ℝ × ℝ`; every measurable map on `E` extends
to one (E is a measurable set), and values off `E` are never used. -/
def IsDecisionRule (c : ℝ) (f : ℝ × ℝ → ℝ × ℝ) : Prop :=
  Measurable f ∧ ∀ x ∈ stateSpace, f x ∈ admissibleSet c x

end BauerleRiederMDP.TransactionCosts


