-- Prove2me | Definitions.Def_XOSMax_Supplement_RandomizedProg
-- name    : XOSMax_Supplement_RandomizedProg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T01:31:44.620773+00:00
-- url     : https://prove2.me/theorems/6f2d505c-274f-4794-962e-791606946b59
-- title:
--   Randomized value-oracle programs, query traces, and the Lemma 16 hard instance
-- statement:
--   A randomized value-oracle algorithm is a probability distribution over the published deterministic oracle programs, chosen independently of the input function. Its expected objective value is the probability-weighted value of the returned set. The query trace records every queried set and answer; its length is the number of value-oracle calls. The same interface defines the Lemma 16 instance $\hat f_S(X)=1$ exactly when $X\subseteq S$ and $|X|\ge t$.
--
--   This interface separates oracle calls from the charged-step cost used by the deterministic algorithms and gives the product probabilities used in the lower bounds.
-- source:
--   Filmus, Kawase, Kobayashi & Yamaguchi, Tight Approximation for Unconstrained XOS Maximization, arXiv:1811.09045v3, definition of randomized approximation, p.2; Lemma 16, p.10

import Mathlib
import Definitions.Def_XOSMax_OracleProg

namespace XOSMax.Supplement

open XOSMax OracleProg

/-- A randomized value-oracle algorithm is a probability mass function on deterministic
value-oracle programs (Filmus, Kawase, Kobayashi & Yamaguchi, *Tight Approximation for
Unconstrained XOS Maximization*, arXiv:1811.09045v3, §1, p.2, definition of a randomized
approximation algorithm).

**Formalization Note** The random program is chosen independently of the oracle `f`. Every program
is finite, so all runs terminate. This countable-distribution model includes the finite-support
algorithms used in Theorem 2. -/
abbrev RandomizedProg (E α : Type) : Type := PMF (OracleProg E α)

/-- The ordered trace of value-oracle queries made when `p` is executed against `f`, including each
queried set and its answer (arXiv:1811.09045v3, §1, p.2, running-time convention). Elementary
`step`s are intentionally absent because the lower bounds count value-oracle calls. -/
def trace {E α : Type} (f : Finset E → ℝ) : OracleProg E α → List (Finset E × ℝ)
  | .ret _ => []
  | .query X k => (X, f X) :: trace f (k (f X))
  | .step p => trace f p

/-- The number of value-oracle calls made by a deterministic run. -/
def queries {E α : Type} (f : Finset E → ℝ) (p : OracleProg E α) : ℕ :=
  (trace f p).length

/-- Expected objective value of a randomized algorithm. -/
noncomputable def expectedValue {E : Type} (A : RandomizedProg E (Finset E))
    (f : Finset E → ℝ) : ℝ :=
  ∑' p, (A p).toReal * f (run f p).1

/-- Probability of an event on the random deterministic program. -/
noncomputable def programProbability {E α : Type} (A : RandomizedProg E α)
    (P : OracleProg E α → Prop) [DecidablePred P] : ℝ :=
  ∑' p, (A p).toReal * if P p then 1 else 0

/-- The hard instance of Lemma 16: its value is one exactly on sets contained in `S` and having
cardinality at least `t` (arXiv:1811.09045v3, Lemma 16, p.10). -/
def hardInstance {n : ℕ} (S : Finset (Fin n)) (t : ℕ) (X : Finset (Fin n)) : ℝ :=
  if X ⊆ S ∧ t ≤ X.card then 1 else 0

end XOSMax.Supplement


