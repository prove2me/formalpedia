-- Prove2me | Definitions.Def_WildeQIT_coupling
-- name    : WildeQIT_coupling
-- status  : Definition
-- author  : @nonlocally
-- created : 2026-09-07T05:41:49.611497+00:00
-- url     : https://prove2.me/theorems/aef9ffe3-3388-4dc7-bb7c-7118ffc98da9
-- title:
--   Couplings and maximal couplings of two random variables (Definitions 10.7.2–10.7.3)
-- statement:
--   **Definition 10.7.2 (Coupling).** A coupling of a pair $(X,Y)$ of two random variables is a pair $(\hat X,\hat Y)$ of two other random variables that have the same marginal distributions as those of $X$ and $Y$. Representing $(\hat X,\hat Y)$ by its joint distribution $c$ on $\mathcal{X}\times\mathcal{Y}$, this says
--
--   $$
--   \sum_y c(x,y) = p_X(x)\ \text{ for all } x, \qquad \sum_x c(x,y) = p_Y(y)\ \text{ for all } y .
--   $$
--
--   **Definition 10.7.3 (Maximal coupling).** A coupling $(\hat X,\hat Y)$ of $(X,Y)$, both on a common alphabet $\mathcal{A}$, is maximal if $\Pr\{\hat X=\hat Y\}=\sum_{u}c(u,u)$ takes on its maximum value with respect to all couplings of $X$ and $Y$.
--
--   Maximal couplings realise the trace distance as a probability of disagreement (Lemma 10.7.2) and are the tool of the proof of the Zhang–Audenaert continuity bound.
--
--   **Formalization Note.** `WildeQIT.FinDist.IsCoupling p q c` is the conjunction of the two marginal conditions for `c : FinDist (α × β)`; `WildeQIT.FinDist.probEq c = ∑ x, c.prob (x, x)` is $\Pr\{\hat X=\hat Y\}$ for `c : FinDist (α × α)`; `WildeQIT.FinDist.IsMaximalCoupling p q c` is `IsCoupling p q c ∧ ∀ c', IsCoupling p q c' → c'.probEq ≤ c.probEq`. Existence of a maximal coupling is not asserted by the definition.
-- source:
--   Wilde, Quantum Information Theory 2nd ed. (Cambridge 2017; arXiv:1106.1445v8), Definition 10.7.2, §Continuity of Entropy (roster-items.csv line 17360); and Definition 10.7.3 (Maximal Coupling), line 17366.

import Definitions.Def_WildeQIT_FinDist

/-!
Wilde, *Quantum Information Theory* (2nd ed.), Definitions 10.7.2 (Coupling) and 10.7.3
(Maximal coupling): a coupling of `(X, Y)` is a pair `(X̂, Ŷ)` with the same marginals as `X`
and `Y`; it is maximal if `Pr{X̂ = Ŷ}` is as large as possible among all couplings.
A pair of random variables is represented by its joint distribution.
-/

namespace WildeQIT

namespace FinDist

variable {α β : Type} [Fintype α] [Fintype β]

/-- Definition 10.7.2. `c` (a joint distribution on `α × β`) is a coupling of `p` and `q`:
its first marginal is `p` and its second marginal is `q`. -/
def IsCoupling (p : FinDist α) (q : FinDist β) (c : FinDist (α × β)) : Prop :=
  (∀ x, c.fst.prob x = p.prob x) ∧ (∀ y, c.snd.prob y = q.prob y)

/-- `Pr{X̂ = Ŷ} = ∑_x c(x, x)` for a joint distribution `c` on `α × α`. -/
noncomputable def probEq (c : FinDist (α × α)) : ℝ := ∑ x, c.prob (x, x)

/-- Definition 10.7.3. A coupling `c` of `p` and `q` (both on `α`) is maximal if `Pr{X̂ = Ŷ}`
under `c` is at least `Pr{X̂ = Ŷ}` under every other coupling of `p` and `q`. -/
def IsMaximalCoupling (p q : FinDist α) (c : FinDist (α × α)) : Prop :=
  IsCoupling p q c ∧ ∀ c' : FinDist (α × α), IsCoupling p q c' → c'.probEq ≤ c.probEq

end FinDist

end WildeQIT


