-- Prove2me | Definitions.Def_FoundationsRL_LinUCB_confidenceSet
-- name    : FoundationsRL_LinUCB_confidenceSet
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:22:14.010241+00:00
-- url     : https://prove2.me/theorems/b4f75f53-4eca-414a-a022-2bb79495186b
-- title:
--   The least-squares confidence set $\mathcal F^t$ (Eq. (3.9))
-- statement:
--   For a class $\mathcal F$ and a slack $\beta$, the **confidence set** of round $t$ is the set of functions whose empirical square loss is within $\beta$ of the smallest one:
--
--   $$
--   \mathcal F^t=\Bigl\{f\in\mathcal F:\ \sum_{i<t}\bigl(f(x^i,\pi^i)-r^i\bigr)^2\le\sum_{i<t}\bigl(\widehat f^t(x^i,\pi^i)-r^i\bigr)^2+\beta\Bigr\},
--   $$
--
--   where $\widehat f^t$ is an empirical risk minimizer over $\mathcal F$.
--
--   **Formalization Note** The condition is written $\forall g\in\mathcal F,\ L(f)\le L(g)+\beta$, which says the same without choosing a minimizer, so the set does not depend on tie-breaking. Before any data is seen the set is $\mathcal F$ when $\beta\ge0$, the book's $\mathcal F^1=\mathcal F$.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, Eqs. (3.8)–(3.9), p. 41

import Mathlib
import Definitions.Def_FoundationsRL_LinUCB_sqLoss

open MeasureTheory ProbabilityTheory

namespace FoundationsRL.LinUCB

/-- The least-squares confidence set `F^t` of round `t` (Foster & Rakhlin, *Foundations of Reinforcement Learning and Interactive Decision Making*, arXiv:2312.16730v1, Eq. (3.9), p. 41): the `f ∈ F` whose
empirical square loss is within `β` of that of the empirical risk minimizer.

**Formalization Note.** `∀ g ∈ F, L(f) ≤ L(g) + β` says `L(f) ≤ min_{g ∈ F} L(g) + β` without
choosing a minimizer, so the set does not depend on how ties in `arg min` are broken. With no data
(Lean's `t = 0`, the book's `t = 1`) the loss vanishes and the set is `F`, the book's `F^1 = F`,
for `β ≥ 0`. -/
def confidenceSet {Ω X Act : Type*} {mΩ : MeasurableSpace Ω} [MeasurableSpace X]
    [MeasurableSpace Act] {P : Measure Ω} {Mstar : Kernel (X × Act) ℝ}
    (F : Set (X → Act → ℝ)) (R : ContextualBanditRun P Mstar) (β : ℝ) (t : ℕ) (ω : Ω) :
    Set (X → Act → ℝ) :=
  {f | f ∈ F ∧ ∀ g ∈ F, sqLoss R f t ω ≤ sqLoss R g t ω + β}

end FoundationsRL.LinUCB


