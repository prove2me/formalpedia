-- Prove2me | Definitions.Def_FulfillFlex_IsDLPOptimal
-- name    : FulfillFlex_IsDLPOptimal
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T04:26:12.646033+00:00
-- url     : https://prove2.me/theorems/8247c359-e403-46e4-b33c-68beffc63789
-- title:
--   Optimal solutions of the DLP (5), and those with the structure of Lemma 8
-- statement:
--   A pair $(f,l)$ is an **optimal solution** of the DLP (5) if it is feasible and no feasible pair has a smaller objective.
--
--   It is **structured** if moreover
--
--   1. $f_{jj'}>0$ for some $j'\ne j$ implies $f_{jj}=m_j$, and
--   2. $f_{jj}<m_j$ implies $f_{jj}=r_j$.
--
--   These are the conclusion of Lemma 8 and its consequence. The first says that a DC ships out only after its own mean demand is covered; the second says that it leaves mean demand unfilled locally only after using all its inventory locally. The spillover limit policy of the proof of Proposition 3 is built from a structured optimal solution.
--
--   **Formalization Note** Optimality is stated by comparison with every feasible pair, so it does not depend on the infimum defining `dlpValue`.
-- source:
--   DeValve, Wei, Wu, Yuan, Understanding the Value of Fulfillment Flexibility in an Online Retailing Environment, SSRN 3265838 (2021-01-18 version), display (5), p.16; Lemma 8, p.50; Appendix B.3.1, p.51

import Mathlib
import Definitions.Def_FulfillFlex_dlpValue

namespace FulfillFlex

/-- **Optimal solution of the DLP (5).**
DeValve, Wei, Wu, Yuan, SSRN 3265838 (2021-01-18 version), display (5), p.16: `(f, l)` is feasible
and no feasible pair has a smaller objective. -/
def IsDLPOptimal {N : ℕ} (A : Set (DC N × DC N)) (c : DC N → DC N → ℝ) (p : DC N → ℝ)
    (α : DC N → unitInterval) (m r : DC N → ℝ) (f : DC N → DC N → ℝ) (l : DC N → ℝ) : Prop :=
  DLPFeasible A α m r f l ∧
    ∀ f' l', DLPFeasible A α m r f' l' → dlpObjective c p f l ≤ dlpObjective c p f' l'

/-- **The optimal solutions the proof of Proposition 3 uses.**
DeValve, Wei, Wu, Yuan, SSRN 3265838 (2021-01-18 version), Lemma 8, p.50, and its consequence in
Appendix B.3.1, p.51: an optimal solution of (5) such that

* `f_{jj'} > 0` for `j' ≠ j` implies `f_jj = m_j`;
* `f_jj < m_j` implies `f_jj = r_j`.

**Formalization Note** `m` stands for the paper's `Tμ`. -/
def IsStructuredOptimal {N : ℕ} (A : Set (DC N × DC N)) (c : DC N → DC N → ℝ) (p : DC N → ℝ)
    (α : DC N → unitInterval) (m r : DC N → ℝ) (f : DC N → DC N → ℝ) (l : DC N → ℝ) : Prop :=
  IsDLPOptimal A c p α m r f l ∧
    (∀ j j', j' ≠ j → 0 < f j j' → f j j = m j) ∧
    (∀ j, f j j < m j → f j j = r j)

end FulfillFlex


