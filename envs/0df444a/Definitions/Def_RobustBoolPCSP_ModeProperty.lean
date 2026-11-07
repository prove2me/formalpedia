-- Prove2me | Definitions.Def_RobustBoolPCSP_ModeProperty
-- name    : RobustBoolPCSP_ModeProperty
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:21:49.389585+00:00
-- url     : https://prove2.me/theorems/e2dda88d-d6c5-41be-9392-bc8a81e3b54a
-- title:
--   The mode property (Definition 2.3)
-- statement:
--   Let $A$ be a finite set and $P,W\subseteq A^r$. The pair $(P,W)$ has the **mode property** if no distribution supported on $P$ has a forbidden tuple $b\notin W$ as its vector of unique marginal modes; equivalently, there is no probability vector $\lambda$ on $P$ and no $b\notin W$ with
--
--   $$\sum_{x:\,x_i=b_i}\lambda_x>\sum_{x:\,x_i=a}\lambda_x\qquad\text{for all } i\in[r],\ a\in A\setminus\{b_i\}.$$
--
--   If $P$ is empty the property holds vacuously; for a singleton domain or a nullary relation the comparisons are vacuous and the property says that every tuple of a nonempty $P$ lies in $W$.
--
--   For a template with output map $h:A\to B$ it is applied to $(P_j,W_j)$ with $W_j=(h^{r_j})^{-1}(Q_j)$; it is the hypothesis of the log-free robust algorithm.
--
--   **Formalization Note** The equivalent probability-vector form is used: $\lambda$ is a nonnegative function on $A^r$ vanishing off $P$ with total mass $1$.
-- source:
--   Cai, Jiang, Zou, On Robust Promise CSPs: A Boolean Dichotomy, Sharp Quantitative Bounds, and Soft-Equality Transfer, STOC 2027 submission (manuscript of 2026-11-03, sha256 fd1be0d0624155f00f7a115874a4dadfb7ebb2d4187530c7d0bdd4e1406e8732), §2.2, Definition 2.3, p.8

import Mathlib

set_option autoImplicit false

namespace RobustBoolPCSP

/-- The **mode property** of a pair `(P, W)` of relations of arity `r` on `A` (Definition 2.3, p.8):
"no distribution supported on P has a forbidden tuple b ∉ W as its vector of unique marginal modes.
Equivalently, there is no probability vector λ on P satisfying
Σ_{x:xi=bi} λx > Σ_{x:xi=a} λx for all i ∈ [r], a ∈ A \ {bi}."

**Formalization Note.** The equivalent form is used: there is no `λ : A^r → ℝ`, nonnegative,
vanishing off `P` and summing to `1`, and no `b ∉ W` with the strict marginal comparisons. For
`P = ∅` there is no such `λ` and the property holds vacuously; for a singleton `A` or `r = 0` the
comparisons are vacuous and the property says that every tuple of a nonempty `P` lies in `W`, as
the definition states. The weight `λ` is named `wt` (`λ` is not an identifier). -/
def ModeProperty {A : Type} [Fintype A] [DecidableEq A] {r : ℕ} (P W : Set (Fin r → A)) :
    Prop :=
  ¬ ∃ (wt : (Fin r → A) → ℝ) (b : Fin r → A),
      (∀ x, 0 ≤ wt x) ∧ (∀ x, wt x ≠ 0 → x ∈ P) ∧ (∑ x, wt x = 1) ∧ b ∉ W ∧
      ∀ i : Fin r, ∀ a : A, a ≠ b i →
        ∑ x ∈ Finset.univ.filter (fun x : Fin r → A => x i = a), wt x <
          ∑ x ∈ Finset.univ.filter (fun x : Fin r → A => x i = b i), wt x

end RobustBoolPCSP


