-- Prove2me | Definitions.Def_SteuerChoo_Lexico_IsLexMin
-- name    : SteuerChoo_Lexico_IsLexMin
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T16:51:24.884985+00:00
-- url     : https://prove2.me/theorems/b720ed46-2087-4c32-9f50-9fa5b1b2cad9
-- title:
--   Minimizers of the lexicographic weighted Tchebycheff program
-- statement:
--   Let $Z\subseteq\mathbb R^k$, weights $\lambda$ and an ideal vector $z^*$ be given, and write $t_\lambda(z)=\max_i\lambda_i(z^*_i-z_i)$ and $e^{\mathsf T}(z^*-z)=\sum_{i=1}^k(z^*_i-z_i)$. The **lexicographic weighted Tchebycheff program**
--   $$
--   \operatorname{lex\,min}\ \big\{\,P_1\,\alpha+P_2\,e^{\mathsf T}(z^*-z)\,\big\}\quad\text{s.t.}\quad \alpha\ge\lambda_i(z^*_i-z_i),\ 1\le i\le k,\quad z\in Z,
--   $$
--   with pre-emptive priority factors, is solved in two stages: first minimize $\alpha$ (equivalently $t_\lambda$) over $Z$; then, among the first-stage minimizers, minimize $e^{\mathsf T}(z^*-z)$.
--
--   Thus $z$ **minimizes the lexicographic weighted Tchebycheff program** when
--
--   1. $z\in Z$;
--   2. $t_\lambda(z)\le t_\lambda(w)$ for every $w\in Z$;
--   3. $e^{\mathsf T}(z^*-z)\le e^{\mathsf T}(z^*-w)$ for every $w\in Z$ with $t_\lambda(w)\le t_\lambda(z)$.
--
--   **Formalization Note** The paper prints the priority as "$P_1 <<< P_2$", which read literally would give the second objective priority; its own text on p. 336 ("the first stage of the lexicographic weighted Tchebycheff program is the weighted Tchebycheff program") and the goal-programming convention it cites give $\alpha$ priority, which is what is encoded. The program is not encoded as a weighted sum with numerical $P_1,P_2$, which would be the augmented program. The variables $\alpha$ and $x$ are eliminated; "$z$ uniquely minimizes" is expressed separately as: every minimizer equals $z$.
-- source:
--   Steuer and Choo, An Interactive Weighted Tchebycheff Procedure for Multiple Objective Programming, Math. Programming 26 (1983), p. 335, Theorem 4.5 (the lexicographic weighted Tchebycheff program); p. 336, paragraph after Theorem 4.6 (the two stages)

import Mathlib
import Definitions.Def_SteuerChoo_Lexico_tcheb

namespace SteuerChoo.Lexico

/-- `z` minimizes the lexicographic weighted Tchebycheff program over `Z`
(Theorem 4.5, p. 335): `z ∈ Z` minimizes the first stage `tcheb lam zstar`
over `Z`, and among the first-stage minimizers it minimizes the second stage
`eᵀ(z* − z) = Σ_i (z*_i − z_i)`. -/
def IsLexMin {k : ℕ} [NeZero k] (Z : Set (Fin k → ℝ)) (lam zstar z : Fin k → ℝ) : Prop :=
  z ∈ Z ∧ (∀ w ∈ Z, tcheb lam zstar z ≤ tcheb lam zstar w) ∧
    ∀ w ∈ Z, tcheb lam zstar w ≤ tcheb lam zstar z →
      ∑ i, (zstar i - z i) ≤ ∑ i, (zstar i - w i)

end SteuerChoo.Lexico


