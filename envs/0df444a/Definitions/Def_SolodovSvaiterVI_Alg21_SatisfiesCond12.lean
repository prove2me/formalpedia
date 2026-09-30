-- Prove2me | Definitions.Def_SolodovSvaiterVI_Alg21_SatisfiesCond12
-- name    : SolodovSvaiterVI_Alg21_SatisfiesCond12
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T09:53:25.079015+00:00
-- url     : https://prove2.me/theorems/ef3fc2b9-3a97-4946-a9ec-8a68f961ee24
-- title:
--   Condition (1.2): $\langle F(x), x - x^* \rangle \ge 0$ for all $x \in C$ and all solutions $x^*$
-- statement:
--   Let $C \subseteq \mathbb{R}^n$, $F : \mathbb{R}^n \to \mathbb{R}^n$ and let $S$ be the solution set of $\mathrm{VI}(F, C)$. The pair $(F, C)$ satisfies **condition (1.2)** if for every solution $x^* \in S$,
--
--   $$\langle F(x), x - x^* \rangle \ge 0 \qquad \text{for all } x \in C. \tag{1.2}$$
--
--   Condition (1.2) holds when $F$ is monotone or pseudomonotone, but it is strictly weaker than both: it only compares points of $C$ with solutions. It is the generalized monotonicity assumption under which the convergence theorem of the mission is proved.
--
--   **Formalization Note** The paper phrases (1.2) as "Let $x^*$ be any element of the solution set $S$"; the definition quantifies over every $x^* \in S$, not over some $x^*$.
-- source:
--   Solodov & Svaiter, A New Projection Method for Variational Inequality Problems, SIAM J. Control Optim. 37 (1999), p. 765, Section 1, Eq. (1.2)

import Mathlib
import Definitions.Def_SolodovSvaiterVI_Alg21_viSol

open scoped InnerProductSpace

namespace SolodovSvaiterVI.Alg21

/-- Condition (1.2) of Solodov–Svaiter (p. 765): for every solution `x*` of `VI(F, C)` and every
`x ∈ C`, `⟨F(x), x − x*⟩ ≥ 0`. It holds for monotone and for pseudomonotone `F`, but is weaker
than both. -/
def SatisfiesCond12 {n : ℕ} (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (C : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  ∀ xs ∈ viSol F C, ∀ x ∈ C, 0 ≤ ⟪F x, x - xs⟫_ℝ

end SolodovSvaiterVI.Alg21


