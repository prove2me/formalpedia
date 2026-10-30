-- Prove2me | Definitions.Def_RoughgardenPOA_IsSmooth
-- name    : RoughgardenPOA_IsSmooth
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T00:35:45.896693+00:00
-- url     : https://prove2.me/theorems/b769990f-b569-477d-8387-48d85acfca83
-- title:
--   $(\lambda,\mu)$-smooth cost-minimization game (Definition 2.1)
-- statement:
--   Let $\lambda, \mu \in \mathbb R$. A cost-minimization game is **$(\lambda, \mu)$-smooth** if for every two outcomes $\mathbf s$ and $\mathbf s^*$,
--
--   $$\sum_{i=1}^k C_i(s_i^*, \mathbf s_{-i}) \le \lambda \cdot C(\mathbf s^*) + \mu \cdot C(\mathbf s),$$
--
--   where $(s_i^*, \mathbf s_{-i})$ is the outcome in which player $i$ plays $s_i^*$ and every other player $j \ne i$ keeps its strategy $s_j$ from $\mathbf s$, and $C$ is the joint cost objective.
--
--   Smoothness bounds the total cost of the $k$ one-player perturbations of an arbitrary outcome; it is the hypothesis behind every price-of-anarchy bound of the paper.
--
--   **Formalization Note** $(s_i^*, \mathbf s_{-i})$ is `Function.update s i (sStar i)`. As in Definition 2.1, no sign condition is placed on $\lambda$ or $\mu$; the constraint $\mu < 1$ enters only in the robust price of anarchy.
-- source:
--   Roughgarden, Intrinsic Robustness of the Price of Anarchy, J. ACM 62(5) (2015), doi:10.1145/2806883, Definition 2.1, eq. (2), p. 4

import Mathlib
import Definitions.Def_RoughgardenPOA_objective

namespace RoughgardenPOA

/-- **(λ, µ)-smooth cost-minimization game (Definition 2.1).**
Roughgarden, *Intrinsic Robustness of the Price of Anarchy*, J. ACM 62(5) (2015),
doi:10.1145/2806883, Definition 2.1, (2), p. 4: "A cost-minimization game is (λ, µ)-smooth if
for every two outcomes s and s*, Σ_{i=1}^k Ci(s*_i, s−i) ≤ λ · C(s*) + µ · C(s). (2)"

`IsSmooth C lam mu` says: for all outcomes `s` and `sStar`,
`∑ i, C i (Function.update s i (sStar i)) ≤ lam * objective C sStar + mu * objective C s`.

**Formalization Note.** The outcome `(s*_i, s−i)`, in which player `i` switches to `s*_i` and
every other player keeps its strategy from `s`, is `Function.update s i (sStar i)`. `λ` is a
Lean keyword, so the parameter is named `lam`. No sign condition is imposed on `lam` or `mu`
here, as in Definition 2.1; the constraint `µ < 1` belongs to Definition 2.2. -/
def IsSmooth {ι : Type*} [Fintype ι] [DecidableEq ι] {S : ι → Type*}
    (C : ι → (∀ i, S i) → ℝ) (lam mu : ℝ) : Prop :=
  ∀ s sStar : (∀ i, S i),
    ∑ i, C i (Function.update s i (sStar i)) ≤ lam * objective C sStar + mu * objective C s

end RoughgardenPOA


