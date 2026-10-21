-- Prove2me | Definitions.Def_NatureSLT_GrowthFunction_vcDimReal
-- name    : NatureSLT_GrowthFunction_vcDimReal
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-20T15:50:46.920479+00:00
-- url     : https://prove2.me/theorems/98efebcd-67be-45b4-959b-5fcf49595b91
-- title:
--   VC dimension of a set of real functions, through the indicators (3.22)
-- statement:
--   Let $A \le Q(z, \alpha) \le B$, $\alpha \in \Lambda$, be a set of real functions on a set $Z$ bounded by constants $A$ and $B$, where $A$ may be $-\infty$ and $B$ may be $+\infty$. Along with it consider the set of indicators
--
--   $$I(z, \alpha, \beta) = \theta\{Q(z, \alpha) - \beta\}, \qquad \alpha \in \Lambda,\ \beta \in (A, B), \tag{3.22}$$
--
--   where $\theta(z) = 0$ for $z < 0$ and $\theta(z) = 1$ for $z \ge 0$. The **VC dimension of the set of real functions** is the VC dimension (maximum number of shattered vectors, possibly $\infty$) of the set of indicators (3.22), whose parameter is the pair $(\alpha, \beta)$ with $\alpha \in \Lambda$ and $A < \beta < B$.
--
--   **Formalization Note** $A$ and $B$ are extended reals and are only compared with the real threshold $\beta$. The bounds $A \le Q \le B$ describe the setting of the definition and are not part of its value: a theorem about a particular set of functions states them; they are void when $A = -\infty$ and $B = +\infty$.
-- source:
--   Vapnik, The Nature of Statistical Learning Theory, 2nd ed., Springer 2000, p. 80, Section 3.6, Eq. (3.22)

import Mathlib
import Definitions.Def_NatureSLT_GrowthFunction_vcDim
import Definitions.Def_NatureSLT_GrowthFunction_stepFunction

namespace NatureSLT.GrowthFunction

/-- The indicators (3.22) of a set of real functions `Q(z, α)`, `α ∈ Λ`, with bounds `A`, `B`
(Vapnik, *The Nature of Statistical Learning Theory*, 2nd ed., §3.6, p. 80):
`I(z, α, β) = θ{Q(z, α) − β}`, `α ∈ Λ`, `β ∈ (A, B)`, indexed by the pairs `(α, β)` with
`A < β < B`. `A` and `B` are extended reals because the book allows `A = −∞` and `B = ∞`; they
are only compared with the real `β`. -/
noncomputable def realIndicators {Z Λ : Type*} (Q : Λ → Z → ℝ) (A B : EReal) :
    {p : Λ × ℝ // A < (p.2 : EReal) ∧ (p.2 : EReal) < B} → Z → Bool :=
  fun p z => stepFunction (Q p.1.1 z - p.1.2)

/-- The **VC dimension of a set of real functions** `A ≤ Q(z, α) ≤ B`, `α ∈ Λ` (Vapnik, *The
Nature of Statistical Learning Theory*, 2nd ed., §3.6, p. 80): the VC dimension of the set of
corresponding indicators (3.22), `θ{Q(z, α) − β}`, with parameters `α ∈ Λ` and `β ∈ (A, B)`.
The bounds `A ≤ Q ≤ B` are the setting of the definition, not part of its value; a theorem
about a particular set of functions states them (they are void for `A = −∞`, `B = ∞`). -/
noncomputable def vcDimReal {Z Λ : Type*} (Q : Λ → Z → ℝ) (A B : EReal) : ℕ∞ :=
  vcDim (realIndicators Q A B)

end NatureSLT.GrowthFunction


