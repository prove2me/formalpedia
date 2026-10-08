-- Prove2me | Definitions.Def_Disjunctive_Polarity_FacetDefining
-- name    : Disjunctive_Polarity_FacetDefining
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-10-06T21:59:30.964519+00:00
-- url     : https://prove2.me/theorems/bac582c6-748b-4c72-b498-642ba2e82f2f
-- title:
--   Inequality defines a facet (validity + facet)
-- statement:
--   For $P \subseteq \mathbb{R}^n$, the inequality $\alpha x \ge \alpha_0$ **defines a facet** of $P$ (`DefinesFacetGE P α α₀`) if it is valid for $P$ ($\alpha x \ge \alpha_0$ for all $x \in P$) and $P \cap \{x : \alpha x = \alpha_0\}$ is a facet of $P$ (`IsFacet`: a nonempty extreme subset of dimension $\dim P - 1$). `DefinesFacetLE P v v₀` is the same for $v x \le v_0$, the convention of Balas's projection sections.
--
--   **Formalization Note.** `IsFacet P F` describes only the set $F$, which is the same for $(\alpha,\alpha_0)$ and $(-\alpha,-\alpha_0)$; statements about "the inequality $\alpha x \ge \alpha_0$ defines a facet" must also require validity. This module is additive (it imports `Disjunctive_Polarity_Projection` and redefines nothing), so it can be imported together with every existing module of the mission.
-- source:
--   Balas, Disjunctive Programming, Springer 2018, §2.2.3 (p. 30) and §2.4 (p. 36): 'the inequality defines a facet'

import Mathlib
import Definitions.Def_Disjunctive_Polarity_Projection

namespace Disjunctive.Polarity

/-- The inequality `α x ≥ α₀` **defines a facet** of `P ⊆ ℝⁿ` (Balas §2.4, p. 36, Theorem 2.18;
§2.2.3): the inequality is *valid* for `P` (`α x ≥ α₀` for every `x ∈ P`) and the face it cuts
out, `P ∩ {x : α x = α₀}`, is a facet of `P` in the sense of `IsFacet`.

`IsFacet P F` alone only describes the *set* `F`; it does not say on which side of the hyperplane
`{α x = α₀}` the set `P` lies, so `IsFacet P (P ∩ {α x = α₀})` holds for `(α, α₀)` and for
`(-α, -α₀)` alike. A statement about "the inequality `α x ≥ α₀`" must also assert its validity,
which is what this predicate adds. -/
def DefinesFacetGE {n : ℕ} (P : Set (Fin n → ℝ)) (α : Fin n → ℝ) (α0 : ℝ) : Prop :=
  (∀ x ∈ P, α0 ≤ dotProduct α x) ∧ IsFacet P (P ∩ {x | dotProduct α x = α0})

/-- The inequality `v x ≤ v₀` **defines a facet** of `P ⊆ ℝ^q` (Balas §2.3, p. 32, the `≤`
convention of the projection sections): `v x ≤ v₀` is valid for `P` and `P ∩ {x : v x = v₀}` is
a facet of `P` in the sense of `IsFacet`. -/
def DefinesFacetLE {q : ℕ} (P : Set (Fin q → ℝ)) (v : Fin q → ℝ) (v0 : ℝ) : Prop :=
  (∀ x ∈ P, dotProduct v x ≤ v0) ∧ IsFacet P (P ∩ {x | dotProduct v x = v0})

end Disjunctive.Polarity


