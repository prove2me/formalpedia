-- Prove2me | Definitions.Def_LeastMajorized_WeakSuperABMajorized
-- name    : LeastMajorized_WeakSuperABMajorized
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:47:40.665996+00:00
-- url     : https://prove2.me/theorems/959e7849-2af6-4fe2-93bf-70c67e6b10a2
-- title:
--   Weak $(a,b)$-supermajorization $x\prec^{\uparrow}_{(a,b)}y$
-- statement:
--   For $a\in\mathbb R^n_{>0}$ and $b\in\mathbb R^n$, a vector $x$ is **weakly $(a,b)$-supermajorized** by $y$, written $x\prec^{\uparrow}_{(a,b)}y$, if for every non-increasing continuous convex function $\phi:\mathbb R\to\mathbb R$,
--
--   $$
--   \sum_{i\in N}a_i\,\phi\!\Big(\frac{x_i+b_i}{a_i}\Big)\ \le\ \sum_{i\in N}a_i\,\phi\!\Big(\frac{y_i+b_i}{a_i}\Big).
--   $$
--
--   Unlike $(a,b)$-majorization there is no equal-sum requirement. It is the hypothesis of Lemma 14.
--
--   **Formalization Note** "Non-increasing" is `Antitone`; convexity is on all of $\mathbb R$; continuity is kept as printed. The relation is written for every $a$; the mission uses it only with $a=(1,\dots,1)$.
-- source:
--   Schoot Uiterkamp, A characterization of simultaneous optimization, majorization, and (bi)submodular polyhedra, arXiv:2201.06596v2, §3.2, p.9

import Mathlib

namespace LeastMajorized

/-- **Weak `(a, b)`-supermajorization**, Schoot Uiterkamp, arXiv:2201.06596v2, §3.2, p.9: `x` is
weakly `(a, b)`-supermajorized by `y`, written `x ≺↑_(a,b) y`, "if for all non-increasing
continuous convex functions `φ` we have `Σ_{i∈N} aᵢ φ((xᵢ + bᵢ)/aᵢ) ≤ Σ_{i∈N} aᵢ φ((yᵢ + bᵢ)/aᵢ)`."

**Formalization Note** `φ : ℝ → ℝ` non-increasing is `Antitone φ`; convex is
`ConvexOn ℝ Set.univ φ`; continuity is kept as printed. There is no equal-sum clause. The
relation is written for every `a`; the paper fixes `a ∈ ℝⁿ_{>0}`, and the mission uses it only
with `a = (1, …, 1)`. -/
def WeakSuperABMajorized {n : ℕ} (a b x y : Fin n → ℝ) : Prop :=
  ∀ φ : ℝ → ℝ, Antitone φ → ConvexOn ℝ Set.univ φ → Continuous φ →
    ∑ i, a i * φ ((x i + b i) / a i) ≤ ∑ i, a i * φ ((y i + b i) / a i)

end LeastMajorized


