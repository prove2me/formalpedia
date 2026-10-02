-- Prove2me | Definitions.Def_TeschlODE_IVP_LocallyLipschitzSecond
-- name    : TeschlODE_IVP_LocallyLipschitzSecond
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T10:50:11.160107+00:00
-- url     : https://prove2.me/theorems/196ecd2c-65ab-42c0-98f2-c8e6771bc74f
-- title:
--   Locally Lipschitz in the second argument, uniformly in the first (2.18)
-- statement:
--   Let $U \subseteq \mathbb{R} \times \mathbb{R}^n$ and $f : \mathbb{R} \times \mathbb{R}^n \to \mathbb{R}^n$. The function $f$ is **locally Lipschitz continuous in the second argument, uniformly with respect to the first**, on $U$ if for every compact set $V_0 \subseteq U$ there is a constant $L$ such that
--   $$|f(t, x) - f(t, y)| \le L\,|x - y| \qquad \text{whenever } (t, x), (t, y) \in V_0 .$$
--
--   The book phrases this as: for every compact $V_0 \subset U$ the number
--   $$L = \sup_{(t,x) \ne (t,y) \in V_0} \frac{|f(t,x) - f(t,y)|}{|x - y|} \qquad (2.18)$$
--   is finite. The two formulations are equivalent: a finite supremum is such a constant, and any such constant bounds the supremum.
--
--   **Formalization Note.** The Lipschitz constant is an existential witness, not a real supremum, so no convention for the supremum of an empty or unbounded set is involved. $|\cdot|$ is the Euclidean norm on `EuclideanSpace ℝ (Fin n)`.
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), p. 37, §2.2, Eq. (2.18)

import Mathlib

namespace TeschlODE.IVP

/-- Teschl, §2.2, p. 37, (2.18): `f` is locally Lipschitz continuous in the second argument,
uniformly with respect to the first, on `U`: for every compact `V₀ ⊆ U` the number
`sup_{(t,x) ≠ (t,y) ∈ V₀} |f(t,x) - f(t,y)| / |x - y|` is finite, i.e. there is a constant `L`
with `|f(t,x) - f(t,y)| ≤ L |x - y|` whenever `(t,x), (t,y) ∈ V₀`. -/
def LocallyLipschitzSecond {n : ℕ} (U : Set (ℝ × EuclideanSpace ℝ (Fin n)))
    (f : ℝ × EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) : Prop :=
  ∀ V₀ : Set (ℝ × EuclideanSpace ℝ (Fin n)), V₀ ⊆ U → IsCompact V₀ →
    ∃ L : ℝ, ∀ t : ℝ, ∀ x y : EuclideanSpace ℝ (Fin n),
      (t, x) ∈ V₀ → (t, y) ∈ V₀ → ‖f (t, x) - f (t, y)‖ ≤ L * ‖x - y‖

end TeschlODE.IVP


