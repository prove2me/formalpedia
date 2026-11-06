-- Prove2me | Definitions.Def_GeomDRSub_IsUpperLinearizable
-- name    : GeomDRSub_IsUpperLinearizable
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:10:10.667795+00:00
-- url     : https://prove2.me/theorems/523173bf-ed8b-4144-a5b0-90bb776c8228
-- title:
--   Upper-linearizability (Definition 3.2)
-- statement:
--   Let $\mathcal F$ be a class of functions on the cube, $K$ a set, $h$ a map with $h(K)\subseteq K$, and $g(f,x)\in\mathbb R^d$ a vector field. The triple is **upper-linearizable with parameters $\alpha,\beta>0$** if, for every $f\in\mathcal F$,
--   $$
--   \alpha f(o)-f(h(x))\le\beta\,\langle g(f,x),\,o-x\rangle\qquad(x,o\in K).
--   $$
--   The action map does not depend on $f$ and the field does not depend on $o$.
-- source:
--   Aggarwal–Lu, Geometry-Dependent Online and Offline Approximation for Non-Monotone DR-Submodular Maximization, arXiv:2610.00545, Definition 3.2, p.9, Eq. (10)

import Mathlib

namespace GeomDRSub

/-- **Upper-linearizability (Definition 3.2).** Aggarwal–Lu, arXiv:2610.00545, p.9: "A function
class on `Q`, an action map `h : K → K`, and a vector field `g(f, x) ∈ ℝᵈ` are upper-linearizable
with parameters `α, β > 0` if, for every `f` in the class,
`αf(o) − f(h(x)) ≤ β⟨g(f, x), o − x⟩` `(x, o ∈ K)`. (10)
The action map is independent of `f`, and the vector field is independent of `o`."

**Formalization Note.** The class is a set `𝓕` of real functions on `ℝᵈ` (only their values on the
cube matter); `h : K → K` is a map `ℝᵈ → ℝᵈ` sending `K` into `K`. The independence requirements
are the typing: `h` takes no `f`, and `g` takes no `o`. -/
def IsUpperLinearizable {d : ℕ} (𝓕 : Set (EuclideanSpace ℝ (Fin d) → ℝ))
    (K : Set (EuclideanSpace ℝ (Fin d)))
    (h : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (g : (EuclideanSpace ℝ (Fin d) → ℝ) → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (α β : ℝ) : Prop :=
  0 < α ∧ 0 < β ∧ (∀ x ∈ K, h x ∈ K) ∧
    ∀ f ∈ 𝓕, ∀ x ∈ K, ∀ o ∈ K, α * f o - f (h x) ≤ β * inner ℝ (g f x) (o - x)

end GeomDRSub


