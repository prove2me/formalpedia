-- Prove2me | Definitions.Def_ConeLifts_Factorization_Supplement_IsConvexRadical
-- name    : ConeLifts_Factorization_Supplement_IsConvexRadical
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T10:45:22.79146+00:00
-- url     : https://prove2.me/theorems/56086800-76eb-4a33-aa31-9f64428ee7fe
-- title:
--   Real variety and convex radical ideal
-- statement:
--   For an ideal $I \subseteq \mathbb R[x_1, \dots, x_n]$, its **real variety** is $\mathcal V_{\mathbb R}(I) = \{x \in \mathbb R^n : f(x) = 0 \text{ for all } f \in I\}$. Let $C = \operatorname{conv}(\mathcal V_{\mathbb R}(I))$. The **convex radical** of $I$ is the ideal of all polynomials vanishing on $\mathcal V_{\mathbb R}(I) \cap \operatorname{ext}(C)$, and $I$ is **convex radical** if
--
--   $$
--   I = \{\, f \in \mathbb R[x] : f(x) = 0 \text{ for all } x \in \mathcal V_{\mathbb R}(I) \cap \operatorname{ext}(C) \,\}.
--   $$
--
--   Replacing $I$ by its convex radical does not change $C$, so §5.2 assumes this throughout.
--
--   **Formalization Note** Polynomials are `MvPolynomial (Fin n) ℝ`, evaluated at $x \in$ `EuclideanSpace ℝ (Fin n)` by `polyEval`.
-- source:
--   Gouveia, Parrilo & Thomas, Lifts of Convex Sets and Cone Factorizations, arXiv:1111.3164v2, pp. 20–21, §5.2 (real variety; convex radical ideal)

import Mathlib

namespace ConeLifts.Factorization.Supplement

/-- The value `f(x)` of a real polynomial `f ∈ ℝ[x₁, …, xₙ]` at a point `x ∈ ℝⁿ`
(`ℝⁿ = EuclideanSpace ℝ (Fin n)`, variables indexed by `Fin n`). -/
noncomputable def polyEval {n : ℕ} (x : EuclideanSpace ℝ (Fin n))
    (f : MvPolynomial (Fin n) ℝ) : ℝ :=
  MvPolynomial.eval (fun i => x i) f

/-- The **real variety** `𝒱_ℝ(I) = {x ∈ ℝⁿ : f(x) = 0 for all f ∈ I}` of an ideal
`I ⊆ ℝ[x₁, …, xₙ]` (Gouveia, Parrilo & Thomas, arXiv:1111.3164v2, §5.2, p. 20). -/
def realZeroSet {n : ℕ} (I : Ideal (MvPolynomial (Fin n) ℝ)) : Set (EuclideanSpace ℝ (Fin n)) :=
  {x | ∀ f ∈ I, polyEval x f = 0}

/-- `I` is a **convex radical ideal** (Gouveia, Parrilo & Thomas, arXiv:1111.3164v2, §5.2,
p. 21): `I` equals its convex radical `conv√I`, the ideal of all polynomials vanishing on
`𝒱_ℝ(I) ∩ ext(C)` with `C = conv(𝒱_ℝ(I))`. -/
def IsConvexRadical {n : ℕ} (I : Ideal (MvPolynomial (Fin n) ℝ)) : Prop :=
  (I : Set (MvPolynomial (Fin n) ℝ)) =
    {f | ∀ x ∈ realZeroSet I ∩ Set.extremePoints ℝ (convexHull ℝ (realZeroSet I)),
      polyEval x f = 0}

end ConeLifts.Factorization.Supplement


