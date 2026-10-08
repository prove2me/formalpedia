-- Prove2me | Definitions.Def_OTDRO_StrongCvx_Assumptions
-- name    : OTDRO_StrongCvx_Assumptions
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T21:09:31.064479+00:00
-- url     : https://prove2.me/theorems/36f06062-595f-416d-ab97-3e5790d00427
-- title:
--   Assumptions 3–5 and the uniform squared-derivative bounds
-- statement:
--   Assumption 3 requires a twice differentiable loss with $\ell''(u)\le M$ for all $u$, where $M>0$, and requires $\ell'(\beta^{\mathsf T}X)$ to be nonzero with positive probability for every $\beta\in B$. Assumption 4 requires $B$ to be compact and convex, with radius $R_\beta=\sup_{\beta\in B}\|\beta\|$. Assumption 5 requires local strong convexity of $\ell$ and, separately for each $\beta\in B$, constants $c_1,c_2>0$ and $p\in(0,1)$ such that
--
--   $$P_0\bigl(|\ell'(\beta^{\mathsf T}X)|>c_1,\ |\beta^{\mathsf T}X|>c_2\|\beta\|\bigr)\ge p.$$
--
--   The auxiliary predicate for Lemma 6 records positive uniform bounds $\underline L\le\mathbb E_{P_0}[\ell'(\beta^{\mathsf T}X)^2]\le\overline L$ for every $\beta\in B$. These assumptions determine the regime of the strong-convexity results.
--
--   **Formalization Note** Local strong convexity is a positive lower bound on $\ell''$ on each compact interval, the form used in the paper's proof. Squared-derivative integrability is explicit in the auxiliary predicate. The constants in Assumption 5 retain the paper's per-$\beta$ quantifier order.
-- source:
--   Blanchet, Murthy & Zhang, arXiv:1810.02403v3, Assumptions 3–5, pp. 10–11; Lemma 6, p. 33

import Mathlib
import Definitions.Def_OTDRO_Dual_Setting

namespace OTDRO.StrongCvx

open MeasureTheory

/-- Assumption 3, p. 10: a twice differentiable convex loss has a positive global upper
bound on its second derivative; its first derivative is nonzero with positive probability
at every decision in B. Convexity itself belongs to Assumption 2. -/
structure Assumption3 {d : ℕ} (P0 : Measure (EuclideanSpace ℝ (Fin d)))
    (ℓ : ℝ → ℝ) (B : Set (EuclideanSpace ℝ (Fin d))) (M : ℝ) : Prop where
  differentiable : Differentiable ℝ ℓ
  deriv_differentiable : Differentiable ℝ (deriv ℓ)
  M_pos : 0 < M
  second_deriv_le : ∀ u, deriv (deriv ℓ) u ≤ M
  nonzero_deriv : ∀ β ∈ B, ¬ (∀ᵐ x ∂P0, deriv ℓ (inner ℝ β x) = 0)

/-- Assumption 4, p. 11: the decision region is convex and compact. -/
structure Assumption4 {d : ℕ} (B : Set (EuclideanSpace ℝ (Fin d))) : Prop where
  convex : Convex ℝ B
  compact : IsCompact B

/-- The radius R_β = sup_{β∈B} ‖β‖ from Assumption 4, p. 11. Used only for
nonempty compact B. -/
noncomputable def Rbeta {d : ℕ} (B : Set (EuclideanSpace ℝ (Fin d))) : ℝ :=
  sSup ((fun β => ‖β‖) '' B)

/-- Assumption 5, p. 11. The constants c₁,c₂,p may depend on β as printed.
Local strong convexity means a positive lower bound on ℓ'' on every compact interval. -/
structure Assumption5 {d : ℕ} (P0 : Measure (EuclideanSpace ℝ (Fin d)))
    (ℓ : ℝ → ℝ) (B : Set (EuclideanSpace ℝ (Fin d))) : Prop where
  locally_strongly_convex : ∀ R : ℝ, ∃ c : ℝ, 0 < c ∧
    ∀ u : ℝ, |u| ≤ R → c ≤ deriv (deriv ℓ) u
  nondegenerate : ∀ β ∈ B, ∃ c1 c2 p : ℝ,
    0 < c1 ∧ 0 < c2 ∧ 0 < p ∧ p < 1 ∧
    ENNReal.ofReal p ≤ P0 {x | c1 < |deriv ℓ (inner ℝ β x)| ∧
      c2 * ‖β‖ < |inner ℝ β x|}

/-- The pair of uniform bounds furnished by Lemma 6, with integrability explicit
so that the expectations denote mathematical expectations. -/
def DerivSqBounds {d : ℕ} (P0 : Measure (EuclideanSpace ℝ (Fin d)))
    (ℓ : ℝ → ℝ) (B : Set (EuclideanSpace ℝ (Fin d)))
    (Llow Lbar : ℝ) : Prop :=
  0 < Llow ∧ 0 < Lbar ∧ ∀ β ∈ B,
    Integrable (fun x => (deriv ℓ (inner ℝ β x)) ^ 2) P0 ∧
    Llow ≤ ∫ x, (deriv ℓ (inner ℝ β x)) ^ 2 ∂P0 ∧
    ∫ x, (deriv ℓ (inner ℝ β x)) ^ 2 ∂P0 ≤ Lbar

end OTDRO.StrongCvx


