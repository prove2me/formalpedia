-- Prove2me | Definitions.Def_ShapeSOS_ConvexConsistency_Approximation
-- name    : ShapeSOS_ConvexConsistency_Approximation
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T23:21:57.076995+00:00
-- url     : https://prove2.me/theorems/ef4fa88d-5687-4522-9e87-ff5bfc709b55
-- title:
--   The printed Bernstein polynomial and mixed within-box derivatives
-- statement:
--   For a function $f$ and integer $d\ge0$, the printed polynomial is
--   $$B_d(f,x)=\sum_{j_1+\cdots+j_n=d}f(j_1/d,\ldots,j_n/d)\prod_i {d\choose j_i}x_i^{j_i}(1-x_i)^{d-j_i}.$$
--   The indices are nonnegative integers; each automatically lies between zero and $d$. The sum is deliberately the one printed in Lemma B.5, even though it is not the usual tensor-product Bernstein formula. At $d=0$ Lean division returns zero; this initial value does not affect the limit as $d$ grows.
--
--   For a nonnegative multi-index $k$, mixed derivatives apply the coordinate derivative within the box repeatedly in coordinate order. On the stated smooth domain these are the usual mixed derivatives. This module contains the formula and derivative operation, without any approximation assertion.
-- source:
--   Curmei and Hall, Shape-Constrained Regression using Sum of Squares Polynomials, arXiv:2004.03853v3, p. 26, Lemma B.5

import Definitions.Def_ShapeSOS_ConvexConsistency_Geometry

set_option autoImplicit false
open scoped BigOperators

namespace ShapeSOS.ConvexConsistency
noncomputable section

/-- Printed B.5 formula: sum of indices equals d, not the tensor-product cube index set. -/
def bernstein {n : ℕ} (d : ℕ) (f : Vec n → ℝ) : Poly n :=
  ∑ j ∈ (Finset.univ : Finset (Fin n → Fin (d+1))).filter
      (fun j => ∑ i, (j i).val = d),
    MvPolynomial.C (f (fun i => ((j i).val : ℝ) / (d : ℝ))) *
      ∏ i, MvPolynomial.C ((Nat.choose d (j i).val : ℕ) : ℝ) *
        MvPolynomial.X i ^ (j i).val * (1 - MvPolynomial.X i) ^ (d - (j i).val)

/-- Mixed partials in coordinate order, with the same within-box boundary convention. -/
def mixedPartial {n : ℕ} (S : Set (Vec n)) (k : Fin n → ℕ)
    (f : Vec n → ℝ) : Vec n → ℝ :=
  (List.finRange n).foldl (fun g i => (fun h => partialWithin S h i)^[k i] g) f

end
end ShapeSOS.ConvexConsistency


