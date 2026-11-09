-- Prove2me | Definitions.Def_OptimalTraceDistance_Estimation_Scalar
-- name    : OptimalTraceDistance_Estimation_Scalar
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T05:34:13.207435+00:00
-- url     : https://prove2.me/theorems/37fa2aac-aa55-4d93-8876-9f7ee3ea8ce2
-- title:
--   Jackson approximation, Chebyshev filters and divided differences
-- statement:
--   The normalized Jackson kernel $J_M$ has its removable singularities completed by continuity. The polynomial $g_K$ is its finite Chebyshev convolution with $\operatorname{sgn}(\cos\theta)$, using the coefficient formula on p.25, and $q_K$ is its polynomial antiderivative with value zero at zero. Thus the family is computed from Appendix A.1 rather than chosen by an approximation guarantee. Set $q_{K,s}(x)=s q_K(x/s)$ and $E_{K,s}(U)=\operatorname{tr}(|U|-q_{K,s}(U))$.
--
--   The filter $r_m$ is the polynomial quotient of $1-T_m(1-x)$ by $m^2x$, computed by shifting coefficients. For $b\ge1/32$, $R_b=1$; otherwise $R_b=2r_m-r_m^2$ for $m=\lfloor(8b)^{-1/2}\rfloor$. Divided differences are defined on monomials by the finite composition sum (69), including repeated nodes. A separated representation retains its finite factors and a sum of products of uniform factor bounds; a pointwise bound alone does not satisfy it. Analytic estimates are separate open theorems.
-- source:
--   Ziyun Chen, Minbo Gao, Qisheng Wang, STOC 2027 submission #875 (October 2026), §§2.2–2.3, Appendices A.1, B.1, B.3, pp.7–8,24–26,28.

import Definitions.Def_OptimalTraceDistance_Estimation_Core

open scoped BigOperators Matrix
noncomputable section

namespace OptimalTraceDistance.Estimation

def sign (x : ℝ) : ℝ := if x < 0 then -1 else if x = 0 then 0 else 1
/-- Appendix A.1 (56), continuous completion at removable singularities. -/
def jackson (M : ℕ) (t : ℝ) : ℝ :=
  3 / (2 * Real.pi * M * (2 * (M : ℝ)^2 + 1)) *
    (if Real.sin (t/2) = 0 then (M : ℝ) else Real.sin (M*t/2) / Real.sin (t/2))^4

/-- The finite Chebyshev expansion of the convolution in (59), using the coefficients on p.25. -/
def jacksonDerivative (K : ℕ) : Polynomial ℝ :=
  ∑ l ∈ Finset.range K,
    Polynomial.C (if l = 0 then 0 else
      4 * Real.sin (Real.pi * l / 2) / (Real.pi * l) *
        ∫ t in (-Real.pi)..Real.pi, jackson (K / 2 + 1) t * Real.cos (l*t)) *
      Polynomial.Chebyshev.T ℝ l

/-- Integrate that actual polynomial with constant term zero, not a choice satisfying an estimate. -/
def q (K : ℕ) : Polynomial ℝ :=
  ∑ j ∈ (jacksonDerivative K).support,
    Polynomial.C ((jacksonDerivative K).coeff j / (j+1 : ℝ)) * Polynomial.X^(j+1)

def qScaled (K : ℕ) (s : ℝ) : Polynomial ℝ :=
  Polynomial.C s * (q K).comp (Polynomial.C s⁻¹ * Polynomial.X)
def matrixEval {d : ℕ} (p : Polynomial ℝ) (A : Mat d) : Mat d :=
  ∑ k ∈ p.support, (p.coeff k : ℂ) • A^k
def traceError {d : ℕ} (K : ℕ) (s : ℝ) (A : Mat d) : ℝ :=
  tr (absMat A - matrixEval (qScaled K s) A)

/-- Polynomial quotient by X via coefficients; no 0/0 at the origin. -/
def rFilter (m : ℕ) : Polynomial ℝ :=
  let p := 1 - (Polynomial.Chebyshev.T ℝ m).comp (1 - Polynomial.X)
  ∑ j ∈ Finset.range m,
    Polynomial.C (p.coeff (j+1) / (m : ℝ)^2) * Polynomial.X^j

def filter (b : ℝ) : Polynomial ℝ :=
  if 1/32 ≤ b then 1 else
    let r := rFilter ⌊1 / Real.sqrt (8*b)⌋₊
    2*r-r^2

/-- (69), including repeated nodes and the zero divided difference when a>k. -/
def dividedDifference (p : Polynomial ℝ) (a : ℕ) (x : Fin (a+1) → ℝ) : ℝ :=
  ∑ k ∈ p.support, if a ≤ k then
    p.coeff k * ∑ r ∈ (Finset.pi Finset.univ (fun _ : Fin (a+1) => Finset.range (k+1))).filter
      (fun r => (∑ i, r i (Finset.mem_univ i)) = k-a),
      ∏ i, x i ^ (r i (Finset.mem_univ i))
    else 0

/-- A separated finite sum with uniform factor bounds. Existence of the sum is theorem content. -/
def HasSeparatedBound (a : ℕ) (I : Set ℝ) (f : (Fin (a+1) → ℝ) → ℝ) (M : ℝ) : Prop :=
  ∃ (L : ℕ) (c : Fin L → ℝ) (g : Fin L → Fin (a+1) → ℝ → ℝ)
      (B : Fin L → Fin (a+1) → ℝ),
    (∀ α i, 0 ≤ B α i ∧ ∀ x ∈ I, |g α i x| ≤ B α i) ∧
    (∀ x, (∀ i, x i ∈ I) → f x = ∑ α, c α * ∏ i, g α i (x i)) ∧
    (∑ α, |c α| * ∏ i, B α i) ≤ M

end OptimalTraceDistance.Estimation


