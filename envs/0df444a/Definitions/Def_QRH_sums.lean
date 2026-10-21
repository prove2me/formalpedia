-- Prove2me | Definitions.Def_QRH_sums
-- name    : QRH_sums
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-20T12:02:25.643258+00:00
-- url     : https://prove2.me/theorems/73f87c6a-e02f-4244-8324-6599c86a7c5b
-- title:
--   The smoothed twisted Mobius sums and the completed dual energy family
-- statement:
--   QRHSums is the interface for the finite sums of the source over a fixed arithmetic world: a finite truncation of the elements prime to S to norm at most X, the primary primes with norm in (Y/2, Y], the elements prime to S of norm at most X divisible by a prime p, with the divisor-count bound that the count is at most cdiv X / N p, Landau's prime ideal theorem in the uniform form that the number of such primes is at least cL Y / log Y for Y >= 2, a dyadic range of auxiliary indices F <= N f < 2F, and the squarefree elements prime to S of norm at most X. Over this data the bundle defines the smoothed twisted Mobius sum A_u(D): the finite sum over the elements prime to S of the coefficient c n twisted by the sextic symbol chi_n(u) of the row u and weighted by Wt at N n / D; the untwisted sum A_1(D) at the row u = 1; the mean square msSum of the family over the rows of norm at most H, which is the left-hand side of the mean-square estimate of Proposition 3.1; and the completed dual energy family E(H, X, F) of section 6: the mean square, over the auxiliary indices f in a dyadic range and the rows k of norm at most H, of the squarefree-index column sums with the cubic Gauss-sum coefficients and the sextic twist chi_n(f)^4, normalized by X F. The canonical estimate for this family is the engine of the mean-square estimate.
-- source:
--   The Quasi-Riemann Hypothesis, October 2026, Sections 2, 3, and 6 (equations 2.2, 3.1, and 6.3).

import Mathlib
import Definitions.Def_QRH_arith

universe u

/-!
# The Quasi-Riemann Hypothesis: the smoothed sums and the dual family

The finite sums of the source, in the form of an interface: the
truncation of the ideals prime to the fixed set S into finite sets, the
smoothed twisted Möbius sums A_u(D) of equation 2.2, their mean square
over the rows — the left-hand side of the mean-square estimate of
Proposition 3.1 — and the completed dual energy family E(H, X, F) of
section 6, together with the counting inputs of the prime-extraction
step: Landau's prime ideal theorem and the divisor-count bound of
section 3.
-/

namespace QRH

/-- The truncation and counting data of the smoothed sums. The source's
sums run over the ideals of the Eisenstein integers prime to the fixed
set S, weighted by a smooth compactly supported function of the norm;
the interface replaces the support condition by a finite truncation and
carries the counting theorems — Landau's prime ideal theorem in the
uniform form supplied by the paper, and the divisor-count bound — as
fields. -/
structure QRHSums (W : QRHWorld.{u}) where
  /-- the elements prime to S of norm at most X -/
  fin : ℝ → Finset W.E
  fin_spec : ∀ (X : ℝ) (n : W.E), n ∈ fin X ↔ (W.Sgood n ∧ W.N n ≤ X)
  /-- the primary primes with Y / 2 < N p ≤ Y: the rows p⁶ of the
  extraction step of section 3 -/
  primeRange : ℝ → Finset W.E
  primeRange_spec : ∀ (Y : ℝ) (p : W.E),
    p ∈ primeRange Y ↔ (W.IsP p ∧ Y / 2 < W.N p ∧ W.N p ≤ Y)
  /-- the elements prime to S, of norm at most X, and divisible by p -/
  divBy : W.E → ℝ → Finset W.E
  divBy_spec : ∀ (p n : W.E) (X : ℝ),
    n ∈ divBy p X ↔ (p ∈ W.divs n ∧ W.Sgood n ∧ W.N n ≤ X)
  /-- the constant of the divisor-count bound -/
  cdiv : ℝ
  count_divisor : ∀ (p : W.E) (X : ℝ), W.IsP p → 0 < X →
    ((divBy p X).card : ℝ) ≤ cdiv * X / W.N p
  /-- the constant of Landau's prime ideal theorem -/
  cL : ℝ
  landau : ∀ (Y : ℝ), 2 ≤ Y → cL * Y / Real.log Y ≤ ((primeRange Y).card : ℝ)
  /-- a dyadic range of auxiliary indices F ≤ N f < 2F -/
  dyad : ℝ → Finset W.E
  dyad_spec : ∀ (F : ℝ) (f : W.E),
    f ∈ dyad F ↔ (F ≤ W.N f ∧ W.N f < 2 * F)
  /-- the squarefree elements prime to S, of norm at most X -/
  sqfs : ℝ → Finset W.E
  sqfs_spec : ∀ (X : ℝ) (n : W.E),
    n ∈ sqfs X ↔ (W.IsSqf n ∧ W.Sgood n ∧ W.N n ≤ X)

/-- The smoothed twisted Möbius sum A_u(D) of the source (equation 2.2):
the coefficient sequence c, twisted by the sextic symbol χ_n(u) of the
row u, weighted by the function Wt at N n / D, truncated to the elements
prime to S of norm at most X. -/
noncomputable def Asum (W : QRHWorld) (S : QRHSums W) (c : W.E → ℂ) (u : W.E)
    (Wt : ℝ → ℂ) (D X : ℝ) : ℂ :=
  ∑ n ∈ S.fin X, c n * W.chi n u * Wt (W.N n / D)

/-- The untwisted sum A₁(D): the row u = 1 of the family, the smoothed
ν-twisted Möbius sum whose power saving implies the zero-free
half-plane. -/
noncomputable def A1sum (W : QRHWorld) (S : QRHSums W) (c : W.E → ℂ)
    (Wt : ℝ → ℂ) (D X : ℝ) : ℂ :=
  Asum W S c W.one Wt D X

/-- The mean square of the family over the rows of norm at most H: the
left-hand side of the mean-square estimate of Proposition 3.1. -/
noncomputable def msSum (W : QRHWorld) (S : QRHSums W) (c : W.E → ℂ) (Wt : ℝ → ℂ)
    (H D X : ℝ) : ℝ :=
  ∑ u ∈ S.fin H, ‖Asum W S c u Wt D X‖ ^ 2

/-- The completed dual energy family E(H, X, F) of section 6 of the
source (equation 6.3): the mean square, over the auxiliary indices f in
a dyadic range and the rows k of norm at most H, of the squarefree-index
column sums with the cubic Gauss-sum coefficients and the sextic twist
χ_n(f)⁴, normalized by X F. The canonical estimate for this family —
proved in the source from the quadratic large sieve, the theta
transformation, and the admissible-exponent descent — is the engine of
the mean-square estimate. -/
noncomputable def Eener (W : QRHWorld) (S : QRHSums W) (coef : W.E → ℂ) (Wt : ℝ → ℂ)
    (H X F : ℝ) : ℝ :=
  1 / (X * F) * ∑ f ∈ S.dyad F, ∑ k ∈ S.fin H,
    ‖∑ n ∈ S.sqfs (2 * X),
      coef n * W.chi n k * W.chi n f ^ 4 * Wt (W.N n / X)‖ ^ 2

end QRH


