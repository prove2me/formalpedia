-- Prove2me | Definitions.Def_NetworkEquilibriumCLS_LinearNash_Potential
-- name    : NetworkEquilibriumCLS_LinearNash_Potential
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:16:47.76565+00:00
-- url     : https://prove2.me/theorems/56ef2c5f-945f-44f6-bc1a-105cd9cc41e3
-- title:
--   The complete bilinear potential and residual of Section 4
-- statement:
--   Let p be a rational quadratic in m variables and h an integer square-free quadratic in n variables. Each block q has independent real coordinates x_q,y_q,s_q,s′_q. Put z_q=(x_q+y_q)/2, d_q=x_q−y_q, and s̄_q=(s_q+s′_q)/2. Symmetrize the upper-triangular weights of h with zero diagonal. Set
--
--   $$W=1+\max_q\sum_{r\ne q}|w_{qr}|,\quad \tau=\frac1{4mW},\quad \widetilde b_q=\bar s_q-\tau\sum_j d_{q,j}.$$
--
--   The finite maximum defaults to zero before adding one if n=0; all Section 4 statements require m,n>0. The shifted vector is not clipped. With the two-copy polynomial P of Eq. (4) and the correction P̂=P−Σ_{i<j}(x_i−y_i)(x_j−y_j), define
--
--   $$\Phi=h(\widetilde b)+\sum_q\left(\frac{\tau^2}4\widehat P(x_q,y_q)+\frac\tau4\bar s_q\sum_jd_{q,j}-\frac18s_qs'_q\right),\quad R_q=\nabla h(\widetilde b)_q-\frac{\widetilde b_q}4.$$
--
--   The code evaluates these actual polynomials. Its coordinates form n copies of two m-vectors and two scalar controls; no derivative identity or decoding conclusion is built into validity. This definition is shared by all four analytic milestones.
-- source:
--   Ioannis Anagnostides, Ioannis Panageas, Jingming Yan, STOC 2027 submission #653 (October 2026), pp.10–11 (PDF 11–12), §4.1, Eqs. (3)–(7).

import Mathlib
import Definitions.Def_NetworkEquilibriumCLS_LinearNash_Quadratics

open Finset

noncomputable section

namespace NetworkEquilibriumCLS.LinearNash

/-- Coordinates x,y,s,s′ of §4.1: n(2m+2) independent real coordinates. -/
abbrev Coordinate (m n : ℕ) := Fin n × ((Bool × Fin m) ⊕ Bool)

def xIndex {m n : ℕ} (q : Fin n) (i : Fin m) : Coordinate m n := (q, .inl (false, i))
def yIndex {m n : ℕ} (q : Fin n) (i : Fin m) : Coordinate m n := (q, .inl (true, i))
def sIndex {m n : ℕ} (q : Fin n) : Coordinate m n := (q, .inr false)
def tIndex {m n : ℕ} (q : Fin n) : Coordinate m n := (q, .inr true)

def copyX {m n : ℕ} (v : Coordinate m n → ℝ) (q : Fin n) (i : Fin m) : ℝ := v (xIndex q i)
def copyY {m n : ℕ} (v : Coordinate m n → ℝ) (q : Fin n) (i : Fin m) : ℝ := v (yIndex q i)
def controlS {m n : ℕ} (v : Coordinate m n → ℝ) (q : Fin n) : ℝ := v (sIndex q)
def controlT {m n : ℕ} (v : Coordinate m n → ℝ) (q : Fin n) : ℝ := v (tIndex q)
def averageZ {m n : ℕ} (v : Coordinate m n → ℝ) (q : Fin n) (i : Fin m) : ℝ :=
  (copyX v q i + copyY v q i) / 2
def differenceD {m n : ℕ} (v : Coordinate m n → ℝ) (q : Fin n) (i : Fin m) : ℝ :=
  copyX v q i - copyY v q i
def controlAverage {m n : ℕ} (v : Coordinate m n → ℝ) (q : Fin n) : ℝ :=
  (controlS v q + controlT v q) / 2

/-- Symmetric off-diagonal coefficients; the supplied lower triangle is immaterial. -/
def symmetricWeight {n : ℕ} (h : BooleanPolynomial n) (q r : Fin n) : ℤ :=
  if q = r then 0 else if q < r then h.weight q r else h.weight r q

/-- Finite maximum, with default zero; equals the printed maximum when n>0. -/
def rowBound {n : ℕ} (h : BooleanPolynomial n) : ℕ :=
  1 + (univ.sup fun q => ∑ r, (symmetricWeight h q r).natAbs)

noncomputable def tau {n : ℕ} (m : ℕ) (h : BooleanPolynomial n) : ℝ :=
  1 / (4 * (m : ℝ) * (rowBound h : ℝ))

noncomputable def shiftedB {m n : ℕ} (h : BooleanPolynomial n) (v : Coordinate m n → ℝ)
    (q : Fin n) : ℝ := controlAverage v q - tau m h * ∑ j, differenceD v q j

noncomputable def twoCopy {m : ℕ} (p : Quadratic m) (x y : Fin m → ℝ) : ℝ :=
  (∑ i, (p.Q i i : ℝ) * x i * y i) +
    (∑ i, ∑ j ∈ univ.filter (i < ·), (p.Q i j : ℝ) * (x i + y i) * (x j + y j)) / 2 +
    ∑ i, (p.c i : ℝ) * (x i + y i)

noncomputable def correctedCopy {m : ℕ} (p : Quadratic m) (x y : Fin m → ℝ) : ℝ :=
  twoCopy p x y - ∑ i, ∑ j ∈ univ.filter (i < ·), (x i - y i) * (x j - y j)

/-- The actual polynomial (6), p.11 (PDF 12), evaluated also outside the cube. -/
noncomputable def potential {m n : ℕ} (p : Quadratic m) (h : BooleanPolynomial n)
    (v : Coordinate m n → ℝ) : ℝ :=
  booleanValue h (shiftedB h v) + ∑ q,
    ((tau m h)^2 / 4 * correctedCopy p (copyX v q) (copyY v q) +
     tau m h / 4 * controlAverage v q * (∑ j, differenceD v q j) -
     (1 / 8 : ℝ) * controlS v q * controlT v q)

noncomputable def residual {m n : ℕ} (h : BooleanPolynomial n) (v : Coordinate m n → ℝ)
    (q : Fin n) : ℝ := booleanGradient h (shiftedB h v) q - shiftedB h v q / 4

end NetworkEquilibriumCLS.LinearNash


