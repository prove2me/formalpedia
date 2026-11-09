-- Prove2me | Definitions.Def_NetworkEquilibriumCLS_LinearNash_Quadratics
-- name    : NetworkEquilibriumCLS_LinearNash_Quadratics
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:16:10.268735+00:00
-- url     : https://prove2.me/theorems/7dc9b359-9fe3-4033-bc64-0ccc7a3f38c4
-- title:
--   Rational quadratics, box KKT signs, and integer Boolean polynomials
-- statement:
--   Let m and n be finite dimensions. A rational quadratic is specified by a symmetric rational matrix Q and a rational vector c, and is evaluated on real vectors by
--
--   $$p(z)=\tfrac12\sum_{i,j}Q_{ij}z_i z_j+\sum_i c_i z_i,\qquad F_i(z)=\sum_jQ_{ij}z_j+c_i.$$
--
--   A point z is an exact box KKT point for minimization when z belongs to [0,1]^m and each coordinate satisfies z_i>0 implies F_i(z)≤0 and z_i<1 implies F_i(z)≥0. The approximate version replaces these two bounds by ε and −ε, with ε≥0. Bilinear quadratics have Q_{ii}=0. Diagonal normalization is a separate predicate, not a restriction on the general quadratic input.
--
--   For an integer vector β and upper-triangular integer coefficients w, define h(u)=Σ_q β_q u_q+Σ_{q<r}w_{qr}u_qu_r on all real vectors. Boolean local minimality means that no individual bit flip reduces h. The coordinate derivative of a function is the ordinary derivative along the coordinate-update line. Thus the KKT relation for a supplied polynomial uses its actual derivatives.
--
--   These objects provide the common analytic interface for the rounding, decoding, and coordination lemmas. Finite sums have their usual empty values; the theorems that use positive dimensions state positivity explicitly.
-- source:
--   Ioannis Anagnostides, Ioannis Panageas, Jingming Yan, STOC 2027 submission #653 (October 2026), p.6 (PDF 7), §2.1, Eq. (1), Definition 2.1; p.8 (PDF 9), §3, Eq. (2).

import Mathlib

open Finset

noncomputable section

namespace NetworkEquilibriumCLS.LinearNash

/-- Rational quadratic data, Eq. (1), printed p.6 (PDF 7).
Symmetry is validity data; there is no convexity or diagonal normalization here. -/
structure Quadratic (m : ℕ) where
  Q : Fin m → Fin m → ℚ
  c : Fin m → ℚ
  symmetric : ∀ i j, Q i j = Q j i

noncomputable def quadraticValue {m : ℕ} (p : Quadratic m) (z : Fin m → ℝ) : ℝ :=
  (∑ i, ∑ j, (p.Q i j : ℝ) * z i * z j) / 2 + ∑ i, (p.c i : ℝ) * z i

noncomputable def sourceGradient {m : ℕ} (p : Quadratic m) (z : Fin m → ℝ) (i : Fin m) : ℝ :=
  ∑ j, (p.Q i j : ℝ) * z j + p.c i

def InCube {ι : Type*} (z : ι → ℝ) : Prop := ∀ i, 0 ≤ z i ∧ z i ≤ 1

/-- Definition 2.1, including both boundary signs. -/
def BoxSigns {ι : Type*} (F : ι → ℝ) (z : ι → ℝ) (ε : ℝ) : Prop :=
  InCube z ∧ ∀ i, (0 < z i → F i ≤ ε) ∧ (z i < 1 → -ε ≤ F i)

noncomputable def QuadraticKKT {m : ℕ} (p : Quadratic m) (z : Fin m → ℝ) : Prop :=
  BoxSigns (sourceGradient p z) z 0

noncomputable def ApproxQuadraticKKT {m : ℕ} (p : Quadratic m) (ε : ℝ) (z : Fin m → ℝ) : Prop :=
  0 ≤ ε ∧ BoxSigns (sourceGradient p z) z ε

/-- A genuine coordinate derivative of the specified function, not a prescribed gradient. -/
noncomputable def coordinatePartial {ι : Type*} [DecidableEq ι] (f : (ι → ℝ) → ℝ)
    (v : ι → ℝ) (i : ι) : ℝ :=
  deriv (fun t => f (Function.update v i t)) (v i)

noncomputable def FunctionKKT {ι : Type*} [DecidableEq ι] (f : (ι → ℝ) → ℝ) (v : ι → ℝ) : Prop :=
  BoxSigns (coordinatePartial f v) v 0

def IsBilinear {m : ℕ} (p : Quadratic m) : Prop := ∀ i, p.Q i i = 0

def IsNormalized {m : ℕ} (p : Quadratic m) : Prop := ∀ i, |p.Q i i| ≤ 1

/-- Integer bilinear polynomial of §3, p.8 (PDF 9). Only upper triangular entries are used. -/
structure BooleanPolynomial (n : ℕ) where
  beta : Fin n → ℤ
  weight : Fin n → Fin n → ℤ

noncomputable def booleanValue {n : ℕ} (h : BooleanPolynomial n) (u : Fin n → ℝ) : ℝ :=
  ∑ q, (h.beta q : ℝ) * u q +
    ∑ q, ∑ r ∈ univ.filter (q < ·), (h.weight q r : ℝ) * u q * u r

noncomputable def booleanGradient {n : ℕ} (h : BooleanPolynomial n) (u : Fin n → ℝ)
    (q : Fin n) : ℝ :=
  h.beta q + ∑ r ∈ univ.filter (· ≠ q),
    (if q < r then (h.weight q r : ℝ) else (h.weight r q : ℝ)) * u r

/-- The real-domain version, for a vector already known to be Boolean. -/
noncomputable def BooleanLocalMin {n : ℕ} (h : BooleanPolynomial n) (b : Fin n → ℝ) : Prop :=
  (∀ q, b q = 0 ∨ b q = 1) ∧
    ∀ q, booleanValue h b ≤ booleanValue h (Function.update b q (1 - b q))

end NetworkEquilibriumCLS.LinearNash


