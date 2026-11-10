-- Prove2me | Definitions.Def_SuperlatSVP_Sec41Setting
-- name    : SuperlatSVP_Sec41Setting
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T21:46:20.986852+00:00
-- url     : https://prove2.me/theorems/b0e08e87-10a1-417b-bfd8-88e00f08ae3e
-- title:
--   The standing assumptions of §4.1: $\det L=1$, (2.3) with $b=2^\beta\ge\sqrt{4/3}$, $\lambda_1\le\lambda\le(1+n^{-2})\lambda_1$, and the prime range (4.7)
-- statement:
--   Section 4.1 fixes the following setting, used by Lemmas 4.1–4.3. The input is a basis $B$ and $L=B\mathbb Z^n$. A length estimate $\lambda$, an exponent $\beta$ with $b=2^\beta$, and an integer $p$ satisfy:
--
--   1. $\det L=1$, i.e. $|\det B|=1$;
--   2. the point-count bound (2.3) with its prefactor absorbed into $b$ (p.14: "absorb it into $b$ by using $b=2^\beta A_n^{1/n}$"), and $b\ge\sqrt{4/3}$:
--   $$N_L(r\lambda_1(L))\le b^n r^n\qquad(r\ge1);$$
--   3. $\lambda_1(L)\le\lambda\le(1+n^{-2})\,\lambda_1(L)$;
--   4. the range (4.7) for $p$, where $q=2^{\lceil n/\log_2 n\rceil}$ and $A$ is the midpoint shell:
--   $$\frac{q\,(3b^2/4)^{n/2}}{\operatorname{vol}(A)}\le p\le\frac{2q\,(3b^2/4)^{n/2}}{\operatorname{vol}(A)} .$$
--
--   Primality of $p$ is assumed separately in each statement.
--
--   **Formalization Note** $\beta$ is any real number, so the absorbed exponent $\beta+\tfrac1n\log_2A_n$ is covered. $\operatorname{vol}(A)$ is finite and is used as a real number.
-- source:
--   Hhan, Kim, Kim, Laarhoven, Superlattice methods for the shortest vector problem and discrete Gaussian sampling, STOC 2027 submission (manuscript sha256 fcf5b14f…ba), §4.1, p.32 (PDF p.32), footnote 2; (4.7); §2.1, p.14

import Mathlib
import Definitions.Def_SuperlatSVP_lat
import Definitions.Def_SuperlatSVP_shellA

open MeasureTheory

namespace SuperlatSVP

/-- The standing assumptions of §4.1 (p.32), for the input basis `B`, the length estimate `λ`, the
point-count exponent `β` and the modulus `p` (primality is assumed separately):

1. "the input lattice is L = BZⁿ with det L = 1": `|det B| = 1`;
2. "We use the point-count bound (2.3) with b = 2^β ≥ √(4/3)", with the prefactor absorbed into
   `b` (p.14: "absorb it into b by using b = 2^βAₙ^{1/n}"): `N_L(rλ₁(L)) ≤ bⁿrⁿ` for `r ≥ 1`;
3. "the algorithm is given the estimation λ of λ1(L) satisfying λ1(L) ≤ λ ≤ (1+n^{−2})λ1(L)";
4. (4.7): `q(3b²/4)^{n/2}/vol(A) ≤ p ≤ 2q(3b²/4)^{n/2}/vol(A)`, `q = 2^{⌈n/log₂ n⌉}`.

**Formalization Note.** `b = 2^β` with `β` real, so the absorbed bound is `PointCountBound` with the
constant prefactor `1`. `vol(A)` is the (finite) Lebesgue volume of the midpoint shell as a real. -/
def Sec41Setting (n : ℕ) (B : Matrix (Fin n) (Fin n) ℝ) (lam β : ℝ) (p : ℕ) : Prop :=
  |B.det| = 1 ∧
  Real.sqrt (4 / 3) ≤ (2 : ℝ) ^ β ∧
  PointCountBound (lat B) (fun _ => 1) β ∧
  lam1 (lat B) ≤ lam ∧ lam ≤ (1 + ((n : ℝ) ^ 2)⁻¹) * lam1 (lat B) ∧
  (chainQ n : ℝ) * (3 * ((2 : ℝ) ^ β) ^ 2 / 4) ^ ((n : ℝ) / 2) / (volume (shellA n lam)).toReal
      ≤ (p : ℝ) ∧
  (p : ℝ) ≤ 2 * (chainQ n : ℝ) * (3 * ((2 : ℝ) ^ β) ^ 2 / 4) ^ ((n : ℝ) / 2) /
      (volume (shellA n lam)).toReal

end SuperlatSVP


