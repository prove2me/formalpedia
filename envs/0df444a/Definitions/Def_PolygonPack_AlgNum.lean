-- Prove2me | Definitions.Def_PolygonPack_AlgNum
-- name    : PolygonPack_AlgNum
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:52:26.251849+00:00
-- url     : https://prove2.me/theorems/e68ae976-942b-4cbc-b7ac-cf2b0906eeca
-- title:
--   Exact real algebraic number: integer polynomial with an isolating rational interval
-- statement:
--   An **algebraic number description** is a list of integer coefficients, low degree first, with two rationals $\mathrm{lo},\mathrm{hi}$. It **denotes** the real number $r$ if the polynomial is nonzero, $r\in[\mathrm{lo},\mathrm{hi}]$, and $r$ is its only root in that interval.
--
--   For example, $x^2-2$ with the interval $[1,2]$ denotes $\sqrt2$, and with the interval $[-2,2]$ it denotes nothing. A rational $q=p/d$ is described by the coefficients $(-p,d)$ with $\mathrm{lo}=\mathrm{hi}=q$.
--
--   **Formalization Note** This is the per-coordinate form. The paper also mentions a real univariate representation of a whole configuration on p.46.
-- source:
--   Khan, Mathur, Constant Approximation Algorithms for Knapsack and Bin Packing for Convex Polygons, STOC 2027 submission (manuscript sha256 7a527fb3…), §2.7, p.13; App. F, F.1, p.48

import Mathlib

namespace PolygonPack

/-- **Exact real algebraic number.** Khan, Mathur, *Constant Approximation Algorithms for Knapsack and Bin Packing for Convex Polygons*, STOC 2027 submission (manuscript sha256 7a527fb3…), §2.7, p.13: "Placements are returned as exact real algebraic
numbers of polynomial description length", and App. F, F.1, p.48: "algebraic degree bounded by a
constant and a defining polynomial with coefficients of polynomial bit length"; root isolation, p.48.

`α : AlgNum` is an integer coefficient list (low degree first) with rational bounds. `AlgNum.Denotes α r`
says that the polynomial is nonzero and that `r` is its only root in `[lo, hi]`.

**Formalization Note.** This is the per-coordinate form. The paper also mentions a real univariate
representation of a whole configuration (p.46). A rational `q` is degree 1 with `lo = hi = q`.
The description length is bounded by the machine's running time wherever an `AlgNum` is an output. -/
structure AlgNum where
  /-- coefficients, low degree first -/
  coeffs : List ℤ
  /-- lower end of the isolating interval -/
  lo : ℚ
  /-- upper end of the isolating interval -/
  hi : ℚ

/-- The polynomial with the given coefficients, low degree first. -/
noncomputable def polyOf : List ℤ → Polynomial ℤ
  | [] => 0
  | c :: cs => Polynomial.C c + Polynomial.X * polyOf cs

/-- The defining polynomial of `α`. -/
noncomputable def AlgNum.poly (α : AlgNum) : Polynomial ℤ := polyOf α.coeffs

/-- `α` denotes the real number `r`: the only root of its nonzero polynomial in `[lo, hi]`. -/
def AlgNum.Denotes (α : AlgNum) (r : ℝ) : Prop :=
  α.poly ≠ 0 ∧ (α.lo : ℝ) ≤ r ∧ r ≤ (α.hi : ℝ) ∧ Polynomial.aeval r α.poly = 0 ∧
    ∀ r' : ℝ, (α.lo : ℝ) ≤ r' → r' ≤ (α.hi : ℝ) → Polynomial.aeval r' α.poly = 0 → r' = r

end PolygonPack


