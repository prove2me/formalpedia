-- Prove2me | Definitions.Def_TateCurve_Tails
-- name    : TateCurve_Tails
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:29.330635+00:00
-- url     : https://prove2.me/theorems/d2f55381-ba94-5ea4-be36-04ce07a82a35
-- title:
--   Divisor-sum coefficients of the Tate parametrisation, with growth bounds
-- statement:
--   Throughout, $K$ is a nontrivially normed field whose norm is ultrametric. For $u \in K$ and $d \in \mathbb{N}$ the module defines the two divisor terms occurring in the $q$-expansion of the Tate parametrisation,
--   $$\mathtt{xDivTerm}\,u\,d = d\,(u^{d} + (u^{-1})^{d} - 2), \qquad \mathtt{yDivTerm}\,u\,d = \binom{d}{2}\bigl(u^{d} - (u^{-1})^{d}\bigr) - d\,(u^{-1})^{d} + d,$$
--   where $d$ and $\binom{d}{2}$ are read in $K$ via the natural-number cast, and then the coefficients themselves as sums over the divisors of $N$: `xCoeff u N` $= \sum_{d \mid N} \mathtt{xDivTerm}\,u\,d$ and `yCoeff u N` $= \sum_{d \mid N} \mathtt{yDivTerm}\,u\,d$. Since `Nat.divisors 0` is empty, both coefficients vanish at $N = 0$. The growth parameter is $\mathtt{growthBound}\,u = \max(\max(\lVert u\rVert, \lVert u^{-1}\rVert), 1)$, an explicit real number, not a normalised valuation.
--
--   The accompanying lemmas record the elementary estimates attached to these definitions: $\mathtt{growthBound}\,u \ge 1$ and hence $\ge 0$, and $\mathtt{growthBound}\,u^{d} \ge 1$ for all $d$; $\lVert u^{d}\rVert \le \mathtt{growthBound}\,u^{d}$ and $\lVert (u^{-1})^{d}\rVert \le \mathtt{growthBound}\,u^{d}$; and, using that in an ultrametric field every natural-number cast has norm at most $1$, $\lVert (k : K)\rVert \le \mathtt{growthBound}\,u^{d}$ for all $k, d$. Two private helpers restate the ultrametric inequality for sums and differences in the form $\lVert a \pm b\rVert \le \max(\lVert a\rVert, \lVert b\rVert)$. The two main estimates are termwise: $\lVert \mathtt{xDivTerm}\,u\,d\rVert \le \mathtt{growthBound}\,u^{d}$ and $\lVert \mathtt{yDivTerm}\,u\,d\rVert \le \mathtt{growthBound}\,u^{d}$, proved by combining the above with the ultrametric inequality. The corresponding bound on the divisor sums `xCoeff`, `yCoeff` is not asserted in this module.
--
--   **Relation to Mathlib.** Mathlib supplies the ambient framework used here — normed fields, `IsUltrametricDist` together with `IsUltrametricDist.norm_natCast_le_one`, and `Nat.divisors` — while the coefficient functions of the Tate parametrisation and the growth parameter `growthBound` are the project's own definitions.
--
--   **Where it is used.** These are the coefficients of the power series in $q$ expressing the Weierstrass coordinates $X(u,q)$ and $Y(u,q)$ of the Tate parametrisation on the fundamental annulus, and the growth bounds are what makes their Cauchy products converge; they feed the analysis of the Weierstrass defect for the Tate curve, used in the local study of elliptic curves with multiplicative reduction.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_TateCurve_Tails.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped NNReal
open IsUltrametricDist

namespace TateCurve

section Coefficients

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]

private theorem norm_add_le_max' (a b : K) : ‖a + b‖ ≤ max ‖a‖ ‖b‖ := by
  exact_mod_cast nnnorm_add_le_max a b

private theorem norm_sub_le_max' (a b : K) : ‖a - b‖ ≤ max ‖a‖ ‖b‖ := by
  rw [sub_eq_add_neg]
  simpa [norm_neg] using norm_add_le_max' a (-b)

noncomputable def xDivTerm (u : K) (d : ℕ) : K := (d : K) * (u ^ d + u⁻¹ ^ d - 2)

noncomputable def yDivTerm (u : K) (d : ℕ) : K :=
  ((d.choose 2 : ℕ) : K) * (u ^ d - u⁻¹ ^ d) - (d : K) * u⁻¹ ^ d + (d : K)

noncomputable def xCoeff (u : K) (N : ℕ) : K := ∑ d ∈ N.divisors, xDivTerm u d

noncomputable def yCoeff (u : K) (N : ℕ) : K := ∑ d ∈ N.divisors, yDivTerm u d

noncomputable def growthBound (u : K) : ℝ := max (max ‖u‖ ‖u⁻¹‖) 1

theorem one_le_growthBound (u : K) : 1 ≤ growthBound u := le_max_right _ _

theorem growthBound_nonneg (u : K) : 0 ≤ growthBound u :=
  zero_le_one.trans (one_le_growthBound u)

theorem norm_pow_le_growthBound (u : K) (d : ℕ) : ‖u ^ d‖ ≤ growthBound u ^ d := by
  rw [norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg u) ((le_max_left _ _).trans (le_max_left _ _)) d

theorem norm_inv_pow_le_growthBound (u : K) (d : ℕ) : ‖u⁻¹ ^ d‖ ≤ growthBound u ^ d := by
  rw [norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) ((le_max_right _ _).trans (le_max_left _ _)) d

theorem one_le_growthBound_pow (u : K) (d : ℕ) : (1 : ℝ) ≤ growthBound u ^ d :=
  one_le_pow₀ (one_le_growthBound u)

theorem norm_natCast_le_growthBound_pow (u : K) (k d : ℕ) :
    ‖(k : K)‖ ≤ growthBound u ^ d :=
  (IsUltrametricDist.norm_natCast_le_one K k).trans (one_le_growthBound_pow u d)

theorem norm_xDivTerm_le (u : K) (d : ℕ) : ‖xDivTerm u d‖ ≤ growthBound u ^ d := by
  rw [xDivTerm]
  calc ‖(d : K) * (u ^ d + u⁻¹ ^ d - 2)‖
      = ‖(d : K)‖ * ‖u ^ d + u⁻¹ ^ d - 2‖ := norm_mul _ _
    _ ≤ 1 * ‖u ^ d + u⁻¹ ^ d - 2‖ :=
        mul_le_mul_of_nonneg_right (IsUltrametricDist.norm_natCast_le_one K d)
          (norm_nonneg _)
    _ = ‖u ^ d + (u⁻¹ ^ d - 2)‖ := by rw [one_mul, add_sub_assoc]
    _ ≤ max ‖u ^ d‖ ‖u⁻¹ ^ d - 2‖ := norm_add_le_max' _ _
    _ ≤ growthBound u ^ d := by
        refine max_le (norm_pow_le_growthBound u d) ?_
        refine (norm_sub_le_max' _ _).trans
          (max_le (norm_inv_pow_le_growthBound u d) ?_)
        calc ‖(2 : K)‖ = ‖((2 : ℕ) : K)‖ := by norm_num
          _ ≤ growthBound u ^ d := norm_natCast_le_growthBound_pow u 2 d

theorem norm_yDivTerm_le (u : K) (d : ℕ) : ‖yDivTerm u d‖ ≤ growthBound u ^ d := by
  rw [yDivTerm]
  refine (norm_add_le_max' _ _).trans (max_le ?_ ?_)
  · refine (norm_sub_le_max' _ _).trans (max_le ?_ ?_)
    · calc ‖((d.choose 2 : ℕ) : K) * (u ^ d - u⁻¹ ^ d)‖
          = ‖((d.choose 2 : ℕ) : K)‖ * ‖u ^ d - u⁻¹ ^ d‖ := norm_mul _ _
        _ ≤ 1 * ‖u ^ d - u⁻¹ ^ d‖ :=
            mul_le_mul_of_nonneg_right (IsUltrametricDist.norm_natCast_le_one K _)
              (norm_nonneg _)
        _ = ‖u ^ d - u⁻¹ ^ d‖ := one_mul _
        _ ≤ max ‖u ^ d‖ ‖u⁻¹ ^ d‖ := norm_sub_le_max' _ _
        _ ≤ growthBound u ^ d := max_le (norm_pow_le_growthBound u d)
            (norm_inv_pow_le_growthBound u d)
    · calc ‖(d : K) * u⁻¹ ^ d‖ = ‖(d : K)‖ * ‖u⁻¹ ^ d‖ := norm_mul _ _
        _ ≤ 1 * (growthBound u ^ d) :=
            mul_le_mul (IsUltrametricDist.norm_natCast_le_one K d)
              (norm_inv_pow_le_growthBound u d) (norm_nonneg _) zero_le_one
        _ = growthBound u ^ d := one_mul _
  · exact norm_natCast_le_growthBound_pow u d d

end Coefficients

end TateCurve


