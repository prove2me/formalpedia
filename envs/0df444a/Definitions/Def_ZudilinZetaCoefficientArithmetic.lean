-- Prove2me | Definitions.Def_ZudilinZetaCoefficientArithmetic
-- name    : ZudilinZetaCoefficientArithmetic
-- status  : Definition
-- author  : @tomasz
-- created : 2026-10-01T13:45:33.629742+00:00
-- url     : https://prove2.me/theorems/b157b417-9ecc-4862-808a-6874a3c79f85
-- title:
--   Pole support, harmonic shifts, and coefficient denominator factors
-- statement:
--   Let $P$ be admissible, $h_j=\mathrm{hh}(P,n,j)$ and $S=q-r$. For $1\le s\le S$, define the order-dependent pole interval and two complementary arithmetic multipliers by
--   $$
--   K_s=\{h_{r+s},\ldots,h_0-h_{r+s}\},\qquad
--   L_s=D_{m_1n}^{r}\prod_{j=2}^{s}D_{m_jn},\qquad
--   T_s=\frac{\prod_{j=s+1}^{S}D_{m_jn}}{\Phi_n}.
--   $$
--   The first factor is a natural number and the second is rational. For a partial-fraction datum $d=(c_{s,k})$, define the shifted finite constant
--   $$
--   A'_0=-\sum_{s=1}^{S}w_s\sum_{k\in K}c_{s,k}
--     \sum_{l=1}^{k-h_1}\frac{1}{l^{s+r-1}},\qquad
--   w_s=\frac{s(s+1)\cdots(s+r-2)}{(r-1)!}.
--   $$
--   Here $K$ is the full pole interval from the partial-fraction definition; the inner sum is empty when its natural-number upper bound is zero. These definitions do not assert the coefficient support, the equality with the unshifted constant, or integrality. Those are separate theorems.
-- source:
--   W. Zudilin, One of the numbers ζ(5), ζ(7), ζ(9), ζ(11) is irrational, Russian Math. Surveys 56 (2001), pp. 774–775, R_n and Lemma 1, https://www.math.ru.nl/~zudilin/PS/zeta5-11%24.pdf; Arithmetic of linear forms involving odd zeta values, https://arxiv.org/abs/math/0206176, Lemmas 15–19, pp. 27–33, especially (8.10)–(8.12).

import Definitions.Def_ZudilinZetaPartialFractions

namespace ZudilinZeta

/-- Possible poles for a coefficient of order `s`. -/
def orderPoleRange (P : Params) (n s : ℕ) : Finset ℕ :=
  Finset.Icc (hh P n (P.r+s)) (hh P n 0 - hh P n (P.r+s))

/-- The part of the lcm multiplier reserved for a harmonic denominator of order `s+r-1`. -/
def prefixClearing (P : Params) (n s : ℕ) : ℕ :=
  D (m P 1*n)^P.r * ∏ j ∈ Finset.Icc 2 s, D (m P j*n)

/-- The complementary lcm multiplier, including the prime-product improvement. -/
noncomputable def tailDenominatorScale (P : Params) (n s : ℕ) : ℚ :=
  (∏ j ∈ Finset.Icc (s+1) (P.q-P.r), (D (m P j*n) : ℚ)) / (Phi P n : ℚ)

/-- The finite harmonic constant after extending the original series down to `1-h₁`. -/
def PartialFractionData.shiftedConstantCoefficient {P : Params} {n : ℕ}
    (d : PartialFractionData P n) : ℚ :=
  -(∑ s ∈ Finset.Icc 1 (P.q-P.r), derivativeWeight P.r s *
    ∑ k ∈ poleRange P n, d.coeff s k *
      ∑ l ∈ Finset.range (k-hh P n 1), (1 : ℚ) / ((l : ℚ)+1)^(s+(P.r-1)))

end ZudilinZeta


