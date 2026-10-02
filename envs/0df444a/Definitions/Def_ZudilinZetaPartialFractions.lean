-- Prove2me | Definitions.Def_ZudilinZetaPartialFractions
-- name    : ZudilinZetaPartialFractions
-- status  : Definition
-- author  : @tomasz
-- created : 2026-10-01T12:00:58.788049+00:00
-- url     : https://prove2.me/theorems/215cb22b-a443-44fd-b9dc-10549ecb24a4
-- title:
--   Finite partial-fraction data and rational coefficients for Zudilin’s forms
-- statement:
--   For admissible parameters $P$ and an integer $n\ge0$, put $h_j=\mathrm{hh}(P,n,j)$, $S=q-r$, and $K=\{h_{r+1},\ldots,h_0-h_{r+1}\}$. A partial-fraction datum consists of rational numbers $c_{s,k}$ with the identities
--   $$
--   R_n(t)=\sum_{s=1}^{S}\sum_{k\in K}\frac{c_{s,k}}{(t+k)^s}\quad(t>-1),\qquad
--   c_{s,h_0-k}=(-1)^{s+1}c_{s,k},\qquad
--   \sum_{k\in K}c_{1,k}=0.
--   $$
--   The reflection identity is required for $1\le s\le S$ and $k\in K$. No existence of such data is asserted by this definition.
--
--   Write
--   $$
--   w_s=\frac{s(s+1)\cdots(s+r-2)}{(r-1)!},\qquad
--   A_s=w_s\sum_{k\in K}c_{s,k},\qquad
--   A_0=-\sum_{s=1}^{S}w_s\sum_{k\in K}c_{s,k}\sum_{l=1}^{k-1}l^{-(s+r-1)}.
--   $$
--   The empty rising product is $1$. The named coefficient definitions are these finite rational expressions. The definition also names the rational normalization
--   $$
--   Q_n=\frac{D_{m_1n}^{r}\prod_{j=2}^{q-r}D_{m_jn}}{\Phi_n}.
--   $$
--   These data separate the finite partial-fraction and coefficient estimates from the analytic evaluation of the series defining $F_n$. The rational function is exactly the one in the 2001 note, including its factor $h_0+2t$.
-- source:
--   W. Zudilin, One of the numbers ζ(5), ζ(7), ζ(9), ζ(11) is irrational, Russian Math. Surveys 56 (2001), pp. 774–775, definition of R_n and Lemma 1, https://www.math.ru.nl/~zudilin/PS/zeta5-11%24.pdf; W. Zudilin, Arithmetic of linear forms involving odd zeta values, https://arxiv.org/abs/math/0206176, Lemma 19 and its proof, pp. 31–33, equations (8.10)–(8.12).

import Definitions.Def_ZudilinZetaArith

/-!
# Finite partial-fraction data for Zudilin's linear forms

The coefficients describe the mission's rational function on the open ray (-1,∞).
The reflection and residue identities record its antisymmetry and decay at infinity.
The remaining definitions are finite rational expressions; they do not assume any
zeta-value identity or denominator estimate.
-/
namespace ZudilinZeta

/-- The integer locations of the possible poles of `R P n`. -/
def poleRange (P : Params) (n : ℕ) : Finset ℕ :=
  Finset.Icc (hh P n (P.r + 1)) (hh P n 0 - hh P n (P.r + 1))

/-- The rational multiplier in the definition of `Lambda`. -/
noncomputable def denominatorScale (P : Params) (n : ℕ) : ℚ :=
  ((D (m P 1 * n) : ℚ) ^ P.r *
    ∏ j ∈ Finset.Icc 2 (P.q - P.r), (D (m P j * n) : ℚ)) / (Phi P n : ℚ)

/-- The derivative multiplier, equal to `choose (s+r-2) (r-1)` for `s>0`. -/
def derivativeWeight (r s : ℕ) : ℚ :=
  (s.ascFactorial (r - 1) : ℚ) / ((r - 1).factorial : ℚ)

/-- A finite rational partial-fraction expansion with the two cancellation identities. -/
structure PartialFractionData (P : Params) (n : ℕ) where
  coeff : ℕ → ℕ → ℚ
  expansion : ∀ t : ℝ, -1 < t →
    R P n t = ∑ s ∈ Finset.Icc 1 (P.q - P.r),
      ∑ k ∈ poleRange P n, (coeff s k : ℝ) / (t + (k : ℝ)) ^ s
  reflection : ∀ s ∈ Finset.Icc 1 (P.q - P.r), ∀ k ∈ poleRange P n,
    coeff s (hh P n 0 - k) = (-1 : ℚ) ^ (s + 1) * coeff s k
  residues : ∑ k ∈ poleRange P n, coeff 1 k = 0

/-- Coefficient of `ζ(s+r-1)` before eliminating the zero rows. -/
def PartialFractionData.zetaCoefficient {P : Params} {n : ℕ}
    (d : PartialFractionData P n) (s : ℕ) : ℚ :=
  derivativeWeight P.r s * ∑ k ∈ poleRange P n, d.coeff s k

/-- Constant term obtained by subtracting the finite initial tails of the zeta series. -/
def PartialFractionData.constantCoefficient {P : Params} {n : ℕ}
    (d : PartialFractionData P n) : ℚ :=
  -(∑ s ∈ Finset.Icc 1 (P.q - P.r), derivativeWeight P.r s *
    ∑ k ∈ poleRange P n, d.coeff s k *
      ∑ l ∈ Finset.range (k - 1), (1 : ℚ) / ((l : ℚ) + 1) ^ (s + (P.r - 1)))

end ZudilinZeta


