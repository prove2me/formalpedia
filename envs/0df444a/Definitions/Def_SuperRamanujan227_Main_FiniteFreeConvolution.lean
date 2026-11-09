-- Prove2me | Definitions.Def_SuperRamanujan227_Main_FiniteFreeConvolution
-- name    : SuperRamanujan227_Main_FiniteFreeConvolution
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T09:29:05.128613+00:00
-- url     : https://prove2.me/theorems/bdd09eae-2ff6-416e-88d6-6c49d4e73147
-- title:
--   Finite free additive and multiplicative convolutions $p\boxplus_D q$, $p\boxtimes_D q$
-- statement:
--   Fix a degree $D$ and write real polynomials of degree at most $D$ as
--   $$p(x)=\sum_{i=0}^{D}(-1)^i a_i x^{D-i},\qquad q(x)=\sum_{i=0}^{D}(-1)^i b_i x^{D-i}.$$
--   The **finite free additive convolution** is
--   $$(p\boxplus_D q)(x)=\sum_{k=0}^{D}(-1)^k x^{D-k}\sum_{i+j=k}\frac{(D-i)!\,(D-j)!}{D!\,(D-k)!}\,a_i b_j,$$
--   and the **finite free multiplicative convolution** is
--   $$(p\boxtimes_D q)(x)=\sum_{i=0}^{D}(-1)^i x^{D-i}\,\frac{a_i b_i}{\binom{D}{i}}.$$
--
--   For characteristic polynomials $p=\chi_x(A)$, $q=\chi_x(B)$ of $D\times D$ real symmetric matrices these coincide with the Haar averages $\mathbb E_Q\chi_x(A+QBQ^{\mathsf T})$ and $\mathbb E_Q\chi_x(AQBQ^{\mathsf T})$ of Definition 2.4 (Marcus–Spielman–Srivastava). They are the convolutions appearing in Lemma 2.5 and Lemma 5.4.
--
--   **Formalization Note** The convolutions are defined by these coefficient formulas, bilinear in $(p,q)$, rather than by Haar integrals; only coefficients of degree at most $D$ are read.
-- source:
--   Gil Cohen, Gal Maor, Quantitative Results on Super-Ramanujan Graphs, STOC 2027 submission #227 (October 2026), SHA-256 1ba5eacb267c8a63eff5e5b9d6b96d9f2b04d5a1e147d887b9e61574127831f8, Definition 2.4, p. 8, with the explicit coefficient formulas of [MSS22] referred to on p. 8

import Mathlib

open Polynomial

namespace SuperRamanujan227.Main

/-- The coefficient `a_i` of `p` in degree `D`, written `p(x) = ∑_{i=0}^{D} (-1)^i a_i x^{D-i}`. -/
noncomputable def ffCoeff (D : ℕ) (p : ℝ[X]) (i : ℕ) : ℝ :=
  (-1) ^ i * p.coeff (D - i)

/-- Finite free additive convolution `p ⊞_D q` in degree `D` (Definition 2.4, p. 8), by the
coefficient formula of Marcus–Spielman–Srivastava [MSS22]: the coefficient of `x^{D-k}` is
`(-1)^k ∑_{i+j=k} (D-i)!(D-j)!/(D!(D-k)!) a_i b_j`. -/
noncomputable def ffAdd (D : ℕ) (p q : ℝ[X]) : ℝ[X] :=
  ∑ k ∈ Finset.range (D + 1),
    C ((-1) ^ k * ∑ i ∈ Finset.range (k + 1),
        ((D - i).factorial : ℝ) * ((D - (k - i)).factorial : ℝ) /
          ((D.factorial : ℝ) * ((D - k).factorial : ℝ)) * ffCoeff D p i * ffCoeff D q (k - i)) *
      X ^ (D - k)

/-- Finite free multiplicative convolution `p ⊠_D q` in degree `D` (Definition 2.4, p. 8), by
the coefficient formula of [MSS22]: the coefficient of `x^{D-i}` is `(-1)^i a_i b_i / binom(D, i)`. -/
noncomputable def ffMul (D : ℕ) (p q : ℝ[X]) : ℝ[X] :=
  ∑ i ∈ Finset.range (D + 1),
    C ((-1) ^ i * ffCoeff D p i * ffCoeff D q i / (D.choose i : ℝ)) * X ^ (D - i)

end SuperRamanujan227.Main


