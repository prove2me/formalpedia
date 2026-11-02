-- Prove2me | Definitions.Def_Grothendieck_Series
-- name    : Grothendieck_Series
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-02T04:14:18.334801+00:00
-- url     : https://prove2.me/theorems/b1e9568c-d738-4feb-ba6f-de8fd5dfc8b9
-- title:
--   The rounding function $E_r$ and the Taylor coefficients of $E_r^{-1}$
-- statement:
--   The paper's analysis is carried by the function $E_r:[-1,1]\to[-1,1]$ defined by
--
--   $$
--   E_r(x\cdot y)=\mathbb E\Big[\frac{Zx}{\lVert Zx\rVert}\cdot\frac{Zy}{\lVert Zy\rVert}\Big],
--   $$
--
--   where $x,y$ range over unit vectors of $\ell^2(\mathbb R)$ and $Z$ is an $r\times\infty$ matrix with independent standard normal entries. By rotational invariance the expectation depends only on $x\cdot y$, which is what makes $E_r$ a function of one variable.
--
--   Lemma 2.1 of the paper identifies this function with a hypergeometric series: with the constant
--
--   $$
--   C_r=\frac2r\Big(\frac{\Gamma((r+1)/2)}{\Gamma(r/2)}\Big)^2 ,
--   $$
--
--   one has
--
--   $$
--   E_r(t)=C_r\,t\;{}_2F_1\!\Big(\begin{smallmatrix}1/2,\,1/2\\ r/2+1\end{smallmatrix};t^2\Big)
--   =\sum_{k\ge0}C_r\,\frac{(1/2)_k(1/2)_k}{(r/2+1)_k\,k!}\,t^{2k+1},
--   $$
--
--   where $(a)_k=a(a+1)\cdots(a+k-1)$ is the rising factorial. This is the series encoded here: the rising factorial, the constant $C_r$, the coefficient $a_{2k+1}$ of $t^{2k+1}$, the real series $E_r$, and the analytic extension $E_r(z)=C_rz\,{}_2F_1(1/2,1/2;r/2+1;z^2)$ to the unit disc of $\mathbb C$.
--
--   The second half of the definition is the object of Section 3: the *inverse* function $E_r^{-1}$ of $E_r$ on $[-1,1]$, and its Taylor coefficients at the origin, written
--
--   $$
--   E_r^{-1}(t)=\sum_{k\ge0}b_{2k+1}t^{2k+1}.
--   $$
--
--   The paper needs to know that this expansion is valid on the whole interval $[-\beta(r,G),\beta(r,G)]$ used by the rounding argument, so the definition also records the number
--
--   $$
--   c_r=\min\{|E_r(e^{it})|:t\in[0,2\pi]\},
--   $$
--
--   which Theorem 3.1 and Lemmas 3.2 and 3.5 show is a lower bound for the radius of convergence of the Taylor series of $E_r^{-1}$.
--
--   **Formalization Note** $E_r$ and its complex extension are `tsum` of the hypergeometric series; the inverse is `Function.invFunOn (Er r) (Set.Icc (-1) 1)`, and $b_j$ is defined as $(E_r^{-1})^{(j)}(0)/j!$ using `iteratedDeriv`, so the coefficients are those of the analytic inverse rather than a separately postulated sequence. $c_r$ is the `sInf` of $\{|E_r(e^{it})|:t\in[0,2\pi]\}$.
-- source:
--   J. Briët, F. M. de Oliveira Filho, F. Vallentin, *Grothendieck inequalities for semidefinite programs with rank constraint*, Theory of Computing 10(4), 2014, pp. 77-105, equation (2.1), p. 84; equation (3.1), p. 88; equation (3.2), p. 88; equation (3.3), p. 88. https://doi.org/10.4086/toc.2014.v010a004

import Mathlib

/-!
# The function `E_r` and the Taylor coefficients of its inverse

Briët, de Oliveira Filho, Vallentin, *Grothendieck inequalities for semidefinite
programs with rank constraint*, Theory of Computing 10(4), 2014, pp. 77--105.

Sections 2 and 3 of the paper. `E_r : [-1,1] → [-1,1]` is defined by

  `E_r(x·y) = E[ (Zx/‖Zx‖) · (Zy/‖Zy‖) ]`,  `Z ∈ R^{r×∞}` standard Gaussian,

and Lemma 2.1 computes it as the hypergeometric series (2.1)

  `E_r(t) = C_r t ₂F₁(1/2, 1/2; r/2 + 1; t²)`,  `C_r = (2/r)(Γ((r+1)/2)/Γ(r/2))²`.

This file records:

* `risingFact` — the rising factorial `(a)_k = a(a+1)···(a+k-1)`;
* `Cr` — the constant `C_r` of (3.2);
* `ErCoeff r k` — the coefficient `a_{2k+1}` of `t^{2k+1}` in the series (2.1);
* `Er` — the real series (2.1), and `ErComplex` — its analytic extension (3.2) to `ℂ`;
* `ErInv` — the inverse function `E_r⁻¹` of the paper, and `invCoeff r j` — the
  Taylor coefficient `b_j` of `E_r⁻¹` at the origin, so that the expansion (3.1)
  reads `E_r⁻¹(t) = ∑_{k} b_{2k+1} t^{2k+1}`;
* `cr` — the number `c_r = min{|E_r(e^{it})| : t ∈ [0,2π]}` of (3.3).
-/

noncomputable section

open scoped BigOperators Real

namespace Grothendieck

/-- The rising factorial `(a)_k = a(a+1)···(a+k-1)`, with `(a)_0 = 1`. -/
def risingFact (a : ℝ) (k : ℕ) : ℝ := ∏ i ∈ Finset.range k, (a + (i : ℝ))

/-- The constant `C_r = (2/r) (Γ((r+1)/2)/Γ(r/2))²` of (3.2), p. 88. -/
def Cr (r : ℕ) : ℝ :=
  2 / (r : ℝ) * (Real.Gamma (((r : ℝ) + 1) / 2) / Real.Gamma ((r : ℝ) / 2)) ^ 2

/-- `ErCoeff r k = a_{2k+1}`: the coefficient of `t^{2k+1}` in the hypergeometric
series (2.1), namely `C_r (1/2)_k (1/2)_k / ((r/2+1)_k k!)`. -/
def ErCoeff (r k : ℕ) : ℝ :=
  Cr r * (risingFact (1 / 2) k) ^ 2 / (risingFact ((r : ℝ) / 2 + 1) k * (k.factorial : ℝ))

/-- `E_r(t) = C_r t ₂F₁(1/2, 1/2; r/2+1; t²) = ∑_k a_{2k+1} t^{2k+1}`, the
hypergeometric series (2.1) of Lemma 2.1, p. 84. -/
def Er (r : ℕ) (t : ℝ) : ℝ := ∑' k : ℕ, ErCoeff r k * t ^ (2 * k + 1)

/-- The analytic extension `E_r(z) = C_r z ₂F₁(1/2, 1/2; r/2+1; z²)` of `E_r` to the
unit disc, equation (3.2), p. 88. -/
def ErComplex (r : ℕ) (z : ℂ) : ℂ := ∑' k : ℕ, (ErCoeff r k : ℂ) * z ^ (2 * k + 1)

/-- The inverse function `E_r⁻¹` of `E_r` on `[-1,1]`. -/
def ErInv (r : ℕ) : ℝ → ℝ := Function.invFunOn (Er r) (Set.Icc (-1) 1)

/-- `invCoeff r j = b_j`: the `j`-th Taylor coefficient at the origin of `E_r⁻¹`, i.e.
`b_j = (E_r⁻¹)^{(j)}(0)/j!`, so that the expansion (3.1) reads
`E_r⁻¹(t) = ∑_k b_{2k+1} t^{2k+1}`. -/
def invCoeff (r j : ℕ) : ℝ := iteratedDeriv j (ErInv r) 0 / (j.factorial : ℝ)

/-- The number `c_r = min{|E_r(e^{it})| : t ∈ [0,2π]}` of equation (3.3), p. 88. -/
def cr (r : ℕ) : ℝ :=
  sInf {y : ℝ | ∃ t ∈ Set.Icc (0 : ℝ) (2 * Real.pi), y = ‖ErComplex r (Complex.exp (Complex.I * t))‖}

end Grothendieck


