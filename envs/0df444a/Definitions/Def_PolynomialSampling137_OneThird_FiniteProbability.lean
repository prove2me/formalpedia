-- Prove2me | Definitions.Def_PolynomialSampling137_OneThird_FiniteProbability
-- name    : PolynomialSampling137_OneThird_FiniteProbability
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T10:25:25.696934+00:00
-- url     : https://prove2.me/theorems/b0b0ed02-59a4-47d1-a4ea-eab2bc7508e7
-- title:
--   Finite probability operations, overlap, and KL divergence
-- statement:
--   Let $P$ be a Mathlib probability mass function on a finite carrier. Its real mass at $x$ is $P(x)$, and $\mathbb E_Pg=\sum_xP(x)g(x)$. For masses $P,M$, define
--
--   $$\operatorname{Ov}(P,M)=\sum_x\min\{P(x),M(x)\}.$$
--
--   The product mass of coordinate laws $M_i$ is $\prod_iM_i(y_i)$; the marginal $R_i$ is the push-forward of $R$ under coordinate projection. Relative entropy is $\sum_{R(x)>0}R(x)\ln(R(x)/M(x))$ when $R\ll M$, and $+\infty$ otherwise. Total correlation is $D(R\Vert\bigotimes_iR_i)$.
--
--   These operations allow zero point masses and empty coordinate families. KL uses extended nonnegative reals; conversion of the finite nonnegative sum loses no value on probability laws. Raw signed mass functions are outside the probability-law interpretation of these operations. This interface supplies the overlap and entropy quantities in the selected results.
-- source:
--   Yan Zhong, STOC 2027 submission #137 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/137.pdf, §2.1, printed p. 8 / PDF p. 10; §2.3 Eqs. (9)–(10), printed p. 9 / PDF p. 11

import Mathlib
open scoped ENNReal

noncomputable section

namespace PolynomialSampling137.OneThird

/-- Real point masses of a Mathlib probability mass function; zeros are allowed. -/
def mass {α : Type*} (P : PMF α) (x : α) : ℝ := (P x).toReal

/-- Expectation on a finite carrier. -/
def expectation {α : Type*} [Fintype α] (P : PMF α) (g : α → ℝ) : ℝ :=
  ∑ x, mass P x * g x

/-- Common mass, equal to one minus statistical distance for probability laws. -/
def overlap {α : Type*} [Fintype α] (P M : α → ℝ) : ℝ :=
  ∑ x, min (P x) (M x)

/-- Independent product point masses on a finite heterogeneous product. -/
def productMass {n : ℕ} {Ω : Fin n → Type*} (M : ∀ i, PMF (Ω i))
    (y : ∀ i, Ω i) : ℝ := ∏ i, mass (M i) (y i)

/-- The actual coordinate marginal, computed by push-forward. -/
def marginal {n : ℕ} {Ω : Fin n → Type*} (R : PMF (∀ i, Ω i))
    (i : Fin n) : PMF (Ω i) := R.map (fun y => y i)

/-- Finite-law KL in nats. Non-absolutely-continuous inputs have value infinity.
On probability masses the finite sum is nonnegative, so `ofReal` loses nothing.
The zero-mass summand is explicitly zero, including when both masses vanish. -/
def relativeEntropy {α : Type*} [Fintype α] (R M : α → ℝ) : ℝ≥0∞ :=
  if ∀ y, M y = 0 → R y = 0 then
    ENNReal.ofReal (∑ y, if R y = 0 then 0 else R y * Real.log (R y / M y))
  else ⊤

/-- Total correlation uses the product of the actual marginals. -/
def totalCorrelation {n : ℕ} {Ω : Fin n → Type*} [∀ i, Fintype (Ω i)]
    (R : PMF (∀ i, Ω i)) : ℝ≥0∞ :=
  relativeEntropy (mass R) (productMass (marginal R))

end PolynomialSampling137.OneThird


