-- Prove2me | Definitions.Def_IsingVectorBalancing_Subgaussian_Law
-- name    : IsingVectorBalancing_Subgaussian_Law
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T01:33:17.244969+00:00
-- url     : https://prove2.me/theorems/64533f61-9b00-42a7-8cc9-ce0cf423c305
-- title:
--   Product Ising weights, finite expectations and log partition function
-- statement:
--   Let $v_i\in\mathbb R^d$ and $\Omega=\{-1,+1\}^n$. For a real external field $h=(h_i)$ define
--   $$w_v(\sigma)=\prod_{i<j}(1-\sigma_i\sigma_j\langle v_i,v_j\rangle),\quad
--   w_{v,h}(\sigma)=e^{\sum_i h_i\sigma_i}w_v(\sigma),\quad
--   Z_v(h)=\sum_\sigma w_{v,h}(\sigma),\quad
--   \mu_{v,h}(\sigma)=\frac{w_{v,h}(\sigma)}{Z_v(h)}.$$
--   Finite expectation is $\mathbb E_h f=\sum_\sigma\mu_{v,h}(\sigma)f(\sigma)$. The signed sum is $s_v(\sigma)=\sum_i\sigma_i v_i$, its mean is $m_v(h)=\sum_\sigma\mu_{v,h}(\sigma)s_v(\sigma)$, and variance is $\operatorname{Var}_h(f)=\mathbb E_h[(f-\mathbb E_h f)^2]$. The spin covariance has entries
--   $$\operatorname{Cov}_h(\sigma)_{ij}=\mathbb E_h[\sigma_i\sigma_j]-\mathbb E_h[\sigma_i]\mathbb E_h[\sigma_j],\qquad F_v(h)=\log Z_v(h).$$
--   These definitions fix the actual law used in every concentration statement. No covariance or moment bound is included in the definitions.
--
--   **Formalization Note** Configurations are Boolean functions with `true` mapped to $+1$ and `false` to $-1$. These are total real formulas, including away from admissible inputs: if $Z=0$, real division returns zero; the logarithm also has Lean's total extension. The separate well-definedness theorem establishes positive $Z$ and a probability law on all admissible inputs.
-- source:
--   Heng Guo, Daniel Spielman, Xinyuan Zhang, STOC 2027 submission #1240 (October 2026), Subgaussian Vector Balancing by an Ising Model, pp. 1, 6, 8 (PDF 2, 7, 9), Eq. (1), Eqs. (5)–(6), §6.1 before Claim 8; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1240.pdf

import Definitions.Def_IsingVectorBalancing_Subgaussian_Geometry

open scoped BigOperators
set_option autoImplicit false

namespace IsingVectorBalancing.Subgaussian

abbrev Configuration (n : ℕ) := Fin n → Bool

def spin (b : Bool) : ℝ := if b then 1 else -1

/-- Equation (1): one factor for each unordered pair of distinct indices. -/
noncomputable def weight {n d : ℕ} (v : Fin n → Vec d) (σ : Configuration n) : ℝ :=
  ∏ i : Fin n, ∏ j ∈ Finset.univ.filter (fun j : Fin n => i < j),
    (1 - spin (σ i) * spin (σ j) * inner ℝ (v i) (v j))

/-- Equation (5), with no restriction on the real external field. -/
noncomputable def tiltedWeight {n d : ℕ} (v : Fin n → Vec d)
    (h : Fin n → ℝ) (σ : Configuration n) : ℝ :=
  Real.exp (∑ i, h i * spin (σ i)) * weight v σ

noncomputable def partition {n d : ℕ} (v : Fin n → Vec d) (h : Fin n → ℝ) : ℝ :=
  ∑ σ : Configuration n, tiltedWeight v h σ

/-- Equation (6). Well-definedness on Admissible inputs is a theorem, not data. -/
noncomputable def probability {n d : ℕ} (v : Fin n → Vec d)
    (h : Fin n → ℝ) (σ : Configuration n) : ℝ :=
  tiltedWeight v h σ / partition v h

noncomputable def expectation {n d : ℕ} (v : Fin n → Vec d)
    (h : Fin n → ℝ) (f : Configuration n → ℝ) : ℝ :=
  ∑ σ : Configuration n, probability v h σ * f σ

noncomputable def signedSum {n d : ℕ} (v : Fin n → Vec d)
    (σ : Configuration n) : Vec d :=
  ∑ i, spin (σ i) • v i

noncomputable def meanSum {n d : ℕ} (v : Fin n → Vec d) (h : Fin n → ℝ) : Vec d :=
  ∑ σ : Configuration n, probability v h σ • signedSum v σ

noncomputable def variance {n d : ℕ} (v : Fin n → Vec d)
    (h : Fin n → ℝ) (f : Configuration n → ℝ) : ℝ :=
  expectation v h (fun σ => (f σ - expectation v h f) ^ 2)

noncomputable def spinCovariance {n d : ℕ} (v : Fin n → Vec d)
    (h : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => expectation v h (fun σ => spin (σ i) * spin (σ j)) -
    expectation v h (fun σ => spin (σ i)) * expectation v h (fun σ => spin (σ j))

noncomputable def logPartition {n d : ℕ} (v : Fin n → Vec d) (h : Fin n → ℝ) : ℝ :=
  Real.log (partition v h)

end IsingVectorBalancing.Subgaussian


