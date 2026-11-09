-- Prove2me | Definitions.Def_CKKSPrecision_FourierUnits_fourier_construction
-- name    : CKKSPrecision_FourierUnits_fourier_construction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T08:40:30.211855+00:00
-- url     : https://prove2.me/theorems/453d40ec-ccc8-48cf-89be-d7c2de49faf8
-- title:
--   The Fourier quotient, rounding and explicit conjugate product
-- statement:
--   Let $r\ge2$ be a power of two, $m=4r$, and $\zeta=\exp(2\pi i/(4r))$. Order the selected embeddings by $\sigma_j(\zeta)=\zeta^{5^j}$ for $0\le j<r$. Let $\tau(\zeta)=\zeta^5$ and define
--   $$
--   u_0=\zeta^{-2}c_5=\zeta^{-2}+\zeta^{-1}+1+\zeta+\zeta^2,
--   \qquad \ell_j=\log_2|\sigma_j(u_0)|.
--   $$
--   For a vector $z\in\mathbb C^r$, the forward and inverse transforms are
--   $$
--   \widehat z_k=\sum_{j=0}^{r-1}z_j e^{-2\pi i jk/r},
--   \qquad z_j=\frac1r\sum_{k=0}^{r-1}\widehat z_k e^{2\pi i jk/r}.
--   $$
--   For a real target $t$, compute $\widehat a_0=0$ and $\widehat a_k=\widehat t_k/\widehat\ell_k$ for $k\ne0$, then take the inverse transform. Let $a_j$ be its real part and $n_j=\lfloor a_j+\tfrac12\rfloor$. Finally define
--   $$
--   u(n)=\prod_{k=0}^{r-1}\tau^{-k}(u_0)^{n_k},
--   \qquad C_r=\tfrac12\sum_{j=0}^{r-1}|\ell_j|.
--   $$
--   The output is this product computed from $t$. The definitions also name the $r-1$ vectors $\operatorname{Log}(c_{5^h})$, $1\le h<r$, and the $r$ conjugate logarithms $\operatorname{Log}(\tau^k(u_0))$.
--
--   These functions specify the construction whose correctness is the goal. Reality of the inverse transform, nonzero nonconstant Fourier modes and integral-unit membership are conclusions of the theorem items, with none assumed by these definitions.
--
--   **Formalization Note** Coordinates use `Fin r`, and the basis family uses `Fin (r-1)` shifted by one. Half-integer rounding ties go toward $+\infty$. Outside the authorized power-of-two domain, an automorphism at a noncoprime exponent defaults to the identity; theorems never use that branch. Zero frequency is handled explicitly before division.
-- source:
--   Zhaoyang Liang, Runkun Liu, Jingwei Fang, Dan Ding, A New Approach to Reducing Modulus Requirements in Homomorphic Computation: Precision Allocation in CKKS, STOC 2027 submission #148 (October 2026), p. 5, Corollary 2.1; pp. 7–8, Section 4.2 and Eq. (8) (PDF pp. 7, 9–10)

import Definitions.Def_CKKSPrecision_FourierUnits_arithmetic_model

set_option autoImplicit false

noncomputable section

namespace CKKSPrecision.FourierUnits

/-- CKKS conductor m=4r; r is positive in the definitions and at least two in the results. -/
def conductor (r : ℕ+) : ℕ+ := ⟨4 * (r : ℕ), Nat.mul_pos (by decide) r.pos⟩

/-- The cyclic order of one embedding from each conjugate pair, j=0,...,r-1. -/
def slots (r : ℕ+) (j : Fin (r : ℕ)) : K (conductor r) →ₐ[ℚ] ℂ :=
  embedding (conductor r) (5 ^ j.val)

/-- τ(ζ)=ζ^5 on the authorized power-of-two conductors. -/
def tau (r : ℕ+) : K (conductor r) ≃ₐ[ℚ] K (conductor r) :=
  powerAut (conductor r) 5

/-- u₀=ζ⁻²c₅=ζ⁻²+ζ⁻¹+1+ζ+ζ². -/
def initialUnit (r : ℕ+) : K (conductor r) :=
  zeta (conductor r) ^ (-2 : ℤ) * c (conductor r) 5

/-- The full logarithmic vector in the cyclic embedding order. -/
def slotLog (r : ℕ+) (z : K (conductor r)) : Fin (r : ℕ) → ℝ := Log (slots r) z

def ell (r : ℕ+) : Fin (r : ℕ) → ℝ := slotLog r (initialUnit r)

/-- Forward transform, negative exponent and no normalization. -/
def fourier (r : ℕ+) (z : Fin (r : ℕ) → ℂ) (k : Fin (r : ℕ)) : ℂ :=
  ∑ j, z j * Complex.exp
    (((-2 * Real.pi * (j.val : ℝ) * (k.val : ℝ) / (r : ℕ) : ℝ) : ℂ) * Complex.I)

/-- Inverse transform, positive exponent and normalization 1/r. -/
def inverseFourier (r : ℕ+) (z : Fin (r : ℕ) → ℂ) (j : Fin (r : ℕ)) : ℂ :=
  ((r : ℕ) : ℂ)⁻¹ * ∑ k, z k * Complex.exp
    (((2 * Real.pi * (j.val : ℝ) * (k.val : ℝ) / (r : ℕ) : ℝ) : ℂ) * Complex.I)

/-- Frequency zero is explicitly zero, not a default result of division by zero. -/
def quotientSpectrum (r : ℕ+) (t : Fin (r : ℕ) → ℝ) (k : Fin (r : ℕ)) : ℂ :=
  if k.val = 0 then 0 else
    fourier r (fun j => (t j : ℂ)) k / fourier r (fun j => (ell r j : ℂ)) k

/-- Compute the complex inverse transform before taking its real part. -/
def inverseCoefficients (r : ℕ+) (t : Fin (r : ℕ) → ℝ) : Fin (r : ℕ) → ℂ :=
  inverseFourier r (quotientSpectrum r t)

def realCoefficients (r : ℕ+) (t : Fin (r : ℕ) → ℝ) (j : Fin (r : ℕ)) : ℝ :=
  (inverseCoefficients r t j).re

/-- Nearest integer with half-integer ties toward +∞, fixed for all targets. -/
def roundedCoefficients (r : ℕ+) (t : Fin (r : ℕ) → ℝ) (j : Fin (r : ℕ)) : ℤ :=
  ⌊realCoefficients r t j + 1 / 2⌋

/-- Equation (8), including inverse automorphisms and negative integral exponents. -/
def conjugateProduct (r : ℕ+) (n : Fin (r : ℕ) → ℤ) : K (conductor r) :=
  ∏ k, (((tau r) ^ (-(k.val : ℤ))) (initialUnit r)) ^ n k

/-- The actual output computed from the arbitrary real target. -/
def constructed (r : ℕ+) (t : Fin (r : ℕ) → ℝ) : K (conductor r) :=
  conjugateProduct r (roundedCoefficients r t)

/-- The exact constant in Theorem 4.1, independent of t. -/
def roundingConstant (r : ℕ+) : ℝ := (1 / 2) * ∑ j, |ell r j|

/-- The r-1 logarithms in Corollary 2.1; h=1,...,r-1. -/
def basisVectors (r : ℕ+) (h : Fin ((r : ℕ) - 1)) : Fin (r : ℕ) → ℝ :=
  slotLog r (c (conductor r) (5 ^ (h.val + 1)))

/-- The r logarithms in Lemma 4.1; positive powers of τ here. -/
def conjugateLogs (r : ℕ+) (k : Fin (r : ℕ)) : Fin (r : ℕ) → ℝ :=
  slotLog r (((tau r) ^ k.val) (initialUnit r))

end CKKSPrecision.FourierUnits


