-- Prove2me | Definitions.Def_HGASUndecidable_Main_Fourier
-- name    : HGASUndecidable_Main_Fourier
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T20:15:20.394026+00:00
-- url     : https://prove2.me/theorems/7fc6c1df-c82e-4ccb-88f0-7cc4d9316b6e
-- title:
--   Diophantine data, normalized theta series, Fourier coefficients, and trajectory conditions
-- statement:
--   DiophantineData records q,r,A,B,c₀,c₁ and rhs=c₀+ec₁; validity requires positive q,r, nonzero columns of B and the halting equivalence for integer solutions of A n^{◦2}+Bn=rhs. The scalar constants are exactly λ=1/256 and η=1/2. Θλ and Pη are their bilateral series. Q_j, χ_l,V_j,S_j and D_e are the characters and product of (7.6)–(7.7). Fourier coefficients use the normalized Lebesgue integral on [0,2π]^{q+r}, and absolute convergence includes both summability of coefficient norms and pointwise reconstruction. The four period-one Jacobi theta functions, theta constants, E₂ with divisor sums, τλ=i log(256)/π, and the ordered primes are explicit. Forward recurrence means x(t_k)→x(0) for t_k→∞; moderate growth bounds the time average of ‖x‖^μ for some real μ≥1; a zero average means existence of the limit with value zero.
-- source:
--   Shevchenko, Liu, Liu (2026), arXiv:2610.12434 (SHA-256 72e185f4750fe9bb72a2f146b2802fa13a97dcdd4f66e0e762b703dc7ddd77a8), §§7–8.3.1, printed pp. 36–51 (PDF 38–53)

import Definitions.Def_HGASUndecidable_Main_Codes

noncomputable section
open MeasureTheory Filter Topology
open scoped BigOperators ComplexConjugate

namespace HGASUndecidable.Main

structure DiophantineData where
  q : ℕ
  r : ℕ
  A : Matrix (Fin r) (Fin q) ℤ
  B : Matrix (Fin r) (Fin q) ℤ
  c₀ : Fin r → ℤ
  c₁ : Fin r → ℤ

def rhs (a : DiophantineData) (e : ℕ) (l : Fin a.r) : ℤ := a.c₀ l + (e : ℤ) * a.c₁ l

def DiophantineSolution (a : DiophantineData) (e : ℕ) (v : Fin a.q → ℤ) : Prop :=
  ∀ l, (∑ j, (a.A l j * (v j)^2 + a.B l j * v j)) = rhs a e l

def DiophantineValid (a : DiophantineData) : Prop :=
  1 ≤ a.q ∧ 1 ≤ a.r ∧ (∀ j, ∃ l, a.B l j ≠ 0) ∧
  ∀ e, haltingSet e ↔ ∃ v, DiophantineSolution a e v

def lambda : ℝ := 1 / 256
def eta : ℝ := 1 / 2

def thetaSeries (Q V : ℂ) : ℂ :=
  ∑' n : ℤ, (lambda : ℂ) ^ (n.natAbs ^ 2) * Q ^ (n.natAbs ^ 2) * V ^ n

def poissonSeries (W : ℂ) : ℂ := ∑' s : ℤ, (eta : ℂ) ^ s.natAbs * W ^ s

def phaseQ (a : DiophantineData) (φ : Fin (a.q + a.r) → ℝ) (j : Fin a.q) : ℂ :=
  Complex.exp (4 * Complex.I * φ (Fin.castAdd a.r j))
def phaseChi (a : DiophantineData) (φ : Fin (a.q + a.r) → ℝ) (l : Fin a.r) : ℂ :=
  Complex.exp (4 * Complex.I * φ (Fin.natAdd a.q l))
def phaseV (a : DiophantineData) (φ : Fin (a.q + a.r) → ℝ) (j : Fin a.q) : ℂ :=
  ∏ l, phaseChi a φ l ^ a.B l j
def phaseS (a : DiophantineData) (φ : Fin (a.q + a.r) → ℝ) (j : Fin a.q) : ℂ :=
  ∏ l, phaseChi a φ l ^ a.A l j

def torusFunction (a : DiophantineData) (e : ℕ) (φ : Fin (a.q + a.r) → ℝ) : ℂ :=
  (∏ l, phaseChi a φ l ^ (-rhs a e l)) *
  ∏ j, thetaSeries (phaseQ a φ j) (phaseV a φ j) *
    poissonSeries ((phaseQ a φ j)⁻¹ * phaseS a φ j)

def character {d : ℕ} (k : Fin d → ℤ) (φ : Fin d → ℝ) : ℂ :=
  Complex.exp (Complex.I * ∑ i, (k i : ℂ) * (φ i : ℂ))

def fourierCoeff {d : ℕ} (f : (Fin d → ℝ) → ℂ) (k : Fin d → ℤ) : ℂ :=
  ((2 * Real.pi : ℂ) ^ d)⁻¹ *
    ∫ φ in Set.pi Set.univ (fun _ => Set.Icc (0 : ℝ) (2 * Real.pi)),
      f φ * conj (character k φ)

def AbsolutelyConvergentFourier {d : ℕ} (f : (Fin d → ℝ) → ℂ) : Prop :=
  Summable (fun k : Fin d → ℤ => ‖fourierCoeff f k‖) ∧
  ∀ φ, f φ = ∑' k : Fin d → ℤ, fourierCoeff f k * character k φ

def theta (k : ℕ) (z τ : ℂ) : ℂ :=
  if k = 1 then -Complex.I * ∑' n : ℤ, (-1 : ℂ)^n *
    Complex.exp (Real.pi * Complex.I * (((n : ℂ) + 1/2)^2 * τ + (2*n+1)*z))
  else if k = 2 then ∑' n : ℤ,
    Complex.exp (Real.pi * Complex.I * (((n : ℂ) + 1/2)^2 * τ + (2*n+1)*z))
  else if k = 3 then ∑' n : ℤ,
    Complex.exp (Real.pi * Complex.I * ((n : ℂ)^2 * τ + 2*n*z))
  else ∑' n : ℤ, (-1 : ℂ)^n *
    Complex.exp (Real.pi * Complex.I * ((n : ℂ)^2 * τ + 2*n*z))

def thetaConstant (k : ℕ) (τ : ℂ) : ℂ := theta k 0 τ

def eisensteinTwo (τ : ℂ) : ℂ := 1 - 24 * ∑' n : ℕ,
  ((∑ d ∈ (n+1).divisors, d : ℕ) : ℂ) * Complex.exp (2*Real.pi*Complex.I*(n+1)*τ)

def tauLambda : ℂ := Complex.I * Real.log 256 / Real.pi

def primeAt (l : ℕ) : ℕ := Nat.nth Nat.Prime l

def forwardRecurrent {n : ℕ} (x : ℝ → State n) : Prop :=
  ∃ t : ℕ → ℝ, Tendsto t atTop atTop ∧ Tendsto (fun k => x (t k)) atTop (𝓝 (x 0))

def moderateGrowth {n : ℕ} (x : ℝ → State n) : Prop :=
  ∃ μ : ℝ, 1 ≤ μ ∧ ∃ C : ℝ, ∀ T : ℝ, 1 ≤ T →
    (∫ t in (0 : ℝ)..T, ‖x t‖ ^ μ) / T ≤ C

def zeroAverage (f : ℝ → ℂ) : Prop :=
  Tendsto (fun T : ℝ => (T : ℂ)⁻¹ * ∫ t in (0 : ℝ)..T, f t) atTop (𝓝 0)

end HGASUndecidable.Main


