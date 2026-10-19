-- Prove2me | Definitions.Def_QAlgorithms_Defs_SunWoottersData
-- name    : QAlgorithms_Defs_SunWoottersData
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:33:11.512973+00:00
-- url     : https://prove2.me/theorems/02e1320f-f4dc-40b4-95f0-9e5ee7b7a7c2
-- title:
--   SunWoottersData
-- statement:
--   SunWoottersData
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\SunWoottersData.lean

import Definitions.Def_QAlgorithms_Defs_ReedSolomonDecoders
noncomputable section

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.SunWootters

/-- Common-density discrepancy; 2607.16541 p.7 (8). -/
def discrepancy {p : ℕ} (S : Finset (ZMod p)) (rho : ℝ)
    (_hrho : 0 < rho ∧ rho < 1) (a : ZMod p) : ℝ :=
  ((if a ∈ S then 1 else 0)-rho)/Real.sqrt (rho*(1-rho))

/-- Negative-phase, 1/p-normalized local Fourier coefficients;
2607.16541 p.6 (4). This is not the unitary QFT normalization. -/
def localFourier {p : ℕ} [NeZero p] (g : ZMod p → ℝ) (z : ZMod p) : ℂ :=
  (p : ℂ)⁻¹*∑ a : ZMod p, (g a : ℂ)*
    Complex.exp (-2*Real.pi*Complex.I*((a*z).val : ℂ)/p)

/-- Unordered elementary symmetric discrepancy product; 2607.16541 p.7 (10). -/
def symmetricProduct {p m n : ℕ} (B : Matrix (Fin m) (Fin n) (ZMod p))
    (g : Fin m → ZMod p → ℝ) (k : ℕ) (x : Fin n → ZMod p) : ℝ :=
  ∑ T ∈ (Finset.univ : Finset (Fin m)).powersetCard k, ∏ i ∈ T, g i (B.mulVec x i)

/-- Positive nonempty shell domain; 2607.16541 p.7 (11).
Signed subtraction is used in shell construction. -/
structure ShellDomain (m : ℕ) where
  ell : ℕ
  lower : 3 ≤ ell
  upper : ell ≤ m

/-- log-log-width shell, using natural logarithms and signed lower endpoint;
2607.16541 p.7 (11). -/
def shell {m : ℕ} (D : ShellDomain m) : Finset ℕ :=
  (Finset.range (m+1)).filter fun k =>
    (D.ell : ℤ)-⌊Real.log (Real.log D.ell)⌋ ≤ (k : ℤ) ∧ k ≤ D.ell

/-- Amplitude, not probability, weights; 2607.16541 p.8 (12). -/
def shellWeights {m : ℕ} (D : ShellDomain m) (k : ℕ) : ℝ :=
  if k ∈ shell D then (Real.sqrt (Nat.choose m k))⁻¹ else 0

/-- Actual constructed shell amplitude; 2607.16541 p.8 (12)–(13). -/
def targetAmplitude {p m n : ℕ} (B : Matrix (Fin m) (Fin n) (ZMod p))
    (g : Fin m → ZMod p → ℝ) (D : ShellDomain m) (x : Fin n → ZMod p) : ℝ :=
  ∑ k ∈ shell D, shellWeights D k*symmetricProduct B g k x

/-- Target probability weights, only on their positive denominator domain;
2607.16541 p.8 (13). No zero polynomial is silently normalized. -/
def targetLaw {p m n : ℕ} [NeZero p] (B : Matrix (Fin m) (Fin n) (ZMod p))
    (g : Fin m → ZMod p → ℝ) (D : ShellDomain m)
    (_positive : 0 < ∑ x : Fin n → ZMod p, targetAmplitude B g D x^2) :
    (Fin n → ZMod p) → ℝ :=
  fun x => targetAmplitude B g D x^2/(∑ y : Fin n → ZMod p, targetAmplitude B g D y^2)

/-- Exact rational cutoff with floor of the whole first expression;
2607.16541 p.17, theorem 7.1. -/
def rationalCutoff (m n : ℕ) (delta : ℚ) (_positive : 0 < delta) : ℕ :=
  min ⌊(n : ℚ)/2+delta*m⌋₊ (m/2)

example {p m n : ℕ} (B : Matrix (Fin m) (Fin n) (ZMod p))
    (g : Fin m → ZMod p → ℝ) (x : Fin n → ZMod p) :
    symmetricProduct B g 0 x = 1 := by simp [symmetricProduct,Finset.powersetCard_zero]

example : rationalCutoff 5 1 (1/10) (by norm_num) = 1 := by
  norm_num [rationalCutoff]


end QAlgorithms.SunWootters


