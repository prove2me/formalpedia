-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ZetaActRefl
-- name    : Development_AbelianVarietyTheory_Definitions_Divisors_ZetaActRefl
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:05:49.614838+00:00
-- url     : https://prove2.me/theorems/56c9d279-1de0-4873-9b0c-3777f9ce2588
-- title:
--   Zeta Act Refl
-- statement:
--   Definitions and structural lemmas for Zeta Act Refl, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ZetaActRefl.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped UpperHalfPlane MatrixGroups Matrix
open GlobalTheory.QFam
namespace GlobalTheory.WpFam
def pv (τ : ℍ) (x : Fin 2 → ℝ) : ℂ := (x 0 : ℂ) * τ + (x 1 : ℂ)
def eta (τ : ℍ) (x : Fin 2 → ℝ) : ℂ := EisensteinSeries.G2 τ * pv τ x - 2 * Real.pi * Complex.I * (x 0 : ℂ)
def G2s (τ : ℍ) : ℂ := EisensteinSeries.G2 τ - (Real.pi : ℂ) / (τ.im : ℂ)
def redR (γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℝ := (γ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ℝ)
def redGL (N : ℕ) (γ : SL(2, ℤ)) : GL (Fin 2) (ZMod N) :=
  Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod N)) γ)
def vmul {N : ℕ} (x : Fin 2 → ZMod N) (α : GL (Fin 2) (ZMod N)) : Fin 2 → ZMod N :=
  x ᵥ* (α : Matrix (Fin 2) (Fin 2) (ZMod N))
def vact (N : ℕ) (x : Fin 2 → ZMod N) (γ : SL(2, ℤ)) : Fin 2 → ZMod N := vmul x (redGL N γ)
def gact (N : ℕ) (D : GL (Fin 2) (ZMod N)) (α : GL (Fin 2) (ZMod N)) (γ : SL(2, ℤ)) : GL (Fin 2) (ZMod N) :=
  α * (D * redGL N γ * D⁻¹)
def dg {N : ℕ} (a : (ZMod N)ˣ) : GL (Fin 2) (ZMod N) where
  val := !![1, 0; 0, (a : ZMod N)]
  inv := !![1, 0; 0, ((a⁻¹ : (ZMod N)ˣ) : ZMod N)]
  val_inv := by rw [Matrix.mul_fin_two, Matrix.one_fin_two]; simp
  inv_val := by rw [Matrix.mul_fin_two, Matrix.one_fin_two]; simp
def tors (N : ℕ) (τ : ℍ) (x : Fin 2 → ZMod N) : ℂ := (((x 0).val : ℂ) * τ + ((x 1).val : ℂ)) / N
def wp (N : ℕ) (x : Fin 2 → ZMod N) (τ : ℍ) : ℂ :=
  (tauPair τ).weierstrassP (tors N τ x) / (2 * Real.pi * Complex.I) ^ 2
def wpd (N : ℕ) (x : Fin 2 → ZMod N) (τ : ℍ) : ℂ :=
  (tauPair τ).derivWeierstrassP (tors N τ x) / (2 * Real.pi * Complex.I) ^ 3
def gN (τ : ℍ) : ℂ := EisensteinSeries.G2 τ / (2 * Real.pi * Complex.I) ^ 2
def wB (N : ℕ) (x : Fin 2 → ZMod N) (τ : ℍ) : ℂ := gN τ + wp N x τ
def ch (N : ℕ) (j : ZMod N) : ℂ := Complex.exp (2 * Real.pi * Complex.I * (j.val : ℂ) / N)
def ZetaAct (g : ℂ ≃+* ℂ) (N : ℕ) (a : ZMod N) : Prop := ∀ j : ZMod N, g (ch N j) = ch N (a * j)
open Classical in

def cSum (N e : ℕ) (ε : ℂ) (x : Fin 2 → ZMod N) (k : ℕ) : ℂ :=
  ∑ m ∈ k.divisors, (m : ℂ) ^ e * ((if ((k / m : ℕ) : ZMod N) = x 0 then ch N ((m : ZMod N) * x 1) else 0) +
    ε * (if ((k / m : ℕ) : ZMod N) = -x 0 then ch N (-((m : ZMod N) * x 1)) else 0))
open Classical in

def cB (N : ℕ) (x : Fin 2 → ZMod N) (k : ℕ) : ℂ :=
  if k = 0 then (if x 0 = 0 then ch N (x 1) / (1 - ch N (x 1)) ^ 2 else 0) else cSum N 1 1 x k
open Classical in

def cD (N : ℕ) (x : Fin 2 → ZMod N) (k : ℕ) : ℂ :=
  if k = 0 then (if x 0 = 0 then ch N (x 1) * (1 + ch N (x 1)) / (1 - ch N (x 1)) ^ 3 else 0) else cSum N 2 (-1) x k
def cG (N : ℕ) (k : ℕ) : ℂ :=
  if k = 0 then -1 / 12 else if N ∣ k then 2 * (ArithmeticFunction.sigma 1 (k / N) : ℂ) else 0
open Classical in

def cP (N : ℕ) (x : Fin 2 → ZMod N) (k : ℕ) : ℂ := if x = 0 then 0 else cB N x k - cG N k
end GlobalTheory.WpFam


