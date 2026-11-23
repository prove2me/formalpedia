-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_Integral
-- name    : Development_AbelianVarietyTheory_Definitions_Foundations_Integral
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:05:08.161733+00:00
-- url     : https://prove2.me/theorems/2364a9ea-9ac4-4279-8981-55314b9f180d
-- title:
--   Integral
-- statement:
--   Definitions and structural lemmas for Integral, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/Integral.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open scoped Classical
namespace GlobalTheory.KummerEisensteinGalois
variable {K : Type*} [Field K] [CharZero K]
def frc (M : ℕ) (a : ℤ) : ℚ := ((a % (M : ℤ) : ℤ) : ℚ) / M
def const0 (j M : ℕ) (ζ : K) (a₁ a₂ : ℤ) : K :=
  if j = 1 then
    (if (M : ℤ) ∣ a₁ then (1 / 2 : K) * (1 + ζ ^ a₂) / (1 - ζ ^ a₂) else ((1 / 2 - frc M a₁ : ℚ) : K))
  else -(((Polynomial.bernoulli j).eval (frc M a₁) / j : ℚ) : K)
def coefPos (j M : ℕ) (ζ : K) (a₁ a₂ : ℤ) (n : ℕ) : K :=
  ∑ d ∈ n.divisors,
    ((if ((n / d : ℕ) : ℤ) ≡ a₁ [ZMOD M] then (((n / d : ℕ) : K) / M) ^ (j - 1) * ζ ^ (a₂ * d) else 0) -
     (if (-((n / d : ℕ) : ℤ)) ≡ a₁ [ZMOD M] then (-(((n / d : ℕ) : K) / M)) ^ (j - 1) * ζ ^ (-(a₂ * d)) else 0))
def eisF (j M : ℕ) (ζ : K) (a₁ a₂ : ℤ) (n : ℕ) : K :=
  if n = 0 then const0 j M ζ a₁ a₂ else coefPos j M ζ a₁ a₂ n
def smF (c : ℤ) (j M : ℕ) (ζ : K) (a₁ a₂ : ℤ) (n : ℕ) : K :=
  (c : K) ^ 2 * eisF j M ζ a₁ a₂ n - (c : K) ^ ((2 : ℤ) - j) * eisF j M ζ (c * a₁) (c * a₂) n
def cmul (f g : ℕ → K) (n : ℕ) : K := ∑ i ∈ range (n + 1), f i * g (n - i)
def up (p : ℕ) (f : ℕ → K) (n : ℕ) : K := f (p * n)
def vp (p : ℕ) (f : ℕ → K) (n : ℕ) : K := if p ∣ n then f (n / p) else 0
def rowIdx (N p n : ℕ) (γ : GL (Fin 2) (ZMod (p ^ n))) (i : Fin 2) (y : ℤ) : ℤ × ℤ :=
  ((N : ℤ) * ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) i 0).val,
   (N : ℤ) * ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) i 1).val + (p : ℤ) ^ n * y)
def piece (N p n m k : ℕ) [NeZero p] (ψ : DirichletCharacter K (p ^ m)) (c d x t : ℤ) (ζ : K)
    (X : Finset (GL (Fin 2) (ZMod (p ^ n)))) (r : ℕ) : K :=
  -((p : K) ^ ((n : ℤ) * ((k : ℤ) - 4))) * ∑ γ ∈ X,
    ψ (((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))).det.val : ℕ) : ZMod (p ^ m)) *
      cmul (smF c (k - 1) (N * p ^ n) ζ (rowIdx N p n γ 0 (x * t)).1 (rowIdx N p n γ 0 (x * t)).2)
           (smF d 1 (N * p ^ n) ζ (rowIdx N p n γ 1 t).1 (rowIdx N p n γ 1 t).2) r
def unitSet (p n : ℕ) [NeZero p] : Finset (GL (Fin 2) (ZMod (p ^ n))) :=
  Finset.univ.filter fun γ => ¬ (p : ℕ) ∣ ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) 0 0).val ∧
    ¬ (p : ℕ) ∣ ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) 1 0).val
def gaussS (p m : ℕ) [NeZero p] (ψ : DirichletCharacter K (p ^ m)) (ζm : K) : K :=
  ∑ a : ZMod (p ^ m), ψ a * ζm ^ a.val
def ffPos (N p m k : ℕ) (ψ : DirichletCharacter K (p ^ m)) (x t : ℤ) (ζ : K) (full : Bool) (n : ℕ) : K :=
  ∑ d ∈ n.divisors, if (full || ¬ p ∣ d) && ¬ p ∣ (n / d) then
    (ψ ((n / d : ℕ) : ZMod (p ^ m)) * ((n / d : ℕ) : K) ^ (k - 2) * (ζ ^ (p ^ m)) ^ (x * t * d) -
     ψ (-((n / d : ℕ) : ZMod (p ^ m))) * (-((n / d : ℕ) : K)) ^ (k - 2) * (ζ ^ (p ^ m)) ^ (-(x * t * d)))
    else 0
def eePos (N p m : ℕ) (ψ : DirichletCharacter K (p ^ m)) (t : ℤ) (ζ : K) (full : Bool) (n : ℕ) : K :=
  ∑ d ∈ n.divisors, if (full || ¬ p ∣ (n / d)) && ¬ p ∣ d then
    (ψ⁻¹ ((d : ℕ) : ZMod (p ^ m)) * (ζ ^ (p ^ m)) ^ (t * d) -
     ψ⁻¹ (-((d : ℕ) : ZMod (p ^ m))) * (ζ ^ (p ^ m)) ^ (-(t * d)))
    else 0
def lval (p m k : ℕ) (ψ : DirichletCharacter K (p ^ m)) : K :=
  ((p : K) ^ m) ^ (k - 2) * ∑ u ∈ range (p ^ m), ψ (u : ZMod (p ^ m)) *
    (-(((Polynomial.bernoulli (k - 1)).eval ((u : ℚ) / (p ^ m : ℕ)) / (k - 1 : ℕ) : ℚ) : K))
def eeConst (N p m : ℕ) [NeZero p] (ψ : DirichletCharacter K (p ^ m)) (t : ℤ) (ζ : K) : K :=
  (gaussS p m ψ (ζ ^ N))⁻¹ * ∑ v ∈ range (p ^ m), ψ (v : ZMod (p ^ m)) *
    ((1 / 2 : K) * (1 + ζ ^ ((N : ℤ) * v + (p : ℤ) ^ m * t)) / (1 - ζ ^ ((N : ℤ) * v + (p : ℤ) ^ m * t)))
def ffSer (N p m k : ℕ) (ψ : DirichletCharacter K (p ^ m)) (x t : ℤ) (ζ : K) (n : ℕ) : K :=
  if n = 0 then lval p m k ψ else ffPos N p m k ψ x t ζ true n
def eeSer (N p m : ℕ) [NeZero p] (ψ : DirichletCharacter K (p ^ m)) (t : ℤ) (ζ : K) (n : ℕ) : K :=
  if n = 0 then eeConst N p m ψ t ζ else eePos N p m ψ t ζ true n
def xSer (N p m k : ℕ) [NeZero p] (ψ : DirichletCharacter K (p ^ m)) (x t : ℤ) (ζ : K) : ℕ → K :=
  cmul (ffSer N p m k ψ x t ζ) (eeSer N p m ψ t ζ)
def coPt (N p m k : ℕ) (ψ : DirichletCharacter K (p ^ m)) (x t : ℤ) (ζ : K) : ℕ → K :=
  cmul (fun n => if n = 0 then 0 else ffPos N p m k ψ x t ζ false n)
       (fun n => if n = 0 then 0 else eePos N p m ψ t ζ false n)
def toQ (M : ℕ) (f : ℕ → K) (n : ℕ) : K := f (M * n)
def Integral (M : ℕ) (f : ℕ → K) : Prop := ∀ n, ¬ M ∣ n → f n = 0
end GlobalTheory.KummerEisensteinGalois


