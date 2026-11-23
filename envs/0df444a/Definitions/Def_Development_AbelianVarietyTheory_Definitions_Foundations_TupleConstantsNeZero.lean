-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_TupleConstantsNeZero
-- name    : Development_AbelianVarietyTheory_Definitions_Foundations_TupleConstantsNeZero
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T04:57:50.849795+00:00
-- url     : https://prove2.me/theorems/7c1268d5-4409-4977-baa2-a6e1b19f33d0
-- title:
--   Tuple Constants Ne Zero
-- statement:
--   Definitions and structural lemmas for Tuple Constants Ne Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/TupleConstantsNeZero.lean

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementH
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Finset
open Formalism.DivisionValues (vw conjPl)
open Formalism.PairingDivisionLocalBalance (Pl wt)
noncomputable section
namespace GlobalTheory.Square
variable {K : Type} [Field K] [NumberField K] [StarRing K]
def IsAwayUnit (m : ℕ) (x : K) : Prop :=
  ∃ (a : 𝓞 K) (k k' : ℕ), a ∣ (m : 𝓞 K) ^ k' ∧ x * (m : K) ^ k = (a : K)
structure An (y : ℕ) where

  c : ℂ

  c0 : ℂ

  u : Fin y → ℂ

  Lv : ℤ → ℂ
structure Co (K κ : Type) where

  X : Type
  [finX : Fintype X]

  gam : X → ℕ

  z : X → κ → K

  z' : X → κ → K
attribute [instance] Co.finX
def normAlg {κ X : Type} [Fintype κ] [Fintype X] (G : κ → κ → K) (gam : X → ℕ) (z : X → κ → K) : K :=
  ∑ x, (gam x : K)⁻¹ * ∑ k, ∑ l, z x k * star (z x l) * G k l
structure Sq (K : Type) where

  κ : Type
  [finκ : Fintype κ]

  G : κ → κ → K

  Om : ℂ

  Om' : ℂ

  A : ℂ

  e : ℕ

  p : ℕ

  q : ℕ

  e0 : ℕ

  h0 : ℕ

  base : An (p + q)
attribute [instance] Sq.finκ
structure Sq.OK (S : Sq K) (hd y : ℕ) : Prop where

  e0_eq : S.e0 + S.p = S.e + S.q

  sqrt_error_le_half : S.e0 ≤ S.h0

  hd_eq : hd = S.h0 + S.p + S.q

  y_eq : y = S.p + S.q

  Om_ne : S.Om ≠ 0

  Om'_ne : S.Om' ≠ 0

  A_ne : S.A ≠ 0

  c_ne : S.base.c ≠ 0
structure Sq.Tuple (S : Sq K) (σ₀ : K →+* ℂ) (a : An (S.p + S.q)) (Z : Co K S.κ) (w : Pl K) (dl : ℝ) : Prop where

  tower : a.c * ∏ k ∈ range S.q, a.Lv ((S.e : ℤ) + k + 1) =
    (∏ i, a.u i) * a.c0 * ∏ k ∈ range S.p, a.Lv ((S.e : ℤ) + S.q - k)

  bottom : ∀ x k, σ₀ (Z.z x k) * S.Om = a.c0 * (σ₀ (Z.z' x k) * S.Om')

  norm_eq : σ₀ (normAlg S.G Z.gam Z.z) * ((‖S.Om‖ ^ 2 : ℝ) : ℂ) =
    S.A * ∏ s ∈ Icc (1 - (S.e0 : ℤ)) (S.h0 : ℤ), a.Lv s

  norm'_ne : normAlg S.G Z.gam Z.z' ≠ 0

  L_ne : ∀ s : ℤ, 1 - (S.e0 : ℤ) ≤ s → s ≤ (S.h0 : ℤ) + S.p + S.q → a.Lv s ≠ 0

  u_ne : ∀ i, a.u i ≠ 0

  gam_pos : ∀ x, 0 < Z.gam x

  z_int : ∀ x k, -dl ≤ (vw w (Z.z x k) : ℝ) ∧ -dl ≤ (vw (conjPl w) (Z.z x k) : ℝ)

  z'_int : ∀ x k, -dl ≤ (vw w (Z.z' x k) : ℝ) ∧ -dl ≤ (vw (conjPl w) (Z.z' x k) : ℝ)

  G_int : ∀ x k l, -dl ≤ (vw w (S.G k l / (Z.gam x : K)) : ℝ)
def StepRatio {T : Type} (σ₀ : K →+* ℂ) (Qn : ℕ) (S0 : Finset T) (cc qq : T → ℕ) (u1 u0 : ℂ) : Prop :=
  ∃ (b : K) (g g' : T → 𝓞 K), IsAwayUnit Qn b ∧
    (∀ v ∈ S0, g v ∣ (qq v : 𝓞 K) ^ cc v ∧ g' v ∣ (qq v : 𝓞 K) ^ cc v) ∧
    u1 = σ₀ (b * ∏ v ∈ S0, (g v : K) / (g' v : K)) * u0
def Sq.Twisted (S : Sq K) (σ₀ : K →+* ℂ) (w : Pl K) (cw : ℂ) (zA zA' : K) (zT zTd : ℤ → K) (gT : ℤ → ℤ) (n0 : ℤ → ℝ)
    (er dl : ℝ) {T : Type} (S0 : Finset T) (cc qq : T → ℕ) : Prop :=
  ∃ (a : An (S.p + S.q)) (Z0 Z1 : Co K S.κ) (zψ Ep : ℤ → K) (Qn : ℕ),
    a.c = cw ∧ S.Tuple σ₀ S.base Z0 w dl ∧ S.Tuple σ₀ a Z1 w dl ∧
    normAlg S.G Z0.gam Z0.z = zA ∧ normAlg S.G Z0.gam Z0.z' = zA' ∧ (Qn : 𝓞 K) ∉ w.asIdeal ∧
    (∀ s : ℤ, 1 ≤ s → s ≤ (S.h0 : ℤ) + S.p + S.q →
      zT s ≠ 0 ∧ zTd s ≠ 0 ∧ σ₀ (zψ s) * S.base.Lv s = σ₀ (zT s) * a.Lv s ∧
      -(n0 s) ≤ ((vw w (zψ s) + gT s : ℤ) : ℝ) ∧ (vw w (zψ s) : ℝ) ≤ (vw w (zTd s) : ℝ) + er) ∧
    (∀ s : ℤ, 1 - (S.e0 : ℤ) ≤ s → s ≤ 0 → IsAwayUnit Qn (Ep s) ∧
      a.Lv s * S.base.Lv (1 - s) = σ₀ (Ep s) * (a.Lv (1 - s) * S.base.Lv s)) ∧
    (∀ i, StepRatio σ₀ Qn S0 cc qq (a.u i) (S.base.u i))
namespace TwoStep
def square (K : Type) [Field K] : Sq K where
  κ := Unit
  G := fun _ _ => 1
  Om := Complex.I
  Om' := 1
  A := 1
  e := 1
  p := 1
  q := 1
  e0 := 1
  h0 := 1
  base := ⟨Complex.I, Complex.I, fun _ => 1, fun _ => 1⟩
def coords (K : Type) [Field K] (t : ℕ) : Co K Unit where
  X := Fin 2
  gam := fun _ => 2
  z := fun _ _ => t
  z' := fun _ _ => 1
def numbers (n m Q : ℕ) : An 2 :=
  ⟨(n ^ 2 * m * Q : ℕ) * Complex.I, (m * Q : ℕ) * Complex.I, fun _ => n, fun s => if s = 0 then (Q ^ 2 * m : ℕ) else m⟩
end TwoStep
example : IsAwayUnit 2 (1 / 2 : ℚ) := ⟨1, 1, 0, by simp, by norm_num⟩
example (s t : K) : normAlg (κ := Fin 2) (X := Unit) ![![0, 1], ![0, 0]] (fun _ => 1) (fun _ => ![s, t]) = s * star t := by
  simp [normAlg, Fin.sum_univ_two]
end GlobalTheory.Square


