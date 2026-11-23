-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_ExpUpper
-- name    : Development_AbelianVarietyTheory_Definitions_Foundations_ExpUpper
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:04:44.894218+00:00
-- url     : https://prove2.me/theorems/86e8f8cd-fe73-4f5a-b01e-564a15ca1d1d
-- title:
--   Exp Upper
-- statement:
--   Definitions and structural lemmas for Exp Upper, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/ExpUpper.lean

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
open scoped MatrixGroups
namespace GlobalTheory.KZ
def Hs : Set ℂ := {z | 0 < z.im}
abbrev Mero : Type := Filter.Germ (Filter.codiscreteWithin Hs) ℂ
abbrev GQ : Type := ↥(Matrix.GLPos (Fin 2) ℚ)
def ent (g : GQ) (i j : Fin 2) : ℚ := ((g : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) i j
def mob (g : GQ) (z : ℂ) : ℂ :=
  ((ent g 0 0 : ℂ) * z + (ent g 0 1 : ℂ)) / ((ent g 1 0 : ℂ) * z + (ent g 1 1 : ℂ))
def ofSL : SL(2, ℤ) →* GQ :=
  Matrix.SpecialLinearGroup.toGLPos.comp (Matrix.SpecialLinearGroup.map (Int.castRingHom ℚ))
def en (γ : SL(2, ℤ)) (i j : Fin 2) : ℤ := (γ : Matrix (Fin 2) (Fin 2) ℤ) i j
def toGQ (m : Matrix (Fin 2) (Fin 2) ℤ) : GQ :=
  if h : 0 < m.det then
    ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (m.map (Int.castRingHom ℚ))
        (by
          have e := RingHom.map_det (Int.castRingHom ℚ) m
          simp only [RingHom.mapMatrix_apply] at e
          rw [← e, eq_intCast]; exact_mod_cast h.ne'),
      by
        show 0 < Matrix.det (m.map (Int.castRingHom ℚ))
        have e := RingHom.map_det (Int.castRingHom ℚ) m
        simp only [RingHom.mapMatrix_apply] at e
        rw [← e, eq_intCast]; exact_mod_cast h⟩
  else 1
def eOm {Ω : Type} [Field Ω] (ε : Ω →+* ℂ) (x : ℚ) : Ω :=
  Function.invFun ε (Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)))
structure Tower (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) where

  K : Type
  [fld : Field K]
  [alg : Algebra Ω K]

  exp : K →ₐ[Ω] HahnSeries ℚ Ω

  sl : GQ → (K ≃ₐ[Ω] K)

  sl_one : ∀ f, sl 1 f = f

  sl_mul : ∀ g h f, sl (g * h) f = sl h (sl g f)

  gal : (Ω ≃ₐ[ℚ] Ω) → (K ≃+* K)

  gal_exp : ∀ s f r, (exp (gal s f)).coeff r = s ((exp f).coeff r)

  an : K →+* Mero

  an_c : ∀ c : Ω, an (algebraMap Ω K c) = ((fun _ => ε c : ℂ → ℂ) : Mero)

  an_sl : ∀ (g : GQ) (f : K) (φ : ℂ → ℂ), an f = (φ : Mero) → an (sl g f) = ((fun z => φ (mob g z)) : Mero)

  an_mero : ∀ f : K, ∃ a b : ℂ → ℂ, DifferentiableOn ℂ a Hs ∧ DifferentiableOn ℂ b Hs ∧ (b : Mero) ≠ 0 ∧
    an f * (b : Mero) = (a : Mero)

  an_exp : ∀ f : K, ∃ (φ : ℂ → ℂ) (C : ℝ), an f = (φ : Mero) ∧ ∀ z : ℂ, C < z.im →
    HasSum (fun r : ℚ => ε ((exp f).coeff r) * Complex.exp (2 * Real.pi * Complex.I * (r : ℂ) * z)) (φ z)

  level : ∀ f : K, ∃ M : ℕ, 0 < M ∧ ∀ γ ∈ CongruenceSubgroup.Gamma M, sl (ofSL γ) f = f

  exp_upper : ∀ (g : GQ), ent g 1 0 = 0 → ∀ (f : K) (r : ℚ),
    (exp (sl g f)).coeff (r * ent g 0 0 / ent g 1 1) = eOm ε (r * ent g 0 1 / ent g 1 1) * (exp f).coeff r

  recip : ∀ (M : ℕ) (f : K), 0 < M → (∀ γ ∈ CongruenceSubgroup.Gamma M, sl (ofSL γ) f = f) →
    ∀ (ζ : Ω), IsPrimitiveRoot ζ M → ∀ (s : Ω ≃ₐ[ℚ] Ω) (d : ℤ), s ζ = ζ ^ d → ∀ γ γ' : SL(2, ℤ),
      ((en γ' 0 0 : ZMod M) = en γ 0 0 ∧ (en γ' 0 1 : ZMod M) = d * en γ 0 1 ∧
        (d : ZMod M) * en γ' 1 0 = en γ 1 0 ∧ (en γ' 1 1 : ZMod M) = en γ 1 1) →
      gal s (sl (ofSL γ) f) = sl (ofSL γ') (gal s f)

  jK : K

  j_inv : ∀ γ : SL(2, ℤ), sl (ofSL γ) jK = jK

  j_exp : (exp jK).coeff (-1) = 1 ∧ (∀ r : ℚ, r < -1 → (exp jK).coeff r = 0) ∧ ∀ r : ℚ, ∃ n : ℤ, (exp jK).coeff r = n

  j_hol : ∃ φ : ℂ → ℂ, an jK = (φ : Mero) ∧ DifferentiableOn ℂ φ Hs

  alg_j : ∀ f : K, IsAlgebraic (IntermediateField.adjoin Ω {jK}) f

  bdd : ∀ f : K, ∃ D : ℕ, 0 < D ∧ ∀ r : ℚ, ∃ k : ℕ, IsIntegral ℤ ((D : Ω) ^ k * (exp f).coeff r)

  sat : ∀ (a b : ℂ → ℂ) (M : ℕ), 0 < M → DifferentiableOn ℂ a Hs → DifferentiableOn ℂ b Hs → (b : Mero) ≠ 0 →
    (∀ γ ∈ CongruenceSubgroup.Gamma M, ((fun z => a (mob (ofSL γ) z) * b z) : Mero) = ((fun z => a z * b (mob (ofSL γ) z)) : Mero)) →
    (∃ P : Polynomial K, P ≠ 0 ∧ P.eval₂ an (((a / b : ℂ → ℂ)) : Mero) = 0) →
    ∃ f : K, an f * (b : Mero) = (a : Mero)

  mem_q : ∀ (a : ℂ → ℂ) (M : ℕ), 0 < M → DifferentiableOn ℂ a Hs →
    (∀ γ ∈ CongruenceSubgroup.Gamma M, ∀ z ∈ Hs, a (mob (ofSL γ) z) = a z) →
    (∀ γ : SL(2, ℤ), ∃ (c : ℤ → Ω) (n0 : ℤ), (∀ n < n0, c n = 0) ∧ ∀ z ∈ Hs,
      HasSum (fun n : ℤ => ε (c n) * Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * z / M)) (a (mob (ofSL γ) z))) →
    ∃ f : K, an f = (a : Mero)
attribute [instance] Tower.fld Tower.alg
example (z : ℂ) : mob 1 z = z := by
  simp [mob, ent]
example : ent (ofSL 1) 0 1 = 0 := by
  simp [ent]
example (z : ℂ) : mob (toGQ !![1, 1; 0, 1]) z = z + 1 := by
  have h : (0 : ℤ) < (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ).det := by simp [Matrix.det_fin_two]
  simp [mob, ent, toGQ, h]
example : (1 : ℂ) ∈ Hs ↔ False := by
  simp [Hs]
end GlobalTheory.KZ


