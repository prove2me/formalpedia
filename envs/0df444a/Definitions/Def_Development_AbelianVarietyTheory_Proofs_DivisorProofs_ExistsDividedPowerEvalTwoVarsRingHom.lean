-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsDividedPowerEvalTwoVarsRingHom
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsDividedPowerEvalTwoVarsRingHom
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:02:27.159792+00:00
-- url     : https://prove2.me/theorems/a92dcb2a-f620-4e3a-92fd-7abd132927ff
-- title:
--   Exists Divided Power Eval Two Vars Ring Hom
-- statement:
--   Definitions and structural lemmas for Exists Divided Power Eval Two Vars Ring Hom, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsDividedPowerEvalTwoVarsRingHom.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.DPEval2
def bv (p : ℕ × ℕ) : MvPolynomial (Fin 2) ℚ :=
  ((p.1.factorial : ℚ)⁻¹ • (X 0 : MvPolynomial (Fin 2) ℚ) ^ p.1) * ((p.2.factorial : ℚ)⁻¹ • X 1 ^ p.2)
def ex (p : ℕ × ℕ) : Fin 2 →₀ ℕ := Finsupp.single 0 p.1 + Finsupp.single 1 p.2
theorem ex_injective : Function.Injective ex := by
  intro p q h
  have h0 := congrArg (fun f : Fin 2 →₀ ℕ ↦ f 0) h
  have h1 := congrArg (fun f : Fin 2 →₀ ℕ ↦ f 1) h
  simp [ex] at h0 h1
  exact Prod.ext h0 h1
theorem bv_eq (p : ℕ × ℕ) :
    bv p = ((p.1.factorial : ℚ)⁻¹ * (p.2.factorial : ℚ)⁻¹) • monomial (ex p) (1 : ℚ) := by
  rw [bv, ex, X_pow_eq_monomial, X_pow_eq_monomial, smul_monomial, smul_monomial, monomial_mul,
    smul_monomial]
  simp
theorem bv_li : LinearIndependent ℚ bv := by
  have h := ((basisMonomials (Fin 2) ℚ).linearIndependent.comp ex ex_injective).units_smul
    (fun p : ℕ × ℕ ↦ Units.mk0 ((p.1.factorial : ℚ)⁻¹ * (p.2.factorial : ℚ)⁻¹) (by positivity))
  have e : bv = (fun p : ℕ × ℕ ↦ Units.mk0 ((p.1.factorial : ℚ)⁻¹ * (p.2.factorial : ℚ)⁻¹) (by positivity)) •
      (⇑(basisMonomials (Fin 2) ℚ) ∘ ex) := by
    funext p
    simp [bv_eq, Units.smul_def, coe_basisMonomials]
  rw [e]; exact h
def D : Submodule ℤ (MvPolynomial (Fin 2) ℚ) := Submodule.span ℤ (Set.range bv)
theorem bv_mem (p : ℕ × ℕ) : bv p ∈ D := Submodule.subset_span ⟨p, rfl⟩
def β : Module.Basis (ℕ × ℕ) ℤ D := Module.Basis.span (bv_li.restrict_scalars' ℤ)
variable {B : Type} [CommRing B] (u v : ℕ → B)
def ψ : D →ₗ[ℤ] B := β.constr ℤ fun p ↦ u p.1 * v p.2
open Classical in

def φ (q : MvPolynomial (Fin 2) ℚ) : B := if h : q ∈ D then ψ u v ⟨q, h⟩ else 0
end GlobalTheory.DPEval2
namespace GlobalTheory
end GlobalTheory


