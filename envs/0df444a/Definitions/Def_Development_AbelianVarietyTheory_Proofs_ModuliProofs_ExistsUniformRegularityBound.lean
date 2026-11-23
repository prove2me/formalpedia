-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniformRegularityBound
-- name    : Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniformRegularityBound
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:14:38.314149+00:00
-- url     : https://prove2.me/theorems/d315af75-ce3f-434a-a815-9d80810cef5e
-- title:
--   Exists Uniform Regularity Bound
-- statement:
--   Definitions and structural lemmas for Exists Uniform Regularity Bound, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsUniformRegularityBound.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Module MvPolynomial
namespace GlobalTheory.RegBound
variable {σ K : Type} [Field K]
noncomputable abbrev piece (I : Ideal (MvPolynomial σ K)) (e : ℕ) : Submodule K (MvPolynomial σ K) :=
  homogeneousSubmodule σ K e ⊓ I.restrictScalars K
noncomputable abbrev genIn (I : Ideal (MvPolynomial σ K)) (e : ℕ) : Ideal (MvPolynomial σ K) :=
  Ideal.span {G | G ∈ I ∧ G.IsHomogeneous e}
instance finite_forms [Finite σ] (e : ℕ) : Module.Finite K (homogeneousSubmodule σ K e) :=
  Module.Finite.iff_fg.2 (homogeneousSubmodule_fg σ K e)
instance finite_piece [Finite σ] (I : Ideal (MvPolynomial σ K)) (e : ℕ) :
    Module.Finite K (piece I e) :=
  Submodule.finiteDimensional_of_le (S₂ := homogeneousSubmodule σ K e) inf_le_left
noncomputable def nmon (σ : Type) (e : ℕ) : ℕ := Nat.card {d : σ →₀ ℕ | d.degree = e}
section BaseChange
variable {L : Type} [Field L] [Algebra K L]
noncomputable def contr (φ : L →ₗ[K] K) (F : MvPolynomial σ L) : MvPolynomial σ K :=
  ∑ m ∈ F.support, monomial m (φ (coeff m F))
@[simp] theorem coeff_contr (φ : L →ₗ[K] K) (F : MvPolynomial σ L) (m : σ →₀ ℕ) :
    coeff m (contr φ F) = φ (coeff m F) := by
  classical
  simp only [contr, coeff_sum, coeff_monomial, Finset.sum_ite_eq', MvPolynomial.mem_support_iff]
  split_ifs with h
  · rfl
  · rw [not_not.1 h, map_zero]
theorem contr_add (φ : L →ₗ[K] K) (F G : MvPolynomial σ L) :
    contr φ (F + G) = contr φ F + contr φ G := by ext; simp
theorem contr_zero (φ : L →ₗ[K] K) : contr φ (0 : MvPolynomial σ L) = 0 := by ext; simp
theorem contr_X_mul (φ : L →ₗ[K] K) (i : σ) (F : MvPolynomial σ L) :
    contr φ (X i * F) = X i * contr φ F := by
  classical
  ext m
  simp only [coeff_contr, coeff_X_mul']
  split_ifs <;> simp
theorem contr_smul (φ : L →ₗ[K] K) (c : L) (F : MvPolynomial σ L) :
    contr φ (c • F) = contr (φ ∘ₗ LinearMap.mulLeft K c) F := by ext; simp
def extSub (L : Type) [Field L] [Algebra K L] (W : Submodule K (MvPolynomial σ K)) :
    Submodule L (MvPolynomial σ L) where
  carrier := {F | ∀ φ : L →ₗ[K] K, contr φ F ∈ W}
  add_mem' ha hb φ := by rw [contr_add]; exact W.add_mem (ha φ) (hb φ)
  zero_mem' φ := by rw [contr_zero]; exact W.zero_mem
  smul_mem' c F hF φ := by rw [contr_smul]; exact hF _
def extIdeal (L : Type) [Field L] [Algebra K L] (I : Ideal (MvPolynomial σ K)) :
    Ideal (MvPolynomial σ L) where
  carrier := {F | ∀ φ : L →ₗ[K] K, contr φ F ∈ I}
  add_mem' ha hb φ := by rw [contr_add]; exact I.add_mem (ha φ) (hb φ)
  zero_mem' φ := by rw [contr_zero]; exact I.zero_mem
  smul_mem' A F hF := by
    rw [smul_eq_mul]
    induction A using MvPolynomial.induction_on generalizing F with
    | C a => intro φ; rw [C_mul', contr_smul]; exact hF _
    | add p q hp hq => intro φ; rw [add_mul, contr_add]; exact I.add_mem (hp _ hF φ) (hq _ hF φ)
    | mul_X p i hp =>
      rw [mul_assoc]
      exact hp _ fun φ => by rw [contr_X_mul]; exact I.mul_mem_left _ (hF φ)
end BaseChange
end GlobalTheory.RegBound
namespace GlobalTheory
end GlobalTheory


