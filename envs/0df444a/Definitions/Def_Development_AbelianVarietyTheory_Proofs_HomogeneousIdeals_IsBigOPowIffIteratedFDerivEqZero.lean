-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsBigOPowIffIteratedFDerivEqZero
-- name    : Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsBigOPowIffIteratedFDerivEqZero
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T00:01:00.128193+00:00
-- url     : https://prove2.me/theorems/04616b72-d404-493d-aea5-c2bf5f26bbc8
-- title:
--   Is Big OPow Iff Iterated FDeriv Eq Zero
-- statement:
--   Definitions and structural lemmas for Is Big OPow Iff Iterated FDeriv Eq Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsBigOPowIffIteratedFDerivEqZero.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MemUnitaryGroupIffIsIsometry
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsAddFundamentalDomainLatticeDomain
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_EqExpFderiv
import Theorems.Thm_GlobalTheory_mem_prodLpLattice
import Theorems.Thm_GlobalTheory_ringOfIntegers_coe_star
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.mem_prodLpLattice
attribute [local simp] GlobalTheory.ringOfIntegers_coe_star


set_option autoImplicit false
open Filter Topology Asymptotics Complex
open scoped Real ComplexConjugate
namespace GlobalTheory.Doubling
noncomputable section
section Rigidity
variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup G]
  [NormedSpace ℂ G]
end Rigidity
section Series
variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup G]
  [NormedSpace ℂ G]
def quadPart (h : E → G) (z : E) : G := (2 : ℂ)⁻¹ • iteratedFDeriv ℂ 2 h 0 fun _ => z
def doublingSeries (p : FormalMultilinearSeries ℂ E G) : FormalMultilinearSeries ℂ E G :=
  fun n => if n ≤ 2 then 0 else (-((2 : ℂ) ^ n - 4)⁻¹) • p n
end Series
section Character
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
end Character
section Alternating
variable {V : Type*} [AddCommGroup V] [Module ℂ V]
theorem alt_I_smul_I_smul {B : V → V → ℂ} (hB : ∀ z u, B (I • z) u = I * B z u)
    (hE : ∀ u v, (B v u - B u v).im = 0) (u v : V) :
    B (I • v) (I • u) - B (I • u) (I • v) = B v u - B u v := by
  have h1 := hE (I • u) (I • v)
  have h2 := hE (I • u) v
  have h3 := hE u (I • v)
  have h4 := hE u v
  simp only [hB, sub_im, mul_im, I_re, I_im, zero_mul, one_mul, zero_add] at h1 h2 h3 h4 ⊢
  apply Complex.ext <;> simp <;> linarith
def altHerm (l : V →ₗ[ℝ] V →ₗ[ℂ] ℂ) (hE : ∀ u v, (l u v - l v u).im = 0) : HermForm ℂ V :=
  HermForm.ofFun (fun u v => (l (I • u) v - l v (I • u)) + I * (l u v - l v u))
    (fun x y z => by simp; ring)
    (fun a x y => by
      have h := alt_I_smul_I_smul (B := fun z u => l u z) (by simp) hE x (I • y)
      have ha : ∀ w : V, a • w = a.re • w + a.im • (I • w) := fun w => by
        conv_lhs => rw [← re_add_im a, add_smul, mul_smul]
        rfl
      have hII : ∀ w : V, I • I • w = -w := fun w => by simp [smul_smul]
      rw [smul_comm I a x, ha x, ha (I • x), hII]
      simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, map_neg,
        LinearMap.neg_apply, LinearMap.map_smul_of_tower, real_smul, smul_eq_mul]
      conv_rhs => rw [← re_add_im a]
      linear_combination (-(a.im : ℂ) * (l x y - l y x)) * I_sq)
    (fun x y => by
      have h := alt_I_smul_I_smul (B := fun z u => l u z) (by simp) hE x (I • y)
      have hII : ∀ w : V, I • I • w = -w := fun w => by simp [smul_smul]
      have h1 := conj_eq_iff_im.2 (hE (I • x) y)
      have h2 := conj_eq_iff_im.2 (hE x y)
      rw [star_add, star_mul', Complex.star_def, h1, h2, conj_I]
      simp only [hII, map_neg, LinearMap.neg_apply] at h
      linear_combination -h)
end Alternating
section Lattice
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L]
end Lattice
example (z : ℂ) : quadPart (fun z : ℂ => z ^ 2 + z ^ 4) z = z ^ 2 := by
  have h1 : deriv (fun z : ℂ => z ^ 2 + z ^ 4) = fun z => 2 * z + 4 * z ^ 3 := by
    funext z; simp
  have h2 : deriv (fun z : ℂ => 2 * z + 4 * z ^ 3) 0 = 2 := by
    have := (((hasDerivAt_id (0 : ℂ)).const_mul 2).fun_add ((hasDerivAt_pow 3 0).const_mul 4)).deriv
    simpa using this
  rw [quadPart, iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod, iteratedDeriv_succ,
    iteratedDeriv_one, h1, h2]
  simp [sq]
  ring
example (z : ℂ) : cexp (π * (z + I) ^ 2 / 2) * jacobiTheta₂ (z + I) I =
    1 * cexp (π * (z * conj I) + π * (I * conj I) / 2) * (cexp (π * z ^ 2 / 2) * jacobiTheta₂ z I) := by
  rw [jacobiTheta₂_add_left', ← mul_assoc, ← mul_assoc, one_mul, ← exp_add, ← exp_add, conj_I]
  congr 2
  linear_combination ((π : ℂ) / 2 - π + π / 2) * I_sq
end
end GlobalTheory.Doubling


