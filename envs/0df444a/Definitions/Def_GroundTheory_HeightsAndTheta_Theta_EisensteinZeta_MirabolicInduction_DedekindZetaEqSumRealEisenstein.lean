-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_DedekindZetaEqSumRealEisenstein
-- name    : GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_DedekindZetaEqSumRealEisenstein
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:01:50.233678+00:00
-- url     : https://prove2.me/theorems/7b43de8d-9ed7-4c8e-9c3e-253f20b6c175
-- title:
--   Dedekind Zeta Eq Sum Real Eisenstein
-- statement:
--   Definitions and structural lemmas for Dedekind Zeta Eq Sum Real Eisenstein, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/DedekindZetaEqSumRealEisenstein.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_DiscrNegAndAbsNormMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_DedekindZetaSeries_SummableDedekindZetaTerm
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_EtaPeriodLatticeClass_coord_unique_a2cc2d0ceb8a
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_EtaPeriodLatticeClass_mem_latticeOf_8c9b33b78633

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.Heights₂.Theta
namespace projectiveLineClassData
open NumberField UpperHalfPlane
open scoped nonZeroDivisors
section Series
def eisTerm (τ : ℍ) (s : ℝ) (p : ℤ × ℤ) : ℝ :=
  if p = 0 then 0 else τ.im ^ s / ‖(p.1 : ℂ) * τ + p.2‖ ^ (2 * s)
end Series
section IdealSum
variable (K : Type) [Field K] [NumberField K]
end IdealSum
section ClassSum
variable {K : Type} [Field K] [NumberField K]
open FractionalIdeal EtaPeriodLatticeClass
local notation "↑ᶠ" J => ((J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K)
theorem spanSingleton_mul_inv_le_one (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {x : K}
    (hx : x ∈ (↑ᶠ J)) : spanSingleton (𝓞 K)⁰ x * (↑ᶠ J⁻¹) ≤ 1 := by
  rw [spanSingleton_mul_le_iff]
  intro z hz
  have h := mul_mem_mul hx hz
  rwa [← Units.val_mul, mul_inv_cancel, Units.val_one] at h
def idealOf (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {x : K} (hx : x ∈ (↑ᶠ J)) : Ideal (𝓞 K) :=
  (le_one_iff_exists_coeIdeal.mp (spanSingleton_mul_inv_le_one J hx)).choose
theorem coe_idealOf (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {x : K} (hx : x ∈ (↑ᶠ J)) :
    ((idealOf J hx : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) =
      spanSingleton (𝓞 K)⁰ x * (↑ᶠ J⁻¹) :=
  (le_one_iff_exists_coeIdeal.mp (spanSingleton_mul_inv_le_one J hx)).choose_spec
theorem idealOf_mem (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {x : K} (hx : x ∈ (↑ᶠ J)) (hx0 : x ≠ 0) :
    idealOf J hx ∈ (Ideal (𝓞 K))⁰ := by
  rw [mem_nonZeroDivisors_iff_ne_zero]
  intro h
  have h2 := coe_idealOf J hx
  rw [h, Ideal.zero_eq_bot, coeIdeal_bot] at h2
  exact mul_ne_zero (spanSingleton_ne_zero_iff.mpr hx0) (Units.ne_zero _) h2.symm
theorem class_idealOf_eq_inv_class (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {x : K} (hx : x ∈ (↑ᶠ J)) (hx0 : x ≠ 0) :
    ClassGroup.mk0 ⟨idealOf J hx, idealOf_mem J hx hx0⟩ = (ClassGroup.mk K J)⁻¹ := by
  rw [← ClassGroup.mk_mk0 K]
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← map_mul, ClassGroup.mk_eq_one_iff, Units.val_mul, FractionalIdeal.coe_mk0, coe_idealOf,
    mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, mul_one, coe_spanSingleton]
  exact ⟨⟨x, rfl⟩⟩
abbrev Nz (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : Type := {x : K // x ∈ (↑ᶠ J) ∧ x ≠ 0}
abbrev InvClassIdeals (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : Type :=
  ((ClassGroup.mk0 ⁻¹' {(ClassGroup.mk K J)⁻¹} : Set (Ideal (𝓞 K))⁰))
def psi (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x : Nz J) : InvClassIdeals J :=
  ⟨⟨idealOf J x.2.1, idealOf_mem J x.2.1 x.2.2⟩, class_idealOf_eq_inv_class J x.2.1 x.2.2⟩
theorem coe_psi (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x : Nz J) :
    (((psi J x : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) =
      spanSingleton (𝓞 K)⁰ (x : K) * (↑ᶠ J⁻¹) :=
  coe_idealOf J x.2.1
theorem psi_eq_iff (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x y : Nz J) :
    psi J x = psi J y ↔ spanSingleton (𝓞 K)⁰ (x : K) = spanSingleton (𝓞 K)⁰ (y : K) := by
  constructor
  · intro h
    have h2 := congrArg (fun t : InvClassIdeals J =>
      (((t : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)) h
    simp only [coe_psi] at h2
    exact mul_right_cancel₀ (Units.ne_zero _) h2
  · intro h
    apply Subtype.ext
    apply Subtype.ext
    apply coeIdeal_injective (K := K)
    change (((psi J x : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) =
      (((psi J y : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)
    rw [coe_psi, coe_psi, h]
end ClassSum
section Fibres
variable {K : Type} [Field K] [NumberField K]
open FractionalIdeal
local notation "↑ᶠ" J => ((J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K)
def unitMul (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x₀ : Nz J) (u : (𝓞 K)ˣ) : Nz J :=
  ⟨algebraMap (𝓞 K) K (u : 𝓞 K) * x₀, by
    have h := Submodule.smul_mem ((↑ᶠ J) : Submodule (𝓞 K) K) (u : 𝓞 K) (mem_coe.mpr x₀.2.1)
    rw [Algebra.smul_def] at h
    exact mem_coe.mp h,
   mul_ne_zero ((map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr u.ne_zero) x₀.2.2⟩
theorem psi_unitMul (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x₀ : Nz J) (u : (𝓞 K)ˣ) :
    psi J (unitMul J x₀ u) = psi J x₀ := by
  rw [psi_eq_iff, eq_comm, spanSingleton_eq_spanSingleton]
  exact ⟨u, by rw [Units.smul_def, Algebra.smul_def]; rfl⟩
def fiberEquiv (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x₀ : Nz J) :
    (𝓞 K)ˣ ≃ (psi J ⁻¹' {psi J x₀}) :=
  Equiv.ofBijective (fun u => ⟨unitMul J x₀ u, psi_unitMul J x₀ u⟩) (by
    constructor
    · intro u v h
      have h2 := congrArg (fun y : (psi J ⁻¹' {psi J x₀}) => ((y : Nz J) : K)) h
      simp only [unitMul] at h2
      have h3 := mul_right_cancel₀ x₀.2.2 h2
      exact Units.ext (IsFractionRing.injective (𝓞 K) K h3)
    · rintro ⟨y, hy⟩
      have hy' : psi J y = psi J x₀ := hy
      rw [psi_eq_iff, eq_comm, spanSingleton_eq_spanSingleton] at hy'
      obtain ⟨z, hz⟩ := hy'
      refine ⟨z, Subtype.ext (Subtype.ext ?_)⟩
      rw [← hz, Units.smul_def, Algebra.smul_def]
      rfl)
end Fibres
section Lattice
variable {K : Type} [Field K] [NumberField K]
open FractionalIdeal EtaPeriodLatticeClass
local notation "↑ᶠ" J => ((J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K)
abbrev NzPair : Type := {p : ℤ × ℤ // p ≠ 0}
abbrev NzLattice (τ : ℍ) : Type := {z : ℂ // z ∈ latticeOf (τ : ℂ) ∧ z ≠ 0}
def pairToLattice (τ : ℍ) (p : NzPair) : NzLattice τ :=
  ⟨p.1.1 * τ + p.1.2, mem_latticeOf.mpr ⟨p.1.2, p.1.1, by ring⟩, by
    intro h
    apply p.2
    have := coord_unique (τ := τ) (m := p.1.2) (n := p.1.1) (m' := 0) (n' := 0)
      (by push_cast; linear_combination h)
    exact Prod.ext this.2 this.1⟩
def eltToLattice (σ : K →+* ℂ) (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (τ : ℍ) (c : ℂ) (hc : c ≠ 0)
    (himg : (fun z => c * z) '' (σ '' ((↑ᶠ J) : Set K)) = latticeOf (τ : ℂ)) (x : Nz J) :
    NzLattice τ :=
  ⟨c * σ x, by rw [← himg]; exact ⟨σ x, ⟨x, x.2.1, rfl⟩, rfl⟩,
    mul_ne_zero hc ((map_ne_zero σ).mpr x.2.2)⟩
end Lattice
section Main
end Main
end projectiveLineClassData
end GroundTheory.Heights₂.Theta


