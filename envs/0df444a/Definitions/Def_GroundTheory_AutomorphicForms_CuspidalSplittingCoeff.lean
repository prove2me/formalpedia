-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_CuspidalSplittingCoeff
-- name    : GroundTheory_AutomorphicForms_CuspidalSplittingCoeff
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T12:41:48.877015+00:00
-- url     : https://prove2.me/theorems/51eb7024-ba31-40aa-ac32-b8ddd66e8ea5
-- title:
--   Cuspidal Splitting Coeff
-- statement:
--   Definitions and structural lemmas for Cuspidal Splitting Coeff, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/CuspidalSplittingCoeff.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_CuspidalSplittingSums
import Theorems.Thm_GroundTheory_Automorphic_Cartan_dominantEquivDoubleCoset_apply
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_quotientEquivLattice_mk
import Theorems.Thm_GroundTheory_Automorphic_Measures_adUnipotentHom_apply
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_IsCompactModCenter_comp_inv
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_finite_support_quotSum
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_isCompactModCenter_matrixCoeff
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_quotSum_congr
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_quotSum_mul_left
import Theorems.Thm_GroundTheory_Automorphic_coinvariantsTranslate_mk
import Theorems.Thm_GroundTheory_Automorphic_frobenius_apply
import Theorems.Thm_GroundTheory_Automorphic_frobenius_symm_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.Cartan.dominantEquivDoubleCoset_apply
attribute [local simp] GroundTheory.Automorphic.GLnLocal.quotientEquivLattice_mk
attribute [local simp] GroundTheory.Automorphic.Measures.adUnipotentHom_apply
attribute [local simp] GroundTheory.Automorphic.coinvariantsTranslate_mk
attribute [local simp] GroundTheory.Automorphic.frobenius_apply
attribute [local simp] GroundTheory.Automorphic.frobenius_symm_apply


set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.Automorphic
namespace Parabolic
open Function
open scoped Pointwise
theorem linearMap_finsum {ι M N : Type*} [AddCommMonoid M] [AddCommMonoid N] [Module ℂ M]
    [Module ℂ N] (L : M →ₗ[ℂ] N) {φ : ι → M} (h : HasFiniteSupport φ) :
    L (∑ᶠ i, φ i) = ∑ᶠ i, L (φ i) :=
  map_finsum L h
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}
section CentralChar
variable {U : Type*} [AddCommGroup U] [Module ℂ U]
def HasCentralChar (ρ : Representation ℂ (GL (Fin n) F) U) (ω : GL (Fin n) F → ℂ) : Prop :=
  ∀ z ∈ Subgroup.center (GL (Fin n) F), ∀ u, ρ z u = ω z • u
variable {ρ : Representation ℂ (GL (Fin n) F) U} {ω : GL (Fin n) F → ℂ}
end CentralChar
section CenterSup
abbrev centerSup (K : Subgroup (GL (Fin n) F)) : Subgroup (GL (Fin n) F) :=
  Subgroup.center (GL (Fin n) F) ⊔ K
omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem mem_centerSup {K : Subgroup (GL (Fin n) F)} {x : GL (Fin n) F} :
    x ∈ centerSup K ↔ ∃ z ∈ Subgroup.center (GL (Fin n) F), ∃ k ∈ K, z * k = x :=
  Subgroup.mem_sup_of_normal_left
omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in

theorem rightInv_centerSup {X : Type*} {K : Subgroup (GL (Fin n) F)} {Φ : GL (Fin n) F → X}
    (hZ : ∀ g, ∀ z ∈ Subgroup.center (GL (Fin n) F), Φ (g * z) = Φ g)
    (hK : ∀ g, ∀ k ∈ K, Φ (g * k) = Φ g) : ∀ g, ∀ h ∈ centerSup K, Φ (g * h) = Φ g := by
  intro g h hh
  obtain ⟨z, hz, k, hk, rfl⟩ := mem_centerSup.1 hh
  rw [← mul_assoc, hK _ k hk, hZ g z hz]
theorem isOpen_centerSup {K : Subgroup (GL (Fin n) F)} (hKo : IsOpen (K : Set (GL (Fin n) F))) :
    IsOpen (centerSup K : Set (GL (Fin n) F)) :=
  Subgroup.isOpen_mono le_sup_right hKo
theorem finite_support_centerSup {M : Type*} [AddCommMonoid M] {K : Subgroup (GL (Fin n) F)}
    (hKo : IsOpen (K : Set (GL (Fin n) F))) {Φ : GL (Fin n) F → M} {φ : GL (Fin n) F → ℂ}
    (hφ : IsCompactModCenter φ) (h : ∀ g, φ g = 0 → Φ g = 0) :
    HasFiniteSupport fun q : GL (Fin n) F ⧸ centerSup K => Φ q.out := by
  obtain ⟨C, hC, hsupp⟩ := hφ
  exact finite_support_quotSum (isOpen_centerSup hKo) le_sup_left hC
    (fun g hg => hsupp (mt (h g) hg))
end CenterSup
section CoeffSum
variable {V U W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup U] [Module ℂ U]
  [AddCommGroup W] [Module ℂ W]
  (π : Representation ℂ (GL (Fin n) F) V) (ρ : Representation ℂ (GL (Fin n) F) U)
def coeffSum (K : Subgroup (GL (Fin n) F)) (f : Module.Dual ℂ V) (u : U) (w : V) : U :=
  quotSum (centerSup K) fun g => f (π g⁻¹ w) • ρ g u
variable {π ρ} {K : Subgroup (GL (Fin n) F)} {f : Module.Dual ℂ V} {u : U}
  {ω : GL (Fin n) F → ℂ}
omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in

theorem coeffSum_summand_rightInv (hωπ : HasCentralChar π ω) (hωρ : HasCentralChar ρ ω)
    (hω : ∀ z ∈ Subgroup.center (GL (Fin n) F), ω z⁻¹ * ω z = 1)
    (hf : ∀ k ∈ K, ∀ x, f (π k x) = f x) (hu : u ∈ fixedVectors ρ K) (w : V) :
    ∀ g, ∀ h ∈ centerSup K, f (π (g * h)⁻¹ w) • ρ (g * h) u = f (π g⁻¹ w) • ρ g u := by
  refine rightInv_centerSup (Φ := fun g => f (π g⁻¹ w) • ρ g u) (fun g z hz => ?_)
    (fun g k hk => ?_)
  · have e1 : π (g * z)⁻¹ w = ω z⁻¹ • π g⁻¹ w := by
      rw [mul_inv_rev, map_mul, Module.End.mul_apply, hωπ _ (inv_mem hz)]
    have e2 : ρ (g * z) u = ω z • ρ g u := by
      rw [map_mul, Module.End.mul_apply, hωρ z hz, map_smul]
    rw [e1, e2, map_smul, smul_eq_mul, smul_smul]
    congr 1
    linear_combination f (π g⁻¹ w) * hω z hz
  · have e1 : π (g * k)⁻¹ w = π k⁻¹ (π g⁻¹ w) := by
      rw [mul_inv_rev, map_mul, Module.End.mul_apply]
    rw [e1, hf _ (inv_mem hk), map_mul, Module.End.mul_apply, hu k hk]
theorem mem_smoothVectors_dual_of_inv (hKo : IsOpen (K : Set (GL (Fin n) F)))
    (hf : ∀ k ∈ K, ∀ x, f (π k x) = f x) : f ∈ smoothVectors (Representation.dual π) :=
  mem_smoothVectors_of_mem_fixedVectors hKo (mem_fixedVectors_dual.2 hf)
theorem finite_support_coeffSum (hπ : IsSmooth π) (hsc : IsSupercuspidal π)
    (hKo : IsOpen (K : Set (GL (Fin n) F))) (hf : ∀ k ∈ K, ∀ x, f (π k x) = f x) (w : V) :
    HasFiniteSupport fun q : GL (Fin n) F ⧸ centerSup K => f (π q.out⁻¹ w) • ρ q.out u :=
  finite_support_centerSup (Φ := fun g => f (π g⁻¹ w) • ρ g u) hKo
    (isCompactModCenter_matrixCoeff hπ hsc w (mem_smoothVectors_dual_of_inv hKo hf)).comp_inv
    fun g h0 => by
      change f (π g⁻¹ w) = 0 at h0
      simp only [h0, zero_smul]
variable (hπ : IsSmooth π) (hsc : IsSupercuspidal π) (hKo : IsOpen (K : Set (GL (Fin n) F)))
  (hωπ : HasCentralChar π ω) (hωρ : HasCentralChar ρ ω)
  (hω : ∀ z ∈ Subgroup.center (GL (Fin n) F), ω z⁻¹ * ω z = 1)
  (hf : ∀ k ∈ K, ∀ x, f (π k x) = f x) (hu : u ∈ fixedVectors ρ K)
include hπ hsc hKo hf in
theorem coeffSum_add (w₁ w₂ : V) :
    coeffSum π ρ K f u (w₁ + w₂) = coeffSum π ρ K f u w₁ + coeffSum π ρ K f u w₂ := by
  unfold coeffSum quotSum
  rw [← finsum_add_distrib (finite_support_coeffSum hπ hsc hKo hf w₁)
    (finite_support_coeffSum hπ hsc hKo hf w₂)]
  refine finsum_congr fun q => ?_
  dsimp only
  rw [map_add, map_add, add_smul]
include hπ hsc hKo hf in
theorem coeffSum_smul (c : ℂ) (w : V) :
    coeffSum π ρ K f u (c • w) = c • coeffSum π ρ K f u w := by
  unfold coeffSum quotSum
  rw [smul_finsum' c (finite_support_coeffSum hπ hsc hKo hf w)]
  refine finsum_congr fun q => ?_
  dsimp only
  rw [map_smul, map_smul, smul_eq_mul, mul_smul]
include hπ hsc hKo hωπ hωρ hω hf hu in

theorem coeffSum_act (x : GL (Fin n) F) (w : V) :
    coeffSum π ρ K f u (π x w) = ρ x (coeffSum π ρ K f u w) := by
  have hΨ := coeffSum_summand_rightInv hωπ hωρ hω hf hu w
  have hΨ' : ∀ g, ∀ h ∈ centerSup K, ρ x (f (π (g * h)⁻¹ w) • ρ (g * h) u) =
      ρ x (f (π g⁻¹ w) • ρ g u) := fun g h hh => by rw [hΨ g h hh]
  calc coeffSum π ρ K f u (π x w)
      = quotSum (centerSup K) fun g => ρ x (f (π (x⁻¹ * g)⁻¹ w) • ρ (x⁻¹ * g) u) := by
        refine quotSum_congr fun g => ?_
        have h1 : (x⁻¹ * g)⁻¹ = g⁻¹ * x := by group
        rw [map_smul, h1, map_mul π g⁻¹ x, Module.End.mul_apply, ← Module.End.mul_apply (ρ x),
          ← map_mul ρ, mul_inv_cancel_left]
    _ = quotSum (centerSup K) fun g => ρ x (f (π g⁻¹ w) • ρ g u) :=
        quotSum_mul_left (Φ := fun g => ρ x (f (π g⁻¹ w) • ρ g u)) hΨ' x⁻¹
    _ = ρ x (coeffSum π ρ K f u w) :=
        (linearMap_finsum (ρ x) (finite_support_coeffSum hπ hsc hKo hf w)).symm
def coeffMap : Representation.IntertwiningMap π ρ where
  toFun := coeffSum π ρ K f u
  map_add' := coeffSum_add hπ hsc hKo hf
  map_smul' := coeffSum_smul hπ hsc hKo hf
  isIntertwining' x := LinearMap.ext fun w => coeffSum_act hπ hsc hKo hωπ hωρ hω hf hu x w
end CoeffSum
section Scalar
variable {V : Type*} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ (GL (Fin n) F) V}
  {K : Subgroup (GL (Fin n) F)} {f : Module.Dual ℂ V} {v : V} {ω : GL (Fin n) F → ℂ}
end Scalar
end Parabolic
end GroundTheory.Automorphic


