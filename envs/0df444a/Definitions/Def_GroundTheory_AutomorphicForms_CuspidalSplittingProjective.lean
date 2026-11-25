-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_CuspidalSplittingProjective
-- name    : GroundTheory_AutomorphicForms_CuspidalSplittingProjective
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T13:15:53.094909+00:00
-- url     : https://prove2.me/theorems/2c58d441-03aa-51d2-bf52-a6fe2011308e
-- title:
--   Cuspidal Splitting Projective
-- statement:
--   Definitions and structural lemmas for Cuspidal Splitting Projective, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/CuspidalSplittingProjective.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_CuspidalSplittingPositivity
import Theorems.Thm_GroundTheory_Automorphic_Cartan_dominantEquivDoubleCoset_apply
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_quotientEquivLattice_mk
import Theorems.Thm_GroundTheory_Automorphic_Measures_adUnipotentHom_apply
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
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}
variable {V U W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup U] [Module ℂ U]
  [AddCommGroup W] [Module ℂ W] {π : Representation ℂ (GL (Fin n) F) V}
  {ρ : Representation ℂ (GL (Fin n) F) U} {σ : Representation ℂ (GL (Fin n) F) W}
  {ω : GL (Fin n) F → ℂ}
section Injective
variable (σ π) in

def pairingSum (K : Subgroup (GL (Fin n) F)) (ψ : Module.Dual ℂ W) (v : V) (b : W)
    (ũ : smoothVectors (Representation.dual π)) : ℂ :=
  quotSum (centerSup K) fun g => ψ (σ g⁻¹ b) * (ũ : Module.Dual ℂ V) (π g v)
variable {K : Subgroup (GL (Fin n) F)} {ψ : Module.Dual ℂ W} {v : V}
theorem finite_support_pairingSum (hπ : IsSmooth π) (hsc : IsSupercuspidal π)
    (hKo : IsOpen (K : Set (GL (Fin n) F))) (b : W) (ũ : smoothVectors (Representation.dual π)) :
    HasFiniteSupport fun q : GL (Fin n) F ⧸ centerSup K =>
      ψ (σ q.out⁻¹ b) * (ũ : Module.Dual ℂ V) (π q.out v) :=
  finite_support_centerSup (Φ := fun g => ψ (σ g⁻¹ b) * (ũ : Module.Dual ℂ V) (π g v)) hKo
    (isCompactModCenter_matrixCoeff hπ hsc v ũ.2) fun g h0 => by
      change (ũ : Module.Dual ℂ V) (π g v) = 0 at h0
      simp only [h0, mul_zero]
theorem pairingSum_summand_rightInv (hωπ : HasCentralChar π ω) (hωσ : HasCentralChar σ ω)
    (hω : ∀ z ∈ Subgroup.center (GL (Fin n) F), ω z⁻¹ * ω z = 1)
    (hψ : ∀ k ∈ K, ∀ x, ψ (σ k x) = ψ x) (hv : v ∈ fixedVectors π K) (b : W)
    (ũ : smoothVectors (Representation.dual π)) :
    ∀ g, ∀ h ∈ centerSup K, ψ (σ (g * h)⁻¹ b) * (ũ : Module.Dual ℂ V) (π (g * h) v) =
      ψ (σ g⁻¹ b) * (ũ : Module.Dual ℂ V) (π g v) := by
  refine rightInv_centerSup
    (Φ := fun g => ψ (σ g⁻¹ b) * (ũ : Module.Dual ℂ V) (π g v)) (fun g z hz => ?_)
    (fun g k hk => ?_)
  · have e1 : σ (g * z)⁻¹ b = ω z⁻¹ • σ g⁻¹ b := by
      rw [mul_inv_rev, map_mul, Module.End.mul_apply, hωσ _ (inv_mem hz)]
    have e2 : π (g * z) v = ω z • π g v := by
      rw [map_mul, Module.End.mul_apply, hωπ z hz, map_smul]
    simp only [e1, e2, map_smul, smul_eq_mul]
    linear_combination ψ (σ g⁻¹ b) * (ũ : Module.Dual ℂ V) (π g v) * hω z hz
  · have e1 : σ (g * k)⁻¹ b = σ k⁻¹ (σ g⁻¹ b) := by
      rw [mul_inv_rev, map_mul, Module.End.mul_apply]
    simp only [e1, hψ _ (inv_mem hk), map_mul, Module.End.mul_apply, hv k hk]
variable (hπ : IsSmooth π) (hsc : IsSupercuspidal π) (hωπ : HasCentralChar π ω)
  (hωσ : HasCentralChar σ ω) (hω : ∀ z ∈ Subgroup.center (GL (Fin n) F), ω z⁻¹ * ω z = 1)
  (hKo : IsOpen (K : Set (GL (Fin n) F))) (hψ : ∀ k ∈ K, ∀ x, ψ (σ k x) = ψ x)
  (hv : v ∈ fixedVectors π K)
include hπ hsc hωπ hωσ hω hKo hψ hv
omit hπ hsc hKo in

theorem pairingSum_act (h : GL (Fin n) F) (b : W) (ũ : smoothVectors (Representation.dual π)) :
    pairingSum π σ K ψ v (σ h b) ũ = pairingSum π σ K ψ v b (contragredient π h⁻¹ ũ) := by
  unfold pairingSum
  rw [← quotSum_mul_left (pairingSum_summand_rightInv hωπ hωσ hω hψ hv (σ h b) ũ) h]
  refine quotSum_congr fun g => ?_
  rw [contragredient_apply_apply, inv_inv, mul_inv_rev, map_mul, Module.End.mul_apply,
    ← Module.End.mul_apply (σ h⁻¹), ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply,
    map_mul, Module.End.mul_apply]
omit hωπ hωσ hω hψ hv in
theorem pairingSum_add (b : W) (ũ₁ ũ₂ : smoothVectors (Representation.dual π)) :
    pairingSum π σ K ψ v b (ũ₁ + ũ₂) = pairingSum π σ K ψ v b ũ₁ + pairingSum π σ K ψ v b ũ₂ := by
  unfold pairingSum quotSum
  rw [← finsum_add_distrib (finite_support_pairingSum hπ hsc hKo b ũ₁)
    (finite_support_pairingSum hπ hsc hKo b ũ₂)]
  refine finsum_congr fun q => ?_
  simp only [Submodule.coe_add, LinearMap.add_apply, mul_add]
omit hωπ hωσ hω hψ hv in
theorem pairingSum_smul (b : W) (c : ℂ) (ũ : smoothVectors (Representation.dual π)) :
    pairingSum π σ K ψ v b (c • ũ) = c • pairingSum π σ K ψ v b ũ := by
  unfold pairingSum quotSum
  rw [smul_finsum' c (finite_support_pairingSum hπ hsc hKo b ũ)]
  refine finsum_congr fun q => ?_
  simp only [SetLike.val_smul, LinearMap.smul_apply, smul_eq_mul]
  ring
omit hωπ hωσ hω hψ hv in
theorem pairingSum_add_left (b₁ b₂ : W) (ũ : smoothVectors (Representation.dual π)) :
    pairingSum π σ K ψ v (b₁ + b₂) ũ = pairingSum π σ K ψ v b₁ ũ + pairingSum π σ K ψ v b₂ ũ := by
  unfold pairingSum quotSum
  rw [← finsum_add_distrib (finite_support_pairingSum hπ hsc hKo b₁ ũ)
    (finite_support_pairingSum hπ hsc hKo b₂ ũ)]
  refine finsum_congr fun q => ?_
  simp only [map_add, add_mul]
omit hωπ hωσ hω hψ hv in
theorem pairingSum_smul_left (c : ℂ) (b : W) (ũ : smoothVectors (Representation.dual π)) :
    pairingSum π σ K ψ v (c • b) ũ = c • pairingSum π σ K ψ v b ũ := by
  unfold pairingSum quotSum
  rw [smul_finsum' c (finite_support_pairingSum hπ hsc hKo b ũ)]
  refine finsum_congr fun q => ?_
  simp only [map_smul, smul_eq_mul]
  ring
omit hωπ hωσ hω hψ hv in

def pairingForm (b : W) : Module.Dual ℂ (smoothVectors (Representation.dual π)) where
  toFun := pairingSum π σ K ψ v b
  map_add' := pairingSum_add hπ hsc hKo b
  map_smul' c ũ := pairingSum_smul hπ hsc hKo b c ũ
theorem pairingForm_mem (hσ : IsSmooth σ) (b : W) :
    pairingForm (σ := σ) hπ hsc hKo (K := K) (ψ := ψ) (v := v) b ∈
      smoothVectors (Representation.dual (contragredient π)) := by
  rw [mem_smoothVectors]
  refine Subgroup.isOpen_mono (fun h hh => ?_) (hσ b)
  rw [mem_stabilizerOf] at hh ⊢
  refine LinearMap.ext fun ũ => ?_
  rw [dual_apply_apply]
  change pairingSum π σ K ψ v b (contragredient π h⁻¹ ũ) = pairingSum π σ K ψ v b ũ
  rw [← pairingSum_act hωπ hωσ hω hψ hv, hh]
omit hπ hsc hωπ hωσ hω hKo hψ hv in

def pairingMap (hπ : IsSmooth π) (hsc : IsSupercuspidal π) (hωπ : HasCentralChar π ω)
    (hωσ : HasCentralChar σ ω) (hω : ∀ z ∈ Subgroup.center (GL (Fin n) F), ω z⁻¹ * ω z = 1)
    (hKo : IsOpen (K : Set (GL (Fin n) F))) (hψ : ∀ k ∈ K, ∀ x, ψ (σ k x) = ψ x)
    (hv : v ∈ fixedVectors π K) (hσ : IsSmooth σ) :
    Representation.IntertwiningMap σ (contragredient (contragredient π)) where
  toFun b := ⟨pairingForm (σ := σ) hπ hsc hKo b, pairingForm_mem hπ hsc hωπ hωσ hω hKo hψ hv hσ b⟩
  map_add' b₁ b₂ := Subtype.ext (LinearMap.ext fun ũ => pairingSum_add_left hπ hsc hKo b₁ b₂ ũ)
  map_smul' c b := Subtype.ext (LinearMap.ext fun ũ => pairingSum_smul_left hπ hsc hKo c b ũ)
  isIntertwining' h := LinearMap.ext fun b => Subtype.ext (LinearMap.ext fun ũ => by
    change pairingSum π σ K ψ v (σ h b) ũ = pairingSum π σ K ψ v b (contragredient π h⁻¹ ũ)
    exact pairingSum_act hωπ hωσ hω hψ hv h b ũ)
end Injective
end Parabolic
end GroundTheory.Automorphic


