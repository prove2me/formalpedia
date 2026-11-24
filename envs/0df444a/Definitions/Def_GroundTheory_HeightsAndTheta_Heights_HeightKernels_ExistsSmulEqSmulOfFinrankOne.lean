-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ExistsSmulEqSmulOfFinrankOne
-- name    : GroundTheory_HeightsAndTheta_Heights_HeightKernels_ExistsSmulEqSmulOfFinrankOne
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:11:05.508455+00:00
-- url     : https://prove2.me/theorems/557854a0-9ef1-405e-9b15-3e8fce7378f0
-- title:
--   Exists Smul Eq Smul Of Finrank One
-- statement:
--   Definitions and structural lemmas for Exists Smul Eq Smul Of Finrank One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/ExistsSmulEqSmulOfFinrankOne.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HermitianSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StdCoordMapInjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels
open NumberField NumberField.ComplexEmbedding TensorProduct Matrix GroundTheory.Heights₂.Heights
open scoped nonZeroDivisors
noncomputable section
section Coefficient
variable {K : Type*} [Field K] [NumberField K] {E : HermitianBundle K}
theorem exists_smul_eq_smul_of_finrank_one {N : Submodule (𝓞 K) E.carrier}
    (hN : Module.finrank (𝓞 K) N = 1) {l : E.carrier} (hl : l ∈ N) (hl0 : l ≠ 0)
    {w : E.carrier} (hw : w ∈ N) : ∃ t s : 𝓞 K, t ≠ 0 ∧ t • w = s • l := by
  by_contra hcon
  simp only [not_exists, not_and] at hcon
  have hli : LinearIndependent (𝓞 K) ![(⟨w, hw⟩ : N), ⟨l, hl⟩] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h : s • w + t • l = 0 := congrArg Subtype.val hst
    by_cases hs : s = 0
    · subst hs
      rw [zero_smul, zero_add] at h
      exact ⟨rfl, (smul_eq_zero.mp h).resolve_right hl0⟩
    · exact absurd (by rw [neg_smul]; exact eq_neg_of_add_eq_zero_left h) (hcon s (-t) hs)
  have := hli.fintype_card_le_finrank
  rw [Fintype.card_fin, hN] at this
  omega
theorem lineCoef_ratio_unique {l w : E.carrier} (hl0 : l ≠ 0) {t s t' s' : 𝓞 K} (ht : t ≠ 0) (ht' : t' ≠ 0)
    (h : t • w = s • l) (h' : t' • w = s' • l) : (s : K) / t = s' / t' := by
  have key : (t' * s - t * s') • l = 0 := by
    rw [sub_smul, mul_smul, mul_smul, ← h, ← h', smul_comm t' t, sub_self]
  have key' : t' * s = t * s' := sub_eq_zero.mp ((smul_eq_zero.mp key).resolve_right hl0)
  have h1 : (t : K) ≠ 0 := by exact_mod_cast ht
  have h2 : (t' : K) ≠ 0 := by exact_mod_cast ht'
  have h3 := congrArg (fun x : 𝓞 K => (x : K)) key'
  push_cast at h3
  rw [div_eq_div_iff h1 h2]
  linear_combination h3
variable {N : Submodule (𝓞 K) E.carrier} (hN : Module.finrank (𝓞 K) N = 1) {l : E.carrier}
  (hl : l ∈ N) (hl0 : l ≠ 0)
def lineCoefFun (w : N) : K :=
  ((exists_smul_eq_smul_of_finrank_one hN hl hl0 w.2).choose_spec.choose : K) /
    ((exists_smul_eq_smul_of_finrank_one hN hl hl0 w.2).choose : K)
theorem lineCoefFun_eq (w : N) {t s : 𝓞 K} (ht : t ≠ 0) (h : t • (w : E.carrier) = s • l) :
    lineCoefFun hN hl hl0 w = (s : K) / t :=
  lineCoef_ratio_unique hl0 (exists_smul_eq_smul_of_finrank_one hN hl hl0 w.2).choose_spec.choose_spec.1 ht
    (exists_smul_eq_smul_of_finrank_one hN hl hl0 w.2).choose_spec.choose_spec.2 h
def lineCoef : N →ₗ[𝓞 K] K where
  toFun := lineCoefFun hN hl hl0
  map_add' w w' := by
    obtain ⟨t, s, ht, h⟩ := exists_smul_eq_smul_of_finrank_one hN hl hl0 w.2
    obtain ⟨t', s', ht', h'⟩ := exists_smul_eq_smul_of_finrank_one hN hl hl0 w'.2
    have h'' : (t * t') • ((w + w' : N) : E.carrier) = (t' * s + t * s') • l := by
      rw [Submodule.coe_add, smul_add, mul_smul, mul_smul, h', smul_comm t t' (w : E.carrier), h,
        ← mul_smul, ← mul_smul, ← add_smul]
    rw [lineCoefFun_eq hN hl hl0 w ht h, lineCoefFun_eq hN hl hl0 w' ht' h',
      lineCoefFun_eq hN hl hl0 (w + w') (mul_ne_zero ht ht') h'']
    have h1 : (t : K) ≠ 0 := by exact_mod_cast ht
    have h2 : (t' : K) ≠ 0 := by exact_mod_cast ht'
    push_cast
    field_simp
  map_smul' c w := by
    obtain ⟨t, s, ht, h⟩ := exists_smul_eq_smul_of_finrank_one hN hl hl0 w.2
    have h' : t • ((c • w : N) : E.carrier) = (c * s) • l := by
      rw [Submodule.coe_smul, smul_comm, h, mul_smul]
    rw [lineCoefFun_eq hN hl hl0 w ht h, lineCoefFun_eq hN hl hl0 (c • w) ht h', RingHom.id_apply,
      Algebra.smul_def]
    push_cast
    rw [mul_div_assoc]
end Coefficient
end
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels


