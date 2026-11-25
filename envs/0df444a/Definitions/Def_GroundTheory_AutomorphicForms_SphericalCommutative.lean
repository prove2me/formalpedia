-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_SphericalCommutative
-- name    : GroundTheory_AutomorphicForms_SphericalCommutative
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T09:55:44.494692+00:00
-- url     : https://prove2.me/theorems/292a4825-16d6-47b7-a3ae-e43e5c4995e3
-- title:
--   Spherical Commutative
-- statement:
--   Definitions and structural lemmas for Spherical Commutative, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/SphericalCommutative.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HeckeIrreducible
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresGL
import Theorems.Thm_GroundTheory_Automorphic_Cartan_dominantEquivDoubleCoset_apply
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_isCompact_integralGL
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_quotientEquivLattice_mk
import Theorems.Thm_GroundTheory_Automorphic_HeckeAlgebra_mul_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.Cartan.dominantEquivDoubleCoset_apply
attribute [local simp] GroundTheory.Automorphic.GLnLocal.quotientEquivLattice_mk


set_option autoImplicit false
noncomputable section
namespace GroundTheory.Automorphic
open MeasureTheory Measure Matrix GLnLocal HeckeAlgebra
namespace Spherical
variable (F : Type*) [Field F] [ValuativeRel F] (n : ℕ)
def transposeInv : GL (Fin n) F ≃* GL (Fin n) F where
  toFun g := ⟨((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)ᵀ,
    ((g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)ᵀ,
    by rw [← transpose_mul, Units.mul_inv, transpose_one],
    by rw [← transpose_mul, Units.inv_mul, transpose_one]⟩
  invFun g := ⟨((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)ᵀ,
    ((g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)ᵀ,
    by rw [← transpose_mul, Units.mul_inv, transpose_one],
    by rw [← transpose_mul, Units.inv_mul, transpose_one]⟩
  left_inv g := Units.ext (transpose_transpose _)
  right_inv g := Units.ext (transpose_transpose _)
  map_mul' g h := Units.ext (by
    change (((g * h)⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)ᵀ =
      ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)ᵀ * ((h⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)ᵀ
    rw [_root_.mul_inv_rev, Units.val_mul, transpose_mul])
variable {F n}
@[simp]
theorem coe_transposeInv (g : GL (Fin n) F) :
    ((transposeInv F n g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)ᵀ := rfl
@[simp]
theorem coe_inv_transposeInv (g : GL (Fin n) F) :
    (((transposeInv F n g)⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      ((g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)ᵀ := rfl
theorem transposeInv_transposeInv (g : GL (Fin n) F) : transposeInv F n (transposeInv F n g) = g :=
  (transposeInv F n).left_inv g
theorem transposeInv_mem_integralGL {k : GL (Fin n) F} (hk : k ∈ integralGL F n) :
    transposeInv F n k ∈ integralGL F n := by
  rw [mem_integralGL_iff] at hk ⊢
  exact ⟨fun i j => hk.2 j i, fun i j => hk.1 j i⟩
theorem transposeInv_mem_integralGL_iff {k : GL (Fin n) F} :
    transposeInv F n k ∈ integralGL F n ↔ k ∈ integralGL F n :=
  ⟨fun h => by simpa [transposeInv_transposeInv] using transposeInv_mem_integralGL h,
    transposeInv_mem_integralGL⟩
theorem inv_transposeInv_diagPow [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (l : Fin n → ℤ) : (transposeInv F n (Cartan.diagPow F n l))⁻¹ = Cartan.diagPow F n l := by
  ext i j
  rw [coe_inv_transposeInv, Cartan.coe_diagPow, diagonal_transpose]
variable [TopologicalSpace F] [IsNonarchimedeanLocalField F]
theorem continuous_transposeInv : Continuous (transposeInv F n) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · change Continuous fun g : GL (Fin n) F => ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)ᵀ
    exact (Units.continuous_val.comp continuous_inv).matrix_transpose
  · change Continuous fun g : GL (Fin n) F => ((g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)ᵀ
    exact Units.continuous_val.matrix_transpose
def transposeInvHomeomorph : GL (Fin n) F ≃ₜ GL (Fin n) F where
  toEquiv := (transposeInv F n).toEquiv
  continuous_toFun := continuous_transposeInv
  continuous_invFun := continuous_transposeInv
variable [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)]
  (μ : Measure (GL (Fin n) F)) [μ.IsHaarMeasure]
theorem map_transposeInv : μ.map (transposeInv F n) = μ := by
  have hH : (μ.map (transposeInv F n)).IsHaarMeasure :=
    (transposeInv F n).isHaarMeasure_map μ continuous_transposeInv
      (transposeInvHomeomorph (F := F) (n := n)).continuous_invFun
  set K := integralGL F n
  have hK0 : μ K ≠ 0 := (isOpen_integralGL F n).measure_ne_zero μ ⟨1, K.one_mem⟩
  have hKT : μ K ≠ ⊤ := (isCompact_integralGL F n).measure_lt_top.ne
  have e := isMulLeftInvariant_eq_smul (μ.map (transposeInv F n)) μ
  have hpre : transposeInv F n ⁻¹' (K : Set (GL (Fin n) F)) = K := by
    ext x
    exact transposeInv_mem_integralGL_iff
  have hK : μ.map (transposeInv F n) K = μ K := by
    rw [map_apply continuous_transposeInv.measurable (isOpen_integralGL F n).measurableSet, hpre]
  have hc : haarScalarFactor (μ.map (transposeInv F n)) μ = 1 := by
    have h := congrArg (fun ν : Measure (GL (Fin n) F) => ν K) e
    simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h
    rw [hK] at h
    have := (ENNReal.mul_eq_right hK0 hKT).1 h.symm
    exact_mod_cast this
  rw [e, hc, one_smul]
theorem integral_comp_transposeInv (f : GL (Fin n) F → ℂ) :
    ∫ g, f (transposeInv F n g) ∂μ = ∫ g, f g ∂μ := by
  have := integral_map_equiv (μ := μ) (transposeInvHomeomorph (F := F) (n := n)).toMeasurableEquiv f
  change ∫ g, f g ∂(μ.map (transposeInv F n)) = _ at this
  rw [map_transposeInv] at this
  exact this.symm
theorem apply_inv_transposeInv {f : GL (Fin n) F → ℂ}
    (hf : ∀ k ∈ integralGL F n, ∀ x, f (k * x) = f x ∧ f (x * k) = f x) (g : GL (Fin n) F) :
    f (transposeInv F n g)⁻¹ = f g := by
  obtain ⟨l, -, k₁, hk₁, k₂, hk₂, rfl⟩ := Cartan.exists_eq_mul_diagPow_mul F n g
  have : (transposeInv F n (k₁ * Cartan.diagPow F n l * k₂))⁻¹ =
      (transposeInv F n k₂)⁻¹ * Cartan.diagPow F n l * (transposeInv F n k₁)⁻¹ := by
    rw [map_mul, map_mul, _root_.mul_inv_rev, _root_.mul_inv_rev, inv_transposeInv_diagPow, mul_assoc]
  have h₁ := (integralGL F n).inv_mem (transposeInv_mem_integralGL hk₁)
  have h₂ := (integralGL F n).inv_mem (transposeInv_mem_integralGL hk₂)
  rw [this, (hf _ h₁ _).2, (hf _ h₂ _).1, (hf _ hk₂ _).2, (hf _ hk₁ _).1]
variable {μ}
theorem heckeAlgebraLevel_mul_comm
    (a b : HeckeAlgebraLevel μ (integralGL F n) (isCompact_integralGL F n)
      (isOpen_integralGL F n)) : a * b = b * a := by
  have ha := HeckeAlgebraLevel.val_mem (isCompact_integralGL F n) (isOpen_integralGL F n) a
  have hb := HeckeAlgebraLevel.val_mem (isCompact_integralGL F n) (isOpen_integralGL F n) b
  have hab := HeckeAlgebraLevel.val_mem (isCompact_integralGL F n) (isOpen_integralGL F n) (a * b)
  refine HeckeAlgebraLevel.ext (isCompact_integralGL F n) (isOpen_integralGL F n)
    (HeckeAlgebra.ext fun x => ?_)
  rw [HeckeAlgebraLevel.val_mul, HeckeAlgebraLevel.val_mul]
  rw [HeckeAlgebra.mul_apply (b : HeckeAlgebra μ)]
  set c := (transposeInv F n x)⁻¹
  have step1 : ∫ y, (b : HeckeAlgebra μ) y * (a : HeckeAlgebra μ) (y⁻¹ * x) ∂μ =
      ∫ y, (b : HeckeAlgebra μ) (transposeInv F n y)⁻¹ *
        (a : HeckeAlgebra μ) (c * transposeInv F n y) ∂μ := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    have e1 := apply_inv_transposeInv hb y
    have e2 := apply_inv_transposeInv ha (y⁻¹ * x)
    have hyx : (transposeInv F n (y⁻¹ * x))⁻¹ = c * transposeInv F n y := by
      rw [map_mul, map_inv (transposeInv F n), _root_.mul_inv_rev, inv_inv]
    show _ * _ = _ * _
    rw [← e1, ← e2, hyx]
  have step2 : ∫ y, (b : HeckeAlgebra μ) (transposeInv F n y)⁻¹ *
        (a : HeckeAlgebra μ) (c * transposeInv F n y) ∂μ =
      ∫ w, (b : HeckeAlgebra μ) w⁻¹ * (a : HeckeAlgebra μ) (c * w) ∂μ :=
    integral_comp_transposeInv μ (fun w => (b : HeckeAlgebra μ) w⁻¹ * (a : HeckeAlgebra μ) (c * w))
  have step3 : ∫ w, (b : HeckeAlgebra μ) w⁻¹ * (a : HeckeAlgebra μ) (c * w) ∂μ =
      ((a : HeckeAlgebra μ) * (b : HeckeAlgebra μ)) c := by
    have key := integral_mul_left_eq_self (μ := μ)
      (fun y => (a : HeckeAlgebra μ) y * (b : HeckeAlgebra μ) (y⁻¹ * c)) c
    rw [HeckeAlgebra.mul_apply, ← key]
    refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    simp only [_root_.mul_inv_rev, inv_mul_cancel_right]
    ring
  rw [step1, step2, step3]
  have := apply_inv_transposeInv hab x
  rw [HeckeAlgebraLevel.val_mul] at this
  exact this.symm
instance instCommRing :
    CommRing (HeckeAlgebraLevel μ (integralGL F n) (isCompact_integralGL F n)
      (isOpen_integralGL F n)) :=
  { (inferInstance : Ring (HeckeAlgebraLevel μ (integralGL F n) (isCompact_integralGL F n)
      (isOpen_integralGL F n))) with
    mul_comm := heckeAlgebraLevel_mul_comm }
end Spherical
namespace HeckeAlgebra.HeckeAlgebraLevel
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  [MeasurableSpace G] [BorelSpace G] {μ : Measure G} [μ.IsHaarMeasure]
  {K : Subgroup G} (hKc : IsCompact (K : Set G)) (hKo : IsOpen (K : Set G))
instance : IsScalarTower ℂ (HeckeAlgebraLevel μ K hKc hKo) (HeckeAlgebraLevel μ K hKc hKo) where
  smul_assoc c a b := ext hKc hKo (by
    change ((c • a : HeckeAlgebraLevel μ K hKc hKo) : HeckeAlgebra μ) * (b : HeckeAlgebra μ) =
      c • ((a : HeckeAlgebra μ) * (b : HeckeAlgebra μ))
    rw [val_smul, smul_mul_assoc])
instance : SMulCommClass ℂ (HeckeAlgebraLevel μ K hKc hKo) (HeckeAlgebraLevel μ K hKc hKo) where
  smul_comm c a b := ext hKc hKo (by
    change c • ((a : HeckeAlgebra μ) * (b : HeckeAlgebra μ)) =
      (a : HeckeAlgebra μ) * ((c • b : HeckeAlgebraLevel μ K hKc hKo) : HeckeAlgebra μ)
    rw [val_smul, mul_smul_comm])
instance instAlgebra : Algebra ℂ (HeckeAlgebraLevel μ K hKc hKo) := Algebra.ofModule
  (fun c a b => smul_mul_assoc c a b) (fun c a b => (mul_smul_comm c a b))
end HeckeAlgebra.HeckeAlgebraLevel
end GroundTheory.Automorphic


