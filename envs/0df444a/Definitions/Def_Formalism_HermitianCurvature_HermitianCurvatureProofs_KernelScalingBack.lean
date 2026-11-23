-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelScalingBack
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelScalingBack
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T18:18:56.288844+00:00
-- url     : https://prove2.me/theorems/49af28c7-7bc3-46af-84b5-ccc28fdb64e6
-- title:
--   Kernel Scaling Back
-- statement:
--   Definitions and structural lemmas for Kernel Scaling Back, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/KernelScalingBack.lean

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ColumnOperationTripleForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LatticeAverageIdentity
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revIn
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Supp_blk_revIn
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_mv_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_gl_coe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.blk_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_val
attribute [local simp] Formalism.FourierDecayAlt.P.A5x5.mv_apply


set_option autoImplicit false
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open scoped ComplexConjugate
noncomputable section
namespace Formalism.FourierDecayAlt.P.KernelScalingBack
section Diag
variable {K : Type} [CommRing K] {n : ℕ}
def DG (d : Fin n → Kˣ) : GL (Fin n) K :=
  ⟨diagonal fun b => ((d b : Kˣ) : K), diagonal fun b => (((d b)⁻¹ : Kˣ) : K),
    by rw [diagonal_mul_diagonal]; simp, by rw [diagonal_mul_diagonal]; simp⟩
theorem DG_coe (d : Fin n → Kˣ) :
    ((DG d : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = diagonal fun b => ((d b : Kˣ) : K) := rfl
theorem DG_inv_coe (d : Fin n → Kˣ) :
    (((DG d)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      diagonal fun b => (((d b)⁻¹ : Kˣ) : K) := rfl
def cj (d : Fin n → Kˣ) (g : GL (Fin n) K) : GL (Fin n) K := (DG d)⁻¹ * g * DG d
theorem cj_apply (d : Fin n → Kˣ) (g : GL (Fin n) K) (a b : Fin n) :
    ((cj d g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) a b =
      (((d a)⁻¹ : Kˣ) : K) * (g : Matrix (Fin n) (Fin n) K) a b * ((d b : Kˣ) : K) := by
  unfold cj
  rw [Units.val_mul, Units.val_mul, DG_coe, DG_inv_coe, mul_diagonal, diagonal_mul]
theorem entry_back (d : Fin n → Kˣ) (g : GL (Fin n) K) (a b : Fin n) :
    (g : Matrix (Fin n) (Fin n) K) a b = ((d a : Kˣ) : K) *
      ((cj d g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) a b * (((d b)⁻¹ : Kˣ) : K) := by
  rw [cj_apply]
  have h1 : ((d a : Kˣ) : K) * (((d a)⁻¹ : Kˣ) : K) = 1 := Units.mul_inv _
  have h2 : ((d b : Kˣ) : K) * (((d b)⁻¹ : Kˣ) : K) = 1 := Units.mul_inv _
  linear_combination (-(g : Matrix (Fin n) (Fin n) K) a b * ((d b : Kˣ) : K) * (((d b)⁻¹ : Kˣ) : K)) * h1
    - (g : Matrix (Fin n) (Fin n) K) a b * h2
theorem isUpUni_cj (d : Fin n → Kˣ) (g : GL (Fin n) K) :
    IsUpUni ((cj d g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ↔
      IsUpUni (g : Matrix (Fin n) (Fin n) K) := by
  constructor
  · intro h
    refine ⟨fun a b hab => ?_, fun a => ?_⟩
    · rw [entry_back d, h.1 hab]; simp
    · rw [entry_back d, h.2 a]; simp
  · intro h
    refine ⟨fun a b hab => ?_, fun a => ?_⟩
    · rw [cj_apply, h.1 hab]; simp
    · rw [cj_apply, h.2 a]; simp
theorem isLowUni_cj (d : Fin n → Kˣ) (g : GL (Fin n) K)
    (h : IsLowUni (g : Matrix (Fin n) (Fin n) K)) :
    IsLowUni ((cj d g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  refine ⟨fun a b hab => ?_, fun a => ?_⟩
  · rw [cj_apply, h.1 hab]; simp
  · rw [cj_apply, h.2 a]; simp
end Diag
section Scale
variable {K : Type} [CommRing K] (R : Subring K) (S : List ℕ) (T c : ℕ → Kˣ)
def dg (b : Fin S.sum) : Kˣ := c (blk S b)
theorem pt_scale :
    pt S (T * c) = pt S T * ((DG (dg S c) : GL (Fin S.sum) K) : Matrix (Fin S.sum) (Fin S.sum) K) := by
  ext a b
  rw [DG_coe, mul_diagonal]
  simp only [pt]
  split_ifs with hb
  · rw [dg, hb, Formalism.DoubleCosetMeasures.P.Phase.blk_revIn S a a.2]; simp
  · simp
theorem mem_lowW_scale {g : GL (Fin S.sum) K} (hg : g ∈ lowW K S T) : g ∈ lowW K S (T * c) := by
  obtain ⟨h1, x, hx, e⟩ := hg
  have hxd : x.det = 1 := isLowUni_det K hx
  refine ⟨h1, ((cj (dg S c) (A5x8.sec_gl x hxd) : GL (Fin S.sum) K) :
    Matrix (Fin S.sum) (Fin S.sum) K), isLowUni_cj _ _ hx, ?_⟩
  rw [pt_scale, ← Matrix.mul_assoc, e]
  unfold cj
  rw [Units.val_mul, Units.val_mul, A5x8.sec_gl_coe]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc ((DG (dg S c) : GL (Fin S.sum) K) : Matrix (Fin S.sum) (Fin S.sum) K),
    ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]
def fm (p : lowW K S T × upUniG K S.sum) : lowW K S (T * c) × upUniG K S.sum :=
  (⟨p.1.1, mem_lowW_scale S T c p.1.2⟩, ⟨cj (dg S c) p.2.1, (isUpUni_cj _ _).2 p.2.2⟩)
variable (hc : ∀ b, ((c b : Kˣ) : K) ∈ R ∧ (((c b)⁻¹ : Kˣ) : K) ∈ R)
end Scale
section Typ
variable {K : Type} [CommRing K] (R : Subring K) {n : ℕ}
theorem latZ_mul_DG (d : Fin n → Kˣ)
    (hd : ∀ b, ((d b : Kˣ) : K) ∈ R ∧ (((d b)⁻¹ : Kˣ) : K) ∈ R) (Z : Matrix (Fin n) (Fin n) K) :
    latZ R Z = latZ R (Z * ((DG d : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
  ext x
  rw [Formalism.DoubleCosetMeasures.P.mem_latZ, Formalism.DoubleCosetMeasures.P.mem_latZ]
  constructor
  · rintro ⟨t, e⟩
    refine ⟨fun b => ⟨_, (hd b).2⟩ * t b, ?_⟩
    rw [← e, ← Matrix.mulVec_mulVec]
    congr 1
    funext b
    rw [DG_coe, mulVec_diagonal, Formalism.DoubleCosetMeasures.P.coeLin_apply, Formalism.DoubleCosetMeasures.P.coeLin_apply]
    simp
  · rintro ⟨t, e⟩
    refine ⟨fun b => ⟨_, (hd b).1⟩ * t b, ?_⟩
    rw [← e, ← Matrix.mulVec_mulVec]
    congr 1
    funext b
    rw [DG_coe, mulVec_diagonal, Formalism.DoubleCosetMeasures.P.coeLin_apply, Formalism.DoubleCosetMeasures.P.coeLin_apply]
    simp
end Typ
section Main
variable {K : Type} [CommRing K] (R : Subring K) (S : List ℕ) (T c : ℕ → Kˣ)
end Main
section Block
variable {K : Type} [CommRing K] (R : Subring K)
end Block
section Det
variable {K : Type} [CommRing K]
end Det
section Top
variable {K : Type} [CommRing K] (R : Subring K)
end Top
end Formalism.FourierDecayAlt.P.KernelScalingBack
namespace Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.KernelScalingBack
end Formalism.FourierDecayAlt.P


