-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_SemiTop
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_SemiTop
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T11:01:31.367664+00:00
-- url     : https://prove2.me/theorems/d6984896-fbc2-56bf-b2db-85928b49b28c
-- title:
--   Semi Top
-- statement:
--   Definitions and structural lemmas for Semi Top, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/SemiTop.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_MulInvPiGMemN
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_SemidirectExistsOfParts
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicLocalCompactness_T2SpaceTensorProductFiniteExtension
import Theorems.Thm_P2M_PI_LevelKSplit_W_SemiA_N_le_S__494d858967cb
import Theorems.Thm_PI_LevelKSplit_W_SemiA_H_le_S
import Theorems.Thm_PI_LevelKSplit_W_SemiA_mul_inv_piG_mem_N
import Theorems.Thm_PI_LevelKSplit_W_SemiA_piG_mem_H
import Theorems.Thm_PI_LevelKSplit_W_SemiA_piG_mul
import Theorems.Thm_PI_LevelKSplit_W_SemiA_piG_of_H
import Theorems.Thm_PI_LevelKSplit_W_SemiA_piG_of_N

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.LevelKSplit.W.SemiT
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub PI.LevelKSplit.W.SemiA PI.VolSemiDirect.W
open scoped TensorProduct
section Cont
variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E] {R : Type}
  [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
  {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E} {r : ℕ} {P : Frame E M r} {T : F}
theorem piMat_eq (g : HA R σ J) :
    piMat (P := P) (T := T) g = LinearMap.toMatrix' (datR R σ J P T).pU +
      LinearMap.toMatrix' (datR R σ J P T).pW *
        ((HA.mat R σ J g : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) *
          LinearMap.toMatrix' (datR R σ J P T).pW := by
  rw [piMat, PI.LevelKSplit.W.SemiG.Dat.Pi, map_add, LinearMap.toMatrix'_comp,
    LinearMap.toMatrix'_comp, lin, ← Matrix.toLin'_apply', LinearMap.toMatrix'_toLin', Matrix.mul_assoc]
theorem continuous_piMat : Continuous fun g : HA R σ J => piMat (P := P) (T := T) g := by
  have hm : Continuous fun g : HA R σ J =>
      ((HA.mat R σ J g : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) :=
    Units.continuous_val.comp continuous_subtype_val
  have he : (fun g : HA R σ J => piMat (P := P) (T := T) g) = fun g =>
      LinearMap.toMatrix' (datR R σ J P T).pU + LinearMap.toMatrix' (datR R σ J P T).pW *
        ((HA.mat R σ J g : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) *
          LinearMap.toMatrix' (datR R σ J P T).pW := funext piMat_eq
  rw [he]
  exact continuous_const.add ((continuous_const.matrix_mul hm).matrix_mul continuous_const)
theorem continuous_piMat_inv : Continuous fun g : HA R σ J => piMat (P := P) (T := T) g⁻¹ := by
  exact (continuous_piMat (P := P) (T := T)).comp continuous_inv
variable (R) in

def fwdM (hP : P.IsStd σ J T) (p : Nsub R σ J P × Hsub R σ J P) : Ssub R σ J P :=
  ⟨(p.1 : HA R σ J) * (p.2 : HA R σ J), (Ssub R σ J P).mul_mem (N_le_S' (R := R) hP p.1.2) (H_le_S p.2.2)⟩
theorem continuous_fwdM (hP : P.IsStd σ J T) : Continuous (fwdM R hP) := by
  apply continuous_induced_rng.2
  exact (continuous_subtype_val.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd)
variable (hσσ : ∀ x, σ (σ x) = x) (hJ : IsHermND σ J) (hP : P.IsStd σ J T)
include hσσ hJ hP
theorem continuous_piG : Continuous fun s : Ssub R σ J P => piG hσσ hJ hP (s : HA R σ J) s.2 := by
  apply continuous_induced_rng.2
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · exact (continuous_piMat (P := P) (T := T)).comp continuous_subtype_val
  · exact (continuous_piMat_inv (P := P) (T := T)).comp continuous_subtype_val
variable (R) in

def bwdM (s : Ssub R σ J P) : Nsub R σ J P × Hsub R σ J P :=
  (⟨(s : HA R σ J) * (piG (R := R) hσσ hJ hP (s : HA R σ J) s.2)⁻¹, mul_inv_piG_mem_N hσσ hJ hP s.2⟩,
    ⟨piG (R := R) hσσ hJ hP (s : HA R σ J) s.2, piG_mem_H hσσ hJ hP (s : HA R σ J) s.2⟩)
theorem continuous_bwdM : Continuous (bwdM R hσσ hJ hP) := by
  have hpi := continuous_piG (R := R) hσσ hJ hP
  refine Continuous.prodMk ?_ ?_
  · apply continuous_induced_rng.2
    exact continuous_subtype_val.mul hpi.inv
  · apply continuous_induced_rng.2
    exact hpi
theorem bwd_fwd : Function.LeftInverse (bwdM R hσσ hJ hP) (fwdM R hP) := by
  rintro ⟨n, h⟩
  have hnS := N_le_S' (R := R) hP n.2
  have hhS := H_le_S (R := R) h.2
  have key : piG (R := R) hσσ hJ hP ((n : HA R σ J) * (h : HA R σ J))
      ((Ssub R σ J P).mul_mem hnS hhS) = h := by
    rw [piG_mul hσσ hJ hP hnS hhS, piG_of_N hσσ hJ hP n.2 hnS, piG_of_H hσσ hJ hP h.2 hhS, one_mul]
  refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
  · show (n : HA R σ J) * (h : HA R σ J) *
      (piG (R := R) hσσ hJ hP ((n : HA R σ J) * (h : HA R σ J)) _)⁻¹ = n
    rw [key, mul_inv_cancel_right]
  · exact key
theorem fwd_bwd : Function.RightInverse (bwdM R hσσ hJ hP) (fwdM R hP) := by
  intro s
  apply Subtype.ext
  exact inv_mul_cancel_right _ _
variable (R) in

def homeoNH : (Nsub R σ J P × Hsub R σ J P) ≃ₜ Ssub R σ J P where
  toFun := fwdM R hP
  invFun := bwdM R hσσ hJ hP
  left_inv := bwd_fwd hσσ hJ hP
  right_inv := fwd_bwd hσσ hJ hP
  continuous_toFun := continuous_fwdM hP
  continuous_invFun := continuous_bwdM (R := R) hσσ hJ hP
end Cont
end PI.LevelKSplit.W.SemiT


