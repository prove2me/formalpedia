-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_PHFlProdLinear
-- name    : GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_PHFlProdLinear
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T09:03:47.02755+00:00
-- url     : https://prove2.me/theorems/4ef93953-af45-4a50-8c65-1f46f1c97bab
-- title:
--   PHFl Prod Linear
-- statement:
--   Definitions and structural lemmas for PHFl Prod Linear, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/PHFlProdLinear.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_StatementsFlagGrassSteps
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PRFormula
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PThmAExpand
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagRAux_I_snoc_triv_8bf95163c347
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagRAux_hermZpow_neg_one_a_9c1e838b59b3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagRAux_hermZpow_neg_one_h_d58c8ac90aed
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_DiagRAux_isSmoothHerm_tensor_0936e44f2d46
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_fam_snoc_zpow_be457e2d980a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_fam_update_eq_snoc_8276b4e1bae1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_isSmoothHerm_hermZpow_47ad9a4aea08
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_isSmoothHerm_ofMetrics_fs_afa86c0133a5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_isSmoothHerm_tensor_ef70dcc84f59
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ofMetrics_fs_h_bd4ac42ff7dd
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_fsHerm_h_2fda21fa2b8a

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
namespace GroundTheory.Heights₂.Heights.LowerBoundFree
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
namespace FlagHeightMultilinear
section FS
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
theorem isSmoothHerm_fsHerm (a : K → ℤ) : IsSmoothHerm (fsHerm ι a) := by
  have h := Inter.isSmoothHerm_ofMetrics_fs (ι := ι) a
  unfold IsSmoothHerm at h ⊢
  refine h.congr fun z _ => ?_
  rw [fsHerm_h, Inter.ofMetrics_fs_h]
  unfold refNorm
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [← sq_rpow_half (Real.sqrt_nonneg _) (a k),
    Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
theorem refNorm_mul {a b : K → ℤ} {z : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    refNorm a z * refNorm b z = refNorm (a + b) z := by
  unfold refNorm
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  obtain ⟨i, hi⟩ := hz k
  have hpos : 0 < ∑ i, ‖z ⟨k, i⟩‖ ^ 2 :=
    Finset.sum_pos' (fun j _ => sq_nonneg ‖z ⟨k, j⟩‖) ⟨i, Finset.mem_univ _, pow_pos (norm_pos_iff.mpr hi) 2⟩
  rw [← Real.rpow_add hpos]
  congr 1
  simp only [Pi.add_apply, Int.cast_add]
  ring
variable {I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ} {P : Ideal (MRing ι)} {n : ℕ}
theorem I_snoc_congr (hI : IsIntersectionFamily I) (hP : IsArithVar P (n + 1)) (L : Fin n → HermLine ι)
    (hL : ∀ j, IsSmoothHerm (L j)) {A B : HermLine ι} (hA : IsSmoothHerm A) (hB : IsSmoothHerm B)
    (ha : A.a = B.a) (hh : ∀ z ∈ mcPts P, A.h z = B.h z) :
    I P (n + 1) (Fin.snoc L A) = I P (n + 1) (Fin.snoc L B) := by
  have hBi := Inter.isSmoothHerm_hermZpow hB (-1)
  have h0 := Inter.DiagRAux.I_snoc_triv hI hP hL (Inter.isSmoothHerm_tensor hA hBi)
    (by
      show A.a + (Inter.hermZpow B (-1)).a = 0
      rw [Inter.DiagRAux.hermZpow_neg_one_a, ha, add_neg_cancel])
    (fun z hz => by
      show A.h z * (Inter.hermZpow B (-1)).h z = 1
      rw [Inter.DiagRAux.hermZpow_neg_one_h, hh z hz, mul_inv_cancel₀ (B.pos z hz.1).ne'])
  have h1 := hI.2.1 P n L A (Inter.hermZpow B (-1)) hP hL hA hBi
  have h2 := Inter.fam_snoc_zpow hI hP L hL hB (-1)
  rw [h0, h2] at h1
  push_cast at h1
  linarith
theorem I_snoc_fsHerm_add (hI : IsIntersectionFamily I) (hP : IsArithVar P (n + 1)) (L : Fin n → HermLine ι)
    (hL : ∀ j, IsSmoothHerm (L j)) (a b : K → ℤ) :
    I P (n + 1) (Fin.snoc L (fsHerm ι (a + b))) =
      I P (n + 1) (Fin.snoc L (fsHerm ι a)) + I P (n + 1) (Fin.snoc L (fsHerm ι b)) := by
  rw [← hI.2.1 P n L _ _ hP hL (isSmoothHerm_fsHerm a) (isSmoothHerm_fsHerm b)]
  exact I_snoc_congr hI hP L hL (isSmoothHerm_fsHerm _)
    (Inter.isSmoothHerm_tensor (isSmoothHerm_fsHerm a) (isSmoothHerm_fsHerm b)) rfl
    (fun z hz => (refNorm_mul hz.1).symm)
theorem I_update_fsHerm_add (hI : IsIntersectionFamily I) (hP : IsArithVar P (n + 1))
    (v : Fin (n + 1) → K → ℤ) (j : Fin (n + 1)) (a b : K → ℤ) :
    I P (n + 1) (fun i => fsHerm ι (Function.update v j (a + b) i)) =
      I P (n + 1) (fun i => fsHerm ι (Function.update v j a i)) +
        I P (n + 1) (fun i => fsHerm ι (Function.update v j b i)) := by
  have hL : ∀ i, IsSmoothHerm (fsHerm ι (v i)) := fun i => isSmoothHerm_fsHerm _
  have e : ∀ c : K → ℤ, (fun i => fsHerm ι (Function.update v j c i)) =
      Function.update (fun i => fsHerm ι (v i)) j (fsHerm ι c) := by
    intro c
    funext i
    rcases eq_or_ne i j with rfl | h
    · simp
    · simp [Function.update_of_ne h]
  rw [e, e, e, Inter.fam_update_eq_snoc hI hP _ hL j (isSmoothHerm_fsHerm _),
    Inter.fam_update_eq_snoc hI hP _ hL j (isSmoothHerm_fsHerm _),
    Inter.fam_update_eq_snoc hI hP _ hL j (isSmoothHerm_fsHerm _)]
  exact I_snoc_fsHerm_add hI hP _ (fun i => hL _) a b
def fsMultilin (hI : IsIntersectionFamily I) (hP : IsArithVar P (n + 1)) :
    MultilinearMap ℤ (fun _ : Fin (n + 1) => K → ℤ) ℝ where
  toFun v := I P (n + 1) (fun i => fsHerm ι (v i))
  map_update_add' := by
    intro inst v j a b
    have e : inst = instDecidableEqFin (n + 1) := Subsingleton.elim _ _
    subst e
    exact I_update_fsHerm_add hI hP v j a b
  map_update_smul' := by
    intro inst v j c a
    have e : inst = instDecidableEqFin (n + 1) := Subsingleton.elim _ _
    subst e
    let g : (K → ℤ) →+ ℝ := AddMonoidHom.mk' (fun a => I P (n + 1) (fun i => fsHerm ι (Function.update v j a i)))
      (fun a b => I_update_fsHerm_add hI hP v j a b)
    exact map_zsmul g c a
end FS
variable (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ)
end FlagHeightMultilinear
end GroundTheory.Heights₂.Heights.LowerBoundFree


