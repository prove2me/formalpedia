-- Prove2me | solution 1 for AlgebraicCurve.NodeAnnulusEngine.ord_residue_smul_eq_sInf_dominantIndices_of_ringEquiv_uvCrossingModel
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/c1a578d5-5178-5c35-b770-5de07238f54c

import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_ModularCurve_UVCrossingModel
import Definitions.Def_ModularCurve_UVCrossingGaussOrder
import Definitions.Def_ModularCurve_UVCrossingDominantIndices
import Theorems.Thm_ModularCurve_UVCrossingModel_existsUnique_normalForm
import Theorems.Thm_ModularCurve_UVCrossingModel_sSup_dominantIndices_eq_neg_of_sub_mul_V_pow_mem
import Theorems.Thm_ModularCurve_UVCrossingModel_sInf_dominantIndices_eq_of_sub_mul_U_pow_mem
import Theorems.Thm_ModularCurve_UVCrossingModel_sInf_dominantIndices_zero_mul_and_sSup_dominantIndices_mul
import Theorems.Thm_ModularCurve_UVCrossingModel_dominantIndices_scale
import Theorems.Thm_IsLocalRing_comap_map_adicCompletion_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_NodeAnnulusEngine_ord_residue_smul_eq_sInf_dominantIndices_of_ringEquiv_uvCrossingModel

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_NodeAnnulusEngine_ord_residue_smul_eq_sInf_dominantIndices_of_ringEquiv_uvCrossingModel.AlgebraicCurve IsLocalRing ModularCurve~UVCrossingModel.repGaussOrder_normalForm_eq_iInf_termOrder P2MW.S_AlgebraicCurve_NodeAnnulusEngine_ord_residue_smul_eq_sInf_dominantIndices_of_ringEquiv_uvCrossingModel.ModularCurve ModularCurve.UVCrossingModel~repGaussOrder_normalForm_eq_iInf_termOrder P2MW.S_AlgebraicCurve_NodeAnnulusEngine_ord_residue_smul_eq_sInf_dominantIndices_of_ringEquiv_uvCrossingModel.ModularCurve.UVCrossingModel"

universe u

namespace ModularCurve
p2m_export "ModularCurve" "uvCrossingIdeal UVCrossingModel UVCrossingModel.existsUnique_normalForm UVCrossingModel.sSup_dominantIndices_eq_neg_of_sub_mul_V_pow_mem UVCrossingModel.sInf_dominantIndices_eq_of_sub_mul_U_pow_mem UVCrossingModel.sInf_dominantIndices_zero_mul_and_sSup_dominantIndices_mul UVCrossingModel.dominantIndices_scale"
namespace UVCrossingModel
p2m_export "ModularCurve.UVCrossingModel" "mk U V const constHom_apply S inU inV coeff_inU coeff_inV annulusWeight repGaussOrder repGaussOrder_le le_repGaussOrder_iff nfCoeff nfExponent termOrder dominantIndices existsUnique_normalForm sSup_dominantIndices_eq_neg_of_sub_mul_V_pow_mem sInf_dominantIndices_eq_of_sub_mul_U_pow_mem sInf_dominantIndices_zero_mul_and_sSup_dominantIndices_mul dominantIndices_scale"
p2m_open "ModularCurve.UVCrossingModel~repGaussOrder_normalForm_eq_iInf_termOrder ModularCurve~UVCrossingModel.repGaussOrder_normalForm_eq_iInf_termOrder"

variable {W : Type u} [CommRing W]

@[scoped simp] theorem nfCoeff_negSucc (ab : PowerSeries W × PowerSeries W) (j : ℕ) :
    nfCoeff ab (Int.negSucc j) = PowerSeries.coeff (j + 1) ab.2 := rfl
@[scoped simp] theorem nfCoeff_natCast (ab : PowerSeries W × PowerSeries W) (i : ℕ) :
    nfCoeff ab (i : ℤ) = PowerSeries.coeff i ab.1 := rfl
omit [CommRing W] in
@[scoped simp] theorem nfExponent_negSucc (j : ℕ) : nfExponent (Int.negSucc j) = Finsupp.single 1 (j + 1) := rfl
omit [CommRing W] in
@[scoped simp] theorem nfExponent_natCast (i : ℕ) : nfExponent (i : ℤ) = Finsupp.single 0 i := rfl

theorem coeff_inU_add_inV (a b : PowerSeries W) (d : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff d (inU a + inV b) =
      (if d 1 = 0 then PowerSeries.coeff (d 0) a else 0) + (if d 0 = 0 then PowerSeries.coeff (d 1) b else 0) := by
  rw [map_add, coeff_inU, coeff_inV]

theorem coeff_nfExponent (ab : PowerSeries W × PowerSeries W) (hb : PowerSeries.constantCoeff ab.2 = 0) (n : ℤ) :
    MvPowerSeries.coeff (nfExponent n) (inU ab.1 + inV ab.2) = nfCoeff ab n := by
  cases n with
  | ofNat i =>
    rw [Int.ofNat_eq_natCast, nfExponent_natCast, nfCoeff_natCast, coeff_inU_add_inV]
    simp only [Finsupp.single_apply, Fin.one_eq_zero_iff, OfNat.ofNat_ne_one, if_false, if_true]
    by_cases hi : i = 0
    · subst hi; simp [hb]
    · simp [hi]
  | negSucc j =>
    rw [nfExponent_negSucc, nfCoeff_negSucc, coeff_inU_add_inV]
    simp [Finsupp.single_apply]

theorem termOrder_natCast (v : W → ℕ∞) (E t : ℕ) (ab : PowerSeries W × PowerSeries W) (i : ℕ) :
    termOrder v E t ab (i : ℤ) = v (PowerSeries.coeff i ab.1) + ((i * t : ℕ) : ℕ∞) := by
  simp [termOrder, annulusWeight]

theorem termOrder_negSucc (v : W → ℕ∞) (E t : ℕ) (ab : PowerSeries W × PowerSeries W) (j : ℕ) :
    termOrder v E t ab (Int.negSucc j) = v (PowerSeries.coeff (j + 1) ab.2) + (((j + 1) * (E - t) : ℕ) : ℕ∞) := by
  simp [termOrder, annulusWeight]

theorem repGaussOrder_normalForm_eq_iInf_termOrder
    (v : W → ℕ∞) (hv0 : v 0 = ⊤) (E t : ℕ) (ab : PowerSeries W × PowerSeries W)
    (hb : PowerSeries.constantCoeff ab.2 = 0) :
    repGaussOrder v E t (inU ab.1 + inV ab.2) = ⨅ n : ℤ, termOrder v E t ab n := by
  apply le_antisymm
  · refine le_iInf fun n => ?_
    have := repGaussOrder_le v E t (inU ab.1 + inV ab.2) (nfExponent n)
    rwa [coeff_nfExponent ab hb n] at this
  · rw [le_repGaussOrder_iff]
    intro d
    by_cases h0 : d 0 = 0 <;> by_cases h1 : d 1 = 0
    · have hd : d = nfExponent ((0 : ℕ) : ℤ) := by
        rw [nfExponent_natCast]; ext k; fin_cases k <;> simp [h0, h1]
      rw [hd, coeff_nfExponent ab hb]
      exact iInf_le _ _
    · obtain ⟨j, hj⟩ : ∃ j, d 1 = j + 1 := Nat.exists_eq_succ_of_ne_zero h1
      have hd : d = nfExponent (Int.negSucc j) := by
        rw [nfExponent_negSucc]; ext k; fin_cases k <;> simp [h0, hj]
      rw [hd, coeff_nfExponent ab hb]
      exact iInf_le _ _
    · obtain ⟨i, hi⟩ : ∃ i, d 0 = i + 1 := Nat.exists_eq_succ_of_ne_zero h0
      have hd : d = nfExponent ((i + 1 : ℕ) : ℤ) := by
        rw [nfExponent_natCast]; ext k; fin_cases k <;> simp [h1, hi]
      rw [hd, coeff_nfExponent ab hb]
      exact iInf_le _ _
    · rw [coeff_inU_add_inV, if_neg h1, if_neg h0, add_zero, hv0, top_add]
      exact le_top

theorem termOrder_succ_add (v : W → ℕ∞) (E t : ℕ) (hte : t + 1 ≤ E) (ab : PowerSeries W × PowerSeries W) (n : ℤ) :
    termOrder v E (t + 1) ab n + ((-n).toNat : ℕ∞) = termOrder v E t ab n + (n.toNat : ℕ∞) := by
  cases n with
  | ofNat i =>
    simp only [Int.ofNat_eq_natCast, termOrder_natCast, Int.toNat_natCast]
    have : (-(i : ℤ)).toNat = 0 := by simp
    rw [this, Nat.cast_zero, add_zero, add_assoc, ← Nat.cast_add, Nat.mul_succ]
  | negSucc j =>
    have hn : (-(Int.negSucc j)).toNat = j + 1 := by simp
    rw [termOrder_negSucc, termOrder_negSucc, hn, Int.toNat_negSucc, Nat.cast_zero, add_zero,
      add_assoc, ← Nat.cast_add]
    have h1 : E - t = (E - (t + 1)) + 1 := by omega
    have h2 : (j + 1) * (E - (t + 1)) + (j + 1) = (j + 1) * (E - t) := by rw [h1]; ring
    rw [h2]

theorem mem_dominantIndices_iff (v : W → ℕ∞) (hv0 : v 0 = ⊤) (E t : ℕ) (ab : PowerSeries W × PowerSeries W)
    (hb : PowerSeries.constantCoeff ab.2 = 0) (n : ℤ) :
    n ∈ dominantIndices v E t ab ↔ termOrder v E t ab n = ⨅ m : ℤ, termOrder v E t ab m := by
  rw [dominantIndices, Set.mem_setOf_eq, repGaussOrder_normalForm_eq_iInf_termOrder v hv0 E t ab hb]

theorem dominantIndices_nonempty (v : W → ℕ∞) (hv0 : v 0 = ⊤) (E t : ℕ) (ab : PowerSeries W × PowerSeries W)
    (hb : PowerSeries.constantCoeff ab.2 = 0) : (dominantIndices v E t ab).Nonempty := by
  obtain ⟨n, hn⟩ := ciInf_mem (fun n : ℤ => termOrder v E t ab n)
  exact ⟨n, (mem_dominantIndices_iff v hv0 E t ab hb n).mpr hn⟩

theorem dominantIndices_bddBelow (v : W → ℕ∞) (hv0 : v 0 = ⊤) (E t : ℕ) (hte : t < E)
    (ab : PowerSeries W × PowerSeries W) (hb : PowerSeries.constantCoeff ab.2 = 0)
    (hfin : (⨅ m : ℤ, termOrder v E t ab m) < ⊤) : BddBelow (dominantIndices v E t ab) := by
  obtain ⟨g, hg⟩ := ENat.ne_top_iff_exists.mp hfin.ne
  refine ⟨-(g : ℤ) - 1, fun n hn => ?_⟩
  rw [mem_dominantIndices_iff v hv0 E t ab hb] at hn
  by_contra hlt
  push Not at hlt
  obtain ⟨j, rfl⟩ : ∃ j : ℕ, n = Int.negSucc j := Int.eq_negSucc_of_lt_zero (by omega)
  have hj : g + 1 ≤ j + 1 := by
    have : (Int.negSucc j : ℤ) = -(j : ℤ) - 1 := by rw [Int.negSucc_eq]; ring
    omega
  have h1 : (((j + 1) * (E - t) : ℕ) : ℕ∞) ≤ termOrder v E t ab (Int.negSucc j) := by
    rw [termOrder_negSucc]; exact le_add_self
  rw [hn, ← hg] at h1
  have : (j + 1) * (E - t) ≤ g := by exact_mod_cast h1
  have het : 1 ≤ E - t := by omega
  nlinarith

theorem dominantIndices_bddAbove (v : W → ℕ∞) (hv0 : v 0 = ⊤) (E t : ℕ) (ht0 : 0 < t)
    (ab : PowerSeries W × PowerSeries W) (hb : PowerSeries.constantCoeff ab.2 = 0)
    (hfin : (⨅ m : ℤ, termOrder v E t ab m) < ⊤) : BddAbove (dominantIndices v E t ab) := by
  obtain ⟨g, hg⟩ := ENat.ne_top_iff_exists.mp hfin.ne
  refine ⟨(g : ℤ), fun n hn => ?_⟩
  rw [mem_dominantIndices_iff v hv0 E t ab hb] at hn
  by_contra hlt
  push Not at hlt
  obtain ⟨i, rfl⟩ : ∃ i : ℕ, n = (i : ℤ) := ⟨n.toNat, (Int.toNat_of_nonneg (by omega)).symm⟩
  have hi : g + 1 ≤ i := by omega
  have h1 : ((i * t : ℕ) : ℕ∞) ≤ termOrder v E t ab i := by rw [termOrder_natCast]; exact le_add_self
  rw [hn, ← hg] at h1
  have : i * t ≤ g := by exact_mod_cast h1
  nlinarith

theorem iInf_termOrder_lt_top (v : W → ℕ∞) (hv : ∀ c, v c = ⊤ → c = 0) (π : W) (E t : ℕ)
    (ab : PowerSeries W × PowerSeries W) (hb : PowerSeries.constantCoeff ab.2 = 0)
    (hx : mk π (inU ab.1 + inV ab.2) ≠ 0) : (⨅ n : ℤ, termOrder v E t ab n) < ⊤ := by
  rw [lt_top_iff_ne_top]
  intro htop
  apply hx
  have hall : ∀ n, termOrder v E t ab n = ⊤ := fun n => top_le_iff.mp (htop ▸ iInf_le _ n)
  have hcoef : ∀ n, nfCoeff ab n = 0 := fun n => by
    apply hv
    have := hall n
    rw [termOrder] at this
    exact (WithTop.add_eq_top.mp this).resolve_right (ENat.coe_ne_top _)
  have ha : ab.1 = 0 := by
    ext i; simpa using hcoef (i : ℤ)
  have hb' : ab.2 = 0 := by
    ext j
    cases j with
    | zero => simpa using hb
    | succ j => simpa using hcoef (Int.negSucc j)
  have h0 : inU ab.1 + inV ab.2 = 0 := by
    ext d; rw [coeff_inU_add_inV, ha, hb']; simp
  rw [h0, map_zero]

theorem mem_dominantIndices_iff_forall_le (v : W → ℕ∞) (hv0 : v 0 = ⊤) (E t : ℕ)
    (ab : PowerSeries W × PowerSeries W) (hb : PowerSeries.constantCoeff ab.2 = 0) (n : ℤ) :
    n ∈ dominantIndices v E t ab ↔ ∀ m, termOrder v E t ab n ≤ termOrder v E t ab m := by
  rw [mem_dominantIndices_iff v hv0 E t ab hb]
  exact ⟨fun h m => h ▸ iInf_le _ m, fun h => le_antisymm (le_iInf h) (iInf_le _ n)⟩

end ModularCurve.UVCrossingModel
p2m_reactivate "P2MW.S_AlgebraicCurve_NodeAnnulusEngine_ord_residue_smul_eq_sInf_dominantIndices_of_ringEquiv_uvCrossingModel.ModularCurve P2MW.S_AlgebraicCurve_NodeAnnulusEngine_ord_residue_smul_eq_sInf_dominantIndices_of_ringEquiv_uvCrossingModel.ModularCurve.UVCrossingModel"
p2m_reactivate "P2MW.S_AlgebraicCurve_NodeAnnulusEngine_ord_residue_smul_eq_sInf_dominantIndices_of_ringEquiv_uvCrossingModel.ModularCurve"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ord Place.ord_zero RegularProlongation IsCurveOver"
namespace NodeAnnulusEngine
namespace EndReader
namespace Branch
p2m_open "AlgebraicCurve"

variable {W : Type u} [CommRing W]

noncomputable def keepVar (s : Fin 2) : Fin 2 → PowerSeries W :=
  fun i => if i = s then PowerSeries.X else 0

theorem hasSubst_keepVar (s : Fin 2) : MvPowerSeries.HasSubst (keepVar (W := W) s) := by
  apply MvPowerSeries.hasSubst_of_constantCoeff_zero
  intro i
  by_cases h : i = s
  · simp only [keepVar, if_pos h]; exact PowerSeries.constantCoeff_X
  · simp [keepVar, h]

noncomputable def keepHom (s : Fin 2) : MvPowerSeries (Fin 2) W →ₐ[W] PowerSeries W :=
  MvPowerSeries.substAlgHom (hasSubst_keepVar s)

theorem keepHom_X_self (s : Fin 2) : keepHom (W := W) s (MvPowerSeries.X s) = PowerSeries.X := by
  unfold keepHom
  rw [MvPowerSeries.substAlgHom_X]
  simp [keepVar]

theorem keepHom_X_other (s s' : Fin 2) (h : s' ≠ s) : keepHom (W := W) s (MvPowerSeries.X s') = 0 := by
  unfold keepHom
  rw [MvPowerSeries.substAlgHom_X]
  simp [keepVar, h]

theorem keepHom_C (s : Fin 2) (w : W) : keepHom (W := W) s (MvPowerSeries.C w) = PowerSeries.C w := by
  unfold keepHom
  rw [MvPowerSeries.substAlgHom_apply, MvPowerSeries.subst_C]
  rfl

variable [IsLocalRing W]

noncomputable def branchRed₀ (s : Fin 2) : MvPowerSeries (Fin 2) W →+* PowerSeries (ResidueField W) :=
  (PowerSeries.map (residue W)).comp (keepHom s).toRingHom

theorem branchRed₀_X_self (s : Fin 2) : branchRed₀ (W := W) s (MvPowerSeries.X s) = PowerSeries.X := by
  simp [branchRed₀, keepHom_X_self]

theorem branchRed₀_X_other (s s' : Fin 2) (h : s' ≠ s) : branchRed₀ (W := W) s (MvPowerSeries.X s') = 0 := by
  simp [branchRed₀, keepHom_X_other s s' h]

theorem branchRed₀_C (s : Fin 2) (w : W) : branchRed₀ (W := W) s (MvPowerSeries.C w) = PowerSeries.C (residue W w) := by
  simp [branchRed₀, keepHom_C]

theorem branchRed₀_crossing (s : Fin 2) (ϖ : W) (hϖ : ϖ ∈ maximalIdeal W) (e : ℕ) (he : 1 ≤ e) :
    branchRed₀ (W := W) s ((MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W) * MvPowerSeries.X 1 - MvPowerSeries.C (ϖ ^ e)) = 0 := by
  have hres : residue W (ϖ ^ e) = 0 := by
    rw [map_pow, (residue_eq_zero_iff _).mpr hϖ, zero_pow (by omega)]
  rw [map_sub, map_mul, branchRed₀_C, hres, map_zero, sub_zero]
  obtain rfl | rfl : s = 0 ∨ s = 1 := by fin_cases s <;> simp
  · rw [branchRed₀_X_other (W := W) 0 1 (by decide), mul_zero]
  · rw [branchRed₀_X_other (W := W) 1 0 (by decide), zero_mul]

noncomputable def branchRed (s : Fin 2) (ϖ : W) (hϖ : ϖ ∈ maximalIdeal W) (e : ℕ) (he : 1 ≤ e) :
    UVCrossingModel W (ϖ ^ e) →+* PowerSeries (ResidueField W) :=
  Ideal.Quotient.lift (uvCrossingIdeal W (ϖ ^ e)) (branchRed₀ s)
    (fun f hf => by
      rw [uvCrossingIdeal, Ideal.mem_span_singleton] at hf
      obtain ⟨g, rfl⟩ := hf
      rw [map_mul, branchRed₀_crossing s ϖ hϖ e he, zero_mul])

theorem branchRed_mk (s : Fin 2) (ϖ : W) (hϖ : ϖ ∈ maximalIdeal W) (e : ℕ) (he : 1 ≤ e) (F : MvPowerSeries (Fin 2) W) :
    branchRed s ϖ hϖ e he (mk (ϖ ^ e) F) = branchRed₀ s F := rfl

end AlgebraicCurve.NodeAnnulusEngine.EndReader.Branch
p2m_reactivate "P2MW.S_AlgebraicCurve_NodeAnnulusEngine_ord_residue_smul_eq_sInf_dominantIndices_of_ringEquiv_uvCrossingModel.ModularCurve P2MW.S_AlgebraicCurve_NodeAnnulusEngine_ord_residue_smul_eq_sInf_dominantIndices_of_ringEquiv_uvCrossingModel.ModularCurve.UVCrossingModel"
p2m_reactivate "P2MW.S_AlgebraicCurve_NodeAnnulusEngine_ord_residue_smul_eq_sInf_dominantIndices_of_ringEquiv_uvCrossingModel.ModularCurve P2MW.S_AlgebraicCurve_NodeAnnulusEngine_ord_residue_smul_eq_sInf_dominantIndices_of_ringEquiv_uvCrossingModel.ModularCurve.UVCrossingModel"
p2m_reactivate "P2MW.S_AlgebraicCurve_NodeAnnulusEngine_ord_residue_smul_eq_sInf_dominantIndices_of_ringEquiv_uvCrossingModel.ModularCurve P2MW.S_AlgebraicCurve_NodeAnnulusEngine_ord_residue_smul_eq_sInf_dominantIndices_of_ringEquiv_uvCrossingModel.ModularCurve.UVCrossingModel"
p2m_reactivate "P2MW.S_AlgebraicCurve_NodeAnnulusEngine_ord_residue_smul_eq_sInf_dominantIndices_of_ringEquiv_uvCrossingModel.ModularCurve P2MW.S_AlgebraicCurve_NodeAnnulusEngine_ord_residue_smul_eq_sInf_dominantIndices_of_ringEquiv_uvCrossingModel.ModularCurve.UVCrossingModel"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ord Place.ord_zero RegularProlongation IsCurveOver"
namespace NodeAnnulusEngine
namespace EndReader
namespace Branch
p2m_open "AlgebraicCurve"

variable {W : Type u} [CommRing W]

theorem coeff_keepHom (s : Fin 2) (F : MvPowerSeries (Fin 2) W) (n : ℕ) :
    PowerSeries.coeff n (keepHom s F) = MvPowerSeries.coeff (Finsupp.single s n) F := by
  classical
  unfold keepHom
  rw [MvPowerSeries.substAlgHom_apply, PowerSeries.coeff, MvPowerSeries.coeff_subst (hasSubst_keepVar s)]
  rw [finsum_eq_single _ (Finsupp.single s n)]
  have hk : keepVar (W := W) s s = PowerSeries.X := by simp [keepVar]
  ·
    rw [Finsupp.prod_single_index (by simp), hk, smul_eq_mul]
    rw [show (MvPowerSeries.coeff (Finsupp.single () n)) ((PowerSeries.X : PowerSeries W) ^ n) =
      PowerSeries.coeff n ((PowerSeries.X : PowerSeries W) ^ n) from rfl, PowerSeries.coeff_X_pow_self, mul_one]
  · intro d hd

    by_cases hoff : d (if s = 0 then 1 else 0) = 0
    · have hds : d = Finsupp.single s (d s) := by
        ext i
        obtain rfl | rfl : s = 0 ∨ s = 1 := by fin_cases s <;> simp
        all_goals obtain rfl | rfl : i = 0 ∨ i = 1 := by fin_cases i <;> simp
        all_goals simp_all
      have hne : d s ≠ n := fun h => hd (by rw [hds, h])
      have hk : keepVar (W := W) s s = PowerSeries.X := by simp [keepVar]
      rw [hds, Finsupp.prod_single_index (by simp), hk, smul_eq_mul]
      rw [show (MvPowerSeries.coeff (Finsupp.single () n)) ((PowerSeries.X : PowerSeries W) ^ d s) =
        PowerSeries.coeff n ((PowerSeries.X : PowerSeries W) ^ d s) from rfl, PowerSeries.coeff_X_pow,
        if_neg (Ne.symm hne), mul_zero]
    ·
      set t : Fin 2 := if s = 0 then 1 else 0 with ht
      have hts : t ≠ s := by obtain rfl | rfl : s = 0 ∨ s = 1 := by fin_cases s <;> simp
                             all_goals simp [ht]
      have hmem : t ∈ d.support := Finsupp.mem_support_iff.mpr hoff
      have hzero : (d.prod fun i k => keepVar (W := W) s i ^ k) = 0 := by
        rw [Finsupp.prod, Finset.prod_eq_zero hmem]
        simp [keepVar, hts, zero_pow hoff]
      rw [hzero, map_zero, smul_zero]

theorem keepHom_zero_inU_add_inV (a b : PowerSeries W) (hb : PowerSeries.constantCoeff b = 0) :
    keepHom 0 (inU a + inV b) = a := by
  ext n
  rw [coeff_keepHom, map_add, coeff_inU, coeff_inV]
  simp only [Finsupp.single_apply]
  by_cases hn : n = 0
  · subst hn; simp [hb]
  · simp [hn]

theorem keepHom_one_inU_add_inV (a b : PowerSeries W) (hb : PowerSeries.constantCoeff b = 0) :
    keepHom 1 (inU a + inV b) = PowerSeries.C (PowerSeries.constantCoeff a) + b := by
  ext n
  rw [coeff_keepHom, map_add, coeff_inU, coeff_inV, map_add]
  simp only [Finsupp.single_apply]
  by_cases hn : n = 0
  · subst hn; simp [hb]
  · simp [hn, PowerSeries.coeff_C]

variable [IsLocalRing W]

theorem branchRed_zero_normalForm (ϖ : W) (hϖ : ϖ ∈ maximalIdeal W) (e : ℕ) (he : 1 ≤ e)
    (a b : PowerSeries W) (hb : PowerSeries.constantCoeff b = 0) :
    branchRed 0 ϖ hϖ e he (mk (ϖ ^ e) (inU a + inV b)) = PowerSeries.map (residue W) a := by
  rw [branchRed_mk, branchRed₀, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    keepHom_zero_inU_add_inV a b hb]

theorem branchRed_one_normalForm (ϖ : W) (hϖ : ϖ ∈ maximalIdeal W) (e : ℕ) (he : 1 ≤ e)
    (a b : PowerSeries W) (hb : PowerSeries.constantCoeff b = 0) :
    branchRed 1 ϖ hϖ e he (mk (ϖ ^ e) (inU a + inV b)) =
      PowerSeries.C (residue W (PowerSeries.constantCoeff a)) + PowerSeries.map (residue W) b := by
  rw [branchRed_mk, branchRed₀, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    keepHom_one_inU_add_inV a b hb, map_add, PowerSeries.map_C]

end AlgebraicCurve.NodeAnnulusEngine.EndReader.Branch
p2m_reactivate "P2MW.S_AlgebraicCurve_NodeAnnulusEngine_ord_residue_smul_eq_sInf_dominantIndices_of_ringEquiv_uvCrossingModel.ModularCurve P2MW.S_AlgebraicCurve_NodeAnnulusEngine_ord_residue_smul_eq_sInf_dominantIndices_of_ringEquiv_uvCrossingModel.ModularCurve.UVCrossingModel"
p2m_reactivate "P2MW.S_AlgebraicCurve_NodeAnnulusEngine_ord_residue_smul_eq_sInf_dominantIndices_of_ringEquiv_uvCrossingModel.ModularCurve P2MW.S_AlgebraicCurve_NodeAnnulusEngine_ord_residue_smul_eq_sInf_dominantIndices_of_ringEquiv_uvCrossingModel.ModularCurve.UVCrossingModel"
p2m_reactivate "P2MW.S_AlgebraicCurve_NodeAnnulusEngine_ord_residue_smul_eq_sInf_dominantIndices_of_ringEquiv_uvCrossingModel.ModularCurve P2MW.S_AlgebraicCurve_NodeAnnulusEngine_ord_residue_smul_eq_sInf_dominantIndices_of_ringEquiv_uvCrossingModel.ModularCurve.UVCrossingModel"
p2m_reactivate "P2MW.S_AlgebraicCurve_NodeAnnulusEngine_ord_residue_smul_eq_sInf_dominantIndices_of_ringEquiv_uvCrossingModel.ModularCurve P2MW.S_AlgebraicCurve_NodeAnnulusEngine_ord_residue_smul_eq_sInf_dominantIndices_of_ringEquiv_uvCrossingModel.ModularCurve.UVCrossingModel"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ord Place.ord_zero RegularProlongation IsCurveOver"
namespace NodeAnnulusEngine
namespace EndReader
namespace Branch
p2m_open "AlgebraicCurve"

variable {W : Type u} [CommRing W]

theorem inU_C_mul (w : W) (a : PowerSeries W) : inU (PowerSeries.C w * a) = MvPowerSeries.C w * inU a := by
  ext d; rw [coeff_inU, MvPowerSeries.coeff_C_mul, coeff_inU]; split_ifs <;> simp [PowerSeries.coeff_C_mul]

theorem inV_C_mul (w : W) (b : PowerSeries W) : inV (PowerSeries.C w * b) = MvPowerSeries.C w * inV b := by
  ext d; rw [coeff_inV, MvPowerSeries.coeff_C_mul, coeff_inV]; split_ifs <;> simp [PowerSeries.coeff_C_mul]

theorem mk_C_mul (π w : W) (F : MvPowerSeries (Fin 2) W) : mk π (MvPowerSeries.C w * F) = const π w * mk π F := by
  rw [map_mul]; rfl

theorem exists_eq_C_mul_of_forall_dvd (w : W) (a : PowerSeries W) (h : ∀ i, w ∣ PowerSeries.coeff i a) :
    ∃ a' : PowerSeries W, a = PowerSeries.C w * a' := by
  choose c hc using h
  refine ⟨PowerSeries.mk c, ?_⟩
  ext i
  rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_mk, hc i]

variable [IsDomain W] [IsDiscreteValuationRing W]

theorem varpi_mem (ϖ : W) (hϖ : Irreducible ϖ) : ϖ ∈ maximalIdeal W :=
  (Irreducible.maximalIdeal_eq hϖ) ▸ Ideal.mem_span_singleton_self ϖ

theorem residue_eq_zero_iff_dvd (ϖ : W) (hϖ : Irreducible ϖ) (w : W) : residue W w = 0 ↔ ϖ ∣ w := by
  rw [residue_eq_zero_iff, Irreducible.maximalIdeal_eq hϖ, Ideal.mem_span_singleton]

theorem exists_eq_const_mul_of_branchRed_eq_zero [IsAdicComplete (maximalIdeal W) W]
    (ϖ : W) (hϖ : Irreducible ϖ) (e : ℕ) (he : 1 ≤ e) (y : UVCrossingModel W (ϖ ^ e))
    (h0 : branchRed 0 ϖ (varpi_mem ϖ hϖ) e he y = 0)
    (h1 : branchRed 1 ϖ (varpi_mem ϖ hϖ) e he y = 0) :
    ∃ y' : UVCrossingModel W (ϖ ^ e), y = const (ϖ ^ e) ϖ * y' := by
  haveI : IsAdicComplete (Ideal.span {ϖ}) W :=
    (Irreducible.maximalIdeal_eq hϖ) ▸ (inferInstance : IsAdicComplete (maximalIdeal W) W)
  obtain ⟨⟨a, b⟩, ⟨hb, rfl⟩, -⟩ := ModularCurve.UVCrossingModel.existsUnique_normalForm ϖ e he y
  simp only at hb h0 h1 ⊢
  rw [branchRed_zero_normalForm _ _ _ _ a b hb] at h0
  rw [branchRed_one_normalForm _ _ _ _ a b hb] at h1
  have ha : ∀ i, ϖ ∣ PowerSeries.coeff i a := fun i => by
    rw [← residue_eq_zero_iff_dvd ϖ hϖ]
    have := congrArg (PowerSeries.coeff i) h0
    rwa [PowerSeries.coeff_map, map_zero] at this
  have hbd : ∀ j, ϖ ∣ PowerSeries.coeff j b := fun j => by
    by_cases hj : j = 0
    · subst hj; rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply] at hb; rw [hb]; exact dvd_zero _
    rw [← residue_eq_zero_iff_dvd ϖ hϖ]
    have := congrArg (PowerSeries.coeff j) h1
    rwa [map_add, PowerSeries.coeff_map, PowerSeries.coeff_C, if_neg hj, zero_add, map_zero] at this
  obtain ⟨a', rfl⟩ := exists_eq_C_mul_of_forall_dvd ϖ a ha
  obtain ⟨b', rfl⟩ := exists_eq_C_mul_of_forall_dvd ϖ b hbd
  refine ⟨mk (ϖ ^ e) (inU a' + inV b'), ?_⟩
  rw [inU_C_mul, inV_C_mul, ← mul_add, mk_C_mul]

theorem branchRed_const (s : Fin 2) (ϖ : W) (hϖm : ϖ ∈ maximalIdeal W) (e : ℕ) (he : 1 ≤ e) (w : W) :
    branchRed s ϖ hϖm e he (const (ϖ ^ e) w) = PowerSeries.C (residue W w) := by
  change branchRed s ϖ hϖm e he (mk (ϖ ^ e) (MvPowerSeries.C w)) = _
  rw [branchRed_mk, branchRed₀_C]

end AlgebraicCurve.NodeAnnulusEngine.EndReader.Branch
p2m_reactivate "P2MW.S_AlgebraicCurve_NodeAnnulusEngine_ord_residue_smul_eq_sInf_dominantIndices_of_ringEquiv_uvCrossingModel.ModularCurve P2MW.S_AlgebraicCurve_NodeAnnulusEngine_ord_residue_smul_eq_sInf_dominantIndices_of_ringEquiv_uvCrossingModel.ModularCurve.UVCrossingModel"
p2m_reactivate "P2MW.S_AlgebraicCurve_NodeAnnulusEngine_ord_residue_smul_eq_sInf_dominantIndices_of_ringEquiv_uvCrossingModel.ModularCurve P2MW.S_AlgebraicCurve_NodeAnnulusEngine_ord_residue_smul_eq_sInf_dominantIndices_of_ringEquiv_uvCrossingModel.ModularCurve.UVCrossingModel"
p2m_reactivate "P2MW.S_AlgebraicCurve_NodeAnnulusEngine_ord_residue_smul_eq_sInf_dominantIndices_of_ringEquiv_uvCrossingModel.ModularCurve P2MW.S_AlgebraicCurve_NodeAnnulusEngine_ord_residue_smul_eq_sInf_dominantIndices_of_ringEquiv_uvCrossingModel.ModularCurve.UVCrossingModel"
p2m_reactivate "P2MW.S_AlgebraicCurve_NodeAnnulusEngine_ord_residue_smul_eq_sInf_dominantIndices_of_ringEquiv_uvCrossingModel.ModularCurve P2MW.S_AlgebraicCurve_NodeAnnulusEngine_ord_residue_smul_eq_sInf_dominantIndices_of_ringEquiv_uvCrossingModel.ModularCurve.UVCrossingModel"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.ord Place.ord_zero RegularProlongation IsCurveOver"
namespace NodeAnnulusEngine
namespace EndReader
p2m_open "AlgebraicCurve"

open Branch

section Helpers

theorem vsub_inv_mem {F : Type*} [Field F] (O : ValuationSubring F) {f : F} (hf : f ∈ O)
    (hu : IsUnit (⟨f, hf⟩ : O)) : f⁻¹ ∈ O :=
  O.mem_of_valuation_le_one _ (by
    rw [map_inv₀, show O.valuation f = 1 from (O.valuation_eq_one_iff ⟨f, hf⟩).mp hu, inv_one])

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

theorem isUnit_iff_ord_eq_zero {f : F} (hf : f ∈ v.toValuationSubring) (hf0 : f ≠ 0) :
    IsUnit (⟨f, hf⟩ : v.toValuationSubring) ↔ v.ord f = 0 := by
  rw [← v.adicValuation_coe_eq_one_iff ⟨f, hf⟩]
  simp only [Place.ord]
  constructor
  · intro h
    rw [h, WithZero.log_one, neg_zero]
  · intro h
    have hne := v.adicValuation_ne_zero hf0
    have hlog : WithZero.log (v.adicValuation f) = 0 := by omega
    rw [← WithZero.exp_log hne, hlog, WithZero.exp_zero]

theorem ord_pow (f : F) (n : ℕ) : v.ord (f ^ n) = n * v.ord f := by
  have := v.ord_zpow f (n : ℤ)
  rwa [zpow_natCast] at this

end Helpers
p2m_reactivate "P2MW.S_AlgebraicCurve_NodeAnnulusEngine_ord_residue_smul_eq_sInf_dominantIndices_of_ringEquiv_uvCrossingModel.ModularCurve P2MW.S_AlgebraicCurve_NodeAnnulusEngine_ord_residue_smul_eq_sInf_dominantIndices_of_ringEquiv_uvCrossingModel.ModularCurve.UVCrossingModel"

section OneEnd

variable {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
  {Fb : Type*} [Field Fb] [Algebra (ResidueField A) Fb]
  (R : RegularProlongation A F Fb) (xk : Place (ResidueField A) Fb)
  (B : Subring F) [IsLocalRing ↥B] [IsNoetherianRing ↥B]
  (hBR : ∀ f : F, f ∈ B → f ∈ R.integers)
  {W : Type*} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W]
  (π : W) (hπ : Irreducible π) (E : ℕ) (hE : 1 ≤ E)
  (ι : AdicCompletion (maximalIdeal ↥B) ↥B ≃+* UVCrossingModel W (π ^ E))
  (s : Fin 2) (Uu Vv : UVCrossingModel W (π ^ E))

omit hπ in
theorem order_map_unit (hϖm : π ∈ maximalIdeal W) {γ : UVCrossingModel W (π ^ E)} (hγ : IsUnit γ) :
    (branchRed s π hϖm E hE γ).order = 0 := by
  have hu : IsUnit (branchRed s π hϖm E hE γ) := hγ.map _
  rw [PowerSeries.isUnit_iff_constantCoeff] at hu
  show (branchRed s π hϖm E hE γ).order = ((0 : ℕ) : ℕ∞)
  rw [PowerSeries.order_eq_nat]
  refine ⟨?_, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  rw [PowerSeries.coeff_zero_eq_constantCoeff]
  exact hu.ne_zero

def incl : ↥B →+* ↥R.integers where
  toFun f := ⟨(f : F), hBR f f.2⟩
  map_one' := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl
  map_zero' := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl

theorem incl_apply (f : ↥B) : incl R B hBR f = ⟨(f : F), hBR f f.2⟩ := rfl

variable
  (hΘU : branchRed s π (varpi_mem π hπ) E hE Uu = 0)
  (hΘV : branchRed s π (varpi_mem π hπ) E hE Vv = PowerSeries.X)
  (hres : ∀ (f : ↥B) (n : ℕ), R.residue ⟨f, hBR f f.2⟩ ≠ 0 →
      xk.ord (R.residue ⟨f, hBR f f.2⟩) = (n : ℤ) →
        ∃ γ : UVCrossingModel W (π ^ E), IsUnit γ ∧
          ι (algebraMap ↥B _ f) - γ * Vv ^ n ∈ Ideal.span {const (π ^ E) π, Uu})
  (yy : F) (hyy : yy ∈ B) (hyy1 : xk.ord (R.residue ⟨yy, hBR yy hyy⟩) = 1)

include hΘU hΘV hres hyy1

theorem theta_eq_zero_of_mem {z : UVCrossingModel W (π ^ E)} (hz : z ∈ Ideal.span {const (π ^ E) π, Uu}) :
    branchRed s π (varpi_mem π hπ) E hE z = 0 := by
  rw [Ideal.mem_span_pair] at hz
  obtain ⟨a, b, rfl⟩ := hz
  rw [map_add, map_mul, map_mul, branchRed_const, hΘU, mul_zero, add_zero,
    (residue_eq_zero_iff _).mpr (varpi_mem π hπ), map_zero, mul_zero]

theorem theta_read (f : ↥B) (n : ℕ) (h0 : R.residue ⟨f, hBR f f.2⟩ ≠ 0)
    (hn : xk.ord (R.residue ⟨f, hBR f f.2⟩) = (n : ℤ)) :
    ∃ γ : UVCrossingModel W (π ^ E), IsUnit γ ∧
      branchRed s π (varpi_mem π hπ) E hE (ι (algebraMap ↥B _ f)) =
        branchRed s π (varpi_mem π hπ) E hE γ * PowerSeries.X ^ n := by
  obtain ⟨γ, hγ, hmem⟩ := hres f n h0 hn
  refine ⟨γ, hγ, ?_⟩
  have := theta_eq_zero_of_mem R xk B hBR π hπ E hE ι s Uu Vv hΘU hΘV hres yy hyy hyy1 hmem
  rw [map_sub, map_mul, map_pow, hΘV, sub_eq_zero] at this
  exact this

theorem order_theta_read (f : ↥B) (n : ℕ) (h0 : R.residue ⟨f, hBR f f.2⟩ ≠ 0)
    (hn : xk.ord (R.residue ⟨f, hBR f f.2⟩) = (n : ℤ)) :
    (branchRed s π (varpi_mem π hπ) E hE (ι (algebraMap ↥B _ f))).order = n := by
  obtain ⟨γ, hγ, h⟩ := theta_read R xk B hBR π hπ E hE ι s Uu Vv hΘU hΘV hres yy hyy hyy1 f n h0 hn
  rw [h, PowerSeries.order_mul, order_map_unit π E hE s (varpi_mem π hπ) hγ, PowerSeries.order_X_pow, zero_add]

theorem residue_probe_ne_zero : R.residue ⟨yy, hBR yy hyy⟩ ≠ 0 := by
  intro h0
  rw [h0, Place.ord_zero] at hyy1
  exact zero_ne_one hyy1

theorem order_theta_probe_pow (m : ℕ) :
    (branchRed s π (varpi_mem π hπ) E hE (ι (algebraMap ↥B _ ((⟨yy, hyy⟩ : ↥B) ^ m)))).order = m := by
  have h0 : R.residue ⟨(((⟨yy, hyy⟩ : ↥B) ^ m : ↥B) : F), hBR _ ((⟨yy, hyy⟩ : ↥B) ^ m).2⟩ ≠ 0 ∧
      xk.ord (R.residue ⟨(((⟨yy, hyy⟩ : ↥B) ^ m : ↥B) : F), hBR _ ((⟨yy, hyy⟩ : ↥B) ^ m).2⟩) = (m : ℤ) := by
    have : R.residue ⟨(((⟨yy, hyy⟩ : ↥B) ^ m : ↥B) : F), hBR _ ((⟨yy, hyy⟩ : ↥B) ^ m).2⟩ =
        R.residue ⟨yy, hBR yy hyy⟩ ^ m := by
      rw [← map_pow]; congr 1
    rw [this]
    refine ⟨pow_ne_zero _ (residue_probe_ne_zero R xk B hBR π hπ E hE ι s Uu Vv hΘU hΘV hres yy hyy hyy1), ?_⟩
    rw [ord_pow, hyy1, mul_one]
  exact order_theta_read R xk B hBR π hπ E hE ι s Uu Vv hΘU hΘV hres yy hyy hyy1 _ m h0.1 h0.2

theorem ord_residue_nonneg (t : ↥B) (h0 : R.residue ⟨t, hBR t t.2⟩ ≠ 0) :
    0 ≤ xk.ord (R.residue ⟨t, hBR t t.2⟩) := by
  by_contra hneg
  push Not at hneg
  set m : ℕ := (-xk.ord (R.residue ⟨t, hBR t t.2⟩)).toNat with hm
  have hm' : (m : ℤ) = -xk.ord (R.residue ⟨t, hBR t t.2⟩) := by rw [hm]; omega
  have hm1 : 1 ≤ m := by omega

  set t' : ↥B := (⟨yy, hyy⟩ : ↥B) ^ m * t with ht'
  have hres' : R.residue ⟨t', hBR t' t'.2⟩ = R.residue ⟨yy, hBR yy hyy⟩ ^ m * R.residue ⟨t, hBR t t.2⟩ := by
    rw [← map_pow, ← map_mul]; congr 1
  have h0' : R.residue ⟨t', hBR t' t'.2⟩ ≠ 0 := by
    rw [hres']; exact mul_ne_zero (pow_ne_zero _ (residue_probe_ne_zero R xk B hBR π hπ E hE ι s Uu Vv hΘU hΘV hres yy hyy hyy1)) h0
  have hord' : xk.ord (R.residue ⟨t', hBR t' t'.2⟩) = ((0 : ℕ) : ℤ) := by
    rw [hres', xk.ord_mul (pow_ne_zero _ (residue_probe_ne_zero R xk B hBR π hπ E hE ι s Uu Vv hΘU hΘV hres yy hyy hyy1)) h0, ord_pow, hyy1]
    push_cast; omega
  have h1 := order_theta_read R xk B hBR π hπ E hE ι s Uu Vv hΘU hΘV hres yy hyy hyy1 t' 0 h0' hord'

  have h2 : branchRed s π (varpi_mem π hπ) E hE (ι (algebraMap ↥B _ t')) =
      branchRed s π (varpi_mem π hπ) E hE (ι (algebraMap ↥B _ ((⟨yy, hyy⟩ : ↥B) ^ m))) *
        branchRed s π (varpi_mem π hπ) E hE (ι (algebraMap ↥B _ t)) := by
    rw [ht', map_mul, map_mul, map_mul]
  rw [h2, PowerSeries.order_mul, order_theta_probe_pow R xk B hBR π hπ E hE ι s Uu Vv hΘU hΘV hres yy hyy hyy1 m]
    at h1
  have : ((m : ℕ) : ℕ∞) ≤ 0 := by
    calc ((m : ℕ) : ℕ∞) ≤ (m : ℕ∞) + (branchRed s π (varpi_mem π hπ) E hE (ι (algebraMap ↥B _ t))).order :=
          le_self_add
      _ = ((0 : ℕ) : ℕ∞) := h1
  have : m = 0 := by exact_mod_cast nonpos_iff_eq_zero.mp this
  omega

theorem theta_eq_zero_of_residue_eq_zero (p : ↥B) (hp : R.residue ⟨p, hBR p p.2⟩ = 0) :
    branchRed s π (varpi_mem π hπ) E hE (ι (algebraMap ↥B _ p)) = 0 := by
  by_contra hne

  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (mt PowerSeries.order_eq_top.mp hne)

  set p' : ↥B := p + (⟨yy, hyy⟩ : ↥B) ^ (n + 1) with hp'
  have hres' : R.residue ⟨p', hBR p' p'.2⟩ = R.residue ⟨yy, hBR yy hyy⟩ ^ (n + 1) := by
    have : R.residue ⟨p', hBR p' p'.2⟩ = R.residue ⟨p, hBR p p.2⟩ +
        R.residue ⟨(((⟨yy, hyy⟩ : ↥B) ^ (n + 1) : ↥B) : F), hBR _ ((⟨yy, hyy⟩ : ↥B) ^ (n+1)).2⟩ := by
      rw [← map_add]; congr 1
    rw [this, hp, zero_add, ← map_pow]; congr 1
  have h0' : R.residue ⟨p', hBR p' p'.2⟩ ≠ 0 := by
    rw [hres']; exact pow_ne_zero _ (residue_probe_ne_zero R xk B hBR π hπ E hE ι s Uu Vv hΘU hΘV hres yy hyy hyy1)
  have hord' : xk.ord (R.residue ⟨p', hBR p' p'.2⟩) = ((n + 1 : ℕ) : ℤ) := by
    rw [hres', ord_pow, hyy1, mul_one]
  have h1 := order_theta_read R xk B hBR π hπ E hE ι s Uu Vv hΘU hΘV hres yy hyy hyy1 p' (n + 1) h0' hord'

  have h2 : branchRed s π (varpi_mem π hπ) E hE (ι (algebraMap ↥B _ p')) =
      branchRed s π (varpi_mem π hπ) E hE (ι (algebraMap ↥B _ p)) +
        branchRed s π (varpi_mem π hπ) E hE (ι (algebraMap ↥B _ ((⟨yy, hyy⟩ : ↥B) ^ (n + 1)))) := by
    rw [hp', map_add, map_add, map_add]
  have hy := order_theta_probe_pow R xk B hBR π hπ E hE ι s Uu Vv hΘU hΘV hres yy hyy hyy1 (n + 1)
  rw [h2, PowerSeries.order_add_of_order_ne _ _ (by rw [← hn, hy]; exact_mod_cast n.succ_ne_self.symm),
    ← hn, hy] at h1
  have : min (n : ℕ∞) ((n + 1 : ℕ) : ℕ∞) = (n : ℕ∞) := min_eq_left (by exact_mod_cast n.le_succ)
  rw [this] at h1
  have : n = n + 1 := by exact_mod_cast h1
  omega

end OneEnd
p2m_reactivate "P2MW.S_AlgebraicCurve_NodeAnnulusEngine_ord_residue_smul_eq_sInf_dominantIndices_of_ringEquiv_uvCrossingModel.ModularCurve P2MW.S_AlgebraicCurve_NodeAnnulusEngine_ord_residue_smul_eq_sInf_dominantIndices_of_ringEquiv_uvCrossingModel.ModularCurve.UVCrossingModel"

section Helpers2

theorem vsub_isUnit_of_inv_mem {F : Type*} [Field F] (O : ValuationSubring F) {f : F} (hf : f ∈ O)
    (hf0 : f ≠ 0) (hi : f⁻¹ ∈ O) : IsUnit (⟨f, hf⟩ : O) :=
  isUnit_iff_exists_inv.mpr ⟨⟨f⁻¹, hi⟩, Subtype.ext (mul_inv_cancel₀ hf0)⟩

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

theorem ord_algebraMap (c : K) : v.ord (algebraMap K F c) = 0 := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  have hc' : algebraMap K F c ≠ 0 := (map_ne_zero _).mpr hc
  apply (isUnit_iff_ord_eq_zero v (v.algebraMap_mem' c) hc').mp
  refine vsub_isUnit_of_inv_mem _ _ hc' ?_
  rw [← map_inv₀]
  exact v.algebraMap_mem' c⁻¹

end Helpers2
p2m_reactivate "P2MW.S_AlgebraicCurve_NodeAnnulusEngine_ord_residue_smul_eq_sInf_dominantIndices_of_ringEquiv_uvCrossingModel.ModularCurve P2MW.S_AlgebraicCurve_NodeAnnulusEngine_ord_residue_smul_eq_sInf_dominantIndices_of_ringEquiv_uvCrossingModel.ModularCurve.UVCrossingModel"

section Quotient

theorem ord_residue_quotient {L F Fb : Type*} [Field L] [Field F] [Algebra L F] (A : ValuationSubring L)
    [Field Fb] [Algebra (ResidueField A) Fb]
    (R : RegularProlongation A F Fb) (xk : Place (ResidueField A) Fb)
    {a b f : F} (ha : a ≠ 0) (hb : b ≠ 0) (hfab : f * b = a) {c d e : L}
    (hca : c • a ∈ R.integers) (hdb : d • b ∈ R.integers) (hef : e • f ∈ R.integers)
    (hca0 : R.residue ⟨c • a, hca⟩ ≠ 0) (hdb0 : R.residue ⟨d • b, hdb⟩ ≠ 0) (hef0 : R.residue ⟨e • f, hef⟩ ≠ 0) :
    xk.ord (R.residue ⟨e • f, hef⟩) = xk.ord (R.residue ⟨c • a, hca⟩) - xk.ord (R.residue ⟨d • b, hdb⟩) := by
  have hf : f ≠ 0 := by
    rintro rfl
    rw [zero_mul] at hfab
    exact ha hfab.symm
  have hc : c ≠ 0 := R.smul_const_ne_zero hca hca0
  have hd : d ≠ 0 := R.smul_const_ne_zero hdb hdb0
  have he : e ≠ 0 := R.smul_const_ne_zero hef hef0
  have he' : algebraMap L F e ≠ 0 := (map_ne_zero _).mpr he
  have hd' : algebraMap L F d ≠ 0 := (map_ne_zero _).mpr hd
  have hκF : algebraMap L F (c / (e * d)) * (d • b) * (e • f) = c • a := by
    simp only [Algebra.smul_def, map_div₀, map_mul]
    field_simp
    rw [← hfab]
    ring
  have huef : IsUnit (⟨e • f, hef⟩ : R.integers) := R.isUnit_of_residue_ne_zero hef0
  have hudb : IsUnit (⟨d • b, hdb⟩ : R.integers) := R.isUnit_of_residue_ne_zero hdb0
  have h1 : e • f ≠ 0 := smul_ne_zero he hf
  have h2 : d • b ≠ 0 := smul_ne_zero hd hb
  have hκmem : algebraMap L F (c / (e * d)) ∈ R.integers := by
    have : algebraMap L F (c / (e * d)) = (c • a) * (e • f)⁻¹ * (d • b)⁻¹ := by
      rw [eq_mul_inv_iff_mul_eq₀ h2, eq_mul_inv_iff_mul_eq₀ h1]
      exact hκF
    rw [this]
    exact mul_mem (mul_mem hca (vsub_inv_mem _ hef huef)) (vsub_inv_mem _ hdb hudb)
  have hκA : c / (e * d) ∈ A := (R.algebraMap_mem_iff _).mp hκmem
  have hprod : (⟨algebraMap L F (c / (e * d)), hκmem⟩ : R.integers) * ⟨d • b, hdb⟩ * ⟨e • f, hef⟩ = ⟨c • a, hca⟩ :=
    Subtype.ext hκF
  have hres := congrArg R.residue hprod
  rw [map_mul, map_mul] at hres
  have hκres : R.residue ⟨algebraMap L F (c / (e * d)), hκmem⟩ =
      algebraMap (ResidueField A) Fb (IsLocalRing.residue A ⟨c / (e * d), hκA⟩) :=
    R.residue_algebraMap ⟨c / (e * d), hκA⟩
  have hκres0 : R.residue ⟨algebraMap L F (c / (e * d)), hκmem⟩ ≠ 0 := by
    intro h0
    rw [h0, zero_mul, zero_mul] at hres
    exact hca0 hres.symm
  have hord := congrArg xk.ord hres
  rw [xk.ord_mul (mul_ne_zero hκres0 hdb0) hef0, xk.ord_mul hκres0 hdb0, hκres, ord_algebraMap] at hord
  omega

end Quotient
p2m_reactivate "P2MW.S_AlgebraicCurve_NodeAnnulusEngine_ord_residue_smul_eq_sInf_dominantIndices_of_ringEquiv_uvCrossingModel.ModularCurve P2MW.S_AlgebraicCurve_NodeAnnulusEngine_ord_residue_smul_eq_sInf_dominantIndices_of_ringEquiv_uvCrossingModel.ModularCurve.UVCrossingModel"

section Mono

variable {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
  {Fb : Type*} [Field Fb] [Algebra (ResidueField A) Fb]
  (R : RegularProlongation A F Fb) (xk : Place (ResidueField A) Fb)
  (B : Subring F)
  (hBR : ∀ f : F, f ∈ B → f ∈ R.integers)
  (yy : F) (hyy : yy ∈ B) (hyres : R.residue ⟨yy, hBR yy hyy⟩ ≠ 0)
  (ϖB : ↥B) (ϖA : ↥A) (hϖAB : algebraMap L F (ϖA : L) = (ϖB : F)) (hϖAm : ϖA ∈ maximalIdeal ↥A)
  (hϖA0 : (ϖA : L) ≠ 0)
  (hrk : ∀ a b : ↥A, a ∈ maximalIdeal ↥A → b ≠ 0 → ∃ n : ℕ, b ∣ a ^ n)
  (hdiv : ∀ p : ↥B, R.residue ⟨p, hBR p p.2⟩ = 0 → ∃ r : ↥B, p * ⟨yy, hyy⟩ = ϖB * r)

include hyres hϖAB hϖAm hϖA0 hrk hdiv in
theorem exists_mul_pow_eq_pow_mul (a : ↥B) (ha : a ≠ 0) :
    ∃ (k : ℕ) (r : ↥B), R.residue ⟨r, hBR r r.2⟩ ≠ 0 ∧ a * ⟨yy, hyy⟩ ^ k = ϖB ^ k * r := by
  have ha0F : (a : F) ≠ 0 := fun h0 => ha (Subtype.ext h0)
  obtain ⟨c, hc, hcne⟩ := R.exists_smul_mem (a : F) ha0F
  have huca : IsUnit (⟨c • (a : F), hc⟩ : R.integers) := R.isUnit_of_residue_ne_zero hcne
  have hc0 : c ≠ 0 := R.smul_const_ne_zero hc hcne
  have hyu : IsUnit (⟨yy, hBR yy hyy⟩ : R.integers) := R.isUnit_of_residue_ne_zero hyres
  have hy0 : yy ≠ 0 := fun h0 => hyres (by
    have : (⟨yy, hBR yy hyy⟩ : R.integers) = 0 := Subtype.ext h0
    rw [this, map_zero])
  have hϖB0 : (ϖB : F) ≠ 0 := by rw [← hϖAB]; exact (map_ne_zero _).mpr hϖA0

  have hca_ne : c • (a : F) ≠ 0 := smul_ne_zero hc0 ha0F
  have hdF : algebraMap L F c⁻¹ = (a : F) * (c • (a : F))⁻¹ := by
    rw [Algebra.smul_def, map_inv₀]
    field_simp
  have hdmem : algebraMap L F c⁻¹ ∈ R.integers := by
    rw [hdF]; exact mul_mem (hBR _ a.2) (vsub_inv_mem _ hc huca)
  have hdA : c⁻¹ ∈ A := (R.algebraMap_mem_iff _).mp hdmem
  have hd0 : (⟨c⁻¹, hdA⟩ : ↥A) ≠ 0 := fun h0 => by
    have := congrArg Subtype.val h0
    simp [hc0] at this

  have key : ∀ (k : ℕ) (r : ↥B), a * ⟨yy, hyy⟩ ^ k = ϖB ^ k * r → ϖA ^ k ∣ (⟨c⁻¹, hdA⟩ : ↥A) := by
    intro k r hk
    have hkF : (a : F) * yy ^ k = (ϖB : F) ^ k * (r : F) := by
      have := congrArg (fun z : ↥B => (z : F)) hk
      simpa using this
    have hq : algebraMap L F (c⁻¹ / (ϖA : L) ^ k) = (r : F) * (yy ^ k)⁻¹ * (c • (a : F))⁻¹ := by
      rw [map_div₀, map_pow, hϖAB, Algebra.smul_def, map_inv₀]
      have hc' : algebraMap L F c ≠ 0 := (map_ne_zero _).mpr hc0
      field_simp
      linear_combination hkF
    have hqmem : algebraMap L F (c⁻¹ / (ϖA : L) ^ k) ∈ R.integers := by
      rw [hq]
      refine mul_mem (mul_mem (hBR _ r.2) ?_) (vsub_inv_mem _ hc huca)
      have : (yy ^ k)⁻¹ = (yy⁻¹) ^ k := by rw [inv_pow]
      rw [this]
      exact pow_mem (vsub_inv_mem _ (hBR yy hyy) hyu) k
    have hqA : c⁻¹ / (ϖA : L) ^ k ∈ A := (R.algebraMap_mem_iff _).mp hqmem
    refine ⟨⟨c⁻¹ / (ϖA : L) ^ k, hqA⟩, Subtype.ext ?_⟩
    change c⁻¹ = (ϖA : L) ^ k * (c⁻¹ / (ϖA : L) ^ k)
    field_simp
  obtain ⟨n₀, hn₀⟩ := hrk ϖA ⟨c⁻¹, hdA⟩ hϖAm hd0

  have iter : ∀ k : ℕ, (∃ j, j ≤ k ∧ ∃ r : ↥B, R.residue ⟨r, hBR r r.2⟩ ≠ 0 ∧ a * ⟨yy, hyy⟩ ^ j = ϖB ^ j * r) ∨
      (∃ r : ↥B, a * ⟨yy, hyy⟩ ^ k = ϖB ^ k * r) := by
    intro k
    induction k with
    | zero => exact Or.inr ⟨a, by simp⟩
    | succ k ih =>
      rcases ih with ⟨j, hj, rest⟩ | ⟨r, hr⟩
      · exact Or.inl ⟨j, by omega, rest⟩
      · by_cases hres0 : R.residue ⟨r, hBR r r.2⟩ = 0
        · obtain ⟨r', hr'⟩ := hdiv r hres0
          refine Or.inr ⟨r', ?_⟩
          calc a * ⟨yy, hyy⟩ ^ (k + 1) = a * ⟨yy, hyy⟩ ^ k * ⟨yy, hyy⟩ := by ring
            _ = ϖB ^ k * r * ⟨yy, hyy⟩ := by rw [hr]
            _ = ϖB ^ k * (ϖB * r') := by rw [mul_assoc, hr']
            _ = ϖB ^ (k + 1) * r' := by ring
        · exact Or.inl ⟨k, Nat.le_succ k, r, hres0, hr⟩
  rcases iter (n₀ + 1) with ⟨j, -, r, h1, h2⟩ | ⟨r, hr⟩
  · exact ⟨j, r, h1, h2⟩
  · exfalso
    have h1 : ϖA ^ (n₀ + 1) ∣ ϖA ^ n₀ := (key (n₀ + 1) r hr).trans hn₀
    have hϖA0' : ϖA ≠ 0 := fun h0 => hϖA0 (by rw [h0]; rfl)
    have hnu : ¬ IsUnit ϖA := (IsLocalRing.mem_maximalIdeal _).mp hϖAm
    have := (pow_dvd_pow_iff hϖA0' hnu).mp h1
    omega

end Mono
p2m_reactivate "P2MW.S_AlgebraicCurve_NodeAnnulusEngine_ord_residue_smul_eq_sInf_dominantIndices_of_ringEquiv_uvCrossingModel.ModularCurve P2MW.S_AlgebraicCurve_NodeAnnulusEngine_ord_residue_smul_eq_sInf_dominantIndices_of_ringEquiv_uvCrossingModel.ModularCurve.UVCrossingModel"

section NFunctional

variable {W : Type*} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W]
  (π : W) (hπ : Irreducible π) (E : ℕ) (hE : 1 ≤ E)

omit [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W] in
theorem inU_C_eq (w : W) : inU (PowerSeries.C w) = (MvPowerSeries.C w : MvPowerSeries (Fin 2) W) := by
  ext d
  rw [coeff_inU, PowerSeries.coeff_C, MvPowerSeries.coeff_C]
  by_cases h1 : d 1 = 0
  · rw [if_pos h1]
    by_cases h0 : d 0 = 0
    · rw [if_pos h0, if_pos]; ext k; fin_cases k <;> simp [h0, h1]
    · rw [if_neg h0, if_neg]; intro h; exact h0 (by rw [h]; simp)
  · rw [if_neg h1, if_neg]; intro h; exact h1 (by rw [h]; simp)

omit [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W] in
theorem inV_zero' : inV (0 : PowerSeries W) = 0 := by ext d; simp [coeff_inV]

omit [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W] in
theorem termOrder_C_zero_natCast (v : W → ℕ∞) (w : W) (E t i : ℕ) :
    termOrder v E t (PowerSeries.C w, 0) (i : ℤ) = v (if i = 0 then w else 0) + ((i * t : ℕ) : ℕ∞) := by
  simp [termOrder, annulusWeight, nfCoeff, nfExponent, PowerSeries.coeff_C]

omit [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W] in
theorem termOrder_C_zero_negSucc (v : W → ℕ∞) (w : W) (E t j : ℕ) :
    termOrder v E t (PowerSeries.C w, 0) (Int.negSucc j) = v 0 + ((((j + 1) * (E - t)) : ℕ) : ℕ∞) := by
  simp [termOrder, annulusWeight, nfCoeff, nfExponent]

omit [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W] in

theorem dominantIndices_C_zero (v : W → ℕ∞) (hv0 : v 0 = ⊤) (w : W) (hw : v w ≠ ⊤) (E t : ℕ) :
    dominantIndices v E t (PowerSeries.C w, 0) = {0} := by
  have hT0 : termOrder v E t (PowerSeries.C w, 0) 0 = v w := by
    have := termOrder_C_zero_natCast v w E t 0
    simpa using this
  have hTtop : ∀ n : ℤ, n ≠ 0 → termOrder v E t (PowerSeries.C w, 0) n = ⊤ := by
    intro n hn
    cases n with
    | ofNat i =>
      have hi : i ≠ 0 := fun h => hn (by simp [h])
      rw [Int.ofNat_eq_natCast, termOrder_C_zero_natCast, if_neg hi, hv0, top_add]
    | negSucc j => rw [termOrder_C_zero_negSucc, hv0, top_add]
  ext n
  rw [mem_dominantIndices_iff_forall_le v hv0 E t (PowerSeries.C w, 0) (by simp), Set.mem_singleton_iff]
  constructor
  · intro h
    by_contra hn
    have := h 0
    rw [hTtop n hn, hT0, top_le_iff] at this
    exact hw this
  · rintro rfl m
    by_cases hm : m = 0
    · rw [hm]
    · rw [hTtop m hm]; exact le_top

noncomputable def nf (X : UVCrossingModel W (π ^ E)) : PowerSeries W × PowerSeries W :=
  haveI : IsAdicComplete (Ideal.span {π}) W := hπ.maximalIdeal_eq ▸ (inferInstance : IsAdicComplete (maximalIdeal W) W)
  (ModularCurve.UVCrossingModel.existsUnique_normalForm π E hE X).exists.choose

theorem nf_spec (X : UVCrossingModel W (π ^ E)) :
    PowerSeries.constantCoeff (nf π hπ E hE X).2 = 0 ∧ mk (π ^ E) (inU (nf π hπ E hE X).1 + inV (nf π hπ E hE X).2) = X := by
  haveI : IsAdicComplete (Ideal.span {π}) W := hπ.maximalIdeal_eq ▸ (inferInstance : IsAdicComplete (maximalIdeal W) W)
  exact (ModularCurve.UVCrossingModel.existsUnique_normalForm π E hE X).exists.choose_spec

theorem nf_unique (X : UVCrossingModel W (π ^ E)) (ab : PowerSeries W × PowerSeries W)
    (hb : PowerSeries.constantCoeff ab.2 = 0) (habx : mk (π ^ E) (inU ab.1 + inV ab.2) = X) :
    ab = nf π hπ E hE X := by
  haveI : IsAdicComplete (Ideal.span {π}) W := hπ.maximalIdeal_eq ▸ (inferInstance : IsAdicComplete (maximalIdeal W) W)
  exact (ModularCurve.UVCrossingModel.existsUnique_normalForm π E hE X).unique ⟨hb, habx⟩ (nf_spec π hπ E hE X)

noncomputable def Nsup (X : UVCrossingModel W (π ^ E)) : ℤ :=
  sSup (dominantIndices (IsDiscreteValuationRing.addVal W) E E (nf π hπ E hE X))

noncomputable def Ninf (X : UVCrossingModel W (π ^ E)) : ℤ :=
  sInf (dominantIndices (IsDiscreteValuationRing.addVal W) E 0 (nf π hπ E hE X))

theorem Nsup_mul (X Y : UVCrossingModel W (π ^ E)) (hX : X ≠ 0) (hY : Y ≠ 0) :
    Nsup π hπ E hE (X * Y) = Nsup π hπ E hE X + Nsup π hπ E hE Y :=
  (ModularCurve.UVCrossingModel.sInf_dominantIndices_zero_mul_and_sSup_dominantIndices_mul π hπ E hE X hX
    (nf π hπ E hE X) (nf_spec π hπ E hE X).1 (nf_spec π hπ E hE X).2 Y hY (nf π hπ E hE Y) (nf_spec π hπ E hE Y).1
    (nf_spec π hπ E hE Y).2 (nf π hπ E hE (X * Y)) (nf_spec π hπ E hE (X * Y)).1 (nf_spec π hπ E hE (X * Y)).2).2

theorem Ninf_mul (X Y : UVCrossingModel W (π ^ E)) (hX : X ≠ 0) (hY : Y ≠ 0) :
    Ninf π hπ E hE (X * Y) = Ninf π hπ E hE X + Ninf π hπ E hE Y :=
  (ModularCurve.UVCrossingModel.sInf_dominantIndices_zero_mul_and_sSup_dominantIndices_mul π hπ E hE X hX
    (nf π hπ E hE X) (nf_spec π hπ E hE X).1 (nf_spec π hπ E hE X).2 Y hY (nf π hπ E hE Y) (nf_spec π hπ E hE Y).1
    (nf_spec π hπ E hE Y).2 (nf π hπ E hE (X * Y)) (nf_spec π hπ E hE (X * Y)).1 (nf_spec π hπ E hE (X * Y)).2).1

theorem nf_const (w : W) : nf π hπ E hE (const (π ^ E) w) = (PowerSeries.C w, 0) :=
  (nf_unique π hπ E hE _ (PowerSeries.C w, 0) (by simp) (by
    simp only
    rw [inU_C_eq, inV_zero', add_zero]; rfl)).symm

theorem Nsup_const (w : W) (hw : w ≠ 0) : Nsup π hπ E hE (const (π ^ E) w) = 0 := by
  rw [Nsup, nf_const, dominantIndices_C_zero _ IsDiscreteValuationRing.addVal_zero w
    (IsDiscreteValuationRing.addVal_eq_top_iff.not.mpr hw)]
  exact csSup_singleton 0

theorem Ninf_const (w : W) (hw : w ≠ 0) : Ninf π hπ E hE (const (π ^ E) w) = 0 := by
  rw [Ninf, nf_const, dominantIndices_C_zero _ IsDiscreteValuationRing.addVal_zero w
    (IsDiscreteValuationRing.addVal_eq_top_iff.not.mpr hw)]
  exact csInf_singleton 0

theorem Nsup_read (X : UVCrossingModel W (π ^ E)) (hX : X ≠ 0) (γ : UVCrossingModel W (π ^ E)) (hγ : IsUnit γ)
    (n : ℕ) (h : X - γ * V (π ^ E) ^ n ∈ Ideal.span {const (π ^ E) π, U (π ^ E)}) :
    Nsup π hπ E hE X = -(n : ℤ) := by
  have := (ModularCurve.UVCrossingModel.sSup_dominantIndices_eq_neg_of_sub_mul_V_pow_mem π hπ E hE 1 le_rfl X hX
    (nf π hπ E hE X) (nf_spec π hπ E hE X).1 (nf_spec π hπ E hE X).2 γ hγ n h).2
  rw [ModularCurve.UVCrossingModel.dominantIndices_scale _ E E 1 le_rfl] at this
  exact this

theorem Ninf_read (X : UVCrossingModel W (π ^ E)) (hX : X ≠ 0) (γ : UVCrossingModel W (π ^ E)) (hγ : IsUnit γ)
    (n : ℕ) (h : X - γ * U (π ^ E) ^ n ∈ Ideal.span {const (π ^ E) π, V (π ^ E)}) :
    Ninf π hπ E hE X = (n : ℤ) := by
  have := (ModularCurve.UVCrossingModel.sInf_dominantIndices_eq_of_sub_mul_U_pow_mem π hπ E hE 1 le_rfl X hX
    (nf π hπ E hE X) (nf_spec π hπ E hE X).1 (nf_spec π hπ E hE X).2 γ hγ n h).2
  have hsc := ModularCurve.UVCrossingModel.dominantIndices_scale (IsDiscreteValuationRing.addVal W) E 0 1 le_rfl
    (nf π hπ E hE X)
  rw [mul_zero] at hsc
  rw [hsc] at this
  exact this

end NFunctional
p2m_reactivate "P2MW.S_AlgebraicCurve_NodeAnnulusEngine_ord_residue_smul_eq_sInf_dominantIndices_of_ringEquiv_uvCrossingModel.ModularCurve P2MW.S_AlgebraicCurve_NodeAnnulusEngine_ord_residue_smul_eq_sInf_dominantIndices_of_ringEquiv_uvCrossingModel.ModularCurve.UVCrossingModel"

section TwoEnds

variable {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
  {Fb₁ : Type*} [Field Fb₁] [Algebra (ResidueField A) Fb₁]
  {Fb₂ : Type*} [Field Fb₂] [Algebra (ResidueField A) Fb₂]
  (R₁ : RegularProlongation A F Fb₁) (R₂ : RegularProlongation A F Fb₂)
  (x₁ : Place (ResidueField A) Fb₁) (x₂ : Place (ResidueField A) Fb₂)
  (B : Subring F) [IsLocalRing ↥B] [IsNoetherianRing ↥B]
  (hBR : ∀ f : F, f ∈ B → f ∈ R₁.integers ∧ f ∈ R₂.integers)
  {W : Type*} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W]
  (π : W) (hπ : Irreducible π) (E : ℕ) (hE : 1 ≤ E)
  (ι : AdicCompletion (maximalIdeal ↥B) ↥B ≃+* UVCrossingModel W (π ^ E))
  (hres₁ : ∀ (f : ↥B) (n : ℕ), R₁.residue ⟨f, (hBR f f.2).1⟩ ≠ 0 →
      x₁.ord (R₁.residue ⟨f, (hBR f f.2).1⟩) = (n : ℤ) →
        ∃ γ : UVCrossingModel W (π ^ E), IsUnit γ ∧
          ι (algebraMap ↥B _ f) - γ * V (π ^ E) ^ n ∈ Ideal.span {const (π ^ E) π, U (π ^ E)})
  (hres₂ : ∀ (f : ↥B) (n : ℕ), R₂.residue ⟨f, (hBR f f.2).2⟩ ≠ 0 →
      x₂.ord (R₂.residue ⟨f, (hBR f f.2).2⟩) = (n : ℤ) →
        ∃ γ : UVCrossingModel W (π ^ E), IsUnit γ ∧
          ι (algebraMap ↥B _ f) - γ * U (π ^ E) ^ n ∈ Ideal.span {const (π ^ E) π, V (π ^ E)})
  (x y : F) (hxmem : x ∈ B) (hymem : y ∈ B)
  (x_fst : R₁.residue ⟨x, (hBR x hxmem).1⟩ = 0)
  (x_snd : x₂.ord (R₂.residue ⟨x, (hBR x hxmem).2⟩) = 1)
  (y_snd : R₂.residue ⟨y, (hBR y hymem).2⟩ = 0)
  (y_fst : x₁.ord (R₁.residue ⟨y, (hBR y hymem).1⟩) = 1)
  (ϖB : ↥B) (hϖB : ι (algebraMap ↥B _ ϖB) = const (π ^ E) π)

omit hπ in
theorem branchRed_one_U (hm : π ∈ maximalIdeal W) : branchRed 1 π hm E hE (U (π ^ E)) = 0 := by
  change branchRed 1 π hm E hE (mk (π ^ E) (MvPowerSeries.X 0)) = 0
  rw [branchRed_mk, branchRed₀_X_other 1 0 (by decide)]

omit hπ in
theorem branchRed_one_V (hm : π ∈ maximalIdeal W) : branchRed 1 π hm E hE (V (π ^ E)) = PowerSeries.X := by
  change branchRed 1 π hm E hE (mk (π ^ E) (MvPowerSeries.X 1)) = _
  rw [branchRed_mk, branchRed₀_X_self]

omit hπ in
theorem branchRed_zero_V (hm : π ∈ maximalIdeal W) : branchRed 0 π hm E hE (V (π ^ E)) = 0 := by
  change branchRed 0 π hm E hE (mk (π ^ E) (MvPowerSeries.X 1)) = 0
  rw [branchRed_mk, branchRed₀_X_other 0 1 (by decide)]

omit hπ in
theorem branchRed_zero_U (hm : π ∈ maximalIdeal W) : branchRed 0 π hm E hE (U (π ^ E)) = PowerSeries.X := by
  change branchRed 0 π hm E hE (mk (π ^ E) (MvPowerSeries.X 0)) = _
  rw [branchRed_mk, branchRed₀_X_self]

include hϖB in

theorem exists_eq_varpi_mul (z : ↥B)
    (h0 : branchRed 0 π (varpi_mem π hπ) E hE (ι (algebraMap ↥B _ z)) = 0)
    (h1 : branchRed 1 π (varpi_mem π hπ) E hE (ι (algebraMap ↥B _ z)) = 0) : ∃ r : ↥B, z = ϖB * r := by
  obtain ⟨z', hz'⟩ := exists_eq_const_mul_of_branchRed_eq_zero π hπ E hE _ h0 h1
  have hmem : algebraMap ↥B (AdicCompletion (maximalIdeal ↥B) ↥B) z ∈
      (Ideal.span {ϖB}).map (algebraMap ↥B (AdicCompletion (maximalIdeal ↥B) ↥B)) := by
    rw [Ideal.map_span, Set.image_singleton]
    refine Ideal.mem_span_singleton'.mpr ⟨ι.symm z', ?_⟩
    apply ι.injective
    rw [map_mul, hϖB, RingEquiv.apply_symm_apply, mul_comm]
    exact hz'.symm
  have hcm := IsLocalRing.comap_map_adicCompletion_eq (Ideal.span {ϖB})
  have hz : z ∈ Ideal.span {ϖB} := by rw [← hcm]; exact Ideal.mem_comap.mpr hmem
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp hz
  exact ⟨r, by rw [← hr, mul_comm]⟩

include hπ hE hres₁ hres₂ x_fst x_snd y_snd y_fst hϖB in

theorem div_step_fst (p : ↥B) (hp : R₁.residue ⟨p, (hBR p p.2).1⟩ = 0) :
    ∃ r : ↥B, p * ⟨y, hymem⟩ = ϖB * r := by
  refine exists_eq_varpi_mul B π hπ E hE ι ϖB hϖB _ ?_ ?_
  ·
    have hy := theta_eq_zero_of_residue_eq_zero R₂ x₂ B (fun f hf => (hBR f hf).2) π hπ E hE ι 0
      (V (π ^ E)) (U (π ^ E)) (branchRed_zero_V π E hE (varpi_mem π hπ)) (branchRed_zero_U π E hE (varpi_mem π hπ))
      hres₂ x hxmem x_snd ⟨y, hymem⟩ y_snd
    rw [map_mul, map_mul, map_mul, hy, mul_zero]
  · have hp' := theta_eq_zero_of_residue_eq_zero R₁ x₁ B (fun f hf => (hBR f hf).1) π hπ E hE ι 1
      (U (π ^ E)) (V (π ^ E)) (branchRed_one_U π E hE (varpi_mem π hπ)) (branchRed_one_V π E hE (varpi_mem π hπ))
      hres₁ y hymem y_fst p hp
    rw [map_mul, map_mul, map_mul, hp', zero_mul]

include hπ hE hres₁ hres₂ x_fst x_snd y_snd y_fst hϖB in

theorem div_step_snd (p : ↥B) (hp : R₂.residue ⟨p, (hBR p p.2).2⟩ = 0) :
    ∃ r : ↥B, p * ⟨x, hxmem⟩ = ϖB * r := by
  refine exists_eq_varpi_mul B π hπ E hE ι ϖB hϖB _ ?_ ?_
  · have hp' := theta_eq_zero_of_residue_eq_zero R₂ x₂ B (fun f hf => (hBR f hf).2) π hπ E hE ι 0
      (V (π ^ E)) (U (π ^ E)) (branchRed_zero_V π E hE (varpi_mem π hπ)) (branchRed_zero_U π E hE (varpi_mem π hπ))
      hres₂ x hxmem x_snd p hp
    rw [map_mul, map_mul, map_mul, hp', zero_mul]
  · have hx := theta_eq_zero_of_residue_eq_zero R₁ x₁ B (fun f hf => (hBR f hf).1) π hπ E hE ι 1
      (U (π ^ E)) (V (π ^ E)) (branchRed_one_U π E hE (varpi_mem π hπ)) (branchRed_one_V π E hE (varpi_mem π hπ))
      hres₁ y hymem y_fst ⟨x, hxmem⟩ x_fst
    rw [map_mul, map_mul, map_mul, hx, mul_zero]

end TwoEnds
p2m_reactivate "P2MW.S_AlgebraicCurve_NodeAnnulusEngine_ord_residue_smul_eq_sInf_dominantIndices_of_ringEquiv_uvCrossingModel.ModularCurve P2MW.S_AlgebraicCurve_NodeAnnulusEngine_ord_residue_smul_eq_sInf_dominantIndices_of_ringEquiv_uvCrossingModel.ModularCurve.UVCrossingModel"

section Assembly

variable {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
  {Fb₁ : Type*} [Field Fb₁] [Algebra (ResidueField A) Fb₁]
  {Fb₂ : Type*} [Field Fb₂] [Algebra (ResidueField A) Fb₂]
  (R₁ : RegularProlongation A F Fb₁) (R₂ : RegularProlongation A F Fb₂)
  (x₁ : Place (ResidueField A) Fb₁) (x₂ : Place (ResidueField A) Fb₂)
  (B : Subring F) [IsLocalRing ↥B] [IsNoetherianRing ↥B]
  (hBR : ∀ f : F, f ∈ B → f ∈ R₁.integers ∧ f ∈ R₂.integers)
  {W : Type*} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W]
  (π : W) (hπ : Irreducible π) (E : ℕ) (hE : 1 ≤ E)
  (ι : AdicCompletion (maximalIdeal ↥B) ↥B ≃+* UVCrossingModel W (π ^ E))
  (hres₁ : ∀ (f : ↥B) (n : ℕ), R₁.residue ⟨f, (hBR f f.2).1⟩ ≠ 0 →
      x₁.ord (R₁.residue ⟨f, (hBR f f.2).1⟩) = (n : ℤ) →
        ∃ γ : UVCrossingModel W (π ^ E), IsUnit γ ∧
          ι (algebraMap ↥B _ f) - γ * V (π ^ E) ^ n ∈ Ideal.span {const (π ^ E) π, U (π ^ E)})
  (hres₂ : ∀ (f : ↥B) (n : ℕ), R₂.residue ⟨f, (hBR f f.2).2⟩ ≠ 0 →
      x₂.ord (R₂.residue ⟨f, (hBR f f.2).2⟩) = (n : ℤ) →
        ∃ γ : UVCrossingModel W (π ^ E), IsUnit γ ∧
          ι (algebraMap ↥B _ f) - γ * U (π ^ E) ^ n ∈ Ideal.span {const (π ^ E) π, V (π ^ E)})
  (x y : F) (hxmem : x ∈ B) (hymem : y ∈ B)
  (x_fst : R₁.residue ⟨x, (hBR x hxmem).1⟩ = 0)
  (x_snd : x₂.ord (R₂.residue ⟨x, (hBR x hxmem).2⟩) = 1)
  (y_snd : R₂.residue ⟨y, (hBR y hymem).2⟩ = 0)
  (y_fst : x₁.ord (R₁.residue ⟨y, (hBR y hymem).1⟩) = 1)
  (ϖB : ↥B) (hϖB : ι (algebraMap ↥B _ ϖB) = const (π ^ E) π)
  (ϖA : ↥A) (hϖAB : algebraMap L F (ϖA : L) = (ϖB : F)) (hϖAm : ϖA ∈ maximalIdeal ↥A) (hϖA0 : (ϖA : L) ≠ 0)
  (hrk : ∀ a b : ↥A, a ∈ maximalIdeal ↥A → b ≠ 0 → ∃ n : ℕ, b ∣ a ^ n)

include hπ hE in
theorem phi_ne_zero (z : ↥B) (hz : z ≠ 0) : ι (algebraMap ↥B (AdicCompletion (maximalIdeal ↥B) ↥B) z) ≠ 0 := by
  intro h0
  apply hz
  have hinj : Function.Injective (algebraMap ↥B (AdicCompletion (maximalIdeal ↥B) ↥B)) := by
    haveI : IsHausdorff (maximalIdeal ↥B) ↥B := inferInstance
    exact AdicCompletion.of_injective (maximalIdeal ↥B) ↥B
  have h1 : algebraMap ↥B (AdicCompletion (maximalIdeal ↥B) ↥B) z = 0 := ι.injective (by rw [h0, map_zero])
  exact hinj (by rw [h1, map_zero])

include hπ hE hres₁ hres₂ x_fst x_snd y_snd y_fst hϖB hϖAB hϖAm hϖA0 hrk in

theorem ord_residue_smul_fst (a : ↥B) (e : L) (h : e • (a : F) ∈ R₁.integers)
    (hne : R₁.residue ⟨e • (a : F), h⟩ ≠ 0)
    (ab : PowerSeries W × PowerSeries W) (hb : PowerSeries.constantCoeff ab.2 = 0)
    (habx : mk (π ^ E) (inU ab.1 + inV ab.2) = ι (algebraMap ↥B _ a)) :
    x₁.ord (R₁.residue ⟨e • (a : F), h⟩) = - sSup (dominantIndices (IsDiscreteValuationRing.addVal W) E E ab) := by
  have hBR₁ : ∀ f : F, f ∈ B → f ∈ R₁.integers := fun f hf => (hBR f hf).1
  have brU := branchRed_one_U π E hE (varpi_mem π hπ)
  have brV := branchRed_one_V π E hE (varpi_mem π hπ)
  have hyres : R₁.residue ⟨y, hBR₁ y hymem⟩ ≠ 0 :=
    residue_probe_ne_zero R₁ x₁ B hBR₁ π hπ E hE ι 1 (U (π ^ E)) (V (π ^ E)) brU brV hres₁ y hymem y_fst
  have hy0 : (⟨y, hymem⟩ : ↥B) ≠ 0 := fun h0 => hyres (by
    have : (⟨y, hBR₁ y hymem⟩ : R₁.integers) = 0 := Subtype.ext (show y = 0 from congrArg Subtype.val h0)
    rw [this, map_zero])
  have ha0 : a ≠ 0 := by
    intro h0; apply hne
    have : (⟨e • (a : F), h⟩ : R₁.integers) = 0 := Subtype.ext (by simp [h0])
    rw [this, map_zero]
  have hϖB0 : ϖB ≠ 0 := fun h0 => hϖA0 (by
    have : (ϖB : F) = 0 := congrArg Subtype.val h0
    rw [← hϖAB] at this
    exact (map_eq_zero _).mp this)

  obtain ⟨k, r, hr0, hk⟩ := exists_mul_pow_eq_pow_mul R₁ B hBR₁ y hymem hyres ϖB ϖA hϖAB hϖAm hϖA0 hrk
    (div_step_fst R₁ R₂ x₁ x₂ B hBR π hπ E hE ι hres₁ hres₂ x y hxmem hymem x_fst x_snd y_snd y_fst ϖB hϖB) a ha0
  have hr0' : r ≠ 0 := fun h0 => hr0 (by
    have : (⟨(r : F), hBR₁ r r.2⟩ : R₁.integers) = 0 := Subtype.ext (show (r : F) = 0 from congrArg Subtype.val h0)
    rw [this, map_zero])

  have hn0 := ord_residue_nonneg R₁ x₁ B hBR₁ π hπ E hE ι 1 (U (π ^ E)) (V (π ^ E)) brU brV hres₁ y hymem y_fst r hr0
  obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le hn0

  have hmodel : ι (algebraMap ↥B _ a) * ι (algebraMap ↥B _ ((⟨y, hymem⟩ : ↥B) ^ k)) =
      const (π ^ E) (π ^ k) * ι (algebraMap ↥B _ r) := by
    have h1 := congrArg (fun z : ↥B => ι (algebraMap ↥B (AdicCompletion (maximalIdeal ↥B) ↥B) z)) hk
    simp only [map_mul] at h1
    have h2 : ι (algebraMap ↥B (AdicCompletion (maximalIdeal ↥B) ↥B) (ϖB ^ k)) = const (π ^ E) (π ^ k) := by
      rw [map_pow, map_pow, hϖB, ← constHom_apply, ← map_pow, constHom_apply]
    rw [h2] at h1
    exact h1

  have hN := congrArg (Nsup π hπ E hE) hmodel
  rw [Nsup_mul π hπ E hE _ _ (phi_ne_zero B π hπ E hE ι a ha0) (phi_ne_zero B π hπ E hE ι _ (pow_ne_zero _ hy0)),
    Nsup_mul π hπ E hE _ _ (fun h0 => ?_) (phi_ne_zero B π hπ E hE ι r hr0')] at hN
  swap
  ·
    have : ι (algebraMap ↥B _ (ϖB ^ k)) = const (π ^ E) (π ^ k) := by
      rw [map_pow, map_pow, hϖB, ← constHom_apply, ← map_pow, constHom_apply]
    exact phi_ne_zero B π hπ E hE ι _ (pow_ne_zero _ hϖB0) (this.trans h0)
  have hyk : R₁.residue ⟨(((⟨y, hymem⟩ : ↥B) ^ k : ↥B) : F), hBR₁ _ ((⟨y, hymem⟩ : ↥B) ^ k).2⟩ =
      R₁.residue ⟨y, hBR₁ y hymem⟩ ^ k := by
    rw [← map_pow]; congr 1
  have hNy : Nsup π hπ E hE (ι (algebraMap ↥B _ ((⟨y, hymem⟩ : ↥B) ^ k))) = -(k : ℤ) := by
    obtain ⟨γ, hγ, hmem⟩ := hres₁ ((⟨y, hymem⟩ : ↥B) ^ k) k (by rw [hyk]; exact pow_ne_zero _ hyres)
      (by rw [hyk, ord_pow, y_fst, mul_one])
    exact Nsup_read π hπ E hE _ (phi_ne_zero B π hπ E hE ι _ (pow_ne_zero _ hy0)) γ hγ k hmem
  have hNr : Nsup π hπ E hE (ι (algebraMap ↥B _ r)) = -(n : ℤ) := by
    obtain ⟨γ, hγ, hmem⟩ := hres₁ r n hr0 hn
    exact Nsup_read π hπ E hE _ (phi_ne_zero B π hπ E hE ι r hr0') γ hγ n hmem
  have hNc : Nsup π hπ E hE (const (π ^ E) (π ^ k)) = 0 := Nsup_const π hπ E hE _ (pow_ne_zero _ hπ.ne_zero)
  rw [hNy, hNr, hNc] at hN

  have hab : sSup (dominantIndices (IsDiscreteValuationRing.addVal W) E E ab) = Nsup π hπ E hE (ι (algebraMap ↥B _ a)) := by
    rw [nf_unique π hπ E hE _ ab hb habx]; rfl
  rw [hab]

  have hkF : (a : F) * y ^ k = ((ϖB : F) ^ k * (r : F)) := by
    have := congrArg (fun z : ↥B => (z : F)) hk
    simpa using this
  have hϖF0 : (ϖB : F) ≠ 0 := fun h0 => hϖB0 (Subtype.ext h0)
  have hc_eq : ((ϖA : L) ^ k)⁻¹ • ((ϖB : F) ^ k * (r : F)) = (r : F) := by
    rw [Algebra.smul_def, map_inv₀, map_pow, hϖAB]
    field_simp
  have hcmem : ((ϖA : L) ^ k)⁻¹ • ((ϖB : F) ^ k * (r : F)) ∈ R₁.integers := by rw [hc_eq]; exact hBR₁ _ r.2
  have hcres : R₁.residue ⟨_, hcmem⟩ = R₁.residue ⟨(r : F), hBR₁ r r.2⟩ := by congr 1; exact Subtype.ext hc_eq
  have hd : (1 : L) • y ^ k ∈ R₁.integers := by rw [one_smul]; exact pow_mem (hBR₁ y hymem) k
  have hdres : R₁.residue ⟨(1 : L) • y ^ k, hd⟩ = R₁.residue ⟨y, hBR₁ y hymem⟩ ^ k := by
    rw [← map_pow]; congr 1; exact Subtype.ext (by simp)
  have ha0F : (a : F) ≠ 0 := fun h0 => ha0 (Subtype.ext h0)
  have hr0F : (r : F) ≠ 0 := fun h0 => hr0' (Subtype.ext h0)
  have hy0F : y ≠ 0 := fun h0 => hy0 (Subtype.ext h0)
  have key := ord_residue_quotient A R₁ x₁ (mul_ne_zero (pow_ne_zero _ hϖF0) hr0F) (pow_ne_zero _ hy0F) hkF
    hcmem hd h (by rw [hcres]; exact hr0) (by rw [hdres]; exact pow_ne_zero _ hyres) hne
  rw [key, hcres, hdres, hn, ord_pow, y_fst]
  omega

include hπ hE hres₁ hres₂ x_fst x_snd y_snd y_fst hϖB hϖAB hϖAm hϖA0 hrk in

theorem ord_residue_smul_snd (a : ↥B) (e : L) (h : e • (a : F) ∈ R₂.integers)
    (hne : R₂.residue ⟨e • (a : F), h⟩ ≠ 0)
    (ab : PowerSeries W × PowerSeries W) (hb : PowerSeries.constantCoeff ab.2 = 0)
    (habx : mk (π ^ E) (inU ab.1 + inV ab.2) = ι (algebraMap ↥B _ a)) :
    x₂.ord (R₂.residue ⟨e • (a : F), h⟩) = sInf (dominantIndices (IsDiscreteValuationRing.addVal W) E 0 ab) := by
  have hBR₂ : ∀ f : F, f ∈ B → f ∈ R₂.integers := fun f hf => (hBR f hf).2
  have brV := branchRed_zero_V π E hE (varpi_mem π hπ)
  have brU := branchRed_zero_U π E hE (varpi_mem π hπ)
  have hxres : R₂.residue ⟨x, hBR₂ x hxmem⟩ ≠ 0 :=
    residue_probe_ne_zero R₂ x₂ B hBR₂ π hπ E hE ι 0 (V (π ^ E)) (U (π ^ E)) brV brU hres₂ x hxmem x_snd
  have hx0 : (⟨x, hxmem⟩ : ↥B) ≠ 0 := fun h0 => hxres (by
    have : (⟨x, hBR₂ x hxmem⟩ : R₂.integers) = 0 := Subtype.ext (show x = 0 from congrArg Subtype.val h0)
    rw [this, map_zero])
  have ha0 : a ≠ 0 := by
    intro h0; apply hne
    have : (⟨e • (a : F), h⟩ : R₂.integers) = 0 := Subtype.ext (by simp [h0])
    rw [this, map_zero]
  have hϖB0 : ϖB ≠ 0 := fun h0 => hϖA0 (by
    have : (ϖB : F) = 0 := congrArg Subtype.val h0
    rw [← hϖAB] at this
    exact (map_eq_zero _).mp this)
  obtain ⟨k, r, hr0, hk⟩ := exists_mul_pow_eq_pow_mul R₂ B hBR₂ x hxmem hxres ϖB ϖA hϖAB hϖAm hϖA0 hrk
    (div_step_snd R₁ R₂ x₁ x₂ B hBR π hπ E hE ι hres₁ hres₂ x y hxmem hymem x_fst x_snd y_snd y_fst ϖB hϖB) a ha0
  have hr0' : r ≠ 0 := fun h0 => hr0 (by
    have : (⟨(r : F), hBR₂ r r.2⟩ : R₂.integers) = 0 := Subtype.ext (show (r : F) = 0 from congrArg Subtype.val h0)
    rw [this, map_zero])
  have hn0 := ord_residue_nonneg R₂ x₂ B hBR₂ π hπ E hE ι 0 (V (π ^ E)) (U (π ^ E)) brV brU hres₂ x hxmem x_snd r hr0
  obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le hn0
  have hmodel : ι (algebraMap ↥B _ a) * ι (algebraMap ↥B _ ((⟨x, hxmem⟩ : ↥B) ^ k)) =
      const (π ^ E) (π ^ k) * ι (algebraMap ↥B _ r) := by
    have h1 := congrArg (fun z : ↥B => ι (algebraMap ↥B (AdicCompletion (maximalIdeal ↥B) ↥B) z)) hk
    simp only [map_mul] at h1
    have h2 : ι (algebraMap ↥B (AdicCompletion (maximalIdeal ↥B) ↥B) (ϖB ^ k)) = const (π ^ E) (π ^ k) := by
      rw [map_pow, map_pow, hϖB, ← constHom_apply, ← map_pow, constHom_apply]
    rw [h2] at h1
    exact h1
  have hN := congrArg (Ninf π hπ E hE) hmodel
  rw [Ninf_mul π hπ E hE _ _ (phi_ne_zero B π hπ E hE ι a ha0) (phi_ne_zero B π hπ E hE ι _ (pow_ne_zero _ hx0)),
    Ninf_mul π hπ E hE _ _ (fun h0 => ?_) (phi_ne_zero B π hπ E hE ι r hr0')] at hN
  swap
  · have : ι (algebraMap ↥B _ (ϖB ^ k)) = const (π ^ E) (π ^ k) := by
      rw [map_pow, map_pow, hϖB, ← constHom_apply, ← map_pow, constHom_apply]
    exact phi_ne_zero B π hπ E hE ι _ (pow_ne_zero _ hϖB0) (this.trans h0)
  have hxk : R₂.residue ⟨(((⟨x, hxmem⟩ : ↥B) ^ k : ↥B) : F), hBR₂ _ ((⟨x, hxmem⟩ : ↥B) ^ k).2⟩ =
      R₂.residue ⟨x, hBR₂ x hxmem⟩ ^ k := by
    rw [← map_pow]; congr 1
  have hNx : Ninf π hπ E hE (ι (algebraMap ↥B _ ((⟨x, hxmem⟩ : ↥B) ^ k))) = (k : ℤ) := by
    obtain ⟨γ, hγ, hmem⟩ := hres₂ ((⟨x, hxmem⟩ : ↥B) ^ k) k (by rw [hxk]; exact pow_ne_zero _ hxres)
      (by rw [hxk, ord_pow, x_snd, mul_one])
    exact Ninf_read π hπ E hE _ (phi_ne_zero B π hπ E hE ι _ (pow_ne_zero _ hx0)) γ hγ k hmem
  have hNr : Ninf π hπ E hE (ι (algebraMap ↥B _ r)) = (n : ℤ) := by
    obtain ⟨γ, hγ, hmem⟩ := hres₂ r n hr0 hn
    exact Ninf_read π hπ E hE _ (phi_ne_zero B π hπ E hE ι r hr0') γ hγ n hmem
  have hNc : Ninf π hπ E hE (const (π ^ E) (π ^ k)) = 0 := Ninf_const π hπ E hE _ (pow_ne_zero _ hπ.ne_zero)
  rw [hNx, hNr, hNc] at hN
  have hab : sInf (dominantIndices (IsDiscreteValuationRing.addVal W) E 0 ab) = Ninf π hπ E hE (ι (algebraMap ↥B _ a)) := by
    rw [nf_unique π hπ E hE _ ab hb habx]; rfl
  rw [hab]
  have hkF : (a : F) * x ^ k = ((ϖB : F) ^ k * (r : F)) := by
    have := congrArg (fun z : ↥B => (z : F)) hk
    simpa using this
  have hϖF0 : (ϖB : F) ≠ 0 := fun h0 => hϖB0 (Subtype.ext h0)
  have hc_eq : ((ϖA : L) ^ k)⁻¹ • ((ϖB : F) ^ k * (r : F)) = (r : F) := by
    rw [Algebra.smul_def, map_inv₀, map_pow, hϖAB]
    field_simp
  have hcmem : ((ϖA : L) ^ k)⁻¹ • ((ϖB : F) ^ k * (r : F)) ∈ R₂.integers := by rw [hc_eq]; exact hBR₂ _ r.2
  have hcres : R₂.residue ⟨_, hcmem⟩ = R₂.residue ⟨(r : F), hBR₂ r r.2⟩ := by congr 1; exact Subtype.ext hc_eq
  have hd : (1 : L) • x ^ k ∈ R₂.integers := by rw [one_smul]; exact pow_mem (hBR₂ x hxmem) k
  have hdres : R₂.residue ⟨(1 : L) • x ^ k, hd⟩ = R₂.residue ⟨x, hBR₂ x hxmem⟩ ^ k := by
    rw [← map_pow]; congr 1; exact Subtype.ext (by simp)
  have hr0F : (r : F) ≠ 0 := fun h0 => hr0' (Subtype.ext h0)
  have hx0F : x ≠ 0 := fun h0 => hx0 (Subtype.ext h0)
  have key := ord_residue_quotient A R₂ x₂ (mul_ne_zero (pow_ne_zero _ hϖF0) hr0F) (pow_ne_zero _ hx0F) hkF
    hcmem hd h (by rw [hcres]; exact hr0) (by rw [hdres]; exact pow_ne_zero _ hxres) hne
  rw [key, hcres, hdres, hn, ord_pow, x_snd]
  omega

end Assembly
p2m_reactivate "P2MW.S_AlgebraicCurve_NodeAnnulusEngine_ord_residue_smul_eq_sInf_dominantIndices_of_ringEquiv_uvCrossingModel.ModularCurve P2MW.S_AlgebraicCurve_NodeAnnulusEngine_ord_residue_smul_eq_sInf_dominantIndices_of_ringEquiv_uvCrossingModel.ModularCurve.UVCrossingModel"

end AlgebraicCurve.NodeAnnulusEngine.EndReader
p2m_reactivate "P2MW.S_AlgebraicCurve_NodeAnnulusEngine_ord_residue_smul_eq_sInf_dominantIndices_of_ringEquiv_uvCrossingModel.ModularCurve P2MW.S_AlgebraicCurve_NodeAnnulusEngine_ord_residue_smul_eq_sInf_dominantIndices_of_ringEquiv_uvCrossingModel.ModularCurve.UVCrossingModel"
p2m_reactivate "P2MW.S_AlgebraicCurve_NodeAnnulusEngine_ord_residue_smul_eq_sInf_dominantIndices_of_ringEquiv_uvCrossingModel.ModularCurve P2MW.S_AlgebraicCurve_NodeAnnulusEngine_ord_residue_smul_eq_sInf_dominantIndices_of_ringEquiv_uvCrossingModel.ModularCurve.UVCrossingModel"
p2m_reactivate "P2MW.S_AlgebraicCurve_NodeAnnulusEngine_ord_residue_smul_eq_sInf_dominantIndices_of_ringEquiv_uvCrossingModel.ModularCurve P2MW.S_AlgebraicCurve_NodeAnnulusEngine_ord_residue_smul_eq_sInf_dominantIndices_of_ringEquiv_uvCrossingModel.ModularCurve.UVCrossingModel"

open AlgebraicCurve.NodeAnnulusEngine.EndReader in
theorem solution
    {L : Type*} [Field L] [IsAlgClosed L] [CharZero L] (A : ValuationSubring L) {F : Type*} [Field F] [Algebra L F]
    [IsCurveOver L F] [Algebra.EssFiniteType L F]
    {Fbar₁ : Type*} [Field Fbar₁] [Algebra (ResidueField A) Fbar₁]
    {Fbar₂ : Type*} [Field Fbar₂] [Algebra (ResidueField A) Fbar₂]
    (R₁ : RegularProlongation A F Fbar₁) (R₂ : RegularProlongation A F Fbar₂)
    (x₁ : Place (ResidueField A) Fbar₁) (x₂ : Place (ResidueField A) Fbar₂)
    (S : Set (Place L F))
    (hrat : ∀ P ∈ S, P.IsRational)
    (𝒩₀ : Subring F) [IsLocalRing ↥𝒩₀] [IsNoetherianRing ↥𝒩₀]
    (h𝒩₀R : ∀ f : F, f ∈ 𝒩₀ → f ∈ R₁.integers ∧ f ∈ R₂.integers)
    (hS : ∀ P : Place L F, P ∈ S ↔
      (∀ f : F, f ∈ 𝒩₀ → f ∈ P.toValuationSubring) ∧
      (∀ f : ↥𝒩₀, ¬ IsUnit f → ∃ h : P.evalAt (f : F) ∈ A, (⟨_, h⟩ : ↥A) ∈ maximalIdeal ↥A))
    (hgen : ∀ f : F, ∃ (n : ℕ) (c : Fin n → L) (a : Fin n → ↥𝒩₀) (b : ↥𝒩₀),
      (b : F) ≠ 0 ∧ f * (b : F) = ∑ i, c i • ((a i : ↥𝒩₀) : F))
    (C : Subring L) (hC : ∀ c : L, c ∈ C → c ∈ A)
    (hCmem : ∀ c : L, c ∈ C → algebraMap L F c ∈ 𝒩₀)
    (ϖ : ↥C)
    (hϖ : ∀ d : ↥C, IsLocalRing.residue A ⟨(d : L), hC d d.2⟩ = 0 ↔ ∃ d' : ↥C, d = ϖ * d')
    (hϖ0 : ((ϖ : ↥C) : L) ≠ 0)
    [IsDomain ↥C] [IsDiscreteValuationRing ↥C]
    (halg : ∀ a : L, a ∈ A → IsAlgebraic ↥C a)
    (hld : ∀ (n : ℕ) (c : Fin n → L) (a : Fin n → ↥𝒩₀), LinearIndependent ↥C c →
      ∑ i, c i • ((a i : ↥𝒩₀) : F) = 0 → ∀ i, a i = 0)
    (hrk : ∀ a b : ↥A, a ∈ maximalIdeal ↥A → b ≠ 0 → ∃ n : ℕ, b ∣ a ^ n)
    (hres : ∀ g : ↥𝒩₀, ∃ o : ↥C, ¬ IsUnit (g - ⟨algebraMap L F (o : L), hCmem o o.2⟩))
    {W : Type*} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W]
    (π : W) (hπ : Irreducible π)
    (σ : W →+* AdicCompletion (maximalIdeal ↥𝒩₀) ↥𝒩₀)
    (hσπ : σ π = algebraMap ↥𝒩₀ (AdicCompletion (maximalIdeal ↥𝒩₀) ↥𝒩₀) ⟨algebraMap L F (ϖ : L), hCmem ϖ ϖ.2⟩)
    (E : ℕ) (hE : 1 ≤ E)
    (ι : AdicCompletion (maximalIdeal ↥𝒩₀) ↥𝒩₀ ≃+* UVCrossingModel W (π ^ E))
    (hconst : ∀ o : W, ι (σ o) = const (π ^ E) o)
    (hres₁ : ∀ (f : ↥𝒩₀) (n : ℕ), R₁.residue ⟨f, (h𝒩₀R f f.2).1⟩ ≠ 0 →
      x₁.ord (R₁.residue ⟨f, (h𝒩₀R f f.2).1⟩) = (n : ℤ) →
        ∃ γ : UVCrossingModel W (π ^ E), IsUnit γ ∧
          ι (algebraMap ↥𝒩₀ _ f) - γ * V (π ^ E) ^ n ∈ Ideal.span {const (π ^ E) π, U (π ^ E)})
    (hres₂ : ∀ (f : ↥𝒩₀) (n : ℕ), R₂.residue ⟨f, (h𝒩₀R f f.2).2⟩ ≠ 0 →
      x₂.ord (R₂.residue ⟨f, (h𝒩₀R f f.2).2⟩) = (n : ℤ) →
        ∃ γ : UVCrossingModel W (π ^ E), IsUnit γ ∧
          ι (algebraMap ↥𝒩₀ _ f) - γ * U (π ^ E) ^ n ∈ Ideal.span {const (π ^ E) π, V (π ^ E)})
    (x y : F) (hxmem : x ∈ 𝒩₀) (hymem : y ∈ 𝒩₀)
    (x_fst : R₁.residue ⟨x, (h𝒩₀R x hxmem).1⟩ = 0)
    (x_snd : x₂.ord (R₂.residue ⟨x, (h𝒩₀R x hxmem).2⟩) = 1)
    (y_snd : R₂.residue ⟨y, (h𝒩₀R y hymem).2⟩ = 0)
    (y_fst : x₁.ord (R₁.residue ⟨y, (h𝒩₀R y hymem).1⟩) = 1)
    (q : ℕ) (hq : 1 ≤ q)
    (a : ↥𝒩₀) (e : L) (h : e • (a : F) ∈ R₂.integers) (hne : R₂.residue ⟨e • (a : F), h⟩ ≠ 0)
    (ab : PowerSeries W × PowerSeries W) (hb : PowerSeries.constantCoeff ab.2 = 0)
    (habx : mk (π ^ E) (inU ab.1 + inV ab.2) = ι (algebraMap ↥𝒩₀ _ a)) :
    x₂.ord (R₂.residue ⟨e • (a : F), h⟩) =
      sInf (dominantIndices (fun w => (q : ℕ∞) * IsDiscreteValuationRing.addVal W w) (q * E) 0 ab) := by
  have hsc := ModularCurve.UVCrossingModel.dominantIndices_scale (IsDiscreteValuationRing.addVal W) E 0 q hq ab
  rw [mul_zero] at hsc
  rw [hsc]
  have hϖB : ι (algebraMap ↥𝒩₀ (AdicCompletion (maximalIdeal ↥𝒩₀) ↥𝒩₀) ⟨algebraMap L F (ϖ : L), hCmem ϖ ϖ.2⟩) =
      const (π ^ E) π := by rw [← hσπ, hconst]
  have hϖAm : (⟨(ϖ : L), hC ϖ ϖ.2⟩ : ↥A) ∈ maximalIdeal ↥A := by
    rw [← IsLocalRing.residue_eq_zero_iff]
    exact (hϖ ϖ).mpr ⟨1, by simp⟩
  exact ord_residue_smul_snd R₁ R₂ x₁ x₂ 𝒩₀ h𝒩₀R π hπ E hE ι hres₁ hres₂ x y hxmem hymem x_fst x_snd y_snd y_fst
    ⟨algebraMap L F (ϖ : L), hCmem ϖ ϖ.2⟩ hϖB ⟨(ϖ : L), hC ϖ ϖ.2⟩ rfl hϖAm hϖ0 hrk a e h hne ab hb habx

end S_AlgebraicCurve_NodeAnnulusEngine_ord_residue_smul_eq_sInf_dominantIndices_of_ringEquiv_uvCrossingModel
end P2MW
export P2MW.S_AlgebraicCurve_NodeAnnulusEngine_ord_residue_smul_eq_sInf_dominantIndices_of_ringEquiv_uvCrossingModel (solution)
