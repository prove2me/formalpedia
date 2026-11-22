-- Prove2me | Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_LayerLadder
-- name    : LeanPool_LowWeightPauliDynamics_Pauli_LayerLadder
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T08:00:08.492519+00:00
-- url     : https://prove2.me/theorems/b9c96299-06da-4b32-bee7-a0c3357a0db5
-- title:
--   Layer Ladder
-- statement:
--   Definitions and structural lemmas for Layer Ladder, from Jue Xu; LeanPool contributors's pinned Low-weight Pauli dynamics and truncation error development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/LayerLadder.lean

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_LayerFlow
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Truncate
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Constants_Entry
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Ladder_MultiJump
public import Theorems.Thm_Lean4LPD_PauliString_cls_fst
public import Theorems.Thm_Lean4LPD_PauliString_cls_herm
public import Theorems.Thm_Lean4LPD_PauliString_cls_snd
public import Theorems.Thm_Lean4LPD_PauliString_coeffVec_apply
public import Theorems.Thm_Lean4LPD_PauliString_coeffVec_layerConj
public import Theorems.Thm_Lean4LPD_PauliString_cover_nil
public import Theorems.Thm_Lean4LPD_PauliString_herm_x
public import Theorems.Thm_Lean4LPD_PauliString_herm_z
public import Theorems.Thm_Lean4LPD_PauliString_highNorm_eq_zero
public import Theorems.Thm_Lean4LPD_PauliString_highNorm_nonneg
public import Theorems.Thm_Lean4LPD_PauliString_jumpAct_apply
public import Theorems.Thm_Lean4LPD_PauliString_jumpAct_zero
public import Theorems.Thm_Lean4LPD_PauliString_layerInflowMatrix_zero
public import Theorems.Thm_Lean4LPD_PauliString_mem_antiLayer
public import Theorems.Thm_Lean4LPD_PauliString_mem_antiSites
public import Theorems.Thm_Lean4LPD_PauliString_mem_highSet
public import Theorems.Thm_Lean4LPD_PauliString_mem_support
public import Theorems.Thm_Lean4LPD_PauliString_norm_coeffVec
public import Theorems.Thm_Lean4LPD_PauliString_norm_layerAct
public import Theorems.Thm_Lean4LPD_PauliString_norm_layerInflowMatrix_clm_le
public import Theorems.Thm_Lean4LPD_PauliString_norm_layerInflowMatrix_clm_le_restr
public import Theorems.Thm_Lean4LPD_PauliString_norm_restr_layerAct_le_sum_inflow
public import Theorems.Thm_Lean4LPD_PauliString_oneLayer_cons
public import Theorems.Thm_Lean4LPD_PauliString_oneLayer_nil
public import Theorems.Thm_Lean4LPD_PauliString_pauliNorm_nonneg
public import Theorems.Thm_Lean4LPD_PauliString_pauliNorm_sq
public import Theorems.Thm_Lean4LPD_PauliString_phaseMul_eq_phaseMul_iff
public import Theorems.Thm_Lean4LPD_PauliString_phaseMul_eq_self_iff
public import Theorems.Thm_Lean4LPD_PauliString_phaseMul_phase
public import Theorems.Thm_Lean4LPD_PauliString_phaseMul_x
public import Theorems.Thm_Lean4LPD_PauliString_phaseMul_z
public import Theorems.Thm_Lean4LPD_PauliString_phaseMul_zero
public import Theorems.Thm_Lean4LPD_PauliString_reachable_cons
public import Theorems.Thm_Lean4LPD_PauliString_reachable_nil
public import Theorems.Thm_Lean4LPD_PauliString_restr_apply
public import Theorems.Thm_Lean4LPD_PauliString_restr_univ
public import Theorems.Thm_Lean4LPD_PauliString_self_mem_branch
public import Theorems.Thm_Lean4LPD_PauliString_site_mul
public import Theorems.Thm_Lean4LPD_PauliString_site_one
public import Theorems.Thm_Lean4LPD_PauliString_site_phaseMul
public import Theorems.Thm_Lean4LPD_PauliString_stayAct_apply
public import Theorems.Thm_Lean4LPD_PauliString_stayAct_zero
public import Theorems.Thm_Lean4LPD_PauliString_support_phaseMul
public import Theorems.Thm_Lean4LPD_PauliString_sympForm_mul_self_right
public import Theorems.Thm_Lean4LPD_PauliString_sympForm_phaseMul_left
public import Theorems.Thm_Lean4LPD_PauliString_sympForm_phaseMul_right
public import Theorems.Thm_Lean4LPD_PauliString_sympForm_self
public import Theorems.Thm_Lean4LPD_PauliString_toMatrix_one
public import Theorems.Thm_Lean4LPD_PauliString_toMatrix_phaseMul
public import Theorems.Thm_Lean4LPD_PauliString_weight_one
public import Theorems.Thm_Lean4LPD_PauliString_weight_phaseMul
public import Theorems.Thm_Lean4LPD_PauliString_wt_cls
public import Theorems.Thm_Lean4LPD_conj_negOnePow
public import Theorems.Thm_Lean4LPD_epsJump_nonneg
public import Theorems.Thm_Lean4LPD_epsJump_ratio
public import Theorems.Thm_Lean4LPD_iPow_signPhase
public import Theorems.Thm_Lean4LPD_iPow_two
public import Theorems.Thm_Lean4LPD_negOnePow_mul_self
public import Theorems.Thm_Lean4LPD_negOnePow_one
public import Theorems.Thm_Lean4LPD_negOnePow_zero
public import Theorems.Thm_Lean4LPD_norm_iPow
public import Theorems.Thm_Lean4LPD_rungW_nonneg
public import Theorems.Thm_Lean4LPD_rungWeight_one
public import Theorems.Thm_Lean4LPD_star_negOnePow
attribute [local simp] Lean4LPD.PauliString.cls_fst
attribute [local simp] Lean4LPD.PauliString.cls_herm
attribute [local simp] Lean4LPD.PauliString.cls_snd
attribute [local simp] Lean4LPD.PauliString.coeffVec_apply
attribute [local simp] Lean4LPD.PauliString.cover_nil
attribute [local simp] Lean4LPD.PauliString.herm_x
attribute [local simp] Lean4LPD.PauliString.herm_z
attribute [local simp] Lean4LPD.PauliString.jumpAct_apply
attribute [local simp] Lean4LPD.PauliString.jumpAct_zero
attribute [local simp] Lean4LPD.PauliString.mem_antiLayer
attribute [local simp] Lean4LPD.PauliString.mem_antiSites
attribute [local simp] Lean4LPD.PauliString.mem_highSet
attribute [local simp] Lean4LPD.PauliString.mem_support
attribute [local simp] Lean4LPD.PauliString.oneLayer_cons
attribute [local simp] Lean4LPD.PauliString.oneLayer_nil
attribute [local simp] Lean4LPD.PauliString.pauliNorm_sq
attribute [local simp] Lean4LPD.PauliString.phaseMul_eq_phaseMul_iff
attribute [local simp] Lean4LPD.PauliString.phaseMul_eq_self_iff
attribute [local simp] Lean4LPD.PauliString.phaseMul_phase
attribute [local simp] Lean4LPD.PauliString.phaseMul_x
attribute [local simp] Lean4LPD.PauliString.phaseMul_z
attribute [local simp] Lean4LPD.PauliString.phaseMul_zero
attribute [local simp] Lean4LPD.PauliString.reachable_cons
attribute [local simp] Lean4LPD.PauliString.reachable_nil
attribute [local simp] Lean4LPD.PauliString.restr_apply
attribute [local simp] Lean4LPD.PauliString.restr_univ
attribute [local simp] Lean4LPD.PauliString.self_mem_branch
attribute [local simp] Lean4LPD.PauliString.site_mul
attribute [local simp] Lean4LPD.PauliString.site_one
attribute [local simp] Lean4LPD.PauliString.site_phaseMul
attribute [local simp] Lean4LPD.PauliString.stayAct_apply
attribute [local simp] Lean4LPD.PauliString.stayAct_zero
attribute [local simp] Lean4LPD.PauliString.support_phaseMul
attribute [local simp] Lean4LPD.PauliString.sympForm_mul_self_right
attribute [local simp] Lean4LPD.PauliString.sympForm_phaseMul_left
attribute [local simp] Lean4LPD.PauliString.sympForm_phaseMul_right
attribute [local simp] Lean4LPD.PauliString.sympForm_self
attribute [local simp] Lean4LPD.PauliString.toMatrix_one
attribute [local simp] Lean4LPD.PauliString.toMatrix_phaseMul
attribute [local simp] Lean4LPD.PauliString.weight_one
attribute [local simp] Lean4LPD.PauliString.weight_phaseMul
attribute [local simp] Lean4LPD.PauliString.wt_cls
attribute [local simp] Lean4LPD.conj_negOnePow
attribute [local simp] Lean4LPD.iPow_signPhase
attribute [local simp] Lean4LPD.iPow_two
attribute [local simp] Lean4LPD.negOnePow_mul_self
attribute [local simp] Lean4LPD.negOnePow_one
attribute [local simp] Lean4LPD.negOnePow_zero
attribute [local simp] Lean4LPD.norm_iPow
attribute [local simp] Lean4LPD.rungWeight_one
attribute [local simp] Lean4LPD.star_negOnePow


set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace Lean4LPD
open Finset
theorem summable_epsJump_tail {kh1 c a : ℝ} (hkh : 0 < kh1) (hc : 0 ≤ c) (ha : 0 ≤ a)
    {m : ℕ} (hm : 1 ≤ m) (hb : betaOf kh1 c a < 1) :
    Summable (fun i : ℕ => epsJump kh1 c a (m + i) m) := by
  have hb0 : 0 ≤ betaOf kh1 c a := by
    have hw := rungW_nonneg hkh hc (m := 2) (by omega)
    unfold betaOf
    positivity
  have hgeom : ∀ i : ℕ, epsJump kh1 c a (m + i) m ≤
      betaOf kh1 c a ^ i * epsJump kh1 c a m m := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      calc
        epsJump kh1 c a (m + (i + 1)) m ≤
            betaOf kh1 c a * epsJump kh1 c a (m + i) m := by
          simpa only [Nat.add_assoc] using epsJump_ratio hkh hc ha hm (Nat.le_add_right m i)
        _ ≤ betaOf kh1 c a * (betaOf kh1 c a ^ i * epsJump kh1 c a m m) :=
          mul_le_mul_of_nonneg_left ih hb0
        _ = betaOf kh1 c a ^ (i + 1) * epsJump kh1 c a m m := by rw [pow_succ]; ring
  exact Summable.of_nonneg_of_le
    (fun i => epsJump_nonneg hkh hc ha _ _ (by omega)) hgeom
    ((summable_geometric_of_lt_one hb0 hb).mul_right _)
theorem sum_Ico_epsJump_le_entryFactor {kh1 c a : ℝ}
    (hkh : 0 < kh1) (hc : 0 ≤ c) (ha : 0 ≤ a) {m : ℕ} (hm : 1 ≤ m)
    (hb : betaOf kh1 c a < 1) (K : ℕ) :
    (∑ j ∈ Ico m K, epsJump kh1 c a j m) ≤ entryFactor kh1 c a m := by
  rw [Finset.sum_Ico_eq_sum_range, entryFactor]
  exact (summable_epsJump_tail hkh hc ha hm hb).sum_le_tsum _
    (fun i _ => epsJump_nonneg hkh hc ha _ _ (by omega))
namespace PauliString
variable {n : ℕ}
theorem rungWeight_cast_eq_rungW {ko kh m : ℕ} (hkh : 2 ≤ kh) (hm : 1 ≤ m) :
    (rungWeight ko kh m : ℝ) = rungW (kh - 1 : ℕ) ((ko : ℝ) / (kh - 1 : ℕ)) m := by
  have hd : ((kh - 1 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (by omega : kh - 1 ≠ 0)
  simp only [rungWeight, Nat.cast_add, Nat.cast_mul, Nat.cast_sub hm, Nat.cast_one, rungW]
  field_simp
  ring
theorem rungWeight_add_jump (ko kh m j : ℕ) (hm : 1 ≤ m) :
    rungWeight ko kh m + j * (kh - 1) = rungWeight ko kh (m + j) := by
  have h : m + j - 1 = (m - 1) + j := by omega
  simp only [rungWeight, h, Nat.add_mul, Nat.add_assoc]
theorem rungWeight_sub_jump (ko kh m j : ℕ) (hj : j < m) :
    rungWeight ko kh (m - j) + j * (kh - 1) = rungWeight ko kh m := by
  have h := rungWeight_add_jump ko kh (m - j) j (by omega)
  simpa only [Nat.sub_add_cancel (Nat.le_of_lt hj)] using h
theorem layer_factor_eq_epsJump {ko kh m : ℕ} (hkh : 2 ≤ kh) (hm : 1 ≤ m)
    (a : ℝ) (j : ℕ) :
    ((((rungWeight ko kh m + j * (kh - 1) : ℕ) : ℝ) * a) ^ j / (Nat.factorial j : ℝ)) =
      epsJump (kh - 1 : ℕ) ((ko : ℝ) / (kh - 1 : ℕ)) a j m := by
  rw [rungWeight_add_jump ko kh m j hm, rungWeight_cast_eq_rungW hkh (by omega), epsJump]
noncomputable def layerTraj (Ls : ℕ → List (PauliString n × ℝ))
    (S : ℕ → Finset (PauliIndex n)) (O : Matrix (Bits n) (Bits n) ℂ) :
    ℕ → Matrix (Bits n) (Bits n) ℂ
  | 0 => O
  | T + 1 => truncOp (S T) (layerConj (Ls T) (layerTraj Ls S O T))
@[simp] theorem layerTraj_zero (Ls : ℕ → List (PauliString n × ℝ))
    (S : ℕ → Finset (PauliIndex n)) (O : Matrix (Bits n) (Bits n) ℂ) :
    layerTraj Ls S O 0 = O := rfl
theorem layerTraj_succ (Ls : ℕ → List (PauliString n × ℝ))
    (S : ℕ → Finset (PauliIndex n)) (O : Matrix (Bits n) (Bits n) ℂ) (T : ℕ) :
    layerTraj Ls S O (T + 1) = truncOp (S T) (layerConj (Ls T) (layerTraj Ls S O T)) := rfl
theorem pauliNorm_layerConj (L : List (PauliString n × ℝ))
    (hL : ∀ g ∈ L, IsSelfAdjoint g.1) (O : Matrix (Bits n) (Bits n) ℂ) :
    pauliNorm (layerConj L O) = pauliNorm O := by
  rw [← norm_coeffVec, coeffVec_layerConj L hL, norm_layerAct L hL, norm_coeffVec]
theorem pauliNorm_layerTraj_le (Ls : ℕ → List (PauliString n × ℝ))
    (hL : ∀ T, ∀ g ∈ Ls T, IsSelfAdjoint g.1) (S : ℕ → Finset (PauliIndex n))
    (O : Matrix (Bits n) (Bits n) ℂ) (T : ℕ) :
    pauliNorm (layerTraj Ls S O T) ≤ pauliNorm O := by
  induction T with
  | zero => exact le_rfl
  | succ T ih =>
    rw [layerTraj_succ]
    exact (pauliNorm_truncOp_le _ _).trans ((pauliNorm_layerConj _ (hL T) _).le.trans ih)
noncomputable def layerN (Ls : ℕ → List (PauliString n × ℝ))
    (S : ℕ → Finset (PauliIndex n)) (O : Matrix (Bits n) (Bits n) ℂ) (ko kh : ℕ) :
    ℕ → ℕ → ℝ
  | 0, T => pauliNorm (layerTraj Ls S O T)
  | m + 1, T => highNorm (rungWeight ko kh (m + 1)) (layerTraj Ls S O T)
theorem layerN_eq_highNorm (Ls : ℕ → List (PauliString n × ℝ))
    (S : ℕ → Finset (PauliIndex n)) (O : Matrix (Bits n) (Bits n) ℂ) (ko kh m T : ℕ)
    (hm : 1 ≤ m) :
    layerN Ls S O ko kh m T = highNorm (rungWeight ko kh m) (layerTraj Ls S O T) := by
  cases m with
  | zero => omega
  | succ m => rfl
theorem layerN_nonneg (Ls : ℕ → List (PauliString n × ℝ))
    (S : ℕ → Finset (PauliIndex n)) (O : Matrix (Bits n) (Bits n) ℂ) (ko kh m T : ℕ) :
    0 ≤ layerN Ls S O ko kh m T := by
  cases m with
  | zero => exact pauliNorm_nonneg _
  | succ m => exact highNorm_nonneg _ _
theorem layerN_init (Ls : ℕ → List (PauliString n × ℝ))
    (S : ℕ → Finset (PauliIndex n)) {O : Matrix (Bits n) (Bits n) ℂ} {ko kh : ℕ}
    (hloc : ∀ p : PauliIndex n, ko < wt p → coeff O p = 0) (m : ℕ) (hm : 1 ≤ m) :
    layerN Ls S O ko kh m 0 = 0 := by
  rw [layerN_eq_highNorm _ _ _ _ _ _ _ hm, layerTraj_zero]
  refine highNorm_eq_zero _ fun p hp => hloc p (lt_of_le_of_lt ?_ hp)
  exact Nat.le_add_right ko ((m - 1) * (kh - 1))
theorem highNorm_layerConj_le_multi (L : List (PauliString n × ℝ)) {ko kh m : ℕ}
    (hkh : 2 ≤ kh) (hL : IsLayer kh (L.map Prod.fst))
    (hherm : ∀ g ∈ L, IsSelfAdjoint g.1) {a : ℝ} (ha : 0 ≤ a)
    (hsin : ∀ g ∈ L, |Real.sin g.2| ≤ a) (hm : 1 ≤ m)
    (hb : betaOf (kh - 1 : ℕ) ((ko : ℝ) / (kh - 1 : ℕ)) a < 1)
    (O : Matrix (Bits n) (Bits n) ℂ) :
    highNorm (rungWeight ko kh m) (layerConj L O) ≤
      highNorm (rungWeight ko kh m) O +
        (∑ j ∈ Ico 1 m, epsJump (kh - 1 : ℕ) ((ko : ℝ) / (kh - 1 : ℕ)) a j m *
          highNorm (rungWeight ko kh (m - j)) O) +
        entryFactor (kh - 1 : ℕ) ((ko : ℝ) / (kh - 1 : ℕ)) a m * pauliNorm O := by
  have hkh1 : (0 : ℝ) < (kh - 1 : ℕ) := by exact_mod_cast (by omega : 0 < kh - 1)
  have hc : 0 ≤ (ko : ℝ) / (kh - 1 : ℕ) := div_nonneg (Nat.cast_nonneg _) hkh1.le
  let f : ℕ → ℝ := fun j =>
    ‖Lean4LPD.clm (layerInflowMatrix L (rungWeight ko kh m) j) (coeffVec O)‖
  have hf0 : f 0 = 0 := by
    simp [f, layerInflowMatrix_zero, Lean4LPD.clm]
  have hfnonneg (j : ℕ) : 0 ≤ f j := norm_nonneg _
  have hsmall (j : ℕ) (hj : j ∈ Ico 1 m) :
      f j ≤ epsJump (kh - 1 : ℕ) ((ko : ℝ) / (kh - 1 : ℕ)) a j m *
        highNorm (rungWeight ko kh (m - j)) O := by
    have hj' := Finset.mem_Ico.1 hj
    have h := norm_layerInflowMatrix_clm_le_restr L hL ha hsin
      (rungWeight_sub_jump ko kh m j hj'.2).le (coeffVec O)
    rw [layer_factor_eq_epsJump hkh hm] at h
    exact h
  have hlarge (j : ℕ) :
      f j ≤ epsJump (kh - 1 : ℕ) ((ko : ℝ) / (kh - 1 : ℕ)) a j m * pauliNorm O := by
    have h := norm_layerInflowMatrix_clm_le L hL ha hsin
      (rungWeight ko kh m) j (coeffVec O)
    rw [layer_factor_eq_epsJump hkh hm, norm_coeffVec] at h
    exact h
  let K := max m (L.length + 1)
  have hmK : m ≤ K := le_max_left _ _
  have hlenK : L.length + 1 ≤ K := le_max_right _ _
  have hsum : (∑ j ∈ range (L.length + 1), f j) ≤
      (∑ j ∈ Ico 1 m, epsJump (kh - 1 : ℕ) ((ko : ℝ) / (kh - 1 : ℕ)) a j m *
        highNorm (rungWeight ko kh (m - j)) O) +
      entryFactor (kh - 1 : ℕ) ((ko : ℝ) / (kh - 1 : ℕ)) a m * pauliNorm O := by
    calc
      (∑ j ∈ range (L.length + 1), f j) ≤ ∑ j ∈ range K, f j :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hlenK)
          (fun j _ _ => hfnonneg j)
      _ = (∑ j ∈ Ico 1 m, f j) + ∑ j ∈ Ico m K, f j := by
        rw [Finset.sum_range_eq_add_Ico f (by omega), hf0, zero_add,
          ← Finset.sum_Ico_consecutive f hm hmK]
      _ ≤ (∑ j ∈ Ico 1 m, epsJump (kh - 1 : ℕ) ((ko : ℝ) / (kh - 1 : ℕ)) a j m *
          highNorm (rungWeight ko kh (m - j)) O) +
          ∑ j ∈ Ico m K, epsJump (kh - 1 : ℕ) ((ko : ℝ) / (kh - 1 : ℕ)) a j m *
            pauliNorm O :=
        add_le_add (Finset.sum_le_sum hsmall) (Finset.sum_le_sum fun j _ => hlarge j)
      _ ≤ _ := by
        rw [← Finset.sum_mul]
        exact add_le_add le_rfl
          (mul_le_mul_of_nonneg_right
            (sum_Ico_epsJump_le_entryFactor hkh1 hc ha hm hb K) (pauliNorm_nonneg O))
  calc
    highNorm (rungWeight ko kh m) (layerConj L O) =
        ‖restr (highSet n (rungWeight ko kh m)) (layerAct L (coeffVec O))‖ := by
      rw [highNorm, coeffVec_layerConj L hherm]
    _ ≤ highNorm (rungWeight ko kh m) O + ∑ j ∈ range (L.length + 1), f j :=
      norm_restr_layerAct_le_sum_inflow L hherm _ _
    _ ≤ _ := by
      have h := add_le_add (le_refl (highNorm (rungWeight ko kh m) O)) hsum
      simpa only [add_assoc] using h
theorem layerN_step (Ls : ℕ → List (PauliString n × ℝ))
    (S : ℕ → Finset (PauliIndex n)) (O : Matrix (Bits n) (Bits n) ℂ) {ko kh : ℕ}
    (hkh : 2 ≤ kh) (hL : ∀ T, IsLayer kh ((Ls T).map Prod.fst))
    (hherm : ∀ T, ∀ g ∈ Ls T, IsSelfAdjoint g.1) {a : ℝ} (ha : 0 ≤ a)
    (hsin : ∀ T, ∀ g ∈ Ls T, |Real.sin g.2| ≤ a)
    (hb : betaOf (kh - 1 : ℕ) ((ko : ℝ) / (kh - 1 : ℕ)) a < 1)
    (m T : ℕ) (hm : 1 ≤ m) :
    layerN Ls S O ko kh m (T + 1) ≤ layerN Ls S O ko kh m T +
      (∑ j ∈ Ico 1 m, epsJump (kh - 1 : ℕ) ((ko : ℝ) / (kh - 1 : ℕ)) a j m *
        layerN Ls S O ko kh (m - j) T) +
      entryFactor (kh - 1 : ℕ) ((ko : ℝ) / (kh - 1 : ℕ)) a m * pauliNorm O := by
  have hkh1 : (0 : ℝ) < (kh - 1 : ℕ) := by exact_mod_cast (by omega : 0 < kh - 1)
  have hc : 0 ≤ (ko : ℝ) / (kh - 1 : ℕ) := div_nonneg (Nat.cast_nonneg _) hkh1.le
  have hE : 0 ≤ entryFactor (kh - 1 : ℕ) ((ko : ℝ) / (kh - 1 : ℕ)) a m :=
    tsum_nonneg fun i => epsJump_nonneg hkh1 hc ha _ _ (by omega)
  rw [layerN_eq_highNorm _ _ _ _ _ _ _ hm, layerTraj_succ]
  have hflow := (highNorm_truncOp_le (rungWeight ko kh m) (S T) _).trans
    (highNorm_layerConj_le_multi (Ls T) hkh (hL T) (hherm T) ha (hsin T) hm hb
      (layerTraj Ls S O T))
  have hsum : (∑ j ∈ Ico 1 m, epsJump (kh - 1 : ℕ) ((ko : ℝ) / (kh - 1 : ℕ)) a j m *
      highNorm (rungWeight ko kh (m - j)) (layerTraj Ls S O T)) =
      ∑ j ∈ Ico 1 m, epsJump (kh - 1 : ℕ) ((ko : ℝ) / (kh - 1 : ℕ)) a j m *
        layerN Ls S O ko kh (m - j) T := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [layerN_eq_highNorm _ _ _ _ _ _ _ (by have := Finset.mem_Ico.1 hj; omega)]
  rw [hsum, ← layerN_eq_highNorm _ _ _ _ _ _ _ hm] at hflow
  exact hflow.trans (add_le_add le_rfl
    (mul_le_mul_of_nonneg_left (pauliNorm_layerTraj_le Ls hherm S O T) hE))
noncomputable def pauliMultiLadder (Ls : ℕ → List (PauliString n × ℝ))
    (S : ℕ → Finset (PauliIndex n)) (O : Matrix (Bits n) (Bits n) ℂ) {ko kh : ℕ}
    (hkh : 2 ≤ kh) (hL : ∀ T, IsLayer kh ((Ls T).map Prod.fst))
    (hherm : ∀ T, ∀ g ∈ Ls T, IsSelfAdjoint g.1) {a : ℝ} (ha : 0 ≤ a)
    (hsin : ∀ T, ∀ g ∈ Ls T, |Real.sin g.2| ≤ a)
    (hb : betaOf (kh - 1 : ℕ) ((ko : ℝ) / (kh - 1 : ℕ)) a < 1)
    (hloc : ∀ p : PauliIndex n, ko < wt p → coeff O p = 0) :
    MultiLadder (epsJump (kh - 1 : ℕ) ((ko : ℝ) / (kh - 1 : ℕ)) a)
      (entryFactor (kh - 1 : ℕ) ((ko : ℝ) / (kh - 1 : ℕ)) a) (pauliNorm O) where
  N := layerN Ls S O ko kh
  nonneg := layerN_nonneg Ls S O ko kh
  init := layerN_init Ls S hloc
  step := layerN_step Ls S O hkh hL hherm ha hsin hb
end PauliString
end Lean4LPD


