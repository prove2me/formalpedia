-- Prove2me | Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Truncate
-- name    : LeanPool_LowWeightPauliDynamics_Pauli_Truncate
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T07:32:49.13104+00:00
-- url     : https://prove2.me/theorems/fb50bf75-e175-4967-b958-50ca1ec04bd4
-- title:
--   Truncate
-- statement:
--   Definitions and structural lemmas for Truncate, from Jue Xu; LeanPool contributors's pinned Low-weight Pauli dynamics and truncation error development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Truncate.lean

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Flow
public import Theorems.Thm_Lean4LPD_PauliString_cls_fst
public import Theorems.Thm_Lean4LPD_PauliString_cls_herm
public import Theorems.Thm_Lean4LPD_PauliString_cls_snd
public import Theorems.Thm_Lean4LPD_PauliString_coeffVec_apply
public import Theorems.Thm_Lean4LPD_PauliString_coeff_toMatrix_herm
public import Theorems.Thm_Lean4LPD_PauliString_coeff_toMatrix_herm_eq_zero
public import Theorems.Thm_Lean4LPD_PauliString_herm_x
public import Theorems.Thm_Lean4LPD_PauliString_herm_z
public import Theorems.Thm_Lean4LPD_PauliString_highNorm_eq_zero
public import Theorems.Thm_Lean4LPD_PauliString_highNorm_nonneg
public import Theorems.Thm_Lean4LPD_PauliString_highNorm_restr_le
public import Theorems.Thm_Lean4LPD_PauliString_isSelfAdjoint_X1
public import Theorems.Thm_Lean4LPD_PauliString_mem_antiSites
public import Theorems.Thm_Lean4LPD_PauliString_mem_highSet
public import Theorems.Thm_Lean4LPD_PauliString_mem_support
public import Theorems.Thm_Lean4LPD_PauliString_norm_coeffVec
public import Theorems.Thm_Lean4LPD_PauliString_norm_restr_le
public import Theorems.Thm_Lean4LPD_PauliString_pauliNorm_nonneg
public import Theorems.Thm_Lean4LPD_PauliString_pauliNorm_sq
public import Theorems.Thm_Lean4LPD_PauliString_phaseMul_eq_phaseMul_iff
public import Theorems.Thm_Lean4LPD_PauliString_phaseMul_eq_self_iff
public import Theorems.Thm_Lean4LPD_PauliString_phaseMul_phase
public import Theorems.Thm_Lean4LPD_PauliString_phaseMul_x
public import Theorems.Thm_Lean4LPD_PauliString_phaseMul_z
public import Theorems.Thm_Lean4LPD_PauliString_phaseMul_zero
public import Theorems.Thm_Lean4LPD_PauliString_restr_apply
public import Theorems.Thm_Lean4LPD_PauliString_restr_univ
public import Theorems.Thm_Lean4LPD_PauliString_site_mul
public import Theorems.Thm_Lean4LPD_PauliString_site_one
public import Theorems.Thm_Lean4LPD_PauliString_site_phaseMul
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
public import Theorems.Thm_Lean4LPD_iPow_signPhase
public import Theorems.Thm_Lean4LPD_iPow_two
public import Theorems.Thm_Lean4LPD_negOnePow_mul_self
public import Theorems.Thm_Lean4LPD_negOnePow_one
public import Theorems.Thm_Lean4LPD_negOnePow_zero
public import Theorems.Thm_Lean4LPD_norm_iPow
public import Theorems.Thm_Lean4LPD_rungWeight_one
public import Theorems.Thm_Lean4LPD_star_negOnePow
attribute [local simp] Lean4LPD.PauliString.cls_fst
attribute [local simp] Lean4LPD.PauliString.cls_herm
attribute [local simp] Lean4LPD.PauliString.cls_snd
attribute [local simp] Lean4LPD.PauliString.coeffVec_apply
attribute [local simp] Lean4LPD.PauliString.herm_x
attribute [local simp] Lean4LPD.PauliString.herm_z
attribute [local simp] Lean4LPD.PauliString.mem_antiSites
attribute [local simp] Lean4LPD.PauliString.mem_highSet
attribute [local simp] Lean4LPD.PauliString.mem_support
attribute [local simp] Lean4LPD.PauliString.pauliNorm_sq
attribute [local simp] Lean4LPD.PauliString.phaseMul_eq_phaseMul_iff
attribute [local simp] Lean4LPD.PauliString.phaseMul_eq_self_iff
attribute [local simp] Lean4LPD.PauliString.phaseMul_phase
attribute [local simp] Lean4LPD.PauliString.phaseMul_x
attribute [local simp] Lean4LPD.PauliString.phaseMul_z
attribute [local simp] Lean4LPD.PauliString.phaseMul_zero
attribute [local simp] Lean4LPD.PauliString.restr_apply
attribute [local simp] Lean4LPD.PauliString.restr_univ
attribute [local simp] Lean4LPD.PauliString.site_mul
attribute [local simp] Lean4LPD.PauliString.site_one
attribute [local simp] Lean4LPD.PauliString.site_phaseMul
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
namespace PauliString
variable {n ko kh : ℕ}
noncomputable def truncOp (S : Finset (PauliIndex n)) (O : Matrix (Bits n) (Bits n) ℂ) :
    Matrix (Bits n) (Bits n) ℂ :=
  ∑ p ∈ S, coeff O p • toMatrix (herm p)
theorem coeff_truncOp (S : Finset (PauliIndex n)) (O : Matrix (Bits n) (Bits n) ℂ)
    (q : PauliIndex n) :
    coeff (truncOp S O) q = if q ∈ S then coeff O q else 0 := by
  have hc : ∀ A : Matrix (Bits n) (Bits n) ℂ,
      coeff A q = ((2 : ℂ) ^ n)⁻¹ * (toMatrix (herm q) * A).trace := fun _ => rfl
  have hterm : ∀ p ∈ S,
      ((2 : ℂ) ^ n)⁻¹ * (toMatrix (herm q) * (coeff O p • toMatrix (herm p))).trace
        = if q = p then coeff O p else 0 := by
    intro p _
    rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, ← mul_assoc,
      mul_comm (((2 : ℂ) ^ n)⁻¹) (coeff O p), mul_assoc, ← hc, coeff_toMatrix_herm]
    split <;> simp
  rw [hc, truncOp, Finset.mul_sum, Matrix.trace_sum, Finset.mul_sum,
    Finset.sum_congr rfl hterm, Finset.sum_ite_eq]
theorem coeffVec_truncOp (S : Finset (PauliIndex n)) (O : Matrix (Bits n) (Bits n) ℂ) :
    coeffVec (truncOp S O) = restr S (coeffVec O) := by
  ext p
  rw [coeffVec_apply, restr_apply, coeff_truncOp]
  simp only [coeffVec_apply]
theorem highNorm_truncOp_le (w : ℕ) (S : Finset (PauliIndex n))
    (O : Matrix (Bits n) (Bits n) ℂ) : highNorm w (truncOp S O) ≤ highNorm w O := by
  rw [highNorm, highNorm, coeffVec_truncOp]
  exact highNorm_restr_le S (coeffVec O)
theorem pauliNorm_truncOp_le (S : Finset (PauliIndex n)) (O : Matrix (Bits n) (Bits n) ℂ) :
    pauliNorm (truncOp S O) ≤ pauliNorm O := by
  rw [← norm_coeffVec, ← norm_coeffVec, coeffVec_truncOp]
  exact norm_restr_le _ _
noncomputable def trajTrunc (Gs : ℕ → PauliString n) (θ : ℕ → ℝ)
    (S : ℕ → Finset (PauliIndex n)) (O : Matrix (Bits n) (Bits n) ℂ) :
    ℕ → Matrix (Bits n) (Bits n) ℂ
  | 0 => O
  | g + 1 => truncOp (S g)
      (rot (toMatrix (Gs g)) (θ g) * trajTrunc Gs θ S O g * rot (toMatrix (Gs g)) (-(θ g)))
@[simp] lemma trajTrunc_zero (Gs : ℕ → PauliString n) (θ : ℕ → ℝ)
    (S : ℕ → Finset (PauliIndex n)) (O : Matrix (Bits n) (Bits n) ℂ) :
    trajTrunc Gs θ S O 0 = O := rfl
lemma trajTrunc_succ (Gs : ℕ → PauliString n) (θ : ℕ → ℝ) (S : ℕ → Finset (PauliIndex n))
    (O : Matrix (Bits n) (Bits n) ℂ) (g : ℕ) :
    trajTrunc Gs θ S O (g + 1)
      = truncOp (S g)
          (rot (toMatrix (Gs g)) (θ g) * trajTrunc Gs θ S O g
            * rot (toMatrix (Gs g)) (-(θ g))) := rfl
theorem pauliNorm_trajTrunc_le {Gs : ℕ → PauliString n} (hG : ∀ g, IsSelfAdjoint (Gs g))
    (θ : ℕ → ℝ) (S : ℕ → Finset (PauliIndex n)) (O : Matrix (Bits n) (Bits n) ℂ) (g : ℕ) :
    pauliNorm (trajTrunc Gs θ S O g) ≤ pauliNorm O := by
  induction g with
  | zero => exact le_rfl
  | succ g ih =>
    rw [trajTrunc_succ]
    exact le_trans (pauliNorm_truncOp_le _ _)
      (le_trans (le_of_eq (pauliNorm_conj (hG g) (θ g) _)) ih)
noncomputable def ladderNTrunc (Gs : ℕ → PauliString n) (θ : ℕ → ℝ)
    (S : ℕ → Finset (PauliIndex n)) (O : Matrix (Bits n) (Bits n) ℂ) (ko kh : ℕ) : ℕ → ℕ → ℝ
  | 0, g => pauliNorm (trajTrunc Gs θ S O g)
  | m + 1, g => highNorm (rungWeight ko kh (m + 1)) (trajTrunc Gs θ S O g)
lemma ladderNTrunc_nonneg (Gs : ℕ → PauliString n) (θ : ℕ → ℝ)
    (S : ℕ → Finset (PauliIndex n)) (O : Matrix (Bits n) (Bits n) ℂ) (ko kh m g : ℕ) :
    0 ≤ ladderNTrunc Gs θ S O ko kh m g := by
  cases m with
  | zero => exact pauliNorm_nonneg _
  | succ m => exact highNorm_nonneg _ _
lemma ladderNTrunc_init {Gs : ℕ → PauliString n} {θ : ℕ → ℝ} {S : ℕ → Finset (PauliIndex n)}
    {O : Matrix (Bits n) (Bits n) ℂ} {ko kh : ℕ}
    (hloc : ∀ p : PauliIndex n, ko < wt p → coeff O p = 0) (m : ℕ) (hm : 1 ≤ m) :
    ladderNTrunc Gs θ S O ko kh m 0 = 0 := by
  obtain ⟨m, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  refine highNorm_eq_zero _ fun p hp => hloc p (lt_of_le_of_lt ?_ hp)
  simp only [rungWeight, Nat.add_sub_cancel]
  exact Nat.le_add_right ko (m * (kh - 1))
theorem highNorm_conj_trajTrunc_le {Gs : ℕ → PauliString n} {θ : ℕ → ℝ}
    {S : ℕ → Finset (PauliIndex n)} {O : Matrix (Bits n) (Bits n) ℂ}
    (hG : ∀ g, IsSelfAdjoint (Gs g)) (hk : ∀ g, weight (Gs g) ≤ kh) (m g : ℕ) (hm : 1 ≤ m) :
    highNorm (rungWeight ko kh m)
        (rot (toMatrix (Gs g)) (θ g) * trajTrunc Gs θ S O g * rot (toMatrix (Gs g)) (-(θ g)))
      ≤ ladderNTrunc Gs θ S O ko kh m g
        + |Real.sin (θ g)| * ladderNTrunc Gs θ S O ko kh (m - 1) g := by
  match m, hm with
  | 1, _ =>
    change highNorm (rungWeight ko kh 1) _
      ≤ highNorm (rungWeight ko kh 1) (trajTrunc Gs θ S O g)
        + |Real.sin (θ g)| * pauliNorm (trajTrunc Gs θ S O g)
    exact highNorm_conj_le_pauliNorm (hG g) (θ g) _
  | (m + 2), _ =>
    change highNorm (rungWeight ko kh (m + 2)) _
      ≤ highNorm (rungWeight ko kh (m + 2)) (trajTrunc Gs θ S O g)
        + |Real.sin (θ g)| * highNorm (rungWeight ko kh (m + 1)) (trajTrunc Gs θ S O g)
    exact highNorm_conj_le_highNorm (w := rungWeight ko kh (m + 2))
      (w' := rungWeight ko kh (m + 1)) (hG g) (hk g) (rungWeight_add_two ko kh m).ge (θ g) _
theorem ladderNTrunc_step {Gs : ℕ → PauliString n} {θ : ℕ → ℝ}
    {S : ℕ → Finset (PauliIndex n)} {O : Matrix (Bits n) (Bits n) ℂ}
    (hG : ∀ g, IsSelfAdjoint (Gs g)) (hk : ∀ g, weight (Gs g) ≤ kh) (m g : ℕ) (hm : 1 ≤ m) :
    ladderNTrunc Gs θ S O ko kh m (g + 1)
      ≤ ladderNTrunc Gs θ S O ko kh m g
        + |Real.sin (θ g)| * ladderNTrunc Gs θ S O ko kh (m - 1) g := by
  refine le_trans ?_ (highNorm_conj_trajTrunc_le (ko := ko) hG hk m g hm)
  match m, hm with
  | (m + 1), _ =>
    change highNorm (rungWeight ko kh (m + 1)) (trajTrunc Gs θ S O (g + 1)) ≤ _
    rw [trajTrunc_succ]
    exact highNorm_truncOp_le _ _ _
noncomputable def pauliLadderTrunc {Gs : ℕ → PauliString n} {θ : ℕ → ℝ}
    {S : ℕ → Finset (PauliIndex n)} {O : Matrix (Bits n) (Bits n) ℂ} {ko kh : ℕ} {a : ℝ}
    (hG : ∀ g, IsSelfAdjoint (Gs g)) (hk : ∀ g, weight (Gs g) ≤ kh)
    (ha : ∀ g, |Real.sin (θ g)| ≤ a)
    (hloc : ∀ p : PauliIndex n, ko < wt p → coeff O p = 0) :
    Ladder a (pauliNorm O) where
  N := ladderNTrunc Gs θ S O ko kh
  nonneg := ladderNTrunc_nonneg Gs θ S O ko kh
  reservoir g := pauliNorm_trajTrunc_le hG θ S O g
  init := ladderNTrunc_init hloc
  step m g hm :=
    le_trans (ladderNTrunc_step hG hk m g hm)
      (add_le_add le_rfl (mul_le_mul_of_nonneg_right (ha g)
        (ladderNTrunc_nonneg Gs θ S O ko kh (m - 1) g)))
noncomputable def pauliWeightedLadderTrunc {Gs : ℕ → PauliString n} {θ : ℕ → ℝ}
    {S : ℕ → Finset (PauliIndex n)} {O : Matrix (Bits n) (Bits n) ℂ} {ko kh : ℕ} {c : ℕ → ℝ}
    (hG : ∀ g, IsSelfAdjoint (Gs g)) (hk : ∀ g, weight (Gs g) ≤ kh)
    (hc : ∀ g m, |Real.sin (θ g)| ≤ c m)
    (hloc : ∀ p : PauliIndex n, ko < wt p → coeff O p = 0) :
    WeightedLadder c (pauliNorm O) where
  N := ladderNTrunc Gs θ S O ko kh
  nonneg := ladderNTrunc_nonneg Gs θ S O ko kh
  reservoir g := pauliNorm_trajTrunc_le hG θ S O g
  init := ladderNTrunc_init hloc
  step m g hm :=
    le_trans (ladderNTrunc_step hG hk m g hm)
      (add_le_add le_rfl (mul_le_mul_of_nonneg_right (hc g m)
        (ladderNTrunc_nonneg Gs θ S O ko kh (m - 1) g)))
noncomputable def pauliLadderTruncAt {Gs : ℕ → PauliString n} {θ : ℕ → ℝ}
    {O : Matrix (Bits n) (Bits n) ℂ} {ko kh : ℕ} {a : ℝ} (wstar : ℕ)
    (hG : ∀ g, IsSelfAdjoint (Gs g)) (hk : ∀ g, weight (Gs g) ≤ kh)
    (ha : ∀ g, |Real.sin (θ g)| ≤ a)
    (hloc : ∀ p : PauliIndex n, ko < wt p → coeff O p = 0) :
    Ladder a (pauliNorm O) :=
  pauliLadderTrunc (S := fun _ => (highSet n wstar)ᶜ) (ko := ko) (kh := kh) hG hk ha hloc
noncomputable example (dt : ℝ) : Ladder |Real.sin dt| (pauliNorm (toMatrix Z1)) := by
  have hz : herm (cls Z1) = Z1 := by decide
  refine hz ▸ pauliLadderTruncAt (ko := wt (cls Z1)) (kh := 1) (Gs := fun _ => X1)
    (θ := fun _ => dt) 1 (fun _ => isSelfAdjoint_X1) (fun _ => ?_) (fun _ => le_rfl)
    (fun _ hp => coeff_toMatrix_herm_eq_zero hp)
  decide
end PauliString
end Lean4LPD


