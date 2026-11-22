-- Prove2me | Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Flow
-- name    : LeanPool_LowWeightPauliDynamics_Pauli_Flow
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T07:27:19.780888+00:00
-- url     : https://prove2.me/theorems/3be2fe9b-97f2-4f51-8f17-c67d288aaff2
-- title:
--   Flow
-- statement:
--   Definitions and structural lemmas for Flow, from Jue Xu; LeanPool contributors's pinned Low-weight Pauli dynamics and truncation error development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Flow.lean

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Ladder_Defs
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Ladder_Weighted
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Branch
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Coeff
public import Theorems.Thm_Lean4LPD_PauliString_cls_fst
public import Theorems.Thm_Lean4LPD_PauliString_cls_herm
public import Theorems.Thm_Lean4LPD_PauliString_cls_snd
public import Theorems.Thm_Lean4LPD_PauliString_coeffVec_apply
public import Theorems.Thm_Lean4LPD_PauliString_coeff_toMatrix_herm_eq_zero
public import Theorems.Thm_Lean4LPD_PauliString_herm_x
public import Theorems.Thm_Lean4LPD_PauliString_herm_z
public import Theorems.Thm_Lean4LPD_PauliString_highNorm_eq_zero
public import Theorems.Thm_Lean4LPD_PauliString_highNorm_nonneg
public import Theorems.Thm_Lean4LPD_PauliString_isSelfAdjoint_X1
public import Theorems.Thm_Lean4LPD_PauliString_isSelfAdjoint_herm
public import Theorems.Thm_Lean4LPD_PauliString_isSelfAdjoint_iff_phase
public import Theorems.Thm_Lean4LPD_PauliString_isSelfAdjoint_phaseMul_one_mul
public import Theorems.Thm_Lean4LPD_PauliString_mem_antiSites
public import Theorems.Thm_Lean4LPD_PauliString_mem_highSet
public import Theorems.Thm_Lean4LPD_PauliString_mem_support
public import Theorems.Thm_Lean4LPD_PauliString_norm_coeffVec
public import Theorems.Thm_Lean4LPD_PauliString_norm_restr_le
public import Theorems.Thm_Lean4LPD_PauliString_norm_restr_sq
public import Theorems.Thm_Lean4LPD_PauliString_pauliNorm_nonneg
public import Theorems.Thm_Lean4LPD_PauliString_pauliNorm_sq
public import Theorems.Thm_Lean4LPD_PauliString_pauli_rotation_branch_anticommute_hermitian
public import Theorems.Thm_Lean4LPD_PauliString_pauli_rotation_branch_commute
public import Theorems.Thm_Lean4LPD_PauliString_phaseMul_eq_phaseMul_iff
public import Theorems.Thm_Lean4LPD_PauliString_phaseMul_eq_self_iff
public import Theorems.Thm_Lean4LPD_PauliString_phaseMul_phase
public import Theorems.Thm_Lean4LPD_PauliString_phaseMul_x
public import Theorems.Thm_Lean4LPD_PauliString_phaseMul_z
public import Theorems.Thm_Lean4LPD_PauliString_phaseMul_zero
public import Theorems.Thm_Lean4LPD_PauliString_phase_sub_of_isSelfAdjoint
public import Theorems.Thm_Lean4LPD_PauliString_restr_add
public import Theorems.Thm_Lean4LPD_PauliString_restr_add_restr_compl
public import Theorems.Thm_Lean4LPD_PauliString_restr_apply
public import Theorems.Thm_Lean4LPD_PauliString_restr_univ
public import Theorems.Thm_Lean4LPD_PauliString_site_mul
public import Theorems.Thm_Lean4LPD_PauliString_site_one
public import Theorems.Thm_Lean4LPD_PauliString_site_phaseMul
public import Theorems.Thm_Lean4LPD_PauliString_sympForm_eq_zero_or_one
public import Theorems.Thm_Lean4LPD_PauliString_sympForm_mul_self_right
public import Theorems.Thm_Lean4LPD_PauliString_sympForm_phaseMul_left
public import Theorems.Thm_Lean4LPD_PauliString_sympForm_phaseMul_right
public import Theorems.Thm_Lean4LPD_PauliString_sympForm_self
public import Theorems.Thm_Lean4LPD_PauliString_toMatrix_one
public import Theorems.Thm_Lean4LPD_PauliString_toMatrix_phaseMul
public import Theorems.Thm_Lean4LPD_PauliString_weight_congr
public import Theorems.Thm_Lean4LPD_PauliString_weight_le_weight_mul_add_kh
public import Theorems.Thm_Lean4LPD_PauliString_weight_one
public import Theorems.Thm_Lean4LPD_PauliString_weight_phaseMul
public import Theorems.Thm_Lean4LPD_PauliString_wt_cls
public import Theorems.Thm_Lean4LPD_conj_negOnePow
public import Theorems.Thm_Lean4LPD_iPow_add
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
variable {n : ℕ} {G : PauliString n} {p : PauliIndex n} {kh w w' : ℕ}
lemma le_of_sq_le_sq' {a b : ℝ} (_ha : 0 ≤ a) (hb : 0 ≤ b) (h : a ^ 2 ≤ b ^ 2) : a ≤ b := by
  nlinarith
lemma add_ofLp (y z : EuclideanSpace ℂ (PauliIndex n)) (q : PauliIndex n) :
    (y + z).ofLp q = y.ofLp q + z.ofLp q := rfl
def partner (G : PauliString n) (p : PauliIndex n) : PauliIndex n := (G.x + p.1, G.z + p.2)
@[simp] lemma cls_mul_herm (G : PauliString n) (p : PauliIndex n) :
    cls (G * herm p) = partner G p := rfl
@[simp] lemma partner_partner (G : PauliString n) (p : PauliIndex n) :
    partner G (partner G p) = p := by
  have h : ∀ u v : Bits n, u + (u + v) = v := fun u v => by
    rw [← add_assoc, bits_add_self, zero_add]
  exact Prod.ext (h G.x p.1) (h G.z p.2)
lemma partner_injective (G : PauliString n) : Function.Injective (partner G) := fun a b hab => by
  rw [← partner_partner G a, hab, partner_partner]
@[simp] lemma sympForm_herm_partner (G : PauliString n) (p : PauliIndex n) :
    sympForm G (herm (partner G p)) = sympForm G (herm p) := by
  have h : sympForm G (herm (partner G p)) = sympForm G (G * herm p) := rfl
  rw [h, sympForm_mul_self_right]
lemma wt_partner (G : PauliString n) (p : PauliIndex n) :
    wt (partner G p) = weight (G * herm p) := weight_congr rfl rfl
noncomputable def partnerSign (G : PauliString n) (p : PauliIndex n) : ℂ :=
  iPow ((phaseMul 1 (G * herm p)).phase - (herm (partner G p)).phase)
lemma toMatrix_partner (G : PauliString n) (p : PauliIndex n) :
    toMatrix (phaseMul 1 (G * herm p))
      = partnerSign G p • toMatrix (herm (partner G p)) := by
  rw [partnerSign, ← toMatrix_phaseMul]
  refine congrArg toMatrix (ext' rfl rfl ?_)
  change (phaseMul 1 (G * herm p)).phase
    = (herm (partner G p)).phase
      + ((phaseMul 1 (G * herm p)).phase - (herm (partner G p)).phase)
  ring
lemma partnerSign_eq_one_or_neg_one (hG : IsSelfAdjoint G) (h : sympForm G (herm p) = 1) :
    partnerSign G p = 1 ∨ partnerSign G p = -1 := by
  have hs : IsSelfAdjoint (phaseMul 1 (G * herm p)) :=
    isSelfAdjoint_phaseMul_one_mul hG (isSelfAdjoint_herm p) h
  rcases phase_sub_of_isSelfAdjoint hs (isSelfAdjoint_herm (partner G p)) rfl rfl with hd | hd
  · exact Or.inl (by rw [partnerSign, hd, iPow_zero])
  · exact Or.inr (by rw [partnerSign, hd, iPow_two])
lemma partnerSign_mul_self (hG : IsSelfAdjoint G) (h : sympForm G (herm p) = 1) :
    partnerSign G p * partnerSign G p = 1 := by
  rcases partnerSign_eq_one_or_neg_one hG h with hp | hp <;> rw [hp] <;> ring
lemma norm_partnerSign (hG : IsSelfAdjoint G) (h : sympForm G (herm p) = 1) :
    ‖partnerSign G p‖ = 1 := by
  rcases partnerSign_eq_one_or_neg_one hG h with hp | hp <;> rw [hp] <;> simp
lemma conj_partnerSign (hG : IsSelfAdjoint G) (h : sympForm G (herm p) = 1) :
    (starRingEnd ℂ) (partnerSign G p) = partnerSign G p := by
  rcases partnerSign_eq_one_or_neg_one hG h with hp | hp <;> rw [hp] <;> simp
lemma partnerSign_partner (hG : IsSelfAdjoint G) (h : sympForm G (herm p) = 1) :
    partnerSign G (partner G p) = -partnerSign G p := by
  have hph : ∀ r : PauliIndex n, (phaseMul 1 (G * herm r)).phase
      = G.phase + (herm r).phase + signPhase (G.z ⬝ᵥ r.1) + 1 := fun _ => rfl
  have hsp : signPhase (G.z ⬝ᵥ (partner G p).1)
      = signPhase (G.z ⬝ᵥ G.x) + signPhase (G.z ⬝ᵥ p.1) := by
    change signPhase (G.z ⬝ᵥ (G.x + p.1)) = _
    rw [dotProduct_add, signPhase_add]
  have hG' : signPhase (G.z ⬝ᵥ G.x) = 2 * G.phase := isSelfAdjoint_iff_phase.1 hG
  have hs2 : signPhase (G.z ⬝ᵥ p.1) + signPhase (G.z ⬝ᵥ p.1) = 0 := signPhase_add_self _
  have h4 : ∀ x : ZMod 4, 2 * x + 2 * x = 0 := by decide
  have hsum : ((phaseMul 1 (G * herm (partner G p))).phase
        - (herm (partner G (partner G p))).phase)
      + ((phaseMul 1 (G * herm p)).phase - (herm (partner G p)).phase) = 2 := by
    rw [partner_partner, hph, hph, hsp]
    linear_combination hG' + h4 G.phase + hs2
  have hmul : partnerSign G (partner G p) * partnerSign G p = -1 := by
    rw [partnerSign, partnerSign, ← iPow_add, hsum, iPow_two]
  calc partnerSign G (partner G p)
      = partnerSign G (partner G p) * (partnerSign G p * partnerSign G p) := by
        rw [partnerSign_mul_self hG h, mul_one]
    _ = partnerSign G (partner G p) * partnerSign G p * partnerSign G p := by ring
    _ = -partnerSign G p := by rw [hmul]; ring
noncomputable def rotAct (G : PauliString n) (θ : ℝ) (y : EuclideanSpace ℂ (PauliIndex n)) :
    EuclideanSpace ℂ (PauliIndex n) :=
  WithLp.toLp 2 fun p =>
    if sympForm G (herm p) = 0 then y.ofLp p
    else (Real.cos θ : ℂ) * y.ofLp p
      - (Real.sin θ : ℂ) * (partnerSign G p * y.ofLp (partner G p))
@[simp] lemma rotAct_apply (G : PauliString n) (θ : ℝ) (y : EuclideanSpace ℂ (PauliIndex n))
    (p : PauliIndex n) :
    (rotAct G θ y).ofLp p
      = if sympForm G (herm p) = 0 then y.ofLp p
        else (Real.cos θ : ℂ) * y.ofLp p
          - (Real.sin θ : ℂ) * (partnerSign G p * y.ofLp (partner G p)) := rfl
lemma rotAct_add (G : PauliString n) (θ : ℝ) (y z : EuclideanSpace ℂ (PauliIndex n)) :
    rotAct G θ (y + z) = rotAct G θ y + rotAct G θ z := by
  ext q
  simp only [rotAct_apply, add_ofLp]
  split <;> ring
theorem coeff_conj (hG : IsSelfAdjoint G) (θ : ℝ) (O : Matrix (Bits n) (Bits n) ℂ)
    (p : PauliIndex n) :
    coeff (rot (toMatrix G) θ * O * rot (toMatrix G) (-θ)) p
      = if sympForm G (herm p) = 0 then coeff O p
        else (Real.cos θ : ℂ) * coeff O p
          - (Real.sin θ : ℂ) * (partnerSign G p * coeff O (partner G p)) := by
  have hcyc : (toMatrix (herm p) * (rot (toMatrix G) θ * O * rot (toMatrix G) (-θ))).trace
      = (rot (toMatrix G) (-θ) * toMatrix (herm p) * rot (toMatrix G) θ * O).trace := by
    rw [show toMatrix (herm p) * (rot (toMatrix G) θ * O * rot (toMatrix G) (-θ))
        = toMatrix (herm p) * rot (toMatrix G) θ * O * rot (toMatrix G) (-θ) by
          simp only [mul_assoc], Matrix.trace_mul_comm]
    simp only [mul_assoc]
  rw [coeff, hcyc]
  rcases sympForm_eq_zero_or_one G (herm p) with h | h
  · rw [if_pos h]
    have hbr := pauli_rotation_branch_commute hG h (-θ)
    rw [neg_neg] at hbr
    rw [hbr, coeff]
  · rw [if_neg (by rw [h]; decide : ¬ sympForm G (herm p) = 0)]
    have hbr := pauli_rotation_branch_anticommute_hermitian hG h (-θ)
    rw [neg_neg, Real.cos_neg, Real.sin_neg] at hbr
    rw [hbr, toMatrix_partner, Matrix.add_mul, Matrix.trace_add]
    simp only [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
    rw [coeff, coeff]
    push_cast
    ring
theorem coeffVec_conj (hG : IsSelfAdjoint G) (θ : ℝ) (O : Matrix (Bits n) (Bits n) ℂ) :
    coeffVec (rot (toMatrix G) θ * O * rot (toMatrix G) (-θ)) = rotAct G θ (coeffVec O) := by
  ext p
  rw [coeffVec_apply, rotAct_apply, coeff_conj hG θ O p]
  simp only [coeffVec_apply]
lemma sum_anti_norm_sq (hG : IsSelfAdjoint G) (θ : ℝ)
    (y : EuclideanSpace ℂ (PauliIndex n)) :
    ∑ q ∈ univ.filter fun q : PauliIndex n => ¬ sympForm G (herm q) = 0,
        ‖(rotAct G θ y).ofLp q‖ ^ 2
      = ∑ q ∈ univ.filter fun q : PauliIndex n => ¬ sympForm G (herm q) = 0,
          ‖y.ofLp q‖ ^ 2 := by
  classical
  set A : Finset (PauliIndex n) := univ.filter fun q : PauliIndex n => ¬ sympForm G (herm q) = 0
    with hA
  have hmemA : ∀ q : PauliIndex n, q ∈ A ↔ sympForm G (herm q) = 1 := by
    intro q
    rw [hA, Finset.mem_filter]
    refine ⟨fun hq => ?_, fun h => ⟨Finset.mem_univ _, by rw [h]; decide⟩⟩
    rcases sympForm_eq_zero_or_one G (herm q) with h | h
    · exact absurd h hq.2
    · exact h
  have hpartA : ∀ q ∈ A, partner G q ∈ A := fun q hq =>
    (hmemA _).2 (by rw [sympForm_herm_partner]; exact (hmemA q).1 hq)
  -- the cross term, antisymmetric under the pairing
  set T : PauliIndex n → ℂ := fun q => partnerSign G q *
    (y.ofLp q * (starRingEnd ℂ) (y.ofLp (partner G q))
      + y.ofLp (partner G q) * (starRingEnd ℂ) (y.ofLp q)) with hT
  have hTanti : ∀ q ∈ A, T q + T (partner G q) = 0 := by
    intro q hq
    rw [hT]
    simp only
    rw [partner_partner, partnerSign_partner hG ((hmemA q).1 hq)]
    ring
  have hTsum : ∑ q ∈ A, T q = 0 :=
    Finset.sum_involution (fun q _ => partner G q) hTanti
      (fun q hq hne => by
        intro hfix
        refine hne ?_
        have := hTanti q hq
        rw [hfix] at this
        linear_combination this / 2)
      hpartA (fun q _ => partner_partner G q)
  -- and the two diagonal sums agree
  have hdiag : ∑ q ∈ A, y.ofLp (partner G q) * (starRingEnd ℂ) (y.ofLp (partner G q))
      = ∑ q ∈ A, y.ofLp q * (starRingEnd ℂ) (y.ofLp q) :=
    Finset.sum_nbij' (partner G) (partner G) hpartA hpartA (fun q _ => partner_partner G q)
      (fun q _ => partner_partner G q) (fun q _ => rfl)
  have hcast : ((∑ q ∈ A, ‖(rotAct G θ y).ofLp q‖ ^ 2 : ℝ) : ℂ)
      = ((∑ q ∈ A, ‖y.ofLp q‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    have hterm : ∀ q ∈ A, ((‖(rotAct G θ y).ofLp q‖ : ℝ) : ℂ) ^ 2
        = (Real.cos θ : ℂ) ^ 2 * (y.ofLp q * (starRingEnd ℂ) (y.ofLp q))
          + (Real.sin θ : ℂ) ^ 2
              * (y.ofLp (partner G q) * (starRingEnd ℂ) (y.ofLp (partner G q)))
          - (Real.cos θ : ℂ) * (Real.sin θ : ℂ) * T q := by
      intro q hq
      have hq1 : sympForm G (herm q) = 1 := (hmemA q).1 hq
      rw [← Complex.mul_conj', rotAct_apply, if_neg (by rw [hq1]; decide)]
      rw [map_sub, map_mul, map_mul, map_mul, conj_partnerSign hG hq1]
      simp only [Complex.conj_ofReal]
      have hsign : partnerSign G q * partnerSign G q = 1 := partnerSign_mul_self hG hq1
      rw [hT]
      simp only
      linear_combination (Real.sin θ : ℂ) ^ 2
        * (y.ofLp (partner G q) * (starRingEnd ℂ) (y.ofLp (partner G q))) * hsign
    rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, hdiag, hTsum, mul_zero, sub_zero,
      ← add_mul]
    have hcs : (Real.cos θ : ℂ) ^ 2 + (Real.sin θ : ℂ) ^ 2 = 1 := by
      rw [← Complex.ofReal_pow, ← Complex.ofReal_pow, ← Complex.ofReal_add,
        add_comm (Real.cos θ ^ 2), Real.sin_sq_add_cos_sq, Complex.ofReal_one]
    rw [hcs, one_mul]
    exact Finset.sum_congr rfl fun q _ => Complex.mul_conj' _
  exact_mod_cast hcast
theorem norm_rotAct (hG : IsSelfAdjoint G) (θ : ℝ) (y : EuclideanSpace ℂ (PauliIndex n)) :
    ‖rotAct G θ y‖ = ‖y‖ := by
  classical
  have hsq : ‖rotAct G θ y‖ ^ 2 = ‖y‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,
      ← Finset.sum_filter_add_sum_filter_not univ
        (fun q : PauliIndex n => sympForm G (herm q) = 0)
        (fun q => ‖(rotAct G θ y).ofLp q‖ ^ 2),
      ← Finset.sum_filter_add_sum_filter_not univ
        (fun q : PauliIndex n => sympForm G (herm q) = 0) (fun q => ‖y.ofLp q‖ ^ 2)]
    refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun q hq => ?_) (sum_anti_norm_sq hG θ y)
    rw [rotAct_apply, if_pos (Finset.mem_filter.1 hq).2]
  have h1 : (0 : ℝ) ≤ ‖rotAct G θ y‖ := norm_nonneg _
  have h2 : (0 : ℝ) ≤ ‖y‖ := norm_nonneg _
  nlinarith
lemma norm_restr_high_rotAct_low (hG : IsSelfAdjoint G) (θ : ℝ)
    (y : EuclideanSpace ℂ (PauliIndex n)) (T : Finset (PauliIndex n))
    (hT : ∀ q : PauliIndex n, w < wt q → sympForm G (herm q) = 1 → partner G q ∈ T) :
    ‖restr (highSet n w) (rotAct G θ (restr (highSet n w)ᶜ y))‖
      ≤ |Real.sin θ| * ‖restr T y‖ := by
  classical
  set u : EuclideanSpace ℂ (PauliIndex n) := restr (highSet n w)ᶜ y with hu
  set S : Finset (PauliIndex n) :=
    (highSet n w).filter fun q => sympForm G (herm q) = 1 with hS
  have hzero : ∀ q ∈ highSet n w, u.ofLp q = 0 := by
    intro q hq
    rw [hu, restr_apply, if_neg (by simp [Finset.mem_compl, hq])]
  have hule : ∀ q : PauliIndex n, ‖u.ofLp q‖ ≤ ‖y.ofLp q‖ := by
    intro q
    rw [hu, restr_apply]
    split
    · exact le_rfl
    · simp
  have hcollapse : ∑ q ∈ S, ‖(rotAct G θ u).ofLp q‖ ^ 2
      = ∑ q ∈ highSet n w, ‖(rotAct G θ u).ofLp q‖ ^ 2 := by
    refine Finset.sum_subset (Finset.filter_subset _ _) fun q hq hqS => ?_
    have h0 : sympForm G (herm q) = 0 := by
      rcases sympForm_eq_zero_or_one G (herm q) with h | h
      · exact h
      · exact absurd (Finset.mem_filter.2 ⟨hq, h⟩) hqS
    rw [rotAct_apply, if_pos h0, hzero q hq, norm_zero]
    norm_num
  have hbound : ∀ q ∈ S,
      ‖(rotAct G θ u).ofLp q‖ ^ 2 ≤ Real.sin θ ^ 2 * ‖y.ofLp (partner G q)‖ ^ 2 := by
    intro q hq
    obtain ⟨hqh, hq1⟩ := Finset.mem_filter.1 hq
    rw [rotAct_apply, if_neg (by rw [hq1]; decide), hzero q hqh, mul_zero, zero_sub,
      norm_neg, norm_mul, norm_mul, norm_partnerSign hG hq1, one_mul, Complex.norm_real,
      Real.norm_eq_abs, mul_pow, sq_abs]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hule _) 2) (by positivity)
  have hinj : Set.InjOn (partner G) (S : Set (PauliIndex n)) :=
    fun a _ b _ hab => partner_injective G hab
  have himg : Finset.image (partner G) S ⊆ T := by
    intro t ht
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 ht
    obtain ⟨hqh, hq1⟩ := Finset.mem_filter.1 hq
    exact hT q (mem_highSet.1 hqh) hq1
  have hsq : ‖restr (highSet n w) (rotAct G θ u)‖ ^ 2
      ≤ (|Real.sin θ| * ‖restr T y‖) ^ 2 := by
    rw [norm_restr_sq, ← hcollapse, mul_pow, sq_abs, norm_restr_sq, Finset.mul_sum]
    refine le_trans (Finset.sum_le_sum hbound) ?_
    rw [← Finset.sum_image (f := fun t => Real.sin θ ^ 2 * ‖y.ofLp t‖ ^ 2) hinj]
    exact Finset.sum_le_sum_of_subset_of_nonneg himg (by intros; positivity)
  exact le_of_sq_le_sq' (norm_nonneg _) (by positivity) hsq
theorem highNorm_conj_le (hG : IsSelfAdjoint G) (θ : ℝ) (O : Matrix (Bits n) (Bits n) ℂ)
    (T : Finset (PauliIndex n))
    (hT : ∀ q : PauliIndex n, w < wt q → sympForm G (herm q) = 1 → partner G q ∈ T) :
    highNorm w (rot (toMatrix G) θ * O * rot (toMatrix G) (-θ))
      ≤ highNorm w O + |Real.sin θ| * ‖restr T (coeffVec O)‖ := by
  classical
  set x : EuclideanSpace ℂ (PauliIndex n) := coeffVec O with hx
  set R : Finset (PauliIndex n) := highSet n w with hR
  have hsplit : restr R (rotAct G θ x)
      = restr R (rotAct G θ (restr R x)) + restr R (rotAct G θ (restr Rᶜ x)) := by
    rw [← restr_add, ← rotAct_add, restr_add_restr_compl]
  calc highNorm w (rot (toMatrix G) θ * O * rot (toMatrix G) (-θ))
      = ‖restr R (rotAct G θ x)‖ := by rw [highNorm, coeffVec_conj hG]
    _ ≤ ‖restr R (rotAct G θ (restr R x))‖ + ‖restr R (rotAct G θ (restr Rᶜ x))‖ := by
        rw [hsplit]; exact norm_add_le _ _
    _ ≤ ‖restr R x‖ + |Real.sin θ| * ‖restr T x‖ := by
        refine add_le_add ?_ (norm_restr_high_rotAct_low hG θ x T hT)
        calc ‖restr R (rotAct G θ (restr R x))‖ ≤ ‖rotAct G θ (restr R x)‖ := norm_restr_le _ _
          _ = ‖restr R x‖ := norm_rotAct hG _ _
    _ = highNorm w O + |Real.sin θ| * ‖restr T x‖ := rfl
theorem highNorm_conj_le_highNorm (hG : IsSelfAdjoint G) (hk : weight G ≤ kh)
    (hw : w' + (kh - 1) ≤ w) (θ : ℝ) (O : Matrix (Bits n) (Bits n) ℂ) :
    highNorm w (rot (toMatrix G) θ * O * rot (toMatrix G) (-θ))
      ≤ highNorm w O + |Real.sin θ| * highNorm w' O := by
  refine highNorm_conj_le hG θ O (highSet n w') fun q hq h => ?_
  have h1 : wt q ≤ wt (partner G q) + (kh - 1) := by
    rw [wt_partner]
    exact weight_le_weight_mul_add_kh hk h
  exact mem_highSet.2 (by omega)
theorem highNorm_conj_le_pauliNorm (hG : IsSelfAdjoint G) (θ : ℝ)
    (O : Matrix (Bits n) (Bits n) ℂ) :
    highNorm w (rot (toMatrix G) θ * O * rot (toMatrix G) (-θ))
      ≤ highNorm w O + |Real.sin θ| * pauliNorm O := by
  refine le_trans (highNorm_conj_le hG θ O univ fun q _ _ => Finset.mem_univ _) ?_
  rw [restr_univ, norm_coeffVec]
theorem pauliNorm_conj (hG : IsSelfAdjoint G) (θ : ℝ) (O : Matrix (Bits n) (Bits n) ℂ) :
    pauliNorm (rot (toMatrix G) θ * O * rot (toMatrix G) (-θ)) = pauliNorm O := by
  rw [← norm_coeffVec, ← norm_coeffVec, coeffVec_conj hG, norm_rotAct hG]
lemma rungWeight_add_two (ko kh m : ℕ) :
    rungWeight ko kh (m + 2) = rungWeight ko kh (m + 1) + (kh - 1) := by
  have h1 : m + 2 - 1 = m + 1 := by omega
  have h2 : m + 1 - 1 = m := by omega
  rw [rungWeight, rungWeight, h1, h2, add_mul, one_mul, add_assoc]
noncomputable def traj (Gs : ℕ → PauliString n) (θ : ℕ → ℝ)
    (O : Matrix (Bits n) (Bits n) ℂ) : ℕ → Matrix (Bits n) (Bits n) ℂ
  | 0 => O
  | g + 1 => rot (toMatrix (Gs g)) (θ g) * traj Gs θ O g * rot (toMatrix (Gs g)) (-(θ g))
@[simp] lemma traj_zero (Gs : ℕ → PauliString n) (θ : ℕ → ℝ)
    (O : Matrix (Bits n) (Bits n) ℂ) : traj Gs θ O 0 = O := rfl
lemma traj_succ (Gs : ℕ → PauliString n) (θ : ℕ → ℝ) (O : Matrix (Bits n) (Bits n) ℂ) (g : ℕ) :
    traj Gs θ O (g + 1)
      = rot (toMatrix (Gs g)) (θ g) * traj Gs θ O g * rot (toMatrix (Gs g)) (-(θ g)) := rfl
theorem pauliNorm_traj {Gs : ℕ → PauliString n} (hG : ∀ g, IsSelfAdjoint (Gs g)) (θ : ℕ → ℝ)
    (O : Matrix (Bits n) (Bits n) ℂ) (g : ℕ) : pauliNorm (traj Gs θ O g) = pauliNorm O := by
  induction g with
  | zero => rfl
  | succ g ih => rw [traj_succ, pauliNorm_conj (hG g), ih]
noncomputable def ladderN (Gs : ℕ → PauliString n) (θ : ℕ → ℝ)
    (O : Matrix (Bits n) (Bits n) ℂ) (ko kh : ℕ) : ℕ → ℕ → ℝ
  | 0, g => pauliNorm (traj Gs θ O g)
  | m + 1, g => highNorm (rungWeight ko kh (m + 1)) (traj Gs θ O g)
lemma ladderN_nonneg (Gs : ℕ → PauliString n) (θ : ℕ → ℝ) (O : Matrix (Bits n) (Bits n) ℂ)
    (ko kh m g : ℕ) : 0 ≤ ladderN Gs θ O ko kh m g := by
  cases m with
  | zero => exact pauliNorm_nonneg _
  | succ m => exact highNorm_nonneg _ _
lemma ladderN_init {Gs : ℕ → PauliString n} {θ : ℕ → ℝ} {O : Matrix (Bits n) (Bits n) ℂ}
    {ko kh : ℕ} (hloc : ∀ p : PauliIndex n, ko < wt p → coeff O p = 0) (m : ℕ) (hm : 1 ≤ m) :
    ladderN Gs θ O ko kh m 0 = 0 := by
  obtain ⟨m, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  refine highNorm_eq_zero _ fun p hp => hloc p (lt_of_le_of_lt ?_ hp)
  simp only [rungWeight, Nat.add_sub_cancel]
  exact Nat.le_add_right ko (m * (kh - 1))
noncomputable def pauliLadder {Gs : ℕ → PauliString n} {θ : ℕ → ℝ}
    {O : Matrix (Bits n) (Bits n) ℂ} {ko kh : ℕ} {a : ℝ}
    (hG : ∀ g, IsSelfAdjoint (Gs g)) (hk : ∀ g, weight (Gs g) ≤ kh)
    (ha : ∀ g, |Real.sin (θ g)| ≤ a)
    (hloc : ∀ p : PauliIndex n, ko < wt p → coeff O p = 0) :
    Ladder a (pauliNorm O) where
  N := ladderN Gs θ O ko kh
  nonneg := ladderN_nonneg Gs θ O ko kh
  reservoir g := le_of_eq (pauliNorm_traj hG θ O g)
  init := ladderN_init hloc
  step m g hm := by
    match m, hm with
    | 1, _ =>
      change highNorm (rungWeight ko kh 1) (traj Gs θ O (g + 1))
        ≤ highNorm (rungWeight ko kh 1) (traj Gs θ O g) + a * pauliNorm (traj Gs θ O g)
      rw [traj_succ]
      exact le_trans (highNorm_conj_le_pauliNorm (hG g) (θ g) (traj Gs θ O g))
        (add_le_add le_rfl (mul_le_mul_of_nonneg_right (ha g) (pauliNorm_nonneg _)))
    | (m + 2), _ =>
      change highNorm (rungWeight ko kh (m + 2)) (traj Gs θ O (g + 1))
        ≤ highNorm (rungWeight ko kh (m + 2)) (traj Gs θ O g)
          + a * highNorm (rungWeight ko kh (m + 1)) (traj Gs θ O g)
      rw [traj_succ]
      exact le_trans
        (highNorm_conj_le_highNorm (w := rungWeight ko kh (m + 2))
          (w' := rungWeight ko kh (m + 1)) (hG g) (hk g)
          (rungWeight_add_two ko kh m).ge (θ g) (traj Gs θ O g))
        (add_le_add le_rfl (mul_le_mul_of_nonneg_right (ha g) (highNorm_nonneg _ _)))
noncomputable def pauliWeightedLadder {Gs : ℕ → PauliString n} {θ : ℕ → ℝ}
    {O : Matrix (Bits n) (Bits n) ℂ} {ko kh : ℕ} {c : ℕ → ℝ}
    (hG : ∀ g, IsSelfAdjoint (Gs g)) (hk : ∀ g, weight (Gs g) ≤ kh)
    (hc : ∀ g m, |Real.sin (θ g)| ≤ c m)
    (hloc : ∀ p : PauliIndex n, ko < wt p → coeff O p = 0) :
    WeightedLadder c (pauliNorm O) where
  N := ladderN Gs θ O ko kh
  nonneg := ladderN_nonneg Gs θ O ko kh
  reservoir g := le_of_eq (pauliNorm_traj hG θ O g)
  init := ladderN_init hloc
  step m g hm := by
    match m, hm with
    | 1, _ =>
      change highNorm (rungWeight ko kh 1) (traj Gs θ O (g + 1))
        ≤ highNorm (rungWeight ko kh 1) (traj Gs θ O g) + c 1 * pauliNorm (traj Gs θ O g)
      rw [traj_succ]
      exact le_trans (highNorm_conj_le_pauliNorm (hG g) (θ g) (traj Gs θ O g))
        (add_le_add le_rfl (mul_le_mul_of_nonneg_right (hc g 1) (pauliNorm_nonneg _)))
    | (m + 2), _ =>
      change highNorm (rungWeight ko kh (m + 2)) (traj Gs θ O (g + 1))
        ≤ highNorm (rungWeight ko kh (m + 2)) (traj Gs θ O g)
          + c (m + 2) * highNorm (rungWeight ko kh (m + 1)) (traj Gs θ O g)
      rw [traj_succ]
      exact le_trans
        (highNorm_conj_le_highNorm (w := rungWeight ko kh (m + 2))
          (w' := rungWeight ko kh (m + 1)) (hG g) (hk g)
          (rungWeight_add_two ko kh m).ge (θ g) (traj Gs θ O g))
        (add_le_add le_rfl
          (mul_le_mul_of_nonneg_right (hc g (m + 2)) (highNorm_nonneg _ _)))
noncomputable def pauliLadderOfHerm {Gs : ℕ → PauliString n} {θ : ℕ → ℝ} {kh : ℕ} {a : ℝ}
    (hG : ∀ g, IsSelfAdjoint (Gs g)) (hk : ∀ g, weight (Gs g) ≤ kh)
    (ha : ∀ g, |Real.sin (θ g)| ≤ a) (q : PauliIndex n) :
    Ladder a (pauliNorm (toMatrix (herm q))) :=
  pauliLadder (ko := wt q) hG hk ha fun _ hp => coeff_toMatrix_herm_eq_zero hp
noncomputable example (dt : ℝ) : Ladder |Real.sin dt| (pauliNorm (toMatrix Z1)) := by
  have hz : herm (cls Z1) = Z1 := by decide
  refine hz ▸ pauliLadderOfHerm (Gs := fun _ => X1) (θ := fun _ => dt) (kh := 1)
    (fun _ => isSelfAdjoint_X1) (fun _ => ?_) (fun _ => le_rfl) (cls Z1)
  decide
end PauliString
end Lean4LPD


