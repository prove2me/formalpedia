-- Prove2me | Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Count
-- name    : LeanPool_LowWeightPauliDynamics_Pauli_Count
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T07:25:37.963107+00:00
-- url     : https://prove2.me/theorems/c5ee9d76-715e-459f-aaf5-be93c5d013e5
-- title:
--   Count
-- statement:
--   Definitions and structural lemmas for Count, from Jue Xu; LeanPool contributors's pinned Low-weight Pauli dynamics and truncation error development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LowWeightPauliDynamics/Pauli/Count.lean

module
public import Definitions.Def_LeanPool_LowWeightPauliDynamics_Pauli_Coeff
public import Theorems.Thm_Lean4LPD_PauliString_cls_fst
public import Theorems.Thm_Lean4LPD_PauliString_cls_herm
public import Theorems.Thm_Lean4LPD_PauliString_cls_snd
public import Theorems.Thm_Lean4LPD_PauliString_coeffVec_apply
public import Theorems.Thm_Lean4LPD_PauliString_herm_x
public import Theorems.Thm_Lean4LPD_PauliString_herm_z
public import Theorems.Thm_Lean4LPD_PauliString_mem_antiSites
public import Theorems.Thm_Lean4LPD_PauliString_mem_highSet
public import Theorems.Thm_Lean4LPD_PauliString_mem_support
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
attribute [local simp] Lean4LPD.star_negOnePow


set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace Lean4LPD.PauliString
open Finset
variable {n : ℕ}
def lowSet (n w : ℕ) : Finset (PauliIndex n) := (highSet n w)ᶜ
@[simp] lemma mem_lowSet {w : ℕ} {p : PauliIndex n} : p ∈ lowSet n w ↔ wt p ≤ w := by
  simp [lowSet]
def siteFun (p : PauliIndex n) : Fin n → ZMod 2 × ZMod 2 := fun i => (p.1 i, p.2 i)
def siteEquiv : PauliIndex n ≃ (Fin n → ZMod 2 × ZMod 2) where
  toFun := siteFun
  invFun f := (fun i => (f i).1, fun i => (f i).2)
  left_inv _ := rfl
  right_inv _ := funext fun _ => rfl
def psupp (p : PauliIndex n) : Finset (Fin n) := univ.filter fun i => siteFun p i ≠ 0
lemma wt_eq_card_psupp (p : PauliIndex n) : wt p = (psupp p).card := rfl
@[simp] lemma mem_psupp {p : PauliIndex n} {i : Fin n} : i ∈ psupp p ↔ siteFun p i ≠ 0 := by
  simp [psupp]
def vanishOff (S : Finset (Fin n)) : Finset (PauliIndex n) :=
  univ.filter fun p => ∀ i ∉ S, siteFun p i = 0
lemma card_vanishOff (S : Finset (Fin n)) : (vanishOff S).card = 4 ^ S.card := by
  classical
  have himg : vanishOff S
      = (Fintype.piFinset fun i => if i ∈ S then (univ : Finset (ZMod 2 × ZMod 2)) else {0}).image
          siteEquiv.symm := by
    ext p
    simp only [vanishOff, mem_filter, mem_univ, true_and, mem_image, Fintype.mem_piFinset]
    constructor
    · intro h
      refine ⟨siteFun p, fun i => ?_, siteEquiv.left_inv p⟩
      by_cases hi : i ∈ S
      · simp [hi]
      · simp [hi, h i hi]
    · rintro ⟨f, hf, rfl⟩ i hi
      have hfi := hf i
      simp only [hi, ite_false, mem_singleton] at hfi
      have : siteFun (siteEquiv.symm f) i = f i := rfl
      rw [this, hfi]
  rw [himg, card_image_of_injective _ siteEquiv.symm.injective, Fintype.card_piFinset]
  have hcard : ∀ i : Fin n,
      (if i ∈ S then (univ : Finset (ZMod 2 × ZMod 2)) else {0}).card = if i ∈ S then 4 else 1 := by
    intro i; by_cases hi : i ∈ S <;> simp [hi]
  rw [Finset.prod_congr rfl fun i _ => hcard i, Finset.prod_ite_mem]
  simp
theorem card_lowSet_le (n w : ℕ) (hw : w ≤ n) :
    (lowSet n w).card ≤ n.choose w * 4 ^ w := by
  classical
  have hsub : lowSet n w ⊆ (univ.powersetCard w).biUnion vanishOff := by
    intro p hp
    have hcard : (psupp p).card ≤ w := by
      rw [← wt_eq_card_psupp]; exact mem_lowSet.1 hp
    obtain ⟨S, hPS, -, hScard⟩ :=
      Finset.exists_subsuperset_card_eq (Finset.subset_univ (psupp p)) hcard (by simpa using hw)
    refine mem_biUnion.2 ⟨S, mem_powersetCard.2 ⟨Finset.subset_univ S, hScard⟩, ?_⟩
    simp only [vanishOff, mem_filter, mem_univ, true_and]
    intro i hi
    by_contra hne
    exact hi (hPS (mem_psupp.2 hne))
  calc (lowSet n w).card
      ≤ ((univ.powersetCard w).biUnion vanishOff).card := card_le_card hsub
    _ ≤ ∑ S ∈ univ.powersetCard w, (vanishOff S).card := card_biUnion_le
    _ = n.choose w * 4 ^ w := by
        rw [Finset.sum_congr rfl fun S hS => by
              rw [card_vanishOff, (mem_powersetCard.1 hS).2]]
        rw [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin,
          smul_eq_mul]
example : (lowSet 2 1).card = 7 := by decide
example : (lowSet 2 1).card ≤ Nat.choose 2 1 * 4 ^ 1 := card_lowSet_le 2 1 (by norm_num)
example : (lowSet 2 1).card < Fintype.card (PauliIndex 2) := by decide
example : (lowSet 3 1).card = 10 := by decide
end Lean4LPD.PauliString


