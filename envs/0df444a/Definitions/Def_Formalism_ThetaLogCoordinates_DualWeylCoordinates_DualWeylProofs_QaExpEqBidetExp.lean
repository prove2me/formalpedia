-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QaExpEqBidetExp
-- name    : Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QaExpEqBidetExp
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T10:17:26.458614+00:00
-- url     : https://prove2.me/theorems/376eb001-8bd3-4115-b82b-1a6bb6fe0093
-- title:
--   Qa Exp Eq Bidet Exp
-- statement:
--   Definitions and structural lemmas for Qa Exp Eq Bidet Exp, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DualWeylProofs/QaExpEqBidetExp.lean

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QaNuAntitone
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Theorems.Thm_Formalism_GradedWeylDivisibility_bidetMem
import Theorems.Thm_Formalism_GradedWeylDivisibility_colSums
import Theorems.Thm_Formalism_GradedWeylDivisibility_column_lex_bideterminant
import Theorems.Thm_Formalism_GradedWeylDivisibility_leadInterlaced
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qa_exp_inj
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qa_exp_surj
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qa_row_strictMono
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply


set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
namespace Formalism.InvariantFactorPaths.ColumnFamilies
open Formalism.GradedWeylDivisibility
def qa_P (R : Type*) [CommRing R] {n : ℕ} [NeZero n] {mu : Fin n → ℤ} (I : TIdx mu) :
    MvPolynomial (Fin n × Fin n) R :=
  ∏ c : ↥(TCols mu), initMinor R (qa_row I c) (colH_le mu c)
def qa_e {n : ℕ} [NeZero n] (mu : Fin n → ℤ) : Fin (Fintype.card ↥(TCols mu)) ≃ ↥(TCols mu) :=
  (Fintype.equivFin ↥(TCols mu)).symm
lemma tableauBideterminant_eq_bideterminant (R : Type*) [CommRing R] {n : ℕ} [NeZero n] {mu : Fin n → ℤ} (I : TIdx mu) :
    qa_P R I = bideterminant R (fun k => colH mu (qa_e mu k)) (fun k => colH_le mu (qa_e mu k))
      (fun k => qa_row I (qa_e mu k)) := by
  unfold qa_P bideterminant
  exact (Fintype.prod_equiv (qa_e mu) _ _ (fun _ => rfl)).symm
lemma qa_exp_eq_bidetExp {n : ℕ} [NeZero n] {mu : Fin n → ℤ} (I : TIdx mu) :
    qa_exp I = bidetExp (fun k => colH mu (qa_e mu k)) (fun k => colH_le mu (qa_e mu k))
      (fun k => qa_row I (qa_e mu k)) := by
  unfold qa_exp bidetExp
  exact (Fintype.sum_equiv (qa_e mu) _ _ (fun _ => rfl)).symm
theorem lt_colH_iff_le {n : ℕ} {mu : Fin n → ℤ} (hmu : Antitone mu) (c : ℤ) (t : Fin n) :
    (t : ℕ) < colH mu c ↔ c ≤ mu t := by
  unfold colH
  constructor
  · intro h
    by_contra hc
    push_neg at hc
    have hsub : (Finset.univ.filter fun m : Fin n => c ≤ mu m) ⊆ Finset.Iio t := by
      intro m hm
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hm
      rw [Finset.mem_Iio]
      by_contra hmt
      push_neg at hmt
      have := hmu hmt
      omega
    exact absurd (lt_of_lt_of_le h ((Finset.card_le_card hsub).trans (Fin.card_Iio t).le)) (lt_irrefl _)
  · intro h
    have hsub : Finset.Iic t ⊆ (Finset.univ.filter fun m : Fin n => c ≤ mu m) := by
      intro m hm
      rw [Finset.mem_Iic] at hm
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact h.trans (hmu hm)
    exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) ((Fin.card_Iic t).symm.le.trans (Finset.card_le_card hsub))
lemma qa_shape {n : ℕ} [NeZero n] {mu : Fin n → ℤ} (hmu : Dominant mu) :
    shapeDeg (n := n) (fun k => colH mu (qa_e mu k)) = qa_nu mu := by
  have hmu' : Antitone mu := hmu
  funext t
  unfold shapeDeg qa_nu
  have h1 : (Finset.univ.filter fun k => (t : ℕ) < colH mu ↑(qa_e mu k)).card =
      (Finset.univ.filter fun c : ↥(TCols mu) => (t : ℕ) < colH mu ↑c).card :=
    Finset.card_equiv (qa_e mu) (by simp)
  have h2 : (Finset.univ.filter fun c : ↥(TCols mu) => (t : ℕ) < colH mu ↑c).card =
      ((TCols mu).filter fun c => (t : ℕ) < colH mu c).card := by
    rw [Finset.card_filter, Finset.card_filter]
    exact Finset.sum_coe_sort (TCols mu) (fun c => if (t : ℕ) < colH mu c then 1 else 0)
  have h3 : ((TCols mu).filter fun c => (t : ℕ) < colH mu c) = Finset.Ioc (mu (lastIdx n)) (mu t) := by
    ext c
    have h0 : mu t ≤ mu 0 := hmu' (by simp [Fin.le_iff_val_le_val])
    simp only [TCols, Finset.mem_filter, Finset.mem_Ioc, lt_colH_iff_le hmu']
    constructor <;> intro h <;> omega
  exact h1.trans (h2.trans (by rw [h3, Int.card_Ioc]))
lemma tableauBideterminant_degree_leadingCoeff (R : Type) [CommRing R] [Nontrivial R] {n : ℕ} [NeZero n] {mu : Fin n → ℤ} (I : TIdx mu) :
    (colLex n n).degree (qa_P R I) = qa_exp I ∧ (colLex n n).leadingCoeff (qa_P R I) = 1 := by
  rw [tableauBideterminant_eq_bideterminant, qa_exp_eq_bidetExp]
  exact column_lex_bideterminant R n n _ _ _ _ fun k => qa_row_strictMono I _
lemma tableauBideterminant_mem_dualWeyl (R : Type) [CommRing R] {n : ℕ} [NeZero n] {mu : Fin n → ℤ} (hmu : Dominant mu) (I : TIdx mu) :
    qa_P R I ∈ dualWeyl R n n (qa_nu mu) := by
  rw [tableauBideterminant_eq_bideterminant, ← qa_shape hmu]
  exact bidetMem R n n _ _ _ _
lemma tableauBideterminant_ne_zero (R : Type) [CommRing R] [Nontrivial R] {n : ℕ} [NeZero n] {mu : Fin n → ℤ} (I : TIdx mu) :
    qa_P R I ≠ 0 := by
  intro h
  have := (tableauBideterminant_degree_leadingCoeff R I).2
  rw [h] at this
  simp at this
lemma qa_exp_mem {n : ℕ} [NeZero n] {mu : Fin n → ℤ} (hmu : Dominant mu) (I : TIdx mu) :
    qa_exp I ∈ ssIdx n n (qa_nu mu) := by
  have h1 := leadInterlaced ℤ n n (qa_nu mu) (qa_P ℤ I) (tableauBideterminant_mem_dualWeyl ℤ hmu I) (tableauBideterminant_ne_zero ℤ I)
  have h2 := colSums ℤ n n (qa_nu mu) (qa_P ℤ I) (tableauBideterminant_mem_dualWeyl ℤ hmu I) _
    (((colLex n n).degree_mem_support_iff _).mpr (tableauBideterminant_ne_zero ℤ I))
  rw [(tableauBideterminant_degree_leadingCoeff ℤ I).1] at h1 h2
  exact ⟨h1, h2⟩
def qa_stdEquiv {n : ℕ} [NeZero n] {mu : Fin n → ℤ} (hmu : Dominant mu) :
    {I : TIdx mu // StdT I} ≃ ssIdx n n (qa_nu mu) :=
  Equiv.ofBijective (fun I => ⟨qa_exp I.1, qa_exp_mem hmu I.1⟩)
    ⟨fun I J h => Subtype.ext (qa_exp_inj I.1 J.1 I.2 J.2 (congrArg Subtype.val h)),
     fun m => by
      obtain ⟨I, hI, he⟩ := qa_exp_surj hmu m.1 m.2
      exact ⟨⟨I, hI⟩, Subtype.ext he⟩⟩
end Formalism.InvariantFactorPaths.ColumnFamilies


