-- Prove2me | solution 1 for AlgebraicCurve.pairHt_comm
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/f5dcead8-5581-559f-b55b-c6be06163ac1

import Mathlib
import Definitions.Def_ModularCurve_JZeroHeightForm
import Theorems.Thm_Height_inv_finrank_mul_logHeight_inclusion
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_pairHt_comm

set_option autoImplicit false

open AlgebraicCurve ModularCurve Finset

noncomputable section

namespace P2MQalg

variable {α : Type*}

open Classical in

noncomputable def QA (S : Finset α) (x t : α → ℝ) (bb : α × α → ℝ) (γ : ℝ) : ℝ :=
  (γ + (∑ v ∈ S, x v) - 1) * (∑ v ∈ S, x v * t v)
    - (∑ p ∈ S.offDiag, (x p.1 * x p.2) * bb p) / 2
    - (2 - 2 * γ) * (∑ v ∈ S, (x v * (x v - 1) / 2) * t v)

open Classical in

noncomputable def NF (S : Finset α) (x t : α → ℝ) (bb : α × α → ℝ) (γ : ℝ) : ℝ :=
  2 * γ * (∑ v ∈ S, x v ^ 2 * t v) + ∑ p ∈ S.offDiag, x p.1 * x p.2 * (t p.1 + t p.2 - bb p)

open Classical in
theorem sum_offDiag_eq_sub (S : Finset α) (G : α × α → ℝ) :
    ∑ p ∈ S.offDiag, G p = ∑ p ∈ S ×ˢ S, G p - ∑ p ∈ S.diag, G p := by
  rw [← Finset.diag_union_offDiag, Finset.sum_union (Finset.disjoint_diag_offDiag S)]; ring

open Classical in
theorem sum_offDiag_mul_mul_add (S : Finset α) (x t : α → ℝ) :
    ∑ p ∈ S.offDiag, x p.1 * x p.2 * (t p.1 + t p.2)
      = 2 * ((∑ v ∈ S, x v) * (∑ v ∈ S, x v * t v) - ∑ v ∈ S, x v ^ 2 * t v) := by
  rw [sum_offDiag_eq_sub, Finset.sum_product, Finset.sum_diag]
  have e1 : ∑ v ∈ S, ∑ w ∈ S, x v * x w * (t v + t w)
      = (∑ v ∈ S, x v * t v) * (∑ w ∈ S, x w) + (∑ v ∈ S, x v) * (∑ w ∈ S, x w * t w) := by
    rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun w _ => by ring
  have e2 : ∑ v ∈ S, x v * x v * (t v + t v) = 2 * ∑ v ∈ S, x v ^ 2 * t v := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun v _ => by ring
  rw [e1, e2]; ring

open Classical in
theorem two_mul_QA (S : Finset α) (x t : α → ℝ) (bb : α × α → ℝ) (γ : ℝ) :
    2 * QA S x t bb γ = NF S x t bb γ := by
  unfold QA NF
  have h3 : ∑ v ∈ S, (x v * (x v - 1) / 2) * t v
      = (∑ v ∈ S, x v ^ 2 * t v - ∑ v ∈ S, x v * t v) / 2 := by
    rw [← Finset.sum_sub_distrib, Finset.sum_div]
    exact Finset.sum_congr rfl fun v _ => by ring
  have h4 : ∑ p ∈ S.offDiag, x p.1 * x p.2 * (t p.1 + t p.2 - bb p)
      = ∑ p ∈ S.offDiag, x p.1 * x p.2 * (t p.1 + t p.2) - ∑ p ∈ S.offDiag, (x p.1 * x p.2) * bb p := by
    rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun p _ => by ring
  rw [h3, h4, sum_offDiag_mul_mul_add]
  ring

open Classical in
theorem NF_smul (S : Finset α) (x t : α → ℝ) (bb : α × α → ℝ) (γ c : ℝ) :
    NF S (fun v => c * x v) t bb γ = c ^ 2 * NF S x t bb γ := by
  unfold NF
  rw [mul_add, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  congr 1
  · exact Finset.sum_congr rfl fun v _ => by ring
  · exact Finset.sum_congr rfl fun p _ => by ring

open Classical in
theorem NF_parallelogram (S : Finset α) (x y t : α → ℝ) (bb : α × α → ℝ) (γ : ℝ) :
    NF S (fun v => x v + y v) t bb γ + NF S (fun v => x v - y v) t bb γ
      = 2 * NF S x t bb γ + 2 * NF S y t bb γ := by
  unfold NF
  have a1 : ∑ v ∈ S, (x v + y v) ^ 2 * t v + ∑ v ∈ S, (x v - y v) ^ 2 * t v
      = 2 * ∑ v ∈ S, x v ^ 2 * t v + 2 * ∑ v ∈ S, y v ^ 2 * t v := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun v _ => by ring
  have a2 : ∑ p ∈ S.offDiag, (x p.1 + y p.1) * (x p.2 + y p.2) * (t p.1 + t p.2 - bb p)
      + ∑ p ∈ S.offDiag, (x p.1 - y p.1) * (x p.2 - y p.2) * (t p.1 + t p.2 - bb p)
      = 2 * ∑ p ∈ S.offDiag, x p.1 * x p.2 * (t p.1 + t p.2 - bb p)
        + 2 * ∑ p ∈ S.offDiag, y p.1 * y p.2 * (t p.1 + t p.2 - bb p) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun p _ => by ring
  linear_combination (2 * γ) * a1 + a2

open Classical in
theorem NF_singleton (v : α) (x t : α → ℝ) (bb : α × α → ℝ) (γ : ℝ) :
    NF {v} x t bb γ = 2 * γ * (x v ^ 2 * t v) := by
  unfold NF
  simp [Finset.offDiag_singleton]

variable {F : Type} [Field F] [Algebra (AlgebraicClosure ℚ) F]

open Classical in
theorem heightFormAux_eq_QA {r : ℕ} (s : Fin r → F) (γ : ℤ) (b : Place (AlgebraicClosure ℚ) F)
    (D : Divisor (AlgebraicClosure ℚ) F) (S : Finset (Place (AlgebraicClosure ℚ) F))
    (hS : D.support ⊆ S) :
    heightFormAux s γ b D = QA S (fun v => (D v : ℝ)) (baseHt s b) (fun p => pairHt s p.1 p.2) (γ : ℝ) := by
  unfold heightFormAux QA
  rw [Finsupp.sum_of_support_subset D hS (fun _ n => (n : ℝ)) (by intros; simp),
      Finsupp.sum_of_support_subset D hS (fun v n => (n : ℝ) * baseHt s b v) (by intros; simp),
      Finsupp.sum_of_support_subset D hS (fun v n => ((n : ℝ) * ((n : ℝ) - 1) / 2) * baseHt s b v)
        (by intros; simp)]
  rw [Finset.sum_subset (Finset.offDiag_mono hS)
        (f := fun p => ((D p.1 : ℝ) * (D p.2 : ℝ)) * pairHt s p.1 p.2) ?_]
  intro p hp hnp
  rw [Finset.mem_offDiag] at hp hnp
  have : D p.1 = 0 ∨ D p.2 = 0 := by
    by_contra h
    push Not at h
    exact hnp ⟨Finsupp.mem_support_iff.mpr h.1, Finsupp.mem_support_iff.mpr h.2, hp.2.2⟩
  rcases this with h | h <;> simp [h]

open Classical in

theorem two_mul_heightForm_eq_NF {r : ℕ} (s : Fin r → F) (γ : ℤ) (b : Place (AlgebraicClosure ℚ) F)
    (D : Divisor (AlgebraicClosure ℚ) F) (S : Finset (Place (AlgebraicClosure ℚ) F))
    (hS : (D.erase b).support ⊆ S) :
    2 * heightForm s γ b D
      = NF S (fun v => ((D.erase b) v : ℝ)) (baseHt s b) (fun p => pairHt s p.1 p.2) (γ : ℝ) := by
  unfold heightForm
  rw [heightFormAux_eq_QA s γ b _ S hS, two_mul_QA]

theorem erase_zsmul (b : Place (AlgebraicClosure ℚ) F) (m : ℤ) (D : Divisor (AlgebraicClosure ℚ) F) :
    (m • D).erase b = m • D.erase b := by
  ext v
  by_cases hv : v = b
  · subst hv; simp
  · simp [Finsupp.erase_ne hv]

variable {F : Type} [Field F] [Algebra (AlgebraicClosure ℚ) F]

theorem heightForm_zsmul {r : ℕ} (s : Fin r → F) (γ : ℤ) (b : Place (AlgebraicClosure ℚ) F)
    (m : ℤ) (D : Divisor (AlgebraicClosure ℚ) F) :
    heightForm s γ b (m • D) = (m : ℝ) ^ 2 * heightForm s γ b D := by
  classical
  have hS : ((m • D).erase b).support ⊆ (D.erase b).support := by
    rw [P2MQalg.erase_zsmul]; exact Finsupp.support_smul
  have h1 := P2MQalg.two_mul_heightForm_eq_NF s γ b (m • D) _ hS
  have h2 := P2MQalg.two_mul_heightForm_eq_NF s γ b D _ subset_rfl
  have hfun : (fun v => (((m • D).erase b) v : ℝ)) = fun v => (m : ℝ) * ((D.erase b) v : ℝ) := by
    funext v; rw [P2MQalg.erase_zsmul]; simp
  rw [hfun, P2MQalg.NF_smul, ← h2] at h1
  linarith

theorem heightForm_add_add_heightForm_sub {r : ℕ} (s : Fin r → F) (γ : ℤ)
    (b : Place (AlgebraicClosure ℚ) F) (D E : Divisor (AlgebraicClosure ℚ) F) :
    heightForm s γ b (D + E) + heightForm s γ b (D - E)
      = 2 * heightForm s γ b D + 2 * heightForm s γ b E := by
  classical
  set S := (D.erase b).support ∪ (E.erase b).support with hSdef
  have hD : (D.erase b).support ⊆ S := Finset.subset_union_left
  have hE : (E.erase b).support ⊆ S := Finset.subset_union_right
  have hDE : ((D + E).erase b).support ⊆ S := by
    rw [Finsupp.erase_add]; exact Finsupp.support_add.trans (Finset.union_subset hD hE)
  have hDE' : ((D - E).erase b).support ⊆ S := by
    rw [Finsupp.erase_sub]; exact Finsupp.support_sub.trans (Finset.union_subset hD hE)
  have h1 := P2MQalg.two_mul_heightForm_eq_NF s γ b (D + E) S hDE
  have h2 := P2MQalg.two_mul_heightForm_eq_NF s γ b (D - E) S hDE'
  have h3 := P2MQalg.two_mul_heightForm_eq_NF s γ b D S hD
  have h4 := P2MQalg.two_mul_heightForm_eq_NF s γ b E S hE
  have f1 : (fun v => (((D + E).erase b) v : ℝ)) = fun v => ((D.erase b) v : ℝ) + ((E.erase b) v : ℝ) := by
    funext v; rw [Finsupp.erase_add]; simp
  have f2 : (fun v => (((D - E).erase b) v : ℝ)) = fun v => ((D.erase b) v : ℝ) - ((E.erase b) v : ℝ) := by
    funext v; rw [Finsupp.erase_sub]; simp
  rw [f1] at h1; rw [f2] at h2
  have key := P2MQalg.NF_parallelogram S (fun v => ((D.erase b) v : ℝ)) (fun v => ((E.erase b) v : ℝ))
    (baseHt s b) (fun p => pairHt s p.1 p.2) (γ : ℝ)
  linarith

theorem heightForm_single {r : ℕ} (s : Fin r → F) (γ : ℤ) (b : Place (AlgebraicClosure ℚ) F)
    {v : Place (AlgebraicClosure ℚ) F} (hv : v ≠ b) (n : ℤ) :
    heightForm s γ b (Finsupp.single v n) = (γ : ℝ) * (n : ℝ) ^ 2 * baseHt s b v := by
  classical
  have he : (Finsupp.single v n).erase b = Finsupp.single v n := Finsupp.erase_single_ne (Ne.symm hv)
  have hS : ((Finsupp.single v n).erase b).support ⊆ {v} := by
    rw [he]; exact Finsupp.support_single_subset
  have h1 := P2MQalg.two_mul_heightForm_eq_NF s γ b (Finsupp.single v n) {v} hS
  rw [P2MQalg.NF_singleton, he, Finsupp.single_eq_same] at h1
  linarith

variable {F : Type} [Field F] [Algebra (AlgebraicClosure ℚ) F]

theorem absLogHeight_nonneg {ι : Type} [Fintype ι] (x : ι → AlgebraicClosure ℚ) :
    0 ≤ absLogHeight x := by
  haveI := finiteDimensional_adjoin_range x
  unfold absLogHeight
  exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (Height.logHeight_nonneg _)

theorem pointHt_nonneg {r : ℕ} (s : Fin r → F) (v : Place (AlgebraicClosure ℚ) F) :
    0 ≤ pointHt s v :=
  absLogHeight_nonneg _

theorem baseHt_le_pointHt_add_pointHt {r : ℕ} (s : Fin r → F) (b v : Place (AlgebraicClosure ℚ) F) :
    baseHt s b v ≤ pointHt s v + pointHt s b := by
  unfold baseHt
  split_ifs with h
  · exact add_nonneg (pointHt_nonneg s v) (pointHt_nonneg s b)
  · unfold pairHt
    linarith [absLogHeight_nonneg (chordVec s v b)]

end P2MQalg

namespace P2MQalg

theorem absLogHeight_eq_of_mem {ι : Type} [Fintype ι] (x : ι → AlgebraicClosure ℚ)
    (E' : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ E'] (h : ∀ i, x i ∈ E') :
    absLogHeight x = (Module.finrank ℚ E' : ℝ)⁻¹ * Height.logHeight (fun i => (⟨x i, h i⟩ : E')) := by
  have hle : IntermediateField.adjoin ℚ (Set.range x) ≤ E' :=
    IntermediateField.adjoin_le_iff.mpr (by rintro _ ⟨i, rfl⟩; exact h i)
  haveI := finiteDimensional_adjoin_range x
  unfold absLogHeight
  exact (Height.inv_finrank_mul_logHeight_inclusion (K := IntermediateField.adjoin ℚ (Set.range x))
    (L := E') hle (fun i => ⟨x i, IntermediateField.subset_adjoin ℚ _ ⟨i, rfl⟩⟩)).symm

theorem absLogHeight_neg {ι : Type} [Fintype ι] (x : ι → AlgebraicClosure ℚ) :
    absLogHeight (-x) = absLogHeight x := by
  haveI := finiteDimensional_adjoin_range x
  have hx : ∀ i, x i ∈ IntermediateField.adjoin ℚ (Set.range x) :=
    fun i => IntermediateField.subset_adjoin ℚ _ ⟨i, rfl⟩
  have hnx : ∀ i, (-x) i ∈ IntermediateField.adjoin ℚ (Set.range x) :=
    fun i => by simpa using neg_mem (hx i)
  rw [absLogHeight_eq_of_mem (-x) _ hnx, absLogHeight_eq_of_mem x _ hx]
  congr 1
  have : (fun i => (⟨(-x) i, hnx i⟩ : IntermediateField.adjoin ℚ (Set.range x)))
      = -(fun i => (⟨x i, hx i⟩ : IntermediateField.adjoin ℚ (Set.range x))) := by
    funext i; apply Subtype.ext; simp
  rw [this, Height.logHeight_neg]

variable {F : Type} [Field F] [Algebra (AlgebraicClosure ℚ) F]

theorem chordVec_swap {r : ℕ} (s : Fin r → F) (v w : Place (AlgebraicClosure ℚ) F) :
    chordVec s w v = -chordVec s v w := by
  funext p; simp only [chordVec, Pi.neg_apply]; ring

theorem pairHt_comm {r : ℕ} (s : Fin r → F) (v w : Place (AlgebraicClosure ℚ) F) :
    pairHt s v w = pairHt s w v := by
  unfold pairHt
  rw [P2MQalg.chordVec_swap s v w, P2MQalg.absLogHeight_neg]
  ring

variable {α : Type*}

open Classical in
theorem sum_offDiag_eq_sum_erase (S : Finset α) (G : α × α → ℝ) :
    ∑ p ∈ S.offDiag, G p = ∑ v ∈ S, ∑ w ∈ S.erase v, G (v, w) := by
  rw [sum_offDiag_eq_sub, Finset.sum_product, Finset.sum_diag, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun v hv => ?_
  rw [Finset.sum_erase_eq_sub hv]

open Classical in

theorem NF_add (S : Finset α) (x y t : α → ℝ) (bb : α × α → ℝ) (γ : ℝ)
    (hbb : ∀ p ∈ S.offDiag, bb p = bb p.swap) :
    NF S (fun v => x v + y v) t bb γ
      = NF S x t bb γ + NF S y t bb γ
        + 2 * (2 * γ * ∑ v ∈ S, x v * y v * t v
               + ∑ p ∈ S.offDiag, x p.1 * y p.2 * (t p.1 + t p.2 - bb p)) := by
  unfold NF
  have hswap : ∑ p ∈ S.offDiag, y p.1 * x p.2 * (t p.1 + t p.2 - bb p)
      = ∑ p ∈ S.offDiag, x p.1 * y p.2 * (t p.1 + t p.2 - bb p) := by
    refine Finset.sum_nbij' Prod.swap Prod.swap ?_ ?_ ?_ ?_ ?_
    · intro p hp
      simp only [Finset.mem_offDiag] at hp ⊢
      exact ⟨hp.2.1, hp.1, Ne.symm hp.2.2⟩
    · intro p hp
      simp only [Finset.mem_offDiag] at hp ⊢
      exact ⟨hp.2.1, hp.1, Ne.symm hp.2.2⟩
    · intro p _; simp
    · intro p _; simp
    · intro p hp
      rw [hbb p hp]; simp only [Prod.fst_swap, Prod.snd_swap]; ring
  have a1 : ∑ v ∈ S, (x v + y v) ^ 2 * t v
      = ∑ v ∈ S, x v ^ 2 * t v + ∑ v ∈ S, y v ^ 2 * t v + 2 * ∑ v ∈ S, x v * y v * t v := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun v _ => by ring
  have a2 : ∑ p ∈ S.offDiag, (x p.1 + y p.1) * (x p.2 + y p.2) * (t p.1 + t p.2 - bb p)
      = ∑ p ∈ S.offDiag, x p.1 * x p.2 * (t p.1 + t p.2 - bb p)
        + ∑ p ∈ S.offDiag, y p.1 * y p.2 * (t p.1 + t p.2 - bb p)
        + (∑ p ∈ S.offDiag, x p.1 * y p.2 * (t p.1 + t p.2 - bb p)
           + ∑ p ∈ S.offDiag, y p.1 * x p.2 * (t p.1 + t p.2 - bb p)) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun p _ => by ring
  rw [a1, a2, hswap]; ring

variable {F : Type} [Field F] [Algebra (AlgebraicClosure ℚ) F]

theorem heightForm_add {r : ℕ} (s : Fin r → F) (γ : ℤ) (b : Place (AlgebraicClosure ℚ) F)
    (D E : Divisor (AlgebraicClosure ℚ) F) :
    heightForm s γ b (D + E) = heightForm s γ b D + heightForm s γ b E
      + 2 * (γ : ℝ) * ((D.erase b).sum fun v m => (m : ℝ) * ((E.erase b) v : ℝ) * baseHt s b v)
      + ((D.erase b).sum fun v m => ((E.erase b).erase v).sum fun w k =>
          (m : ℝ) * (k : ℝ) * (baseHt s b v + baseHt s b w - pairHt s v w)) := by
  classical
  set S := (D.erase b).support ∪ (E.erase b).support with hSdef
  have hD : (D.erase b).support ⊆ S := Finset.subset_union_left
  have hE : (E.erase b).support ⊆ S := Finset.subset_union_right
  have hDE : ((D + E).erase b).support ⊆ S := by
    rw [Finsupp.erase_add]; exact Finsupp.support_add.trans (Finset.union_subset hD hE)
  have h1 := P2MQalg.two_mul_heightForm_eq_NF s γ b (D + E) S hDE
  have h3 := P2MQalg.two_mul_heightForm_eq_NF s γ b D S hD
  have h4 := P2MQalg.two_mul_heightForm_eq_NF s γ b E S hE
  have f1 : (fun v => (((D + E).erase b) v : ℝ)) = fun v => ((D.erase b) v : ℝ) + ((E.erase b) v : ℝ) := by
    funext v; rw [Finsupp.erase_add]; simp
  rw [f1, P2MQalg.NF_add S _ _ (baseHt s b) (fun p => pairHt s p.1 p.2) (γ : ℝ)
    (fun p _ => pairHt_comm s p.1 p.2)] at h1
  have g1 : ((D.erase b).sum fun v m => (m : ℝ) * ((E.erase b) v : ℝ) * baseHt s b v)
      = ∑ v ∈ S, ((D.erase b) v : ℝ) * ((E.erase b) v : ℝ) * baseHt s b v :=
    Finsupp.sum_of_support_subset _ hD _ (by intros; simp)
  have g2 : ((D.erase b).sum fun v m => ((E.erase b).erase v).sum fun w k =>
        (m : ℝ) * (k : ℝ) * (baseHt s b v + baseHt s b w - pairHt s v w))
      = ∑ p ∈ S.offDiag, ((D.erase b) p.1 : ℝ) * ((E.erase b) p.2 : ℝ)
          * (baseHt s b p.1 + baseHt s b p.2 - pairHt s p.1 p.2) := by
    rw [Finsupp.sum_of_support_subset _ hD _ (by intros; simp [Finsupp.sum]),
      P2MQalg.sum_offDiag_eq_sum_erase]
    refine Finset.sum_congr rfl fun v _ => ?_
    have hEv : ((E.erase b).erase v).support ⊆ S.erase v := by
      rw [Finsupp.support_erase]; exact Finset.erase_subset_erase v hE
    rw [Finsupp.sum_of_support_subset _ hEv _ (by intros; simp)]
    exact Finset.sum_congr rfl fun w hw => by rw [Finsupp.erase_ne (Finset.ne_of_mem_erase hw)]
  rw [g1, g2]
  linarith

theorem heightForm_add_single {r : ℕ} (s : Fin r → F) (γ : ℤ) (b : Place (AlgebraicClosure ℚ) F)
    (D : Divisor (AlgebraicClosure ℚ) F) {v : Place (AlgebraicClosure ℚ) F} (hv : v ≠ b) :
    heightForm s γ b (D + Finsupp.single v 1)
      = heightForm s γ b D + (γ : ℝ) * (2 * (D v : ℝ) + 1) * baseHt s b v
        + (((D.erase b).erase v).sum fun w m => (m : ℝ) * (baseHt s b v + baseHt s b w - pairHt s v w)) := by
  classical
  rw [heightForm_add, heightForm_single s γ b hv 1, Finsupp.erase_single_ne (Ne.symm hv)]
  have hDv : (D.erase b) v = D v := Finsupp.erase_ne hv

  have t1 : ((D.erase b).sum fun u m => (m : ℝ) * ((Finsupp.single v (1 : ℤ)) u : ℝ) * baseHt s b u)
      = (D v : ℝ) * baseHt s b v := by
    unfold Finsupp.sum
    rw [Finset.sum_eq_single v]
    · simp [hDv]
    · intro u _ huv; simp [Ne.symm huv]
    · intro hv'; simp [Finsupp.notMem_support_iff.mp hv']

  have t2 : ((D.erase b).sum fun u m => ((Finsupp.single v (1 : ℤ)).erase u).sum fun w k =>
        (m : ℝ) * (k : ℝ) * (baseHt s b u + baseHt s b w - pairHt s u w))
      = ((D.erase b).erase v).sum fun w m => (m : ℝ) * (baseHt s b v + baseHt s b w - pairHt s v w) := by
    rw [Finsupp.sum, Finsupp.sum, Finsupp.support_erase]
    symm
    refine (Finset.sum_congr rfl fun u hu => ?_).trans
      (Finset.sum_subset (Finset.erase_subset v _) fun u hu hu' => ?_)
    · have huv : u ≠ v := Finset.ne_of_mem_erase hu
      rw [Finsupp.erase_ne huv, Finsupp.erase_single_ne huv, Finsupp.sum_single_index (by simp),
        pairHt_comm s u v]
      push_cast; ring
    · have huv : u = v := by
        by_contra h; exact hu' (Finset.mem_erase.mpr ⟨h, hu⟩)
      subst huv
      rw [Finsupp.erase_single, Finsupp.sum_zero_index]
  rw [t1, t2]; push_cast; ring

end P2MQalg

end

theorem solution {F : Type} [Field F] [Algebra (AlgebraicClosure ℚ) F] {r : ℕ} (s : Fin r → F) (v w : Place (AlgebraicClosure ℚ) F) :
    pairHt s v w = pairHt s w v :=
  P2MQalg.pairHt_comm s v w

end S_AlgebraicCurve_pairHt_comm
end P2MW
export P2MW.S_AlgebraicCurve_pairHt_comm (solution)
