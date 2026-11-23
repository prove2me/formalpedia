-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwoBlockPoint
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_TwoBlockPoint
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T18:20:59.641551+00:00
-- url     : https://prove2.me/theorems/eb0943a5-15d3-4f8a-ade0-61f4fc52792b
-- title:
--   Two Block Point
-- statement:
--   Definitions and structural lemmas for Two Block Point, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TwoBlockPoint.lean

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ModulusLocallyConstant
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_fib
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_gl_coe
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_left_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_m_ext
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_mem_int
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_right_eq
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


set_option autoImplicit false
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6
open scoped ComplexConjugate
open Formalism.FourierDecayAlt.P.A5x8 (sec_m sec_m_ext sec_gl sec_gl_coe sec_fib sec_right_eq sec_left_eq sec_mem_int toCos)
noncomputable section
namespace Formalism.FourierDecayAlt.P.TwoBlockPoint
section GlobalTheory
variable {K : Type} [CommRing K] {a s N : ℕ}
def eN (hN : N = a + s) : Fin a ⊕ Fin s ≃ Fin N := finSumFinEquiv.trans (finCongr hN.symm)
theorem eN_inl (hN : N = a + s) (i : Fin a) : ((eN hN (Sum.inl i) : Fin N) : ℕ) = i := by
  first
    | simp [eN]
    | rfl
theorem eN_inr (hN : N = a + s) (i : Fin s) : ((eN hN (Sum.inr i) : Fin N) : ℕ) = a + i := by
  first
    | simp [eN]
    | rfl
def blkM (hN : N = a + s) (A : Matrix (Fin a) (Fin a) K) (B : Matrix (Fin a) (Fin s) K)
    (C : Matrix (Fin s) (Fin a) K) (D : Matrix (Fin s) (Fin s) K) : Matrix (Fin N) (Fin N) K :=
  (fromBlocks A B C D).submatrix (eN hN).symm (eN hN).symm
variable (hN : N = a + s) (A A' : Matrix (Fin a) (Fin a) K) (B B' : Matrix (Fin a) (Fin s) K)
    (C C' : Matrix (Fin s) (Fin a) K) (D D' : Matrix (Fin s) (Fin s) K)
theorem blkM_ll (i j : Fin a) : blkM hN A B C D (eN hN (Sum.inl i)) (eN hN (Sum.inl j)) = A i j := by
  simp [blkM]
theorem blkM_lr (i : Fin a) (j : Fin s) :
    blkM hN A B C D (eN hN (Sum.inl i)) (eN hN (Sum.inr j)) = B i j := by
  simp [blkM]
theorem blkM_rl (i : Fin s) (j : Fin a) :
    blkM hN A B C D (eN hN (Sum.inr i)) (eN hN (Sum.inl j)) = C i j := by
  simp [blkM]
theorem blkM_rr (i j : Fin s) : blkM hN A B C D (eN hN (Sum.inr i)) (eN hN (Sum.inr j)) = D i j := by
  simp [blkM]
theorem eq_blkM (M : Matrix (Fin N) (Fin N) K) :
    M = blkM hN (Matrix.of fun i j => M (eN hN (Sum.inl i)) (eN hN (Sum.inl j)))
      (Matrix.of fun i j => M (eN hN (Sum.inl i)) (eN hN (Sum.inr j)))
      (Matrix.of fun i j => M (eN hN (Sum.inr i)) (eN hN (Sum.inl j)))
      (Matrix.of fun i j => M (eN hN (Sum.inr i)) (eN hN (Sum.inr j))) := by
  ext x y
  obtain ⟨p, rfl⟩ := (eN hN).surjective x
  obtain ⟨q, rfl⟩ := (eN hN).surjective y
  rcases p with p | p <;> rcases q with q | q <;> simp [blkM]
variable {A A' B B' C C' D D'} in
theorem blkM_inj (h : blkM hN A B C D = blkM hN A' B' C' D') :
    A = A' ∧ B = B' ∧ C = C' ∧ D = D' := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ext i j
  · simpa [blkM] using congrFun (congrFun h (eN hN (Sum.inl i))) (eN hN (Sum.inl j))
  · simpa [blkM] using congrFun (congrFun h (eN hN (Sum.inl i))) (eN hN (Sum.inr j))
  · simpa [blkM] using congrFun (congrFun h (eN hN (Sum.inr i))) (eN hN (Sum.inl j))
  · simpa [blkM] using congrFun (congrFun h (eN hN (Sum.inr i))) (eN hN (Sum.inr j))
theorem blkM_mul : blkM hN A B C D * blkM hN A' B' C' D' =
    blkM hN (A * A' + B * C') (A * B' + B * D') (C * A' + D * C') (C * B' + D * D') := by
  unfold blkM
  rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
theorem eN_ll_lt (i j : Fin a) : eN hN (Sum.inl i) < eN hN (Sum.inl j) ↔ i < j := by
  rw [Fin.lt_iff_val_lt_val, Fin.lt_iff_val_lt_val, eN_inl, eN_inl]
theorem eN_rr_lt (i j : Fin s) : eN hN (Sum.inr i) < eN hN (Sum.inr j) ↔ i < j := by
  rw [Fin.lt_iff_val_lt_val, Fin.lt_iff_val_lt_val, eN_inr, eN_inr]
  omega
theorem eN_lr_lt (i : Fin a) (j : Fin s) : eN hN (Sum.inl i) < eN hN (Sum.inr j) := by
  rw [Fin.lt_iff_val_lt_val, eN_inl, eN_inr]
  have := i.isLt
  omega
lemma lowTri_lemma {n : ℕ} (M : Matrix (Fin n) (Fin n) K) :
    M.IsLowerTriangular ↔ ∀ i j, i < j → M i j = 0 :=
  ⟨fun h i j hij => h hij, fun h i j hij => h i j hij⟩
theorem blkM_isLowUni : IsLowUni (blkM hN A B C D) ↔ IsLowUni A ∧ B = 0 ∧ IsLowUni D := by
  simp only [IsLowUni, lowTri_lemma]
  constructor
  · rintro ⟨hL, hD⟩
    refine ⟨⟨fun i j hij => ?_, fun i => ?_⟩, ?_, fun i j hij => ?_, fun i => ?_⟩
    · simpa [blkM_ll] using hL _ _ ((eN_ll_lt hN i j).2 hij)
    · simpa [blkM_ll] using hD (eN hN (Sum.inl i))
    · ext i j
      simpa [blkM_lr] using hL _ _ (eN_lr_lt hN i j)
    · simpa [blkM_rr] using hL _ _ ((eN_rr_lt hN i j).2 hij)
    · simpa [blkM_rr] using hD (eN hN (Sum.inr i))
  · rintro ⟨⟨hA, hA1⟩, rfl, hD, hD1⟩
    refine ⟨fun x y hxy => ?_, fun x => ?_⟩
    · obtain ⟨p, rfl⟩ := (eN hN).surjective x
      obtain ⟨q, rfl⟩ := (eN hN).surjective y
      rcases p with i | i <;> rcases q with j | j
      · rw [blkM_ll]
        exact hA i j ((eN_ll_lt hN i j).1 hxy)
      · simp [blkM_lr]
      · exact absurd hxy (not_lt.2 (eN_lr_lt hN j i).le)
      · rw [blkM_rr]
        exact hD i j ((eN_rr_lt hN i j).1 hxy)
    · obtain ⟨p, rfl⟩ := (eN hN).surjective x
      rcases p with i | i
      · rw [blkM_ll]
        exact hA1 i
      · rw [blkM_rr]
        exact hD1 i
lemma upTri_lemma {n : ℕ} (M : Matrix (Fin n) (Fin n) K) :
    M.IsUpperTriangular ↔ ∀ i j, j < i → M i j = 0 :=
  ⟨fun h i j hij => h hij, fun h i j hij => h i j hij⟩
theorem blkM_isUpUni : IsUpUni (blkM hN A B C D) ↔ IsUpUni A ∧ C = 0 ∧ IsUpUni D := by
  simp only [IsUpUni, upTri_lemma]
  constructor
  · rintro ⟨hL, hD⟩
    refine ⟨⟨fun i j hij => ?_, fun i => ?_⟩, ?_, fun i j hij => ?_, fun i => ?_⟩
    · simpa [blkM_ll] using hL _ _ ((eN_ll_lt hN j i).2 hij)
    · simpa [blkM_ll] using hD (eN hN (Sum.inl i))
    · ext i j
      simpa [blkM_rl] using hL _ _ (eN_lr_lt hN j i)
    · simpa [blkM_rr] using hL _ _ ((eN_rr_lt hN j i).2 hij)
    · simpa [blkM_rr] using hD (eN hN (Sum.inr i))
  · rintro ⟨⟨hA, hA1⟩, rfl, hD, hD1⟩
    refine ⟨fun x y hxy => ?_, fun x => ?_⟩
    · obtain ⟨p, rfl⟩ := (eN hN).surjective x
      obtain ⟨q, rfl⟩ := (eN hN).surjective y
      rcases p with i | i <;> rcases q with j | j
      · rw [blkM_ll]
        exact hA i j ((eN_ll_lt hN j i).1 hxy)
      · exact absurd hxy (not_lt.2 (eN_lr_lt hN i j).le)
      · simp [blkM_rl]
      · rw [blkM_rr]
        exact hD i j ((eN_rr_lt hN j i).1 hxy)
    · obtain ⟨p, rfl⟩ := (eN hN).surjective x
      rcases p with i | i
      · rw [blkM_ll]
        exact hA1 i
      · rw [blkM_rr]
        exact hD1 i
def cornL (C : Matrix (Fin s) (Fin a) K) : K :=
  ∑ j : Fin a, ∑ i : Fin s, if i.val = 0 ∧ j.val + 1 = a then C i j else 0
def cornU (B : Matrix (Fin a) (Fin s) K) : K :=
  ∑ i : Fin a, ∑ j : Fin s, if j.val = 0 ∧ i.val + 1 = a then B i j else 0
def bigZ (hN : N = a + s) (Z : Matrix (Fin a) (Fin a) K) (X : Matrix (Fin s) (Fin a) K)
    (Y : Matrix (Fin a) (Fin s) K) (G : Matrix (Fin s) (Fin s) K) : Matrix (Fin N) (Fin N) K :=
  blkM hN Z (Z * Y) (X * Z) (X * Z * Y + G)
end GlobalTheory
section Phi
variable {K : Type} [CommRing K] (R : Subring K)
open Classical in

def Fz {n n' : ℕ} (Z' : Matrix (Fin n') (Fin n') K) (Z : Matrix (Fin n) (Fin n) K) : ℂ :=
  if IsInt R Z then (Nat.card (isoZZ R Z Z') : ℂ) else 0
def outM {ι κ : Type} (x : Matrix ι κ (KR R)) : Matrix ι κ K := fun i j => Quotient.out (x i j)
def clsM {ι κ : Type} (x : Matrix ι κ K) : Matrix ι κ (KR R) :=
  fun i j => Submodule.Quotient.mk (x i j)
def PhiH (ψ : AddChar K ℂ) (h : Point K) {n' : ℕ} (Z' : Matrix (Fin n') (Fin n') K) (n : ℕ)
    (G : Matrix (Fin n) (Fin n) K) : ℂ :=
  ∑ᶠ τ : Cos R h × Matrix (Fin n) (Fin h.1.sum) (KR R) × Matrix (Fin h.1.sum) (Fin n) (KR R),
    Fz R Z' (bigZ rfl (orbZ h (rep R τ.1)) (outM R τ.2.1) (outM R τ.2.2) G) *
      (phase ψ (rep R τ.1) * ψ (cornL (outM R τ.2.1) + cornU (outM R τ.2.2)))
end Phi
section Simple
variable {K : Type} [CommRing K] {a s N : ℕ}
end Simple
section Lists
variable {K : Type} [CommRing K]
lemma revIn_lt_lemma_2 : ∀ (l : List ℕ) (j : ℕ), j < l.sum → revIn l j < l.sum := by
  intro l
  induction l with
  | nil =>
    intro j hj
    simp at hj
  | cons x l ih =>
    intro j hj
    rw [List.sum_cons] at hj ⊢
    simp only [revIn]
    by_cases h : j < x
    · rw [if_pos h]
      omega
    · rw [if_neg h]
      have := ih (j - x) (by omega)
      omega
lemma revIn_invol_lemma_3 : ∀ (l : List ℕ) (j : ℕ), j < l.sum → revIn l (revIn l j) = j := by
  intro l
  induction l with
  | nil =>
    intro j hj
    simp at hj
  | cons x l ih =>
    intro j hj
    rw [List.sum_cons] at hj
    by_cases h : j < x
    · have e1 : revIn (x :: l) j = x - 1 - j := by
        simp only [revIn]
        rw [if_pos h]
      have h' : x - 1 - j < x := by omega
      have e2 : revIn (x :: l) (x - 1 - j) = x - 1 - (x - 1 - j) := by
        simp only [revIn]
        rw [if_pos h']
      rw [e1, e2]
      omega
    · have e1 : revIn (x :: l) j = x + revIn l (j - x) := by
        simp only [revIn]
        rw [if_neg h]
      have h' : ¬ (x + revIn l (j - x) < x) := by omega
      have e2 : revIn (x :: l) (x + revIn l (j - x)) = x + revIn l (x + revIn l (j - x) - x) := by
        simp only [revIn]
        rw [if_neg h']
      rw [e1, e2, show x + revIn l (j - x) - x = revIn l (j - x) by omega, ih (j - x) (by omega)]
      omega
lemma blk_revIn_lemma_4 : ∀ (l : List ℕ) (j : ℕ), j < l.sum → blk l (revIn l j) = blk l j := by
  intro l
  induction l with
  | nil =>
    intro j hj
    simp at hj
  | cons x l ih =>
    intro j hj
    rw [List.sum_cons] at hj
    by_cases h : j < x
    · have e1 : revIn (x :: l) j = x - 1 - j := by
        simp only [revIn]
        rw [if_pos h]
      have h' : x - 1 - j < x := by omega
      have e2 : blk (x :: l) (x - 1 - j) = 0 := by
        simp only [blk]
        rw [if_pos h']
      have e3 : blk (x :: l) j = 0 := by
        simp only [blk]
        rw [if_pos h]
      rw [e1, e2, e3]
    · have e1 : revIn (x :: l) j = x + revIn l (j - x) := by
        simp only [revIn]
        rw [if_neg h]
      have h' : ¬ (x + revIn l (j - x) < x) := by omega
      have e2 : blk (x :: l) (x + revIn l (j - x)) = 1 + blk l (x + revIn l (j - x) - x) := by
        simp only [blk]
        rw [if_neg h']
      have e3 : blk (x :: l) j = 1 + blk l (j - x) := by
        simp only [blk]
        rw [if_neg h]
      rw [e1, e2, e3, show x + revIn l (j - x) - x = revIn l (j - x) by omega, ih (j - x) (by omega)]
lemma pt_unit_lemma_5 (s : List ℕ) (t : ℕ → Kˣ) : IsUnit (pt s t).det := by
  refine Matrix.isUnit_det_of_right_inverse (B := Matrix.of fun b c : Fin s.sum =>
    if (c : ℕ) = revIn s b then (((t (blk s b))⁻¹ : Kˣ) : K) else 0) ?_
  ext a c
  rw [Matrix.mul_apply, Finset.sum_eq_single ⟨revIn s a, revIn_lt_lemma_2 s a a.2⟩]
  · by_cases hca : c = a
    · subst hca
      simp [pt, revIn_invol_lemma_3 s c c.2, blk_revIn_lemma_4 s c c.2]
    · have h1 : (c : ℕ) ≠ a := fun e => hca (Fin.ext e)
      have h2 : a ≠ c := fun e => hca e.symm
      simp [pt, revIn_invol_lemma_3 s a a.2, blk_revIn_lemma_4 s a a.2, Matrix.one_apply, h1, h2]
  · intro b _ hb
    have : (b : ℕ) ≠ revIn s a := fun e => hb (Fin.ext e)
    simp [pt, this]
  · simp
theorem two_block_point_size_sum (h : Point K) (m : ℕ) (t c : Kˣ) :
    (pt2 h m t c).1.sum = h.1.sum + (pt2 (h0 : Point K) m t c).1.sum := by
  simp [pt2, h0, addBlock, List.sum_append, add_assoc]
theorem add_sum (h : Point K) (s : ℕ) (z : Kˣ) :
    (addBlock h s z).1.sum = h.1.sum + (addBlock (h0 : Point K) s z).1.sum := by
  simp [addBlock, h0, List.sum_append]
end Lists
section Cls
variable {K : Type} [CommRing K] (R : Subring K) {ι κ μ : Type}
end Cls
section Grp
variable {K : Type} [CommRing K] {h g w : Point K} (hN : w.1.sum = h.1.sum + g.1.sum)
  (hW : pt w.1 w.2 = blkM hN (pt h.1 h.2) 0 0 (pt g.1 g.2))
include hW in
theorem low_mem (A : Matrix (Fin h.1.sum) (Fin h.1.sum) K)
    (C : Matrix (Fin g.1.sum) (Fin h.1.sum) K) (D : Matrix (Fin g.1.sum) (Fin g.1.sum) K) :
    (IsLowUni (blkM hN A 0 C D) ∧ ∃ H : Matrix (Fin w.1.sum) (Fin w.1.sum) K, IsLowUni H ∧
      blkM hN A 0 C D * pt w.1 w.2 = pt w.1 w.2 * H) ↔
    (IsLowUni A ∧ ∃ H : Matrix (Fin h.1.sum) (Fin h.1.sum) K, IsLowUni H ∧
      A * pt h.1 h.2 = pt h.1 h.2 * H) ∧
    (IsLowUni D ∧ ∃ H : Matrix (Fin g.1.sum) (Fin g.1.sum) K, IsLowUni H ∧
      D * pt g.1 g.2 = pt g.1 g.2 * H) := by
  rw [hW]
  constructor
  · rintro ⟨hL, H, hH, e⟩
    obtain ⟨hA, -, hD⟩ := (blkM_isLowUni _ _ _ _ _).1 hL
    obtain ⟨H1, H2, H3, H4, rfl⟩ : ∃ H1 H2 H3 H4, H = blkM hN H1 H2 H3 H4 :=
      ⟨_, _, _, _, eq_blkM hN H⟩
    obtain ⟨hH1, -, hH4⟩ := (blkM_isLowUni _ _ _ _ _).1 hH
    rw [blkM_mul, blkM_mul] at e
    obtain ⟨e1, -, -, e4⟩ := blkM_inj hN e
    refine ⟨⟨hA, H1, hH1, ?_⟩, ⟨hD, H4, hH4, ?_⟩⟩
    · simpa using e1
    · simpa using e4
  · rintro ⟨⟨hA, H1, hH1, e1⟩, ⟨hD, H4, hH4, e4⟩⟩
    have hu := pt_unit_lemma_5 g.1 g.2
    refine ⟨(blkM_isLowUni _ _ _ _ _).2 ⟨hA, rfl, hD⟩,
      blkM hN H1 0 ((pt g.1 g.2)⁻¹ * C * pt h.1 h.2) H4,
      (blkM_isLowUni _ _ _ _ _).2 ⟨hH1, rfl, hH4⟩, ?_⟩
    rw [blkM_mul, blkM_mul]
    simp only [Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add]
    rw [e1, e4, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.one_mul]
def lowJ (v : lowW K h.1 h.2 × lowW K g.1 g.2) (X : Matrix (Fin g.1.sum) (Fin h.1.sum) K) :
    lowW K w.1 w.2 :=
  ⟨sec_gl (blkM hN (sec_m v.1) 0 (X * sec_m v.1) (sec_m v.2))
    (isLowUni_det K ((blkM_isLowUni _ _ _ _ _).2 ⟨v.1.2.1, rfl, v.2.2.1⟩)),
    (low_mem hN hW (sec_m v.1) (X * sec_m v.1) (sec_m v.2)).2 ⟨v.1.2, v.2.2⟩⟩
def upJ (u : upUniG K h.1.sum × upUniG K g.1.sum) (Y : Matrix (Fin h.1.sum) (Fin g.1.sum) K) :
    upUniG K w.1.sum :=
  ⟨sec_gl (blkM hN (sec_m u.1) (sec_m u.1 * Y) 0 (sec_m u.2))
    (isUpUni_det K ((blkM_isUpUni _ _ _ _ _).2 ⟨u.1.2, rfl, u.2.2⟩)),
    (blkM_isUpUni _ _ _ _ _).2 ⟨u.1.2, rfl, u.2.2⟩⟩
end Grp
section PhiInv
variable {K : Type} [CommRing K] (R : Subring K)
variable {a s : ℕ}
variable {N : ℕ}
def Tsum (ψ : AddChar K ℂ) {n' : ℕ} (Z' : Matrix (Fin n') (Fin n') K)
    (Z1 : Matrix (Fin a) (Fin a) K) (X : Matrix (Fin s) (Fin a) K) (Y : Matrix (Fin a) (Fin s) K)
    (G : Matrix (Fin s) (Fin s) K) : ℂ :=
  Fz R Z' (bigZ rfl Z1 X Y G) * ψ (cornL X + cornU Y)
end PhiInv
section Pert
variable {K : Type} [CommRing K] (R : Subring K)
end Pert
section Sum
variable {K : Type} [CommRing K] (R : Subring K) {h g w : Point K}
  (hN : w.1.sum = h.1.sum + g.1.sum)
  (hW : pt w.1 w.2 = blkM hN (pt h.1 h.2) 0 0 (pt g.1 g.2))
abbrev Par (h g : Point K) : Type :=
  (Cos R h × Cos R g) ×
    (Matrix (Fin g.1.sum) (Fin h.1.sum) (KR R) × Matrix (Fin h.1.sum) (Fin g.1.sum) (KR R))
def sigma (t : Par R h g) : lowW K w.1 w.2 × upUniG K w.1.sum :=
  (lowJ hN hW ((rep R t.1.1).1, (rep R t.1.2).1) (outM R t.2.1),
    upJ hN ((rep R t.1.1).2, (rep R t.1.2).2) (outM R t.2.2))
end Sum
section Fin
variable {K : Type} [CommRing K] (R : Subring K)
end Fin
end Formalism.FourierDecayAlt.P.TwoBlockPoint
namespace Formalism.FourierDecayAlt.P
end Formalism.FourierDecayAlt.P


