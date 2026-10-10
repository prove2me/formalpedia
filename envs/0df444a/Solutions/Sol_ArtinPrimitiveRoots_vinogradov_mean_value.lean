-- Prove2me | solution 1 for ArtinPrimitiveRoots.vinogradov_mean_value
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T15:33:10.504826+00:00
-- url     : https://prove2.me/submissions/cda639b1-7c7a-4edd-a914-56c6ccd9d0fa

import Mathlib
import Definitions.Def_ArtinVinogradov

section
/-! # L33V basics: power-sum vectors, pair counts, Cauchy–Schwarz on fibres, affine invariance -/

namespace ArtinPrimitiveRoots.L33V

open Finset

/-- The power-sum vector `(Σᵢ xᵢ^(j+1))_{j < k}`. -/
def pv (k : ℕ) {ι : Type*} [Fintype ι] (x : ι → ℤ) : Fin k → ℤ :=
  fun j => ∑ i, x i ^ (j.val + 1)

/-- The number of ordered pairs from `X` with equal image under `χ`. -/
def eqc {α V : Type*} [DecidableEq V] (X : Finset α) (χ : α → V) : ℕ :=
  #{p ∈ X ×ˢ X | χ p.1 = χ p.2}

/-- `J_{s,k}` over an arbitrary finite set `A` of integers. -/
def JJ (k s : ℕ) (A : Finset ℤ) : ℕ := eqc (Fintype.piFinset fun _ : Fin s => A) (pv k)

lemma card_filter_eq_sum_fiber {α β V : Type*} [DecidableEq V] (X : Finset α) (Y : Finset β)
    (χ₁ : α → V) (χ₂ : β → V) (W : Finset V) (hW : ∀ x ∈ X, χ₁ x ∈ W) :
    #{p ∈ X ×ˢ Y | χ₁ p.1 = χ₂ p.2} = ∑ v ∈ W, #{x ∈ X | χ₁ x = v} * #{y ∈ Y | χ₂ y = v} := by
  rw [card_eq_sum_card_fiberwise (f := fun p => χ₁ p.1) (t := W)]
  · refine sum_congr rfl fun v _ => ?_
    rw [← card_product]
    congr 1
    ext ⟨x, y⟩
    simp only [mem_filter, mem_product]
    constructor
    · rintro ⟨⟨⟨hx, hy⟩, h⟩, rfl⟩; exact ⟨⟨hx, rfl⟩, hy, h.symm⟩
    · rintro ⟨⟨hx, rfl⟩, hy, h⟩; exact ⟨⟨⟨hx, hy⟩, h.symm⟩, rfl⟩
  · intro p hp
    exact hW _ (mem_product.1 (mem_filter.1 (mem_coe.1 hp)).1).1

/-- Cauchy–Schwarz over the fibres. -/
lemma cs_fiber {α β V : Type*} [DecidableEq V] (X : Finset α) (Y : Finset β)
    (χ₁ : α → V) (χ₂ : β → V) :
    #{p ∈ X ×ˢ Y | χ₁ p.1 = χ₂ p.2} ^ 2 ≤ eqc X χ₁ * eqc Y χ₂ := by
  have h1 : ∀ x ∈ X, χ₁ x ∈ X.image χ₁ ∪ Y.image χ₂ :=
    fun x hx => mem_union_left _ (mem_image_of_mem _ hx)
  have h2 : ∀ y ∈ Y, χ₂ y ∈ X.image χ₁ ∪ Y.image χ₂ :=
    fun y hy => mem_union_right _ (mem_image_of_mem _ hy)
  rw [card_filter_eq_sum_fiber X Y χ₁ χ₂ _ h1, eqc, eqc,
    card_filter_eq_sum_fiber X X χ₁ χ₁ _ h1, card_filter_eq_sum_fiber Y Y χ₂ χ₂ _ h2]
  simpa [sq] using sum_mul_sq_le_sq_mul_sq (X.image χ₁ ∪ Y.image χ₂)
    (fun v => #{x ∈ X | χ₁ x = v}) (fun v => #{y ∈ Y | χ₂ y = v})

lemma sum_add_pow' {ι : Type*} [Fintype ι] (x : ι → ℤ) (c : ℤ) (j : ℕ) :
    ∑ i, (x i + c) ^ j = ∑ l ∈ range (j + 1), (∑ i, x i ^ l) * c ^ (j - l) * (j.choose l) := by
  simp_rw [add_pow, Finset.sum_mul]
  exact Finset.sum_comm

/-- Equal power sums (degrees `1..k`) survive a common translation. -/
lemma pv_translate {k : ℕ} {ι : Type*} [Fintype ι] {x y : ι → ℤ} (h : pv k x = pv k y) (c : ℤ) :
    pv k (fun i => x i + c) = pv k (fun i => y i + c) := by
  funext j
  simp only [pv]
  rw [sum_add_pow', sum_add_pow']
  refine sum_congr rfl fun l hl => ?_
  rcases Nat.eq_zero_or_pos l with rfl | hl0
  · simp
  · have hl' := mem_range.1 hl
    have := congrFun h ⟨l - 1, by have := j.2; omega⟩
    simp only [pv, Nat.sub_add_cancel hl0] at this
    rw [this]

lemma pv_smul {k : ℕ} {ι : Type*} [Fintype ι] (x : ι → ℤ) (b : ℤ) (j : Fin k) :
    pv k (fun i => b * x i) j = b ^ (j.val + 1) * pv k x j := by
  simp [pv, mul_pow, mul_sum]

/-- Backward affine invariance. -/
lemma pv_of_affine {k : ℕ} {ι : Type*} [Fintype ι] {x y : ι → ℤ} (a b : ℤ) (hb : b ≠ 0)
    (h : pv k (fun i => a + b * x i) = pv k (fun i => a + b * y i)) : pv k x = pv k y := by
  have h2 := pv_translate h (-a)
  simp only [add_neg_cancel_comm] at h2
  funext j
  have := congrFun h2 j
  rw [pv_smul, pv_smul] at this
  exact mul_left_cancel₀ (pow_ne_zero _ hb) this

lemma JJ_mono (k s : ℕ) {A B : Finset ℤ} (h : A ⊆ B) : JJ k s A ≤ JJ k s B := by
  unfold JJ eqc
  apply card_le_card
  apply filter_subset_filter
  have : (Fintype.piFinset fun _ : Fin s => A) ⊆ Fintype.piFinset fun _ : Fin s => B :=
    Fintype.piFinset_subset _ _ fun _ => h
  exact product_subset_product this this

lemma JJ_affine_le (k s : ℕ) (A : Finset ℤ) (a b : ℤ) (hb : b ≠ 0) :
    JJ k s (A.image (fun w => a + b * w)) ≤ JJ k s A := by
  unfold JJ eqc
  set G : (Fin s → ℤ) → (Fin s → ℤ) := fun x i => (x i - a) / b
  have hG : ∀ x ∈ Fintype.piFinset (fun _ : Fin s => A.image (fun w => a + b * w)),
      G x ∈ Fintype.piFinset (fun _ : Fin s => A) ∧ (fun i => a + b * G x i) = x := by
    intro x hx
    rw [Fintype.mem_piFinset] at hx
    refine ⟨Fintype.mem_piFinset.2 fun i => ?_, funext fun i => ?_⟩
    · obtain ⟨w, hw, hw'⟩ := mem_image.1 (hx i)
      simp only [G, ← hw', add_sub_cancel_left, Int.mul_ediv_cancel_left _ hb, hw]
    · obtain ⟨w, hw, hw'⟩ := mem_image.1 (hx i)
      simp only [G, ← hw', add_sub_cancel_left, Int.mul_ediv_cancel_left _ hb]
  refine card_le_card_of_injOn (fun p => (G p.1, G p.2)) ?_ ?_
  · intro p hp
    simp only [coe_filter, mem_product, Set.mem_ofPred_eq] at hp
    obtain ⟨⟨h1, h2⟩, h3⟩ := hp
    simp only [coe_filter, mem_product, Set.mem_ofPred_eq]
    refine ⟨⟨(hG _ h1).1, (hG _ h2).1⟩, pv_of_affine a b hb ?_⟩
    rw [(hG _ h1).2, (hG _ h2).2]; exact h3
  · intro p hp q hq hpq
    simp only [coe_filter, mem_product, Set.mem_ofPred_eq] at hp hq
    simp only [Prod.mk.injEq] at hpq
    refine Prod.ext ?_ ?_
    · calc p.1 = (fun i => a + b * G p.1 i) := (hG _ hp.1.1).2.symm
        _ = (fun i => a + b * G q.1 i) := by rw [hpq.1]
        _ = q.1 := (hG _ hq.1.1).2
    · calc p.2 = (fun i => a + b * G p.2 i) := (hG _ hp.1.2).2.symm
        _ = (fun i => a + b * G q.2 i) := by rw [hpq.2]
        _ = q.2 := (hG _ hq.1.2).2

lemma JJ_le_pow (k s : ℕ) (A : Finset ℤ) : JJ k s A ≤ #A ^ (2 * s) := by
  unfold JJ eqc
  refine (card_filter_le _ _).trans ?_
  rw [card_product, Fintype.card_piFinset, prod_const, card_univ, Fintype.card_fin, ← pow_add]
  ring_nf; rfl

/-- The bridge to the statement's `vinogradovCount`. -/
lemma vinogradovCount_le_JJ (s k M : ℕ) :
    vinogradovCount s k M ≤ JJ k s (Icc 1 (M : ℤ)) := by
  classical
  unfold vinogradovCount JJ eqc
  set e : (Fin s → Fin M) → (Fin s → ℤ) := fun u i => ((u i : ℕ) : ℤ) + 1
  refine card_le_card_of_injOn (fun p => (e p.1, e p.2)) ?_ ?_
  · intro p hp
    simp only [coe_filter, mem_product, mem_univ, true_and, Set.mem_ofPred_eq] at hp
    simp only [coe_filter, mem_product, Set.mem_ofPred_eq, Fintype.mem_piFinset, mem_Icc]
    refine ⟨⟨fun i => ⟨by simp [e], ?_⟩, fun i => ⟨by simp [e], ?_⟩⟩, ?_⟩
    · have := (p.1 i).2; simp only [e]; omega
    · have := (p.2 i).2; simp only [e]; omega
    · funext j
      have := hp (j.val + 1) (mem_Icc.2 ⟨by omega, j.2⟩)
      simp only [pv, e]
      exact_mod_cast this
  · intro p _ q _ hpq
    simp only [Prod.mk.injEq] at hpq
    have he : Function.Injective e := by
      intro u v huv
      funext i
      have := congrFun huv i
      simp only [e, add_left_inj, Nat.cast_inj] at this
      exact Fin.ext this
    exact Prod.ext (he hpq.1) (he hpq.2)

end ArtinPrimitiveRoots.L33V
end

section
/-! # L33V: Hölder over residue classes, through the characters of a finite abelian group -/

namespace ArtinPrimitiveRoots.L33V

open Finset

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

omit [Fintype G] [DecidableEq G] in
lemma addChar_map_sum (ψ : AddChar G ℂ) {ι : Type*} (t : Finset ι) (f : ι → G) :
    ψ (∑ i ∈ t, f i) = ∏ i ∈ t, ψ (f i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert a t ha ih => rw [sum_insert ha, AddChar.map_add_eq_mul, ih, prod_insert ha]

/-- Orthogonality: a pair count is the mean square of the character sums. -/
lemma eqc_fourier {α : Type*} (X : Finset α) (χ : α → G) :
    (eqc X χ : ℝ) * Fintype.card G = ∑ ψ : AddChar G ℂ, ‖∑ x ∈ X, ψ (χ x)‖ ^ 2 := by
  apply Complex.ofReal_injective
  push_cast
  simp_rw [← Complex.mul_conj', map_sum, sum_mul_sum, ← AddChar.map_neg_eq_conj,
    ← AddChar.map_add_eq_mul, ← sub_eq_add_neg]
  simp_rw [← sum_product' (s := X) (t := X) (f := fun x y => _)]
  rw [sum_comm]
  simp_rw [AddChar.sum_apply_eq_ite, sub_eq_zero]
  rw [sum_ite, sum_const_zero, add_zero, sum_const, nsmul_eq_mul, eqc, mul_comm]

omit [Fintype G] [DecidableEq G] in
lemma sum_tuple (ψ : AddChar G ℂ) {β : Type*} (Z : Finset β) (ζ : β → G) (U : Finset ℤ)
    (φ : ℤ → G) (s : ℕ) :
    ∑ p ∈ Z ×ˢ Fintype.piFinset (fun _ : Fin s => U), ψ (ζ p.1 + ∑ i, φ (p.2 i)) =
      (∑ z ∈ Z, ψ (ζ z)) * (∑ u ∈ U, ψ (φ u)) ^ s := by
  rw [sum_product, sum_mul]
  refine sum_congr rfl fun z _ => ?_
  simp_rw [AddChar.map_add_eq_mul, addChar_map_sum, ← mul_sum]
  congr 1
  rw [← prod_univ_sum (fun _ : Fin s => U) (fun _ u => ψ (φ u)), prod_const, card_univ,
    Fintype.card_fin]

/-- Hölder over classes: `eqc(Z × U^s) ≤ |I|^(2s-1) Σ_c eqc(Z × U_c^s)`. -/
lemma holder_classes {β : Type*} (Z : Finset β) (ζ : β → G) (U : Finset ℤ) (φ : ℤ → G)
    (I : Finset ℤ) (cls : ℤ → ℤ) (hcls : ∀ u ∈ U, cls u ∈ I) (s : ℕ) (hs : 1 ≤ s) :
    (eqc (Z ×ˢ Fintype.piFinset (fun _ : Fin s => U)) (fun p => ζ p.1 + ∑ i, φ (p.2 i)) : ℝ) ≤
      (#I : ℝ) ^ (2 * s - 1) * ∑ c ∈ I,
        (eqc (Z ×ˢ Fintype.piFinset (fun _ : Fin s => U.filter (fun u => cls u = c)))
          (fun p => ζ p.1 + ∑ i, φ (p.2 i)) : ℝ) := by
  have hG : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  rw [← mul_le_mul_iff_left₀ hG, mul_assoc, sum_mul]
  simp_rw [eqc_fourier, sum_tuple, norm_mul, norm_pow, mul_pow, ← pow_mul]
  rw [sum_comm, mul_sum]
  refine sum_le_sum fun ψ _ => ?_
  rw [← mul_sum, mul_left_comm]
  gcongr ‖_‖ ^ 2 * ?_
  have hsplit : ∑ u ∈ U, ψ (φ u) = ∑ c ∈ I, ∑ u ∈ U.filter (fun u => cls u = c), ψ (φ u) :=
    (sum_fiberwise_of_maps_to hcls _).symm
  rw [hsplit]
  calc ‖∑ c ∈ I, ∑ u ∈ U.filter (fun u => cls u = c), ψ (φ u)‖ ^ (s * 2)
      ≤ (∑ c ∈ I, ‖∑ u ∈ U.filter (fun u => cls u = c), ψ (φ u)‖) ^ (s * 2) := by
        gcongr; exact norm_sum_le _ _
    _ = (∑ c ∈ I, ‖∑ u ∈ U.filter (fun u => cls u = c), ψ (φ u)‖) ^ (2 * s - 1 + 1) := by
        congr 1; omega
    _ ≤ (#I : ℝ) ^ (2 * s - 1) *
          ∑ c ∈ I, ‖∑ u ∈ U.filter (fun u => cls u = c), ψ (φ u)‖ ^ (2 * s - 1 + 1) :=
        pow_sum_le_card_mul_sum_pow (fun _ _ => norm_nonneg _) _
    _ = _ := by congr 2; ext c; congr 1; omega

end ArtinPrimitiveRoots.L33V
end

section
/-! # L33V: power sums modulo `r^k` (Newton's identities mod `r`, Hensel lifting) and the
congruence count (3.5) -/

namespace ArtinPrimitiveRoots.L33V

open Finset

/-- The coordinates of `y` are pairwise incongruent modulo `r`. -/
def injmod (r : ℕ) {k : ℕ} (y : Fin k → ℤ) : Prop := ∀ i l, i ≠ l → ¬ (r : ℤ) ∣ y i - y l

instance (r k : ℕ) : DecidablePred (@injmod r k) := fun y => by unfold injmod; infer_instance

/-- Newton's identities: equal power sums of degrees `1..k` give equal elementary symmetric
functions, when `1, ..., k` are invertible. -/
lemma esymm_eq_of_psum_eq {R : Type*} [Field R] {k : ℕ} (x y : Fin k → R)
    (hchar : ∀ j : ℕ, 0 < j → j ≤ k → (j : R) ≠ 0)
    (h : ∀ j, 1 ≤ j → j ≤ k → ∑ i, x i ^ j = ∑ i, y i ^ j) :
    ∀ j, j ≤ k → (univ.val.map x).esymm j = (univ.val.map y).esymm j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
  intro hj
  rw [← MvPolynomial.aeval_esymm_eq_multiset_esymm (Fin k) R,
    ← MvPolynomial.aeval_esymm_eq_multiset_esymm (Fin k) R]
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · simp [MvPolynomial.esymm_zero]
  have Nx := congrArg (MvPolynomial.aeval x) (MvPolynomial.mul_esymm_eq_sum (Fin k) R j)
  have Ny := congrArg (MvPolynomial.aeval y) (MvPolynomial.mul_esymm_eq_sum (Fin k) R j)
  simp only [map_mul, map_natCast, map_pow, map_neg, map_one, map_sum,
    MvPolynomial.psum, MvPolynomial.aeval_X] at Nx Ny
  have hsum : ∑ a ∈ antidiagonal j with a.1 < j,
      (-1) ^ a.1 * (MvPolynomial.aeval x) (MvPolynomial.esymm (Fin k) R a.1) * ∑ i, x i ^ a.2 =
      ∑ a ∈ antidiagonal j with a.1 < j,
      (-1) ^ a.1 * (MvPolynomial.aeval y) (MvPolynomial.esymm (Fin k) R a.1) * ∑ i, y i ^ a.2 := by
    refine sum_congr rfl fun a ha => ?_
    rw [mem_filter, HasAntidiagonal.mem_antidiagonal] at ha
    rw [MvPolynomial.aeval_esymm_eq_multiset_esymm, MvPolynomial.aeval_esymm_eq_multiset_esymm,
      ih a.1 ha.2 (by omega), h a.2 (by omega) (by omega)]
  rw [hsum, ← Ny] at Nx
  exact mul_left_cancel₀ (hchar j hj0 hj) Nx

/-- Equal power sums of degrees `1..k` give equal multisets (char. `> k`). -/
lemma multiset_eq_of_psum_eq {R : Type*} [Field R] {k : ℕ} (x y : Fin k → R)
    (hchar : ∀ j : ℕ, 0 < j → j ≤ k → (j : R) ≠ 0)
    (h : ∀ j, 1 ≤ j → j ≤ k → ∑ i, x i ^ j = ∑ i, y i ^ j) :
    univ.val.map x = univ.val.map y := by
  have he := esymm_eq_of_psum_eq x y hchar h
  have hP : ((univ.val.map x).map fun a => Polynomial.X - Polynomial.C a).prod =
      ((univ.val.map y).map fun a => Polynomial.X - Polynomial.C a).prod := by
    ext n
    have cx : (univ.val.map x).card = k := by simp
    have cy : (univ.val.map y).card = k := by simp
    rcases le_or_gt n k with hn | hn
    · rw [Multiset.prod_X_sub_C_coeff _ (by rw [cx]; exact hn),
        Multiset.prod_X_sub_C_coeff _ (by rw [cy]; exact hn), cx, cy, he (k - n) (by omega)]
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by
          rw [Polynomial.natDegree_multiset_prod_X_sub_C_eq_card, cx]; exact hn),
        Polynomial.coeff_eq_zero_of_natDegree_lt (by
          rw [Polynomial.natDegree_multiset_prod_X_sub_C_eq_card, cy]; exact hn)]
  have := congrArg Polynomial.roots hP
  rwa [Polynomial.roots_multiset_prod_X_sub_C, Polynomial.roots_multiset_prod_X_sub_C] at this

/-- One Hensel step: congruence modulo `r^m` improves to `r^(m+1)` (Vandermonde Jacobian). -/
lemma hensel_step (r : ℕ) (hr : r.Prime) {k : ℕ} (hk : k < r) (y w : Fin k → ℤ)
    (hw : injmod r w) (hps : ∀ j, 1 ≤ j → j ≤ k → (r : ℤ) ^ k ∣ (∑ i, y i ^ j) - ∑ i, w i ^ j)
    (m : ℕ) (hm1 : 1 ≤ m) (hmk : m + 1 ≤ k) (hd : ∀ i, (r : ℤ) ^ m ∣ y i - w i) :
    ∀ i, (r : ℤ) ^ (m + 1) ∣ y i - w i := by
  have := Fact.mk hr
  choose d hd using hd
  have hr0 : (r : ℤ) ≠ 0 := by exact_mod_cast hr.ne_zero
  have key : ∀ j : Fin k, ∑ i, (d i : ZMod r) * (w i : ZMod r) ^ (j : ℕ) = 0 := by
    intro j
    have hJ : (r : ℤ) ^ (m + 1) ∣ (∑ i, y i ^ ((j : ℕ) + 1)) - ∑ i, w i ^ ((j : ℕ) + 1) :=
      (pow_dvd_pow _ (by omega)).trans (hps ((j : ℕ) + 1) (by omega) (by have := j.2; omega))
    have hE : ∀ i, (r : ℤ) ^ (m + 1) ∣ y i ^ ((j : ℕ) + 1) - w i ^ ((j : ℕ) + 1) -
        w i ^ (j : ℕ) * ((r : ℤ) ^ m * d i) * (((j : ℕ) + 1 : ℕ) : ℤ) := by
      intro i
      have h1 := sq_dvd_add_pow_sub_sub ((r : ℤ) ^ m * d i) (w i) ((j : ℕ) + 1)
      have hy : y i = w i + (r : ℤ) ^ m * d i := by linarith [hd i]
      have h2 : (r : ℤ) ^ (m + 1) ∣ ((r : ℤ) ^ m * d i) ^ 2 :=
        ⟨(r : ℤ) ^ (m - 1) * d i ^ 2, by
          rw [mul_pow, ← pow_mul, ← mul_assoc, ← pow_add]; congr 2; omega⟩
      rw [Nat.add_sub_cancel] at h1
      rw [hy]
      have e : (w i + (r : ℤ) ^ m * d i) ^ ((j : ℕ) + 1) - w i ^ ((j : ℕ) + 1) -
          w i ^ (j : ℕ) * ((r : ℤ) ^ m * d i) * (((j : ℕ) + 1 : ℕ) : ℤ) =
          (w i + (r : ℤ) ^ m * d i) ^ ((j : ℕ) + 1) -
          w i ^ (j : ℕ) * ((r : ℤ) ^ m * d i) * (((j : ℕ) + 1 : ℕ) : ℤ) - w i ^ ((j : ℕ) + 1) := by
        ring
      rw [e]
      exact h2.trans h1
    have hsum := dvd_sub hJ (dvd_sum fun i (_ : i ∈ univ) => hE i)
    rw [← sum_sub_distrib] at hsum
    have heq : (∑ i, (y i ^ ((j : ℕ) + 1) - w i ^ ((j : ℕ) + 1))) -
        ∑ i, (y i ^ ((j : ℕ) + 1) - w i ^ ((j : ℕ) + 1) -
          w i ^ (j : ℕ) * ((r : ℤ) ^ m * d i) * (((j : ℕ) + 1 : ℕ) : ℤ)) =
        (r : ℤ) ^ m * ((((j : ℕ) + 1 : ℕ) : ℤ) * ∑ i, d i * w i ^ (j : ℕ)) := by
      rw [← sum_sub_distrib, mul_sum, mul_sum]
      exact sum_congr rfl fun i _ => by ring
    rw [heq] at hsum
    have hsum' : (r : ℤ) ^ m * (r : ℤ) ∣ (r : ℤ) ^ m *
        ((((j : ℕ) + 1 : ℕ) : ℤ) * ∑ i, d i * w i ^ (j : ℕ)) := by
      rw [← pow_succ]; exact hsum
    rw [mul_dvd_mul_iff_left (pow_ne_zero _ hr0)] at hsum'
    rcases (Nat.prime_iff_prime_int.1 hr).dvd_or_dvd hsum' with h | h
    · exfalso
      have := Int.le_of_dvd (by positivity) h
      have := j.2
      omega
    · have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ r).2 h
      push_cast at this
      exact this
  have hdz : (fun i => (d i : ZMod r)) = 0 := by
    apply Matrix.eq_zero_of_vecMul_eq_zero (M := Matrix.vandermonde (fun i => (w i : ZMod r)))
    · rw [Matrix.det_vandermonde_ne_zero_iff]
      intro i l h
      by_contra hil
      exact hw l i (Ne.symm hil) ((ZMod.intCast_eq_intCast_iff_dvd_sub _ _ r).1 h)
    · funext j
      simp only [Matrix.vecMul, dotProduct, Matrix.vandermonde_apply, Pi.zero_apply]
      exact key j
  intro i
  have := congrFun hdz i
  simp only [Pi.zero_apply] at this
  obtain ⟨e, he⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ r).1 this
  exact ⟨e, by rw [hd i, he, pow_succ]; ring⟩

/-- Power sums congruent modulo `r^k` (degrees `1..k`), coordinates distinct modulo the prime
`r > k`: the tuples agree modulo `r^k` up to a permutation. -/
lemma perm_of_ps_cong (r : ℕ) (hr : r.Prime) {k : ℕ} (hk : k < r) (y y₀ : Fin k → ℤ)
    (hy₀ : injmod r y₀) (hy : injmod r y)
    (h : ∀ j, 1 ≤ j → j ≤ k → (r : ℤ) ^ k ∣ (∑ i, y i ^ j) - ∑ i, y₀ i ^ j) :
    ∃ π : Equiv.Perm (Fin k), ∀ i, (r : ℤ) ^ k ∣ y i - y₀ (π i) := by
  have := Fact.mk hr
  rcases Nat.eq_zero_or_pos k with hk0 | hk0
  · subst hk0; exact ⟨1, fun i => i.elim0⟩
  have hchar : ∀ j : ℕ, 0 < j → j ≤ k → (j : ZMod r) ≠ 0 := by
    intro j hj0 hjk hz
    rw [ZMod.natCast_eq_zero_iff] at hz
    have := Nat.le_of_dvd hj0 hz
    omega
  have hps1 : ∀ j, 1 ≤ j → j ≤ k →
      ∑ i, ((y i : ZMod r)) ^ j = ∑ i, ((y₀ i : ZMod r)) ^ j := by
    intro j h1 h2
    have h' : (r : ℤ) ∣ (∑ i, y i ^ j) - ∑ i, y₀ i ^ j :=
      (dvd_pow_self _ (by omega : k ≠ 0)).trans (h j h1 h2)
    have := (ZMod.intCast_eq_intCast_iff_dvd_sub (∑ i, y₀ i ^ j) (∑ i, y i ^ j) r).2 h'
    push_cast at this
    exact this.symm
  have hm := multiset_eq_of_psum_eq _ _ hchar hps1
  have hex : ∀ i, ∃ l, (y₀ l : ZMod r) = y i := by
    intro i
    have : (y i : ZMod r) ∈ univ.val.map (fun i => (y₀ i : ZMod r)) := by
      rw [← hm]; exact Multiset.mem_map_of_mem _ (mem_univ i)
    simpa using this
  choose π' hπ' using hex
  have hinj : Function.Injective π' := by
    intro i i' hii
    by_contra hne
    have h1 := hπ' i
    rw [hii, hπ' i'] at h1
    exact hy i' i (Ne.symm hne) ((ZMod.intCast_eq_intCast_iff_dvd_sub _ _ r).1 h1.symm)
  let π := Equiv.ofBijective π' (Finite.injective_iff_bijective.1 hinj)
  refine ⟨π, ?_⟩
  have hw : injmod r (fun i => y₀ (π i)) :=
    fun i l hil hd => hy₀ (π i) (π l) (π.injective.ne hil) hd
  have h1 : ∀ i, (r : ℤ) ^ 1 ∣ y i - y₀ (π i) := by
    intro i
    rw [pow_one]
    exact (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ r).1 (hπ' i)
  have hpsw : ∀ j, 1 ≤ j → j ≤ k →
      (r : ℤ) ^ k ∣ (∑ i, y i ^ j) - ∑ i, (fun i => y₀ (π i)) i ^ j := by
    intro j h1 h2
    rw [Equiv.sum_comp π (fun i => y₀ i ^ j)]
    exact h j h1 h2
  have hall : ∀ m, 1 ≤ m → m ≤ k → ∀ i, (r : ℤ) ^ m ∣ y i - y₀ (π i) := by
    intro m hm1
    induction m, hm1 using Nat.le_induction with
    | base => intro _; exact h1
    | succ m hm ih =>
      intro hmk
      exact hensel_step r hr hk y (fun i => y₀ (π i)) hw hpsw m hm hmk (ih (by omega))
  exact hall k hk0 le_rfl

lemma card_Ico_dvd_le (n e : ℕ) (hen : e ≤ n) (r : ℕ) (hr : 0 < r) (v : ℤ) :
    #{T ∈ Ico (0 : ℤ) ((r : ℤ) ^ n) | (r : ℤ) ^ e ∣ T - v} ≤ r ^ (n - e) := by
  have hre : (0 : ℤ) < (r : ℤ) ^ e := by positivity
  calc #{T ∈ Ico (0 : ℤ) ((r : ℤ) ^ n) | (r : ℤ) ^ e ∣ T - v}
      ≤ #(Ico (0 : ℤ) ((r : ℤ) ^ (n - e))) := by
        refine card_le_card_of_injOn (fun T => T / (r : ℤ) ^ e) ?_ ?_
        · intro T hT
          simp only [coe_filter, mem_Ico, Set.mem_ofPred_eq] at hT
          simp only [coe_Ico, Set.mem_Ico]
          refine ⟨Int.ediv_nonneg hT.1.1 hre.le, Int.ediv_lt_of_lt_mul hre ?_⟩
          rw [← pow_add, Nat.sub_add_cancel hen]; exact hT.1.2
        · intro T hT T' hT' hTT
          simp only [coe_filter, mem_Ico, Set.mem_ofPred_eq] at hT hT'
          simp only at hTT
          have hmod : T % (r : ℤ) ^ e = T' % (r : ℤ) ^ e :=
            Int.ModEq.eq (Int.modEq_iff_dvd.2 (by
              have := dvd_sub hT'.2 hT.2; rwa [sub_sub_sub_cancel_right] at this))
          rw [← Int.mul_ediv_add_emod T ((r : ℤ) ^ e), ← Int.mul_ediv_add_emod T' ((r : ℤ) ^ e), hTT, hmod]
    _ = r ^ (n - e) := by rw [Int.card_Ico, sub_zero, ← Nat.cast_pow, Int.toNat_natCast]

/-- The congruence count (3.5): on an interval of `M ≤ r^k` integers, the `k`-tuples with
coordinates distinct mod `r` and prescribed power sums mod `r^j` (`1 ≤ j ≤ k`) number at most
`k! r^(k(k-1)/2)`. -/
lemma cong_count (r : ℕ) (hr : r.Prime) {k : ℕ} (hk : k < r) (M : ℕ) (hM : M ≤ r ^ k) (a : ℤ)
    (t : ℕ → ℤ) :
    #{y ∈ Fintype.piFinset (fun _ : Fin k => Icc a (a + M - 1)) |
        injmod r y ∧ ∀ j, 1 ≤ j → j ≤ k → (r : ℤ) ^ j ∣ (∑ i, y i ^ j) - t j} ≤
      k.factorial * r ^ (k * (k - 1) / 2) := by
  classical
  have hr0 : 0 < r := hr.pos
  have hrpos : (0 : ℤ) < (r : ℤ) ^ k := by positivity
  set S := {y ∈ Fintype.piFinset (fun _ : Fin k => Icc a (a + M - 1)) |
        injmod r y ∧ ∀ j, 1 ≤ j → j ≤ k → (r : ℤ) ^ j ∣ (∑ i, y i ^ j) - t j} with hS
  set F : (Fin k → ℤ) → (Fin k → ℤ) := fun y j => (∑ i, y i ^ ((j : ℕ) + 1)) % ((r : ℤ) ^ k)
  set L := Fintype.piFinset (fun j : Fin k => (Ico (0 : ℤ) ((r : ℤ) ^ k)).filter
    (fun T => (r : ℤ) ^ ((j : ℕ) + 1) ∣ T - t ((j : ℕ) + 1)))
  have hmaps : ∀ y ∈ S, F y ∈ L := by
    intro y hy
    rw [hS, mem_filter] at hy
    rw [Fintype.mem_piFinset]
    intro j
    rw [mem_filter, mem_Ico]
    refine ⟨⟨Int.emod_nonneg _ hrpos.ne', Int.emod_lt_of_pos _ hrpos⟩, ?_⟩
    have h1 := hy.2.2 ((j : ℕ) + 1) (by omega) (by have := j.2; omega)
    have h2 : (r : ℤ) ^ ((j : ℕ) + 1) ∣ (r : ℤ) ^ k := pow_dvd_pow _ (by have := j.2; omega)
    have : F y j - t ((j : ℕ) + 1) = ((∑ i, y i ^ ((j : ℕ) + 1)) - t ((j : ℕ) + 1)) -
        (r : ℤ) ^ k * ((∑ i, y i ^ ((j : ℕ) + 1)) / (r : ℤ) ^ k) := by
      simp only [F]; rw [Int.emod_def]; ring
    rw [this]
    exact dvd_sub h1 (dvd_mul_of_dvd_left h2 _)
  have hfib : ∀ T ∈ L, #{y ∈ S | F y = T} ≤ k.factorial := by
    intro T _
    by_cases hne : ({y ∈ S | F y = T} : Finset _).Nonempty
    · obtain ⟨y₀, hy₀⟩ := hne
      rw [mem_filter] at hy₀
      have hy0S := mem_filter.1 hy₀.1
      calc #{y ∈ S | F y = T}
          ≤ #((univ : Finset (Equiv.Perm (Fin k))).image (fun π i => y₀ (π i))) := by
            apply card_le_card
            intro y hy
            rw [mem_filter] at hy
            have hyS := mem_filter.1 hy.1
            rw [mem_image]
            obtain ⟨π, hπ⟩ := perm_of_ps_cong r hr hk y y₀ hy0S.2.1 hyS.2.1 (by
              intro j h1 h2
              have hF : F y = F y₀ := hy.2.trans hy₀.2.symm
              have := congrFun hF ⟨j - 1, by omega⟩
              simp only [F, Nat.sub_add_cancel h1] at this
              exact Int.ModEq.dvd (Int.ModEq.symm this))
            refine ⟨π, mem_univ _, funext fun i => ?_⟩
            have hyi := mem_Icc.1 (Fintype.mem_piFinset.1 hyS.1 i)
            have hy0i := mem_Icc.1 (Fintype.mem_piFinset.1 hy0S.1 (π i))
            have hMr : (M : ℤ) ≤ (r : ℤ) ^ k := by exact_mod_cast hM
            have := Int.eq_zero_of_abs_lt_dvd (hπ i) (by rw [abs_lt]; constructor <;> linarith)
            linarith
        _ ≤ #(univ : Finset (Equiv.Perm (Fin k))) := card_image_le
        _ = k.factorial := by rw [card_univ, Fintype.card_perm, Fintype.card_fin]
    · rw [not_nonempty_iff_eq_empty.1 hne]; simp
  have hL : #L ≤ r ^ (k * (k - 1) / 2) := by
    rw [Fintype.card_piFinset]
    calc ∏ j : Fin k, #((Ico (0 : ℤ) ((r : ℤ) ^ k)).filter
          (fun T => (r : ℤ) ^ ((j : ℕ) + 1) ∣ T - t ((j : ℕ) + 1)))
        ≤ ∏ j : Fin k, r ^ (k - ((j : ℕ) + 1)) :=
          prod_le_prod' fun j _ => card_Ico_dvd_le k _ (by have := j.2; omega) r hr0 _
      _ = r ^ (∑ j : Fin k, (k - ((j : ℕ) + 1))) := prod_pow_eq_pow_sum _ _ _
      _ = r ^ (k * (k - 1) / 2) := by
        congr 1
        rw [Fin.sum_univ_eq_sum_range (fun j => k - (j + 1)) k]
        have h2 := sum_range_id_mul_two k
        have : ∑ j ∈ range k, (k - (j + 1)) = ∑ j ∈ range k, (k - 1 - j) :=
          sum_congr rfl fun j _ => by omega
        rw [this, sum_range_reflect (fun j => j) k]
        omega
  calc #S ≤ k.factorial * #L := card_le_mul_card_image_of_maps_to hmaps _ hfib
    _ ≤ k.factorial * r ^ (k * (k - 1) / 2) := Nat.mul_le_mul_left _ hL

end ArtinPrimitiveRoots.L33V
end

section
/-! # L33V combinatorics: a separating prime, degenerate tuples, reindexing -/

namespace ArtinPrimitiveRoots.L33V

open Finset

/-- If both `k`-tuples (entries in `[1, M]`) are injective, one of the primes `r ≥ M^{1/k}` in a
list of at least `2k(k^2-k)` of them separates the coordinates of both modulo `r`. -/
lemma exists_good_prime (k M : ℕ) (hk : 2 ≤ k) (R : Finset ℕ)
    (hR : ∀ r ∈ R, r.Prime ∧ M ≤ r ^ k) (hcard : 2 * (k * k - k) * k ≤ #R)
    (z z' : Fin k → ℤ) (hz : ∀ i, 1 ≤ z i ∧ z i ≤ M) (hz' : ∀ i, 1 ≤ z' i ∧ z' i ≤ M)
    (hzi : Function.Injective z) (hzi' : Function.Injective z') :
    ∃ r ∈ R, injmod r z ∧ injmod r z' := by
  by_contra hcon
  push Not at hcon
  set V : ℤ := (∏ p ∈ (univ : Finset (Fin k)).offDiag, (z p.1 - z p.2)) *
    ∏ p ∈ (univ : Finset (Fin k)).offDiag, (z' p.1 - z' p.2)
  have hV0 : V ≠ 0 := mul_ne_zero
    (prod_ne_zero_iff.2 fun p hp => sub_ne_zero.2 (hzi.ne (mem_offDiag.1 hp).2.2))
    (prod_ne_zero_iff.2 fun p hp => sub_ne_zero.2 (hzi'.ne (mem_offDiag.1 hp).2.2))
  have hdvd : ∀ r ∈ R, r ∣ V.natAbs := by
    intro r hr
    rw [← Int.natCast_dvd]
    by_cases h1 : injmod r z
    · have h2 := hcon r hr h1
      unfold injmod at h2
      push Not at h2
      obtain ⟨i, l, hil, hd⟩ := h2
      exact dvd_mul_of_dvd_right (hd.trans (dvd_prod_of_mem (fun p : Fin k × Fin k => z' p.1 - z' p.2)
        (a := (i, l)) (mem_offDiag.2 ⟨mem_univ i, mem_univ l, hil⟩))) _
    · unfold injmod at h1
      push Not at h1
      obtain ⟨i, l, hil, hd⟩ := h1
      exact dvd_mul_of_dvd_left (hd.trans (dvd_prod_of_mem (fun p : Fin k × Fin k => z p.1 - z p.2)
        (a := (i, l)) (mem_offDiag.2 ⟨mem_univ i, mem_univ l, hil⟩))) _
  have hP : ∏ r ∈ R, r ∣ V.natAbs :=
    Finset.prod_primes_dvd _ (fun r hr => (hR r hr).1.prime) hdvd
  have hPle : ∏ r ∈ R, r ≤ V.natAbs := Nat.le_of_dvd (Int.natAbs_pos.2 hV0) hP
  have hoff : #((univ : Finset (Fin k)).offDiag) = k * k - k := by
    rw [offDiag_card, card_univ, Fintype.card_fin]
  have hVle : V.natAbs ≤ (M - 1) ^ (k * k - k) * (M - 1) ^ (k * k - k) := by
    simp only [V, Int.natAbs_mul]
    have e1 := map_prod Int.natAbsHom (fun p : Fin k × Fin k => z p.1 - z p.2) univ.offDiag
    have e2 := map_prod Int.natAbsHom (fun p : Fin k × Fin k => z' p.1 - z' p.2) univ.offDiag
    simp only [Int.natAbsHom_apply] at e1 e2
    rw [e1, e2, ← hoff]
    gcongr
    · exact prod_le_pow_card _ _ _ fun p _ => by
        have := hz p.1; have := hz p.2; omega
    · exact prod_le_pow_card _ _ _ fun p _ => by
        have := hz' p.1; have := hz' p.2; omega
  have hM1 : 1 ≤ M := by have := hz ⟨0, by omega⟩; omega
  have hpow : M ^ #R ≤ (∏ r ∈ R, r) ^ k := by
    rw [← prod_pow, ← prod_const]
    exact prod_le_prod' fun r hr => (hR r hr).2
  have hn0 : 2 * (k * k - k) * k ≠ 0 := by
    have : k ≤ k * k - k := by
      have : 2 * k ≤ k * k := Nat.mul_le_mul_right k hk
      omega
    exact Nat.ne_of_gt (Nat.mul_pos (Nat.mul_pos two_pos (by omega)) (by omega))
  have h1 : M ^ (2 * (k * k - k) * k) ≤ M ^ #R := Nat.pow_le_pow_right hM1 hcard
  have h2 : (∏ r ∈ R, r) ^ k ≤ ((M - 1) ^ (k * k - k) * (M - 1) ^ (k * k - k)) ^ k :=
    Nat.pow_le_pow_left (hPle.trans hVle) k
  have h3 : ((M - 1) ^ (k * k - k) * (M - 1) ^ (k * k - k)) ^ k = (M - 1) ^ (2 * (k * k - k) * k) := by
    rw [← pow_add, ← pow_mul]; ring_nf
  have h4 : (M - 1) ^ (2 * (k * k - k) * k) < M ^ (2 * (k * k - k) * k) :=
    Nat.pow_lt_pow_left (by omega) hn0
  omega

/-- A tuple with at least `k` distinct values has `k` coordinates with distinct values. -/
lemma exists_inj_comp {n k : ℕ} (x : Fin n → ℤ) (h : k ≤ #(univ.image x)) :
    ∃ g : Fin k → Fin n, Function.Injective (fun a => x (g a)) := by
  obtain ⟨S, hS, hSk⟩ := exists_subset_card_eq h
  have hpre : ∀ v ∈ S, ∃ i, x i = v := fun v hv => by simpa using hS hv
  let e : Fin k ≃ S := (S.equivFinOfCardEq hSk).symm
  have hch : ∀ a : Fin k, ∃ i, x i = (e a : ℤ) := fun a => hpre _ (e a).2
  choose g hg using hch
  refine ⟨g, fun a b hab => e.injective (Subtype.ext ?_)⟩
  simp only at hab
  rw [← hg a, ← hg b]
  exact hab

/-- Tuples with fewer than `k` distinct values. -/
lemma card_deg_le (n k M : ℕ) (hM : k - 1 ≤ M) :
    #{x ∈ Fintype.piFinset (fun _ : Fin n => Icc 1 (M : ℤ)) | #(univ.image x) < k} ≤
      M ^ (k - 1) * (k - 1) ^ n := by
  have hcardI : #(Icc 1 (M : ℤ)) = M := by simp
  calc #{x ∈ Fintype.piFinset (fun _ : Fin n => Icc 1 (M : ℤ)) | #(univ.image x) < k}
      ≤ #((powersetCard (k - 1) (Icc 1 (M : ℤ))).biUnion
          (fun S => Fintype.piFinset fun _ : Fin n => S)) := by
        apply card_le_card
        intro x hx
        rw [mem_filter, Fintype.mem_piFinset] at hx
        have hI : univ.image x ⊆ Icc 1 (M : ℤ) := by
          intro v hv
          obtain ⟨i, _, rfl⟩ := mem_image.1 hv
          exact hx.1 i
        obtain ⟨S, hIS, hSI, hSc⟩ := exists_subsuperset_card_eq hI (n := k - 1) (by omega)
          (by rw [hcardI]; exact hM)
        rw [mem_biUnion]
        refine ⟨S, mem_powersetCard.2 ⟨hSI, hSc⟩, Fintype.mem_piFinset.2 fun i => hIS ?_⟩
        exact mem_image_of_mem _ (mem_univ i)
    _ ≤ ∑ S ∈ powersetCard (k - 1) (Icc 1 (M : ℤ)), #(Fintype.piFinset fun _ : Fin n => S) :=
        card_biUnion_le
    _ = ∑ S ∈ powersetCard (k - 1) (Icc 1 (M : ℤ)), (k - 1) ^ n := by
        refine sum_congr rfl fun S hS => ?_
        rw [Fintype.card_piFinset, prod_const, card_univ, Fintype.card_fin,
          (mem_powersetCard.1 hS).2]
    _ = M.choose (k - 1) * (k - 1) ^ n := by
        rw [sum_const, card_powersetCard, hcardI, smul_eq_mul]
    _ ≤ M ^ (k - 1) * (k - 1) ^ n := Nat.mul_le_mul_right _ (Nat.choose_le_pow _ _)

/-- Complete an injection `Fin k → Fin n` to a bijection `Fin k ⊕ Fin s ≃ Fin n`. -/
lemma exists_equiv_extend {n k s : ℕ} (hn : n = k + s) (g : Fin k → Fin n)
    (hg : Function.Injective g) : ∃ e : Fin k ⊕ Fin s ≃ Fin n, ∀ a, e (Sum.inl a) = g a := by
  classical
  have hc : Fintype.card ↥(Set.range g)ᶜ = s := by
    rw [Fintype.card_compl_set, Set.card_range_of_injective hg]; simp [hn]
  let e₂ : Fin s ≃ ↥(Set.range g)ᶜ := (Fintype.equivFinOfCardEq hc).symm
  refine ⟨(Equiv.sumCongr (Equiv.ofInjective g hg) e₂).trans (Equiv.Set.sumCompl (Set.range g)),
    fun a => ?_⟩
  simp

lemma pv_split {k n s : ℕ} (e : Fin k ⊕ Fin s ≃ Fin n) (x : Fin n → ℤ) (K : ℕ) :
    pv K x = pv K (fun a => x (e (Sum.inl a))) + pv K (fun b => x (e (Sum.inr b))) := by
  funext j
  simp only [pv, Pi.add_apply]
  rw [← Equiv.sum_comp e, Fintype.sum_sum_type]

lemma card_filter_prod {α β : Type*} (A : Finset α) (B : Finset β) (P : α × β → Prop)
    [DecidablePred P] : #{p ∈ A ×ˢ B | P p} = ∑ a ∈ A, #{b ∈ B | P (a, b)} := by
  rw [card_filter, sum_product]
  simp only [card_filter]

end ArtinPrimitiveRoots.L33V
end

section
/-! # L33V: the recursive inequality (3.6) of [22] Lemma 3.2 -/

namespace ArtinPrimitiveRoots.L33V

open Finset

noncomputable section

/-- `J_{s,k}(M)`. -/
def Jc (k s M : ℕ) : ℕ := JJ k s (Icc 1 (M : ℤ))

/-- `n`-tuples with entries in `[1, M]`. -/
def tup (n M : ℕ) : Finset (Fin n → ℤ) := Fintype.piFinset fun _ : Fin n => Icc 1 (M : ℤ)

lemma mem_tup {n M : ℕ} {x : Fin n → ℤ} : x ∈ tup n M ↔ ∀ i, 1 ≤ x i ∧ x i ≤ M := by
  simp [tup, Fintype.mem_piFinset]

lemma card_tup (n M : ℕ) : #(tup n M) = M ^ n := by
  simp [tup, Fintype.card_piFinset]

/-- `k`-tuples in `[1, M]` with coordinates distinct modulo `r`. -/
def Zr (k M r : ℕ) : Finset (Fin k → ℤ) := (tup k M).filter (injmod r)

/-- The integers of `[1, M]` with `u ≡ 1 + c (mod r)`. -/
def Ucl (M r : ℕ) (c : ℤ) : Finset ℤ := (Icc 1 (M : ℤ)).filter (fun u => (u - 1) % r = c)

/-- The count `∫ |F_r|^2 |f|^{2s}`. -/
def Nr (k s M r : ℕ) : ℕ := eqc (Zr k M r ×ˢ tup s M) (fun p => pv k p.1 + pv k p.2)

/-- The count `∫ |F_r|^2 |f_c|^{2s}`. -/
def Nrc (k s M r : ℕ) (c : ℤ) : ℕ :=
  eqc (Zr k M r ×ˢ Fintype.piFinset (fun _ : Fin s => Ucl M r c)) (fun p => pv k p.1 + pv k p.2)

/-! ## The nondegenerate pairs -/

lemma count_gr_le (k s M r : ℕ) (g g' : Fin k → Fin (s + k)) :
    #{p ∈ tup (s + k) M ×ˢ tup (s + k) M | pv k p.1 = pv k p.2 ∧
      injmod r (fun a => p.1 (g a)) ∧ injmod r (fun a => p.2 (g' a))} ≤ Nr k s M r := by
  have hinj : ∀ (h : Fin k → Fin (s + k)) (x : Fin (s + k) → ℤ),
      injmod r (fun a => x (h a)) → Function.Injective h := by
    intro h x hx a b hab
    by_contra hne
    exact hx a b hne (by simp [hab])
  by_cases hg : Function.Injective g
  swap
  · rw [card_eq_zero.2]; · exact Nat.zero_le _
    exact filter_eq_empty_iff.2 fun p _ hp => hg (hinj g p.1 hp.2.1)
  by_cases hg' : Function.Injective g'
  swap
  · rw [card_eq_zero.2]; · exact Nat.zero_le _
    exact filter_eq_empty_iff.2 fun p _ hp => hg' (hinj g' p.2 hp.2.2)
  obtain ⟨e, he⟩ := exists_equiv_extend (by omega : s + k = k + s) g hg
  obtain ⟨e', he'⟩ := exists_equiv_extend (by omega : s + k = k + s) g' hg'
  have hsplit : ∀ (e : Fin k ⊕ Fin s ≃ Fin (s + k)) (g : Fin k → Fin (s + k)),
      (∀ a, e (Sum.inl a) = g a) → ∀ x : Fin (s + k) → ℤ,
      pv k x = pv k (fun a => x (g a)) + pv k (fun b => x (e (Sum.inr b))) := by
    intro e g he x
    rw [pv_split e x k]
    simp only [he]
  have hext : ∀ (e : Fin k ⊕ Fin s ≃ Fin (s + k)) (g : Fin k → Fin (s + k)),
      (∀ a, e (Sum.inl a) = g a) → ∀ x y : Fin (s + k) → ℤ, (∀ a, x (g a) = y (g a)) →
      (∀ b, x (e (Sum.inr b)) = y (e (Sum.inr b))) → x = y := by
    intro e g he x y h1 h2
    funext i
    rw [← e.apply_symm_apply i]
    rcases e.symm i with a | b
    · rw [he]; exact h1 a
    · exact h2 b
  unfold Nr eqc
  refine card_le_card_of_injOn (fun p => ((fun a => p.1 (g a), fun b => p.1 (e (Sum.inr b))),
    (fun a => p.2 (g' a), fun b => p.2 (e' (Sum.inr b))))) ?_ ?_
  · intro p hp
    simp only [coe_filter, mem_product, Set.mem_ofPred_eq] at hp
    obtain ⟨⟨h1, h2⟩, h3, h4, h5⟩ := hp
    rw [mem_tup] at h1 h2
    simp only [coe_filter, mem_product, Set.mem_ofPred_eq, Zr, mem_filter, mem_tup]
    refine ⟨⟨⟨⟨fun a => h1 _, h4⟩, fun b => h1 _⟩, ⟨fun a => h2 _, h5⟩, fun b => h2 _⟩, ?_⟩
    rw [← hsplit e g he, ← hsplit e' g' he']
    exact h3
  · intro p _ q _ hpq
    simp only [Prod.mk.injEq] at hpq
    obtain ⟨⟨a1, a2⟩, a3, a4⟩ := hpq
    exact Prod.ext (hext e g he _ _ (fun a => congrFun a1 a) (fun b => congrFun a2 b))
      (hext e' g' he' _ _ (fun a => congrFun a3 a) (fun b => congrFun a4 b))

lemma count_nondeg_le (k s M : ℕ) (hk : 2 ≤ k) (R : Finset ℕ)
    (hR : ∀ r ∈ R, r.Prime ∧ M ≤ r ^ k) (hcard : 2 * (k * k - k) * k ≤ #R) :
    #{p ∈ tup (s + k) M ×ˢ tup (s + k) M | pv k p.1 = pv k p.2 ∧
      k ≤ #(univ.image p.1) ∧ k ≤ #(univ.image p.2)} ≤
      (s + k) ^ k * (s + k) ^ k * ∑ r ∈ R, Nr k s M r := by
  classical
  calc #{p ∈ tup (s + k) M ×ˢ tup (s + k) M | pv k p.1 = pv k p.2 ∧
        k ≤ #(univ.image p.1) ∧ k ≤ #(univ.image p.2)}
      ≤ #(((univ : Finset (Fin k → Fin (s + k))) ×ˢ (univ : Finset (Fin k → Fin (s + k))) ×ˢ R).biUnion
          fun ggr => {p ∈ tup (s + k) M ×ˢ tup (s + k) M | pv k p.1 = pv k p.2 ∧
            injmod ggr.2.2 (fun a => p.1 (ggr.1 a)) ∧ injmod ggr.2.2 (fun a => p.2 (ggr.2.1 a))}) := by
        apply card_le_card
        intro p hp
        rw [mem_filter, mem_product] at hp
        obtain ⟨⟨h1, h2⟩, h3, h4, h5⟩ := hp
        obtain ⟨g, hg⟩ := exists_inj_comp p.1 h4
        obtain ⟨g', hg'⟩ := exists_inj_comp p.2 h5
        rw [mem_tup] at h1 h2
        obtain ⟨r, hr, hr1, hr2⟩ := exists_good_prime k M hk R hR hcard _ _
          (fun a => h1 (g a)) (fun a => h2 (g' a)) hg hg'
        rw [mem_biUnion]
        refine ⟨(g, g', r), mem_product.2 ⟨mem_univ _, mem_product.2 ⟨mem_univ _, hr⟩⟩, ?_⟩
        rw [mem_filter, mem_product, mem_tup, mem_tup]
        exact ⟨⟨h1, h2⟩, h3, hr1, hr2⟩
    _ ≤ ∑ ggr ∈ (univ : Finset (Fin k → Fin (s + k))) ×ˢ (univ : Finset (Fin k → Fin (s + k))) ×ˢ R,
          Nr k s M ggr.2.2 :=
        card_biUnion_le.trans (sum_le_sum fun ggr _ => count_gr_le k s M ggr.2.2 ggr.1 ggr.2.1)
    _ = (s + k) ^ k * (s + k) ^ k * ∑ r ∈ R, Nr k s M r := by
        simp only [sum_product, sum_const, card_univ, Fintype.card_fun, Fintype.card_fin,
          smul_eq_mul]
        ring

/-! ## Hölder over residue classes -/

lemma eqc_cast_eq {α : Type*} {k : ℕ} (X : Finset α) (χ : α → Fin k → ℤ) (P : ℕ) [NeZero P]
    (hb : ∀ x ∈ X, ∀ j, 0 ≤ χ x j ∧ χ x j < P) :
    eqc X (fun x j => ((χ x j : ℤ) : ZMod P)) = eqc X χ := by
  unfold eqc
  congr 1
  apply filter_congr
  intro p hp
  rw [mem_product] at hp
  constructor
  · intro h
    funext j
    have h1 := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ P).1 (congrFun h j)
    have := Int.eq_zero_of_abs_lt_dvd h1 (by
      have := hb _ hp.1 j; have := hb _ hp.2 j; rw [abs_lt]; constructor <;> linarith)
    linarith
  · intro h; exact congrArg (fun v j => ((v j : ℤ) : ZMod P)) h

lemma pv_bound {n k M : ℕ} (hM : 1 ≤ M) (x : Fin n → ℤ) (hx : ∀ i, 1 ≤ x i ∧ x i ≤ M)
    (j : Fin k) : 0 ≤ pv k x j ∧ pv k x j ≤ n * (M : ℤ) ^ k := by
  unfold pv
  constructor
  · exact sum_nonneg fun i _ => pow_nonneg (by linarith [hx i]) _
  · calc ∑ i, x i ^ ((j : ℕ) + 1) ≤ ∑ _i : Fin n, (M : ℤ) ^ k := by
          refine sum_le_sum fun i _ => ?_
          calc x i ^ ((j : ℕ) + 1) ≤ (M : ℤ) ^ ((j : ℕ) + 1) :=
                pow_le_pow_left₀ (by linarith [hx i]) (hx i).2 _
            _ ≤ (M : ℤ) ^ k := pow_le_pow_right₀ (by exact_mod_cast hM) (by have := j.2; omega)
      _ = n * (M : ℤ) ^ k := by simp

lemma Nr_le (k s M r : ℕ) (hs : 1 ≤ s) (hM : 1 ≤ M) (hr : 0 < r) :
    (Nr k s M r : ℝ) ≤ (r : ℝ) ^ (2 * s - 1) * ∑ c ∈ Ico (0 : ℤ) r, (Nrc k s M r c : ℝ) := by
  set P := (k + s) * M ^ k + 1
  have : NeZero P := ⟨by omega⟩
  have hbd : ∀ (U : Finset ℤ), U ⊆ Icc 1 (M : ℤ) →
      ∀ x ∈ Zr k M r ×ˢ Fintype.piFinset (fun _ : Fin s => U),
      ∀ j, 0 ≤ (fun p : (Fin k → ℤ) × (Fin s → ℤ) => pv k p.1 + pv k p.2) x j ∧
        (fun p : (Fin k → ℤ) × (Fin s → ℤ) => pv k p.1 + pv k p.2) x j < P := by
    intro U hU x hx j
    rw [mem_product, Zr, mem_filter, mem_tup, Fintype.mem_piFinset] at hx
    have h1 := pv_bound hM x.1 hx.1.1 j
    have h2 := pv_bound hM x.2 (fun i => by have := mem_Icc.1 (hU (hx.2 i)); exact this) j
    simp only [Pi.add_apply, P]
    push_cast
    constructor <;> nlinarith
  set χZ : (Fin k → ℤ) × (Fin s → ℤ) → Fin k → ℤ := fun p => pv k p.1 + pv k p.2
  set ζ : (Fin k → ℤ) → (Fin k → ZMod P) := fun z j => ((pv k z j : ℤ) : ZMod P)
  set φ : ℤ → (Fin k → ZMod P) := fun u j => ((u ^ ((j : ℕ) + 1) : ℤ) : ZMod P)
  have hχ : (fun p : (Fin k → ℤ) × (Fin s → ℤ) => ζ p.1 + ∑ i, φ (p.2 i)) =
      (fun p j => ((χZ p j : ℤ) : ZMod P)) := by
    funext p j
    simp only [ζ, φ, χZ, pv, Pi.add_apply, Finset.sum_apply]
    push_cast
    rfl
  have H := holder_classes (G := Fin k → ZMod P) (Zr k M r) ζ (Icc 1 (M : ℤ)) φ (Ico (0 : ℤ) r)
    (fun u => (u - 1) % r) (fun u _ => mem_Ico.2 ⟨Int.emod_nonneg _ (by omega),
      Int.emod_lt_of_pos _ (by omega)⟩) s hs
  rw [hχ, eqc_cast_eq _ χZ P (hbd _ subset_rfl)] at H
  have hc : ∀ c ∈ Ico (0 : ℤ) r, (eqc (Zr k M r ×ˢ Fintype.piFinset
      fun _ : Fin s => (Icc 1 (M : ℤ)).filter (fun u => (u - 1) % (r : ℤ) = c))
      (fun p j => ((χZ p j : ℤ) : ZMod P)) : ℝ) = Nrc k s M r c := by
    intro c _
    rw [eqc_cast_eq _ χZ P (hbd _ (filter_subset _ _))]
    rfl
  rw [sum_congr rfl hc] at H
  have hI : #(Ico (0 : ℤ) r) = r := by simp
  rw [hI] at H
  exact H

/-! ## A single residue class -/

/-- Equal power sums with the second blocks `≡ 1 + c (mod r)` give the congruences (3.5). -/
lemma cong35 {k s r : ℕ} (c : ℤ) (z z' : Fin k → ℤ) (u u' : Fin s → ℤ)
    (hu : ∀ i, (u i - 1) % r = c) (hu' : ∀ i, (u' i - 1) % r = c)
    (h : pv k z + pv k u = pv k z' + pv k u') :
    ∀ j, 1 ≤ j → j ≤ k →
      (r : ℤ) ^ j ∣ (∑ i, (z i - (1 + c)) ^ j) - ∑ i, (z' i - (1 + c)) ^ j := by
  intro j hj1 hjk
  have hx : pv k (Sum.elim z u) = pv k (Sum.elim z' u') := by
    funext l
    have := congrFun h l
    simp only [pv, Pi.add_apply] at this ⊢
    rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
    simpa using this
  have ht := congrFun (pv_translate hx (-(1 + c))) ⟨j - 1, by omega⟩
  simp only [pv, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Nat.sub_add_cancel hj1] at ht
  have hdiv : ∀ v : Fin s → ℤ, (∀ i, (v i - 1) % r = c) →
      (r : ℤ) ^ j ∣ ∑ i, (v i + -(1 + c)) ^ j := by
    intro v hv
    refine dvd_sum fun i _ => pow_dvd_pow_of_dvd ?_ j
    have := Int.mul_ediv_add_emod (v i - 1) r
    rw [hv i] at this
    exact ⟨(v i - 1) / r, by linarith⟩
  have := dvd_sub (hdiv u' hu') (hdiv u hu)
  have e : (∑ i, (z i - (1 + c)) ^ j) - ∑ i, (z' i - (1 + c)) ^ j =
      (∑ i, (u' i + -(1 + c)) ^ j) - ∑ i, (u i + -(1 + c)) ^ j := by
    simp only [sub_eq_add_neg] at ht ⊢
    linarith
  rw [e]; exact this

/-- The well-spaced pairs `(z, z')` for the class `c`. -/
def Good (k M r : ℕ) (c : ℤ) : Finset ((Fin k → ℤ) × (Fin k → ℤ)) :=
  (Zr k M r ×ˢ Zr k M r).filter (fun zz => ∀ j, 1 ≤ j → j ≤ k →
    (r : ℤ) ^ j ∣ (∑ i, (zz.1 i - (1 + c)) ^ j) - ∑ i, (zz.2 i - (1 + c)) ^ j)

lemma shift_le {s k : ℕ} (X : Finset (Fin s → ℤ)) (a b : Fin k → ℤ) :
    #{uu ∈ X ×ˢ X | a + pv k uu.1 = b + pv k uu.2} ≤ eqc X (pv k) := by
  have h := cs_fiber X X (fun u => a + pv k u) (fun u => b + pv k u)
  have e1 : eqc X (fun u => a + pv k u) = eqc X (pv k) := by
    unfold eqc; congr 1; exact filter_congr fun _ _ => add_right_inj a
  have e2 : eqc X (fun u => b + pv k u) = eqc X (pv k) := by
    unfold eqc; congr 1; exact filter_congr fun _ _ => add_right_inj b
  rw [e1, e2, ← sq] at h
  exact (Nat.pow_le_pow_iff_left two_ne_zero).1 h

lemma Nrc_le (k s M r : ℕ) (c : ℤ) :
    Nrc k s M r c ≤ #(Good k M r c) * JJ k s (Ucl M r c) := by
  set Tc := Fintype.piFinset (fun _ : Fin s => Ucl M r c)
  calc Nrc k s M r c
      ≤ #{w ∈ Good k M r c ×ˢ (Tc ×ˢ Tc) | pv k w.1.1 + pv k w.2.1 = pv k w.1.2 + pv k w.2.2} := by
        unfold Nrc eqc
        refine card_le_card_of_injOn (fun q => ((q.1.1, q.2.1), (q.1.2, q.2.2))) ?_ ?_
        · intro q hq
          simp only [coe_filter, mem_product, Set.mem_ofPred_eq] at hq
          obtain ⟨⟨⟨h1, h2⟩, h3, h4⟩, h5⟩ := hq
          simp only [coe_filter, mem_product, Set.mem_ofPred_eq, Good, mem_filter]
          refine ⟨⟨⟨⟨h1, h3⟩, cong35 c _ _ _ _ ?_ ?_ h5⟩, h2, h4⟩, h5⟩
          · intro i; exact (mem_filter.1 (Fintype.mem_piFinset.1 h2 i)).2
          · intro i; exact (mem_filter.1 (Fintype.mem_piFinset.1 h4 i)).2
        · intro q _ q' _ h
          simp only [Prod.mk.injEq] at h
          exact Prod.ext (Prod.ext h.1.1 h.2.1) (Prod.ext h.1.2 h.2.2)
    _ = ∑ zz ∈ Good k M r c, #{uu ∈ Tc ×ˢ Tc | pv k zz.1 + pv k uu.1 = pv k zz.2 + pv k uu.2} :=
        card_filter_prod _ _ _
    _ ≤ ∑ _zz ∈ Good k M r c, JJ k s (Ucl M r c) := sum_le_sum fun zz _ => shift_le Tc _ _
    _ = #(Good k M r c) * JJ k s (Ucl M r c) := by rw [sum_const, smul_eq_mul]

lemma card_Good_le (k M r : ℕ) (hr : r.Prime) (hk : k < r) (hM : M ≤ r ^ k) (c : ℤ) :
    #(Good k M r c) ≤ M ^ k * (k.factorial * r ^ (k * (k - 1) / 2)) := by
  unfold Good
  rw [card_filter_prod]
  calc ∑ z ∈ Zr k M r, #{z' ∈ Zr k M r | ∀ j, 1 ≤ j → j ≤ k →
        (r : ℤ) ^ j ∣ (∑ i, (z i - (1 + c)) ^ j) - ∑ i, (z' i - (1 + c)) ^ j}
      ≤ ∑ _z ∈ Zr k M r, k.factorial * r ^ (k * (k - 1) / 2) := by
        refine sum_le_sum fun z _ => ?_
        refine le_trans ?_ (cong_count r hr hk M hM (-c) (fun j => ∑ i, (z i - (1 + c)) ^ j))
        refine card_le_card_of_injOn (fun z' i => z' i - (1 + c)) ?_ ?_
        · intro z' hz'
          simp only [coe_filter, Zr, mem_filter, mem_tup, Set.mem_ofPred_eq] at hz'
          simp only [coe_filter, Set.mem_ofPred_eq, Fintype.mem_piFinset, mem_Icc]
          refine ⟨fun i => ⟨by linarith [hz'.1.1 i], by linarith [hz'.1.1 i]⟩, ?_, ?_⟩
          · intro i l hil hd
            exact hz'.1.2 i l hil (by convert hd using 1; ring)
          · intro j h1 h2
            exact dvd_sub_comm.1 (hz'.2 j h1 h2)
        · intro a _ b _ hab
          funext i
          have := congrFun hab i
          simpa using this
    _ = #(Zr k M r) * (k.factorial * r ^ (k * (k - 1) / 2)) := by rw [sum_const, smul_eq_mul]
    _ ≤ M ^ k * (k.factorial * r ^ (k * (k - 1) / 2)) := by
        gcongr
        rw [← card_tup k M]
        exact card_filter_le _ _

lemma JJ_Ucl_le (k s M r : ℕ) (hM : 1 ≤ M) (hr : 0 < r) (c : ℤ) :
    JJ k s (Ucl M r c) ≤ Jc k s ((M - 1) / r + 1) := by
  have hr' : (0 : ℤ) < r := by exact_mod_cast hr
  set L : ℤ := ((M : ℤ) - 1) / r
  have h1 : Ucl M r c ⊆ (Icc 0 L).image (fun w => (1 + c) + (r : ℤ) * w) := by
    intro u hu
    rw [Ucl, mem_filter, mem_Icc] at hu
    rw [mem_image]
    refine ⟨(u - 1) / r, mem_Icc.2 ⟨Int.ediv_nonneg (by linarith) hr'.le,
      Int.ediv_le_ediv hr' (by linarith)⟩, ?_⟩
    have := Int.mul_ediv_add_emod (u - 1) r
    rw [hu.2] at this
    linarith
  have h2 : Icc 0 L ⊆ (Icc 1 (L + 1)).image (fun w => (-1) + 1 * w) := by
    intro v hv
    rw [mem_Icc] at hv
    exact mem_image.2 ⟨v + 1, mem_Icc.2 ⟨by linarith, by linarith⟩, by ring⟩
  have hL : L + 1 = (((M - 1) / r + 1 : ℕ) : ℤ) := by
    have e : ((M - 1 : ℕ) : ℤ) = (M : ℤ) - 1 := by omega
    simp only [L]
    push_cast
    rw [e]
  calc JJ k s (Ucl M r c) ≤ JJ k s ((Icc 0 L).image (fun w => (1 + c) + (r : ℤ) * w)) :=
        JJ_mono k s h1
    _ ≤ JJ k s (Icc 0 L) := JJ_affine_le k s _ _ _ (by omega)
    _ ≤ JJ k s ((Icc 1 (L + 1)).image (fun w => (-1) + 1 * w)) := JJ_mono k s h2
    _ ≤ JJ k s (Icc 1 (L + 1)) := JJ_affine_le k s _ _ _ one_ne_zero
    _ = Jc k s ((M - 1) / r + 1) := by rw [Jc, hL]

/-! ## The recursive inequality (3.6) -/

lemma Nr_le_full (k s M r : ℕ) (hs : 1 ≤ s) (hM : 1 ≤ M) (hr : r.Prime) (hk : k < r)
    (hMr : M ≤ r ^ k) :
    (Nr k s M r : ℝ) ≤ (r : ℝ) ^ (2 * s) * (M : ℝ) ^ k * k.factorial *
      (r : ℝ) ^ (k * (k - 1) / 2) * Jc k s ((M - 1) / r + 1) := by
  have hr0 := hr.pos
  have hc : ∀ c ∈ Ico (0 : ℤ) r, (Nrc k s M r c : ℝ) ≤
      (M : ℝ) ^ k * k.factorial * (r : ℝ) ^ (k * (k - 1) / 2) * Jc k s ((M - 1) / r + 1) := by
    intro c _
    have h1 := Nrc_le k s M r c
    have h2 := card_Good_le k M r hr hk hMr c
    have h3 := JJ_Ucl_le k s M r hM hr0 c
    have : Nrc k s M r c ≤ M ^ k * (k.factorial * r ^ (k * (k - 1) / 2)) *
        Jc k s ((M - 1) / r + 1) :=
      h1.trans (Nat.mul_le_mul h2 h3)
    calc (Nrc k s M r c : ℝ) ≤ ((M ^ k * (k.factorial * r ^ (k * (k - 1) / 2)) *
        Jc k s ((M - 1) / r + 1) : ℕ) : ℝ) := by exact_mod_cast this
      _ = _ := by push_cast; ring
  calc (Nr k s M r : ℝ) ≤ (r : ℝ) ^ (2 * s - 1) * ∑ c ∈ Ico (0 : ℤ) r, (Nrc k s M r c : ℝ) :=
        Nr_le k s M r hs hM hr0
    _ ≤ (r : ℝ) ^ (2 * s - 1) * ∑ _c ∈ Ico (0 : ℤ) r,
          ((M : ℝ) ^ k * k.factorial * (r : ℝ) ^ (k * (k - 1) / 2) * Jc k s ((M - 1) / r + 1)) := by
        gcongr with c hc'
        exact hc c hc'
    _ = (r : ℝ) ^ (2 * s - 1 + 1) * ((M : ℝ) ^ k * k.factorial * (r : ℝ) ^ (k * (k - 1) / 2) *
          Jc k s ((M - 1) / r + 1)) := by
        rw [sum_const, Int.card_Ico, nsmul_eq_mul, pow_succ]
        simp only [sub_zero, Int.toNat_natCast]
        ring
    _ = _ := by rw [Nat.sub_add_cancel (by omega)]; ring

lemma sq_le_to_le {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (h : a ^ 2 ≤ b ^ 2 * c) :
    a ≤ b * √c := by
  have : (b * √c) ^ 2 = b ^ 2 * c := by rw [mul_pow, Real.sq_sqrt hc]
  exact (pow_le_pow_iff_left₀ ha (by positivity) two_ne_zero).1 (this ▸ h)

/-- [22] (3.6), in counting form. -/
theorem step36 (k s M : ℕ) (hk : 2 ≤ k) (hs : 1 ≤ s) (hM : k ≤ M) (R : Finset ℕ)
    (hR : ∀ r ∈ R, r.Prime ∧ k < r ∧ M ≤ r ^ k) (hcard : 2 * (k * k - k) * k ≤ #R) :
    (Jc k (s + k) M : ℝ) ≤ 2 * ((M : ℝ) ^ (k - 1) * (k : ℝ) ^ (s + k)) * √(Jc k (s + k) M : ℝ) +
      ((s + k : ℕ) : ℝ) ^ (2 * k) * ∑ r ∈ R, ((r : ℝ) ^ (2 * s) * (M : ℝ) ^ k * k.factorial *
        (r : ℝ) ^ (k * (k - 1) / 2) * Jc k s ((M - 1) / r + 1)) := by
  classical
  set T := tup (s + k) M
  set J := Jc k (s + k) M
  have hJ : J = #{p ∈ T ×ˢ T | pv k p.1 = pv k p.2} := rfl
  have hJe : J = eqc T (pv k) := rfl
  set D := T.filter (fun x => #(univ.image x) < k)
  set S1 := {p ∈ D ×ˢ T | pv k p.1 = pv k p.2}
  set S2 := {p ∈ T ×ˢ D | pv k p.1 = pv k p.2}
  set S3 := {p ∈ T ×ˢ T | pv k p.1 = pv k p.2 ∧ k ≤ #(univ.image p.1) ∧ k ≤ #(univ.image p.2)}
  have hsub : {p ∈ T ×ˢ T | pv k p.1 = pv k p.2} ⊆ S1 ∪ S2 ∪ S3 := by
    intro p hp
    rw [mem_filter, mem_product] at hp
    rw [mem_union, mem_union]
    by_cases h1 : #(univ.image p.1) < k
    · left; left
      exact mem_filter.2 ⟨mem_product.2 ⟨mem_filter.2 ⟨hp.1.1, h1⟩, hp.1.2⟩, hp.2⟩
    by_cases h2 : #(univ.image p.2) < k
    · left; right
      exact mem_filter.2 ⟨mem_product.2 ⟨hp.1.1, mem_filter.2 ⟨hp.1.2, h2⟩⟩, hp.2⟩
    · right
      exact mem_filter.2 ⟨mem_product.2 hp.1, hp.2, not_lt.1 h1, not_lt.1 h2⟩
  have hJle : (J : ℝ) ≤ #S1 + #S2 + #S3 := by
    have := (card_le_card hsub).trans ((card_union_le _ _).trans
      (Nat.add_le_add_right (card_union_le _ _) _))
    rw [← hJ] at this
    exact_mod_cast this
  have hDD : eqc D (pv k) ≤ #D ^ 2 := by
    unfold eqc; rw [sq, ← card_product]; exact card_filter_le _ _
  have hS1 : (#S1 : ℝ) ≤ #D * √J := by
    have h := cs_fiber D T (pv k) (pv k)
    rw [← hJe] at h
    have h' : #S1 ^ 2 ≤ #D ^ 2 * J := h.trans (Nat.mul_le_mul_right _ hDD)
    exact sq_le_to_le (by positivity) (by positivity) (by positivity) (by exact_mod_cast h')
  have hS2 : (#S2 : ℝ) ≤ #D * √J := by
    have h := cs_fiber T D (pv k) (pv k)
    rw [← hJe] at h
    have h' : #S2 ^ 2 ≤ #D ^ 2 * J := by
      rw [mul_comm] at h; exact h.trans (Nat.mul_le_mul_right _ hDD)
    exact sq_le_to_le (by positivity) (by positivity) (by positivity) (by exact_mod_cast h')
  have hD : (#D : ℝ) ≤ (M : ℝ) ^ (k - 1) * (k : ℝ) ^ (s + k) := by
    have h1 := card_deg_le (s + k) k M (by omega)
    have h2 : M ^ (k - 1) * (k - 1) ^ (s + k) ≤ M ^ (k - 1) * k ^ (s + k) :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
    exact_mod_cast h1.trans h2
  have hS3 : (#S3 : ℝ) ≤ ((s + k : ℕ) : ℝ) ^ (2 * k) * ∑ r ∈ R, (Nr k s M r : ℝ) := by
    have := count_nondeg_le k s M hk R (fun r hr => ⟨(hR r hr).1, (hR r hr).2.2⟩) hcard
    rw [← pow_add, ← two_mul] at this
    exact_mod_cast this
  have hS3' : ((s + k : ℕ) : ℝ) ^ (2 * k) * ∑ r ∈ R, (Nr k s M r : ℝ) ≤
      ((s + k : ℕ) : ℝ) ^ (2 * k) * ∑ r ∈ R, ((r : ℝ) ^ (2 * s) * (M : ℝ) ^ k * k.factorial *
        (r : ℝ) ^ (k * (k - 1) / 2) * Jc k s ((M - 1) / r + 1)) := by
    gcongr with r hr
    exact Nr_le_full k s M r hs (by omega) (hR r hr).1 (hR r hr).2.1 (hR r hr).2.2
  have hsq : 0 ≤ √(J : ℝ) := Real.sqrt_nonneg _
  nlinarith [mul_le_mul_of_nonneg_right hD hsq]

end

end ArtinPrimitiveRoots.L33V
end

section
/-! # L33V: real-variable bookkeeping for the iteration of (3.6) -/

namespace ArtinPrimitiveRoots.L33V

open Real

/-- `J ≤ a √J + b` implies `J ≤ a² + 2b`. -/
lemma le_of_le_sqrt {J a b : ℝ} (hJ : 0 ≤ J) (h : J ≤ a * √J + b) : J ≤ a ^ 2 + 2 * b := by
  have hs := Real.sq_sqrt hJ
  nlinarith [sq_nonneg (a - √J), Real.sqrt_nonneg J]

/-- The per-prime bound: with `Q r ≤ 2M`, `r^k ≤ B^k M` and `J_s(Q) ≤ C Q^E`,
`r^{2s} r^{K-k} J_s(Q) ≤ C 2^E B^{k^2} M^{E+k-ε/k}`, where `E = 2s - K + ε`, `2K = k^2 + k`. -/
lemma per_r (k s : ℕ) (hk : 1 ≤ k) {r M Q B C ε Kr JQ : ℝ} (hr : 1 ≤ r) (hM : 1 ≤ M)
    (hQ : 1 ≤ Q) (hQr : Q * r ≤ 2 * M) (hB : 1 ≤ B) (hrk : r ^ k ≤ B ^ k * M) (hε0 : 0 ≤ ε)
    (hεk : ε ≤ (k : ℝ) ^ 2) (hKr : 2 * Kr = (k : ℝ) ^ 2 + k) (hE0 : 0 ≤ 2 * s - Kr + ε)
    (hC : 0 ≤ C) (hJ : JQ ≤ C * Q ^ (2 * s - Kr + ε)) :
    r ^ (2 * s) * r ^ (Kr - k) * JQ ≤
      C * 2 ^ (2 * s - Kr + ε) * B ^ ((k : ℝ) ^ 2) * M ^ ((2 * s - Kr + ε) + k - ε / k) := by
  set E := 2 * (s : ℝ) - Kr + ε with hE
  have hr0 : 0 < r := by linarith
  have hM0 : 0 < M := by linarith
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  -- J_s(Q) ≤ C (2M/r)^E
  have h1 : JQ ≤ C * (2 ^ E * M ^ E / r ^ E) := by
    refine hJ.trans (mul_le_mul_of_nonneg_left ?_ hC)
    rw [← mul_rpow (by norm_num) hM0.le, ← div_rpow (by positivity) hr0.le]
    exact rpow_le_rpow (by linarith) ((le_div_iff₀ hr0).2 hQr) hE0
  -- r^{2s} r^{K-k} r^{-E} = r^{k^2 - ε}
  have h2 : r ^ (2 * s) * r ^ (Kr - k) / r ^ E = r ^ ((k : ℝ) ^ 2 - ε) := by
    rw [← rpow_natCast, ← rpow_add hr0, ← rpow_sub hr0]
    congr 1
    rw [hE]; push_cast; nlinarith
  -- r^{k^2 - ε} ≤ B^{k^2} M^{k - ε/k}
  have h3 : r ^ ((k : ℝ) ^ 2 - ε) ≤ B ^ ((k : ℝ) ^ 2) * M ^ ((k : ℝ) - ε / k) := by
    have hx : 0 ≤ ((k : ℝ) ^ 2 - ε) / k := div_nonneg (by linarith) hk0.le
    have e1 : r ^ ((k : ℝ) ^ 2 - ε) = (r ^ k) ^ (((k : ℝ) ^ 2 - ε) / k) := by
      rw [← Real.rpow_natCast r k, ← rpow_mul hr0.le]; congr 1; field_simp
    rw [e1]
    calc (r ^ k) ^ (((k : ℝ) ^ 2 - ε) / k) ≤ (B ^ k * M) ^ (((k : ℝ) ^ 2 - ε) / k) :=
          rpow_le_rpow (by positivity) hrk hx
      _ = B ^ ((k : ℝ) ^ 2 - ε) * M ^ ((k : ℝ) - ε / k) := by
          rw [mul_rpow (by positivity) hM0.le, ← Real.rpow_natCast B k, ← rpow_mul (by linarith)]
          congr 2
          · field_simp
          · field_simp
      _ ≤ B ^ ((k : ℝ) ^ 2) * M ^ ((k : ℝ) - ε / k) :=
          mul_le_mul_of_nonneg_right (rpow_le_rpow_of_exponent_le hB (by linarith)) (by positivity)
  calc r ^ (2 * s) * r ^ (Kr - k) * JQ ≤ r ^ (2 * s) * r ^ (Kr - k) * (C * (2 ^ E * M ^ E / r ^ E)) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = C * 2 ^ E * M ^ E * (r ^ (2 * s) * r ^ (Kr - k) / r ^ E) := by ring
    _ = C * 2 ^ E * M ^ E * r ^ ((k : ℝ) ^ 2 - ε) := by rw [h2]
    _ ≤ C * 2 ^ E * M ^ E * (B ^ ((k : ℝ) ^ 2) * M ^ ((k : ℝ) - ε / k)) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = C * 2 ^ E * B ^ ((k : ℝ) ^ 2) * (M ^ E * M ^ ((k : ℝ) - ε / k)) := by ring
    _ = C * 2 ^ E * B ^ ((k : ℝ) ^ 2) * M ^ (E + k - ε / k) := by
        rw [← rpow_add hM0]; ring_nf

end ArtinPrimitiveRoots.L33V
end

section
/-! # L33V: the iteration of (3.6), and `vinogradov_mean_value` -/

namespace ArtinPrimitiveRoots.L33V

open Finset Real

/-- `m` primes in `(Y, 2^m Y]`, by iterating Bertrand's postulate. -/
lemma primes_chain (m : ℕ) : ∀ Y : ℕ, 1 ≤ Y →
    ∃ R : Finset ℕ, #R = m ∧ ∀ r ∈ R, r.Prime ∧ Y < r ∧ r ≤ 2 ^ m * Y := by
  induction m with
  | zero => intro Y _; exact ⟨∅, by simp, by simp⟩
  | succ m ih =>
    intro Y hY
    obtain ⟨R, hRc, hR⟩ := ih (2 * Y) (by omega)
    obtain ⟨p, hp, hYp, hp2⟩ := Nat.exists_prime_lt_and_le_two_mul Y (by omega)
    have hpR : p ∉ R := fun h => by have := (hR p h).2.1; omega
    refine ⟨insert p R, by rw [card_insert_of_notMem hpR, hRc], ?_⟩
    intro r hr
    rcases mem_insert.1 hr with rfl | hr
    · refine ⟨hp, hYp, hp2.trans (Nat.mul_le_mul_right _ ?_)⟩
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (m + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    · obtain ⟨h1, h2, h3⟩ := hR r hr
      exact ⟨h1, by omega, h3.trans (le_of_eq (by ring))⟩

/-- `K = k(k+1)/2`. -/
def KK (k : ℕ) : ℕ := k * (k + 1) / 2

/-- The number of primes used. -/
def mm (k : ℕ) : ℕ := 2 * k ^ 3

/-- The primes lie in `(Y, 2^m Y]`, and `r ≤ BB · M^{1/k}`. -/
def BB (k : ℕ) : ℕ := 2 ^ (mm k + 1)

/-- Below `M0` the trivial bound is used. -/
def M0 (k : ℕ) : ℕ := BB k ^ 2 * k ^ k

/-- The constant of one step `s → s + k`. -/
def Lam (k s : ℕ) : ℕ :=
  M0 k ^ KK k + 4 * k ^ (2 * (s + k)) +
    2 * (s + k) ^ (2 * k) * mm k * k.factorial * 4 ^ s * BB k ^ (k ^ 2)

lemma two_KK (k : ℕ) : 2 * (KK k : ℝ) = (k : ℝ) ^ 2 + k := by
  have h : KK k * 2 = k * (k + 1) := Nat.div_mul_cancel (Nat.even_mul_succ_self k).two_dvd
  have : ((KK k * 2 : ℕ) : ℝ) = ((k * (k + 1) : ℕ) : ℝ) := by rw [h]
  push_cast at this
  linarith

lemma cast_half_pred (k : ℕ) (hk : 1 ≤ k) : ((k * (k - 1) / 2 : ℕ) : ℝ) = (KK k : ℝ) - k := by
  have h : k * (k - 1) / 2 * 2 = k * (k - 1) := by
    apply Nat.div_mul_cancel
    have := (Nat.even_mul_succ_self (k - 1)).two_dvd
    rwa [Nat.sub_add_cancel hk, mul_comm] at this
  have h2 : ((k * (k - 1) / 2 * 2 : ℕ) : ℝ) = ((k * (k - 1) : ℕ) : ℝ) := by rw [h]
  push_cast [Nat.cast_sub hk] at h2
  have := two_KK k
  linarith

lemma Jc_le_pow (k s M : ℕ) : (Jc k s M : ℝ) ≤ (M : ℝ) ^ (2 * s) := by
  have h := JJ_le_pow k s (Icc 1 (M : ℤ))
  have hc : #(Icc 1 (M : ℤ)) = M := by simp
  rw [hc] at h
  exact_mod_cast h

/-- The primes for a large `M`. -/
lemma exists_primes_large (k M : ℕ) (hk : 2 ≤ k) (hM : M0 k ≤ M) :
    ∃ R : Finset ℕ, #R = mm k ∧ ∀ r ∈ R, r.Prime ∧ k < r ∧ M ≤ r ^ k ∧
      r ^ k ≤ BB k ^ k * M ∧ r ≤ M := by
  have hBB1 : 1 ≤ BB k := Nat.one_le_two_pow
  have hBB4 : 4 ≤ BB k := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ BB k := Nat.pow_le_pow_right (by norm_num) (by
          have : 1 ≤ k ^ 3 := Nat.one_le_pow _ _ (by omega)
          unfold mm; omega)
  have hkk : k ^ k ≤ M0 k := Nat.le_mul_of_pos_left _ (by positivity)
  have hB2M : BB k ^ 2 ≤ M := (Nat.le_mul_of_pos_right _ (by positivity)).trans hM
  have hM16 : 16 ≤ M := (show 16 ≤ BB k ^ 2 by nlinarith).trans hB2M
  have hex : ∃ Y, M ≤ Y ^ k := ⟨M, Nat.le_self_pow (by omega) M⟩
  classical
  set Y := Nat.find hex
  have hY1 : M ≤ Y ^ k := Nat.find_spec hex
  have hYmin : ∀ Y' < Y, ¬ M ≤ Y' ^ k := fun Y' h => Nat.find_min hex h
  have hY2 : 2 ≤ Y := by
    by_contra h
    push Not at h
    have : Y ^ k ≤ 1 := by
      interval_cases Y
      · simp [zero_pow (by omega : k ≠ 0)]
      · simp
    omega
  have hYk : k ≤ Y := by
    by_contra h
    push Not at h
    have := Nat.pow_lt_pow_left h (by omega : k ≠ 0)
    omega
  have hYup : Y ^ k ≤ 2 ^ k * M := by
    have h1 : (Y - 1) ^ k < M := by
      have := hYmin (Y - 1) (by omega); omega
    calc Y ^ k ≤ (2 * (Y - 1)) ^ k := Nat.pow_le_pow_left (by omega) k
      _ = 2 ^ k * (Y - 1) ^ k := by rw [mul_pow]
      _ ≤ 2 ^ k * M := Nat.mul_le_mul_left _ h1.le
  obtain ⟨R, hRc, hRp⟩ := primes_chain (mm k) Y (by omega)
  refine ⟨R, hRc, fun r hr => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hRp r hr
  have hrB : r ^ k ≤ BB k ^ k * M :=
    calc r ^ k ≤ (2 ^ mm k * Y) ^ k := Nat.pow_le_pow_left h3 k
      _ = (2 ^ mm k) ^ k * Y ^ k := by rw [mul_pow]
      _ ≤ (2 ^ mm k) ^ k * (2 ^ k * M) := Nat.mul_le_mul_left _ hYup
      _ = BB k ^ k * M := by rw [BB, pow_succ, mul_pow]; ring
  have hBk : BB k ^ k ≤ M ^ (k - 1) :=
    calc BB k ^ k ≤ BB k ^ (2 * (k - 1)) := Nat.pow_le_pow_right hBB1 (by omega)
      _ = (BB k ^ 2) ^ (k - 1) := by rw [pow_mul]
      _ ≤ M ^ (k - 1) := Nat.pow_le_pow_left hB2M _
  have hrk : r ^ k ≤ M ^ k :=
    calc r ^ k ≤ BB k ^ k * M := hrB
      _ ≤ M ^ (k - 1) * M := Nat.mul_le_mul_right _ hBk
      _ = M ^ k := by rw [← pow_succ, Nat.sub_add_cancel (by omega)]
  exact ⟨h1, by omega, hY1.trans (Nat.pow_le_pow_left h2.le k), hrB,
    (Nat.pow_le_pow_iff_left (by omega)).1 hrk⟩

/-- The contribution of one prime. -/
lemma term_bound (k s : ℕ) (hk : 2 ≤ k) (C ε : ℝ) (hC : 1 ≤ C) (hε0 : 0 ≤ ε)
    (hεK : ε ≤ (KK k : ℝ)) (hE : 2 * (k : ℝ) ≤ 2 * s - KK k + ε)
    (IH : ∀ M : ℕ, 1 ≤ M → (Jc k s M : ℝ) ≤ C * (M : ℝ) ^ (2 * (s : ℝ) - KK k + ε))
    (M r : ℕ) (hM : 1 ≤ M) (hrp : r.Prime) (hrB : r ^ k ≤ BB k ^ k * M) (hrM : r ≤ M) :
    (r : ℝ) ^ (2 * s) * (M : ℝ) ^ k * k.factorial * (r : ℝ) ^ (k * (k - 1) / 2) *
      Jc k s ((M - 1) / r + 1) ≤
      k.factorial * C * 4 ^ s * (BB k : ℝ) ^ (k ^ 2) *
        (M : ℝ) ^ (2 * ((s + k : ℕ) : ℝ) - KK k + (1 - 1 / k) * ε) := by
  have hK2 := two_KK k
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hεk2 : ε ≤ (k : ℝ) ^ 2 := by nlinarith
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hM0 : (0 : ℝ) < M := by linarith
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hrp.one_lt.le
  set Q := (M - 1) / r + 1
  have hQ1n : 1 ≤ Q := Nat.le_add_left 1 _
  have hQ1 : (1 : ℝ) ≤ Q := by exact_mod_cast hQ1n
  have hQr : (Q : ℝ) * r ≤ 2 * M := by
    have : Q * r ≤ 2 * M := by
      have h1 := Nat.div_mul_le_self (M - 1) r
      calc Q * r = (M - 1) / r * r + r := by simp only [Q]; ring
        _ ≤ (M - 1) + M := Nat.add_le_add h1 hrM
        _ ≤ 2 * M := by omega
    exact_mod_cast this
  have hrk : (r : ℝ) ^ k ≤ (BB k : ℝ) ^ k * M := by exact_mod_cast hrB
  have hP := per_r k s (by omega) hr1 hM1 hQ1 hQr (by exact_mod_cast Nat.one_le_two_pow) hrk hε0
    hεk2 hK2 (by linarith) (by linarith) (IH Q hQ1n)
  have hcast : (r : ℝ) ^ (k * (k - 1) / 2) = (r : ℝ) ^ ((KK k : ℝ) - k) := by
    rw [← cast_half_pred k (by omega), rpow_natCast]
  have hBcast : (BB k : ℝ) ^ ((k : ℝ) ^ 2) = (BB k : ℝ) ^ (k ^ 2) := by
    rw [show ((k : ℝ)) ^ 2 = ((k ^ 2 : ℕ) : ℝ) by push_cast; ring, rpow_natCast]
  have h2E : (2 : ℝ) ^ (2 * (s : ℝ) - KK k + ε) ≤ 4 ^ s := by
    calc (2 : ℝ) ^ (2 * (s : ℝ) - KK k + ε) ≤ (2 : ℝ) ^ ((2 * s : ℕ) : ℝ) :=
          rpow_le_rpow_of_exponent_le (by norm_num) (by push_cast; linarith)
      _ = 4 ^ s := by rw [rpow_natCast, pow_mul]; norm_num
  have hexp : (M : ℝ) ^ k * (M : ℝ) ^ ((2 * (s : ℝ) - KK k + ε) + k - ε / k) =
      (M : ℝ) ^ (2 * ((s + k : ℕ) : ℝ) - KK k + (1 - 1 / k) * ε) := by
    rw [← Real.rpow_natCast (M : ℝ) k, ← rpow_add hM0]; congr 1; push_cast; ring
  rw [hcast]
  calc (r : ℝ) ^ (2 * s) * (M : ℝ) ^ k * k.factorial * (r : ℝ) ^ ((KK k : ℝ) - k) * Jc k s Q
      = (M : ℝ) ^ k * k.factorial * ((r : ℝ) ^ (2 * s) * (r : ℝ) ^ ((KK k : ℝ) - k) *
          Jc k s Q) := by ring
    _ ≤ (M : ℝ) ^ k * k.factorial * (C * 2 ^ (2 * (s : ℝ) - KK k + ε) *
          (BB k : ℝ) ^ ((k : ℝ) ^ 2) * (M : ℝ) ^ ((2 * (s : ℝ) - KK k + ε) + k - ε / k)) := by
        gcongr
    _ = k.factorial * C * 2 ^ (2 * (s : ℝ) - KK k + ε) * (BB k : ℝ) ^ (k ^ 2) *
          ((M : ℝ) ^ k * (M : ℝ) ^ ((2 * (s : ℝ) - KK k + ε) + k - ε / k)) := by
        rw [hBcast]; ring
    _ ≤ k.factorial * C * 4 ^ s * (BB k : ℝ) ^ (k ^ 2) *
          ((M : ℝ) ^ k * (M : ℝ) ^ ((2 * (s : ℝ) - KK k + ε) + k - ε / k)) := by
        gcongr
    _ = _ := by rw [hexp]

lemma Lam_cast (k s : ℕ) : (Lam k s : ℝ) = ((M0 k : ℕ) : ℝ) ^ KK k + 4 * (k : ℝ) ^ (2 * (s + k)) +
    2 * ((s + k : ℕ) : ℝ) ^ (2 * k) * (mm k : ℝ) * (k.factorial : ℝ) * 4 ^ s *
      (BB k : ℝ) ^ (k ^ 2) := by
  simp only [Lam]; push_cast; ring

/-- Small `M`: the trivial bound. -/
lemma step_small (k s : ℕ) (hk : 2 ≤ k) (C ε : ℝ) (hC : 1 ≤ C) (hε0 : 0 ≤ ε) (M : ℕ) (hM : 1 ≤ M) (hsmall : M < M0 k) :
    (Jc k (s + k) M : ℝ) ≤
      Lam k s * C * (M : ℝ) ^ (2 * ((s + k : ℕ) : ℝ) - KK k + (1 - 1 / k) * ε) := by
  set E' := 2 * ((s + k : ℕ) : ℝ) - KK k + (1 - 1 / k) * ε with hE'def
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hM0 : (0 : ℝ) < M := by linarith
  have hpowE' : (0 : ℝ) < (M : ℝ) ^ E' := rpow_pos_of_pos hM0 _
  have hLam : ((M0 k : ℕ) : ℝ) ^ KK k ≤ Lam k s := by
    rw [Lam_cast]
    have : (0 : ℝ) ≤ 2 * ((s + k : ℕ) : ℝ) ^ (2 * k) * (mm k : ℝ) * (k.factorial : ℝ) * 4 ^ s *
      (BB k : ℝ) ^ (k ^ 2) := by positivity
    have : (0 : ℝ) ≤ 4 * (k : ℝ) ^ (2 * (s + k)) := by positivity
    linarith
  have hLam0 : (0 : ℝ) ≤ Lam k s := Nat.cast_nonneg _
  calc (Jc k (s + k) M : ℝ) ≤ (M : ℝ) ^ (2 * (s + k)) := Jc_le_pow k (s + k) M
    _ = (M : ℝ) ^ E' * (M : ℝ) ^ (2 * ((s + k : ℕ) : ℝ) - E') := by
        rw [← rpow_add hM0, ← rpow_natCast]; congr 1; push_cast; ring
    _ ≤ (M : ℝ) ^ E' * (M : ℝ) ^ ((KK k : ℕ) : ℝ) := by
        refine mul_le_mul_of_nonneg_left (rpow_le_rpow_of_exponent_le hM1 ?_) hpowE'.le
        rw [hE'def]
        have : 0 ≤ (1 - 1 / (k : ℝ)) * ε := mul_nonneg (by
          rw [sub_nonneg, div_le_one hk0]; exact_mod_cast (show 1 ≤ k by omega)) hε0
        linarith
    _ = (M : ℝ) ^ E' * (M : ℝ) ^ (KK k) := by rw [rpow_natCast]
    _ ≤ (M : ℝ) ^ E' * ((M0 k : ℕ) : ℝ) ^ (KK k) := by
        gcongr
    _ ≤ (M : ℝ) ^ E' * (Lam k s : ℝ) := mul_le_mul_of_nonneg_left hLam hpowE'.le
    _ ≤ Lam k s * C * (M : ℝ) ^ E' := by
        nlinarith [mul_nonneg (mul_nonneg hLam0 hpowE'.le) (sub_nonneg.2 hC)]

/-- One step of the iteration: `J_s ≤ C M^{2s-K+ε}` gives
`J_{s+k} ≤ Λ C M^{2(s+k)-K+(1-1/k)ε}`. -/
theorem step_real (k s : ℕ) (hk : 2 ≤ k) (hs : k ≤ s) (C ε : ℝ) (hC : 1 ≤ C) (hε0 : 0 ≤ ε)
    (hεK : ε ≤ (KK k : ℝ)) (hE : 2 * (k : ℝ) ≤ 2 * s - KK k + ε)
    (IH : ∀ M : ℕ, 1 ≤ M → (Jc k s M : ℝ) ≤ C * (M : ℝ) ^ (2 * (s : ℝ) - KK k + ε))
    (M : ℕ) (hM : 1 ≤ M) :
    (Jc k (s + k) M : ℝ) ≤
      Lam k s * C * (M : ℝ) ^ (2 * ((s + k : ℕ) : ℝ) - KK k + (1 - 1 / k) * ε) := by
  by_cases hsmall : M < M0 k
  · exact step_small k s hk C ε hC hε0 M hM hsmall
  push Not at hsmall
  set E' := 2 * ((s + k : ℕ) : ℝ) - KK k + (1 - 1 / k) * ε with hE'def
  have hK2 := two_KK k
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hM0 : (0 : ℝ) < M := by linarith
  have hJ0 : (0 : ℝ) ≤ Jc k (s + k) M := Nat.cast_nonneg _
  have hpowE' : (0 : ℝ) < (M : ℝ) ^ E' := rpow_pos_of_pos hM0 _
  have hkM : k ≤ M := (Nat.le_self_pow (by omega) k).trans
    ((Nat.le_mul_of_pos_left _ (pow_pos (Nat.two_pow_pos _) 2)).trans hsmall)
  obtain ⟨R, hRc, hR⟩ := exists_primes_large k M hk hsmall
  have hcard : 2 * (k * k - k) * k ≤ #R := by
    rw [hRc, mm]
    have : (k * k - k) * k ≤ k * k * k := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
    nlinarith
  have h36 := step36 k s M hk (by omega) hkM R
    (fun r hr => ⟨(hR r hr).1, (hR r hr).2.1, (hR r hr).2.2.1⟩) hcard
  have hsum : ∑ r ∈ R, ((r : ℝ) ^ (2 * s) * (M : ℝ) ^ k * k.factorial *
      (r : ℝ) ^ (k * (k - 1) / 2) * Jc k s ((M - 1) / r + 1)) ≤
      mm k * (k.factorial * C * 4 ^ s * (BB k : ℝ) ^ (k ^ 2) * (M : ℝ) ^ E') := by
    calc _ ≤ ∑ _r ∈ R, (k.factorial * C * 4 ^ s * (BB k : ℝ) ^ (k ^ 2) * (M : ℝ) ^ E') :=
          sum_le_sum fun r hr => term_bound k s hk C ε hC hε0 hεK hE IH M r hM (hR r hr).1
            (hR r hr).2.2.2.1 (hR r hr).2.2.2.2
      _ = _ := by rw [sum_const, hRc, nsmul_eq_mul]
  have hb := le_of_le_sqrt hJ0 h36
  have hεk2 : ε ≤ (k : ℝ) ^ 2 := by nlinarith
  have hεdk : ε / k ≤ k := by rw [div_le_iff₀ hk0]; nlinarith
  have ha : (2 * ((M : ℝ) ^ (k - 1) * (k : ℝ) ^ (s + k))) ^ 2 ≤
      4 * (k : ℝ) ^ (2 * (s + k)) * (M : ℝ) ^ E' := by
    have : (M : ℝ) ^ (2 * (k - 1)) ≤ (M : ℝ) ^ E' := by
      rw [← rpow_natCast]
      refine rpow_le_rpow_of_exponent_le hM1 ?_
      have : E' = (2 * (s : ℝ) - KK k + ε) + k + (k - ε / k) := by
        rw [hE'def]; push_cast; ring
      rw [this]; push_cast [Nat.cast_sub (by omega : 1 ≤ k)]; linarith
    calc (2 * ((M : ℝ) ^ (k - 1) * (k : ℝ) ^ (s + k))) ^ 2 =
          4 * (k : ℝ) ^ (2 * (s + k)) * (M : ℝ) ^ (2 * (k - 1)) := by ring
      _ ≤ 4 * (k : ℝ) ^ (2 * (s + k)) * (M : ℝ) ^ E' := by gcongr
  have hS := mul_le_mul_of_nonneg_left hsum (by positivity : (0 : ℝ) ≤ ((s + k : ℕ) : ℝ) ^ (2 * k))
  set W := (M : ℝ) ^ E'
  set A := 4 * (k : ℝ) ^ (2 * (s + k))
  set B' := 2 * ((s + k : ℕ) : ℝ) ^ (2 * k) * (mm k : ℝ) * (k.factorial : ℝ) * 4 ^ s *
    (BB k : ℝ) ^ (k ^ 2)
  set Z := ((M0 k : ℕ) : ℝ) ^ KK k
  have e1 : 2 * (((s + k : ℕ) : ℝ) ^ (2 * k) * (mm k * (k.factorial * C * 4 ^ s *
      (BB k : ℝ) ^ (k ^ 2) * W))) = B' * C * W := by simp only [B']; ring
  have hLamc : (Lam k s : ℝ) = Z + A + B' := Lam_cast k s
  have hZ : 0 ≤ Z := by positivity
  have hA : 0 ≤ A := by positivity
  have h1 : A * W ≤ A * C * W := by
    have := mul_le_mul_of_nonneg_left hC (mul_nonneg hA hpowE'.le)
    linarith
  have h2 : 0 ≤ Z * C * W := by positivity
  rw [hLamc]
  linarith

end ArtinPrimitiveRoots.L33V
end

section
/-! # L33V: the iteration and `vinogradov_mean_value` ([22] Lemma 3.2) -/

namespace ArtinPrimitiveRoots.L33V

open Finset Real

/-- An exponent bounding `log₂ Λ(k, s)`. -/
def X (k s : ℕ) : ℕ := (2 * (mm k + 1) + k * k) * (k * k) + (2 + k * (2 * (s + k))) +
  (1 + (s + k) * (2 * k) + mm k + k * k + 2 * s + (mm k + 1) * k ^ 2) + 2

lemma X_mono (k : ℕ) {s s' : ℕ} (h : s ≤ s') : X k s ≤ X k s' := by
  unfold X; gcongr

lemma Lam_le (k s : ℕ) : Lam k s ≤ 2 ^ X k s := by
  set e1 := (2 * (mm k + 1) + k * k) * (k * k)
  set e2 := 2 + k * (2 * (s + k))
  set e3 := 1 + (s + k) * (2 * k) + mm k + k * k + 2 * s + (mm k + 1) * k ^ 2
  have hk2 : k ≤ 2 ^ k := Nat.lt_two_pow_self.le
  have hkk : k ^ k ≤ 2 ^ (k * k) := by rw [pow_mul]; exact Nat.pow_le_pow_left hk2 k
  have hfact : k.factorial ≤ 2 ^ (k * k) := (Nat.factorial_le_pow k).trans hkk
  have hKK : KK k ≤ k * k := Nat.div_le_of_le_mul (by nlinarith)
  have t1 : M0 k ^ KK k ≤ 2 ^ e1 := by
    have : M0 k ≤ 2 ^ (2 * (mm k + 1) + k * k) :=
      calc M0 k = (2 ^ (mm k + 1)) ^ 2 * k ^ k := rfl
        _ ≤ (2 ^ (mm k + 1)) ^ 2 * 2 ^ (k * k) := Nat.mul_le_mul_left _ hkk
        _ = 2 ^ (2 * (mm k + 1) + k * k) := by rw [← pow_mul, ← pow_add, mul_comm (mm k + 1) 2]
    calc M0 k ^ KK k ≤ (2 ^ (2 * (mm k + 1) + k * k)) ^ KK k := Nat.pow_le_pow_left this _
      _ = 2 ^ ((2 * (mm k + 1) + k * k) * KK k) := by rw [← pow_mul]
      _ ≤ 2 ^ e1 := Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left _ hKK)
  have t2 : 4 * k ^ (2 * (s + k)) ≤ 2 ^ e2 := by
    calc 4 * k ^ (2 * (s + k)) ≤ 2 ^ 2 * (2 ^ k) ^ (2 * (s + k)) :=
          Nat.mul_le_mul (by norm_num) (Nat.pow_le_pow_left hk2 _)
      _ = 2 ^ e2 := by rw [← pow_mul, ← pow_add]
  have t3 : 2 * (s + k) ^ (2 * k) * mm k * k.factorial * 4 ^ s * BB k ^ (k ^ 2) ≤ 2 ^ e3 := by
    have a1 : (s + k) ^ (2 * k) ≤ 2 ^ ((s + k) * (2 * k)) := by
      rw [pow_mul 2 (s + k) (2 * k)]; exact Nat.pow_le_pow_left Nat.lt_two_pow_self.le _
    have a2 : mm k ≤ 2 ^ mm k := Nat.lt_two_pow_self.le
    have a3 : 4 ^ s = 2 ^ (2 * s) := by rw [pow_mul]; norm_num
    have a4 : BB k ^ (k ^ 2) = 2 ^ ((mm k + 1) * k ^ 2) := by rw [BB, ← pow_mul]
    calc 2 * (s + k) ^ (2 * k) * mm k * k.factorial * 4 ^ s * BB k ^ (k ^ 2)
        ≤ 2 ^ 1 * 2 ^ ((s + k) * (2 * k)) * 2 ^ mm k * 2 ^ (k * k) * 2 ^ (2 * s) *
            2 ^ ((mm k + 1) * k ^ 2) := by
          rw [a3, a4, pow_one]; gcongr
      _ = 2 ^ e3 := by simp only [← pow_add]; rfl
  have hX : X k s = e1 + e2 + e3 + 2 := rfl
  have h4 : 2 ^ e1 + 2 ^ e2 + 2 ^ e3 ≤ 2 ^ X k s := by
    have b1 : 2 ^ e1 ≤ 2 ^ (e1 + e2 + e3) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have b2 : 2 ^ e2 ≤ 2 ^ (e1 + e2 + e3) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have b3 : 2 ^ e3 ≤ 2 ^ (e1 + e2 + e3) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have : 2 ^ X k s = 4 * 2 ^ (e1 + e2 + e3) := by rw [hX, pow_add]; ring
    omega
  unfold Lam
  omega

/-- The iteration: after `n` steps, `s = (n+1)k` and `ε = K(1-1/k)^n`. -/
theorem iterate (k : ℕ) (hk : 2 ≤ k) : ∀ n : ℕ, ∀ M : ℕ, 1 ≤ M →
    (Jc k ((n + 1) * k) M : ℝ) ≤ 2 ^ (n * X k ((n + 1) * k)) *
      (M : ℝ) ^ (2 * (((n + 1) * k : ℕ) : ℝ) - KK k + KK k * (1 - 1 / (k : ℝ)) ^ n) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hK2 := two_KK k
  intro n
  induction n with
  | zero =>
    intro M hM
    have := Jc_le_pow k k M
    simp only [zero_add, one_mul, zero_mul, pow_zero, mul_one]
    rw [show 2 * (k : ℝ) - KK k + KK k = ((2 * k : ℕ) : ℝ) by push_cast; ring, rpow_natCast]
    exact this
  | succ n ih =>
    intro M hM
    set s := (n + 1) * k with hsdef
    have hs : k ≤ s := Nat.le_mul_of_pos_left k (by omega)
    set ε := (KK k : ℝ) * (1 - 1 / (k : ℝ)) ^ n with hεdef
    have h1k : 1 / (k : ℝ) ≤ 1 := by rw [div_le_one hk0]; exact_mod_cast (show 1 ≤ k by omega)
    have hq0 : 0 ≤ 1 - 1 / (k : ℝ) := by linarith
    have hq1 : 1 - 1 / (k : ℝ) ≤ 1 := by linarith [show (0 : ℝ) ≤ 1 / (k : ℝ) by positivity]
    have hε0 : 0 ≤ ε := mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hq0 _)
    have hεK : ε ≤ KK k := mul_le_of_le_one_right (Nat.cast_nonneg _) (pow_le_one₀ hq0 hq1)
    have hE : 2 * (k : ℝ) ≤ 2 * (s : ℝ) - KK k + ε := by
      have hb := one_add_mul_le_pow (a := -(1 / (k : ℝ))) (by linarith) n
      rw [← sub_eq_add_neg] at hb
      have h2 : (KK k : ℝ) * (1 + n * -(1 / (k : ℝ))) ≤ ε :=
        mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg _)
      have hs' : (s : ℝ) = (n + 1) * k := by rw [hsdef]; push_cast; ring
      have h3 : (KK k : ℝ) * (n * (1 / (k : ℝ))) = n * (k + 1) / 2 := by
        field_simp
        nlinarith
      rw [hs']
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      have h4 : (KK k : ℝ) * (1 + n * -(1 / (k : ℝ))) = KK k - KK k * (n * (1 / (k : ℝ))) := by
        ring
      have h5 : (n : ℝ) * 1 ≤ n * k :=
        mul_le_mul_of_nonneg_left (by exact_mod_cast (show 1 ≤ k by omega)) hn
      linarith
    have hC : (1 : ℝ) ≤ 2 ^ (n * X k s) := one_le_pow₀ (by norm_num)
    have hstep := step_real k s hk hs (2 ^ (n * X k s)) ε hC hε0 hεK hE ih M hM
    have hsk : s + k = (n + 1 + 1) * k := by rw [hsdef]; ring
    have hexp : 2 * ((s + k : ℕ) : ℝ) - KK k + (1 - 1 / (k : ℝ)) * ε =
        2 * (((n + 1 + 1) * k : ℕ) : ℝ) - KK k + KK k * (1 - 1 / (k : ℝ)) ^ (n + 1) := by
      rw [hsk, hεdef]; ring
    rw [hexp, hsk] at hstep
    refine hstep.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
    calc (Lam k s : ℝ) * 2 ^ (n * X k s) ≤ (2 : ℝ) ^ (X k s) * 2 ^ (n * X k s) := by
          gcongr; exact_mod_cast Lam_le k s
      _ = 2 ^ ((n + 1) * X k s) := by rw [← pow_add]; ring_nf
      _ ≤ 2 ^ ((n + 1) * X k ((n + 1 + 1) * k)) :=
          pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_left _ (X_mono k (by rw [hsdef]; nlinarith)))

lemma eps_small (k : ℕ) (hk : 2 ≤ k) :
    (KK k : ℝ) * (1 - 1 / (k : ℝ)) ^ (10 * k ^ 2) ≤ 1 / 100 := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hq0 : 0 ≤ 1 - 1 / (k : ℝ) := by
    have : 1 / (k : ℝ) ≤ 1 := by rw [div_le_one hk0]; linarith
    linarith
  have h1 : (1 - 1 / (k : ℝ)) ^ k ≤ exp (-1) :=
    Real.one_sub_div_pow_le_exp_neg (by linarith)
  have h2 : (1 - 1 / (k : ℝ)) ^ (10 * k ^ 2) ≤ exp (-(10 * k)) := by
    rw [show 10 * k ^ 2 = k * (10 * k) by ring, pow_mul]
    calc ((1 - 1 / (k : ℝ)) ^ k) ^ (10 * k) ≤ (exp (-1)) ^ (10 * k) :=
          pow_le_pow_left₀ (pow_nonneg hq0 _) h1 _
      _ = exp (-(10 * k)) := by rw [← Real.exp_nat_mul]; push_cast; ring_nf
  have h3 : (KK k : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith [two_KK k]
  have h4 : 100 * (k : ℝ) ^ 2 ≤ exp (10 * k) := by
    have := Real.pow_div_factorial_le_exp (10 * k) (by positivity) 3
    norm_num [Nat.factorial] at this
    nlinarith
  have h5 : exp (-(10 * (k : ℝ))) * exp (10 * k) = 1 := by rw [← Real.exp_add]; simp
  have h6 : 0 ≤ (1 - 1 / (k : ℝ)) ^ (10 * k ^ 2) := pow_nonneg hq0 _
  have h7 : 0 < exp (-(10 * (k : ℝ))) := Real.exp_pos _
  calc (KK k : ℝ) * (1 - 1 / (k : ℝ)) ^ (10 * k ^ 2) ≤ (k : ℝ) ^ 2 * exp (-(10 * k)) := by
        gcongr
    _ ≤ 1 / 100 := by nlinarith

lemma nX_le (k : ℕ) (hk : 2 ≤ k) :
    10 * k ^ 2 * X k ((10 * k ^ 2 + 1) * k) ≤ 400 * k ^ 7 := by
  have e : 10 * k ^ 2 * X k ((10 * k ^ 2 + 1) * k) =
      60 * k ^ 7 + 410 * k ^ 6 + 220 * k ^ 5 + 120 * k ^ 4 + 20 * k ^ 3 + 50 * k ^ 2 := by
    unfold X mm; ring
  rw [e]
  have h6 : 2 * k ^ 6 ≤ k ^ 7 := by rw [pow_succ]; nlinarith [Nat.zero_le (k ^ 6)]
  have h5 : 2 * k ^ 5 ≤ k ^ 6 := by rw [pow_succ]; nlinarith [Nat.zero_le (k ^ 5)]
  have h4 : 2 * k ^ 4 ≤ k ^ 5 := by rw [pow_succ]; nlinarith [Nat.zero_le (k ^ 4)]
  have h3 : 2 * k ^ 3 ≤ k ^ 4 := by rw [pow_succ]; nlinarith [Nat.zero_le (k ^ 3)]
  have h2 : 2 * k ^ 2 ≤ k ^ 3 := by rw [pow_succ]; nlinarith [Nat.zero_le (k ^ 2)]
  omega

end ArtinPrimitiveRoots.L33V

namespace ArtinPrimitiveRoots

open Real

end ArtinPrimitiveRoots
end

section
open ArtinPrimitiveRoots
open Real
theorem solution :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ ∀ k : ℕ, 2 ≤ k →
      ∃ s : ℕ, k ≤ s ∧ (s : ℝ) ≤ C₁ * (k : ℝ) ^ 4 ∧ ∀ M : ℕ, 1 ≤ M →
        (vinogradovCount s k M : ℝ) ≤
          exp (C₁ * (k : ℝ) ^ C₂) *
            (M : ℝ) ^ (2 * (s : ℝ) - ((k * (k + 1) / 2 : ℕ) : ℝ) + 1 / 100) := by
  refine ⟨400, 7, by norm_num, by norm_num, fun k hk => ?_⟩
  refine ⟨(10 * k ^ 2 + 1) * k, Nat.le_mul_of_pos_left k (by omega), ?_, fun M hM => ?_⟩
  · have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
    push_cast
    nlinarith [pow_pos (by linarith : (0 : ℝ) < k) 3]
  · have h1 := L33V.vinogradovCount_le_JJ ((10 * k ^ 2 + 1) * k) k M
    have h2 := L33V.iterate k hk (10 * k ^ 2) M hM
    have h3 := L33V.eps_small k hk
    have hX : (2 : ℝ) ^ (10 * k ^ 2 * L33V.X k ((10 * k ^ 2 + 1) * k)) ≤
        exp (400 * (k : ℝ) ^ (7 : ℝ)) := by
      have hnat := L33V.nX_le k hk
      have h2e : (2 : ℝ) ≤ exp 1 := by linarith [Real.add_one_le_exp 1]
      calc (2 : ℝ) ^ (10 * k ^ 2 * L33V.X k ((10 * k ^ 2 + 1) * k))
          ≤ (exp 1) ^ (10 * k ^ 2 * L33V.X k ((10 * k ^ 2 + 1) * k)) :=
            pow_le_pow_left₀ (by norm_num) h2e _
        _ = exp ((10 * k ^ 2 * L33V.X k ((10 * k ^ 2 + 1) * k) : ℕ) : ℝ) := by
            rw [← Real.exp_nat_mul, mul_one]
        _ ≤ exp (400 * (k : ℝ) ^ (7 : ℝ)) := by
            rw [show ((7 : ℝ)) = ((7 : ℕ) : ℝ) by norm_num, rpow_natCast]
            gcongr
            exact_mod_cast hnat
    have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
    calc (vinogradovCount ((10 * k ^ 2 + 1) * k) k M : ℝ)
        ≤ (L33V.Jc k ((10 * k ^ 2 + 1) * k) M : ℝ) := by exact_mod_cast h1
      _ ≤ 2 ^ (10 * k ^ 2 * L33V.X k ((10 * k ^ 2 + 1) * k)) *
          (M : ℝ) ^ (2 * (((10 * k ^ 2 + 1) * k : ℕ) : ℝ) - L33V.KK k +
            L33V.KK k * (1 - 1 / (k : ℝ)) ^ (10 * k ^ 2)) := h2
      _ ≤ exp (400 * (k : ℝ) ^ (7 : ℝ)) *
          (M : ℝ) ^ (2 * (((10 * k ^ 2 + 1) * k : ℕ) : ℝ) - L33V.KK k +
            L33V.KK k * (1 - 1 / (k : ℝ)) ^ (10 * k ^ 2)) :=
        mul_le_mul_of_nonneg_right hX (by positivity)
      _ ≤ exp (400 * (k : ℝ) ^ (7 : ℝ)) *
          (M : ℝ) ^ (2 * (((10 * k ^ 2 + 1) * k : ℕ) : ℝ) - L33V.KK k + 1 / 100) :=
        mul_le_mul_of_nonneg_left (rpow_le_rpow_of_exponent_le hM1 (by linarith [h3]))
          (by positivity)
end
