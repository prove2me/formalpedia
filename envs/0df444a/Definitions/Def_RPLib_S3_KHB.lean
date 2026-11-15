-- Prove2me | Definitions.Def_RPLib_S3_KHB
-- name    : RPLib_S3_KHB
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T15:35:30.495402+00:00
-- url     : https://prove2.me/theorems/98cbf5e6-e71d-47cf-b013-ba1567e3429f
-- title:
--   Kronecker-Hurwitz class number relation: the telescoping identity
-- statement:
--   The telescoping identity.
--
--   `Xn n` : matrices of determinant `n` with positive bottom row. `N ↦ N T` and `N ↦ N T'` are bijections of `Xn n`
--   onto its parts `R < S` and `S < R`; with `local_id` the sum of `wt(N) + wt(N S)` over `Xn n` telescopes:
--   **`tele`** : `∑ᶠ_{Xn n} (wN N + wN (N S)) = ∑ᶠ_{Xn n, R = S} kN N`. All supports lie in the box `|·| ≤ 2n`.
--
--   **Formalization note.** Library module of an elementary formalization of the Kronecker-Hurwitz class number relation $\sum_{t^2 \le 4n} H(4n - t^2) = 2\sigma(n) - \sum_{d \mid n} \min(d, n/d)$ (Popa-Zagier's tessellation proof, recast as a telescoping identity over integer matrices of determinant $n$), part of a formalization of the Ramanujan-Petersson conjecture in weight two. It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   A. A. Popa and D. Zagier, A combinatorial refinement of the Kronecker-Hurwitz class number relation, arXiv:1604.02822 (2016); L. Kronecker, Über die Anzahl der verschiedenen Classen quadratischer Formen von negativer Determinante, J. reine angew. Math. 57 (1860), 248-255; A. Hurwitz, Über Relationen zwischen Classenanzahlen binärer quadratischer Formen von negativer Determinante, Math. Ann. 25 (1885), 157-196; H. Cohen, A Course in Computational Algebraic Number Theory, GTM 138, Springer 1993, Section 5.3

import Mathlib
import Definitions.Def_RPLib_S3_KHA

/-!
# S3-KH, part B: the telescoping identity

`Xn n` : matrices of determinant `n` with positive bottom row. `N ↦ N T` and `N ↦ N T'` are bijections of `Xn n`
onto its parts `R < S` and `S < R`; with `local_id` the sum of `wt(N) + wt(N S)` over `Xn n` telescopes:
**`tele`** : `∑ᶠ_{Xn n} (wN N + wN (N S)) = ∑ᶠ_{Xn n, R = S} kN N`. All supports lie in the box `|·| ≤ 2n`.
-/

set_option autoImplicit false

namespace RamanujanPetersson.S3.KH

/-- Determinant `n`, positive bottom row. -/
def Xn (n : ℤ) : Set (ℤ × ℤ × ℤ × ℤ) := {N | det4 N = n ∧ 0 < N.2.2.1 ∧ 0 < N.2.2.2}

/-- The box `|coordinates| ≤ K`. -/
noncomputable def box (K : ℤ) : Finset (ℤ × ℤ × ℤ × ℤ) :=
  Finset.Icc (-K) K ×ˢ Finset.Icc (-K) K ×ˢ Finset.Icc (-K) K ×ˢ Finset.Icc (-K) K

lemma kp_ne {A B C : ℤ} (h : kp A B C ≠ 0) : B ≤ A ∧ A ≤ C := by
  by_contra hc
  apply h
  rcases not_and_or.1 hc with h1 | h1
  · rw [kp, hs_neg (by omega : A - B < 0), cor_l (by omega : A - B ≠ 0)]; ring
  · rw [kp, hs_neg (by omega : C - A < 0), cor_r (by omega : C - A ≠ 0)]; ring

lemma wt_ne {A B C : ℤ} (hA : 0 < A) (h : wt A B C ≠ 0) : 0 ≤ B ∧ B ≤ A ∧ A ≤ C := by
  by_contra hc
  apply h
  have : B < 0 ∨ A < B ∨ C < A := by omega
  rcases this with h1 | h1 | h1
  · rw [wt, hs_neg h1, cor_l (by omega : A - B ≠ 0)]; ring
  · rw [wt, hs_neg (by omega : A - B < 0), cor_l (by omega : A - B ≠ 0)]; ring
  · rw [wt, hs_neg (by omega : C - A < 0), cor_r (by omega : C - A ≠ 0)]; ring

/-- A matrix of `Xn n` in the cone `S - P ≤ R ≤ -Q` lies in the box `2n`. -/
lemma cone_box {n : ℤ} {N : ℤ × ℤ × ℤ × ℤ} (hN : N ∈ Xn n)
    (h1 : N.2.2.2 - N.1 ≤ N.2.2.1) (h2 : N.2.2.1 ≤ -N.2.1) : N ∈ box (2 * n) := by
  obtain ⟨P, Q, R, S⟩ := N
  obtain ⟨hd, hR, hS⟩ := hN
  simp only [det4] at hd h1 h2 hR hS
  have hP : S - R ≤ P := by linarith
  have e1 : (S - R) * S ≤ P * S := mul_le_mul_of_nonneg_right hP hS.le
  have e2 : R * R ≤ (-Q) * R := mul_le_mul_of_nonneg_right h2 hR.le
  have hRS : R * S ≤ n := by nlinarith [sq_nonneg (S - R), e1, e2]
  have hR' : R ≤ n := by nlinarith
  have hS' : S ≤ n := by nlinarith
  have hPu : P * S ≤ n := by nlinarith
  have hPn : P ≤ n := by rcases le_or_gt P 0 with h | h <;> nlinarith
  have hQ : -Q * R ≤ 2 * n := by nlinarith
  have hQn : -Q ≤ 2 * n := by nlinarith
  simp only [box, Finset.mem_product, Finset.mem_Icc]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> nlinarith

lemma supp_k (n : ℤ) {s : Set (ℤ × ℤ × ℤ × ℤ)} (hs : s ⊆ Xn n) :
    Function.support (s.indicator kN) ⊆ ↑(box (2 * n)) := by
  classical
  intro N hN
  rw [Function.mem_support] at hN
  by_cases hX : N ∈ s
  swap
  · rw [Set.indicator_of_notMem hX] at hN; exact absurd rfl hN
  rw [Set.indicator_of_mem hX] at hN
  have h := kp_ne hN
  exact cone_box (hs hX) h.1 h.2

lemma supp_w (n : ℤ) :
    Function.support ((Xn n).indicator (fun N => wN N + wN (mS N))) ⊆ ↑(box (2 * n)) := by
  classical
  intro N hN
  rw [Function.mem_support] at hN
  by_cases hX : N ∈ Xn n
  swap
  · rw [Set.indicator_of_notMem hX] at hN; exact absurd rfl hN
  rw [Set.indicator_of_mem hX] at hN
  obtain ⟨P, Q, R, S⟩ := N
  have hR : 0 < R := hX.2.1
  have hS : 0 < S := hX.2.2
  by_cases h0 : wN (P, Q, R, S) = 0
  · rw [h0, zero_add] at hN
    have h := wt_ne (A := S) hS (by simpa [wN, mS] using hN)
    exact cone_box hX (by simp only; linarith) (by simp only; linarith)
  · have h := wt_ne (A := R) hR (by simpa [wN] using h0)
    exact cone_box hX (by simp only; linarith) (by simp only; linarith)

/-- `N ↦ N T` as an equivalence. -/
def eT : (ℤ × ℤ × ℤ × ℤ) ≃ (ℤ × ℤ × ℤ × ℤ) where
  toFun := mT
  invFun N := (N.1, N.2.1 - N.1, N.2.2.1, N.2.2.2 - N.2.2.1)
  left_inv N := by rcases N with ⟨a, b, c, d⟩; simp [mT]
  right_inv N := by rcases N with ⟨a, b, c, d⟩; simp [mT]

/-- `N ↦ N T'` as an equivalence. -/
def eT' : (ℤ × ℤ × ℤ × ℤ) ≃ (ℤ × ℤ × ℤ × ℤ) where
  toFun := mT'
  invFun N := (N.1 - N.2.1, N.2.1, N.2.2.1 - N.2.2.2, N.2.2.2)
  left_inv N := by rcases N with ⟨a, b, c, d⟩; simp [mT']
  right_inv N := by rcases N with ⟨a, b, c, d⟩; simp [mT']

lemma mem_T {n : ℤ} (N : ℤ × ℤ × ℤ × ℤ) :
    mT N ∈ Xn n ∩ {N | N.2.2.1 < N.2.2.2} ↔ N ∈ Xn n := by
  rcases N with ⟨P, Q, R, S⟩
  simp only [Xn, mT, det4, Set.mem_inter_iff, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨⟨h1, h2, -⟩, h4⟩; exact ⟨by linarith, h2, by linarith⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨⟨by linarith, h2, by linarith⟩, by linarith⟩

lemma mem_T' {n : ℤ} (N : ℤ × ℤ × ℤ × ℤ) :
    mT' N ∈ Xn n ∩ {N | N.2.2.2 < N.2.2.1} ↔ N ∈ Xn n := by
  rcases N with ⟨P, Q, R, S⟩
  simp only [Xn, mT', det4, Set.mem_inter_iff, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨⟨h1, -, h3⟩, h4⟩; exact ⟨by linarith, by linarith, h3⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨⟨by linarith, by linarith, h3⟩, by linarith⟩

/-- **Telescoping.** -/
theorem tele (n : ℤ) :
    ∑ᶠ N, (Xn n).indicator (fun N => wN N + wN (mS N)) N =
      ∑ᶠ N, (Xn n ∩ {N | N.2.2.1 = N.2.2.2}).indicator kN N := by
  classical
  set f1 := (Xn n ∩ {N : ℤ × ℤ × ℤ × ℤ | N.2.2.1 < N.2.2.2}).indicator kN with hf1
  set f2 := (Xn n ∩ {N : ℤ × ℤ × ℤ × ℤ | N.2.2.2 < N.2.2.1}).indicator kN with hf2
  set f0 := (Xn n ∩ {N : ℤ × ℤ × ℤ × ℤ | N.2.2.1 = N.2.2.2}).indicator kN with hf0
  have hfin : ∀ s ⊆ Xn n, (Function.support (s.indicator kN)).Finite := fun s hs =>
    (box (2 * n)).finite_toSet.subset (supp_k n hs)
  have hpt : ∀ N, (Xn n).indicator (fun N => wN N + wN (mS N)) N =
      (Xn n).indicator kN N - f1 (eT N) - f2 (eT' N) := by
    intro N
    have e1 := mem_T (n := n) N
    have e2 := mem_T' (n := n) N
    by_cases hX : N ∈ Xn n
    · rw [Set.indicator_of_mem hX, Set.indicator_of_mem hX]
      simp only [hf1, hf2, eT, eT', Equiv.coe_fn_mk]
      rw [Set.indicator_of_mem (e1.2 hX), Set.indicator_of_mem (e2.2 hX)]
      rcases N with ⟨P, Q, R, S⟩
      have := local_id P Q R S hX.2.1 hX.2.2
      linarith
    · rw [Set.indicator_of_notMem hX, Set.indicator_of_notMem hX]
      simp only [hf1, hf2, eT, eT', Equiv.coe_fn_mk]
      rw [Set.indicator_of_notMem (fun h => hX (e1.1 h)), Set.indicator_of_notMem (fun h => hX (e2.1 h))]
      ring
  have hsplit : ∀ N, (Xn n).indicator kN N = f0 N + f1 N + f2 N := by
    intro N
    simp only [hf0, hf1, hf2, Set.indicator_apply, Set.mem_inter_iff, Set.mem_ofPred_eq]
    by_cases hX : N ∈ Xn n
    · rcases lt_trichotomy N.2.2.1 N.2.2.2 with h | h | h
      · simp [hX, h, h.ne, not_lt.2 h.le]
      · simp [hX, h]
      · simp [hX, h, h.ne', not_lt.2 h.le]
    · simp [hX]
  have h1f : (Function.support fun N => f1 (eT N)).Finite :=
    (hfin _ Set.inter_subset_left).preimage eT.injective.injOn
  have h2f : (Function.support fun N => f2 (eT' N)).Finite :=
    (hfin _ Set.inter_subset_left).preimage eT'.injective.injOn
  rw [finsum_congr hpt,
    finsum_sub_distrib (((hfin _ le_rfl).union h1f).subset (Function.support_sub _ _)) h2f,
    finsum_sub_distrib (hfin _ le_rfl) h1f, finsum_comp_equiv eT (f := f1), finsum_comp_equiv eT' (f := f2),
    finsum_congr hsplit,
    finsum_add_distrib (((hfin _ Set.inter_subset_left).union (hfin _ Set.inter_subset_left)).subset
      (Function.support_add _ _)) (hfin _ Set.inter_subset_left),
    finsum_add_distrib (hfin _ Set.inter_subset_left) (hfin _ Set.inter_subset_left)]
  ring

end RamanujanPetersson.S3.KH


