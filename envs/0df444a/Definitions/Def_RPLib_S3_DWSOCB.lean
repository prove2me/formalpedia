-- Prove2me | Definitions.Def_RPLib_S3_DWSOCB
-- name    : RPLib_S3_DWSOCB
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T18:01:05.998234+00:00
-- url     : https://prove2.me/theorems/7b2e9910-312e-4a57-8636-d03701f88164
-- title:
--   Weight-two Ramanujan-Petersson library: the ordinary upper bound (O3 + O9(i)), conditional on Tate
-- statement:
--   The ordinary upper bound (O3 + O9(i)), conditional on Tate.
--
--   * `card_le_of_fibers` : a finset whose `g`-fibres have at most `B` elements has at most `#T · B` elements.
--   * `TS F M t` : the pairs `(b, c) ∈ Y₁(M)(F)` whose Tate curve has trace `t`.
--   * `disc_eq_of_ord`, `f_mem_fset_of_ord`, `not_dvd_f_of_ord` : `t² - 4q = f² D'`, `f ∈ fset D`, `p ∤ f`.
--   * `card_fib_le` : under `TateIsogenyPrimeToP`, the trace-`t` pairs of content `f` number at most
--     `#redPrim(D/f²) · L_f / s(D/f²)` (Pic-class partition, each class inside one `yclSet`).
--   * **`pairCount_le_ellCount`** : `p ∤ t ⇒ pairCount F M t ≤ ellCount M 1 t q` (DWSOrdinary (i)).
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture in weight two (Eichler-Shimura-Ihara route: the Eichler-Selberg trace formula on $S_2(\Gamma_1(M))$, the Deuring-Waterhouse-Schoof count of elliptic curves over $\mathbb F_q$ with level structure by Hurwitz class numbers, conditional on Tate's isogeny theorem in prime-to-$p$ form, the Kronecker-Hurwitz class number relation, and the Hasse-Weil bound for the components of $Y_1(M)$ by the Stepanov-Bombieri method). It contains definitions together with proved lemmas (no `sorry`; where Tate's theorem is used it is an explicit hypothesis), so that later solution files can import them.
-- source:
--   M. Deuring, Die Typen der Multiplikatorenringe elliptischer Funktionenkörper, Abh. Math. Sem. Univ. Hamburg 14 (1941), 197-272; W. C. Waterhouse, Abelian varieties over finite fields, Ann. Sci. École Norm. Sup. (4) 2 (1969), 521-560; R. Schoof, Nonsingular plane cubic curves over finite fields, J. Combin. Theory Ser. A 46 (1987), 183-211; J. H. Silverman, The Arithmetic of Elliptic Curves, 2nd ed., GTM 106, Springer 2009, Chapters III and V; Y. Ihara, Hecke polynomials as congruence zeta functions in elliptic modular case, Ann. of Math. 85 (1967), 267-295; M. Eichler, Quaternäre quadratische Formen und die Riemannsche Vermutung für die Kongruenzzetafunktion, Arch. Math. 5 (1954), 355-366; G. Shimura, Introduction to the Arithmetic Theory of Automorphic Functions, Princeton 1971, Chapter 7

import Mathlib
import Definitions.Def_RPLib_S3_DWSOR
import Definitions.Def_RPLib_S3_DWSTateY

/-!
# S3-DWS-Ordinary, part CB: the ordinary upper bound (O3 + O9(i)), conditional on Tate

* `card_le_of_fibers` : a finset whose `g`-fibres have at most `B` elements has at most `#T · B` elements.
* `TS F M t` : the pairs `(b, c) ∈ Y₁(M)(F)` whose Tate curve has trace `t`.
* `disc_eq_of_ord`, `f_mem_fset_of_ord`, `not_dvd_f_of_ord` : `t² - 4q = f² D'`, `f ∈ fset D`, `p ∤ f`.
* `card_fib_le` : under `TateIsogenyPrimeToP`, the trace-`t` pairs of content `f` number at most
  `#redPrim(D/f²) · L_f / s(D/f²)` (Pic-class partition, each class inside one `yclSet`).
* **`pairCount_le_ellCount`** : `p ∤ t ⇒ pairCount F M t ≤ ellCount M 1 t q` (DWSOrdinary (i)).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open WeierstrassCurve WeierstrassCurve.Affine RPLib.TateNF

namespace RamanujanPetersson.S3.DWSO

open RPLib.Weil RPLib.Isog RPLib.Hasse RPLib.DWS RamanujanPetersson.Hurwitz

lemma card_le_of_fibers {α β : Type*} [DecidableEq β] (s : Finset α) (g : α → β) (T : Finset β)
    (hg : ∀ x ∈ s, g x ∈ T) (B : ℕ) (hB : ∀ x ∈ s, (s.filter (fun y => g y = g x)).card ≤ B) :
    s.card ≤ T.card * B := by
  rw [Finset.card_eq_sum_card_fiberwise (f := g) (t := T) (fun x hx => hg x hx)]
  calc ∑ b ∈ T, (s.filter (fun y => g y = b)).card ≤ ∑ _b ∈ T, B := by
        apply Finset.sum_le_sum
        intro b _
        by_cases h : ∃ x ∈ s, g x = b
        · obtain ⟨x, hx, rfl⟩ := h
          exact hB x hx
        · push_neg at h
          rw [Finset.card_eq_zero.mpr (Finset.filter_eq_empty_iff.mpr fun y hy => h y hy)]
          exact Nat.zero_le _
    _ = T.card * B := by rw [Finset.sum_const, smul_eq_mul]

lemma sD_pos (D : ℤ) : 0 < QA.sD D := by unfold QA.sD; split_ifs <;> norm_num

/-- The pairs `(b, c) ∈ Y₁(M)(F)` whose Tate curve has trace `t`. -/
abbrev TS (F : Type) [Field F] [DecidableEq F] (M : ℕ) (t : ℤ) : Type :=
  {bc : F × F // bc ∈ Y1 F M ∧ RPLib.EllFq.trace (tate bc.1 bc.2) = t}

/-- The Tate curve of a pair. -/
abbrev TS.W {F : Type} [Field F] [DecidableEq F] {M : ℕ} {t : ℤ} (x : TS F M t) : WeierstrassCurve F :=
  tate x.1.1 x.1.2

instance TS.isElliptic {F : Type} [Field F] [DecidableEq F] {M : ℕ} {t : ℤ} (x : TS F M t) :
    x.W.IsElliptic :=
  ⟨by show IsUnit (tate x.1.1 x.1.2).Δ; rw [tate_Δ]; exact isUnit_iff_ne_zero.mpr x.2.1.1⟩

lemma TS.trace_W {F : Type} [Field F] [DecidableEq F] {M : ℕ} {t : ℤ} (x : TS F M t) :
    RPLib.EllFq.trace x.W = t := x.2.2

lemma card_filter_le_ycl {F : Type} [Field F] [Fintype F] [DecidableEq F] {M : ℕ} {t : ℤ}
    (s : Finset (TS F M t)) (x : TS F M t) (h : ∀ y ∈ s, ∃ C : VariableChange F, C • x.W = y.W) :
    s.card ≤ Nat.card (yclSet x.W M) := by
  classical
  rw [Nat.card_coe_set_eq]
  have hsub : ((s.map ⟨Subtype.val, Subtype.val_injective⟩ : Finset (F × F)) : Set (F × F)) ⊆
      yclSet x.W M := by
    intro bc hbc
    simp only [Finset.coe_map, Function.Embedding.coeFn_mk, Set.mem_image, Finset.mem_coe] at hbc
    obtain ⟨y, hy, rfl⟩ := hbc
    exact ⟨y.2.1, h y hy⟩
  calc s.card = (s.map ⟨Subtype.val, Subtype.val_injective⟩).card := (Finset.card_map _).symm
    _ = ((s.map ⟨Subtype.val, Subtype.val_injective⟩ : Finset (F × F)) : Set (F × F)).ncard :=
        (Set.ncard_coe_finset _).symm
    _ ≤ (yclSet x.W M).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)

section Disc

variable {F : Type*} [Field F] [Fintype F] {L : Type*} [Field L] [Algebra F L] [IsAlgClosed L] [DecidableEq L]
  {W : WeierstrassCurve F} [W.IsElliptic]

theorem disc_eq_of_ord (d : OrdData W L) :
    RPLib.EllFq.trace W ^ 2 - 4 * (Fintype.card F : ℤ) = d.f ^ 2 * (tr d.w ^ 2 + 4 * -(deg d.w : ℤ)) := by
  rw [d.htr, d.hq]; ring

theorem div_eq_of_ord (d : OrdData W L) :
    (RPLib.EllFq.trace W ^ 2 - 4 * (Fintype.card F : ℤ)) / d.f ^ 2 = tr d.w ^ 2 + 4 * -(deg d.w : ℤ) := by
  rw [disc_eq_of_ord d, Int.mul_ediv_cancel_left _ (pow_ne_zero 2 d.f_pos.ne')]

theorem f_mem_fset_of_ord (d : OrdData W L) :
    d.f ∈ fset (RPLib.EllFq.trace W ^ 2 - 4 * (Fintype.card F : ℤ)) := by
  have hf := d.f_pos
  have hn := d.disc_neg
  unfold fset
  rw [Finset.mem_filter, Finset.mem_Icc, disc_eq_of_ord d]
  generalize tr d.w ^ 2 + 4 * -(deg d.w : ℤ) = X at hn ⊢
  have h1 : X ≤ -1 := by omega
  have h2 : d.f ≤ d.f ^ 2 := by nlinarith
  refine ⟨⟨by omega, ?_⟩, dvd_mul_right _ _⟩
  rw [abs_of_neg (mul_neg_of_pos_of_neg (by positivity) (by omega))]
  nlinarith [mul_le_mul_of_nonneg_left h1 (sq_nonneg d.f)]

theorem not_dvd_f_of_ord {p : ℕ} [Fact p.Prime] [CharP F p] (d : OrdData W L)
    (hpt : ¬ (p : ℤ) ∣ RPLib.EllFq.trace W) : ¬ (p : ℤ) ∣ d.f := by
  intro hpf
  apply hpt
  have hpq : (p : ℤ) ∣ (Fintype.card F : ℤ) := by
    obtain ⟨n, -, hn⟩ := FiniteField.card F p
    rw [hn]; push_cast; exact dvd_pow_self _ n.ne_zero
  have hD : (p : ℤ) ∣ RPLib.EllFq.trace W ^ 2 := by
    have h1 : (p : ℤ) ∣ d.f ^ 2 * (tr d.w ^ 2 + 4 * -(deg d.w : ℤ)) := (dvd_pow hpf two_ne_zero).mul_right _
    rw [← disc_eq_of_ord d] at h1
    have h2 := dvd_add h1 (hpq.mul_left 4)
    simpa using h2
  exact (Nat.prime_iff_prime_int.mp (Fact.out : p.Prime)).dvd_of_dvd_pow hD

end Disc

end RamanujanPetersson.S3.DWSO


