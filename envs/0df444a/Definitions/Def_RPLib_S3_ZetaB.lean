-- Prove2me | Definitions.Def_RPLib_S3_ZetaB
-- name    : RPLib_S3_ZetaB
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T16:27:43.037849+00:00
-- url     : https://prove2.me/theorems/bab36fa8-beb9-4fe9-b5c7-e3b074a9b4b2
-- title:
--   Weight-two Ramanujan-Petersson library: the index `δ`, divisor classes and the counting formula for `A_n`
-- statement:
--   The index `δ`, divisor classes and the counting formula for `A_n`.
--
--   * `delta Fq F`: the least positive degree of a divisor; every divisor degree is a multiple of it, so
--     `A_n = 0` unless `δ ∣ n` (`numEff_eq_zero_of_not_dvd`).
--   * `newton_delta`: the Newton identity compressed to multiples of `δ`.
--   * Divisor classes `Divisor ⧸ princ`. With full constant field (`constField Fq F = ⊥`), every class of degree
--     `n ≥ 2g - 1` has `(q ^ (n + 1 - g) - 1) / (q - 1)` effective members and the number of such classes does not
--     depend on `n ∈ δℕ`, whence `numEff_formula` : `(q - 1) A_n = h (q ^ (n + 1 - g) - 1)` and the linear recurrence
--     `numEff_rec` : `A_{n+2δ} + q^δ A_n = (1 + q^δ) A_{n+δ}` for `δ ∣ n`, `n ≥ 2g - 1`.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture in weight two (Eichler-Shimura-Ihara route: the Eichler-Selberg trace formula on $S_2(\Gamma_1(M))$, the Deuring-Waterhouse-Schoof count of elliptic curves over $\mathbb F_q$ with level structure by Hurwitz class numbers, conditional on Tate's isogeny theorem in prime-to-$p$ form, the Kronecker-Hurwitz class number relation, and the Hasse-Weil bound for the components of $Y_1(M)$ by the Stepanov-Bombieri method). It contains definitions together with proved lemmas (no `sorry`; where Tate's theorem is used it is an explicit hypothesis), so that later solution files can import them.
-- source:
--   H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer 2009, Chapters 1 and 5; E. Bombieri, Counting points on curves over finite fields (d'après S. A. Stepanov), Séminaire Bourbaki 430 (1973); A. Weil, Sur les courbes algébriques et les variétés qui s'en déduisent, Hermann 1948

import Mathlib
import Definitions.Def_RPLib_S3_ZetaA
import Definitions.Def_RPLib_S3_RRD

/-!
# S3-ZetaSB, O5 part B: the index `δ`, divisor classes and the counting formula for `A_n`

* `delta Fq F`: the least positive degree of a divisor; every divisor degree is a multiple of it, so
  `A_n = 0` unless `δ ∣ n` (`numEff_eq_zero_of_not_dvd`).
* `newton_delta`: the Newton identity compressed to multiples of `δ`.
* Divisor classes `Divisor ⧸ princ`. With full constant field (`constField Fq F = ⊥`), every class of degree
  `n ≥ 2g - 1` has `(q ^ (n + 1 - g) - 1) / (q - 1)` effective members and the number of such classes does not
  depend on `n ∈ δℕ`, whence `numEff_formula` : `(q - 1) A_n = h (q ^ (n + 1 - g) - 1)` and the linear recurrence
  `numEff_rec` : `A_{n+2δ} + q^δ A_n = (1 + q^δ) A_{n+δ}` for `δ ∣ n`, `n ≥ 2g - 1`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial

namespace RamanujanPetersson.ZetaSB

open Places RR

section Delta

variable (Fq : Type*) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (F : Type*) [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]

/-- The degree as an additive homomorphism. -/
noncomputable def degHom : Divisor Fq F →+ ℤ := AddMonoidHom.mk' Divisor.deg Divisor.deg_add

theorem deg_zsmul (k : ℤ) (D : Divisor Fq F) : Divisor.deg (k • D) = k * Divisor.deg D := by
  have h := map_zsmul (degHom Fq F) k D
  simpa only [degHom, AddMonoidHom.mk'_apply, smul_eq_mul] using h

theorem exists_pos_deg : ∃ n : ℕ, 0 < n ∧ ∃ D : Divisor Fq F, Divisor.deg D = n := by
  obtain ⟨P⟩ := nonempty_infPlace Fq F
  refine ⟨Place.deg (Fq := Fq) (F := F) (Sum.inr P), Place.deg_pos _, Finsupp.single (Sum.inr P) 1, ?_⟩
  rw [Divisor.deg_single, one_mul]

/-- `δ`: the least positive degree of a divisor. -/
noncomputable def delta : ℕ := sInf {n : ℕ | 0 < n ∧ ∃ D : Divisor Fq F, Divisor.deg D = n}

theorem delta_mem : 0 < delta Fq F ∧ ∃ D : Divisor Fq F, Divisor.deg D = delta Fq F :=
  Nat.sInf_mem (exists_pos_deg Fq F)

theorem delta_pos : 0 < delta Fq F := (delta_mem Fq F).1

theorem delta_le {n : ℕ} (hn : 0 < n) {D : Divisor Fq F} (hD : Divisor.deg D = n) : delta Fq F ≤ n :=
  Nat.sInf_le ⟨hn, D, hD⟩

theorem delta_dvd_deg (D : Divisor Fq F) : (delta Fq F : ℤ) ∣ Divisor.deg D := by
  obtain ⟨hδ, D0, hD0⟩ := delta_mem Fq F
  have hδ' : (0 : ℤ) < delta Fq F := by exact_mod_cast hδ
  apply Int.dvd_of_emod_eq_zero
  have h0 := Int.emod_nonneg (Divisor.deg D) hδ'.ne'
  have h1 := Int.emod_lt_of_pos (Divisor.deg D) hδ'
  have h2 := Int.emod_add_ediv_mul (Divisor.deg D) (delta Fq F)
  have hE : Divisor.deg (D - (Divisor.deg D / delta Fq F) • D0) = Divisor.deg D % delta Fq F := by
    rw [Divisor.deg_sub, deg_zsmul, hD0]
    linarith
  generalize Divisor.deg D % (delta Fq F : ℤ) = r at h0 h1 hE ⊢
  by_contra hne
  have := delta_le Fq F (n := r.toNat) (by omega) (D := D - (Divisor.deg D / delta Fq F) • D0)
    (by rw [hE]; omega)
  omega

theorem numEff_eq_zero_of_not_dvd {n : ℕ} (hn : ¬ delta Fq F ∣ n) : numEff Fq F n = 0 := by
  rw [numEff, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  intro D hD
  rw [mem_effDivs] at hD
  have := delta_dvd_deg Fq F D
  rw [hD.2] at this
  exact hn (Int.natCast_dvd_natCast.mp this)

/-- The Newton identity compressed to multiples of `δ`:
`δ k A_{δk} = Σ_{j=1}^k N_{δj} A_{δ(k-j)}`. -/
theorem newton_delta (k : ℕ) :
    delta Fq F * k * numEff Fq F (delta Fq F * k) =
      ∑ j ∈ Finset.Icc 1 k, numPoints Fq F (delta Fq F * j) * numEff Fq F (delta Fq F * (k - j)) := by
  have hδ := delta_pos Fq F
  rw [newton]
  symm
  have himg : ∑ j ∈ Finset.Icc 1 k, numPoints Fq F (delta Fq F * j) * numEff Fq F (delta Fq F * (k - j)) =
      ∑ m ∈ (Finset.Icc 1 k).image (delta Fq F * ·), numPoints Fq F m * numEff Fq F (delta Fq F * k - m) := by
    rw [Finset.sum_image (fun a _ b _ h => Nat.eq_of_mul_eq_mul_left hδ h)]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Nat.mul_sub]
  rw [himg]
  apply Finset.sum_subset
  · intro m hm
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hm
    rw [Finset.mem_Icc] at hj ⊢
    exact ⟨le_trans hj.1 (Nat.le_mul_of_pos_left j hδ), Nat.mul_le_mul_left _ hj.2⟩
  · intro m hm hnot
    rw [Finset.mem_Icc] at hm
    have hnd : ¬ delta Fq F ∣ (delta Fq F * k - m) := by
      rintro ⟨c, hc⟩
      by_cases hmd : delta Fq F ∣ m
      · obtain ⟨j, rfl⟩ := hmd
        apply hnot
        refine Finset.mem_image.mpr ⟨j, Finset.mem_Icc.mpr ⟨?_, ?_⟩, rfl⟩
        · rcases Nat.eq_zero_or_pos j with h | h
          · subst h; omega
          · exact h
        · exact Nat.le_of_mul_le_mul_left hm.2 hδ
      · apply hmd
        refine ⟨k - c, ?_⟩
        rw [Nat.mul_sub]
        omega
    simp only [numEff_eq_zero_of_not_dvd Fq F hnd, mul_zero]

end Delta

section Classes

variable (Fq : Type*) [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable (F : Type*) [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]

theorem div_one' : (Places.div (1 : F) : Divisor Fq F) = 0 :=
  (Places.div_eq_zero_iff Fq F one_ne_zero).mpr (one_mem _)

variable {F} in
theorem div_inv' {f : F} (hf : f ≠ 0) : (Places.div f⁻¹ : Divisor Fq F) = -Places.div f := by
  rw [← one_div, Places.div_div one_ne_zero hf, div_one', zero_sub]

variable {F} in
theorem div_algebraMap {c : Fq} (hc : c ≠ 0) : (Places.div (algebraMap Fq F c) : Divisor Fq F) = 0 :=
  (Places.div_eq_zero_iff Fq F ((_root_.map_ne_zero _).mpr hc)).mpr (IntermediateField.algebraMap_mem _ c)

/-- The principal divisors. -/
noncomputable def princ : AddSubgroup (Divisor Fq F) where
  carrier := {D | ∃ f : F, f ≠ 0 ∧ (Places.div f : Divisor Fq F) = D}
  add_mem' := by
    rintro _ _ ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
    exact ⟨f * g, mul_ne_zero hf hg, Places.div_mul hf hg⟩
  zero_mem' := ⟨1, one_ne_zero, div_one' Fq F⟩
  neg_mem' := by
    rintro _ ⟨f, hf, rfl⟩
    exact ⟨f⁻¹, inv_ne_zero hf, div_inv' Fq hf⟩

theorem mem_princ {D : Divisor Fq F} :
    D ∈ princ Fq F ↔ ∃ f : F, f ≠ 0 ∧ (Places.div f : Divisor Fq F) = D := Iff.rfl

/-- The divisor class of `D`. -/
noncomputable abbrev cls (D : Divisor Fq F) : Divisor Fq F ⧸ princ Fq F := QuotientAddGroup.mk D

variable {Fq F}

theorem cls_div_add {f : F} (hf : f ≠ 0) (D : Divisor Fq F) :
    cls Fq F (Places.div f + D) = cls Fq F D := by
  apply QuotientAddGroup.eq.mpr
  refine (mem_princ Fq F).mpr ⟨f⁻¹, inv_ne_zero hf, ?_⟩
  rw [div_inv' Fq hf]
  abel

theorem finite_LF (D : Divisor Fq F) : (LF Fq F D : Set F).Finite := by
  have := Data.finite_LD (ffData_axioms0 (Fq := Fq) (F := F)) D
  exact Set.finite_coe_iff.mp this

/-- With full constant field, every divisor of degree `n ≥ 2g - 1` is equivalent to an effective one. -/
theorem exists_eff_of_deg (hk : constField Fq F = ⊥) {n : ℕ} (hn : 2 * (genusF Fq F : ℤ) - 1 ≤ n)
    (D : Divisor Fq F) (hD : Divisor.deg D = n) :
    ∃ E ∈ effDivs Fq F n, cls Fq F E = cls Fq F D := by
  have h1 := riemann_inequalityF' hk D
  rw [hD] at h1
  have hpos : 0 < ellF Fq F D := by
    have : (0 : ℤ) < ellF Fq F D := by omega
    exact_mod_cast this
  obtain ⟨f, hfL, hf0⟩ := Data.exists_ne_zero_of_ell_pos hpos
  refine ⟨Places.div f + D, mem_effDivs.mpr ⟨(mem_LF hf0).mp hfL, ?_⟩, cls_div_add hf0 D⟩
  rw [Divisor.deg_add, Places.deg_div hf0, hD, zero_add]

theorem ellF_of_mem (hk : constField Fq F = ⊥) {n : ℕ} (hn : 2 * (genusF Fq F : ℤ) - 1 ≤ n)
    {E : Divisor Fq F} (hE : E ∈ effDivs Fq F n) : ellF Fq F E = n + 1 - genusF Fq F := by
  have hd := (mem_effDivs.mp hE).2
  have := ellF_eq_of_deg hk (D := E) (by rw [hd]; exact hn)
  rw [hd] at this
  omega

variable [DecidableEq (Divisor Fq F ⧸ princ Fq F)]

variable (Fq F) in
/-- The number of divisor classes containing an effective divisor of degree `n`. -/
noncomputable def hcl (n : ℕ) : ℕ := ((effDivs Fq F n).image (cls Fq F)).card

/-- A class with an effective member `E0` has `(q ^ ℓ(E0) - 1) / (q - 1)` effective members. -/
theorem card_fiber_mul (hk : constField Fq F = ⊥) {n : ℕ} {E0 : Divisor Fq F} (hE0 : E0 ∈ effDivs Fq F n) :
    ((effDivs Fq F n).filter fun E => cls Fq F E = cls Fq F E0).card * (Fintype.card Fq - 1) =
      Fintype.card Fq ^ ellF Fq F E0 - 1 := by
  classical
  set Fib := (effDivs Fq F n).filter fun E => cls Fq F E = cls Fq F E0 with hFib
  set T := (finite_LF E0).toFinset.filter (· ≠ (0 : F)) with hT
  have hTmem : ∀ f, f ∈ T ↔ f ∈ LF Fq F E0 ∧ f ≠ 0 := by
    intro f
    rw [hT, Finset.mem_filter, Set.Finite.mem_toFinset]
    rfl
  have hcardT : T.card = Fintype.card Fq ^ ellF Fq F E0 - 1 := by
    have h1 : Nat.card (LF Fq F E0) = (finite_LF E0).toFinset.card := Nat.card_eq_card_finite_toFinset _
    have h0 : (0 : F) ∈ (finite_LF E0).toFinset := by
      rw [Set.Finite.mem_toFinset]
      exact (LF Fq F E0).zero_mem
    rw [hT, Finset.filter_ne', Finset.card_erase_of_mem h0, ← h1, card_LF]
  have hmaps : ∀ f ∈ T, (Places.div f + E0 : Divisor Fq F) ∈ Fib := by
    intro f hf
    obtain ⟨hfL, hf0⟩ := (hTmem f).mp hf
    rw [hFib, Finset.mem_filter, mem_effDivs]
    refine ⟨⟨(mem_LF hf0).mp hfL, ?_⟩, cls_div_add hf0 E0⟩
    rw [Divisor.deg_add, Places.deg_div hf0, zero_add]
    exact (mem_effDivs.mp hE0).2
  rw [← hcardT, Finset.card_eq_sum_card_fiberwise hmaps, Finset.card_eq_sum_ones Fib, Finset.sum_mul]
  refine Finset.sum_congr rfl fun E hE => ?_
  rw [one_mul]
  rw [hFib, Finset.mem_filter, mem_effDivs] at hE
  obtain ⟨⟨hEnn, -⟩, hEc⟩ := hE
  obtain ⟨f0, hf0, hdiv⟩ := (mem_princ Fq F).mp (QuotientAddGroup.eq.mp hEc.symm)
  have hE' : E = Places.div f0 + E0 := by rw [hdiv]; abel
  have hf0L : f0 ∈ LF Fq F E0 := (mem_LF hf0).mpr (hE' ▸ hEnn)
  have hfib : T.filter (fun f => Places.div f + E0 = E) =
      (Finset.univ.erase (0 : Fq)).image (fun c => algebraMap Fq F c * f0) := by
    ext f
    rw [Finset.mem_filter, hTmem, Finset.mem_image]
    constructor
    · rintro ⟨⟨_, hf⟩, hφ⟩
      rw [hE'] at hφ
      have hdd : (Places.div (f / f0) : Divisor Fq F) = 0 := by
        rw [Places.div_div hf hf0]
        exact sub_eq_zero.mpr (add_right_cancel hφ)
      have hmem := (Places.div_eq_zero_iff Fq F (div_ne_zero hf hf0)).mp hdd
      rw [hk, IntermediateField.mem_bot] at hmem
      obtain ⟨c, hc⟩ := hmem
      have hfc : f = algebraMap Fq F c * f0 := by rw [hc, div_mul_cancel₀ f hf0]
      refine ⟨c, Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩, hfc.symm⟩
      rintro rfl
      apply hf
      rw [hfc, map_zero, zero_mul]
    · rintro ⟨c, hc, rfl⟩
      have hc0 : c ≠ 0 := (Finset.mem_erase.mp hc).1
      have hne : algebraMap Fq F c ≠ 0 := (_root_.map_ne_zero _).mpr hc0
      refine ⟨⟨?_, mul_ne_zero hne hf0⟩, ?_⟩
      · rw [← Algebra.smul_def]
        exact (LF Fq F E0).smul_mem c hf0L
      · rw [Places.div_mul hne hf0, div_algebraMap Fq hc0, zero_add, hE']
  rw [hfib, Finset.card_image_of_injective _
      (fun a b h => (algebraMap Fq F).injective (mul_right_cancel₀ hf0 h)),
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]

/-- `A_n (q - 1) = h_n (q ^ (n + 1 - g) - 1)` for `n ≥ 2g - 1`. -/
theorem numEff_mul (hk : constField Fq F = ⊥) {n : ℕ} (hn : 2 * (genusF Fq F : ℤ) - 1 ≤ n) :
    numEff Fq F n * (Fintype.card Fq - 1) =
      hcl Fq F n * (Fintype.card Fq ^ (n + 1 - genusF Fq F) - 1) := by
  rw [numEff, hcl, Finset.card_eq_sum_card_fiberwise (f := cls Fq F)
      (t := (effDivs Fq F n).image (cls Fq F)) (fun E hE => Finset.mem_image_of_mem _ hE),
    Finset.sum_mul, Finset.card_eq_sum_ones ((effDivs Fq F n).image (cls Fq F)), Finset.sum_mul]
  refine Finset.sum_congr rfl fun c hc => ?_
  obtain ⟨E0, hE0, rfl⟩ := Finset.mem_image.mp hc
  rw [one_mul, card_fiber_mul hk hE0, ellF_of_mem hk hn hE0]

/-- Translation by a divisor of degree `n' - n` maps the classes of degree `n'` into those of degree `n`. -/
theorem hcl_le (hk : constField Fq F = ⊥) {n n' : ℕ} (hn : 2 * (genusF Fq F : ℤ) - 1 ≤ n)
    (B : Divisor Fq F) (hB : Divisor.deg B = (n' : ℤ) - n) : hcl Fq F n' ≤ hcl Fq F n := by
  unfold hcl
  refine (Finset.card_le_card (t := ((effDivs Fq F n).image (cls Fq F)).image (· + cls Fq F B))
    fun c hc => ?_).trans Finset.card_image_le
  obtain ⟨E', hE', rfl⟩ := Finset.mem_image.mp hc
  have hdeg : Divisor.deg (E' - B) = n := by
    rw [Divisor.deg_sub, hB, (mem_effDivs.mp hE').2]
    ring
  obtain ⟨E, hE, hEc⟩ := exists_eff_of_deg hk hn (E' - B) hdeg
  refine Finset.mem_image.mpr ⟨cls Fq F E, Finset.mem_image_of_mem _ hE, ?_⟩
  rw [hEc]
  simp only [cls, QuotientAddGroup.mk_sub, sub_add_cancel]

end Classes

section Formula

variable {Fq : Type*} [Field Fq] [Fintype Fq] [DecidableEq (RatFunc Fq)]
variable {F : Type*} [Field F] [Algebra Fq F] [Algebra Fq[X] F] [Algebra (RatFunc Fq) F]
  [IsScalarTower Fq[X] (RatFunc Fq) F] [IsScalarTower Fq Fq[X] F] [FunctionField Fq F]
  [Algebra.IsSeparable (RatFunc Fq) F]

/-- **Counting formula**: there is `h` with `(q - 1) A_n = h (q ^ (n + 1 - g) - 1)` for all `n ≥ 2g - 1`
with `δ ∣ n`. -/
theorem numEff_formula (hk : constField Fq F = ⊥) :
    ∃ h : ℕ, ∀ n : ℕ, delta Fq F ∣ n → 2 * (genusF Fq F : ℤ) - 1 ≤ n →
      ((Fintype.card Fq : ℤ) - 1) * numEff Fq F n =
        h * ((Fintype.card Fq : ℤ) ^ (n + 1 - genusF Fq F) - 1) := by
  classical
  obtain ⟨-, D0, hD0⟩ := delta_mem Fq F
  set N0 := delta Fq F * (2 * genusF Fq F) with hN0
  have hK : 2 * (genusF Fq F : ℤ) - 1 ≤ N0 := by
    have : 2 * genusF Fq F ≤ N0 := Nat.le_mul_of_pos_left _ (delta_pos Fq F)
    omega
  refine ⟨hcl Fq F N0, fun n hdvd hn => ?_⟩
  obtain ⟨c, rfl⟩ := hdvd
  have hdeg : ∀ a b : ℕ, Divisor.deg (((a : ℤ) - b) • D0) =
      ((delta Fq F * a : ℕ) : ℤ) - ((delta Fq F * b : ℕ) : ℤ) := by
    intro a b
    rw [deg_zsmul, hD0]
    push_cast
    ring
  have heq : hcl Fq F (delta Fq F * c) = hcl Fq F N0 :=
    le_antisymm (hcl_le hk hK _ (hdeg c (2 * genusF Fq F))) (hcl_le hk hn _ (hdeg (2 * genusF Fq F) c))
  have h := numEff_mul hk hn
  rw [heq] at h
  have hq : 1 ≤ Fintype.card Fq := Fintype.card_pos
  have hq2 : 1 ≤ Fintype.card Fq ^ (delta Fq F * c + 1 - genusF Fq F) := Nat.one_le_pow _ _ Fintype.card_pos
  zify [hq, hq2] at h
  linear_combination h

/-- The linear recurrence `A_{n+2δ} + q^δ A_n = (1 + q^δ) A_{n+δ}` for `δ ∣ n`, `n ≥ 2g - 1`. -/
theorem numEff_rec (hk : constField Fq F = ⊥) {n : ℕ} (hdvd : delta Fq F ∣ n)
    (hn : 2 * (genusF Fq F : ℤ) - 1 ≤ n) :
    (numEff Fq F (n + 2 * delta Fq F) : ℤ) + (Fintype.card Fq : ℤ) ^ delta Fq F * numEff Fq F n =
      (1 + (Fintype.card Fq : ℤ) ^ delta Fq F) * numEff Fq F (n + delta Fq F) := by
  obtain ⟨h, hh⟩ := numEff_formula hk
  have h0 := hh n hdvd hn
  have h1 := hh (n + delta Fq F) (dvd_add hdvd dvd_rfl) (by push_cast; omega)
  have h2 := hh (n + 2 * delta Fq F) (dvd_add hdvd (dvd_mul_left _ _)) (by push_cast; omega)
  rw [show n + delta Fq F + 1 - genusF Fq F = (n + 1 - genusF Fq F) + delta Fq F by omega, pow_add] at h1
  rw [show n + 2 * delta Fq F + 1 - genusF Fq F = (n + 1 - genusF Fq F) + delta Fq F + delta Fq F by omega,
    pow_add, pow_add] at h2
  have hq : (Fintype.card Fq : ℤ) - 1 ≠ 0 := by
    have := Fintype.one_lt_card (α := Fq)
    omega
  apply mul_left_cancel₀ hq
  linear_combination h2 + (Fintype.card Fq : ℤ) ^ delta Fq F * h0 -
    (1 + (Fintype.card Fq : ℤ) ^ delta Fq F) * h1

end Formula

end RamanujanPetersson.ZetaSB


