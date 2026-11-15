-- Prove2me | Definitions.Def_RPLib_S3_PCA
-- name    : RPLib_S3_PCA
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T16:19:45.547048+00:00
-- url     : https://prove2.me/theorems/f8ee8782-8dc0-4511-9d38-13fcbc5692a0
-- title:
--   Weight-two Ramanujan-Petersson library: free classes and the imprimitive classes
-- statement:
--   Free classes and the imprimitive classes.
--
--   For `M ≥ 4`, `Γ₁(M)` acts freely by conjugation on `EllPos M δ' t n` (`free_conj`), so
--   `ellCount M δ' t n` is the number of classes (`ellCount_eq_card`). The classes of matrices divisible by `p`
--   in `EllPos M (δ'' p) (p t') (p² n')` correspond to the classes of `EllPos M δ'' t' n'` (`card_imp`).
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture in weight two (Eichler-Shimura-Ihara route: the Eichler-Selberg trace formula on $S_2(\Gamma_1(M))$, the Deuring-Waterhouse-Schoof count of elliptic curves over $\mathbb F_q$ with level structure by Hurwitz class numbers, conditional on Tate's isogeny theorem in prime-to-$p$ form, the Kronecker-Hurwitz class number relation, and the Hasse-Weil bound for the components of $Y_1(M)$ by the Stepanov-Bombieri method). It contains definitions together with proved lemmas (no `sorry`; where Tate's theorem is used it is an explicit hypothesis), so that later solution files can import them.
-- source:
--   M. Deuring, Die Typen der Multiplikatorenringe elliptischer Funktionenkörper, Abh. Math. Sem. Univ. Hamburg 14 (1941), 197-272; W. C. Waterhouse, Abelian varieties over finite fields, Ann. Sci. École Norm. Sup. (4) 2 (1969), 521-560; R. Schoof, Nonsingular plane cubic curves over finite fields, J. Combin. Theory Ser. A 46 (1987), 183-211; J. H. Silverman, The Arithmetic of Elliptic Curves, 2nd ed., GTM 106, Springer 2009, Chapters III and V; Y. Ihara, Hecke polynomials as congruence zeta functions in elliptic modular case, Ann. of Math. 85 (1967), 267-295; M. Eichler, Quaternäre quadratische Formen und die Riemannsche Vermutung für die Kongruenzzetafunktion, Arch. Math. 5 (1954), 355-366; G. Shimura, Introduction to the Arithmetic Theory of Automorphic Functions, Princeton 1971, Chapter 7

import Mathlib
import Definitions.Def_RPLib_S3_ConjClassesC
import Definitions.Def_RPLib_S3_ConjClassesD

/-!
# S3-DWS-Supersingular, part C (A): free classes and the imprimitive classes

For `M ≥ 4`, `Γ₁(M)` acts freely by conjugation on `EllPos M δ' t n` (`free_conj`), so
`ellCount M δ' t n` is the number of classes (`ellCount_eq_card`). The classes of matrices divisible by `p`
in `EllPos M (δ'' p) (p t') (p² n')` correspond to the classes of `EllPos M δ'' t' n'` (`card_imp`).
-/

set_option autoImplicit false

open Matrix MatrixGroups CongruenceSubgroup RamanujanPetersson.S3.Conj

namespace RamanujanPetersson.S3.DWSS

/-- The `Γ₁(M)`-classes of `EllPos M δ' t n`. -/
abbrev QE (M : ℕ) (δ' : ZMod M) (t : ℤ) (n : ℕ) :=
  MulAction.orbitRel.Quotient (Gamma1 M) (EllPos M δ' t n)

lemma int_dvd_sub_one {M : ℕ} {x : ℤ} (h : (x : ZMod M) = 1) : (M : ℤ) ∣ x - 1 := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast; rw [h, sub_self]

lemma eq_zero_of_dvd_of_abs_lt {M : ℕ} (hM : 4 ≤ M) {x : ℤ} (h : (M : ℤ) ∣ x) (h1 : -4 < x) (h2 : x < 4) :
    x = 0 := by
  obtain ⟨k, rfl⟩ := h
  have hM' : (4 : ℤ) ≤ M := by exact_mod_cast hM
  rcases lt_trichotomy k 0 with hk | hk | hk
  · nlinarith
  · simp [hk]
  · nlinarith

/-- **Freeness.** For `M ≥ 4`, an element of `Γ₁(M)` fixing an elliptic `γ ∈ EllPos` by conjugation is `1`. -/
theorem free_conj {M : ℕ} (hM : 4 ≤ M) {δ' : ZMod M} {t : ℤ} {n : ℕ} {γ : Mat}
    (hγ : γ ∈ EllPos M δ' t n) {h : SL(2, ℤ)} (hh : h ∈ Gamma1 M) (hc : conj h γ = γ) : h = 1 := by
  have : NeZero M := ⟨by omega⟩
  obtain ⟨hdet, htr, hc0, hdisc, -, -⟩ := mem_EllPos_iff'.1 hγ
  rw [conj_eq_iff_commute] at hc
  have e00 := congrFun (congrFun hc 0) 0
  have e10 := congrFun (congrFun hc 1) 0
  simp only [Matrix.mul_apply, Fin.sum_univ_two] at e00 e10
  have hdh : (h : Mat) 0 0 * (h : Mat) 1 1 - (h : Mat) 0 1 * (h : Mat) 1 0 = 1 := by
    rw [← Matrix.det_fin_two]; exact Matrix.SpecialLinearGroup.det_coe h
  rw [Matrix.det_fin_two] at hdet
  rw [Matrix.trace_fin_two] at htr
  obtain ⟨g00, g11, g10⟩ := (Gamma1_mem M h).1 hh
  have hx := int_dvd_sub_one g00
  have hw := int_dvd_sub_one g11
  have hz : (M : ℤ) ∣ (h : Mat) 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 g10
  set x := (h : Mat) 0 0
  set y := (h : Mat) 0 1
  set z := (h : Mat) 1 0
  set w := (h : Mat) 1 1
  set a := γ 0 0
  set b := γ 0 1
  set c := γ 1 0
  set d := γ 1 1
  have key : c ^ 2 * ((x + w) ^ 2 - 4) = z ^ 2 * (t ^ 2 - 4 * n) := by
    rw [← htr, ← hdet]
    linear_combination (-(c * (x - w) + z * (a - d))) * e10 + 4 * c * z * e00 + 4 * c ^ 2 * hdh
  have hD : t ^ 2 - 4 * (n : ℤ) < 0 := by linarith
  have hz0 : z = 0 := by
    by_contra hz0
    have hz2 : 0 < z ^ 2 := by positivity
    have hlt : (x + w) ^ 2 < 4 := by
      have : c ^ 2 * ((x + w) ^ 2 - 4) < 0 := by rw [key]; exact mul_neg_of_pos_of_neg hz2 hD
      have hc2 : 0 < c ^ 2 := by positivity
      nlinarith
    have hs : (M : ℤ) ∣ x + w - 2 := by
      have := dvd_add hx hw; rwa [show x - 1 + (w - 1) = x + w - 2 by ring] at this
    have h1 : x + w ≤ 1 := by nlinarith
    have h2 : -1 ≤ x + w := by nlinarith
    have := eq_zero_of_dvd_of_abs_lt hM hs (by linarith) (by linarith)
    linarith
  rw [hz0] at e00 e10 hdh
  have hxw : x = w := by
    have : c * (x - w) = 0 := by linear_combination -e10
    rcases mul_eq_zero.1 this with h0 | h0
    · linarith
    · linarith
  have hy : y = 0 := by
    have : y * c = 0 := by linear_combination e00
    rcases mul_eq_zero.1 this with h0 | h0
    · exact h0
    · linarith
  rw [← hxw] at hdh
  have hx1 : x = 1 := by
    have hxx : x * x = 1 := by linarith
    rcases Int.eq_one_or_neg_one_of_mul_eq_one hxx with h0 | h0
    · exact h0
    · exfalso
      rw [h0] at hx
      have := eq_zero_of_dvd_of_abs_lt hM hx (by norm_num) (by norm_num)
      norm_num at this
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j
  · simp [Matrix.SpecialLinearGroup.coe_one]; exact hx1
  · simp [Matrix.SpecialLinearGroup.coe_one]; exact hy
  · simp [Matrix.SpecialLinearGroup.coe_one]; exact hz0
  · simp [Matrix.SpecialLinearGroup.coe_one]; exact hxw.symm.trans hx1

/-- For `M ≥ 4`, `ellCount` is the number of `Γ₁(M)`-classes in `EllPos`. -/
theorem ellCount_eq_card {M : ℕ} [NeZero M] (hM : 4 ≤ M) (δ' : ZMod M) (t : ℤ) (n : ℕ) :
    ellCount M δ' t n = Nat.card (QE M δ' t n) := by
  rw [← classSum_EllPos, classSum]
  have hstab : ∀ C : QE M δ' t n, Nat.card (MulAction.stabilizer (Gamma1 M) C.out) = 1 := by
    intro C
    rw [Nat.card_eq_one_iff_exists]
    refine ⟨1, fun g => ?_⟩
    have hg : (g : Gamma1 M) • C.out = C.out := g.2
    have h1 : ((g : Gamma1 M) : SL(2, ℤ)) = 1 :=
      free_conj hM C.out.2 (g : Gamma1 M).2 (by rw [← ellPos_smul_val, hg])
    exact Subtype.ext (Subtype.ext h1)
  simp only [hstab, Nat.cast_one, div_one]
  have := finite_EllPos_quot (M := M) δ' t n
  have := Fintype.ofFinite (QE M δ' t n)
  rw [finsum_eq_sum_of_fintype, Finset.sum_const, Finset.card_univ, Nat.card_eq_fintype_card, nsmul_eq_mul,
    mul_one]

lemma finite_QE (M : ℕ) [NeZero M] (δ' : ZMod M) (t : ℤ) (n : ℕ) : Finite (QE M δ' t n) :=
  finite_EllPos_quot δ' t n

/-! ## Divisibility of matrices -/

theorem dvdMat_iff {p : ℤ} {γ : Mat} : DvdMat p γ ↔ ∃ γ₀ : Mat, γ = p • γ₀ := by
  constructor
  · intro h
    refine ⟨Matrix.of fun i j => γ i j / p, ?_⟩
    ext i j; simp [Int.mul_ediv_cancel' (h i j)]
  · rintro ⟨γ₀, rfl⟩ i j; simp

theorem conj_smul (g : SL(2, ℤ)) (p : ℤ) (γ : Mat) : conj g (p • γ) = p • conj g γ := by
  simp only [conj, Matrix.mul_smul, Matrix.smul_mul]

theorem dvdMat_conj {p : ℤ} {γ : Mat} (h : DvdMat p γ) (g : SL(2, ℤ)) : DvdMat p (conj g γ) := by
  obtain ⟨γ₀, rfl⟩ := dvdMat_iff.1 h
  exact dvdMat_iff.2 ⟨conj g γ₀, conj_smul g p γ₀⟩

theorem dvdMat_conj_iff {p : ℤ} {γ : Mat} (g : SL(2, ℤ)) : DvdMat p (conj g γ) ↔ DvdMat p γ :=
  ⟨fun h => by simpa [conj_inv_conj] using dvdMat_conj h g⁻¹, fun h => dvdMat_conj h g⟩

theorem card_split {α : Type*} [Finite α] (P : α → Prop) :
    Nat.card α = Nat.card {a // P a} + Nat.card {a // ¬ P a} := by
  classical
  rw [← Nat.card_sum, Nat.card_congr (Equiv.sumCompl P)]

/-- A class predicate defined through `out` can be read on any representative. -/
theorem dvdMat_out_iff {M : ℕ} {δ' : ZMod M} {t : ℤ} {n : ℕ} (p : ℤ) (x : EllPos M δ' t n) :
    DvdMat p ((Quotient.out (Quotient.mk (MulAction.orbitRel (Gamma1 M) (EllPos M δ' t n)) x) :
      EllPos M δ' t n) : Mat) ↔ DvdMat p (x : Mat) := by
  obtain ⟨h, hh⟩ := (mk_eq_mk_iff (G := Gamma1 M) _ x).1 (Quotient.out_eq (Quotient.mk _ x))
  rw [← hh, ellPos_smul_val, dvdMat_conj_iff]

/-! ## The imprimitive classes -/

section Imp

variable {M : ℕ} {p : ℕ} {δ'' : ZMod M} {t' : ℤ} {n' : ℕ}

theorem smul_mem (hp : 0 < p) {γ : Mat} (hγ : γ ∈ EllPos M δ'' t' n') :
    (p : ℤ) • γ ∈ EllPos M (δ'' * p) (p * t') (p ^ 2 * n') := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := mem_EllPos_iff'.1 hγ
  have hp' : (0 : ℤ) < p := by exact_mod_cast hp
  refine mem_EllPos_iff'.2 ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Matrix.det_smul, h1]; simp
  · rw [Matrix.trace_smul, h2, smul_eq_mul]
  · simp only [Matrix.smul_apply, smul_eq_mul]; positivity
  · push_cast; nlinarith
  · simp only [Matrix.smul_apply, smul_eq_mul]; push_cast; rw [h5, mul_comm]
  · simp only [Matrix.smul_apply, smul_eq_mul]; push_cast; rw [h6, mul_zero]

theorem unsmul_mem (hp : 0 < p) (hu : IsUnit (p : ZMod M)) {γ : Mat}
    (hγ : (p : ℤ) • γ ∈ EllPos M (δ'' * p) (p * t') (p ^ 2 * n')) : γ ∈ EllPos M δ'' t' n' := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := mem_EllPos_iff'.1 hγ
  have hp' : (0 : ℤ) < p := by exact_mod_cast hp
  rw [Matrix.det_smul] at h1
  rw [Matrix.trace_smul, smul_eq_mul] at h2
  simp only [Matrix.smul_apply, smul_eq_mul] at h3 h5 h6
  push_cast at h1 h4 h5 h6
  refine mem_EllPos_iff'.2 ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Fintype.card_fin] at h1
    exact mul_left_cancel₀ (by positivity) h1
  · exact mul_left_cancel₀ hp'.ne' h2
  · exact pos_of_mul_pos_right h3 hp'.le
  · nlinarith
  · exact hu.mul_left_cancel (by rw [h5, mul_comm])
  · exact hu.mul_left_cancel (by rw [h6, mul_zero])

variable [NeZero M]

/-- `[γ'] ↦ [p γ']` from the classes of `EllPos M δ'' t' n'` to the `p`-divisible classes. -/
noncomputable def impMap (hp : 0 < p) (c : QE M δ'' t' n') :
    {C : QE M (δ'' * p) (p * t') (p ^ 2 * n') // DvdMat p (C.out : Mat)} :=
  ⟨Quotient.mk _ ⟨(p : ℤ) • (c.out : Mat), smul_mem hp c.out.2⟩, by
    rw [dvdMat_out_iff]; exact dvdMat_iff.2 ⟨_, rfl⟩⟩

theorem impMap_bijective (hp : 0 < p) (hu : IsUnit (p : ZMod M)) :
    Function.Bijective (impMap (M := M) (δ'' := δ'') (t' := t') (n' := n') hp) := by
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne'
  constructor
  · intro c₁ c₂ h
    have h' := congrArg Subtype.val h
    simp only [impMap] at h'
    obtain ⟨g, hg⟩ := (mk_eq_mk_iff _ _).1 h'
    have hv := congrArg Subtype.val hg
    rw [ellPos_smul_val] at hv
    simp only at hv
    rw [conj_smul] at hv
    have hv' := smul_right_injective Mat hp0 hv
    rw [← Quotient.out_eq c₁, ← Quotient.out_eq c₂]
    exact (mk_eq_mk_iff _ _).2 ⟨g, Subtype.ext (by rw [ellPos_smul_val]; exact hv')⟩
  · rintro ⟨C, hC⟩
    obtain ⟨γ₀, hγ₀⟩ := dvdMat_iff.1 hC
    have hmem : γ₀ ∈ EllPos M δ'' t' n' := unsmul_mem hp hu (hγ₀ ▸ C.out.2)
    refine ⟨Quotient.mk _ ⟨γ₀, hmem⟩, Subtype.ext ?_⟩
    obtain ⟨g, hg⟩ := (mk_eq_mk_iff _ _).1 (Quotient.out_eq (Quotient.mk (MulAction.orbitRel (Gamma1 M)
      (EllPos M δ'' t' n')) ⟨γ₀, hmem⟩))
    simp only [impMap]
    rw [← Quotient.out_eq C]
    refine (mk_eq_mk_iff _ _).2 ⟨g, Subtype.ext ?_⟩
    have hv := congrArg Subtype.val hg
    rw [ellPos_smul_val] at hv
    rw [ellPos_smul_val, hγ₀, conj_smul]
    exact congrArg (fun X => (p : ℤ) • X) hv

/-- **Imprimitive classes.** `#{p-divisible classes of EllPos(δ'' p, p t', p² n')} = #classes of EllPos(δ'', t', n')`. -/
theorem card_imp (hp : 0 < p) (hu : IsUnit (p : ZMod M)) :
    Nat.card {C : QE M (δ'' * p) (p * t') (p ^ 2 * n') // DvdMat p (C.out : Mat)} =
      Nat.card (QE M δ'' t' n') :=
  (Nat.card_eq_of_bijective _ (impMap_bijective hp hu)).symm

end Imp

end RamanujanPetersson.S3.DWSS


