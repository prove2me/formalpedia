-- Prove2me | Definitions.Def_RPLib_S3_PCC
-- name    : RPLib_S3_PCC
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T16:22:56.059644+00:00
-- url     : https://prove2.me/theorems/ad05d862-1a47-422e-9790-0ef147a7233e
-- title:
--   Weight-two Ramanujan-Petersson library: lines, Hermite representatives and normalisation
-- statement:
--   Lines, Hermite representatives and normalisation.
--
--   `gL p ℓ` (`ℓ : Option (ZMod p)`, the `p + 1` lines of `F_p²`) are the Hermite representatives of determinant `p`:
--   every `β` with `det β = p` is `gL p ℓ * k` for a unique `ℓ` and some `k ∈ SL₂(ℤ)` (`exists_fits`, `fits_unique`,
--   `exists_SL_of_fits`). `bL M p ℓ = gL p ℓ * w` is normalised at level `M` (`NormB`), and
--   `DvdMat p (phiM γ (bL M p ℓ)) ↔ qv p γ ℓ = 0` (`dvdMat_phiM_bL_iff`).
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture in weight two (Eichler-Shimura-Ihara route: the Eichler-Selberg trace formula on $S_2(\Gamma_1(M))$, the Deuring-Waterhouse-Schoof count of elliptic curves over $\mathbb F_q$ with level structure by Hurwitz class numbers, conditional on Tate's isogeny theorem in prime-to-$p$ form, the Kronecker-Hurwitz class number relation, and the Hasse-Weil bound for the components of $Y_1(M)$ by the Stepanov-Bombieri method). It contains definitions together with proved lemmas (no `sorry`; where Tate's theorem is used it is an explicit hypothesis), so that later solution files can import them.
-- source:
--   M. Deuring, Die Typen der Multiplikatorenringe elliptischer Funktionenkörper, Abh. Math. Sem. Univ. Hamburg 14 (1941), 197-272; W. C. Waterhouse, Abelian varieties over finite fields, Ann. Sci. École Norm. Sup. (4) 2 (1969), 521-560; R. Schoof, Nonsingular plane cubic curves over finite fields, J. Combin. Theory Ser. A 46 (1987), 183-211; J. H. Silverman, The Arithmetic of Elliptic Curves, 2nd ed., GTM 106, Springer 2009, Chapters III and V; Y. Ihara, Hecke polynomials as congruence zeta functions in elliptic modular case, Ann. of Math. 85 (1967), 267-295; M. Eichler, Quaternäre quadratische Formen und die Riemannsche Vermutung für die Kongruenzzetafunktion, Arch. Math. 5 (1954), 355-366; G. Shimura, Introduction to the Arithmetic Theory of Automorphic Functions, Princeton 1971, Chapter 7

import Mathlib
import Definitions.Def_RPLib_S3_PCB

/-!
# S3-DWS-Supersingular, part C (C): lines, Hermite representatives and normalisation

`gL p ℓ` (`ℓ : Option (ZMod p)`, the `p + 1` lines of `F_p²`) are the Hermite representatives of determinant `p`:
every `β` with `det β = p` is `gL p ℓ * k` for a unique `ℓ` and some `k ∈ SL₂(ℤ)` (`exists_fits`, `fits_unique`,
`exists_SL_of_fits`). `bL M p ℓ = gL p ℓ * w` is normalised at level `M` (`NormB`), and
`DvdMat p (phiM γ (bL M p ℓ)) ↔ qv p γ ℓ = 0` (`dvdMat_phiM_bL_iff`).
-/

set_option autoImplicit false

open Matrix MatrixGroups CongruenceSubgroup RamanujanPetersson.S3.Conj

namespace RamanujanPetersson.S3.DWSS

theorem dvdMat_of_iff {p a b c d : ℤ} : DvdMat p !![a, b; c, d] ↔ p ∣ a ∧ p ∣ b ∧ p ∣ c ∧ p ∣ d := by
  simp [DvdMat, Fin.forall_fin_two, and_assoc]

theorem dvdMat_iff_cast {p : ℕ} {β : Mat} : DvdMat p β ↔
    ((β 0 0 : ℤ) : ZMod p) = 0 ∧ ((β 0 1 : ℤ) : ZMod p) = 0 ∧ ((β 1 0 : ℤ) : ZMod p) = 0 ∧
      ((β 1 1 : ℤ) : ZMod p) = 0 := by
  simp only [DvdMat, Fin.forall_fin_two, ZMod.intCast_zmod_eq_zero_iff_dvd, and_assoc]

theorem not_dvdMat_of_det {p : ℕ} [Fact p.Prime] {β : Mat} (hβ : β.det = p) : ¬ DvdMat p β := by
  intro h
  obtain ⟨β₀, rfl⟩ := dvdMat_iff.1 h
  rw [Matrix.det_smul] at hβ
  simp only [Fintype.card_fin] at hβ
  have hp : (0 : ℤ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have h1 : (p : ℤ) * ((p : ℤ) * β₀.det) = p * 1 := by linear_combination hβ
  have h2 := mul_left_cancel₀ hp.ne' h1
  have h3 : (p : ℤ) = 1 := Int.eq_one_of_dvd_one hp.le ⟨_, h2.symm⟩
  have h4 : p = 1 := by exact_mod_cast h3
  exact (Fact.out : p.Prime).one_lt.ne' h4

/-! ## Hermite representatives -/

/-- Hermite representatives of determinant `p`. -/
def gL (p : ℕ) : Option (ZMod p) → Mat
  | none => !![(p : ℤ), 0; 0, 1]
  | some j => !![1, 0; (j.val : ℤ), (p : ℤ)]

theorem det_gL (p : ℕ) (ℓ : Option (ZMod p)) : (gL p ℓ).det = p := by
  cases ℓ <;> simp [gL, Matrix.det_fin_two]

/-- `β ∈ gL p ℓ · M₂(ℤ)`. -/
def Fits (p : ℕ) (ℓ : Option (ZMod p)) (β : Mat) : Prop := DvdMat p (adjugate (gL p ℓ) * β)

lemma adj_gL_none_mul (p : ℕ) (β : Mat) :
    adjugate (gL p none) * β = !![β 0 0, β 0 1; p * β 1 0, p * β 1 1] := by
  ext i k; fin_cases i <;> fin_cases k <;>
    simp [gL, adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]

lemma adj_gL_some_mul (p : ℕ) (j : ZMod p) (β : Mat) :
    adjugate (gL p (some j)) * β =
      !![p * β 0 0, p * β 0 1; β 1 0 - j.val * β 0 0, β 1 1 - j.val * β 0 1] := by
  ext i k; fin_cases i <;> fin_cases k <;>
    simp [gL, adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem fits_none_iff {p : ℕ} {β : Mat} : Fits p none β ↔ (p : ℤ) ∣ β 0 0 ∧ (p : ℤ) ∣ β 0 1 := by
  rw [Fits, adj_gL_none_mul, dvdMat_of_iff]
  constructor
  · rintro ⟨h1, h2, -, -⟩; exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, h2, dvd_mul_right _ _, dvd_mul_right _ _⟩

theorem fits_some_iff {p : ℕ} [NeZero p] {j : ZMod p} {β : Mat} :
    Fits p (some j) β ↔ ((β 1 0 : ℤ) : ZMod p) = j * ((β 0 0 : ℤ) : ZMod p) ∧
      ((β 1 1 : ℤ) : ZMod p) = j * ((β 0 1 : ℤ) : ZMod p) := by
  rw [Fits, adj_gL_some_mul, dvdMat_of_iff]
  simp only [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  simp only [ZMod.natCast_self, zero_mul, ZMod.natCast_zmod_val, sub_eq_zero, true_and]

lemma field_rows {K : Type*} [Field K] {a b c d : K} (h : a * d - b * c = 0) :
    (a = 0 ∧ b = 0) ∨ ∃ j, c = j * a ∧ d = j * b := by
  by_cases ha : a = 0
  · by_cases hb : b = 0
    · exact Or.inl ⟨ha, hb⟩
    · refine Or.inr ⟨d / b, ?_, (div_mul_cancel₀ d hb).symm⟩
      rw [ha, mul_zero]
      subst ha
      have : b * c = 0 := by linear_combination -h
      exact (mul_eq_zero.1 this).resolve_left hb
  · refine Or.inr ⟨c / a, (div_mul_cancel₀ c ha).symm, ?_⟩
    rw [div_mul_eq_mul_div, eq_div_iff ha]
    linear_combination h

lemma det_cast_eq_zero {p : ℕ} {β : Mat} (hβ : β.det = p) :
    ((β 0 0 : ℤ) : ZMod p) * ((β 1 1 : ℤ) : ZMod p) - ((β 0 1 : ℤ) : ZMod p) * ((β 1 0 : ℤ) : ZMod p) = 0 := by
  have := congrArg (fun x : ℤ => (x : ZMod p)) hβ
  simp only [Matrix.det_fin_two] at this
  push_cast at this
  rw [this, ZMod.natCast_self]

/-- **Hermite, existence.** -/
theorem exists_fits {p : ℕ} [Fact p.Prime] {β : Mat} (hβ : β.det = p) : ∃ ℓ, Fits p ℓ β := by
  rcases field_rows (det_cast_eq_zero hβ) with ⟨h0, h1⟩ | ⟨j, h0, h1⟩
  · exact ⟨none, fits_none_iff.2 ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 h0,
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 h1⟩⟩
  · exact ⟨some j, fits_some_iff.2 ⟨h0, h1⟩⟩

/-- **Hermite, uniqueness.** -/
theorem fits_unique {p : ℕ} [Fact p.Prime] {β : Mat} (hβ : β.det = p) {ℓ₁ ℓ₂ : Option (ZMod p)}
    (h1 : Fits p ℓ₁ β) (h2 : Fits p ℓ₂ β) : ℓ₁ = ℓ₂ := by
  have hnd := not_dvdMat_of_det hβ
  rw [dvdMat_iff_cast] at hnd
  rcases ℓ₁ with _ | j₁ <;> rcases ℓ₂ with _ | j₂
  · rfl
  · obtain ⟨a0, b0⟩ := fits_none_iff.1 h1
    obtain ⟨c0, d0⟩ := fits_some_iff.1 h2
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd] at a0 b0
    rw [a0, mul_zero] at c0; rw [b0, mul_zero] at d0
    exact absurd ⟨a0, b0, c0, d0⟩ hnd
  · obtain ⟨a0, b0⟩ := fits_none_iff.1 h2
    obtain ⟨c0, d0⟩ := fits_some_iff.1 h1
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd] at a0 b0
    rw [a0, mul_zero] at c0; rw [b0, mul_zero] at d0
    exact absurd ⟨a0, b0, c0, d0⟩ hnd
  · obtain ⟨c1, d1⟩ := fits_some_iff.1 h1
    obtain ⟨c2, d2⟩ := fits_some_iff.1 h2
    congr 1
    by_cases ha : ((β 0 0 : ℤ) : ZMod p) = 0
    · by_cases hb : ((β 0 1 : ℤ) : ZMod p) = 0
      · rw [ha, mul_zero] at c1; rw [hb, mul_zero] at d1
        exact absurd ⟨ha, hb, c1, d1⟩ hnd
      · exact mul_right_cancel₀ hb (d1.symm.trans d2)
    · exact mul_right_cancel₀ ha (c1.symm.trans c2)

theorem exists_SL_of_fits {p : ℕ} [Fact p.Prime] {ℓ : Option (ZMod p)} {β : Mat} (hβ : β.det = p)
    (h : Fits p ℓ β) : ∃ k : SL(2, ℤ), gL p ℓ * (k : Mat) = β := by
  have hp : (0 : ℤ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  obtain ⟨k₀, hk₀⟩ := dvdMat_iff.1 h
  have hdet : k₀.det = 1 := by
    have := congrArg Matrix.det hk₀
    rw [Matrix.det_mul, Matrix.det_adjugate, Matrix.det_smul, det_gL, hβ] at this
    simp only [Fintype.card_fin] at this
    have hp2 : ((p : ℤ) ^ 2) ≠ 0 := by positivity
    exact (mul_left_cancel₀ hp2 (by rw [← this]; ring)).symm
  refine ⟨⟨k₀, hdet⟩, ?_⟩
  apply smul_right_injective Mat hp.ne'
  show (p : ℤ) • (gL p ℓ * k₀) = (p : ℤ) • β
  rw [← Matrix.mul_smul, ← hk₀, ← Matrix.mul_assoc, Matrix.mul_adjugate, det_gL, Matrix.smul_mul,
    Matrix.one_mul]

theorem fits_gL_mul (p : ℕ) (ℓ : Option (ZMod p)) (w : Mat) : Fits p ℓ (gL p ℓ * w) := by
  refine dvdMat_iff.2 ⟨w, ?_⟩
  rw [← Matrix.mul_assoc, Matrix.adjugate_mul, det_gL, Matrix.smul_mul, Matrix.one_mul]

/-! ## Normalisation at level `M` -/

lemma isExact_of_mulVec {M : ℕ} {A : Matrix (Fin 2) (Fin 2) (ZMod M)} {v w : Fin 2 → ZMod M}
    (h : A *ᵥ w = v) (hv : IsExact M v) : IsExact M w := by
  intro d hd hd0 hw
  apply hv d hd hd0
  rw [← h, ← Matrix.mulVec_smul, hw, Matrix.mulVec_zero]

lemma det_redMat (M : ℕ) (β : Mat) : (redMat M β).det = ((β.det : ℤ) : ZMod M) := by
  rw [redMat, ← RingHom.mapMatrix_apply, ← RingHom.map_det]; simp

lemma isUnit_det_redMat {M p : ℕ} (hu : IsUnit (p : ZMod M)) {β : Mat} (hβ : β.det = p) :
    IsUnit (redMat M β).det := by
  rw [det_redMat, hβ]; push_cast; exact hu

theorem exists_normB_mul {M p : ℕ} [NeZero M] (hu : IsUnit (p : ZMod M)) {β : Mat} (hβ : β.det = p) :
    ∃ w : SL(2, ℤ), NormB M (β * (w : Mat)) := by
  have hR := isUnit_det_redMat hu hβ
  have he : redMat M β *ᵥ ((redMat M β)⁻¹ *ᵥ e1 M) = e1 M := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hR, Matrix.one_mulVec]
  obtain ⟨w, hw⟩ := exists_smul_e1 (isExact_of_mulVec he (isExact_e1 M))
  refine ⟨w, ?_⟩
  rw [NormB, redMat_mul, ← Matrix.mulVec_mulVec, ← vsmul_def, hw, he]

theorem exists_normB_left {M p : ℕ} [NeZero M] (hu : IsUnit (p : ZMod M)) {β : Mat} (hβ : β.det = p) :
    ∃ u : SL(2, ℤ), NormB M ((u : Mat) * β) := by
  have hR := isUnit_det_redMat hu hβ
  have he : (redMat M β)⁻¹ *ᵥ (redMat M β *ᵥ e1 M) = e1 M := by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hR, Matrix.one_mulVec]
  obtain ⟨g, hg⟩ := exists_smul_e1 (isExact_of_mulVec he (isExact_e1 M))
  refine ⟨g⁻¹, ?_⟩
  rw [NormB, redMat_mul, ← Matrix.mulVec_mulVec, ← hg, ← vsmul_def, inv_smul_smul]

open Classical in
/-- The normalising factor of the line `ℓ`. -/
noncomputable def wL (M p : ℕ) (ℓ : Option (ZMod p)) : SL(2, ℤ) :=
  if h : ∃ w : SL(2, ℤ), NormB M (gL p ℓ * (w : Mat)) then h.choose else 1

/-- The normalised representative `gL p ℓ * wL` of the line `ℓ`. -/
noncomputable def bL (M p : ℕ) (ℓ : Option (ZMod p)) : Mat := gL p ℓ * (wL M p ℓ : Mat)

theorem normB_bL {M p : ℕ} [NeZero M] (hu : IsUnit (p : ZMod M)) (ℓ : Option (ZMod p)) :
    NormB M (bL M p ℓ) := by
  have h := exists_normB_mul (M := M) hu (det_gL p ℓ)
  rw [bL, wL, dif_pos h]
  exact h.choose_spec

theorem det_bL (M p : ℕ) (ℓ : Option (ZMod p)) : (bL M p ℓ).det = p := by
  rw [bL, Matrix.det_mul, det_gL, Matrix.SpecialLinearGroup.det_coe, mul_one]

theorem fits_bL (M p : ℕ) (ℓ : Option (ZMod p)) : Fits p ℓ (bL M p ℓ) := fits_gL_mul p ℓ _

/-! ## Stable lines -/

/-- `qv p γ ℓ = 0` iff the line `ℓ` is `γ`-stable mod `p`. -/
def qv (p : ℕ) (γ : Mat) : Option (ZMod p) → ZMod p
  | none => ((γ 0 1 : ℤ) : ZMod p)
  | some j => ((γ 1 0 : ℤ) : ZMod p) + (((γ 1 1 : ℤ) : ZMod p) - ((γ 0 0 : ℤ) : ZMod p)) * j -
      ((γ 0 1 : ℤ) : ZMod p) * j ^ 2

lemma phiM_gL_none (p : ℕ) (γ : Mat) :
    phiM γ (gL p none) = !![p * γ 0 0, γ 0 1; p ^ 2 * γ 1 0, p * γ 1 1] := by
  ext i k; fin_cases i <;> fin_cases k <;>
    simp [phiM, gL, adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct] <;> ring

lemma phiM_gL_some (p : ℕ) (j : ZMod p) (γ : Mat) :
    phiM γ (gL p (some j)) = !![p * (γ 0 0 + γ 0 1 * j.val), p ^ 2 * γ 0 1;
      γ 1 0 + (γ 1 1 - γ 0 0) * j.val - γ 0 1 * (j.val : ℤ) ^ 2, p * (γ 1 1 - γ 0 1 * j.val)] := by
  ext i k; fin_cases i <;> fin_cases k <;>
    simp [phiM, gL, adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct] <;> ring

theorem dvdMat_phiM_gL_iff {p : ℕ} [NeZero p] (γ : Mat) (ℓ : Option (ZMod p)) :
    DvdMat p (phiM γ (gL p ℓ)) ↔ qv p γ ℓ = 0 := by
  rcases ℓ with _ | j
  · rw [phiM_gL_none, dvdMat_of_iff, qv, ZMod.intCast_zmod_eq_zero_iff_dvd]
    constructor
    · rintro ⟨-, h, -, -⟩; exact h
    · intro h
      exact ⟨dvd_mul_right _ _, h, Dvd.dvd.mul_right (dvd_pow_self _ two_ne_zero) _, dvd_mul_right _ _⟩
  · rw [phiM_gL_some, dvdMat_of_iff, qv]
    constructor
    · rintro ⟨-, -, h, -⟩
      have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 h
      push_cast at this
      rwa [ZMod.natCast_zmod_val] at this
    · intro h
      refine ⟨dvd_mul_right _ _, Dvd.dvd.mul_right (dvd_pow_self _ two_ne_zero) _, ?_, dvd_mul_right _ _⟩
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      rwa [ZMod.natCast_zmod_val]

theorem dvdMat_phiM_bL_iff {M p : ℕ} [NeZero p] (γ : Mat) (ℓ : Option (ZMod p)) :
    DvdMat p (phiM γ (bL M p ℓ)) ↔ qv p γ ℓ = 0 := by
  rw [bL, phiM_mul_right, dvdMat_conj_iff, dvdMat_phiM_gL_iff]

end RamanujanPetersson.S3.DWSS


