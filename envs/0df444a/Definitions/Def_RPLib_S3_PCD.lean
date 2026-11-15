-- Prove2me | Definitions.Def_RPLib_S3_PCD
-- name    : RPLib_S3_PCD
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T16:25:12.031276+00:00
-- url     : https://prove2.me/theorems/a6563476-8fc8-4879-87ca-d5ad2273382e
-- title:
--   Weight-two Ramanujan-Petersson library: every primitive `γ` is a `Φ`-image
-- statement:
--   Every primitive `γ` is a `Φ`-image.
--
--   For `γ ∈ EllPos M (δ'' p) (p t') (p² n')` not divisible by `p` there are `γ' ∈ EllPos M δ'' t' n'` and `β` with
--   `det β = p`, `β e₁ ≡ e₁ (mod M)` and `adj β · γ' · β = γ` (`exists_pre`).
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture in weight two (Eichler-Shimura-Ihara route: the Eichler-Selberg trace formula on $S_2(\Gamma_1(M))$, the Deuring-Waterhouse-Schoof count of elliptic curves over $\mathbb F_q$ with level structure by Hurwitz class numbers, conditional on Tate's isogeny theorem in prime-to-$p$ form, the Kronecker-Hurwitz class number relation, and the Hasse-Weil bound for the components of $Y_1(M)$ by the Stepanov-Bombieri method). It contains definitions together with proved lemmas (no `sorry`; where Tate's theorem is used it is an explicit hypothesis), so that later solution files can import them.
-- source:
--   M. Deuring, Die Typen der Multiplikatorenringe elliptischer Funktionenkörper, Abh. Math. Sem. Univ. Hamburg 14 (1941), 197-272; W. C. Waterhouse, Abelian varieties over finite fields, Ann. Sci. École Norm. Sup. (4) 2 (1969), 521-560; R. Schoof, Nonsingular plane cubic curves over finite fields, J. Combin. Theory Ser. A 46 (1987), 183-211; J. H. Silverman, The Arithmetic of Elliptic Curves, 2nd ed., GTM 106, Springer 2009, Chapters III and V; Y. Ihara, Hecke polynomials as congruence zeta functions in elliptic modular case, Ann. of Math. 85 (1967), 267-295; M. Eichler, Quaternäre quadratische Formen und die Riemannsche Vermutung für die Kongruenzzetafunktion, Arch. Math. 5 (1954), 355-366; G. Shimura, Introduction to the Arithmetic Theory of Automorphic Functions, Princeton 1971, Chapter 7

import Mathlib
import Definitions.Def_RPLib_S3_PCC

/-!
# S3-DWS-Supersingular, part C (D): every primitive `γ` is a `Φ`-image

For `γ ∈ EllPos M (δ'' p) (p t') (p² n')` not divisible by `p` there are `γ' ∈ EllPos M δ'' t' n'` and `β` with
`det β = p`, `β e₁ ≡ e₁ (mod M)` and `adj β · γ' · β = γ` (`exists_pre`).
-/

set_option autoImplicit false

open Matrix MatrixGroups CongruenceSubgroup RamanujanPetersson.S3.Conj

namespace RamanujanPetersson.S3.DWSS

/-- A line `ℓ` with `p² ∣ Φ(γ, gL p ℓ)`, for `γ` primitive with `p ∣ tr γ`, `p² ∣ det γ`. -/
theorem exists_gL_dvd {p : ℕ} [Fact p.Prime] {γ : Mat} {t' : ℤ} {n' : ℕ}
    (hdet : γ.det = (p : ℤ) ^ 2 * n') (htr : γ.trace = p * t') (hprim : ¬ DvdMat p γ) :
    ∃ ℓ, DvdMat ((p : ℤ) ^ 2) (phiM γ (gL p ℓ)) := by
  have hpp : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 Fact.out
  rw [Matrix.det_fin_two] at hdet
  rw [Matrix.trace_fin_two] at htr
  by_cases hb : (p : ℤ) ∣ γ 0 1
  · refine ⟨none, ?_⟩
    rw [phiM_gL_none, dvdMat_of_iff]
    have hadd : ((γ 0 0 : ℤ) : ZMod p) + ((γ 1 1 : ℤ) : ZMod p) = 0 := by
      have := congrArg (fun x : ℤ => (x : ZMod p)) htr
      push_cast at this
      rw [this, ZMod.natCast_self, zero_mul]
    have hmul : ((γ 0 0 : ℤ) : ZMod p) * ((γ 1 1 : ℤ) : ZMod p) = 0 := by
      have := congrArg (fun x : ℤ => (x : ZMod p)) hdet
      push_cast at this
      rw [(ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 hb, zero_mul, sub_zero, ZMod.natCast_self] at this
      rw [this]; ring
    have ha : ((γ 0 0 : ℤ) : ZMod p) = 0 := by
      have h2 : ((γ 0 0 : ℤ) : ZMod p) ^ 2 = 0 := by
        linear_combination ((γ 0 0 : ℤ) : ZMod p) * hadd - hmul
      exact (pow_eq_zero_iff two_ne_zero).1 h2
    have hd : ((γ 1 1 : ℤ) : ZMod p) = 0 := by linear_combination hadd - ha
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at ha hd
    have hc : ¬ (p : ℤ) ∣ γ 1 0 := fun hc => hprim (by
      simp only [DvdMat, Fin.forall_fin_two]; exact ⟨⟨ha, hb⟩, hc, hd⟩)
    have hb2 : (p : ℤ) ^ 2 ∣ γ 0 1 := by
      have hcop : IsCoprime ((p : ℤ) ^ 2) (γ 1 0) := ((Prime.coprime_iff_not_dvd hpp).2 hc).pow_left
      apply hcop.dvd_of_dvd_mul_right
      have h1 : (p : ℤ) ^ 2 ∣ γ 0 0 * γ 1 1 := by rw [sq]; exact mul_dvd_mul ha hd
      have h2 : γ 0 1 * γ 1 0 = γ 0 0 * γ 1 1 - p ^ 2 * n' := by linear_combination -hdet
      rw [h2]; exact dvd_sub h1 (dvd_mul_right _ _)
    refine ⟨?_, hb2, ?_, ?_⟩
    · rw [sq]; exact mul_dvd_mul_left _ ha
    · exact dvd_mul_right _ _
    · rw [sq]; exact mul_dvd_mul_left _ hd
  · have hb' : ((γ 0 1 : ℤ) : ZMod p) ≠ 0 := by rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    have hbj : ((γ 0 1 : ℤ) : ZMod p) * (((γ 1 1 : ℤ) : ZMod p) / ((γ 0 1 : ℤ) : ZMod p)) =
        ((γ 1 1 : ℤ) : ZMod p) := mul_div_cancel₀ _ hb'
    refine ⟨some (((γ 1 1 : ℤ) : ZMod p) / ((γ 0 1 : ℤ) : ZMod p)), ?_⟩
    rw [phiM_gL_some, dvdMat_of_iff]
    set j : ZMod p := ((γ 1 1 : ℤ) : ZMod p) / ((γ 0 1 : ℤ) : ZMod p) with hj
    set J : ℤ := ((j.val : ℕ) : ℤ) with hJ
    have hJc : ((J : ℤ) : ZMod p) = j := by rw [hJ]; push_cast; exact ZMod.natCast_zmod_val j
    have hsd : (p : ℤ) ∣ γ 0 1 * J - γ 1 1 := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast; rw [hJc, hbj, sub_self]
    obtain ⟨s, hs⟩ := hsd
    have hcop : IsCoprime ((p : ℤ) ^ 2) (γ 0 1) := ((Prime.coprime_iff_not_dvd hpp).2 hb).pow_left
    refine ⟨?_, dvd_mul_right _ _, ?_, ?_⟩
    · rw [sq]; apply mul_dvd_mul_left
      exact ⟨t' + s, by linear_combination htr + hs⟩
    · apply hcop.dvd_of_dvd_mul_right
      exact ⟨-(n' + s * t' + s ^ 2), by
        linear_combination -hdet - p * s * htr + (-γ 0 0 - p * s - γ 0 1 * J) * hs⟩
    · rw [sq]; apply mul_dvd_mul_left
      exact ⟨-s, by linear_combination -hs⟩

lemma adjugate_adjugate_two (β : Mat) : adjugate (adjugate β) = β := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [adjugate_fin_two]

/-- Inverting `Φ`: `Φ(γ, β) = c² γ'` with `det β = c` gives `Φ(γ', adj β) = γ`. -/
lemma phiM_adj_of_eq {γ γ' β : Mat} {c : ℤ} (hβ : β.det = c) (hc : c ≠ 0) (h : phiM γ β = c ^ 2 • γ') :
    phiM γ' (adjugate β) = γ := by
  apply smul_right_injective Mat (pow_ne_zero 2 hc)
  show c ^ 2 • phiM γ' (adjugate β) = c ^ 2 • γ
  rw [phiM, adjugate_adjugate_two, ← Matrix.smul_mul, ← Matrix.mul_smul, ← h, mul_phiM_mul, hβ]

lemma pos_10_of_phiM {γ' β : Mat} (hD : γ'.trace ^ 2 < 4 * γ'.det) (hpos : 0 < phiM γ' β 1 0) :
    0 < γ' 1 0 := by
  rw [phiM_10] at hpos
  rw [Matrix.trace_fin_two, Matrix.det_fin_two] at hD
  set a := γ' 0 0
  set b := γ' 0 1
  set c := γ' 1 0
  set d := γ' 1 1
  set x := β 0 0
  set y := β 1 0
  have hk : 0 < -(d - a) ^ 2 - 4 * b * c := by
    have : -(d - a) ^ 2 - 4 * b * c = 4 * (a * d - b * c) - (a + d) ^ 2 := by ring
    rw [this]; linarith
  have key : 4 * c * (c * x ^ 2 + (d - a) * x * y - b * y ^ 2) =
      (2 * c * x + (d - a) * y) ^ 2 + (-(d - a) ^ 2 - 4 * b * c) * y ^ 2 := by ring
  have h1 : 0 ≤ (2 * c * x + (d - a) * y) ^ 2 + (-(d - a) ^ 2 - 4 * b * c) * y ^ 2 :=
    add_nonneg (sq_nonneg _) (mul_nonneg hk.le (sq_nonneg _))
  by_contra hc
  rcases (not_lt.1 hc).lt_or_eq with hc | hc
  · have : 4 * c * (c * x ^ 2 + (d - a) * x * y - b * y ^ 2) < 0 := by
      have : 4 * c < 0 := by linarith
      exact mul_neg_of_neg_of_pos this hpos
    linarith
  · rw [hc] at hk; nlinarith [sq_nonneg (d - a)]

theorem mem_of_phiM {M p : ℕ} {δ'' : ZMod M} {t' : ℤ} {n' : ℕ} (hp : 0 < p) (hu : IsUnit (p : ZMod M))
    {γ' β : Mat} (hγ : phiM γ' β ∈ EllPos M (δ'' * p) (p * t') (p ^ 2 * n')) (hβ : β.det = p)
    (hN : NormB M β) : γ' ∈ EllPos M δ'' t' n' := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := mem_EllPos_iff'.1 hγ
  obtain ⟨b0, b1⟩ := normB_iff.1 hN
  have hp' : (0 : ℤ) < p := by exact_mod_cast hp
  rw [det_phiM, hβ] at h1
  rw [trace_phiM, hβ] at h2
  have hdet : γ'.det = n' := mul_left_cancel₀ (pow_ne_zero 2 hp'.ne') (h1.trans (by push_cast; ring))
  have htr : γ'.trace = t' := mul_left_cancel₀ hp'.ne' h2
  have h4' : (p : ℤ) ^ 2 * t' ^ 2 < (p : ℤ) ^ 2 * (4 * n') :=
    calc (p : ℤ) ^ 2 * t' ^ 2 = ((p : ℤ) * t') ^ 2 := by ring
      _ < 4 * ((p ^ 2 * n' : ℕ) : ℤ) := h4
      _ = (p : ℤ) ^ 2 * (4 * n') := by push_cast; ring
  have hD : t' ^ 2 < 4 * n' := lt_of_mul_lt_mul_left h4' (by positivity)
  have hdM : ((β 1 1 : ℤ) : ZMod M) = p := by
    have := congrArg (fun x : ℤ => (x : ZMod M)) hβ
    simp only [Matrix.det_fin_two] at this; push_cast at this; rw [b0, b1] at this
    linear_combination this
  have h10 : ((γ' 1 0 : ℤ) : ZMod M) = 0 := by
    rw [phiM_10] at h6; push_cast at h6; rw [b0, b1] at h6
    linear_combination h6
  refine mem_EllPos_iff'.2 ⟨hdet, htr, pos_10_of_phiM (by rw [hdet, htr]; exact hD) h3, hD, ?_, h10⟩
  rw [phiM_00] at h5; push_cast at h5; rw [b0, b1, hdM, h10] at h5
  apply hu.mul_left_cancel
  linear_combination h5

/-- **Surjectivity construction.** -/
theorem exists_pre {M p : ℕ} [NeZero M] [Fact p.Prime] {δ'' : ZMod M} {t' : ℤ} {n' : ℕ}
    (hu : IsUnit (p : ZMod M)) {γ : Mat} (hγ : γ ∈ EllPos M (δ'' * p) (p * t') (p ^ 2 * n'))
    (hprim : ¬ DvdMat p γ) :
    ∃ γ' ∈ EllPos M δ'' t' n', ∃ β : Mat, β.det = p ∧ NormB M β ∧ phiM γ' β = γ := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hp' : (0 : ℤ) < p := by exact_mod_cast hp
  obtain ⟨h1, h2, -, -, -, -⟩ := mem_EllPos_iff'.1 hγ
  obtain ⟨ℓ, hℓ⟩ := exists_gL_dvd (t' := t') (n' := n') (by rw [h1]; push_cast; ring) h2 hprim
  obtain ⟨γ₀, hγ₀⟩ := dvdMat_iff.1 hℓ
  have hdet0 : (adjugate (gL p ℓ)).det = p := by rw [Matrix.det_adjugate, det_gL]; simp
  have hphi0 : phiM γ₀ (adjugate (gL p ℓ)) = γ := phiM_adj_of_eq (det_gL p ℓ) hp'.ne' hγ₀
  obtain ⟨u, hu'⟩ := exists_normB_left hu hdet0
  have hdet1 : ((u : Mat) * adjugate (gL p ℓ)).det = p := by
    rw [Matrix.det_mul, Matrix.SpecialLinearGroup.det_coe, one_mul, hdet0]
  have hphi : phiM (conj u γ₀) ((u : Mat) * adjugate (gL p ℓ)) = γ := by rw [phiM_conj, hphi0]
  exact ⟨conj u γ₀, mem_of_phiM hp hu (hphi ▸ hγ) hdet1 hu', _, hdet1, hu', hphi⟩

end RamanujanPetersson.S3.DWSS


