-- Prove2me | Definitions.Def_RPLib_S3_PCB
-- name    : RPLib_S3_PCB
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T16:21:26.441605+00:00
-- url     : https://prove2.me/theorems/9a18b78d-ed8d-49bb-a521-089dda12f424
-- title:
--   Weight-two Ramanujan-Petersson library: the map `Φ(γ', β) = adj β · γ' · β`
-- statement:
--   The map `Φ(γ', β) = adj β · γ' · β`.
--
--   For `β` of determinant `p` normalised at level `M` (`β e₁ ≡ e₁`), `Φ` maps `EllPos M δ'' t' n'` into
--   `EllPos M (δ'' p) (p t') (p² n')` (`phiM_mem`). It is invariant under `(γ', β) ↦ (g γ' g⁻¹, g β)`, conjugates by
--   `v⁻¹` under `β ↦ β v`, and the key lemma `key_phiM`: two pairs with the same primitive image differ by one `k ∈ SL₂(ℤ)`.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture in weight two (Eichler-Shimura-Ihara route: the Eichler-Selberg trace formula on $S_2(\Gamma_1(M))$, the Deuring-Waterhouse-Schoof count of elliptic curves over $\mathbb F_q$ with level structure by Hurwitz class numbers, conditional on Tate's isogeny theorem in prime-to-$p$ form, the Kronecker-Hurwitz class number relation, and the Hasse-Weil bound for the components of $Y_1(M)$ by the Stepanov-Bombieri method). It contains definitions together with proved lemmas (no `sorry`; where Tate's theorem is used it is an explicit hypothesis), so that later solution files can import them.
-- source:
--   M. Deuring, Die Typen der Multiplikatorenringe elliptischer Funktionenkörper, Abh. Math. Sem. Univ. Hamburg 14 (1941), 197-272; W. C. Waterhouse, Abelian varieties over finite fields, Ann. Sci. École Norm. Sup. (4) 2 (1969), 521-560; R. Schoof, Nonsingular plane cubic curves over finite fields, J. Combin. Theory Ser. A 46 (1987), 183-211; J. H. Silverman, The Arithmetic of Elliptic Curves, 2nd ed., GTM 106, Springer 2009, Chapters III and V; Y. Ihara, Hecke polynomials as congruence zeta functions in elliptic modular case, Ann. of Math. 85 (1967), 267-295; M. Eichler, Quaternäre quadratische Formen und die Riemannsche Vermutung für die Kongruenzzetafunktion, Arch. Math. 5 (1954), 355-366; G. Shimura, Introduction to the Arithmetic Theory of Automorphic Functions, Princeton 1971, Chapter 7

import Mathlib
import Definitions.Def_RPLib_S3_PCA

/-!
# S3-DWS-Supersingular, part C (B): the map `Φ(γ', β) = adj β · γ' · β`

For `β` of determinant `p` normalised at level `M` (`β e₁ ≡ e₁`), `Φ` maps `EllPos M δ'' t' n'` into
`EllPos M (δ'' p) (p t') (p² n')` (`phiM_mem`). It is invariant under `(γ', β) ↦ (g γ' g⁻¹, g β)`, conjugates by
`v⁻¹` under `β ↦ β v`, and the key lemma `key_phiM`: two pairs with the same primitive image differ by one `k ∈ SL₂(ℤ)`.
-/

set_option autoImplicit false

open Matrix MatrixGroups CongruenceSubgroup RamanujanPetersson.S3.Conj

namespace RamanujanPetersson.S3.DWSS

/-- `Φ(γ', β) = adj β · γ' · β`. -/
def phiM (γ β : Mat) : Mat := adjugate β * γ * β

/-- `β e₁ ≡ e₁ (mod M)`. -/
def NormB (M : ℕ) (β : Mat) : Prop := redMat M β *ᵥ e1 M = e1 M

lemma normB_iff {M : ℕ} {β : Mat} :
    NormB M β ↔ ((β 0 0 : ℤ) : ZMod M) = 1 ∧ ((β 1 0 : ℤ) : ZMod M) = 0 := by
  rw [NormB, redMat_mulVec_e1, funext_iff, Fin.forall_fin_two]; simp [e1]

lemma qform_pos {γ : Mat} (hc : 0 < γ 1 0) (hD : γ.trace ^ 2 < 4 * γ.det) {x y : ℤ} (hxy : x ≠ 0 ∨ y ≠ 0) :
    0 < γ 1 0 * x ^ 2 + (γ 1 1 - γ 0 0) * x * y - γ 0 1 * y ^ 2 := by
  rw [Matrix.trace_fin_two, Matrix.det_fin_two] at hD
  have hk : 0 < -((γ 1 1 - γ 0 0) ^ 2 + 4 * γ 0 1 * γ 1 0) := by nlinarith
  rcases eq_or_ne y 0 with hy | hy
  · subst hy
    have hx : x ≠ 0 := by tauto
    have : 0 < x ^ 2 := by positivity
    nlinarith
  · have hy2 : 0 < y ^ 2 := by positivity
    have h4 : 0 < 4 * γ 1 0 * (γ 1 0 * x ^ 2 + (γ 1 1 - γ 0 0) * x * y - γ 0 1 * y ^ 2) := by
      nlinarith [sq_nonneg (2 * γ 1 0 * x + (γ 1 1 - γ 0 0) * y), mul_pos hk hy2]
    nlinarith

lemma phiM_10 (γ β : Mat) : phiM γ β 1 0 =
    γ 1 0 * β 0 0 ^ 2 + (γ 1 1 - γ 0 0) * β 0 0 * β 1 0 - γ 0 1 * β 1 0 ^ 2 := by
  simp [phiM, adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]; ring

lemma phiM_00 (γ β : Mat) : phiM γ β 0 0 =
    β 1 1 * (γ 0 0 * β 0 0 + γ 0 1 * β 1 0) - β 0 1 * (γ 1 0 * β 0 0 + γ 1 1 * β 1 0) := by
  simp [phiM, adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]; ring

lemma det_phiM (γ β : Mat) : (phiM γ β).det = β.det ^ 2 * γ.det := by
  rw [phiM, Matrix.det_mul, Matrix.det_mul, Matrix.det_adjugate]; simp; ring

lemma trace_phiM (γ β : Mat) : (phiM γ β).trace = β.det * γ.trace := by
  rw [phiM, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, Matrix.mul_adjugate, Matrix.mul_smul,
    Matrix.mul_one, Matrix.trace_smul, smul_eq_mul]

theorem phiM_mem {M p : ℕ} (hp : 0 < p) {δ'' : ZMod M} {t' : ℤ} {n' : ℕ} {γ β : Mat}
    (hγ : γ ∈ EllPos M δ'' t' n') (hβ : β.det = p) (hN : NormB M β) :
    phiM γ β ∈ EllPos M (δ'' * p) (p * t') (p ^ 2 * n') := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := mem_EllPos_iff'.1 hγ
  obtain ⟨b0, b1⟩ := normB_iff.1 hN
  have hp' : (0 : ℤ) < p := by exact_mod_cast hp
  have hdM : ((β 1 1 : ℤ) : ZMod M) = p := by
    have := congrArg (fun x : ℤ => (x : ZMod M)) hβ
    simp only [Matrix.det_fin_two] at this; push_cast at this; rw [b0, b1] at this
    linear_combination this
  refine mem_EllPos_iff'.2 ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [det_phiM, hβ, h1]; push_cast; ring
  · rw [trace_phiM, hβ, h2]
  · rw [phiM_10]
    refine qform_pos h3 (by rw [h1, h2]; exact h4) ?_
    by_contra hcon
    push_neg at hcon
    rw [Matrix.det_fin_two, hcon.1, hcon.2] at hβ
    simp at hβ; omega
  · push_cast; nlinarith [mul_lt_mul_of_pos_left h4 (by positivity : (0 : ℤ) < (p : ℤ) ^ 2)]
  · rw [phiM_00]; push_cast; rw [b0, b1, h5, h6]; linear_combination δ'' * hdM
  · rw [phiM_10]; push_cast; rw [b0, b1, h6]; ring

lemma coe_inv_mul_cancel_left (g : SL(2, ℤ)) (X : Mat) : ((g⁻¹ : SL(2, ℤ)) : Mat) * ((g : Mat) * X) = X := by
  rw [← Matrix.mul_assoc, coe_inv_mul_coe, Matrix.one_mul]

lemma coe_mul_cancel_left (g : SL(2, ℤ)) (X : Mat) : (g : Mat) * (((g⁻¹ : SL(2, ℤ)) : Mat) * X) = X := by
  rw [← Matrix.mul_assoc, coe_mul_coe_inv, Matrix.one_mul]

lemma adjugate_SL (g : SL(2, ℤ)) : adjugate (g : Mat) = ((g⁻¹ : SL(2, ℤ)) : Mat) :=
  (Matrix.SpecialLinearGroup.coe_inv g).symm

theorem phiM_conj (g : SL(2, ℤ)) (γ β : Mat) : phiM (conj g γ) ((g : Mat) * β) = phiM γ β := by
  rw [phiM, phiM, conj, Matrix.adjugate_mul_distrib, adjugate_SL]
  simp only [Matrix.mul_assoc, coe_inv_mul_cancel_left]

theorem phiM_mul_right (γ β : Mat) (v : SL(2, ℤ)) : phiM γ (β * (v : Mat)) = conj v⁻¹ (phiM γ β) := by
  rw [phiM, phiM, conj, Matrix.adjugate_mul_distrib, adjugate_SL, inv_inv]
  simp only [Matrix.mul_assoc]

lemma mul_phiM_mul (γ β : Mat) : β * phiM γ β * adjugate β = (β.det ^ 2) • γ := by
  rw [phiM]
  calc β * (adjugate β * γ * β) * adjugate β = (β * adjugate β) * γ * (β * adjugate β) := by
        simp only [Matrix.mul_assoc]
    _ = _ := by
      rw [Matrix.mul_adjugate, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Matrix.one_mul, smul_smul, sq]

theorem phiM_left_cancel {γ₁ γ₂ β : Mat} (hβ : β.det ≠ 0) (h : phiM γ₁ β = phiM γ₂ β) : γ₁ = γ₂ := by
  have := congrArg (fun X => β * X * adjugate β) h
  simp only [mul_phiM_mul] at this
  exact smul_right_injective Mat (pow_ne_zero 2 hβ) this

lemma mem_Gamma1_of_normB {M : ℕ} {k : SL(2, ℤ)} {β₁ β₂ : Mat} (h : (k : Mat) * β₁ = β₂)
    (h1 : NormB M β₁) (h2 : NormB M β₂) : k ∈ Gamma1 M := by
  rw [mem_Gamma1_iff]
  calc k • e1 M = redMat M k *ᵥ (redMat M β₁ *ᵥ e1 M) := by rw [vsmul_def, h1]
    _ = redMat M β₂ *ᵥ e1 M := by rw [Matrix.mulVec_mulVec, ← redMat_mul, h]
    _ = e1 M := h2

/-- `2 × 2` identity `Z X Z = tr(Z X) Z - det Z · adj X`. -/
lemma mul_mul_self_fin_two {R : Type*} [CommRing R] (Z X : Matrix (Fin 2) (Fin 2) R) :
    Z * X * Z = (Z * X).trace • Z - Z.det • adjugate X := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, adjugate_fin_two, Matrix.trace_fin_two, Matrix.det_fin_two] <;> ring

lemma redMat_natCast_smul (p : ℕ) (X : Mat) : redMat p ((p : ℤ) • X) = 0 := by
  ext i j
  simp only [redMat, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply]
  push_cast; simp

/-- Divisibility core of the key lemma. -/
theorem dvd_mul_adj {p : ℕ} [Fact p.Prime] {γ₁ γ₂ β₁ β₂ : Mat} (h1 : β₁.det = p) (h2 : β₂.det = p)
    (heq : phiM γ₁ β₁ = phiM γ₂ β₂) (hprim : ¬ DvdMat p (phiM γ₁ β₁)) : DvdMat p (β₂ * adjugate β₁) := by
  set γ := phiM γ₁ β₁ with hγdef
  have hB : redMat p β₂ * redMat p γ = 0 := by
    rw [← redMat_mul, heq, phiM, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_adjugate, h2,
      Matrix.smul_mul, Matrix.one_mul, Matrix.smul_mul, redMat_natCast_smul]
  have hZ : (redMat p (adjugate β₁)).det = 0 := by
    rw [redMat, ← RingHom.mapMatrix_apply, ← RingHom.map_det, Matrix.det_adjugate, h1]; simp
  obtain ⟨i, j, hij⟩ : ∃ i j : Fin 2, ¬ (p : ℤ) ∣ γ i j := by
    by_contra hcon; push_neg at hcon; exact hprim hcon
  have hne : ((γ i j : ℤ) : ZMod p) ≠ 0 := by rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
  set Z := redMat p (adjugate β₁)
  set E : Matrix (Fin 2) (Fin 2) (ZMod p) := Matrix.single j i 1
  have hid := mul_mul_self_fin_two Z (redMat p γ₁ * redMat p β₁ * E)
  rw [hZ, zero_smul, sub_zero] at hid
  have hγR : redMat p γ = Z * redMat p γ₁ * redMat p β₁ := by
    rw [hγdef, phiM, redMat_mul, redMat_mul]
  have htr : (Z * (redMat p γ₁ * redMat p β₁ * E)).trace = ((γ i j : ℤ) : ZMod p) := by
    rw [← Matrix.mul_assoc Z, ← Matrix.mul_assoc, ← hγR, Matrix.trace_mul_single]
    simp [redMat]
  have h0 : ((γ i j : ℤ) : ZMod p) • (redMat p β₂ * Z) = 0 := by
    rw [← htr, ← Matrix.mul_smul, ← hid]
    calc redMat p β₂ * (Z * (redMat p γ₁ * redMat p β₁ * E) * Z)
        = redMat p β₂ * redMat p γ * E * Z := by rw [hγR]; simp only [Matrix.mul_assoc]
      _ = 0 := by rw [hB, Matrix.zero_mul, Matrix.zero_mul]
  have h0' : redMat p (β₂ * adjugate β₁) = 0 := by
    rw [redMat_mul]; exact (smul_eq_zero.1 h0).resolve_left hne
  intro a b
  have := congrFun (congrFun h0' a) b
  simp only [redMat, Matrix.map_apply, Matrix.zero_apply] at this
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 this

/-- **Key lemma.** Two pairs with the same primitive image differ by `k ∈ SL₂(ℤ)`: `k β₁ = β₂`, `k γ₁ k⁻¹ = γ₂`. -/
theorem key_phiM {p : ℕ} [Fact p.Prime] {γ₁ γ₂ β₁ β₂ : Mat} (h1 : β₁.det = p) (h2 : β₂.det = p)
    (heq : phiM γ₁ β₁ = phiM γ₂ β₂) (hprim : ¬ DvdMat p (phiM γ₁ β₁)) :
    ∃ k : SL(2, ℤ), (k : Mat) * β₁ = β₂ ∧ conj k γ₁ = γ₂ := by
  have hp : (0 : ℤ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  obtain ⟨k₀, hk₀⟩ := dvdMat_iff.1 (dvd_mul_adj h1 h2 heq hprim)
  have hdet : k₀.det = 1 := by
    have := congrArg Matrix.det hk₀
    rw [Matrix.det_mul, Matrix.det_adjugate, Matrix.det_smul, h1, h2] at this
    simp only [Fintype.card_fin] at this
    have hp2 : ((p : ℤ) ^ 2) ≠ 0 := by positivity
    exact (mul_left_cancel₀ hp2 (by rw [← this]; ring)).symm
  let k : SL(2, ℤ) := ⟨k₀, hdet⟩
  have hkβ : (k : Mat) * β₁ = β₂ := by
    apply smul_right_injective Mat hp.ne'
    show (p : ℤ) • (k₀ * β₁) = (p : ℤ) • β₂
    rw [← Matrix.smul_mul, ← hk₀, Matrix.mul_assoc, Matrix.adjugate_mul, h1, Matrix.mul_smul, Matrix.mul_one]
  refine ⟨k, hkβ, ?_⟩
  have e : phiM γ₁ β₁ = phiM (conj k⁻¹ γ₂) β₁ := by
    rw [heq, ← hkβ, ← phiM_conj k⁻¹ γ₂ ((k : Mat) * β₁), coe_inv_mul_cancel_left]
  rw [phiM_left_cancel (by rw [h1]; exact hp.ne') e, conj_conj_inv]

end RamanujanPetersson.S3.DWSS


