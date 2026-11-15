-- Prove2me | Definitions.Def_RPLib_S3_PCE
-- name    : RPLib_S3_PCE
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T16:27:21.861697+00:00
-- url     : https://prove2.me/theorems/2eb7f7d5-f0d5-472b-bbe1-70874a525589
-- title:
--   Weight-two Ramanujan-Petersson library: the primitive classes
-- statement:
--   The primitive classes.
--
--   `(c', ℓ) ↦ [Φ(c'.out, bL ℓ)]` is a bijection from pairs (class of `EllPos M δ'' t' n'`, non-stable line) onto the
--   primitive classes of `EllPos M (δ'' p) (p t') (p² n')` (`psiM_injective`, `psiM_surjective`), hence `card_prim`.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture in weight two (Eichler-Shimura-Ihara route: the Eichler-Selberg trace formula on $S_2(\Gamma_1(M))$, the Deuring-Waterhouse-Schoof count of elliptic curves over $\mathbb F_q$ with level structure by Hurwitz class numbers, conditional on Tate's isogeny theorem in prime-to-$p$ form, the Kronecker-Hurwitz class number relation, and the Hasse-Weil bound for the components of $Y_1(M)$ by the Stepanov-Bombieri method). It contains definitions together with proved lemmas (no `sorry`; where Tate's theorem is used it is an explicit hypothesis), so that later solution files can import them.
-- source:
--   M. Deuring, Die Typen der Multiplikatorenringe elliptischer Funktionenkörper, Abh. Math. Sem. Univ. Hamburg 14 (1941), 197-272; W. C. Waterhouse, Abelian varieties over finite fields, Ann. Sci. École Norm. Sup. (4) 2 (1969), 521-560; R. Schoof, Nonsingular plane cubic curves over finite fields, J. Combin. Theory Ser. A 46 (1987), 183-211; J. H. Silverman, The Arithmetic of Elliptic Curves, 2nd ed., GTM 106, Springer 2009, Chapters III and V; Y. Ihara, Hecke polynomials as congruence zeta functions in elliptic modular case, Ann. of Math. 85 (1967), 267-295; M. Eichler, Quaternäre quadratische Formen und die Riemannsche Vermutung für die Kongruenzzetafunktion, Arch. Math. 5 (1954), 355-366; G. Shimura, Introduction to the Arithmetic Theory of Automorphic Functions, Princeton 1971, Chapter 7

import Mathlib
import Definitions.Def_RPLib_S3_PCD

/-!
# S3-DWS-Supersingular, part C (E): the primitive classes

`(c', ℓ) ↦ [Φ(c'.out, bL ℓ)]` is a bijection from pairs (class of `EllPos M δ'' t' n'`, non-stable line) onto the
primitive classes of `EllPos M (δ'' p) (p t') (p² n')` (`psiM_injective`, `psiM_surjective`), hence `card_prim`.
-/

set_option autoImplicit false

open Matrix MatrixGroups CongruenceSubgroup RamanujanPetersson.S3.Conj

namespace RamanujanPetersson.S3.DWSS

lemma normB_mul_Gamma1 {M : ℕ} {β : Mat} (hN : NormB M β) {g : SL(2, ℤ)} (hg : g ∈ Gamma1 M) :
    NormB M (β * (g : Mat)) := by
  rw [NormB, redMat_mul, ← Matrix.mulVec_mulVec, ← vsmul_def, (mem_Gamma1_iff M g).1 hg]; exact hN

lemma normB_Gamma1_mul {M : ℕ} {β : Mat} (hN : NormB M β) {g : SL(2, ℤ)} (hg : g ∈ Gamma1 M) :
    NormB M ((g : Mat) * β) := by
  rw [NormB, redMat_mul, ← Matrix.mulVec_mulVec, hN, ← vsmul_def, (mem_Gamma1_iff M g).1 hg]

lemma mem_Gamma1_of_normB_right {M p : ℕ} (hu : IsUnit (p : ZMod M)) {β₁ β₂ : Mat} {v : SL(2, ℤ)}
    (hdet : β₁.det = p) (h : β₁ * (v : Mat) = β₂) (h1 : NormB M β₁) (h2 : NormB M β₂) : v ∈ Gamma1 M := by
  rw [mem_Gamma1_iff]
  have hR := isUnit_det_redMat (M := M) hu hdet
  have e : redMat M β₁ *ᵥ (v • e1 M) = redMat M β₁ *ᵥ e1 M := by
    rw [vsmul_def, Matrix.mulVec_mulVec, ← redMat_mul, h]; exact h2.trans h1.symm
  have cancel : ∀ w : Fin 2 → ZMod M, (redMat M β₁)⁻¹ *ᵥ (redMat M β₁ *ᵥ w) = w := fun w => by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hR, Matrix.one_mulVec]
  rw [← cancel (v • e1 M), e, cancel]

lemma fits_mul_right {p : ℕ} {ℓ : Option (ZMod p)} {β : Mat} (h : Fits p ℓ β) (w : Mat) :
    Fits p ℓ (β * w) := by
  obtain ⟨k, hk⟩ := dvdMat_iff.1 h
  exact dvdMat_iff.2 ⟨k * w, by rw [← Matrix.mul_assoc, hk, Matrix.smul_mul]⟩

section Bij

variable {M p : ℕ} [NeZero M] [Fact p.Prime] {δ'' : ZMod M} {t' : ℤ} {n' : ℕ}

/-- Pairs (class, non-stable line). -/
abbrev Dom (M p : ℕ) [NeZero M] (δ'' : ZMod M) (t' : ℤ) (n' : ℕ) :=
  {x : QE M δ'' t' n' × Option (ZMod p) // qv p (x.1.out : Mat) x.2 ≠ 0}

/-- `(c', ℓ) ↦ [Φ(c'.out, bL ℓ)]`. -/
noncomputable def psiM (hu : IsUnit (p : ZMod M)) (x : Dom M p δ'' t' n') :
    {C : QE M (δ'' * p) (p * t') (p ^ 2 * n') // ¬ DvdMat p (C.out : Mat)} :=
  ⟨Quotient.mk _ ⟨phiM (x.1.1.out : Mat) (bL M p x.1.2),
    phiM_mem (Fact.out : p.Prime).pos x.1.1.out.2 (det_bL M p _) (normB_bL hu _)⟩, by
    rw [dvdMat_out_iff, dvdMat_phiM_bL_iff]; exact x.2⟩

theorem psiM_injective (hM : 4 ≤ M) (hu : IsUnit (p : ZMod M)) :
    Function.Injective (psiM (M := M) (p := p) (δ'' := δ'') (t' := t') (n' := n') hu) := by
  rintro ⟨⟨c₁, ℓ₁⟩, h₁⟩ ⟨⟨c₂, ℓ₂⟩, h₂⟩ h
  have h' := congrArg Subtype.val h
  simp only [psiM] at h'
  obtain ⟨g, hg⟩ := (mk_eq_mk_iff _ _).1 h'
  have hv := congrArg Subtype.val hg
  rw [ellPos_smul_val] at hv
  simp only at hv
  have hgG : (g : SL(2, ℤ)) ∈ Gamma1 M := g.2
  have e : phiM (c₁.out : Mat) (bL M p ℓ₁) =
      phiM (c₂.out : Mat) (bL M p ℓ₂ * (((g : SL(2, ℤ))⁻¹ : SL(2, ℤ)) : Mat)) := by
    rw [phiM_mul_right, inv_inv, hv]
  have hprim : ¬ DvdMat p (phiM (c₁.out : Mat) (bL M p ℓ₁)) := by rw [dvdMat_phiM_bL_iff]; exact h₁
  have hd2 : (bL M p ℓ₂ * (((g : SL(2, ℤ))⁻¹ : SL(2, ℤ)) : Mat)).det = p := by
    rw [Matrix.det_mul, det_bL, Matrix.SpecialLinearGroup.det_coe, mul_one]
  obtain ⟨k, hk1, hk2⟩ := key_phiM (det_bL M p ℓ₁) hd2 e hprim
  have hkG : k ∈ Gamma1 M := mem_Gamma1_of_normB hk1 (normB_bL hu ℓ₁)
    (normB_mul_Gamma1 (normB_bL hu ℓ₂) (inv_mem hgG))
  have hc : c₁ = c₂ := by
    rw [← Quotient.out_eq c₁, ← Quotient.out_eq c₂]
    exact (mk_eq_mk_iff _ _).2 ⟨⟨k⁻¹, inv_mem hkG⟩, Subtype.ext (by
      rw [ellPos_smul_val]
      exact (congrArg (conj k⁻¹) hk2).symm.trans (conj_inv_conj k _))⟩
  subst hc
  have hk : k = 1 := free_conj hM c₁.out.2 hkG hk2
  subst hk
  rw [Matrix.SpecialLinearGroup.coe_one, Matrix.one_mul] at hk1
  have hl : ℓ₁ = ℓ₂ := fits_unique (det_bL M p ℓ₁) (fits_bL M p ℓ₁)
    (by rw [hk1]; exact fits_mul_right (fits_bL M p ℓ₂) _)
  subst hl
  rfl

theorem psiM_surjective (hu : IsUnit (p : ZMod M)) :
    Function.Surjective (psiM (M := M) (p := p) (δ'' := δ'') (t' := t') (n' := n') hu) := by
  rintro ⟨C, hC⟩
  obtain ⟨γ', hγ', β, hβ, hN, hphi⟩ := exists_pre hu C.out.2 hC
  obtain ⟨g, hg⟩ := (mk_eq_mk_iff _ _).1 (Quotient.out_eq (Quotient.mk (MulAction.orbitRel (Gamma1 M)
    (EllPos M δ'' t' n')) ⟨γ', hγ'⟩))
  have hgv : ((Quotient.out (Quotient.mk (MulAction.orbitRel (Gamma1 M) (EllPos M δ'' t' n')) ⟨γ', hγ'⟩) :
      EllPos M δ'' t' n') : Mat) = conj (g : SL(2, ℤ)) γ' := by
    rw [← hg, ellPos_smul_val]
  have hβ' : (((g : SL(2, ℤ)) : Mat) * β).det = p := by
    rw [Matrix.det_mul, Matrix.SpecialLinearGroup.det_coe, one_mul, hβ]
  have hN' := normB_Gamma1_mul hN g.2
  obtain ⟨ℓ, hℓ⟩ := exists_fits hβ'
  obtain ⟨k₁, hk₁⟩ := exists_SL_of_fits hβ' hℓ
  have hbv : bL M p ℓ * (((wL M p ℓ)⁻¹ * k₁ : SL(2, ℤ)) : Mat) = ((g : SL(2, ℤ)) : Mat) * β := by
    rw [bL, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_assoc, coe_mul_cancel_left, hk₁]
  have hvG := mem_Gamma1_of_normB_right hu (det_bL M p ℓ) hbv (normB_bL hu ℓ) hN'
  have hphiv : phiM ((Quotient.out (Quotient.mk (MulAction.orbitRel (Gamma1 M) (EllPos M δ'' t' n'))
      ⟨γ', hγ'⟩) : EllPos M δ'' t' n') : Mat) (bL M p ℓ) =
      conj ((wL M p ℓ)⁻¹ * k₁) (C.out : Mat) := by
    rw [← hphi, hgv, ← phiM_conj (g : SL(2, ℤ)) γ' β, ← hbv, phiM_mul_right, conj_conj_inv]
  have hq : qv p ((Quotient.out (Quotient.mk (MulAction.orbitRel (Gamma1 M) (EllPos M δ'' t' n'))
      ⟨γ', hγ'⟩) : EllPos M δ'' t' n') : Mat) ℓ ≠ 0 := by
    rw [Ne, ← dvdMat_phiM_bL_iff (M := M), hphiv, dvdMat_conj_iff]; exact hC
  refine ⟨⟨(Quotient.mk _ ⟨γ', hγ'⟩, ℓ), hq⟩, Subtype.ext ?_⟩
  simp only [psiM]
  rw [← Quotient.out_eq C]
  exact (mk_eq_mk_iff _ _).2 ⟨⟨_, hvG⟩, Subtype.ext (by rw [ellPos_smul_val]; exact hphiv.symm)⟩

/-- **Primitive classes.** -/
theorem card_prim (hM : 4 ≤ M) (hu : IsUnit (p : ZMod M)) [Fintype (QE M δ'' t' n')] :
    Nat.card {C : QE M (δ'' * p) (p * t') (p ^ 2 * n') // ¬ DvdMat p (C.out : Mat)} =
      ∑ c : QE M δ'' t' n', Nat.card {ℓ : Option (ZMod p) // qv p (c.out : Mat) ℓ ≠ 0} := by
  have hb := Nat.card_eq_of_bijective (psiM (M := M) (p := p) (δ'' := δ'') (t' := t') (n' := n') hu)
    ⟨psiM_injective hM hu, psiM_surjective hu⟩
  rw [← hb]
  exact (Nat.card_congr (Equiv.subtypeProdEquivSigmaSubtype
    (fun (c : QE M δ'' t' n') (ℓ : Option (ZMod p)) => qv p (c.out : Mat) ℓ ≠ 0))).trans Nat.card_sigma

end Bij

end RamanujanPetersson.S3.DWSS


