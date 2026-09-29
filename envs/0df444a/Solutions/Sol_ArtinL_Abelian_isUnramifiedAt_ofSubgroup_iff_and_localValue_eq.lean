-- Prove2me | solution 1 for ArtinL.Abelian.isUnramifiedAt_ofSubgroup_iff_and_localValue_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/61043c5f-09a8-54f2-a15f-963802f8108a

import Mathlib
import Definitions.Def_ArtinL_EulerFactor
import Definitions.Def_ArtinL_Abelian
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ArtinL_Abelian_isUnramifiedAt_ofSubgroup_iff_and_localValue_eq

set_option autoImplicit false

open scoped MatrixGroups
open NumberField

local notation "Γℚ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

open scoped Pointwise Classical
open IsDedekindDomain

namespace ArtinL
p2m_export "ArtinL" "Abelian.inertiaGroup Abelian.IsUnramifiedAt Abelian.localValue Abelian.ofSubgroup Abelian.ofSubgroup_apply Abelian.restrictScalars_fixingSubgroupEquiv"
namespace C3
p2m_open "ArtinL"
open scoped Pointwise

section inertia_smul
variable {M R : Type*} [Group M] [Ring R] [MulSemiringAction M R]

theorem mem_inertia_smul_iff (I : Ideal R) (g σ : M) : σ ∈ (g • I).inertia M ↔ g⁻¹ * σ * g ∈ I.inertia M := by
  constructor
  · intro h x
    have := h (g • x)
    rw [Submodule.mem_toAddSubgroup, Ideal.mem_pointwise_smul_iff_inv_smul_mem, smul_sub, inv_smul_smul, ← mul_smul,
      ← mul_smul] at this
    rw [Submodule.mem_toAddSubgroup]
    simpa [mul_assoc] using this
  · intro h x
    have := h (g⁻¹ • x)
    rw [Submodule.mem_toAddSubgroup] at this
    rw [Submodule.mem_toAddSubgroup, Ideal.mem_pointwise_smul_iff_inv_smul_mem, smul_sub, ← mul_smul]
    simpa [mul_smul, mul_assoc] using this

theorem mem_stabilizer_smul_iff (I : Ideal R) (g σ : M) :
    σ ∈ MulAction.stabilizer M (g • I) ↔ g⁻¹ * σ * g ∈ MulAction.stabilizer M I := by
  rw [MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff, mul_smul, mul_smul, inv_smul_eq_iff]

end inertia_smul

section transfer
variable (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField F]
  (K : IntermediateField ℚ F)

theorem restrictScalars_smul (σ' : F ≃ₐ[↥K] F) (x : 𝓞 F) : σ'.restrictScalars ℚ • x = σ' • x := rfl

theorem mem_inertia_iff_restrictScalars (Q : Ideal (𝓞 F)) (σ' : F ≃ₐ[↥K] F) :
    σ' ∈ Q.inertia (F ≃ₐ[↥K] F) ↔ σ'.restrictScalars ℚ ∈ Q.inertia (F ≃ₐ[ℚ] F) := Iff.rfl

theorem mem_stabilizer_iff_restrictScalars (Q : Ideal (𝓞 F)) (σ' : F ≃ₐ[↥K] F) :
    σ' ∈ MulAction.stabilizer (F ≃ₐ[↥K] F) Q ↔ σ'.restrictScalars ℚ ∈ MulAction.stabilizer (F ≃ₐ[ℚ] F) Q := Iff.rfl

variable [IsGalois ℚ F]

theorem exists_restrictScalars_eq_of_mem (H : Subgroup (F ≃ₐ[ℚ] F)) (σ : F ≃ₐ[ℚ] F) (hσ : σ ∈ H) :
    ∃ σ' : F ≃ₐ[↥(IntermediateField.fixedField H)] F, σ'.restrictScalars ℚ = σ :=
  ⟨IntermediateField.fixingSubgroupEquiv (IntermediateField.fixedField H)
      ⟨σ, (IntermediateField.fixingSubgroup_fixedField H).symm ▸ hσ⟩,
    ArtinL.Abelian.restrictScalars_fixingSubgroupEquiv _ _⟩

theorem restrictScalars_mem (H : Subgroup (F ≃ₐ[ℚ] F)) (σ' : F ≃ₐ[↥(IntermediateField.fixedField H)] F) :
    σ'.restrictScalars ℚ ∈ H :=
  (IntermediateField.fixingSubgroup_fixedField H).le fun x => σ'.commutes x

end transfer

end ArtinL.C3

namespace ArtinL
p2m_export "ArtinL" "Abelian.inertiaGroup Abelian.IsUnramifiedAt Abelian.localValue Abelian.ofSubgroup Abelian.ofSubgroup_apply Abelian.restrictScalars_fixingSubgroupEquiv"
namespace C3
p2m_open "ArtinL"
open scoped Pointwise

section frob
variable (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField F] [IsGalois ℚ F]
  (K : IntermediateField ℚ F) {p : ℕ} (hp : p.Prime)
  (Q : Ideal (𝓞 F)) [Q.IsMaximal] [Q.LiesOver (Ideal.span {(p : ℤ)})]

include hp in

theorem card_int_quot_under : Nat.card (ℤ ⧸ Q.under ℤ) = p := by
  have hQu : Q.under ℤ = Ideal.span {(p : ℤ)} := (‹Q.LiesOver (Ideal.span {(p : ℤ)})›.over).symm
  rw [hQu, Nat.card_congr (Int.quotientSpanNatEquivZMod p).toEquiv, Nat.card_zmod]

theorem liesOver_of_under_eq (v : IsDedekindDomain.HeightOneSpectrum (𝓞 ↥K)) (hv : Q.under (𝓞 ↥K) = v.asIdeal) :
    v.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) := by
  constructor
  rw [← hv, Ideal.under_under]
  exact Ideal.LiesOver.over

include hp in

theorem card_quot_place (v : IsDedekindDomain.HeightOneSpectrum (𝓞 ↥K)) (hv : Q.under (𝓞 ↥K) = v.asIdeal) :
    Nat.card (𝓞 ↥K ⧸ v.asIdeal) = p ^ (Ideal.span {(p : ℤ)}).inertiaDeg' v.asIdeal := by
  haveI := liesOver_of_under_eq F K (p := p) Q v hv
  rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, Ideal.absNorm_eq_pow_inertiaDeg' _ hp]

include hp in

theorem frob_pow_smul_sub_pow_mem (j : ℕ) (x : 𝓞 F) :
    (arithFrobAt ℤ (F ≃ₐ[ℚ] F) Q ^ j) • x - x ^ (p ^ j) ∈ Q := by
  have hF : IsArithFrobAt ℤ (arithFrobAt ℤ (F ≃ₐ[ℚ] F) Q) Q := IsArithFrobAt.arithFrobAt ℤ (F ≃ₐ[ℚ] F) Q
  have hstab := hF.mem_stabilizer
  have hcard : Nat.card (ℤ ⧸ Q.under ℤ) = p := card_int_quot_under F hp Q
  have hQ : arithFrobAt ℤ (F ≃ₐ[ℚ] F) Q • Q = Q := MulAction.mem_stabilizer_iff.1 hstab
  have hx : (Ideal.Quotient.mk Q) (arithFrobAt ℤ (F ≃ₐ[ℚ] F) Q • x) = (Ideal.Quotient.mk Q) (x ^ p) := by
    have := hF x
    rw [hcard, ← Ideal.Quotient.eq] at this
    exact this
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ', mul_smul, pow_succ, pow_mul]
    rw [← Ideal.Quotient.eq] at ih ⊢
    have h1 : (Ideal.Quotient.mk Q) ((arithFrobAt ℤ (F ≃ₐ[ℚ] F) Q) • ((arithFrobAt ℤ (F ≃ₐ[ℚ] F) Q ^ j) • x)) =
        (Ideal.Quotient.mk Q) ((arithFrobAt ℤ (F ≃ₐ[ℚ] F) Q) • (x ^ p ^ j)) := by
      rw [Ideal.Quotient.eq, ← smul_sub]
      have := Ideal.smul_mem_pointwise_smul (arithFrobAt ℤ (F ≃ₐ[ℚ] F) Q) _ Q ((Ideal.Quotient.eq).1 ih)
      rwa [hQ] at this
    rw [h1, smul_pow', map_pow, hx, ← map_pow, ← pow_mul, ← pow_mul, mul_comm]

include hp in

theorem isArithFrobAt_of_inv_mul_frob_pow_mem (v : IsDedekindDomain.HeightOneSpectrum (𝓞 ↥K)) (hv : Q.under (𝓞 ↥K) = v.asIdeal)
    (σ' : F ≃ₐ[↥K] F)
    (h : (σ'.restrictScalars ℚ)⁻¹ * arithFrobAt ℤ (F ≃ₐ[ℚ] F) Q ^ (Ideal.span {(p : ℤ)}).inertiaDeg' v.asIdeal ∈
      Q.inertia (F ≃ₐ[ℚ] F)) :
    IsArithFrobAt (𝓞 ↥K) σ' Q := by
  intro x
  change σ' • x - x ^ Nat.card (𝓞 ↥K ⧸ Q.under (𝓞 ↥K)) ∈ Q
  rw [hv, card_quot_place F K hp Q v hv, ← restrictScalars_smul]
  set ι := (σ'.restrictScalars ℚ)⁻¹ * arithFrobAt ℤ (F ≃ₐ[ℚ] F) Q ^ (Ideal.span {(p : ℤ)}).inertiaDeg' v.asIdeal with hι
  have hσ : σ'.restrictScalars ℚ = arithFrobAt ℤ (F ≃ₐ[ℚ] F) Q ^ (Ideal.span {(p : ℤ)}).inertiaDeg' v.asIdeal * ι⁻¹ := by
    rw [hι]; group
  rw [hσ, mul_smul]

  have h1 : ι⁻¹ • x - x ∈ Q := (Q.inertia (F ≃ₐ[ℚ] F)).inv_mem h x
  have hstab := (IsArithFrobAt.arithFrobAt ℤ (F ≃ₐ[ℚ] F) Q).mem_stabilizer
  have h2 : (arithFrobAt ℤ (F ≃ₐ[ℚ] F) Q ^ (Ideal.span {(p : ℤ)}).inertiaDeg' v.asIdeal) • (ι⁻¹ • x) -
      (arithFrobAt ℤ (F ≃ₐ[ℚ] F) Q ^ (Ideal.span {(p : ℤ)}).inertiaDeg' v.asIdeal) • x ∈ Q := by
    rw [← smul_sub]
    have hstabj : arithFrobAt ℤ (F ≃ₐ[ℚ] F) Q ^ (Ideal.span {(p : ℤ)}).inertiaDeg' v.asIdeal ∈
        MulAction.stabilizer (F ≃ₐ[ℚ] F) Q := Subgroup.pow_mem _ hstab _
    have := Ideal.smul_mem_pointwise_smul (arithFrobAt ℤ (F ≃ₐ[ℚ] F) Q ^ (Ideal.span {(p : ℤ)}).inertiaDeg' v.asIdeal) _ Q h1
    rwa [MulAction.mem_stabilizer_iff.1 hstabj] at this
  have h3 := frob_pow_smul_sub_pow_mem F hp Q ((Ideal.span {(p : ℤ)}).inertiaDeg' v.asIdeal) x
  have := Q.add_mem h2 h3
  simpa using this

end frob

end ArtinL.C3

set_option maxHeartbeats 1600000 in

theorem solution
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField F] [IsGalois ℚ F]
    (H : Subgroup (F ≃ₐ[ℚ] F)) (χ : H →* ℂˣ) {p : ℕ} (hp : p.Prime)
    (Q : Ideal (𝓞 F)) [Q.IsMaximal] [Q.LiesOver (Ideal.span {(p : ℤ)})]
    (v : HeightOneSpectrum (𝓞 ↥(IntermediateField.fixedField H)))
    (hv : Q.under (𝓞 ↥(IntermediateField.fixedField H)) = v.asIdeal) :
    (ArtinL.Abelian.IsUnramifiedAt (ArtinL.Abelian.ofSubgroup H χ) v ↔
        ∀ (σ : F ≃ₐ[ℚ] F) (hσ : σ ∈ H), σ ∈ Q.inertia (F ≃ₐ[ℚ] F) → χ ⟨σ, hσ⟩ = 1) ∧
    (ArtinL.Abelian.IsUnramifiedAt (ArtinL.Abelian.ofSubgroup H χ) v →
        ∀ (σ : F ≃ₐ[ℚ] F) (hσ : σ ∈ H),
          σ⁻¹ * arithFrobAt ℤ (F ≃ₐ[ℚ] F) Q ^ (Ideal.span {(p : ℤ)}).inertiaDeg' v.asIdeal ∈
              Q.inertia (F ≃ₐ[ℚ] F) →
            ArtinL.Abelian.localValue (ArtinL.Abelian.ofSubgroup H χ) v = ((χ ⟨σ, hσ⟩ : ℂˣ) : ℂ)) := by

  haveI : Finite (F ≃ₐ[↥(IntermediateField.fixedField H)] F) :=
    Finite.of_injective (fun σ : F ≃ₐ[↥(IntermediateField.fixedField H)] F => σ.restrictScalars ℚ)
      (AlgEquiv.restrictScalars_injective ℚ)
  haveI : Algebra.IsInvariant (𝓞 ↥(IntermediateField.fixedField H)) (𝓞 F) (F ≃ₐ[↥(IntermediateField.fixedField H)] F) :=
    IsGaloisGroup.isInvariant

  obtain ⟨g, hg⟩ := Algebra.IsInvariant.exists_smul_of_under_eq (𝓞 ↥(IntermediateField.fixedField H)) (𝓞 F)
    (F ≃ₐ[↥(IntermediateField.fixedField H)] F) Q (LanglandsTunnell.P2.Artin.primeAbove ↥(IntermediateField.fixedField H) F v)
    (hv.trans (LanglandsTunnell.P2.Artin.under_primeAbove ↥(IntermediateField.fixedField H) F v).symm)

  set ψ := ArtinL.Abelian.ofSubgroup H χ with hψ

  have hunr_iff : ArtinL.Abelian.IsUnramifiedAt ψ v ↔
      ∀ τ ∈ (g • Q).inertia (F ≃ₐ[↥(IntermediateField.fixedField H)] F), ψ τ = 1 := by
    rw [ArtinL.Abelian.IsUnramifiedAt, ArtinL.Abelian.inertiaGroup, hg]

  have hψconj : ∀ a b : F ≃ₐ[↥(IntermediateField.fixedField H)] F, ψ (a * b * a⁻¹) = ψ b := fun a b => by
    rw [map_mul, map_mul, map_inv, mul_comm (ψ a), mul_assoc, mul_inv_cancel, mul_one]
  have key : ArtinL.Abelian.IsUnramifiedAt ψ v ↔
      ∀ (σ : F ≃ₐ[ℚ] F) (hσ : σ ∈ H), σ ∈ Q.inertia (F ≃ₐ[ℚ] F) → χ ⟨σ, hσ⟩ = 1 := by
    rw [hunr_iff]
    constructor
    · intro h σ hσ hI
      obtain ⟨σ', rfl⟩ := ArtinL.C3.exists_restrictScalars_eq_of_mem F H σ hσ
      have hmem : g * σ' * g⁻¹ ∈ (g • Q).inertia (F ≃ₐ[↥(IntermediateField.fixedField H)] F) := by
        rw [ArtinL.C3.mem_inertia_smul_iff]
        simpa [mul_assoc] using (ArtinL.C3.mem_inertia_iff_restrictScalars F _ Q σ').2 hI
      have := h _ hmem
      rw [hψconj] at this
      exact this
    · intro h τ hτ
      have hσ' := (ArtinL.C3.mem_inertia_smul_iff Q g τ).1 hτ
      have h1 : ψ (g⁻¹ * τ * g) = 1 :=
        h _ (ArtinL.C3.restrictScalars_mem F H _) ((ArtinL.C3.mem_inertia_iff_restrictScalars F _ Q _).1 hσ')
      rw [← hψconj g, show g * (g⁻¹ * τ * g) * g⁻¹ = τ by group] at h1
      exact h1
  refine ⟨key, fun hunr σ hσ hfrob => ?_⟩

  rw [ArtinL.Abelian.localValue, if_pos hunr]
  obtain ⟨σ', hσ'⟩ := ArtinL.C3.exists_restrictScalars_eq_of_mem F H σ hσ
  have hFσ' : IsArithFrobAt (𝓞 ↥(IntermediateField.fixedField H)) σ' Q :=
    ArtinL.C3.isArithFrobAt_of_inv_mul_frob_pow_mem F (IntermediateField.fixedField H) hp Q v hv σ' (hσ' ▸ hfrob)
  have hconj := hFσ'.conj g
  have hΦ := LanglandsTunnell.P2.Artin.isArithFrobAt_artinFrob ↥(IntermediateField.fixedField H) F v
  rw [hg] at hΦ
  have hdiff := hΦ.mul_inv_mem_inertia hconj
  have h1 : ψ (LanglandsTunnell.P2.Artin.artinFrob ↥(IntermediateField.fixedField H) F v * (g * σ' * g⁻¹)⁻¹) = 1 :=
    (hunr_iff.1 hunr) _ hdiff
  rw [map_mul, map_inv, mul_inv_eq_one, hψconj] at h1
  rw [h1, hψ, ArtinL.Abelian.ofSubgroup_apply]
  congr 2
  exact Subtype.ext hσ'

end S_ArtinL_Abelian_isUnramifiedAt_ofSubgroup_iff_and_localValue_eq
end P2MW
export P2MW.S_ArtinL_Abelian_isUnramifiedAt_ofSubgroup_iff_and_localValue_eq (solution)
