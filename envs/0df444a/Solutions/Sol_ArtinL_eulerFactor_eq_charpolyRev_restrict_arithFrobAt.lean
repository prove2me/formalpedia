-- Prove2me | solution 1 for ArtinL.eulerFactor_eq_charpolyRev_restrict_arithFrobAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/5eba2fce-99ee-5435-895e-1c6c16e8c56c

import Mathlib
import Definitions.Def_ArtinL_EulerFactor
import Theorems.Thm_ArtinL_eulerFactorAt_eq_eulerFactor
import Theorems.Thm_ValuationSubring_exists_ideal_ringOfIntegers_inertia_eq_map_restrictNormalHom
import Theorems.Thm_ValuationSubring_exists_liesOverPrime_isFrobeniusAt_ratAlgClosure
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ArtinL_eulerFactor_eq_charpolyRev_restrict_arithFrobAt

set_option autoImplicit false

noncomputable section

open scoped MatrixGroups Pointwise
open NumberField

namespace ArtinDictProof

section Rep

variable {G : Type} [Group G] {n : ℕ} (π : G →* GL (Fin n) ℂ)

abbrev Inv (S : Subgroup G) : Submodule ℂ (Fin n → ℂ) :=
  Representation.invariants ((Deformation.matrixRepresentation π).comp S.subtype)

theorem mem_Inv {S : Subgroup G} {v : Fin n → ℂ} :
    v ∈ Inv π S ↔ ∀ s ∈ S, Deformation.matrixRepresentation π s v = v := by
  rw [Inv, Representation.mem_invariants]
  exact ⟨fun h s hs => h ⟨s, hs⟩, fun h s => h s s.2⟩

theorem rep_mul_apply (g h : G) (v : Fin n → ℂ) :
    Deformation.matrixRepresentation π (g * h) v =
      Deformation.matrixRepresentation π g (Deformation.matrixRepresentation π h v) := by
  rw [map_mul]; rfl

theorem stable {S : Subgroup G} {g : G} (hg : ∀ s ∈ S, g⁻¹ * s * g ∈ S) :
    ∀ v ∈ Inv π S, Deformation.matrixRepresentation π g v ∈ Inv π S := by
  intro v hv
  rw [mem_Inv] at hv ⊢
  intro s hs
  have h1 : s * g = g * (g⁻¹ * s * g) := by group
  rw [← rep_mul_apply, h1, rep_mul_apply, hv _ (hg s hs)]

theorem restrict_eq_of_mul_inv_mem {S : Subgroup G} {g h : G} (hgh : g * h⁻¹ ∈ S)
    (hg : ∀ v ∈ Inv π S, Deformation.matrixRepresentation π g v ∈ Inv π S)
    (hh : ∀ v ∈ Inv π S, Deformation.matrixRepresentation π h v ∈ Inv π S) :
    (Deformation.matrixRepresentation π g).restrict hg =
      (Deformation.matrixRepresentation π h).restrict hh := by
  refine LinearMap.ext fun v => Subtype.ext ?_
  obtain ⟨v, hv⟩ := v
  change Deformation.matrixRepresentation π g v = Deformation.matrixRepresentation π h v
  have h1 : g = (g * h⁻¹) * h := by group
  have hhv := hh v hv
  rw [mem_Inv] at hhv
  conv_lhs => rw [h1, rep_mul_apply, hhv _ hgh]

abbrev conjSub (S : Subgroup G) (g : G) : Subgroup G := S.map (MulAut.conj g).toMonoidHom

theorem mem_conjSub {S : Subgroup G} {g x : G} : x ∈ conjSub S g ↔ g⁻¹ * x * g ∈ S := by
  rw [conjSub, Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hy
  · intro h
    exact ⟨g⁻¹ * x * g, h, by simp [MulAut.conj_apply, mul_assoc]⟩

theorem apply_mem_Inv_conj {S : Subgroup G} (g : G) {v : Fin n → ℂ} (hv : v ∈ Inv π S) :
    Deformation.matrixRepresentation π g v ∈ Inv π (conjSub S g) := by
  rw [mem_Inv] at hv ⊢
  intro x hx
  have h1 : x * g = g * (g⁻¹ * x * g) := by group
  rw [← rep_mul_apply, h1, rep_mul_apply, hv _ (mem_conjSub.1 hx)]

def conjEquiv (S : Subgroup G) (g : G) : Inv π S ≃ₗ[ℂ] Inv π (conjSub S g) where
  toFun v := ⟨Deformation.matrixRepresentation π g v, apply_mem_Inv_conj π g v.2⟩
  invFun w := ⟨Deformation.matrixRepresentation π g⁻¹ w, by
    have h := apply_mem_Inv_conj π g⁻¹ w.2
    have hS : conjSub (conjSub S g) g⁻¹ = S := by
      ext x; simp [mul_assoc]
    rwa [hS] at h⟩
  map_add' v w := Subtype.ext (map_add _ _ _)
  map_smul' c v := Subtype.ext (map_smul _ _ _)
  left_inv v := Subtype.ext (by
    change Deformation.matrixRepresentation π g⁻¹ (Deformation.matrixRepresentation π g v) = v
    rw [← rep_mul_apply, inv_mul_cancel, map_one]; rfl)
  right_inv w := Subtype.ext (by
    change Deformation.matrixRepresentation π g (Deformation.matrixRepresentation π g⁻¹ w) = w
    rw [← rep_mul_apply, mul_inv_cancel, map_one]; rfl)

theorem charpolyRev_restrict_conj {S : Subgroup G} (g s : G)
    (hs : ∀ v ∈ Inv π S, Deformation.matrixRepresentation π s v ∈ Inv π S)
    (hs' : ∀ v ∈ Inv π (conjSub S g),
      Deformation.matrixRepresentation π (g * s * g⁻¹) v ∈ Inv π (conjSub S g)) :
    ArtinL.charpolyRev ((Deformation.matrixRepresentation π (g * s * g⁻¹)).restrict hs') =
      ArtinL.charpolyRev ((Deformation.matrixRepresentation π s).restrict hs) := by
  rw [← ArtinL.charpolyRev_conj (conjEquiv π S g) ((Deformation.matrixRepresentation π s).restrict hs)]
  congr 1
  refine LinearMap.ext fun w => Subtype.ext ?_
  rw [LinearEquiv.conj_apply]
  change Deformation.matrixRepresentation π (g * s * g⁻¹) w =
    Deformation.matrixRepresentation π g (Deformation.matrixRepresentation π s
      (Deformation.matrixRepresentation π g⁻¹ w))
  rw [rep_mul_apply, rep_mul_apply]

end Rep

section Inertia

variable {G : Type} [Group G] {S : Type*} [CommRing S] [MulSemiringAction G S]

theorem inertia_smul (Q : Ideal S) (g : G) :
    (g • Q).inertia G = conjSub (Q.inertia G) g := by
  ext τ
  rw [mem_conjSub]
  simp only [Ideal.inertia, AddSubgroup.mem_inertia, Submodule.mem_toAddSubgroup]
  constructor
  · intro h x
    have h1 := h (g • x)
    rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem] at h1
    simpa only [smul_sub, smul_smul, inv_mul_cancel, one_smul, ← mul_assoc] using h1
  · intro h x
    rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem]
    have h1 := h (g⁻¹ • x)
    simp only [smul_sub, smul_smul, mul_inv_cancel_right] at h1 ⊢
    exact h1

theorem conj_mem_inertia {Q : Ideal S} {g : G} (hg : g • Q = Q) {s : G} (hs : s ∈ Q.inertia G) :
    g⁻¹ * s * g ∈ Q.inertia G := by
  have h : s ∈ (g • Q).inertia G := by rwa [hg]
  rw [inertia_smul] at h
  exact mem_conjSub.1 h

end Inertia

section Main

local notation "Γℚ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
local notation "ℚbar" => AlgebraicClosure ℚ

variable {n : ℕ}

theorem card_quotient_under {S : Type*} [CommRing S] [Nontrivial S] [Algebra ℤ S] (Q : Ideal S)
    [Q.IsMaximal] {p : ℕ} (hp : p.Prime) (hpQ : (p : S) ∈ Q) :
    Nat.card (ℤ ⧸ Q.under ℤ) = p := by
  have hunder : Q.under ℤ = Ideal.span {(p : ℤ)} := by
    haveI : (Ideal.span {(p : ℤ)}).IsMaximal :=
      PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible
    refine (Ideal.IsMaximal.eq_of_le this ?_ ?_).symm
    · exact Ideal.comap_ne_top _ (Ideal.IsMaximal.ne_top inferInstance)
    · rw [Ideal.span_singleton_le_iff_mem, Ideal.under, Ideal.mem_comap]
      simpa using hpQ
  rw [hunder, Nat.card_congr (Int.quotientSpanNatEquivZMod p).toEquiv, Nat.card_zmod]

theorem under_eq_span {S : Type*} [CommRing S] [Nontrivial S] [Algebra ℤ S] (Q : Ideal S)
    [Q.IsMaximal] {p : ℕ} (hp : p.Prime) (hpQ : (p : S) ∈ Q) :
    Q.under ℤ = Ideal.span {(p : ℤ)} := by
  haveI : (Ideal.span {(p : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible
  refine (Ideal.IsMaximal.eq_of_le this ?_ ?_).symm
  · exact Ideal.comap_ne_top _ (Ideal.IsMaximal.ne_top inferInstance)
  · rw [Ideal.span_singleton_le_iff_mem, Ideal.under, Ideal.mem_comap]
    simpa using hpQ

theorem residue_eq_iff {L : Type*} [Field L] (A : ValuationSubring L) (a b : A) :
    IsLocalRing.residue A a = IsLocalRing.residue A b ↔ ((a : L) - b) ∈ A.nonunits := by
  rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff,
    ← ValuationSubring.coe_mem_nonunits_iff]
  rfl

@[scoped simp] theorem coe_decomp_smul {K L : Type*} [Field K] [Field L] [Algebra K L]
    (A : ValuationSubring L) (d : A.decompositionSubgroup K) (a : A) :
    ((d • a : A) : L) = (d : L ≃ₐ[K] L) a := rfl

theorem mem_decompositionSubgroup_iff {K L : Type*} [Field K] [Field L] [Algebra K L]
    (A : ValuationSubring L) (σ : L ≃ₐ[K] L) :
    σ ∈ A.decompositionSubgroup K ↔ σ • A = A := MulAction.mem_stabilizer_iff

theorem isFrobeniusAt_iff {K L : Type*} [Field K] [Field L] [Algebra K L] (A : ValuationSubring L)
    (σ : L ≃ₐ[K] L) (q : ℕ) :
    A.IsFrobeniusAt σ q ↔ σ • A = A ∧ ∀ a ∈ A, σ a - a ^ q ∈ A.nonunits := by
  constructor
  · rintro ⟨hσ, h⟩
    refine ⟨(mem_decompositionSubgroup_iff A σ).1 hσ, fun a ha => ?_⟩
    have h1 := h (IsLocalRing.residue A ⟨a, ha⟩)
    rw [← IsLocalRing.ResidueField.residue_smul, ← map_pow, residue_eq_iff] at h1
    simpa using h1
  · rintro ⟨hσ, h⟩
    refine ⟨(mem_decompositionSubgroup_iff A σ).2 hσ, fun x => ?_⟩
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective x
    rw [← IsLocalRing.ResidueField.residue_smul, ← map_pow, residue_eq_iff]
    simpa using h a a.2

theorem charpolyRev_restrict_congr {V : Type*} [AddCommGroup V] [Module ℂ V]
    {W₁ W₂ : Submodule ℂ V} [FiniteDimensional ℂ W₁] [FiniteDimensional ℂ W₂] (e : W₁ = W₂)
    {T₁ T₂ : V →ₗ[ℂ] V} (hT : T₁ = T₂)
    (h₁ : ∀ v ∈ W₁, T₁ v ∈ W₁) (h₂ : ∀ v ∈ W₂, T₂ v ∈ W₂) :
    ArtinL.charpolyRev (T₁.restrict h₁) = ArtinL.charpolyRev (T₂.restrict h₂) := by
  subst e; subst hT; rfl

set_option maxHeartbeats 1600000 in

theorem main (ρ : Γℚ →* GL (Fin n) ℂ)
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField F] [IsGalois ℚ F]
    (ρF : (F ≃ₐ[ℚ] F) →* GL (Fin n) ℂ) (hρ : ρ = ρF.comp (AlgEquiv.restrictNormalHom F))
    {p : ℕ} (hp : p.Prime) (P : Ideal (𝓞 F)) [P.IsMaximal]
    [P.LiesOver (Ideal.span {(p : ℤ)})] :
    ∃ h : ∀ w ∈ Representation.invariants
        ((Deformation.matrixRepresentation ρF).comp (P.inertia (F ≃ₐ[ℚ] F)).subtype),
      Deformation.matrixRepresentation ρF (arithFrobAt ℤ (F ≃ₐ[ℚ] F) P) w ∈
        Representation.invariants
          ((Deformation.matrixRepresentation ρF).comp (P.inertia (F ≃ₐ[ℚ] F)).subtype),
      ArtinL.eulerFactor ρ p =
        ArtinL.charpolyRev
          ((Deformation.matrixRepresentation ρF (arithFrobAt ℤ (F ≃ₐ[ℚ] F) P)).restrict h) := by
  set G := F ≃ₐ[ℚ] F
  set res := AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := ℚbar) F with hres

  obtain ⟨A, σ, hA, hσ⟩ :=
    ValuationSubring.exists_liesOverPrime_isFrobeniusAt_ratAlgClosure ⟨p, hp⟩
  obtain ⟨hst, hEF⟩ := ArtinL.eulerFactorAt_eq_eulerFactor ρ hp A hA σ hσ
  have hE : ArtinL.eulerFactor ρ p =
      ArtinL.charpolyRev ((Deformation.matrixRepresentation ρ σ).restrict hst) := by
    rw [← hEF, ArtinL.eulerFactorAt, dif_pos hst]

  obtain ⟨Q, hQmax, hQfin, hpQ, hle, hmemQ, hI, -, -⟩ :=
    ValuationSubring.exists_ideal_ringOfIntegers_inertia_eq_map_restrictNormalHom F A hp hA
  haveI := hQmax
  haveI := hQfin

  have hρapp : ∀ τ : Γℚ, Deformation.matrixRepresentation ρ τ =
      Deformation.matrixRepresentation ρF (res τ) := by
    intro τ
    rw [Deformation.matrixRepresentation_apply, Deformation.matrixRepresentation_apply, hρ]
    rfl
  have hInv : ArtinL.inertiaInvariants ρ A = Inv ρF (Q.inertia G) := by
    ext v
    rw [ArtinL.inertiaInvariants, ArtinL.invariantsUnder, Representation.mem_invariants, mem_Inv]
    constructor
    · intro h s hs
      rw [← hI, Subgroup.mem_map] at hs
      obtain ⟨τ, hτ, rfl⟩ := hs
      have h1 := h ⟨τ, hτ⟩
      change Deformation.matrixRepresentation ρ τ v = v at h1
      rwa [hρapp] at h1
    · intro h τ
      change Deformation.matrixRepresentation ρ τ v = v
      rw [hρapp]
      exact h _ (hI ▸ Subgroup.mem_map_of_mem res τ.2)

  have hpQ' : ((p : ℕ) : 𝓞 F) ∈ Q := hpQ
  have hcard : Nat.card (ℤ ⧸ Q.under ℤ) = p := card_quotient_under Q hp hpQ'
  have hFrob : IsArithFrobAt ℤ (res σ) Q := by
    intro x
    rw [hcard]
    change (res σ) • x - x ^ p ∈ Q
    rw [hmemQ, ← ValuationSubring.mem_nonunits_iff]
    have hx : algebraMap F ℚbar x ∈ A := (A.valuation_le_one_iff _).1 (hle x)
    obtain ⟨-, hσ'⟩ := (isFrobeniusAt_iff A σ p).1 hσ
    have h1 := hσ' _ hx
    convert h1 using 1
    rw [← AlgEquiv.restrictNormal_commutes σ F]
    push_cast
    rfl

  set φQ := arithFrobAt ℤ G Q with hφQdef
  have hφQ : IsArithFrobAt ℤ φQ Q := IsArithFrobAt.arithFrobAt ℤ G Q
  have hmem : res σ * φQ⁻¹ ∈ Q.inertia G := hFrob.mul_inv_mem_inertia hφQ
  have hQstab : φQ • Q = Q := MulAction.mem_stabilizer_iff.1 hφQ.mem_stabilizer
  have hσQstab : res σ • Q = Q := MulAction.mem_stabilizer_iff.1 hFrob.mem_stabilizer
  have hφQst : ∀ v ∈ Inv ρF (Q.inertia G),
      Deformation.matrixRepresentation ρF φQ v ∈ Inv ρF (Q.inertia G) :=
    stable ρF fun s hs => conj_mem_inertia hQstab hs
  have hσst : ∀ v ∈ Inv ρF (Q.inertia G),
      Deformation.matrixRepresentation ρF (res σ) v ∈ Inv ρF (Q.inertia G) :=
    stable ρF fun s hs => conj_mem_inertia hσQstab hs
  have hE2 : ArtinL.eulerFactor ρ p =
      ArtinL.charpolyRev ((Deformation.matrixRepresentation ρF φQ).restrict hφQst) := by
    rw [hE, ← restrict_eq_of_mul_inv_mem ρF hmem hσst hφQst]
    exact charpolyRev_restrict_congr hInv (hρapp σ) _ _

  have hunderQ : Q.under ℤ = Ideal.span {(p : ℤ)} := under_eq_span Q hp hpQ'
  have hunderP : P.under ℤ = Ideal.span {(p : ℤ)} :=
    (Ideal.LiesOver.over (P := P) (p := Ideal.span {(p : ℤ)})).symm
  obtain ⟨g, hg⟩ :=
    Algebra.IsInvariant.exists_smul_of_under_eq ℤ (𝓞 F) G Q P (hunderQ.trans hunderP.symm)
  subst hg
  have hφP : IsArithFrobAt ℤ (arithFrobAt ℤ G (g • Q)) (g • Q) := IsArithFrobAt.arithFrobAt ℤ G _
  have hcFrob : IsArithFrobAt ℤ (g * φQ * g⁻¹) (g • Q) := hφQ.conj g
  have hmem2 : arithFrobAt ℤ G (g • Q) * (g * φQ * g⁻¹)⁻¹ ∈ (g • Q).inertia G :=
    hφP.mul_inv_mem_inertia hcFrob
  have hPstab : arithFrobAt ℤ G (g • Q) • (g • Q) = g • Q :=
    MulAction.mem_stabilizer_iff.1 hφP.mem_stabilizer
  have hcstab : (g * φQ * g⁻¹) • (g • Q) = g • Q :=
    MulAction.mem_stabilizer_iff.1 hcFrob.mem_stabilizer
  have hφPst : ∀ v ∈ Inv ρF ((g • Q).inertia G),
      Deformation.matrixRepresentation ρF (arithFrobAt ℤ G (g • Q)) v ∈ Inv ρF ((g • Q).inertia G) :=
    stable ρF fun s hs => conj_mem_inertia hPstab hs
  have hcst : ∀ v ∈ Inv ρF ((g • Q).inertia G),
      Deformation.matrixRepresentation ρF (g * φQ * g⁻¹) v ∈ Inv ρF ((g • Q).inertia G) :=
    stable ρF fun s hs => conj_mem_inertia hcstab hs
  have hsub : (g • Q).inertia G = conjSub (Q.inertia G) g := inertia_smul Q g
  have hcst' : ∀ v ∈ Inv ρF (conjSub (Q.inertia G) g),
      Deformation.matrixRepresentation ρF (g * φQ * g⁻¹) v ∈ Inv ρF (conjSub (Q.inertia G) g) := by
    rw [← hsub]; exact hcst
  refine ⟨hφPst, ?_⟩
  rw [hE2, restrict_eq_of_mul_inv_mem ρF hmem2 hφPst hcst,
    charpolyRev_restrict_congr (congrArg (Inv ρF) hsub) rfl hcst hcst',
    charpolyRev_restrict_conj ρF g φQ hφQst hcst']

end Main

end ArtinDictProof
p2m_reactivate "P2MW.S_ArtinL_eulerFactor_eq_charpolyRev_restrict_arithFrobAt.ArtinDictProof"

end
p2m_reactivate "P2MW.S_ArtinL_eulerFactor_eq_charpolyRev_restrict_arithFrobAt.ArtinDictProof"

set_option autoImplicit false

open scoped MatrixGroups
open NumberField

local notation "Γℚ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

theorem solution {n : ℕ} (ρ : Γℚ →* GL (Fin n) ℂ)
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField F] [IsGalois ℚ F]
    (ρF : (F ≃ₐ[ℚ] F) →* GL (Fin n) ℂ) (hρ : ρ = ρF.comp (AlgEquiv.restrictNormalHom F))
    {p : ℕ} (hp : p.Prime) (P : Ideal (𝓞 F)) [P.IsMaximal]
    [P.LiesOver (Ideal.span {(p : ℤ)})] :
    ∃ h : ∀ w ∈ Representation.invariants
        ((Deformation.matrixRepresentation ρF).comp (P.inertia (F ≃ₐ[ℚ] F)).subtype),
      Deformation.matrixRepresentation ρF (arithFrobAt ℤ (F ≃ₐ[ℚ] F) P) w ∈
        Representation.invariants
          ((Deformation.matrixRepresentation ρF).comp (P.inertia (F ≃ₐ[ℚ] F)).subtype),
      ArtinL.eulerFactor ρ p =
        ArtinL.charpolyRev
          ((Deformation.matrixRepresentation ρF (arithFrobAt ℤ (F ≃ₐ[ℚ] F) P)).restrict h) :=
  ArtinDictProof.main ρ F ρF hρ hp P

end S_ArtinL_eulerFactor_eq_charpolyRev_restrict_arithFrobAt
end P2MW
export P2MW.S_ArtinL_eulerFactor_eq_charpolyRev_restrict_arithFrobAt (solution)
