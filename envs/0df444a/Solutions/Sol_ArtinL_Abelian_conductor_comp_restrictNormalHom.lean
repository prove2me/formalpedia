-- Prove2me | solution 1 for ArtinL.Abelian.conductor_comp_restrictNormalHom
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/7c9a1f08-c88d-5a60-b1a7-1227f160fe53

import Mathlib
import Definitions.Def_ArtinL_Abelian
import Theorems.Thm_ArtinL_Abelian_swanConductor_comp_restrictNormalHom
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ArtinL_Abelian_conductor_comp_restrictNormalHom
p2m_attr_erase "instance" "ValuationSubring.lowerRamificationGroup_normal IsLocalRing.lowerRamificationGroup_normal FixedPoints.isLocalRing_subring FixedPoints.isLocalHom_subring_subtype"
p2m_attr_erase "simp" "Ideal.inertia_top ValuationSubring.mem_lowerRamificationGroup IsLocalRing.pointwise_smul_maximalIdeal IsLocalRing.pointwise_smul_maximalIdeal_pow IsLocalRing.mem_lowerRamificationGroup IsLocalRing.upperRamificationGroup_zero IsLocalRing.upperRamificationIndex_zero IsLocalRing.herbrandPhi_zero ValuationSubring.herbrandPhi_zero IsLocalRing.mem_upperRamificationGroup IsLocalRing.lowerRamificationGroup_subgroupOf IsLocalRing.lowerRamificationGroup_map_subtype ValuationSubring.lowerRamificationGroup_map_subtype ValuationSubring.lowerRamificationGroup_subgroupOf"

set_option autoImplicit false

open NumberField NumberField.InfinitePlace IsDedekindDomain LanglandsTunnell.P2.Artin

universe u v w

noncomputable section

namespace ArtinInflation

open scoped Pointwise

section Restriction

variable {K : Type u} {L : Type v} {M : Type w} [Field K] [Field L] [Field M]
  [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M] [Normal K L]

theorem algebraMap_restrictNormalHom_apply (σ : M ≃ₐ[K] M) (y : L) :
    algebraMap L M (AlgEquiv.restrictNormalHom (K₁ := M) L σ y) = σ (algebraMap L M y) :=
  AlgEquiv.restrictNormal_commutes σ L y

theorem algebraMap_restrictNormalHom_smul (σ : M ≃ₐ[K] M) (y : 𝓞 L) :
    algebraMap (𝓞 L) (𝓞 M) (AlgEquiv.restrictNormalHom (K₁ := M) L σ • y) =
      σ • algebraMap (𝓞 L) (𝓞 M) y :=
  RingOfIntegers.ext (algebraMap_restrictNormalHom_apply σ (y : L))

def liftOfRestrictEqOne (σ : M ≃ₐ[K] M) (h : AlgEquiv.restrictNormalHom (K₁ := M) L σ = 1) :
    M ≃ₐ[L] M :=
  { σ.toRingEquiv with
    commutes' := fun y => by
      have h' := algebraMap_restrictNormalHom_apply (K := K) σ y
      rw [h, AlgEquiv.one_apply] at h'
      exact h'.symm }

@[scoped simp] theorem liftOfRestrictEqOne_apply (σ : M ≃ₐ[K] M)
    (h : AlgEquiv.restrictNormalHom (K₁ := M) L σ = 1) (x : M) :
    liftOfRestrictEqOne σ h x = σ x := rfl

scoped instance isScalarTower_ringOfIntegers : IsScalarTower (𝓞 K) (𝓞 L) (𝓞 M) :=
  IsScalarTower.of_algebraMap_eq fun x => RingOfIntegers.ext
    (IsScalarTower.algebraMap_apply K L M (x : K))

end Restriction

section Inertia

attribute [local instance] Ideal.Quotient.field

variable {K : Type u} {L : Type v} {M : Type w} [Field K] [NumberField K] [Field L] [NumberField L]
  [Field M] [NumberField M] [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M]
  [IsGalois K L] [IsGalois K M]

omit [NumberField K] [NumberField L] [NumberField M] [IsGalois K M] in

theorem restrictNormalHom_mem_inertia_under {P : Ideal (𝓞 M)} {σ : M ≃ₐ[K] M}
    (hσ : σ ∈ P.inertia (M ≃ₐ[K] M)) :
    AlgEquiv.restrictNormalHom (K₁ := M) L σ ∈ (P.under (𝓞 L)).inertia (L ≃ₐ[K] L) := by
  intro y
  change algebraMap (𝓞 L) (𝓞 M) (AlgEquiv.restrictNormalHom (K₁ := M) L σ • y - y) ∈ P
  rw [map_sub, algebraMap_restrictNormalHom_smul]
  exact hσ _

omit [NumberField K] [NumberField L] [NumberField M] [IsGalois K M] in
theorem map_inertia_le (P : Ideal (𝓞 M)) :
    (P.inertia (M ≃ₐ[K] M)).map (AlgEquiv.restrictNormalHom (K₁ := M) L) ≤
      (P.under (𝓞 L)).inertia (L ≃ₐ[K] L) := by
  rintro _ ⟨σ, hσ, rfl⟩
  exact restrictNormalHom_mem_inertia_under hσ

theorem map_inertia_eq (P : Ideal (𝓞 M)) [P.IsMaximal] :
    (P.inertia (M ≃ₐ[K] M)).map (AlgEquiv.restrictNormalHom (K₁ := M) L) =
      (P.under (𝓞 L)).inertia (L ≃ₐ[K] L) := by
  classical
  haveI : IsGalois L M := IsGalois.tower_top_of_isGalois K L M

  set G := M ≃ₐ[K] M
  set res : (M ≃ₐ[K] M) →* (L ≃ₐ[K] L) := AlgEquiv.restrictNormalHom (K₁ := M) L with hres
  set Q' : Ideal (𝓞 L) := P.under (𝓞 L) with hQ'
  set p : Ideal (𝓞 K) := P.under (𝓞 K) with hp
  have hPbot : P ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField inferInstance
    (RingOfIntegers.not_isField M)
  have hpbot : p ≠ ⊥ := Ideal.under_ne_bot (A := 𝓞 K) hPbot
  have hQ'bot : Q' ≠ ⊥ := Ideal.under_ne_bot (A := 𝓞 L) hPbot
  haveI : Q'.LiesOver p := ⟨(Ideal.under_under (A := 𝓞 K) (B := 𝓞 L) P).symm⟩
  haveI hpmax : p.IsMaximal := Ideal.IsMaximal.under (𝓞 K) P
  haveI : Finite (𝓞 K ⧸ p) := Ideal.finiteQuotientOfFreeOfNeBot p hpbot
  haveI : Finite (𝓞 L ⧸ Q') := Ideal.finiteQuotientOfFreeOfNeBot Q' hQ'bot

  have hG : Nat.card (P.inertia (M ≃ₐ[K] M)) = Ideal.ramificationIdx' p P := by
    rw [Ideal.card_inertia_eq_ramificationIdxIn p P,
      Ideal.ramificationIdxIn_eq_ramificationIdx p P (M ≃ₐ[K] M), Ideal.ramificationIdx'_eq_ramificationIdx _ _ hpbot]
  have hH : Nat.card (Q'.inertia (L ≃ₐ[K] L)) = Ideal.ramificationIdx' p Q' := by
    rw [Ideal.card_inertia_eq_ramificationIdxIn p Q',
      Ideal.ramificationIdxIn_eq_ramificationIdx p Q' (L ≃ₐ[K] L), Ideal.ramificationIdx'_eq_ramificationIdx _ _ hpbot]
  have hN : Nat.card (P.inertia (M ≃ₐ[L] M)) = Ideal.ramificationIdx' Q' P := by
    rw [Ideal.card_inertia_eq_ramificationIdxIn Q' P,
      Ideal.ramificationIdxIn_eq_ramificationIdx Q' P (M ≃ₐ[L] M), Ideal.ramificationIdx'_eq_ramificationIdx _ _ hQ'bot]
  have htower : Ideal.ramificationIdx' p P = Ideal.ramificationIdx' p Q' * Ideal.ramificationIdx' Q' P :=
    Ideal.ramificationIdx_algebra_tower' p Q' P
  have hePQ' : Ideal.ramificationIdx' Q' P ≠ 0 :=
    Ideal.IsDedekindDomain.ramificationIdx_ne_zero_of_liesOver P hQ'bot

  set f : ↥(P.inertia (M ≃ₐ[K] M)) →* (L ≃ₐ[K] L) := res.comp (P.inertia (M ≃ₐ[K] M)).subtype
    with hf
  have hrange : f.range = (P.inertia (M ≃ₐ[K] M)).map res := by
    rw [hf, MonoidHom.range_comp, Subgroup.range_subtype]

  have hker : Nat.card f.ker ≤ Nat.card (P.inertia (M ≃ₐ[L] M)) := by
    haveI : Finite (P.inertia (M ≃ₐ[L] M)) := inferInstance
    refine Nat.card_le_card_of_injective
      (fun σ => ⟨liftOfRestrictEqOne (σ.1 : M ≃ₐ[K] M) (by
        have h := σ.2
        rw [MonoidHom.mem_ker] at h
        exact h), fun x => ?_⟩) ?_
    ·
      have h := σ.1.2 x
      exact h
    · intro σ τ h
      have h' := congrArg (fun ρ : ↥(P.inertia (M ≃ₐ[L] M)) => ((ρ : M ≃ₐ[L] M) : M → M)) h
      apply Subtype.ext
      apply Subtype.ext
      apply AlgEquiv.ext
      intro x
      exact congrFun h' x

  have hcard : Nat.card f.ker * Nat.card f.range = Nat.card (P.inertia (M ≃ₐ[K] M)) := by
    rw [← Subgroup.index_ker, Subgroup.card_mul_index]
  have hle : f.range ≤ Q'.inertia (L ≃ₐ[K] L) := hrange ▸ map_inertia_le P
  haveI : Finite (Q'.inertia (L ≃ₐ[K] L)) := inferInstance
  have hge : Nat.card (Q'.inertia (L ≃ₐ[K] L)) ≤ Nat.card f.range := by
    rw [hH]
    have h1 : Ideal.ramificationIdx' p Q' * Ideal.ramificationIdx' Q' P ≤
        Nat.card f.range * Ideal.ramificationIdx' Q' P := by
      calc Ideal.ramificationIdx' p Q' * Ideal.ramificationIdx' Q' P
          = Nat.card f.ker * Nat.card f.range := by rw [← htower, ← hG, hcard]
        _ ≤ Nat.card (P.inertia (M ≃ₐ[L] M)) * Nat.card f.range :=
            Nat.mul_le_mul_right _ hker
        _ = Nat.card f.range * Ideal.ramificationIdx' Q' P := by rw [hN, mul_comm]
    exact Nat.le_of_mul_le_mul_right h1 (Nat.pos_of_ne_zero hePQ')
  rw [← hrange]
  exact Subgroup.eq_of_le_of_card_ge hle hge

theorem mem_inertia_smul_iff {G R : Type*} [Group G] [CommRing R] [MulSemiringAction G R]
    (Q : Ideal R) (g τ : G) : τ ∈ (g • Q).inertia G ↔ g⁻¹ * τ * g ∈ Q.inertia G := by
  constructor
  · intro h y
    have h1 : τ • g • y - g • y ∈ g • Q := h (g • y)
    rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem, smul_sub, inv_smul_smul] at h1
    show (g⁻¹ * τ * g) • y - y ∈ Q
    rwa [mul_smul, mul_smul]
  · intro h x
    have h1 : (g⁻¹ * τ * g) • g⁻¹ • x - g⁻¹ • x ∈ Q := h (g⁻¹ • x)
    rw [mul_smul, mul_smul, smul_inv_smul] at h1
    show τ • x - x ∈ g • Q
    rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem, smul_sub]
    exact h1

theorem forall_inertia_smul_iff {G R : Type*} [Group G] [CommRing R] [MulSemiringAction G R]
    (Q : Ideal R) (g : G) (φ : G →* ℂˣ) :
    (∀ τ ∈ (g • Q).inertia G, φ τ = 1) ↔ (∀ τ ∈ Q.inertia G, φ τ = 1) := by
  constructor
  · intro h τ hτ
    have h1 := h (g * τ * g⁻¹) (by
      rw [mem_inertia_smul_iff]
      simpa [mul_assoc] using hτ)
    rwa [map_mul, map_mul, map_inv, mul_right_comm, mul_inv_cancel, one_mul] at h1
  · intro h τ hτ
    have h1 := h _ ((mem_inertia_smul_iff Q g τ).1 hτ)
    rwa [map_mul, map_mul, map_inv, mul_right_comm, inv_mul_cancel, one_mul] at h1

end Inertia

section Finite

attribute [local instance] Ideal.Quotient.field

variable (K : Type u) (L : Type v) (M : Type w) [Field K] [NumberField K] [Field L] [NumberField L]
  [Field M] [NumberField M] [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M]
  [IsGalois K L] [IsGalois K M]

omit [NumberField M] [IsGalois K M] in

theorem exists_smul_primeAbove_eq (v : HeightOneSpectrum (𝓞 K)) :
    ∃ g : L ≃ₐ[K] L, g • primeAbove K L v = (primeAbove K M v).under (𝓞 L) := by
  haveI : ((primeAbove K M v).under (𝓞 L)).LiesOver v.asIdeal :=
    ⟨by rw [Ideal.under_under, ← Ideal.over_def (primeAbove K M v) v.asIdeal]⟩
  exact Ideal.exists_smul_eq_of_isGaloisGroup v.asIdeal (primeAbove K L v)
    ((primeAbove K M v).under (𝓞 L)) (L ≃ₐ[K] L)

theorem isUnramifiedAt_comp_iff (ψ : (L ≃ₐ[K] L) →* ℂˣ) (v : HeightOneSpectrum (𝓞 K)) :
    ArtinL.Abelian.IsUnramifiedAt (ψ.comp (AlgEquiv.restrictNormalHom (K₁ := M) L)) v ↔
      ArtinL.Abelian.IsUnramifiedAt ψ v := by
  obtain ⟨g, hg⟩ := exists_smul_primeAbove_eq K L M v
  unfold ArtinL.Abelian.IsUnramifiedAt ArtinL.Abelian.inertiaGroup
  rw [← forall_inertia_smul_iff (primeAbove K L v) g ψ, hg, ← map_inertia_eq (K := K) (L := L)]
  constructor
  · rintro h _ ⟨σ, hσ, rfl⟩
    exact h σ hσ
  · intro h σ hσ
    exact h _ ⟨σ, hσ, rfl⟩

theorem isArithFrobAt_restrictNormalHom {P : Ideal (𝓞 M)} {σ : M ≃ₐ[K] M}
    (hσ : IsArithFrobAt (𝓞 K) σ P) :
    IsArithFrobAt (𝓞 K) (AlgEquiv.restrictNormalHom (K₁ := M) L σ) (P.under (𝓞 L)) := by
  intro y
  rw [Ideal.under_under]
  change algebraMap (𝓞 L) (𝓞 M)
    (AlgEquiv.restrictNormalHom (K₁ := M) L σ • y - y ^ Nat.card (𝓞 K ⧸ Ideal.under (𝓞 K) P)) ∈ P
  rw [map_sub, map_pow, algebraMap_restrictNormalHom_smul]
  exact hσ _

theorem localValue_comp (ψ : (L ≃ₐ[K] L) →* ℂˣ) (v : HeightOneSpectrum (𝓞 K)) :
    ArtinL.Abelian.localValue (ψ.comp (AlgEquiv.restrictNormalHom (K₁ := M) L)) v =
      ArtinL.Abelian.localValue ψ v := by
  unfold ArtinL.Abelian.localValue
  rw [isUnramifiedAt_comp_iff]
  split_ifs with hun
  ·
    obtain ⟨g, hg⟩ := exists_smul_primeAbove_eq K L M v
    set res : (M ≃ₐ[K] M) →* (L ≃ₐ[K] L) := AlgEquiv.restrictNormalHom (K₁ := M) L with hres
    have hσ : IsArithFrobAt (𝓞 K) (res (artinFrob K M v)) ((primeAbove K M v).under (𝓞 L)) :=
      isArithFrobAt_restrictNormalHom K L M (isArithFrobAt_artinFrob K M v)
    have hσ' : IsArithFrobAt (𝓞 K) (g⁻¹ * res (artinFrob K M v) * g⁻¹⁻¹)
        (g⁻¹ • (primeAbove K M v).under (𝓞 L)) := hσ.conj g⁻¹
    rw [inv_inv, ← hg, inv_smul_smul] at hσ'
    have hτ : IsArithFrobAt (𝓞 K) (artinFrob K L v) (primeAbove K L v) :=
      isArithFrobAt_artinFrob K L v
    have hmem := hσ'.mul_inv_mem_inertia hτ
    have h1 : ψ (g⁻¹ * res (artinFrob K M v) * g * (artinFrob K L v)⁻¹) = 1 := hun _ hmem
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, mul_right_comm (ψ g)⁻¹, inv_mul_cancel,
      one_mul, mul_inv_eq_one] at h1
    rw [MonoidHom.comp_apply, h1]
  · rfl

end Finite

section Archimedean

variable (K : Type u) (L : Type v) (M : Type w) [Field K] [NumberField K] [Field L] [NumberField L]
  [Field M] [NumberField M] [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M]
  [IsGalois K L] [IsGalois K M]

omit [NumberField K] [NumberField L] [NumberField M] [IsGalois K M] in

theorem restrictNormalHom_mem_stabilizer {w' : InfinitePlace M} {σ : M ≃ₐ[K] M}
    (hσ : σ ∈ MulAction.stabilizer (M ≃ₐ[K] M) w') :
    AlgEquiv.restrictNormalHom (K₁ := M) L σ ∈
      MulAction.stabilizer (L ≃ₐ[K] L) (w'.comap (algebraMap L M)) := by
  rw [MulAction.mem_stabilizer_iff] at hσ ⊢
  rw [smul_eq_comap, ← comap_comp]
  have hcomp : (algebraMap L M).comp
      ((AlgEquiv.restrictNormalHom (K₁ := M) L σ).symm : L →+* L) =
        ((σ.symm : M ≃ₐ[K] M) : M →+* M).comp (algebraMap L M) := by
    ext y
    simp only [RingHom.comp_apply, RingHom.coe_coe]
    have h := algebraMap_restrictNormalHom_apply (K := K) (L := L) σ⁻¹ y
    rw [map_inv] at h
    exact h
  rw [hcomp, comap_comp, ← smul_eq_comap, hσ]

omit [NumberField K] in

theorem isPlusAt_comp_iff (ψ : (L ≃ₐ[K] L) →* ℂˣ) (w : InfinitePlace K) :
    ArtinL.Abelian.IsPlusAt (ψ.comp (AlgEquiv.restrictNormalHom (K₁ := M) L)) w ↔
      ArtinL.Abelian.IsPlusAt ψ w := by
  constructor
  · intro h w'' hw'' τ hτ

    by_cases hτ1 : τ = 1
    · rw [hτ1, map_one]

    have hconj : ComplexEmbedding.IsConj (embedding w'') τ := by
      have := (mem_stabilizer_mk_iff (k := K) (embedding w'') τ).1 (by rwa [mk_embedding])
      exact this.resolve_left hτ1

    set φ' : M →+* ℂ := ComplexEmbedding.lift M (embedding w'') with hφ'
    have hφ'L : φ'.comp (algebraMap L M) = embedding w'' :=
      ComplexEmbedding.lift_comp_algebraMap (k := L) M (embedding w'')

    have hreal : (ComplexEmbedding.conjugate φ').comp (algebraMap K M) = φ'.comp (algebraMap K M) := by
      ext x
      have hx : algebraMap K M x = algebraMap L M (algebraMap K L x) := IsScalarTower.algebraMap_apply K L M x
      simp only [RingHom.comp_apply, hx]
      have h1 : φ' (algebraMap L M (algebraMap K L x)) = embedding w'' (algebraMap K L x) := by
        rw [← hφ'L]; rfl
      rw [ComplexEmbedding.conjugate_coe_eq, h1]
      have h2 := RingHom.congr_fun hconj (algebraMap K L x)
      rw [ComplexEmbedding.conjugate_coe_eq, RingHom.comp_apply] at h2
      rw [h2]
      simp
    obtain ⟨σ, hσ⟩ := NumberField.ComplexEmbedding.exists_comp_symm_eq_of_comp_eq _ _ hreal

    have hσconj : ComplexEmbedding.IsConj φ' σ := by
      unfold ComplexEmbedding.IsConj
      refine RingHom.ext fun x => ?_
      have h1 := RingHom.congr_fun hσ (σ x)
      simp only [RingHom.comp_apply, RingHom.coe_coe, AlgEquiv.symm_apply_apply] at h1
      rw [RingHom.comp_apply, RingHom.coe_coe, ← h1]

    have hres : AlgEquiv.restrictNormalHom (K₁ := M) L σ = τ := by
      refine ComplexEmbedding.IsConj.ext ?_ hconj
      ext y
      have h1 := RingHom.congr_fun hσconj (algebraMap L M y)
      rw [ComplexEmbedding.conjugate_coe_eq, RingHom.comp_apply] at h1
      rw [ComplexEmbedding.conjugate_coe_eq, RingHom.comp_apply, ← hφ'L, RingHom.comp_apply,
        RingHom.comp_apply, h1]
      change φ' (σ (algebraMap L M y)) = φ' (algebraMap L M (AlgEquiv.restrictNormalHom L σ y))
      rw [algebraMap_restrictNormalHom_apply]

    have hσstab : σ ∈ MulAction.stabilizer (M ≃ₐ[K] M) (mk φ') :=
      (mem_stabilizer_mk_iff φ' σ).2 (Or.inr hσconj)
    have hw' : (mk φ').comap (algebraMap K M) = w := by
      rw [IsScalarTower.algebraMap_eq K L M, comap_comp, comap_mk, hφ'L, mk_embedding, hw'']
    have := h (mk φ') hw' σ hσstab
    rwa [MonoidHom.comp_apply, hres] at this
  · intro h w' hw' σ hσ
    rw [MonoidHom.comp_apply]
    refine h (w'.comap (algebraMap L M)) ?_ _ (restrictNormalHom_mem_stabilizer K L M hσ)
    rw [← comap_comp, ← IsScalarTower.algebraMap_eq K L M, hw']

end Archimedean

section Conductor

variable (K : Type u) (L : Type v) (M : Type w) [Field K] [NumberField K] [Field L] [NumberField L]
  [Field M] [NumberField M] [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M]
  [IsGalois K L] [IsGalois K M]

theorem conductorExponent_comp (ψ : (L ≃ₐ[K] L) →* ℂˣ) (v : HeightOneSpectrum (𝓞 K)) :
    ArtinL.Abelian.conductorExponent (ψ.comp (AlgEquiv.restrictNormalHom (K₁ := M) L)) v =
      ArtinL.Abelian.conductorExponent ψ v := by
  unfold ArtinL.Abelian.conductorExponent
  rw [ArtinL.Abelian.swanConductor_comp_restrictNormalHom K L M ψ v]
  by_cases h : ArtinL.Abelian.IsUnramifiedAt ψ v
  · rw [if_pos h, if_pos ((isUnramifiedAt_comp_iff K L M ψ v).2 h)]
  · rw [if_neg h, if_neg (mt (isUnramifiedAt_comp_iff K L M ψ v).1 h)]

theorem conductor_comp (ψ : (L ≃ₐ[K] L) →* ℂˣ) :
    ArtinL.Abelian.conductor (ψ.comp (AlgEquiv.restrictNormalHom (K₁ := M) L)) =
      ArtinL.Abelian.conductor ψ := by
  unfold ArtinL.Abelian.conductor
  exact finprod_congr fun v => by rw [conductorExponent_comp]

end Conductor

end ArtinInflation
p2m_reactivate "P2MW.S_ArtinL_Abelian_conductor_comp_restrictNormalHom.ArtinInflation"

end
p2m_reactivate "P2MW.S_ArtinL_Abelian_conductor_comp_restrictNormalHom.ArtinInflation"

theorem solution
    (K : Type u) (L : Type v) (M : Type w) [Field K] [NumberField K] [Field L] [NumberField L]
    [Field M] [NumberField M] [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M]
    [IsGalois K L] [IsGalois K M] (ψ : (L ≃ₐ[K] L) →* ℂˣ) :
    ArtinL.Abelian.conductor (ψ.comp (AlgEquiv.restrictNormalHom (K₁ := M) L)) =
        ArtinL.Abelian.conductor ψ ∧
      (∀ v : HeightOneSpectrum (𝓞 K),
        ArtinL.Abelian.localValue (ψ.comp (AlgEquiv.restrictNormalHom (K₁ := M) L)) v =
          ArtinL.Abelian.localValue ψ v) ∧
      (∀ w : InfinitePlace K,
        ArtinL.Abelian.IsPlusAt (ψ.comp (AlgEquiv.restrictNormalHom (K₁ := M) L)) w ↔
          ArtinL.Abelian.IsPlusAt ψ w) :=
  ⟨ArtinInflation.conductor_comp K L M ψ, ArtinInflation.localValue_comp K L M ψ,
    ArtinInflation.isPlusAt_comp_iff K L M ψ⟩

end S_ArtinL_Abelian_conductor_comp_restrictNormalHom
end P2MW
export P2MW.S_ArtinL_Abelian_conductor_comp_restrictNormalHom (solution)
