-- Prove2me | solution 1 for AdicCompletion.isRegularLocalRing_localization_atPrime_of_mem_of_not_isMaximal_of_tame
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/384ca34a-a131-549a-95f7-16ff596c9fe1

import Mathlib
import Definitions.Def_AdicCompletionGaloisAction
import Definitions.Def_AdicCompletionTensorRing
import Theorems.Thm_AdicCompletion_isField_localization_atPrime_of_not_isMaximal_of_isSeparable
import Theorems.Thm_Algebra_IsInvariant_isSeparable_of_isFractionRing_quotient_of_lt_of_isUnit_card_inertia
import Theorems.Thm_AdicCompletion_mem_nonZeroDivisors_algebraMap_of_mem_nonZeroDivisors_of_liesOver
import Theorems.Thm_IsRegularLocalRing_isDomain_and_isIntegrallyClosed_adicCompletion_of_ringKrullDim_eq_two
import Theorems.Thm_AdicCompletion_isNoetherianRing_and_exists_isLocalRing_maximalIdeal_eq_map_of_isMaximal
import Theorems.Thm_IsIntegrallyClosed_isRegularLocalRing_localization_atPrime_of_ringKrullDim_eq_one
import Theorems.Thm_IsRegularLocalRing_of_isRegularLocalRing_quotient_span_singleton_of_mem_nonZeroDivisors
import Theorems.Thm_IsRegularLocalRing_isDomain
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AdicCompletion_isRegularLocalRing_localization_atPrime_of_mem_of_not_isMaximal_of_tame
p2m_attr_erase "instance" "AdicCompletion.instIsLocalRingMaximalIdeal"

set_option autoImplicit false

open IsLocalRing
open scoped Pointwise TensorProduct
open scoped AdicCompletion.GaloisAction

namespace BDescN4Kit

theorem exists_ringEquiv_localization_quotient_map
    {C : Type} [CommRing C] [IsNoetherianRing C] (𝔫 𝔮 : Ideal C)
    (𝔭 : Ideal (AdicCompletion 𝔫 C)) [𝔭.IsPrime]
    (h𝔮𝔭 : 𝔮.map (algebraMap C (AdicCompletion 𝔫 C)) ≤ 𝔭) :
    ∃ (𝔓 : Ideal (AdicCompletion (𝔫.map (algebraMap C (C ⧸ 𝔮))) (C ⧸ 𝔮))) (_ : 𝔓.IsPrime),
      (𝔓.IsMaximal → 𝔭.IsMaximal) ∧
      Nonempty ((Localization.AtPrime 𝔭 ⧸ 𝔮.map (algebraMap C (Localization.AtPrime 𝔭))) ≃+*
        Localization.AtPrime 𝔓) := by
  classical
  set I : Ideal (AdicCompletion 𝔫 C) := 𝔮.map (algebraMap C (AdicCompletion 𝔫 C)) with hI

  obtain ⟨e, -⟩ : ∃ _ : (AdicCompletion 𝔫 C ⧸ I) ≃+* AdicCompletion (𝔫.map (algebraMap C (C ⧸ 𝔮))) (C ⧸ 𝔮), True :=
    ⟨(Algebra.TensorProduct.quotIdealMapEquivQuotTensor (AdicCompletion 𝔫 C) 𝔮).toRingEquiv.trans
      ((Algebra.TensorProduct.comm C (C ⧸ 𝔮) (AdicCompletion 𝔫 C)).toRingEquiv.trans
        (AdicCompletion.tensorRingEquiv (C ⧸ 𝔮) 𝔫).toRingEquiv), trivial⟩

  have hmk : Function.Surjective (Ideal.Quotient.mk I) := Ideal.Quotient.mk_surjective
  set 𝔭bar : Ideal (AdicCompletion 𝔫 C ⧸ I) := 𝔭.map (Ideal.Quotient.mk I) with h𝔭bar
  have hker : RingHom.ker (Ideal.Quotient.mk I) ≤ 𝔭 := by rw [Ideal.mk_ker]; exact h𝔮𝔭
  haveI h𝔭barp : 𝔭bar.IsPrime := Ideal.map_isPrime_of_surjective hmk hker
  have hmem : ∀ x : AdicCompletion 𝔫 C, Ideal.Quotient.mk I x ∈ 𝔭bar ↔ x ∈ 𝔭 := fun x =>
    Ideal.mem_quotient_iff_mem h𝔮𝔭
  set 𝔓 : Ideal (AdicCompletion (𝔫.map (algebraMap C (C ⧸ 𝔮))) (C ⧸ 𝔮)) := 𝔭bar.comap e.symm.toRingHom with h𝔓
  haveI h𝔓p : 𝔓.IsPrime := Ideal.IsPrime.comap _
  refine ⟨𝔓, h𝔓p, ?_, ?_⟩
  · intro h𝔓m

    have h1 : 𝔭bar = 𝔓.comap e.toRingHom := by
      ext x
      simp only [h𝔓, Ideal.mem_comap, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
        RingEquiv.symm_apply_apply]
    have h2 : 𝔭bar.IsMaximal := by
      rw [h1]; exact Ideal.comap_isMaximal_of_surjective _ e.surjective
    have h3 : 𝔭 = 𝔭bar.comap (Ideal.Quotient.mk I) := by
      ext x; rw [Ideal.mem_comap, hmem]
    rw [h3]; exact Ideal.comap_isMaximal_of_surjective _ hmk
  ·
    haveI : IsLocalization (Algebra.algebraMapSubmonoid (AdicCompletion 𝔫 C ⧸ I) 𝔭.primeCompl)
        (Localization.AtPrime 𝔭 ⧸ I.map (algebraMap (AdicCompletion 𝔫 C) (Localization.AtPrime 𝔭))) :=
      inferInstance
    have H : (Algebra.algebraMapSubmonoid (AdicCompletion 𝔫 C ⧸ I) 𝔭.primeCompl).map e.toMonoidHom =
        𝔓.primeCompl := by
      ext y
      constructor
      · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
        intro hy
        apply hx
        have : e.symm (e (Ideal.Quotient.mk I x)) ∈ 𝔭bar := by
          have hy' : e.symm.toRingHom (e.toMonoidHom (Ideal.Quotient.mk I x)) ∈ 𝔭bar := hy
          exact hy'
        rw [RingEquiv.symm_apply_apply, hmem] at this
        exact this
      · intro hy
        obtain ⟨x, hx⟩ := hmk (e.symm y)
        refine ⟨Ideal.Quotient.mk I x, ⟨x, ?_, rfl⟩, ?_⟩
        · intro hx𝔭
          apply hy
          have : e.symm y ∈ 𝔭bar := by rw [← hx, hmem]; exact hx𝔭
          simp only [h𝔓, Ideal.mem_comap, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom] at this ⊢
          exact this
        · show e (Ideal.Quotient.mk I x) = y
          rw [hx, RingEquiv.apply_symm_apply]
    let f := IsLocalization.ringEquivOfRingEquiv
      (M := Algebra.algebraMapSubmonoid (AdicCompletion 𝔫 C ⧸ I) 𝔭.primeCompl) (T := 𝔓.primeCompl)
      (Localization.AtPrime 𝔭 ⧸ I.map (algebraMap (AdicCompletion 𝔫 C) (Localization.AtPrime 𝔭)))
      (Localization.AtPrime 𝔓) e H
    have hIeq : I.map (algebraMap (AdicCompletion 𝔫 C) (Localization.AtPrime 𝔭)) =
        𝔮.map (algebraMap C (Localization.AtPrime 𝔭)) := by
      rw [hI, Ideal.map_map, ← IsScalarTower.algebraMap_eq]
    exact ⟨(Ideal.quotEquivOfEq hIeq.symm).trans f⟩

end BDescN4Kit

namespace BDescN4Kit2

theorem exists_map_eq_span_singleton_of_height_eq_one
    {C : Type} [CommRing C] [IsDomain C] [IsNoetherianRing C] [IsIntegrallyClosed C]
    (𝔫 : Ideal C) (𝔮 : Ideal C) [𝔮.IsPrime] (hht : 𝔮.height = 1)
    (𝔭 : Ideal (AdicCompletion 𝔫 C)) [𝔭.IsPrime] (h𝔮 : 𝔭.comap (algebraMap C (AdicCompletion 𝔫 C)) = 𝔮)
    (t : C) (ht𝔮 : t ∈ 𝔮) (htNZD : algebraMap C (AdicCompletion 𝔫 C) t ∈ nonZeroDivisors (AdicCompletion 𝔫 C)) :
    ∃ π : Localization.AtPrime 𝔭,
      𝔮.map (algebraMap C (Localization.AtPrime 𝔭)) = Ideal.span {π} ∧
      π ∈ maximalIdeal (Localization.AtPrime 𝔭) ∧ π ∈ nonZeroDivisors (Localization.AtPrime 𝔭) := by
  classical

  have hdim : ringKrullDim (Localization.AtPrime 𝔮) = 1 := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height 𝔮 (Localization.AtPrime 𝔮), hht]; rfl
  have hreg : IsRegularLocalRing (Localization.AtPrime 𝔮) :=
    IsIntegrallyClosed.isRegularLocalRing_localization_atPrime_of_ringKrullDim_eq_one 𝔮 hdim
  have hsf : (maximalIdeal (Localization.AtPrime 𝔮)).spanFinrank = 1 := by
    have h := hreg.spanFinrank_maximalIdeal
    rw [hdim] at h
    exact_mod_cast h
  obtain ⟨sgen, hcard, hspan⟩ := Submodule.FG.exists_span_finset_card_eq_spanFinrank
    (IsNoetherian.noetherian (maximalIdeal (Localization.AtPrime 𝔮)))
  rw [hsf] at hcard
  obtain ⟨π', hπ'⟩ := Finset.card_eq_one.mp hcard
  have hmax : maximalIdeal (Localization.AtPrime 𝔮) = Ideal.span {π'} := by
    rw [← hspan, hπ', Finset.coe_singleton]

  have hunits : ∀ y : 𝔮.primeCompl,
      IsUnit (((algebraMap (AdicCompletion 𝔫 C) (Localization.AtPrime 𝔭)).comp
        (algebraMap C (AdicCompletion 𝔫 C))) y) := by
    rintro ⟨y, hy⟩
    have hy' : algebraMap C (AdicCompletion 𝔫 C) y ∈ 𝔭.primeCompl := by
      show algebraMap C (AdicCompletion 𝔫 C) y ∉ 𝔭
      rw [← Ideal.mem_comap, h𝔮]; exact hy
    exact IsLocalization.map_units (Localization.AtPrime 𝔭) ⟨_, hy'⟩
  letI algQR : Algebra (Localization.AtPrime 𝔮) (Localization.AtPrime 𝔭) :=
    (IsLocalization.lift (M := 𝔮.primeCompl) (S := Localization.AtPrime 𝔮) hunits).toAlgebra
  haveI : IsScalarTower C (Localization.AtPrime 𝔮) (Localization.AtPrime 𝔭) :=
    IsScalarTower.of_algebraMap_eq (fun c => by
      show algebraMap C (Localization.AtPrime 𝔭) c =
        IsLocalization.lift (M := 𝔮.primeCompl) (S := Localization.AtPrime 𝔮) hunits (algebraMap C _ c)
      rw [IsLocalization.lift_eq, RingHom.comp_apply, ← IsScalarTower.algebraMap_apply])
  set π : Localization.AtPrime 𝔭 := algebraMap (Localization.AtPrime 𝔮) (Localization.AtPrime 𝔭) π' with hπ
  have hmapq : 𝔮.map (algebraMap C (Localization.AtPrime 𝔭)) = Ideal.span {π} := by
    rw [IsScalarTower.algebraMap_eq C (Localization.AtPrime 𝔮) (Localization.AtPrime 𝔭), ← Ideal.map_map,
      Localization.AtPrime.map_eq_maximalIdeal, hmax, Ideal.map_span, Set.image_singleton]
  refine ⟨π, hmapq, ?_, ?_⟩
  · have hmem : π ∈ 𝔮.map (algebraMap C (Localization.AtPrime 𝔭)) := by
      rw [hmapq]; exact Ideal.mem_span_singleton_self π
    have hle : 𝔮.map (algebraMap C (Localization.AtPrime 𝔭)) ≤ maximalIdeal (Localization.AtPrime 𝔭) := by
      rw [IsScalarTower.algebraMap_eq C (AdicCompletion 𝔫 C) (Localization.AtPrime 𝔭), ← Ideal.map_map,
        ← Localization.AtPrime.map_eq_maximalIdeal]
      refine Ideal.map_mono ?_
      rw [← h𝔮]; exact Ideal.map_comap_le
    exact hle hmem
  · have ht' : algebraMap C (Localization.AtPrime 𝔮) t ∈ maximalIdeal (Localization.AtPrime 𝔮) := by
      rw [← Localization.AtPrime.map_eq_maximalIdeal]; exact Ideal.mem_map_of_mem _ ht𝔮
    rw [hmax, Ideal.mem_span_singleton'] at ht'
    obtain ⟨a, ha⟩ := ht'
    have htR : algebraMap C (Localization.AtPrime 𝔭) t ∈ nonZeroDivisors (Localization.AtPrime 𝔭) := by
      rw [IsScalarTower.algebraMap_apply C (AdicCompletion 𝔫 C) (Localization.AtPrime 𝔭)]
      exact IsLocalization.nonZeroDivisors_le_comap (M := 𝔭.primeCompl) (S := Localization.AtPrime 𝔭) htNZD
    have hfac : algebraMap C (Localization.AtPrime 𝔭) t =
        algebraMap (Localization.AtPrime 𝔮) (Localization.AtPrime 𝔭) a * π := by
      rw [IsScalarTower.algebraMap_apply C (Localization.AtPrime 𝔮) (Localization.AtPrime 𝔭), ← ha, map_mul]
    rw [hfac] at htR
    exact (mul_mem_nonZeroDivisors.1 htR).2

end BDescN4Kit2

namespace N4ON

theorem isDiscreteValuationRing_quotient
    {O : Type} [CommRing O] [IsNoetherianRing O] [IsLocalRing O] [IsDomain O]
    (ϖ s : O) (hmax : maximalIdeal O = Ideal.span {ϖ, s}) (I : Ideal O) [hIp : I.IsPrime] (hs : s ∈ I) (hϖ : ϖ ∉ I) :
    ∃ (_ : IsDomain (O ⧸ I)), IsDiscreteValuationRing (O ⧸ I) := by
  classical
  haveI : IsDomain (O ⧸ I) := inferInstance
  haveI : IsLocalRing (O ⧸ I) := IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  haveI : IsNoetherianRing (O ⧸ I) := inferInstance
  have hI𝔪 : I ≤ maximalIdeal O := IsLocalRing.le_maximalIdeal hIp.ne_top
  have hmax'' : maximalIdeal (O ⧸ I) = Ideal.span {Ideal.Quotient.mk I ϖ} := by
    have h1 : (maximalIdeal O).map (Ideal.Quotient.mk I) = maximalIdeal (O ⧸ I) := by
      rcases Ideal.map_eq_top_or_isMaximal_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
        (IsLocalRing.maximalIdeal.isMaximal O) with h | h
      · exfalso
        have h1mem : (1 : O ⧸ I) ∈ (maximalIdeal O).map (Ideal.Quotient.mk I) := by rw [h]; trivial
        rw [Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective] at h1mem
        obtain ⟨m, hm, hm1⟩ := h1mem
        rw [← map_one (Ideal.Quotient.mk I), Ideal.Quotient.eq] at hm1
        apply (IsLocalRing.maximalIdeal.isMaximal O).ne_top
        rw [Ideal.eq_top_iff_one]
        have : (1 : O) = m - (m - 1) := by ring
        rw [this]; exact Ideal.sub_mem _ hm (hI𝔪 hm1)
      · exact IsLocalRing.eq_maximalIdeal h
    rw [← h1, hmax, Ideal.map_span, Set.image_insert_eq, Set.image_singleton,
      Ideal.Quotient.eq_zero_iff_mem.mpr hs]
    apply le_antisymm
    · rw [Ideal.span_le]; rintro x (rfl | rfl)
      · exact Ideal.subset_span rfl
      · exact Ideal.zero_mem _
    · exact Ideal.span_mono (by simp)
  have hϖ0 : Ideal.Quotient.mk I ϖ ≠ 0 := fun h => hϖ (Ideal.Quotient.eq_zero_iff_mem.mp h)
  have hnf : ¬ IsField (O ⧸ I) := by
    rw [IsLocalRing.isField_iff_maximalIdeal_eq, hmax'', Ideal.span_singleton_eq_bot]
    exact hϖ0
  have hprinc : Submodule.IsPrincipal (maximalIdeal (O ⧸ I)) :=
    ⟨⟨Ideal.Quotient.mk I ϖ, by rw [hmax'', Ideal.submodule_span_eq]⟩⟩
  exact ⟨inferInstance, ((IsDiscreteValuationRing.TFAE (O ⧸ I) hnf).out 4 0).mp hprinc⟩

theorem ringKrullDim_le_of_isIntegral_ringHom
    {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (hφ : φ.IsIntegral) :
    ringKrullDim S ≤ ringKrullDim R := by
  letI : Algebra R S := φ.toAlgebra
  refine Order.krullDim_le_of_strictMono (fun P : PrimeSpectrum S => PrimeSpectrum.comap φ P) ?_
  intro P Q hPQ
  have hle : P.asIdeal ≤ Q.asIdeal := le_of_lt hPQ
  have hne : P.asIdeal ≠ Q.asIdeal := fun h => ne_of_lt hPQ (PrimeSpectrum.ext h)
  obtain ⟨x, hxQ, hxP⟩ : ∃ x ∈ Q.asIdeal, x ∉ P.asIdeal := by
    by_contra h
    exact hne (le_antisymm hle fun y hy => by_contra fun hy' => h ⟨y, hy, hy'⟩)
  change P.asIdeal.comap φ < Q.asIdeal.comap φ
  exact Ideal.comap_lt_comap_of_integral_mem_sdiff hle ⟨hxQ, hxP⟩ (hφ x)

theorem ringKrullDim_le_one_of_span_singleton (T : Type) [CommRing T] [IsNoetherianRing T] [IsLocalRing T] (a : T)
    (ha : maximalIdeal T = Ideal.span {a}) : ringKrullDim T ≤ 1 := by
  refine (ringKrullDim_le_spanFinrank_maximalIdeal T).trans ?_
  rw [ha]
  exact_mod_cast (Submodule.spanFinrank_span_le_ncard_of_finite (Set.finite_singleton a)).trans
    (by rw [Set.ncard_singleton])

end N4ON

open N4ON in
set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    {O : Type} [CommRing O] [IsRegularLocalRing O]
    (ϖ s : O) (hmaxO : maximalIdeal O = Ideal.span {ϖ, s}) (hdimO : ringKrullDim O = 2)
    (e : ℕ) (he : 0 < e) (heO : IsUnit (e : O))
    {C : Type} [CommRing C] [IsDomain C] [IsIntegrallyClosed C] [Algebra O C] [Module.Finite O C] [FaithfulSMul O C]
    {G : Type} [Group G] [Finite G] [MulSemiringAction G C] [SMulCommClass G O C] [FaithfulSMul G C]
    [Algebra.IsInvariant O C G]
    (𝔫 : Ideal C) [𝔫.IsMaximal] [𝔫.LiesOver (maximalIdeal O)]
    (hI : Nat.card ↥((𝔫.inertia G).subgroupOf (MulAction.stabilizer G 𝔫)) = e)
    (𝔭 : Ideal (AdicCompletion 𝔫 C)) [𝔭.IsPrime] (h𝔭 : ¬ 𝔭.IsMaximal)
    (hs𝔭 : algebraMap O (AdicCompletion 𝔫 C) s ∈ 𝔭) :
    IsRegularLocalRing (Localization.AtPrime 𝔭) := by
  classical
  haveI : IsNoetherianRing O := inferInstance
  haveI : IsDomain O := IsRegularLocalRing.isDomain O
  haveI : IsNoetherianRing C := Algebra.FiniteType.isNoetherianRing O C
  haveI : Algebra.IsIntegral O C := inferInstance
  obtain ⟨hĈnoeth, hĈloc, hĈmax, -, hĈcomap, -⟩ :=
    AdicCompletion.isNoetherianRing_and_exists_isLocalRing_maximalIdeal_eq_map_of_isMaximal 𝔫
  haveI := hĈnoeth
  haveI := hĈloc

  have hs0 : s ≠ 0 := by
    intro h0
    have h1 := ringKrullDim_le_one_of_span_singleton O ϖ (by
      rw [hmaxO, h0]
      apply le_antisymm
      · rw [Ideal.span_le]; rintro x (rfl | rfl)
        · exact Ideal.subset_span rfl
        · exact Ideal.zero_mem _
      · exact Ideal.span_mono (by simp))
    rw [hdimO] at h1; exact absurd h1 (by decide)

  set 𝔮 : Ideal C := 𝔭.comap (algebraMap C (AdicCompletion 𝔫 C)) with h𝔮def
  haveI h𝔮p : 𝔮.IsPrime := Ideal.comap_isPrime _ 𝔭
  have hsC : algebraMap O C s ∈ 𝔮 := by
    show algebraMap C (AdicCompletion 𝔫 C) (algebraMap O C s) ∈ 𝔭
    rw [← IsScalarTower.algebraMap_apply]; exact hs𝔭
  have hsC0 : algebraMap O C s ≠ 0 := fun h =>
    hs0 (FaithfulSMul.algebraMap_injective O C (by rw [h, map_zero]))
  have h𝔮0 : 𝔮 ≠ ⊥ := fun h => hsC0 (by rw [h] at hsC; exact hsC)
  have h𝔮𝔫 : 𝔮 ≤ 𝔫 := by
    intro c hc
    by_contra hcn
    rw [← hĈcomap, Ideal.mem_comap] at hcn
    have hu : IsUnit (algebraMap C (AdicCompletion 𝔫 C) c) := by
      by_contra hnu; exact hcn hnu
    exact ‹𝔭.IsPrime›.ne_top (Ideal.eq_top_of_isUnit_mem _ hc hu)
  have h𝔮ne : 𝔮 ≠ 𝔫 := by
    intro h
    apply h𝔭
    have hle : maximalIdeal (AdicCompletion 𝔫 C) ≤ 𝔭 := by
      rw [hĈmax]
      exact Ideal.map_le_iff_le_comap.mpr h.symm.le
    have := (IsLocalRing.maximalIdeal.isMaximal (AdicCompletion 𝔫 C)).eq_of_le ‹𝔭.IsPrime›.ne_top hle
    rw [← this]; exact IsLocalRing.maximalIdeal.isMaximal _

  set 𝔰 : Ideal O := 𝔮.comap (algebraMap O C) with h𝔰def
  haveI h𝔰p : 𝔰.IsPrime := Ideal.comap_isPrime _ 𝔮
  haveI : 𝔮.LiesOver 𝔰 := ⟨rfl⟩
  have hs𝔰 : s ∈ 𝔰 := hsC
  have h𝔰ne : 𝔰 ≠ maximalIdeal O := by
    intro h
    have hmax𝔮 : 𝔮.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := O) 𝔮
      (by rw [show 𝔮.comap (algebraMap O C) = 𝔰 from rfl, h]; exact IsLocalRing.maximalIdeal.isMaximal O)
    exact h𝔮ne (hmax𝔮.eq_of_le ‹𝔫.IsMaximal›.ne_top h𝔮𝔫)
  have hϖ𝔰 : ϖ ∉ 𝔰 := by
    intro h
    apply h𝔰ne
    refine le_antisymm (IsLocalRing.le_maximalIdeal h𝔰p.ne_top) ?_
    rw [hmaxO, Ideal.span_le]
    rintro x (rfl | rfl)
    · exact h
    · exact hs𝔰
  obtain ⟨hO'dom, hO'dvr⟩ := isDiscreteValuationRing_quotient ϖ s hmaxO 𝔰 hs𝔰 hϖ𝔰
  haveI := hO'dom
  haveI := hO'dvr

  haveI : IsDomain (C ⧸ 𝔮) := inferInstance
  haveI : Module.Finite O (C ⧸ 𝔮) := inferInstance
  haveI : Module.Finite (O ⧸ 𝔰) (C ⧸ 𝔮) := Module.Finite.of_restrictScalars_finite O _ _
  haveI : Algebra.IsIntegral (O ⧸ 𝔰) (C ⧸ 𝔮) := inferInstance
  set 𝔫₀ : Ideal (C ⧸ 𝔮) := 𝔫.map (algebraMap C (C ⧸ 𝔮)) with h𝔫₀def
  haveI h𝔫₀max : 𝔫₀.IsMaximal := by
    rcases Ideal.map_eq_top_or_isMaximal_of_surjective (algebraMap C (C ⧸ 𝔮)) Ideal.Quotient.mk_surjective
      ‹𝔫.IsMaximal› with h | h
    · exfalso
      have h1mem : (1 : C ⧸ 𝔮) ∈ 𝔫.map (algebraMap C (C ⧸ 𝔮)) := by rw [h]; trivial
      rw [Ideal.mem_map_iff_of_surjective (algebraMap C (C ⧸ 𝔮))
        (Ideal.Quotient.mk_surjective : Function.Surjective (algebraMap C (C ⧸ 𝔮)))] at h1mem
      obtain ⟨m, hm, hm1⟩ := h1mem
      have hm1' : m - 1 ∈ 𝔮 := by
        rw [← Ideal.Quotient.eq, map_one]; exact hm1
      apply ‹𝔫.IsMaximal›.ne_top
      rw [Ideal.eq_top_iff_one]
      have : (1 : C) = m - (m - 1) := by ring
      rw [this]; exact Ideal.sub_mem _ hm (h𝔮𝔫 hm1')
    · exact h
  haveI : 𝔫₀.LiesOver (maximalIdeal (O ⧸ 𝔰)) :=
    ⟨(IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := O ⧸ 𝔰) 𝔫₀)).symm⟩

  letI algKL : Algebra (FractionRing (O ⧸ 𝔰)) (FractionRing (C ⧸ 𝔮)) := FractionRing.liftAlgebra (O ⧸ 𝔰) _
  haveI : IsScalarTower (O ⧸ 𝔰) (FractionRing (O ⧸ 𝔰)) (FractionRing (C ⧸ 𝔮)) :=
    FractionRing.isScalarTower_liftAlgebra _ _
  haveI hsep : Algebra.IsSeparable (FractionRing (O ⧸ 𝔰)) (FractionRing (C ⧸ 𝔮)) :=
    Algebra.IsInvariant.isSeparable_of_isFractionRing_quotient_of_lt_of_isUnit_card_inertia
      hdimO e he heO 𝔫 hI 𝔮 h𝔮0 h𝔮𝔫 h𝔮ne 𝔰 (FractionRing (O ⧸ 𝔰)) (FractionRing (C ⧸ 𝔮))

  obtain ⟨𝔓, h𝔓p, h𝔓max, ⟨f⟩⟩ :=
    BDescN4Kit.exists_ringEquiv_localization_quotient_map 𝔫 𝔮 𝔭 Ideal.map_comap_le
  haveI := h𝔓p
  have h𝔓nm : ¬ 𝔓.IsMaximal := fun h => h𝔭 (h𝔓max h)
  have hfield : IsField (Localization.AtPrime 𝔓) :=
    AdicCompletion.isField_localization_atPrime_of_not_isMaximal_of_isSeparable (O := O ⧸ 𝔰) (C := C ⧸ 𝔮)
      (FractionRing (O ⧸ 𝔰)) (FractionRing (C ⧸ 𝔮)) 𝔫₀ 𝔓 h𝔓nm
  have hfieldR : IsField (Localization.AtPrime 𝔭 ⧸ 𝔮.map (algebraMap C (Localization.AtPrime 𝔭))) :=
    MulEquiv.isField hfield f.toMulEquiv

  haveI : IsNoetherianRing (Localization.AtPrime 𝔭) := IsLocalization.isNoetherianRing 𝔭.primeCompl _ hĈnoeth

  have hht : 𝔮.height = 1 := by
    have hC2 : ringKrullDim C ≤ 2 := by
      rw [← hdimO]
      exact ringKrullDim_le_of_isIntegral_ringHom (algebraMap O C) (fun x => Algebra.IsIntegral.isIntegral x)
    have h𝔫2 : 𝔫.height ≤ 2 := by
      have h := (Ideal.height_le_ringKrullDim_of_isPrime (I := 𝔫)).trans hC2
      have h' : ((𝔫.height : ℕ∞) : WithBot ℕ∞) ≤ ((2 : ℕ∞) : WithBot ℕ∞) := h
      exact WithBot.coe_le_coe.mp h'
    haveI : (⊥ : Ideal C).IsPrime := Ideal.bot_prime
    have h1 := Ideal.height_add_one_le_of_lt_of_isPrime (bot_lt_iff_ne_bot.mpr h𝔮0)
    have h2 := Ideal.height_add_one_le_of_lt_of_isPrime (lt_of_le_of_ne h𝔮𝔫 h𝔮ne)
    have h0 : (⊥ : Ideal C).height = 0 := Ideal.height_bot
    rw [h0, zero_add] at h1
    refine le_antisymm ?_ h1
    have h3 : 𝔮.height + 1 ≤ 1 + 1 := h2.trans (h𝔫2.trans (by norm_num))
    exact (ENat.add_le_add_iff_right ENat.one_ne_top).mp h3

  have hsNZD : algebraMap C (AdicCompletion 𝔫 C) (algebraMap O C s) ∈ nonZeroDivisors (AdicCompletion 𝔫 C) := by
    obtain ⟨hÔdom, -, -, -⟩ := IsRegularLocalRing.isDomain_and_isIntegrallyClosed_adicCompletion_of_ringKrullDim_eq_two O hdimO
    haveI := hÔdom
    have hinj : Function.Injective (algebraMap O (AdicCompletion (maximalIdeal O) O)) :=
      AdicCompletion.of_injective (maximalIdeal O) O
    have hs' : algebraMap O (AdicCompletion (maximalIdeal O) O) s ∈ nonZeroDivisors (AdicCompletion (maximalIdeal O) O) :=
      mem_nonZeroDivisors_of_ne_zero (fun h => hs0 (hinj (by rw [h, map_zero])))
    have key := AdicCompletion.mem_nonZeroDivisors_algebraMap_of_mem_nonZeroDivisors_of_liesOver 𝔫 _ hs'
    rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply O C (AdicCompletion 𝔫 C)] at key
    exact key
  obtain ⟨π, hπspan, hπmax, hπnzd⟩ :=
    BDescN4Kit2.exists_map_eq_span_singleton_of_height_eq_one 𝔫 𝔮 hht 𝔭 rfl (algebraMap O C s) hsC hsNZD
  rw [hπspan] at hfieldR
  have hfib : IsRegularLocalRing (Localization.AtPrime 𝔭 ⧸ Ideal.span {π}) := by
    letI := hfieldR.toField
    infer_instance
  exact (IsRegularLocalRing.of_isRegularLocalRing_quotient_span_singleton_of_mem_nonZeroDivisors π hπmax hπnzd hfib).1

end S_AdicCompletion_isRegularLocalRing_localization_atPrime_of_mem_of_not_isMaximal_of_tame
end P2MW
export P2MW.S_AdicCompletion_isRegularLocalRing_localization_atPrime_of_mem_of_not_isMaximal_of_tame (solution)
