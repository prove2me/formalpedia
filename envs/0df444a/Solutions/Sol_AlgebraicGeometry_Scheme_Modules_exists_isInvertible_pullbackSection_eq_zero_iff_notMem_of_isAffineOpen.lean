-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.exists_isInvertible_pullbackSection_eq_zero_iff_notMem_of_isAffineOpen
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/cdc75577-c3fd-5ca5-9dce-e76633c55748

import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme
import Definitions.Def_AlgebraicCurve_RelCartier
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_pullbackSection_eq_zero_iff_mem_support
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_zeroSchemeIdeal_invModuleSection
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_invModule
import Theorems.Thm_AlgebraicGeometry_Smooth_isRegularLocalRing_stalk
import Theorems.Thm_IsRegularRing_uniqueFactorizationMonoid_of_isLocalRing
import Theorems.Thm_AlgebraicGeometry_Scheme_RationalMap_exists_specializes_ringKrullDim_le_one_of_not_mem_domain
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_isInvertible_pullbackSection_eq_zero_iff_notMem_of_isAffineOpen
p2m_attr_erase "instance" "SheafOfModules.isIso_ihomModelToIhom PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback instTopologicallyFGOfFiniteType"
p2m_attr_erase "simp" "PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry TopologicalSpace"

namespace P2mWeilCartier

section SpreadOut

variable {R : Type*} [CommRing R] (p : Ideal R) [p.IsPrime]
  (S : Type*) [CommRing S] [Algebra R S] [IsLocalization.AtPrime S p]

lemma exists_notMem_mul_mem (𝔞 : Ideal R) (h𝔞 : 𝔞.FG) (g : R)
    (h : 𝔞.map (algebraMap R S) = Ideal.span {algebraMap R S g}) :
    ∃ f ∉ p, (∀ a ∈ 𝔞, ∃ r : R, f * a = r * g) ∧ f * g ∈ 𝔞 := by
  classical
  obtain ⟨s, hs⟩ := h𝔞

  have hgen : ∀ a ∈ s, ∃ fa ∉ p, ∃ r : R, fa * a = r * g := by
    intro a ha
    have haS : algebraMap R S a ∈ Ideal.span {algebraMap R S g} :=
      h ▸ Ideal.mem_map_of_mem _ (hs ▸ Ideal.subset_span ha)
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp haS
    obtain ⟨⟨r, u⟩, rfl⟩ := IsLocalization.mk'_surjective p.primeCompl c
    have h1 : algebraMap R S (r * g) = algebraMap R S ((u : R) * a) := by
      rw [map_mul, map_mul, ← hc, ← IsLocalization.mk'_spec S r u]
      ring
    obtain ⟨v, hv⟩ := (IsLocalization.eq_iff_exists p.primeCompl S).mp h1
    refine ⟨(v : R) * u, ?_, v * r, ?_⟩
    · exact fun hmem => ((p.primeCompl).mul_mem v.2 u.2) hmem
    · calc (v : R) * u * a = v * (u * a) := by ring
        _ = v * (r * g) := hv.symm
        _ = v * r * g := by ring
  choose! fa hfa r hr using hgen

  have hgS : algebraMap R S g ∈ 𝔞.map (algebraMap R S) :=
    h ▸ Ideal.subset_span (Set.mem_singleton _)
  obtain ⟨⟨a₀, u₀⟩, hau⟩ := (IsLocalization.mem_map_algebraMap_iff p.primeCompl S).mp hgS
  have h2 : algebraMap R S (g * u₀) = algebraMap R S a₀ := by
    rw [map_mul]; exact hau
  obtain ⟨v₀, hv₀⟩ := (IsLocalization.eq_iff_exists p.primeCompl S).mp h2
  let f₀ : R := v₀ * u₀
  have hf₀ : f₀ ∉ p := fun hmem => ((p.primeCompl).mul_mem v₀.2 u₀.2) hmem
  have hf₀g : f₀ * g ∈ 𝔞 := by
    have : f₀ * g = v₀ * a₀ := by
      calc f₀ * g = (v₀ : R) * (g * u₀) := by simp only [f₀]; ring
        _ = v₀ * a₀ := hv₀
    rw [this]
    exact Ideal.mul_mem_left _ _ a₀.2
  refine ⟨f₀ * ∏ a ∈ s, fa a, ?_, ?_, ?_⟩
  · intro hmem
    have hprod : (∏ a ∈ s, fa a) ∈ p.primeCompl :=
      Submonoid.prod_mem _ fun a ha => hfa a ha
    exact ((p.primeCompl).mul_mem hf₀ hprod) hmem
  · intro a ha
    rw [← hs] at ha
    refine Submodule.span_induction ?_ ?_ ?_ ?_ ha
    · intro a ha
      obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem fa ha
      refine ⟨f₀ * c * r a, ?_⟩
      rw [hc]
      calc f₀ * (fa a * c) * a = f₀ * c * (fa a * a) := by ring
        _ = f₀ * c * (r a * g) := by rw [hr a ha]
        _ = f₀ * c * r a * g := by ring
    · exact ⟨0, by simp⟩
    · rintro a b - - ⟨ra, hra⟩ ⟨rb, hrb⟩
      exact ⟨ra + rb, by rw [mul_add, hra, hrb, add_mul]⟩
    · rintro c a - ⟨ra, hra⟩
      exact ⟨c * ra, by rw [smul_eq_mul, mul_left_comm, hra, mul_assoc]⟩
  · have : f₀ * (∏ a ∈ s, fa a) * g = (∏ a ∈ s, fa a) * (f₀ * g) := by ring
    rw [this]
    exact Ideal.mul_mem_left _ _ hf₀g

lemma map_eq_span_of_away {𝔞 : Ideal R} {f g : R} (h1 : ∀ a ∈ 𝔞, ∃ r : R, f * a = r * g)
    (h2 : f * g ∈ 𝔞) (T : Type*) [CommRing T] [Algebra R T] [IsLocalization.Away f T] :
    𝔞.map (algebraMap R T) = Ideal.span {algebraMap R T g} := by
  have hfu : IsUnit (algebraMap R T f) := IsLocalization.Away.algebraMap_isUnit f
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro a ha
    obtain ⟨r, hr⟩ := h1 a ha
    rw [Ideal.mem_comap, Ideal.mem_span_singleton']
    refine ⟨hfu.unit⁻¹ * algebraMap R T r, ?_⟩
    rw [mul_assoc, ← map_mul, ← hr, map_mul, ← mul_assoc, IsUnit.val_inv_mul, one_mul]
  · rw [Ideal.span_singleton_le_iff_mem]
    have := Ideal.mem_map_of_mem (algebraMap R T) h2
    rw [map_mul] at this
    exact (Ideal.unit_mul_mem_iff_mem _ hfu).mp this

end SpreadOut

section UFD

variable {S : Type*} [CommRing S] [IsDomain S] [UniqueFactorizationMonoid S]

omit [IsDomain S] [UniqueFactorizationMonoid S] in

lemma prod_dvd_of_forall_prime_dvd {ι : Type*} (s : Finset ι) (π : ι → S)
    (hπ : ∀ i ∈ s, Prime (π i)) (hne : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ¬ π i ∣ π j)
    (a : S) (ha : ∀ i ∈ s, π i ∣ a) : (∏ i ∈ s, π i) ∣ a := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.prod_insert hi]
    have hs : (∏ j ∈ s, π j) ∣ a :=
      ih (fun j hj => hπ j (Finset.mem_insert_of_mem hj))
        (fun j hj j' hj' => hne j (Finset.mem_insert_of_mem hj) j' (Finset.mem_insert_of_mem hj'))
        (fun j hj => ha j (Finset.mem_insert_of_mem hj))
    obtain ⟨c, rfl⟩ := hs
    have hpi : Prime (π i) := hπ i (Finset.mem_insert_self i s)
    rcases hpi.dvd_or_dvd (ha i (Finset.mem_insert_self i s)) with h | h
    · obtain ⟨j, hj, hij⟩ := (Prime.dvd_finsetProd_iff hpi _).mp h
      exact absurd hij (hne i (Finset.mem_insert_self i s) j (Finset.mem_insert_of_mem hj)
        (fun e => hi (e ▸ hj)))
    · rw [mul_comm]
      exact mul_dvd_mul_left _ h

lemma exists_eq_span_singleton_of_radical (J : Ideal S) (hJ0 : J ≠ ⊥) (hJrad : J.IsRadical)
    (hfin : J.minimalPrimes.Finite)
    (hht : ∀ Q ∈ J.minimalPrimes, ∀ P : Ideal S, P.IsPrime → P ≠ ⊥ → P ≤ Q → P = Q) :
    ∃ γ : S, J = Ideal.span {γ} := by
  classical

  have hgen : ∀ Q ∈ J.minimalPrimes, ∃ π : S, Prime π ∧ Q = Ideal.span {π} := by
    intro Q hQ
    have hQp : Q.IsPrime := hQ.1.1
    have hQ0 : Q ≠ ⊥ := fun h => hJ0 (le_bot_iff.mp (h ▸ hQ.1.2))
    obtain ⟨π, hπQ, hπ⟩ := hQp.exists_mem_prime_of_ne_bot hQ0
    refine ⟨π, hπ, (hht Q hQ _ ((Ideal.span_singleton_prime hπ.ne_zero).mpr hπ) ?_
      ((Ideal.span_singleton_le_iff_mem _).mpr hπQ)).symm⟩
    simpa using hπ.ne_zero
  choose! π hπ hQπ using hgen
  refine ⟨∏ Q ∈ hfin.toFinset, π Q, le_antisymm ?_ ?_⟩
  ·
    intro a ha
    rw [Ideal.mem_span_singleton]
    refine prod_dvd_of_forall_prime_dvd _ _ (fun Q hQ => hπ Q (hfin.mem_toFinset.mp hQ)) ?_ a ?_
    · intro Q hQ Q' hQ' hne hdvd
      have hQm := hfin.mem_toFinset.mp hQ
      have hQ'm := hfin.mem_toFinset.mp hQ'

      have hle : Q' ≤ Q := by
        rw [hQπ Q hQm, hQπ Q' hQ'm, Ideal.span_singleton_le_span_singleton]
        exact hdvd
      exact hne (le_antisymm (hQm.2 ⟨hQ'm.1.1, hQ'm.1.2⟩ hle) hle)
    · intro Q hQ
      have hQm := hfin.mem_toFinset.mp hQ
      have : a ∈ Q := hQm.1.2 ha
      rw [hQπ Q hQm] at this
      exact Ideal.mem_span_singleton.mp this
  ·
    rw [Ideal.span_singleton_le_iff_mem]
    refine hJrad ?_
    rw [← Ideal.sInf_minimalPrimes, Submodule.mem_sInf]
    intro Q hQ
    have hQm : Q ∈ hfin.toFinset := hfin.mem_toFinset.mpr hQ
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem π hQm
    have hmem : π Q ∈ Q := (hQπ Q hQ).ge (Ideal.mem_span_singleton_self _)
    rw [hc]
    exact Ideal.mul_mem_right _ _ hmem

end UFD

section Geometry

variable {X : Scheme.{u}}

lemma exists_generator_of_notMem (Z : Closeds X) {x : X} (hxZ : x ∉ Z) :
    ∃ (U : X.affineOpens) (f : Γ(X, U)), x ∈ X.basicOpen f ∧
      ∃ g ∈ nonZeroDivisors Γ(X, X.affineBasicOpen f),
        (Scheme.IdealSheafData.vanishingIdeal Z).ideal (X.affineBasicOpen f) = Ideal.span {g} := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVZ⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (show x ∈ (Z : Set X)ᶜ from hxZ) Z.isClosed.isOpen_compl
  refine ⟨⟨V, hV⟩, 1, by simpa using hxV, 1, one_mem _, ?_⟩
  let W : X.affineOpens := X.affineBasicOpen (1 : Γ(X, (⟨V, hV⟩ : X.affineOpens)))
  have hWV : (W : X.Opens) ≤ V := X.basicOpen_le _
  change (Scheme.IdealSheafData.vanishingIdeal Z).ideal W = _
  rw [Ideal.span_singleton_one, Scheme.IdealSheafData.vanishingIdeal_ideal, eq_top_iff]
  intro r _
  refine (PrimeSpectrum.mem_vanishingIdeal _ _).mpr fun P hP => ?_
  have hPV : W.2.fromSpec P ∈ (W : X.Opens) := W.2.range_fromSpec.le ⟨P, rfl⟩
  exact absurd hP (hVZ (hWV hPV))

theorem isInvertible_vanishingIdeal [IsIntegral X] [IsLocallyNoetherian X]
    (hX : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x))
    (Z : Closeds X) (hZ : Z ≠ ⊤)
    (hcodim : ∀ y ∈ Z, (∀ y' ∈ Z, y' ⤳ y → y' = y) → ringKrullDim (X.presheaf.stalk y) ≤ 1) :
    (Scheme.IdealSheafData.vanishingIdeal Z).IsInvertible := by
  classical
  intro x
  by_cases hxZ : x ∈ Z
  swap
  · exact exists_generator_of_notMem Z hxZ

  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  haveI : Nonempty V := ⟨⟨x, hxV⟩⟩
  haveI : IsNoetherianRing Γ(X, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  let p : PrimeSpectrum Γ(X, V) := hV.primeIdealOf ⟨x, hxV⟩
  letI : Algebra Γ(X, V) (X.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨x, hxV⟩ : V)
  have hS : IsLocalization.AtPrime (X.presheaf.stalk x) p.asIdeal := hV.isLocalization_stalk ⟨x, hxV⟩
  haveI := hX x

  let 𝔞 : Ideal Γ(X, V) := (Scheme.IdealSheafData.vanishingIdeal Z).ideal ⟨V, hV⟩
  have h𝔞 : 𝔞 = PrimeSpectrum.vanishingIdeal (hV.fromSpec ⁻¹' (Z : Set X)) :=
    Scheme.IdealSheafData.vanishingIdeal_ideal Z ⟨V, hV⟩
  have ht : IsClosed (X := PrimeSpectrum Γ(X, V)) (hV.fromSpec ⁻¹' (Z : Set X)) :=
    Z.isClosed.preimage hV.fromSpec.continuous
  have hfs : ∀ P : PrimeSpectrum Γ(X, V), hV.fromSpec P ∈ Z ↔ 𝔞 ≤ P.asIdeal := by
    intro P
    constructor
    · intro hP r hr
      rw [h𝔞] at hr
      exact (PrimeSpectrum.mem_vanishingIdeal _ _).mp hr P hP
    · intro hP
      have hP' : P ∈ PrimeSpectrum.zeroLocus (𝔞 : Set Γ(X, V)) := hP
      rw [h𝔞, PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure] at hP'
      exact ht.closure_subset hP'

  have h𝔞0 : 𝔞 ≠ ⊥ := by
    intro h0
    have hVZ : (V : Set X) ⊆ Z := by
      intro y hyV
      obtain ⟨P, rfl⟩ := hV.range_fromSpec.ge hyV
      exact (hfs P).mpr (h0 ▸ bot_le)
    have hZc : ((Z : Set X)ᶜ).Nonempty := by
      rw [Set.nonempty_compl]
      intro h
      exact hZ (SetLike.coe_injective (h.trans Closeds.coe_top.symm))
    obtain ⟨y, hyV, hyZ⟩ := nonempty_preirreducible_inter V.2 Z.isClosed.isOpen_compl ⟨x, hxV⟩ hZc
    exact hyZ (hVZ hyV)

  let J : Ideal (X.presheaf.stalk x) := 𝔞.map (algebraMap Γ(X, V) (X.presheaf.stalk x))
  have h𝔞rad : 𝔞.radical = 𝔞 :=
    Ideal.radical_eq_iff.mpr (h𝔞 ▸ PrimeSpectrum.isRadical_vanishingIdeal _)
  have hJrad : J.IsRadical := by
    intro r hr
    rwa [← IsLocalization.map_radical p.asIdeal.primeCompl (X.presheaf.stalk x) 𝔞, h𝔞rad] at hr
  have hinj : Function.Injective (algebraMap Γ(X, V) (X.presheaf.stalk x)) :=
    IsLocalization.injective (X.presheaf.stalk x) p.asIdeal.primeCompl_le_nonZeroDivisors
  have hJ0 : J ≠ ⊥ := fun h => h𝔞0 ((Ideal.map_eq_bot_iff_of_injective hinj).mp h)
  have hfin : J.minimalPrimes.Finite := Ideal.finite_minimalPrimes_of_isNoetherianRing _ J

  have hht : ∀ Q ∈ J.minimalPrimes, ∀ P : Ideal (X.presheaf.stalk x),
      P.IsPrime → P ≠ ⊥ → P ≤ Q → P = Q := by
    intro Q hQ P hP hP0 hPQ
    haveI hQp : Q.IsPrime := hQ.1.1

    let q : Ideal Γ(X, V) := Q.comap (algebraMap Γ(X, V) (X.presheaf.stalk x))
    haveI hq : q.IsPrime := Ideal.IsPrime.comap _
    have hQq : q.map (algebraMap Γ(X, V) (X.presheaf.stalk x)) = Q :=
      IsLocalization.map_under p.asIdeal.primeCompl _ Q
    have hdisj : Disjoint (p.asIdeal.primeCompl : Set Γ(X, V)) (q : Set Γ(X, V)) := by
      rw [Set.disjoint_left]
      intro m hm hmq
      exact hQp.ne_top (Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_comap.mp hmq)
        (IsLocalization.map_units (X.presheaf.stalk x) ⟨m, hm⟩))
    let y : X := hV.fromSpec ⟨q, hq⟩
    have hyV : y ∈ V := hV.range_fromSpec.le ⟨_, rfl⟩
    have h𝔞q : 𝔞 ≤ q := Ideal.map_le_iff_le_comap.mp hQ.1.2
    have hyZ : y ∈ Z := (hfs ⟨q, hq⟩).mpr h𝔞q

    have hymax : ∀ y' ∈ Z, y' ⤳ y → y' = y := by
      intro y' hy'Z hy'y
      have hy'V : y' ∈ V := hy'y.mem_open V.2 hyV
      let P' := hV.primeIdealOf ⟨y', hy'V⟩
      have hfP' : hV.fromSpec P' = y' := hV.fromSpec_primeIdealOf ⟨y', hy'V⟩
      have hspec : P' ⤳ (⟨q, hq⟩ : PrimeSpectrum Γ(X, V)) :=
        hV.fromSpec.isOpenEmbedding.isInducing.specializes_iff.mp (by rw [hfP']; exact hy'y)
      have hle : P'.asIdeal ≤ q := (PrimeSpectrum.le_iff_specializes P' ⟨q, hq⟩).mpr hspec
      have h𝔞P' : 𝔞 ≤ P'.asIdeal := (hfs P').mp (by rw [hfP']; exact hy'Z)
      have hdisj' : Disjoint (p.asIdeal.primeCompl : Set Γ(X, V)) (P'.asIdeal : Set Γ(X, V)) :=
        hdisj.mono_right (SetLike.coe_subset_coe.mpr hle)
      have hQ'p : (P'.asIdeal.map (algebraMap Γ(X, V) (X.presheaf.stalk x))).IsPrime :=
        IsLocalization.isPrime_of_isPrime_disjoint _ _ P'.asIdeal P'.2 hdisj'
      have hJQ' : J ≤ P'.asIdeal.map (algebraMap Γ(X, V) (X.presheaf.stalk x)) := Ideal.map_mono h𝔞P'
      have hQ'Q : P'.asIdeal.map (algebraMap Γ(X, V) (X.presheaf.stalk x)) ≤ Q :=
        hQq ▸ Ideal.map_mono hle
      have hQQ' : Q ≤ P'.asIdeal.map (algebraMap Γ(X, V) (X.presheaf.stalk x)) :=
        hQ.2 ⟨hQ'p, hJQ'⟩ hQ'Q
      have heq : P'.asIdeal = q := by
        have h1 := IsLocalization.under_map_of_isPrime_disjoint p.asIdeal.primeCompl
          (X.presheaf.stalk x) P'.2 hdisj'
        rw [le_antisymm hQ'Q hQQ'] at h1
        exact h1.symm
      have : P' = ⟨q, hq⟩ := PrimeSpectrum.ext heq
      rw [← hfP', this]

    have hdim : Ring.KrullDimLE 1 (X.presheaf.stalk y) := Ring.krullDimLE_iff.mpr (hcodim y hyZ hymax)
    letI : Algebra Γ(X, V) (X.presheaf.stalk y) :=
      TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨y, hyV⟩ : V)
    have hy : IsLocalization.AtPrime (X.presheaf.stalk y) q := hV.isLocalization_stalk' ⟨q, hq⟩ hyV

    let r : Ideal Γ(X, V) := P.comap (algebraMap Γ(X, V) (X.presheaf.stalk x))
    haveI hr : r.IsPrime := hP.comap _
    have hPr : r.map (algebraMap Γ(X, V) (X.presheaf.stalk x)) = P :=
      IsLocalization.map_under p.asIdeal.primeCompl _ P
    have hrq : r ≤ q := Ideal.comap_mono hPQ
    have hr0 : r ≠ ⊥ := by
      intro h
      apply hP0
      rw [← hPr, h, Ideal.map_bot]
    have hdisjq : Disjoint (q.primeCompl : Set Γ(X, V)) (r : Set Γ(X, V)) := by
      rw [Set.disjoint_left]
      intro m hm hmr
      exact hm (hrq hmr)
    have hP₂ : (r.map (algebraMap Γ(X, V) (X.presheaf.stalk y))).IsPrime :=
      IsLocalization.isPrime_of_isPrime_disjoint q.primeCompl _ r hr hdisjq
    have hinj₂ : Function.Injective (algebraMap Γ(X, V) (X.presheaf.stalk y)) :=
      IsLocalization.injective (X.presheaf.stalk y) q.primeCompl_le_nonZeroDivisors
    have hP₂0 : r.map (algebraMap Γ(X, V) (X.presheaf.stalk y)) ≠ ⊥ := by
      rw [Ne, Ideal.map_eq_bot_iff_of_injective hinj₂]
      exact hr0
    have hP₂max : (r.map (algebraMap Γ(X, V) (X.presheaf.stalk y))).IsMaximal :=
      (Ring.krullDimLE_one_iff_of_noZeroDivisors.mp hdim) _ hP₂0 hP₂
    have hP₂eq : r.map (algebraMap Γ(X, V) (X.presheaf.stalk y)) =
        q.map (algebraMap Γ(X, V) (X.presheaf.stalk y)) := by
      rw [IsLocalization.AtPrime.map_eq_maximalIdeal q (X.presheaf.stalk y)]
      exact IsLocalRing.eq_maximalIdeal hP₂max
    have hrq' : r = q := by
      have h1 := IsLocalization.under_map_of_isPrime_disjoint q.primeCompl (X.presheaf.stalk y) hr hdisjq
      have h2 := IsLocalization.under_map_of_isPrime_disjoint q.primeCompl (X.presheaf.stalk y) hq
        (by rw [Set.disjoint_left]; exact fun m hm hmq => hm hmq)
      rw [hP₂eq] at h1
      exact h1.symm.trans h2
    rw [← hPr, ← hQq, hrq']

  obtain ⟨γ, hγ⟩ := exists_eq_span_singleton_of_radical J hJ0 hJrad hfin hht
  obtain ⟨⟨g, u⟩, rfl⟩ := IsLocalization.mk'_surjective p.asIdeal.primeCompl γ
  have hJg : J = Ideal.span {algebraMap Γ(X, V) (X.presheaf.stalk x) g} := by
    rw [hγ, ← IsLocalization.mk'_spec (X.presheaf.stalk x) g u,
      Ideal.span_singleton_mul_right_unit (IsLocalization.map_units _ u)]
  have hg0 : g ≠ 0 := by
    rintro rfl
    apply hJ0
    rw [hJg, map_zero, Ideal.span_singleton_eq_bot]

  obtain ⟨f, hfp, h1, h2⟩ :=
    exists_notMem_mul_mem p.asIdeal (X.presheaf.stalk x) 𝔞 (IsNoetherian.noetherian 𝔞) g hJg
  have hf0 : f ≠ 0 := fun h => hfp (h ▸ p.asIdeal.zero_mem)
  have hxf : x ∈ X.basicOpen f := by
    rw [X.mem_basicOpen f x hxV]
    exact (IsLocalization.AtPrime.isUnit_to_map_iff (X.presheaf.stalk x) p.asIdeal f).mpr hfp
  haveI : Nonempty (X.basicOpen f) := ⟨⟨x, hxf⟩⟩
  haveI : Nonempty ((X.affineBasicOpen (U := ⟨V, hV⟩) f : X.affineOpens) : X.Opens) :=
    ⟨⟨x, show x ∈ X.basicOpen f from hxf⟩⟩
  have hloc := hV.isLocalization_basicOpen f
  have hinjf : Function.Injective (algebraMap Γ(X, V) Γ(X, X.basicOpen f)) :=
    IsLocalization.injective Γ(X, X.basicOpen f) (powers_le_nonZeroDivisors_of_noZeroDivisors hf0)
  refine ⟨⟨V, hV⟩, f, hxf, algebraMap Γ(X, V) Γ(X, X.basicOpen f) g, ?_, ?_⟩
  · exact mem_nonZeroDivisors_of_ne_zero ((map_ne_zero_iff _ hinjf).mpr hg0)
  · rw [← (Scheme.IdealSheafData.vanishingIdeal Z).map_ideal_basicOpen ⟨V, hV⟩ f]
    exact map_eq_span_of_away h1 h2 Γ(X, X.basicOpen f)

end Geometry

end P2mWeilCartier

namespace P2mCartierCompl

variable {X : Scheme.{u}}

lemma pullbackSection_zero {X' : Scheme.{u}} (F : X' ⟶ X) (M : X.Modules) :
    Scheme.Modules.pullbackSection F (0 : 𝟙_ X.Modules ⟶ M) = 0 := by
  have h : (Scheme.Modules.pullback F).map (0 : (𝟙_ X.Modules) ⟶ M) = 0 := Functor.map_zero _ _ _
  exact (congrArg ((Scheme.Modules.pullbackUnitIso F).inv ≫ ·) h).trans comp_zero

lemma isSeparated_of_isSeparated_over (k : Type u) [Field k] (t : X ⟶ Spec (CommRingCat.of k))
    [IsSeparated t] : X.IsSeparated := by
  rw [Scheme.isSeparated_iff, ← terminal.comp_from t]
  infer_instance

lemma isRegularRing_stalk (k : Type u) [Field k] (t : X ⟶ Spec (CommRingCat.of k)) [Smooth t]
    (x : X) : IsRegularRing (X.presheaf.stalk x) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian t
  rw [isRegularRing_iff]
  intro P hP

  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  let R := Γ(X, V)
  let S := X.presheaf.stalk x
  letI : Algebra R S := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨x, hxV⟩ : V)
  have hS : IsLocalization.AtPrime S (hV.primeIdealOf ⟨x, hxV⟩).asIdeal := hV.isLocalization_stalk ⟨x, hxV⟩
  let T := Localization.AtPrime P
  haveI : IsScalarTower R S T := inferInstance
  let q : Ideal R := P.comap (algebraMap R S)
  haveI hq : q.IsPrime := Ideal.IsPrime.comap _
  have hT : IsLocalization.AtPrime T q :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl (S := S) T P

  let y : X := hV.fromSpec ⟨q, hq⟩
  have hyV : y ∈ V := hV.range_fromSpec.le ⟨_, rfl⟩
  letI : Algebra R (X.presheaf.stalk y) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨y, hyV⟩ : V)
  have hy : IsLocalization.AtPrime (X.presheaf.stalk y) q := hV.isLocalization_stalk' ⟨q, hq⟩ hyV
  let e : T ≃ₐ[R] X.presheaf.stalk y := IsLocalization.algEquiv q.primeCompl T (X.presheaf.stalk y)
  have hreg : IsRegularLocalRing (X.presheaf.stalk y) := Smooth.isRegularLocalRing_stalk (f := t) y
  exact IsRegularLocalRing.of_ringEquiv e.symm.toRingEquiv

lemma uniqueFactorizationMonoid_stalk (k : Type u) [Field k] (t : X ⟶ Spec (CommRingCat.of k))
    [Smooth t] [IsIntegral X] (x : X) : UniqueFactorizationMonoid (X.presheaf.stalk x) := by
  have := isRegularRing_stalk k t x
  exact IsRegularRing.uniqueFactorizationMonoid_of_isLocalRing (X.presheaf.stalk x)

lemma ringKrullDim_stalk_le_one_of_notMem [IsIntegral X] [IsLocallyNoetherian X] [X.IsSeparated]
    (hX : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (U : X.Opens) (hU : IsAffineOpen U) (hUne : (U : Set X).Nonempty) {y : X} (hy : y ∉ U)
    (hmax : ∀ y' : X, y' ∉ U → y' ⤳ y → y' = y) :
    ringKrullDim (X.presheaf.stalk y) ≤ 1 := by
  have : IsAffine U := hU
  have hUd : Dense (U : Set X) := U.2.dense hUne
  let f₀ : X.PartialMap U := ⟨U, hUd, 𝟙 _⟩

  have hdom : ∀ x ∈ f₀.toRationalMap.domain, x ∈ U := by
    intro x hx
    obtain ⟨g, hxg, hg⟩ := Scheme.RationalMap.mem_domain.mp hx
    obtain ⟨W, hW, hWl, hWr, e⟩ := Scheme.PartialMap.toRationalMap_eq_iff.mp hg
    have key : g.hom ≫ U.ι = g.domain.ι := by
      have : IsDominant (X.homOfLE hWl) := AlgebraicGeometry.Opens.isDominant_homOfLE hW _
      refine ext_of_isDominant (X.homOfLE hWl) ?_
      simp only [Scheme.PartialMap.restrict_hom] at e
      rw [reassoc_of% e]
      simp [f₀]
    have hx' : (g.hom ≫ U.ι) ⟨x, hxg⟩ ∈ U := by
      rw [Scheme.Hom.comp_apply]
      exact (g.hom ⟨x, hxg⟩).2
    rw [key] at hx'
    simpa using hx'
  obtain ⟨z, hz, hzy, hdim⟩ :=
    Scheme.RationalMap.exists_specializes_ringKrullDim_le_one_of_not_mem_domain hX f₀.toRationalMap
      y (fun h => hy (hdom y h))
  obtain rfl : z = y := hmax z (fun h => hz (f₀.le_domain_toRationalMap h)) hzy
  exact hdim

end P2mCartierCompl

open P2mCartierCompl in
theorem solution
    (k : Type u) [Field k] {X : Scheme.{u}} (t : X ⟶ Spec (CommRingCat.of k))
    [IsSeparated t] [IsIntegral X] [Smooth t] (U : X.Opens) (hU : IsAffineOpen U) :
    ∃ (L : X.Modules) (_ : Scheme.Modules.IsInvertible L) (θ : 𝟙_ X.Modules ⟶ L),
      ∀ (K : Type u) [Field K] (z : Spec (CommRingCat.of K) ⟶ X),
        Scheme.Modules.pullbackSection z θ = 0 ↔ z (IsLocalRing.closedPoint K) ∉ U := by
  by_cases hU0 : U = ⊥
  ·
    subst hU0
    exact ⟨𝟙_ X.Modules, Scheme.Modules.isInvertible_unit X, 0, fun K _ z =>
      ⟨fun _ h => h, fun _ => pullbackSection_zero z _⟩⟩

  have hUne : (U : Set X).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    exact fun h => hU0 (TopologicalSpace.Opens.ext (by simpa using h))
  let Z : TopologicalSpace.Closeds X := ⟨(U : Set X)ᶜ, U.isOpen.isClosed_compl⟩
  have hZ : Z ≠ ⊤ := by
    intro h
    obtain ⟨x, hx⟩ := hUne
    have : x ∈ (Z : Set X) := by rw [h]; trivial
    exact this hx
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian t
  have : X.IsSeparated := isSeparated_of_isSeparated_over k t
  have hUFD : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x) :=
    uniqueFactorizationMonoid_stalk k t

  have hcodim : ∀ y ∈ Z, (∀ y' ∈ Z, y' ⤳ y → y' = y) → ringKrullDim (X.presheaf.stalk y) ≤ 1 := by
    intro y hy hmax
    exact ringKrullDim_stalk_le_one_of_notMem (fun x => have := hUFD x; inferInstance) U hU hUne
      (fun h => hy h) (fun y' h h' => hmax y' h h')

  have hI : (Scheme.IdealSheafData.vanishingIdeal Z).IsInvertible :=
    P2mWeilCartier.isInvertible_vanishingIdeal hUFD Z hZ hcodim

  refine ⟨(Scheme.IdealSheafData.vanishingIdeal Z).invModule, hI.isInvertible_invModule,
    (Scheme.IdealSheafData.vanishingIdeal Z).invModuleSection, fun K _ z => ?_⟩
  rw [Scheme.Modules.IsInvertible.pullbackSection_eq_zero_iff_mem_support hI.isInvertible_invModule,
    hI.zeroSchemeIdeal_invModuleSection, ← SetLike.mem_coe,
    Scheme.IdealSheafData.coe_support_vanishingIdeal]
  rfl

end S_AlgebraicGeometry_Scheme_Modules_exists_isInvertible_pullbackSection_eq_zero_iff_notMem_of_isAffineOpen
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_isInvertible_pullbackSection_eq_zero_iff_notMem_of_isAffineOpen (solution)
