-- Prove2me | solution 1 for AlgebraicGeometry.exists_valuativeCommSq_isDiscreteValuationRing_finite_residueField_of_specializes
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/044b1156-8dc7-5b77-9129-3ae4c49a671a

import Mathlib
import Theorems.Thm_IsLocalRing_exists_valuationSubring_isDiscreteValuationRing_dominates_finite_residueField
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_valuativeCommSq_isDiscreteValuationRing_finite_residueField_of_specializes

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace SpecDvrSqGC3

open IsLocalRing

section alg

variable {C : Type u} [CommRing C] [IsNoetherianRing C]
  (𝔮 𝔪 : Ideal C) [𝔮.IsPrime] [h𝔪 : 𝔪.IsMaximal]

abbrev mbar : Ideal (C ⧸ 𝔮) := 𝔪.map (Ideal.Quotient.mk 𝔮)

theorem comap_mbar (hqm : 𝔮 ≤ 𝔪) : (mbar 𝔮 𝔪).comap (Ideal.Quotient.mk 𝔮) = 𝔪 := by
  rw [mbar, Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
    Ideal.mk_ker, sup_eq_left.mpr hqm]

theorem mbar_isMaximal (hqm : 𝔮 ≤ 𝔪) : (mbar 𝔮 𝔪).IsMaximal := by
  rcases Ideal.map_eq_top_or_isMaximal_of_surjective (Ideal.Quotient.mk 𝔮) Ideal.Quotient.mk_surjective h𝔪 with h | h
  · exfalso
    have := comap_mbar 𝔮 𝔪 hqm
    rw [mbar] at this
    rw [h, Ideal.comap_top] at this
    exact h𝔪.ne_top this.symm
  · exact h

theorem eq_bot_of_lt_mbar (hqm : 𝔮 ≤ 𝔪)
    (hcov : ∀ p : Ideal C, p.IsPrime → 𝔮 ≤ p → p ≤ 𝔪 → p = 𝔮 ∨ p = 𝔪)
    (P : Ideal (C ⧸ 𝔮)) [P.IsPrime] (hP : P < mbar 𝔮 𝔪) : P = ⊥ := by
  have h1 : 𝔮 ≤ P.comap (Ideal.Quotient.mk 𝔮) := fun c hc => by
    show Ideal.Quotient.mk 𝔮 c ∈ P
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hc]; exact P.zero_mem
  have h2 : P.comap (Ideal.Quotient.mk 𝔮) ≤ 𝔪 := by
    rw [← comap_mbar 𝔮 𝔪 hqm]; exact Ideal.comap_mono hP.le
  rcases hcov _ (Ideal.IsPrime.comap _) h1 h2 with h | h
  · have : P = (P.comap (Ideal.Quotient.mk 𝔮)).map (Ideal.Quotient.mk 𝔮) :=
      (Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective _).symm
    rw [this, h, Ideal.map_quotient_self]
  · exfalso
    have : P = mbar 𝔮 𝔪 := by
      rw [← Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective P, h]
    exact hP.ne this

theorem height_mbar (hqm : 𝔮 ≤ 𝔪) (hne : 𝔮 ≠ 𝔪)
    (hcov : ∀ p : Ideal C, p.IsPrime → 𝔮 ≤ p → p ≤ 𝔪 → p = 𝔮 ∨ p = 𝔪) :
    haveI := mbar_isMaximal 𝔮 𝔪 hqm
    (mbar 𝔮 𝔪).height = 1 := by
  haveI := mbar_isMaximal 𝔮 𝔪 hqm
  apply le_antisymm
  · refine (Ideal.height_le_iff (n := 1)).mpr fun P hP hPlt => ?_
    haveI := hP
    rw [eq_bot_of_lt_mbar 𝔮 𝔪 hqm hcov P hPlt, Ideal.height_bot]
    exact zero_lt_one
  · rw [ENat.one_le_iff_ne_zero]
    intro h0
    rw [Ideal.height_eq_zero_iff] at h0
    have hb : mbar 𝔮 𝔪 = ⊥ := le_bot_iff.mp (h0.2 ⟨Ideal.isPrime_bot, bot_le⟩ bot_le)
    apply hne
    rw [← comap_mbar 𝔮 𝔪 hqm, hb, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]

end alg

end SpecDvrSqGC3

theorem solution
    {C : Type u} [CommRing C] [IsNoetherianRing C] (hfin : ∀ (m : Ideal C) [m.IsMaximal], Finite (C ⧸ m))
    {X : Scheme.{u}} (g : X ⟶ Spec (CommRingCat.of C)) [LocallyOfFiniteType g]
    (x : X) (t : ↥(Spec (CommRingCat.of C))) (ht : IsClosed ({t} : Set ↥(Spec (CommRingCat.of C))))
    (hxt : g.base x ⤳ t) (hne : g.base x ≠ t)
    (hcov : ∀ p : Ideal C, p.IsPrime → (g.base x).asIdeal ≤ p → p ≤ t.asIdeal → p = (g.base x).asIdeal ∨ p = t.asIdeal) :
    ∃ S : ValuativeCommSq g, IsDiscreteValuationRing S.R ∧ Finite (IsLocalRing.ResidueField S.R) ∧
      S.i₂.base (IsLocalRing.closedPoint S.R) = t ∧ Set.range S.i₁.base ⊆ closure {x} := by
  classical

  set 𝔮 : Ideal C := (g.base x).asIdeal with h𝔮def
  have hmax : t.asIdeal.IsMaximal := (PrimeSpectrum.isClosed_singleton_iff_isMaximal t).mp ht
  haveI := hmax
  have hqm : 𝔮 ≤ t.asIdeal := (PrimeSpectrum.le_iff_specializes _ _).mpr hxt
  have hneI : 𝔮 ≠ t.asIdeal := fun h => hne (PrimeSpectrum.ext h)

  haveI hmb : (SpecDvrSqGC3.mbar 𝔮 t.asIdeal).IsMaximal := SpecDvrSqGC3.mbar_isMaximal 𝔮 t.asIdeal hqm
  let R₀ : Type u := C ⧸ 𝔮
  let A : Type u := Localization.AtPrime (SpecDvrSqGC3.mbar 𝔮 t.asIdeal)
  let K₀ : Type u := FractionRing R₀
  haveI : IsDomain A := IsLocalization.isDomain_of_le_nonZeroDivisors (M := (SpecDvrSqGC3.mbar 𝔮 t.asIdeal).primeCompl) A
    (Ideal.primeCompl_le_nonZeroDivisors _)
  haveI : IsNoetherianRing A := IsLocalization.isNoetherianRing (SpecDvrSqGC3.mbar 𝔮 t.asIdeal).primeCompl A inferInstance
  have hdim : ringKrullDim A = 1 := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height (SpecDvrSqGC3.mbar 𝔮 t.asIdeal) A,
      SpecDvrSqGC3.height_mbar 𝔮 t.asIdeal hqm hneI hcov]
    rfl
  haveI : Finite (IsLocalRing.ResidueField A) := by
    haveI : Finite (C ⧸ t.asIdeal) := hfin t.asIdeal
    have e1 : (R₀ ⧸ SpecDvrSqGC3.mbar 𝔮 t.asIdeal) ≃+* A ⧸ IsLocalRing.maximalIdeal A :=
      IsLocalization.AtPrime.equivQuotMaximalIdeal (SpecDvrSqGC3.mbar 𝔮 t.asIdeal) A
    have e2 : (R₀ ⧸ SpecDvrSqGC3.mbar 𝔮 t.asIdeal) ≃+* C ⧸ t.asIdeal := DoubleQuot.quotQuotEquivQuotOfLE hqm
    exact Finite.of_equiv _ (e2.symm.trans e1).toEquiv

  let iK : C →+* K₀ := (algebraMap R₀ K₀).comp (Ideal.Quotient.mk 𝔮)
  have hiK : RingHom.ker iK = 𝔮 := by
    rw [← RingHom.comap_ker, (RingHom.injective_iff_ker_eq_bot _).mp (IsFractionRing.injective R₀ K₀),
      ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
  let XK := pullback g (Spec.map (CommRingCat.ofHom iK))
  haveI : JacobsonSpace XK := LocallyOfFiniteType.jacobsonSpace (pullback.snd g (Spec.map (CommRingCat.ofHom iK)))

  let pt : Spec (CommRingCat.of K₀) := IsLocalRing.closedPoint K₀
  have hpt : g.base x = (Spec.map (CommRingCat.ofHom iK)).base pt := by
    apply PrimeSpectrum.ext
    rw [Spec.map_apply]
    show 𝔮 = Ideal.comap iK (IsLocalRing.maximalIdeal K₀)
    rw [(IsLocalRing.isField_iff_maximalIdeal_eq).mp (Field.toIsField K₀), ← RingHom.ker_eq_comap_bot, hiK]
  obtain ⟨x', hx'1, -⟩ := Scheme.Pullback.exists_preimage_pullback x pt hpt

  obtain ⟨z', hz'cl, hz'c⟩ := nonempty_inter_closedPoints (Z := closure {x'}) ⟨x', subset_closure rfl⟩
    isClosed_closure.isLocallyClosed
  rw [mem_closedPoints_iff] at hz'c
  have hxz : x ⤳ (pullback.fst g (Spec.map (CommRingCat.ofHom iK))).base z' := by
    rw [← hx'1]
    exact (specializes_iff_mem_closure.mpr hz'cl).map (pullback.fst g _).continuous

  let L : Type u := XK.residueField z'
  let ψ : CommRingCat.of K₀ ⟶ XK.residueField z' :=
    Spec.preimage (XK.fromSpecResidueField z' ≫ pullback.snd g (Spec.map (CommRingCat.ofHom iK)))
  have hψ : Spec.map ψ = XK.fromSpecResidueField z' ≫ pullback.snd g _ := Spec.map_preimage _
  haveI : IsClosedImmersion (XK.fromSpecResidueField z') := isClosed_singleton_iff_isClosedImmersion.mp hz'c
  have hfinψ : ψ.hom.Finite := by
    rw [← IsFinite.SpecMap_iff, hψ]
    exact (isFinite_iff_locallyOfFiniteType_of_jacobsonSpace).mpr inferInstance
  letI algKL : Algebra K₀ L := ψ.hom.toAlgebra
  haveI : Module.Finite K₀ L := hfinψ
  letI algAL : Algebra A L := (ψ.hom.comp (algebraMap A K₀)).toAlgebra
  haveI : IsScalarTower A K₀ L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)

  obtain ⟨V, hVdvr, hVsub, hVdom, hVfin⟩ :=
    IsLocalRing.exists_valuationSubring_isDiscreteValuationRing_dominates_finite_residueField (A := A) hdim (K := K₀) (L := L)
  let jV : A →+* ↥V := (algebraMap A L).codRestrict V hVsub
  let φC : C →+* ↥V := jV.comp ((algebraMap R₀ A).comp (Ideal.Quotient.mk 𝔮))

  have hcomm : ψ.hom.comp iK = (algebraMap (↥V) L).comp φC := by
    ext c
    show ψ.hom (algebraMap R₀ K₀ (Ideal.Quotient.mk 𝔮 c)) = algebraMap A L (algebraMap R₀ A (Ideal.Quotient.mk 𝔮 c))
    rw [RingHom.algebraMap_toAlgebra, RingHom.comp_apply, ← IsScalarTower.algebraMap_apply R₀ A K₀]
  have w : (XK.fromSpecResidueField z' ≫ pullback.fst g (Spec.map (CommRingCat.ofHom iK))) ≫ g =
      Spec.map (CommRingCat.ofHom (algebraMap (↥V) L)) ≫ Spec.map (CommRingCat.ofHom φC) := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, ← hψ, ← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext1
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom]
    exact hcomm
  let Sq : ValuativeCommSq g :=
    ValuativeCommSq.mk (R := ↥V) (K := L) (XK.fromSpecResidueField z' ≫ pullback.fst g (Spec.map (CommRingCat.ofHom iK)))
      (Spec.map (CommRingCat.ofHom φC)) ⟨w⟩
  refine ⟨Sq, hVdvr, hVfin, ?_, ?_⟩
  ·
    apply PrimeSpectrum.ext
    show ((Spec.map (CommRingCat.ofHom φC)).base (IsLocalRing.closedPoint ↥V)).asIdeal = t.asIdeal
    rw [Spec.map_apply]
    show Ideal.comap φC (IsLocalRing.maximalIdeal ↥V) = t.asIdeal
    have h1 : Ideal.comap jV (IsLocalRing.maximalIdeal ↥V) = IsLocalRing.maximalIdeal A := by
      ext a
      rw [Ideal.mem_comap, hVdom a, ← ValuationSubring.coe_mem_nonunits_iff]
      rfl
    rw [show Ideal.comap φC (IsLocalRing.maximalIdeal ↥V) =
        ((Ideal.comap jV (IsLocalRing.maximalIdeal ↥V)).comap (algebraMap R₀ A)).comap (Ideal.Quotient.mk 𝔮) by
      rw [Ideal.comap_comap, Ideal.comap_comap], h1]
    rw [← Ideal.under_def, Localization.AtPrime.under_maximalIdeal]
    exact SpecDvrSqGC3.comap_mbar 𝔮 t.asIdeal hqm
  ·
    rintro _ ⟨p, rfl⟩
    rw [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]
    exact specializes_iff_mem_closure.mp hxz

end S_AlgebraicGeometry_exists_valuativeCommSq_isDiscreteValuationRing_finite_residueField_of_specializes
end P2MW
export P2MW.S_AlgebraicGeometry_exists_valuativeCommSq_isDiscreteValuationRing_finite_residueField_of_specializes (solution)
