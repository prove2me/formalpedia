-- Prove2me | solution 1 for AlgebraicGeometry.exists_isIrreducible_topologicalKrullDim_le_add_of_apply_eq_of_isClosed_singleton
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/61f0f81e-b2ee-54c4-9768-07ea128e72d3

import Mathlib
import Theorems.Thm_Ideal_height_add_ringKrullDim_quotient_eq_ringKrullDim_of_finiteType
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_isReduced_subscheme_vanishingIdeal_and_le_ker
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_isIrreducible_topologicalKrullDim_le_add_of_apply_eq_of_isClosed_singleton

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits TopologicalSpace Topology

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Surjective Scheme.Hom IsAffineOpen.SpecMap_appLE_fromSpec LocallyOfFiniteType Spec IsIntegral Spec.map Scheme Scheme.basicOpen_zero IsReduced exists_isAffineOpen_mem_and_subset isAffineOpen_top IsAffineOpen.comap_primeIdealOf_appLE IsAffineOpen.primeIdealOf IsAffineOpen Scheme.Hom.comp_apply range_eq_univ Scheme.IdealSheafData Scheme.ΓSpecIso isIntegral_of_irreducibleSpace_of_isReduced Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal_and_le_ker"
p2m_open "AlgebraicGeometry"

namespace FibreDimensionC1

section Algebra

theorem height_eq_ringKrullDim_of_isMaximal (k : Type u) [Field k] {A : Type v} [CommRing A]
    [IsDomain A] [Algebra k A] [Algebra.FiniteType k A] (m : Ideal A) [hm : m.IsMaximal] :
    (m.height : WithBot ℕ∞) = ringKrullDim A := by
  have h := Ideal.height_add_ringKrullDim_quotient_eq_ringKrullDim_of_finiteType k m
  have h0 : ringKrullDim (A ⧸ m) = 0 := by
    letI : Field (A ⧸ m) := Ideal.Quotient.field m
    exact ringKrullDim_eq_zero_of_field (A ⧸ m)
  rwa [h0, add_zero] at h

theorem exists_ringKrullDim_eq_natCast (k : Type u) {A : Type v} [Field k] [CommRing A]
    [IsDomain A] [Algebra k A] [Algebra.FiniteType k A] : ∃ n : ℕ, ringKrullDim A = n := by
  haveI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  obtain ⟨m, hm⟩ := Ideal.exists_maximal A
  have hfin : m.height ≠ ⊤ := by
    haveI : m.FiniteHeight := inferInstance
    exact Ideal.height_ne_top hm.ne_top
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hfin
  refine ⟨n, ?_⟩
  rw [← height_eq_ringKrullDim_of_isMaximal k m, ← hn]
  rfl

theorem ringKrullDim_le_ringKrullDim_localization (k : Type u) [Field k] {A : Type v} [CommRing A]
    [IsDomain A] [Algebra k A] [Algebra.FiniteType k A] {g : A} (hg : g ≠ 0)
    (L : Type v) [CommRing L] [Algebra A L] [IsLocalization.Away g L] :
    ringKrullDim A ≤ ringKrullDim L := by
  haveI : IsJacobsonRing A := isJacobsonRing_of_finiteType (A := k) (B := A)

  have hjac : (⊥ : Ideal A).jacobson = ⊥ := by
    rw [← Ideal.radical_eq_jacobson, Ideal.radical_bot_of_noZeroDivisors]
  have hg' : g ∉ (⊥ : Ideal A).jacobson := by rw [hjac]; simpa using hg
  rw [Ideal.jacobson, Ideal.mem_sInf] at hg'
  simp only [Set.mem_setOf_eq, not_forall, exists_prop] at hg'
  obtain ⟨M, ⟨-, hM⟩, hgM⟩ := hg'
  haveI : M.IsMaximal := hM

  have hdisj : Disjoint ((Submonoid.powers g : Submonoid A) : Set A) (M : Set A) := by
    rw [Set.disjoint_left]
    rintro _ ⟨n, rfl⟩ hn
    exact hgM (hM.isPrime.mem_of_pow_mem n hn)
  have hMap : (M.map (algebraMap A L)).height = M.height :=
    IsLocalization.height_map_of_disjoint (Submonoid.powers g) M hdisj
  haveI : (M.map (algebraMap A L)).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers g) L M hM.isPrime hdisj
  calc ringKrullDim A = M.height := (height_eq_ringKrullDim_of_isMaximal k M).symm
    _ = (M.map (algebraMap A L)).height := by rw [hMap]
    _ ≤ ringKrullDim L := Ideal.height_le_ringKrullDim_of_isPrime

theorem exists_minimalPrime_ringKrullDim_le (k : Type u) [Field k] {A : Type v} [CommRing A]
    [IsDomain A] [Algebra k A] [Algebra.FiniteType k A] {B : Type v} [CommRing B]
    [IsNoetherianRing B] (φ : B →+* A) (P : Ideal A) [P.IsPrime] (m : Ideal B) [hm : m.IsMaximal]
    (hmP : m = P.comap φ) :
    ∃ Q : Ideal A, Q.IsPrime ∧ Q ≤ P ∧ m.map φ ≤ Q ∧
      ringKrullDim A ≤ ringKrullDim (A ⧸ Q) +
        ((m.map (Ideal.Quotient.mk (RingHom.ker φ))).height : WithBot ℕ∞) := by
  haveI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A

  set J : Ideal A := m.map φ with hJ
  have hJP : J ≤ P := by rw [hJ, Ideal.map_le_iff_le_comap, hmP]
  obtain ⟨Q, hQmin, hQP⟩ := Ideal.exists_minimalPrimes_le hJP
  haveI hQ : Q.IsPrime := hQmin.1.1
  have hJQ : J ≤ Q := hQmin.1.2
  refine ⟨Q, hQ, hQP, hJQ, ?_⟩

  set I : Ideal B := RingHom.ker φ with hI
  let ψ : B ⧸ I →+* A := RingHom.kerLift φ
  have hψmk : ψ.comp (Ideal.Quotient.mk I) = φ := RingHom.ext fun b => RingHom.kerLift_mk φ b
  letI : Algebra (B ⧸ I) A := ψ.toAlgebra

  set m' : Ideal (B ⧸ I) := m.map (Ideal.Quotient.mk I) with hm'
  have hIm : I ≤ m := by
    rw [hmP, hI, RingHom.ker_eq_comap_bot]
    exact Ideal.comap_mono bot_le
  have hm'c : m'.comap (Ideal.Quotient.mk I) = m := by
    rw [hm', Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
      Ideal.mk_ker, sup_eq_left.mpr hIm]
  haveI hm'max : m'.IsMaximal := by
    refine (Ideal.map_eq_top_or_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective hm).resolve_left ?_
    intro htop
    apply hm.ne_top
    rw [← hm'c]
    change Ideal.comap (Ideal.Quotient.mk I) (Ideal.map (Ideal.Quotient.mk I) m) = ⊤
    rw [htop, Ideal.comap_top]
  have hm'J : m'.map (algebraMap (B ⧸ I) A) = J := by
    show (m.map (Ideal.Quotient.mk I)).map ψ = m.map φ
    rw [Ideal.map_map, hψmk]
  haveI : Q.LiesOver m' := by
    refine ⟨(hm'max.eq_of_le ?_ ?_)⟩
    · exact Ideal.IsPrime.ne_top inferInstance
    · rw [Ideal.under_def, ← Ideal.map_le_iff_le_comap, hm'J]
      exact hJQ

  have hkrull := Ideal.height_le_height_add_of_liesOver m' Q
  rw [hm'J] at hkrull
  have hQJ : (Q.map (Ideal.Quotient.mk J)).height = 0 := by
    obtain ⟨q, hq, hqQ⟩ : ∃ q ∈ minimalPrimes (A ⧸ J), Ideal.comap (Ideal.Quotient.mk J) q = Q := by
      have : Q ∈ Ideal.comap (Ideal.Quotient.mk J) '' minimalPrimes (A ⧸ J) := by
        rw [← Ideal.minimalPrimes_eq_comap]; exact hQmin
      exact this
    have hqeq : Q.map (Ideal.Quotient.mk J) = q := by
      rw [← hqQ, Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective]
    haveI : q.IsPrime := hq.1.1
    rw [hqeq]
    exact Ideal.height_eq_zero_iff.mpr hq
  rw [hQJ, add_zero] at hkrull

  have hdimf := Ideal.height_add_ringKrullDim_quotient_eq_ringKrullDim_of_finiteType k Q
  rw [← hdimf, add_comm]
  have hk' : ((Q.height : ℕ∞) : WithBot ℕ∞) ≤ ((m'.height : ℕ∞) : WithBot ℕ∞) := by
    exact_mod_cast hkrull
  exact add_le_add_right hk' _

end Algebra

section TopologyB

attribute [local instance] specializationOrder

theorem topologicalKrullDim_le_of_forall_exists_isOpenEmbedding {X : Type u} [TopologicalSpace X]
    [QuasiSober X] [T0Space X] (n : WithBot ℕ∞)
    (h : ∀ x : X, ∃ (U : Type u) (_ : TopologicalSpace U) (g : U → X),
      IsOpenEmbedding g ∧ x ∈ Set.range g ∧ topologicalKrullDim U ≤ n) :
    topologicalKrullDim X ≤ n := by
  rw [topologicalKrullDim, Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := X)),
    Order.krullDim_eq_iSup_coheight]
  refine iSup_le fun x => ?_
  obtain ⟨U, _, g, hg, ⟨y, rfl⟩, hU⟩ := h x
  haveI : QuasiSober U := hg.quasiSober
  haveI : T0Space U := hg.isEmbedding.t0Space
  rw [hg.coheight_eq (x := y)]
  calc (↑(Order.coheight y) : WithBot ℕ∞) ≤ Order.krullDim U := Order.coheight_le_krullDim _
    _ = topologicalKrullDim U :=
        (Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := U))).symm
    _ ≤ n := hU

end TopologyB

section TopologyB2

theorem topologicalKrullDim_affineOpen {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U) :
    topologicalKrullDim ↥U = ringKrullDim Γ(X, U) := by
  have h : topologicalKrullDim (Spec Γ(X, U)) = ringKrullDim Γ(X, U) :=
    PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim _
  rw [← IsHomeomorph.topologicalKrullDim_eq _ hU.isoSpec.hom.homeomorph.isHomeomorph] at h
  exact h

theorem topologicalKrullDim_zeroLocus {A : Type u} [CommRing A] (I : Ideal A) :
    topologicalKrullDim (PrimeSpectrum.zeroLocus (I : Set A)) = ringKrullDim (A ⧸ I) := by
  have hce := PrimeSpectrum.isClosedEmbedding_comap_of_surjective (A ⧸ I) (Ideal.Quotient.mk I)
    Ideal.Quotient.mk_surjective
  have hr : Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk I)) =
      PrimeSpectrum.zeroLocus (I : Set A) := by
    rw [range_comap_of_surjective (A ⧸ I) _ Ideal.Quotient.mk_surjective, Ideal.mk_ker]
  let e : PrimeSpectrum (A ⧸ I) ≃ₜ PrimeSpectrum.zeroLocus (I : Set A) :=
    hce.isEmbedding.toHomeomorph.trans (Homeomorph.setCongr hr)
  rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim (A ⧸ I)]
  exact (IsHomeomorph.topologicalKrullDim_eq _ e.isHomeomorph).symm

theorem topologicalKrullDim_le_of_isEmbedding_image {X Y : Type u} [TopologicalSpace X]
    [TopologicalSpace Y] {f : X → Y} (hf : IsEmbedding f) (s : Set X) (t : Set Y)
    (hst : f '' s ⊆ t) : topologicalKrullDim s ≤ topologicalKrullDim t := by
  let φ : s → t := fun z => ⟨f z.1, hst ⟨z.1, z.2, rfl⟩⟩
  have hφ : IsInducing φ := (hf.isInducing.comp IsInducing.subtypeVal).codRestrict _
  exact Topology.IsInducing.topologicalKrullDim_le hφ

end TopologyB2

section Integral

variable {k : Type u} [Field k]

noncomputable abbrev chartAlgebra {X : Scheme.{u}} (fX : X ⟶ Spec (CommRingCat.of k)) (U : X.Opens) :
    Algebra k Γ(X, U) :=
  ((fX.appLE ⊤ U le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom).toAlgebra

theorem chart_finiteType {X : Scheme.{u}} (fX : X ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType fX] {U : X.Opens} (hU : IsAffineOpen U) :
    letI := chartAlgebra fX U
    Algebra.FiniteType k Γ(X, U) := by
  have h1 : (fX.appLE ⊤ U le_top).hom.FiniteType :=
    fX.finiteType_appLE (isAffineOpen_top _) hU le_top
  have h2 : (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom.FiniteType :=
    RingHom.FiniteType.of_surjective _
      (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.symm.surjective
  exact h1.comp h2

theorem topologicalKrullDim_le_ringKrullDim {X : Scheme.{u}} (fX : X ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType fX] [IsIntegral X] {U : X.Opens} (hU : IsAffineOpen U)
    (hUne : (U : Set X).Nonempty) :
    topologicalKrullDim X ≤ ringKrullDim Γ(X, U) := by
  refine topologicalKrullDim_le_of_forall_exists_isOpenEmbedding (X := X) _ fun ξ => ?_
  obtain ⟨U', hU', hξU', -⟩ := exists_isAffineOpen_mem_and_subset (X := X) (x := ξ) (U := ⊤) trivial
  refine ⟨↥U', inferInstance, Subtype.val, U'.2.isOpenEmbedding_subtypeVal, ⟨⟨ξ, hξU'⟩, rfl⟩, ?_⟩
  rw [topologicalKrullDim_affineOpen hU']

  obtain ⟨z, hzU, hzU'⟩ := nonempty_preirreducible_inter U.2 U'.2 hUne ⟨ξ, hξU'⟩
  obtain ⟨g, hgU, hzg⟩ := hU'.exists_basicOpen_le ⟨z, hzU⟩ hzU'
  have hg : g ≠ 0 := by
    rintro rfl
    rw [Scheme.basicOpen_zero] at hzg
    exact hzg

  haveI : Nonempty U' := ⟨⟨ξ, hξU'⟩⟩
  letI := chartAlgebra fX U'
  haveI := chart_finiteType fX hU'
  haveI := hU'.isLocalization_basicOpen g
  have h1 : ringKrullDim Γ(X, U') ≤ ringKrullDim Γ(X, X.basicOpen g) :=
    ringKrullDim_le_ringKrullDim_localization k hg _
  have h2 : ringKrullDim Γ(X, X.basicOpen g) = topologicalKrullDim ↥(X.basicOpen g) :=
    (topologicalKrullDim_affineOpen (hU'.basicOpen g)).symm
  have h3 : topologicalKrullDim ↥(X.basicOpen g) ≤ topologicalKrullDim ↥U :=
    Topology.IsInducing.topologicalKrullDim_le (IsEmbedding.inclusion hgU).isInducing
  rw [← topologicalKrullDim_affineOpen hU]
  exact h1.trans (h2.le.trans h3)

theorem main_integral {X Y : Scheme.{u}}
    (fX : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType fX] [IsIntegral X]
    (fY : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType fY]
    (o : X ⟶ Y) (_ho : o ≫ fY = fX) {y : ↥Y} (hy : IsClosed ({y} : Set ↥Y))
    {x : ↥X} (hx : o x = y) :
    ∃ Z : Set ↥X, x ∈ Z ∧ Z ⊆ o ⁻¹' {y} ∧ IsIrreducible Z ∧ IsClosed Z ∧
      topologicalKrullDim ↥X ≤
        topologicalKrullDim ↥Z + topologicalKrullDim ↥(closure (Set.range o)) := by

  obtain ⟨V, hV, hyV, -⟩ := exists_isAffineOpen_mem_and_subset (X := Y) (x := y) (U := ⊤) trivial
  have hxV : x ∈ o ⁻¹ᵁ V := by show o x ∈ V; rw [hx]; exact hyV
  obtain ⟨U, hU, hxU, hUV⟩ := exists_isAffineOpen_mem_and_subset hxV
  have hUV' : U ≤ o ⁻¹ᵁ V := hUV

  haveI : Nonempty U := ⟨⟨x, hxU⟩⟩
  letI algA := chartAlgebra fX U
  haveI : Algebra.FiniteType k Γ(X, U) := chart_finiteType fX hU
  haveI : IsNoetherianRing Γ(Y, V) := by
    letI := chartAlgebra fY V
    haveI : Algebra.FiniteType k Γ(Y, V) := chart_finiteType fY hV
    exact Algebra.FiniteType.isNoetherianRing k Γ(Y, V)
  let φ : Γ(Y, V) →+* Γ(X, U) := (o.appLE V U hUV').hom

  let px : PrimeSpectrum Γ(X, U) := hU.primeIdealOf ⟨x, hxU⟩
  let py : PrimeSpectrum Γ(Y, V) := hV.primeIdealOf ⟨y, hyV⟩
  haveI hmax : py.asIdeal.IsMaximal := hV.primeIdealOf_isMaximal_of_isClosed ⟨y, hyV⟩ hy
  have hcomap : px.comap φ = py := by
    have h := IsAffineOpen.comap_primeIdealOf_appLE (f := o) V hV U hU hUV' hxU

    have : (⟨o x, hUV' hxU⟩ : V) = ⟨y, hyV⟩ := Subtype.ext hx
    rw [this] at h
    exact h
  have hmP : py.asIdeal = px.asIdeal.comap φ := by
    rw [← hcomap]; rfl

  obtain ⟨Q, hQ, hQP, hmQ, hdim⟩ :=
    exists_minimalPrime_ringKrullDim_le k φ px.asIdeal py.asIdeal hmP

  let Z₀ : Set (PrimeSpectrum Γ(X, U)) := PrimeSpectrum.zeroLocus (Q : Set Γ(X, U))
  let ι : PrimeSpectrum Γ(X, U) → X := fun p => hU.fromSpec p
  have hιemb : IsOpenEmbedding ι := hU.fromSpec.isOpenEmbedding
  let Z : Set X := closure (ι '' Z₀)
  have hxZ₀ : px ∈ Z₀ := by
    show px ∈ PrimeSpectrum.zeroLocus (Q : Set Γ(X, U))
    rw [PrimeSpectrum.mem_zeroLocus]
    exact hQP
  have hιpx : ι px = x := hU.fromSpec_primeIdealOf ⟨x, hxU⟩
  refine ⟨Z, ?_, ?_, ?_, isClosed_closure, ?_⟩
  ·
    exact subset_closure ⟨px, hxZ₀, hιpx⟩
  ·
    refine closure_minimal ?_ (hy.preimage o.continuous)
    rintro _ ⟨p, hp, rfl⟩
    show o (hU.fromSpec p) = y
    have hsq := congrArg (fun f => f p) (congrArg (fun f : Spec Γ(X, U) ⟶ Y => (f : _ → Y))
      (IsAffineOpen.SpecMap_appLE_fromSpec o hV hU hUV'))
    simp only [Scheme.Hom.comp_apply] at hsq
    rw [← hsq]

    have hcp : PrimeSpectrum.comap φ p = py := by
      apply PrimeSpectrum.ext
      refine (hmax.eq_of_le (Ideal.IsPrime.ne_top inferInstance) ?_).symm
      rw [PrimeSpectrum.comap_asIdeal, ← Ideal.map_le_iff_le_comap]
      exact hmQ.trans ((PrimeSpectrum.mem_zeroLocus _ _).mp hp)
    have : Spec.map (o.appLE V U hUV') p = py := hcp
    rw [this]
    exact hV.fromSpec_primeIdealOf ⟨y, hyV⟩
  ·
    refine IsIrreducible.closure (IsIrreducible.image ?_ ι hιemb.continuous.continuousOn)
    rw [PrimeSpectrum.isIrreducible_zeroLocus_iff, Ideal.IsPrime.radical hQ]
    exact hQ
  ·
    have hX : topologicalKrullDim X ≤ ringKrullDim Γ(X, U) :=
      topologicalKrullDim_le_ringKrullDim fX hU ⟨x, hxU⟩
    have hZ : ringKrullDim (Γ(X, U) ⧸ Q) ≤ topologicalKrullDim Z := by
      rw [← topologicalKrullDim_zeroLocus Q]
      exact topologicalKrullDim_le_of_isEmbedding_image hιemb.isEmbedding Z₀ Z subset_closure
    have hI : ((Ideal.map (Ideal.Quotient.mk (RingHom.ker φ)) py.asIdeal).height : WithBot ℕ∞) ≤
        topologicalKrullDim (closure (Set.range o)) := by
      refine (Ideal.height_le_ringKrullDim_of_ne_top ?_).trans ?_
      ·
        intro htop
        apply hmax.ne_top
        have hIm : RingHom.ker φ ≤ py.asIdeal := by
          rw [hmP, RingHom.ker_eq_comap_bot]; exact Ideal.comap_mono bot_le
        have := congrArg (Ideal.comap (Ideal.Quotient.mk (RingHom.ker φ))) htop
        rwa [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
          Ideal.mk_ker, sup_eq_left.mpr hIm, Ideal.comap_top] at this
      ·
        rw [← topologicalKrullDim_zeroLocus (RingHom.ker φ), ← PrimeSpectrum.closure_range_comap]
        let ιV : PrimeSpectrum Γ(Y, V) → Y := fun p => hV.fromSpec p
        have hιV : IsOpenEmbedding ιV := hV.fromSpec.isOpenEmbedding
        refine topologicalKrullDim_le_of_isEmbedding_image hιV.isEmbedding _ _ ?_
        refine (image_closure_subset_closure_image hιV.continuous).trans (closure_mono ?_)
        rintro _ ⟨_, ⟨p, rfl⟩, rfl⟩
        refine ⟨ι p, ?_⟩
        have hsq := congrArg (fun f => f p) (congrArg (fun f : Spec Γ(X, U) ⟶ Y => (f : _ → Y))
          (IsAffineOpen.SpecMap_appLE_fromSpec o hV hU hUV'))
        simp only [Scheme.Hom.comp_apply] at hsq
        exact hsq.symm
    calc topologicalKrullDim X ≤ ringKrullDim Γ(X, U) := hX
      _ ≤ ringKrullDim (Γ(X, U) ⧸ Q) +
          ((Ideal.map (Ideal.Quotient.mk (RingHom.ker φ)) py.asIdeal).height : WithBot ℕ∞) := hdim
      _ ≤ topologicalKrullDim Z + topologicalKrullDim (closure (Set.range o)) := add_le_add hZ hI

end Integral

section Reduction

open AlgebraicGeometry.Scheme.IdealSheafData

variable {k : Type u} [Field k]

theorem main {X Y : Scheme.{u}}
    (fX : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType fX] [IrreducibleSpace ↥X]
    (fY : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType fY]
    (o : X ⟶ Y) (ho : o ≫ fY = fX) {y : ↥Y} (hy : IsClosed ({y} : Set ↥Y))
    {x : ↥X} (hx : o x = y) :
    ∃ Z : Set ↥X, x ∈ Z ∧ Z ⊆ o ⁻¹' {y} ∧ IsIrreducible Z ∧ IsClosed Z ∧
      topologicalKrullDim ↥X ≤
        topologicalKrullDim ↥Z + topologicalKrullDim ↥(closure (Set.range o)) := by

  let Xr : Scheme.{u} := (vanishingIdeal (⊤ : Closeds X)).subscheme
  let ι : Xr ⟶ X := (vanishingIdeal (⊤ : Closeds X)).subschemeι
  haveI : IsReduced Xr :=
    (AlgebraicGeometry.Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal_and_le_ker
      (⊤ : Closeds X)).1
  have hrange : Set.range ι = Set.univ := by
    show Set.range (vanishingIdeal (⊤ : Closeds X)).subschemeι = Set.univ
    rw [range_subschemeι]
    apply Set.eq_univ_of_univ_subset
    have : (⊤ : Closeds X) ≤ (vanishingIdeal (⊤ : Closeds X)).support :=
      le_support_iff_le_vanishingIdeal.mpr le_rfl
    exact this
  have hsurj : Function.Surjective ι := Set.range_eq_univ.mp hrange
  have hemb : IsEmbedding ι := ι.isClosedEmbedding.isEmbedding
  let e : Xr ≃ₜ X := hemb.toHomeomorphOfSurjective hsurj
  have he : ∀ z, e z = ι z := fun z => rfl
  haveI : IrreducibleSpace Xr := e.irreducibleSpace_iff.mpr inferInstance
  haveI : IsIntegral Xr := isIntegral_of_irreducibleSpace_of_isReduced Xr

  obtain ⟨x', hx'⟩ := hsurj x
  have hx'' : (ι ≫ o) x' = y := by rw [Scheme.Hom.comp_apply, hx', hx]
  obtain ⟨Z', hxZ', hZ'fib, hZ'irr, hZ'cl, hdim⟩ :=
    main_integral (ι ≫ fX) fY (ι ≫ o) (by rw [Category.assoc, ho]) hy hx''
  refine ⟨ι '' Z', ⟨x', hxZ', hx'⟩, ?_, hZ'irr.image _ ι.continuous.continuousOn,
    ι.isClosedEmbedding.isClosedMap _ hZ'cl, ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    have := hZ'fib hz
    rwa [Set.mem_preimage, Scheme.Hom.comp_apply] at this
  · have h1 : topologicalKrullDim X = topologicalKrullDim Xr :=
      (IsHomeomorph.topologicalKrullDim_eq _ e.isHomeomorph).symm
    have h2 : topologicalKrullDim Z' ≤ topologicalKrullDim (ι '' Z') :=
      topologicalKrullDim_le_of_isEmbedding_image hemb Z' _ le_rfl
    have h3 : closure (Set.range (ι ≫ o)) = closure (Set.range o) := by
      congr 1
      ext z
      simp only [Set.mem_range, Scheme.Hom.comp_apply]
      constructor
      · rintro ⟨w, rfl⟩; exact ⟨_, rfl⟩
      · rintro ⟨w, rfl⟩
        obtain ⟨w', rfl⟩ := hsurj w
        exact ⟨w', rfl⟩
    rw [h1, ← h3]
    exact hdim.trans (add_le_add h2 le_rfl)

end Reduction

end FibreDimensionC1

end AlgebraicGeometry

p2m_open "CategoryTheory AlgebraicGeometry P2MW.S_AlgebraicGeometry_exists_isIrreducible_topologicalKrullDim_le_add_of_apply_eq_of_isClosed_singleton.AlgebraicGeometry"

theorem solution
    {k : Type u} [Field k] {X Y : Scheme.{u}}
    (fX : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType fX] [IrreducibleSpace ↥X]
    (fY : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType fY]
    (o : X ⟶ Y) (ho : o ≫ fY = fX) {y : ↥Y} (hy : IsClosed ({y} : Set ↥Y))
    {x : ↥X} (hx : o x = y) :
    ∃ Z : Set ↥X, x ∈ Z ∧ Z ⊆ o ⁻¹' {y} ∧ IsIrreducible Z ∧ IsClosed Z ∧
      topologicalKrullDim ↥X ≤
        topologicalKrullDim ↥Z + topologicalKrullDim ↥(closure (Set.range o)) :=
  AlgebraicGeometry.FibreDimensionC1.main fX fY o ho hy hx

end S_AlgebraicGeometry_exists_isIrreducible_topologicalKrullDim_le_add_of_apply_eq_of_isClosed_singleton
end P2MW
export P2MW.S_AlgebraicGeometry_exists_isIrreducible_topologicalKrullDim_le_add_of_apply_eq_of_isClosed_singleton (solution)
