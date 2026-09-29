-- Prove2me | solution 1 for AlgebraicGeometry.exists_closure_eq_preimage_closure_and_ringKrullDim_stalk_eq_of_flat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/6124d715-cafa-58ee-b70c-72ec7bab99d3

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_closure_eq_preimage_closure_and_ringKrullDim_stalk_eq_of_flat

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace Topology

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_apply Scheme.Hom GeometricallyIrreducible IsAffineOpen.SpecMap_appLE_fromSpec LocallyOfFiniteType Spec Scheme UniversallyOpen Scheme.Hom.comp_base Flat HasRingHomProperty.appLE exists_isAffineOpen_mem_and_subset isAffineOpen_top IsAffineOpen Flat.generalizingMap HasRingHomProperty Scheme.Hom.isIrreducible_preimage geometrically Scheme.ΓSpecIso"
namespace GenericFibreDim
p2m_open "AlgebraicGeometry"

variable {k : Type u} [Field k]

noncomputable abbrev chartAlgebra {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    (U : X.Opens) : Algebra k Γ(X, U) :=
  ((f.appLE ⊤ U le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom).toAlgebra

theorem chart_finiteType {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType f] {U : X.Opens} (hU : IsAffineOpen U) :
    letI := chartAlgebra f U
    Algebra.FiniteType k Γ(X, U) := by
  have h1 : (f.appLE ⊤ U le_top).hom.FiniteType :=
    f.finiteType_appLE (isAffineOpen_top _) hU le_top
  have h2 : (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom.FiniteType :=
    RingHom.FiniteType.of_surjective _
      (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.symm.surjective
  exact h1.comp h2

theorem chart_isNoetherianRing {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType f] {U : X.Opens} (hU : IsAffineOpen U) :
    IsNoetherianRing Γ(X, U) := by
  letI := chartAlgebra f U
  haveI := chart_finiteType f hU
  exact Algebra.FiniteType.isNoetherianRing k Γ(X, U)

theorem primeIdealOf_fromSpec {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U)
    (q : PrimeSpectrum Γ(X, U)) (h : hU.fromSpec q ∈ U) :
    hU.primeIdealOf ⟨hU.fromSpec q, h⟩ = q := by
  apply hU.fromSpec.isOpenEmbedding.injective
  exact hU.fromSpec_primeIdealOf ⟨hU.fromSpec q, h⟩

theorem ringKrullDim_stalk_eq_height {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U)
    (x : X) (hx : x ∈ U) :
    ringKrullDim (X.presheaf.stalk x) = (hU.primeIdealOf ⟨x, hx⟩).asIdeal.height := by
  letI := X.presheaf.algebra_section_stalk (⟨x, hx⟩ : U)
  haveI := hU.isLocalization_stalk ⟨x, hx⟩
  exact IsLocalization.AtPrime.ringKrullDim_eq_height (hU.primeIdealOf ⟨x, hx⟩).asIdeal
    (X.presheaf.stalk x)

section Generic

variable {G P : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k)) (p : P ⟶ Spec (CommRingCat.of k))

theorem exists_isGenericPoint [UniversallyOpen f] [GeometricallyIrreducible f] [Flat f] (w : P) :
    ∃ ζ : ↥(pullback f p),
      IsGenericPoint ζ ((pullback.snd f p).base ⁻¹' closure ({w} : Set P)) ∧
      (pullback.snd f p).base ζ = w := by
  set g := pullback.snd f p with hg
  have hT : IsIrreducible ((g.base : ↥(pullback f p) → P) ⁻¹' closure ({w} : Set P)) :=
    g.isIrreducible_preimage g.isOpenMap isIrreducible_singleton.closure
  have hTc : IsClosed ((g.base : ↥(pullback f p) → P) ⁻¹' closure ({w} : Set P)) :=
    isClosed_closure.preimage g.continuous
  obtain ⟨ζ, hζ⟩ := QuasiSober.sober hT hTc
  refine ⟨ζ, hζ, ?_⟩

  have hζT : ζ ∈ (g.base : ↥(pullback f p) → P) ⁻¹' closure ({w} : Set P) := hζ.mem
  have hwy : w ⤳ g.base ζ := specializes_iff_mem_closure.mpr hζT
  have hgen : GeneralizingMap g := Flat.generalizingMap g
  obtain ⟨ζ', hζ'ζ, hζ'w⟩ := hgen hwy
  have hζ'T : ζ' ∈ (g.base : ↥(pullback f p) → P) ⁻¹' closure ({w} : Set P) := by
    show g.base ζ' ∈ closure ({w} : Set P)
    rw [hζ'w]; exact subset_closure rfl
  have hζζ' : ζ ⤳ ζ' := hζ.specializes hζ'T
  have : ζ' = ζ := (hζ'ζ.antisymm hζζ').eq
  rw [← this]; exact hζ'w

end Generic

section Heights

variable {G P : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k)) (p : P ⟶ Spec (CommRingCat.of k))

theorem height_eq [Flat f] [LocallyOfFiniteType f] [LocallyOfFiniteType p] (w : P)
    (ζ : ↥(pullback f p))
    (hζ : IsGenericPoint ζ ((pullback.snd f p).base ⁻¹' closure ({w} : Set P)))
    (hζw : (pullback.snd f p).base ζ = w)
    {V : P.Opens} (hV : IsAffineOpen V) (hwV : w ∈ V)
    {U : (pullback f p).Opens} (hU : IsAffineOpen U) (hζU : ζ ∈ U)
    (hUV : U ≤ (pullback.snd f p) ⁻¹ᵁ V) :
    (hU.primeIdealOf ⟨ζ, hζU⟩).asIdeal.height = (hV.primeIdealOf ⟨w, hwV⟩).asIdeal.height := by
  set g : pullback f p ⟶ P := pullback.snd f p with hg

  let φ : Γ(P, V) →+* Γ(pullback f p, U) := (g.appLE V U hUV).hom
  have hφ : φ.Flat :=
    HasRingHomProperty.appLE @Flat g (inferInstance : Flat g) ⟨V, hV⟩ ⟨U, hU⟩ hUV
  letI : Algebra Γ(P, V) Γ(pullback f p, U) := φ.toAlgebra
  haveI : Module.Flat Γ(P, V) Γ(pullback f p, U) := hφ
  haveI : Algebra.HasGoingDown Γ(P, V) Γ(pullback f p, U) := inferInstance
  haveI : IsNoetherianRing Γ(P, V) := chart_isNoetherianRing p hV
  haveI : IsNoetherianRing Γ(pullback f p, U) := chart_isNoetherianRing (pullback.fst f p ≫ f) hU
  set Q : PrimeSpectrum Γ(pullback f p, U) := hU.primeIdealOf ⟨ζ, hζU⟩ with hQ
  set pw : PrimeSpectrum Γ(P, V) := hV.primeIdealOf ⟨w, hwV⟩ with hpw

  have hcomap : ∀ q : PrimeSpectrum Γ(pullback f p, U),
      hV.fromSpec (PrimeSpectrum.comap φ q) = g.base (hU.fromSpec q) := by
    intro q
    have h1 := IsAffineOpen.SpecMap_appLE_fromSpec g hV hU hUV
    have h2 := congrArg (fun h => h.base q) h1
    simp only [Scheme.Hom.comp_base, TopCat.comp_app] at h2
    rw [Spec.map_apply] at h2
    exact h2
  have hmemU : ∀ q : PrimeSpectrum Γ(pullback f p, U), hU.fromSpec q ∈ U := fun q => by
    have := hU.range_fromSpec ▸ Set.mem_range_self (f := hU.fromSpec) q
    exact this
  have hmemV : ∀ q : PrimeSpectrum Γ(P, V), hV.fromSpec q ∈ V := fun q => by
    have := hV.range_fromSpec ▸ Set.mem_range_self (f := hV.fromSpec) q
    exact this
  have hζQ : hU.fromSpec Q = ζ := hU.fromSpec_primeIdealOf ⟨ζ, hζU⟩
  have hwpw : hV.fromSpec pw = w := hV.fromSpec_primeIdealOf ⟨w, hwV⟩

  have hunder : PrimeSpectrum.comap φ Q = pw := by
    have h1 : hV.fromSpec (PrimeSpectrum.comap φ Q) = w := by rw [hcomap, hζQ, hζw]
    have h2 := primeIdealOf_fromSpec hV (PrimeSpectrum.comap φ Q) (hmemV _)
    rw [← h2]

    have : (⟨hV.fromSpec (PrimeSpectrum.comap φ Q), hmemV _⟩ : V) = ⟨w, hwV⟩ := Subtype.ext h1
    rw [this]
  haveI hlies : Q.asIdeal.LiesOver pw.asIdeal := by
    refine ⟨?_⟩
    rw [Ideal.under_def]
    have := congrArg PrimeSpectrum.asIdeal hunder
    have h__af := this.symm
    simp [PrimeSpectrum.comap_asIdeal] at h__af
    exact h__af

  have hmin : ∀ Q' : PrimeSpectrum Γ(pullback f p, U), pw.asIdeal.map φ ≤ Q'.asIdeal → Q' ≤ Q → Q' = Q := by
    intro Q' hJ hle

    set ζ' : ↥(pullback f p) := hU.fromSpec Q' with hζ'
    have hζ'ζ : ζ' ⤳ ζ := by
      have := ((PrimeSpectrum.le_iff_specializes _ _).mp hle).map hU.fromSpec.continuous
      rwa [hζQ] at this

    have hpw' : pw ≤ PrimeSpectrum.comap φ Q' := by
      rw [← PrimeSpectrum.asIdeal_le_asIdeal, PrimeSpectrum.comap_asIdeal, ← Ideal.map_le_iff_le_comap]
      exact hJ
    have hgζ' : g.base ζ' ∈ closure ({w} : Set P) := by
      have := ((PrimeSpectrum.le_iff_specializes _ _).mp hpw').map hV.fromSpec.continuous
      rw [hwpw, hcomap] at this
      exact specializes_iff_mem_closure.mp this
    have hζ'T : ζ' ∈ (g.base : ↥(pullback f p) → P) ⁻¹' closure ({w} : Set P) := hgζ'
    have hζζ' : ζ ⤳ ζ' := hζ.specializes hζ'T
    have heq : ζ' = ζ := (hζ'ζ.antisymm hζζ').eq

    have h1 := primeIdealOf_fromSpec hU Q' (hmemU _)
    rw [← h1]
    have : (⟨hU.fromSpec Q', hmemU _⟩ : U) = ⟨ζ, hζU⟩ := Subtype.ext heq
    rw [this]

  set J : Ideal Γ(pullback f p, U) := pw.asIdeal.map (algebraMap Γ(P, V) Γ(pullback f p, U)) with hJdef
  have hJφ : J = pw.asIdeal.map φ := rfl
  have hJQ : J ≤ Q.asIdeal := by
    rw [hJdef, Ideal.map_le_iff_le_comap]
    exact le_of_eq (hlies.over.symm ▸ rfl)
  have hfib : (Q.asIdeal.map (Ideal.Quotient.mk J)).height = 0 := by
    rw [Ideal.height_eq_zero_iff]
    haveI hQm : (Q.asIdeal.map (Ideal.Quotient.mk J)).IsPrime :=
      Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])
    refine ⟨⟨hQm, bot_le⟩, ?_⟩
    rintro q' ⟨hq', -⟩ hq'le

    haveI := hq'
    let Q' : PrimeSpectrum Γ(pullback f p, U) := ⟨q'.comap (Ideal.Quotient.mk J), inferInstance⟩
    have hJQ' : pw.asIdeal.map φ ≤ Q'.asIdeal := by
      show J ≤ q'.comap (Ideal.Quotient.mk J)
      intro x hx
      rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hx]
      exact q'.zero_mem
    have hQ'Q : Q' ≤ Q := by
      rw [← PrimeSpectrum.asIdeal_le_asIdeal]
      show q'.comap (Ideal.Quotient.mk J) ≤ Q.asIdeal
      intro x hx
      rw [Ideal.mem_comap] at hx
      have hx' : Ideal.Quotient.mk J x ∈ Q.asIdeal.map (Ideal.Quotient.mk J) := hq'le hx
      rw [Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective] at hx'
      obtain ⟨y, hy, hyx⟩ := hx'
      rw [Ideal.Quotient.eq, ← neg_sub] at hyx
      have hxy : x - y ∈ Q.asIdeal := hJQ ((neg_mem_iff).mp hyx)
      have := Q.asIdeal.add_mem hxy hy
      simpa using this
    have hEq : Q' = Q := hmin Q' hJQ' hQ'Q

    have hq'eq : q' = Q.asIdeal.map (Ideal.Quotient.mk J) := by
      have h1 : q' = (q'.comap (Ideal.Quotient.mk J)).map (Ideal.Quotient.mk J) :=
        (Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective q').symm
      rw [h1]
      show Q'.asIdeal.map _ = _
      rw [hEq]
    exact le_of_eq hq'eq.symm

  have hgd := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown pw.asIdeal Q.asIdeal
  rw [hfib, add_zero] at hgd
  exact hgd

end Heights

theorem main {G P : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k))
    (p : P ⟶ Spec (CommRingCat.of k))
    [GeometricallyIrreducible f] [LocallyOfFiniteType f] [LocallyOfFiniteType p] (w : P) :
    ∃ ζ : ↥(pullback f p),
      closure ({ζ} : Set ↥(pullback f p)) = (pullback.snd f p).base ⁻¹' closure ({w} : Set P) ∧
      (pullback.snd f p).base ζ = w ∧
      ringKrullDim ((pullback f p).presheaf.stalk ζ) = ringKrullDim (P.presheaf.stalk w) := by

  haveI : Flat f := inferInstance
  haveI : UniversallyOpen f := inferInstance
  obtain ⟨ζ, hζ, hζw⟩ := exists_isGenericPoint f p w
  refine ⟨ζ, hζ, hζw, ?_⟩

  obtain ⟨V, hV, hwV, -⟩ := exists_isAffineOpen_mem_and_subset (X := P) (x := w) (U := ⊤) trivial
  have hζV : ζ ∈ (pullback.snd f p) ⁻¹ᵁ V := by
    show (pullback.snd f p).base ζ ∈ V
    rw [hζw]; exact hwV
  obtain ⟨U, hU, hζU, hUV⟩ :=
    exists_isAffineOpen_mem_and_subset (X := pullback f p) (x := ζ) (U := (pullback.snd f p) ⁻¹ᵁ V) hζV
  rw [ringKrullDim_stalk_eq_height hU ζ hζU, ringKrullDim_stalk_eq_height hV w hwV,
    height_eq f p w ζ hζ hζw hV hwV hU hζU hUV]

end AlgebraicGeometry.GenericFibreDim

open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry _root_.P2MW.S_AlgebraicGeometry_exists_closure_eq_preimage_closure_and_ringKrullDim_stalk_eq_of_flat.AlgebraicGeometry in

theorem solution
    {k : Type u} [Field k] {G P : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k))
    (p : P ⟶ Spec (CommRingCat.of k))
    [GeometricallyIrreducible f] [LocallyOfFiniteType f] [LocallyOfFiniteType p] (w : P) :
    ∃ ζ : ↥(pullback f p),
      closure ({ζ} : Set ↥(pullback f p)) = (pullback.snd f p).base ⁻¹' closure ({w} : Set P) ∧
      (pullback.snd f p).base ζ = w ∧
      ringKrullDim ((pullback f p).presheaf.stalk ζ) = ringKrullDim (P.presheaf.stalk w) :=
  AlgebraicGeometry.GenericFibreDim.main f p w

end S_AlgebraicGeometry_exists_closure_eq_preimage_closure_and_ringKrullDim_stalk_eq_of_flat
end P2MW
export P2MW.S_AlgebraicGeometry_exists_closure_eq_preimage_closure_and_ringKrullDim_stalk_eq_of_flat (solution)
