-- Prove2me | solution 1 for AlgebraicGeometry.exists_specializes_of_closed_of_specialFibre_of_flat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/6bdf1a2c-c153-5508-b28c-a52762968fc8

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_exists_specializes_of_closed_of_specialFibre_of_flat

set_option autoImplicit false

p2m_open "CategoryTheory AlgebraicGeometry P2MW.S_AlgebraicGeometry_exists_specializes_of_closed_of_specialFibre_of_flat.AlgebraicGeometry IsLocalRing Topology TopologicalSpace"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp IsLocallyNoetherian Scheme.fromSpecStalk_closedPoint Spec.map_apply IsProper LocallyOfFiniteType.isLocallyNoetherian Scheme.Hom Scheme.Hom.range_fiberι Scheme.range_fromSpecStalk Scheme.Hom.fiber LocallyOfFiniteType Spec IsIntegral Spec.map Scheme Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber Scheme.Hom.fiberι_asFiber Flat Scheme.Hom.isOpen_quasiFiniteAt Scheme.SpecMap_stalkMap_fromSpecStalk IsNoetherian LocallyOfFinitePresentation Scheme.Hom.comp_apply Spec.fromSpecStalk_eq Scheme.ΓSpecIso"
namespace PureDimOneAux
p2m_open "AlgebraicGeometry"

section LocalAlgebra

variable {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]

theorem eq_bot_of_lt_of_mem_minimalPrimes_span_singleton (a : R) (Q : Ideal R) [Q.IsPrime]
    (hmin : Q ∈ (Ideal.span {a}).minimalPrimes) (P : Ideal R) [P.IsPrime] (hlt : P < Q) :
    P = ⊥ := by
  have h1 : Q.height ≤ 1 :=
    Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes (Ideal.span {a}) Q hmin
  have h1' : Q.height ≤ ((1 : ℕ) : ℕ∞) := by simpa using h1
  have h2 : P.height < ((1 : ℕ) : ℕ∞) := Ideal.height_le_iff.mp h1' P ‹_› hlt
  have h3 : P.height = 0 := by
    have : P.height < 1 := by simpa using h2
    exact ENat.lt_one_iff_eq_zero.mp this
  have h4 : P ∈ minimalPrimes R := Ideal.height_eq_zero_iff.mp h3
  exact le_bot_iff.mp (h4.2 ⟨Ideal.isPrime_bot, bot_le⟩ bot_le)

theorem false_of_mem_forall_prime_of_lt_of_lt (ϖ : R) (hϖ : ϖ ≠ 0)
    (hall : ∀ P : Ideal R, P.IsPrime → P ≠ ⊥ → ϖ ∈ P)
    (P Q : Ideal R) [P.IsPrime] [Q.IsPrime] (h₁ : P ≠ ⊥) (h₂ : P < Q) : False := by
  classical
  have hQne : Q ≠ ⊥ := ne_bot_of_gt h₂

  have hQnot : Q ∉ (Ideal.span {ϖ}).minimalPrimes := fun hmin =>
    h₁ (eq_bot_of_lt_of_mem_minimalPrimes_span_singleton ϖ Q hmin P h₂)

  have hfin : (Ideal.span {ϖ}).minimalPrimes.Finite :=
    Ideal.finite_minimalPrimes_of_isNoetherianRing R (Ideal.span {ϖ})
  have hspan_ne_top : Ideal.span {ϖ} ≠ ⊤ := by
    intro htop
    have hϖQ : ϖ ∈ Q := hall Q ‹_› hQne
    have : Ideal.span {ϖ} ≤ Q := (Ideal.span_singleton_le_iff_mem Q).mpr hϖQ
    exact (‹Q.IsPrime›.ne_top) (top_le_iff.mp (htop ▸ this))
  obtain ⟨J₀, hJ₀⟩ := Ideal.nonempty_minimalPrimes hspan_ne_top
  have hJ₀' : J₀ ∈ hfin.toFinset := hfin.mem_toFinset.mpr hJ₀

  have havoid : ¬ ((Q : Set R) ⊆ ⋃ J ∈ (hfin.toFinset : Set (Ideal R)), (J : Set R)) := by
    intro hsub
    have hprime : ∀ J ∈ hfin.toFinset, J ≠ J₀ → J ≠ J₀ → J.IsPrime :=
      fun J hJ _ _ => (hfin.mem_toFinset.mp hJ).1.1
    obtain ⟨J, hJ, hQJ⟩ := (Ideal.subset_union_prime J₀ J₀ hprime).mp hsub
    have hJmin : J ∈ (Ideal.span {ϖ}).minimalPrimes := hfin.mem_toFinset.mp hJ
    haveI : J.IsPrime := hJmin.1.1
    rcases eq_or_lt_of_le hQJ with h | hlt
    · exact hQnot (h ▸ hJmin)
    · exact hQne (eq_bot_of_lt_of_mem_minimalPrimes_span_singleton ϖ J hJmin Q hlt)
  obtain ⟨x, hxQ, hxU⟩ := Set.not_subset.mp havoid
  have hx0 : x ≠ 0 := by
    rintro rfl
    apply hxU
    simp only [Set.mem_iUnion, SetLike.mem_coe]
    exact ⟨J₀, hJ₀', Submodule.zero_mem J₀⟩

  obtain ⟨Q₁, hQ₁min, hQ₁Q⟩ :=
    Ideal.exists_minimalPrimes_le ((Ideal.span_singleton_le_iff_mem Q).mpr hxQ)
  haveI : Q₁.IsPrime := hQ₁min.1.1
  have hxQ₁ : x ∈ Q₁ := hQ₁min.1.2 (Ideal.subset_span (Set.mem_singleton x))
  have hQ₁ne : Q₁ ≠ ⊥ := by
    intro h; rw [h] at hxQ₁; exact hx0 ((Submodule.mem_bot R).mp hxQ₁)

  have hϖQ₁ : ϖ ∈ Q₁ := hall Q₁ ‹_› hQ₁ne
  obtain ⟨J, hJmin, hJQ₁⟩ :=
    Ideal.exists_minimalPrimes_le ((Ideal.span_singleton_le_iff_mem Q₁).mpr hϖQ₁)
  haveI : J.IsPrime := hJmin.1.1
  have hJne : J ≠ ⊥ := by
    intro h
    have hϖJ : ϖ ∈ J := hJmin.1.2 (Ideal.subset_span (Set.mem_singleton ϖ))
    rw [h] at hϖJ; exact hϖ ((Submodule.mem_bot R).mp hϖJ)
  have hJQ₁eq : J = Q₁ := by
    rcases eq_or_lt_of_le hJQ₁ with h | hlt
    · exact h
    · exact absurd (eq_bot_of_lt_of_mem_minimalPrimes_span_singleton x Q₁ hQ₁min J hlt) hJne
  apply hxU
  simp only [Set.mem_iUnion, SetLike.mem_coe]
  exact ⟨J, hfin.mem_toFinset.mpr hJmin, hJQ₁eq ▸ hxQ₁⟩

end LocalAlgebra

section Topology

variable {Z : Type*} [TopologicalSpace Z]

theorem isOpen_singleton_of_forall_specializes [NoetherianSpace Z] [QuasiSober Z] (p : Z)
    (hgen : ∀ q : Z, q ⤳ p → q = p) (hsp : ∀ q : Z, p ⤳ q → q = p) :
    IsOpen ({p} : Set Z) := by
  classical
  set C : Set Z := ⋃₀ {c : Set Z | c ∈ irreducibleComponents Z ∧ p ∉ c} with hCdef
  have hCfin : {c : Set Z | c ∈ irreducibleComponents Z ∧ p ∉ c}.Finite :=
    NoetherianSpace.finite_irreducibleComponents.subset fun c hc => hc.1
  have hC : IsClosed C := by
    rw [hCdef, Set.sUnion_eq_biUnion]
    exact hCfin.isClosed_biUnion fun c hc => isClosed_of_mem_irreducibleComponents c hc.1
  have hpC : ({p} : Set Z) = Cᶜ := by
    ext z
    simp only [Set.mem_singleton_iff, Set.mem_compl_iff]
    constructor
    · rintro rfl hz
      obtain ⟨c, ⟨-, hpc⟩, hzc⟩ := Set.mem_sUnion.mp hz
      exact hpc hzc
    · intro hz
      have hc := irreducibleComponent_mem_irreducibleComponents z
      have hzc : z ∈ irreducibleComponent z := mem_irreducibleComponent
      have hpc : p ∈ irreducibleComponent z := by
        by_contra hpc
        exact hz (Set.mem_sUnion.mpr ⟨_, ⟨hc, hpc⟩, hzc⟩)
      obtain ⟨ζ, hζ⟩ := QuasiSober.sober (isIrreducible_irreducibleComponent (x := z))
        isClosed_irreducibleComponent
      have h2 : ζ = p := hgen ζ (hζ.specializes hpc)
      subst h2
      exact hsp z (hζ.specializes hzc)
  rw [hpC]
  exact hC.isOpen_compl

end Topology

section OverDVR

variable {A₀ : Type} [CommRing A₀] [IsDomain A₀] [IsDiscreteValuationRing A₀]

theorem eq_maximalIdeal_iff_mem {ϖ : A₀} (hϖ : maximalIdeal A₀ = Ideal.span {ϖ})
    (q : Ideal A₀) [hq : q.IsPrime] : q = maximalIdeal A₀ ↔ ϖ ∈ q := by
  constructor
  · rintro rfl
    rw [hϖ]; exact Ideal.subset_span (Set.mem_singleton ϖ)
  · intro h
    have hle : maximalIdeal A₀ ≤ q := by
      rw [hϖ]; exact (Ideal.span_singleton_le_iff_mem q).mpr h
    exact ((IsLocalRing.maximalIdeal.isMaximal A₀).eq_of_le hq.ne_top hle).symm

theorem eq_of_ne_closedPoint (t t' : PrimeSpectrum A₀) (ht : t ≠ closedPoint A₀)
    (ht' : t' ≠ closedPoint A₀) : t = t' := by
  have key : ∀ u : PrimeSpectrum A₀, u ≠ closedPoint A₀ → u.asIdeal = ⊥ := by
    intro u hu
    by_contra hne
    apply hu
    have hmax : u.asIdeal.IsMaximal := u.isPrime.isMaximal hne
    ext1
    exact IsLocalRing.eq_maximalIdeal hmax
  ext1
  rw [key t ht, key t' ht']

variable {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of A₀))

noncomputable def constToStalk (y : X) : (CommRingCat.of A₀) ⟶ X.presheaf.stalk y :=
  (Scheme.ΓSpecIso (CommRingCat.of A₀)).inv ≫
    (Spec (CommRingCat.of A₀)).presheaf.germ ⊤ (f y) trivial ≫ f.stalkMap y

omit [IsDomain A₀] [IsDiscreteValuationRing A₀] in
theorem fromSpecStalk_comp (y : X) :
    X.fromSpecStalk y ≫ f = Spec.map (constToStalk f y) := by
  rw [← Scheme.SpecMap_stalkMap_fromSpecStalk, Spec.fromSpecStalk_eq, ← Spec.map_comp,
    constToStalk, Category.assoc]

omit [IsDomain A₀] [IsDiscreteValuationRing A₀] in
theorem base_fromSpecStalk (y : X) (p : PrimeSpectrum (X.presheaf.stalk y)) :
    f (X.fromSpecStalk y p) = PrimeSpectrum.comap (constToStalk f y).hom p := by
  rw [← Scheme.Hom.comp_apply, fromSpecStalk_comp, Spec.map_apply]

theorem base_fromSpecStalk_eq_closedPoint_iff {ϖ : A₀} (hϖ : maximalIdeal A₀ = Ideal.span {ϖ})
    (y : X) (p : PrimeSpectrum (X.presheaf.stalk y)) :
    f (X.fromSpecStalk y p) = closedPoint A₀ ↔ (constToStalk f y).hom ϖ ∈ p.asIdeal := by
  rw [base_fromSpecStalk]
  constructor
  · intro h
    have h' := congrArg PrimeSpectrum.asIdeal h
    rw [PrimeSpectrum.comap_asIdeal] at h'
    exact Ideal.mem_comap.mp ((eq_maximalIdeal_iff_mem hϖ _).mp h')
  · intro h
    apply PrimeSpectrum.ext
    rw [PrimeSpectrum.comap_asIdeal]
    exact (eq_maximalIdeal_iff_mem hϖ _).mpr (Ideal.mem_comap.mpr h)

end OverDVR

end AlgebraicGeometry.PureDimOneAux

open AlgebraicGeometry.PureDimOneAux

theorem solution
    (A₀ : Type) [CommRing A₀] [IsDomain A₀] [IsDiscreteValuationRing A₀]
    (X₀ : Scheme.{0}) (toBase₀ : X₀ ⟶ Spec (CommRingCat.of A₀))
    [IsIntegral X₀] [IsProper toBase₀] [Flat toBase₀] [LocallyOfFinitePresentation toBase₀]

    (hpos : ∃ η : X₀, toBase₀.base η = closedPoint A₀ ∧ ∃ y : X₀, η ⤳ y ∧ y ≠ η)
    (x₀ : X₀) (hx₀ : toBase₀.base x₀ = closedPoint A₀) (hcl : ∀ y : X₀, x₀ ⤳ y → y = x₀) :
    ∃ η : X₀, toBase₀.base η = closedPoint A₀ ∧ (∃ y : X₀, η ⤳ y ∧ y ≠ η) ∧ η ⤳ x₀ := by
  classical
  set f := toBase₀ with hfdef
  haveI : IsLocallyNoetherian X₀ := LocallyOfFiniteType.isLocallyNoetherian f
  by_contra hne

  have hbad : ∀ z : X₀, f.base z = closedPoint A₀ → z ⤳ x₀ → z = x₀ := by
    intro z hz hzx
    by_contra hzne
    exact hne ⟨z, hz, ⟨x₀, hzx, fun h => hzne h.symm⟩, hzx⟩

  set ξ : X₀ := genericPoint X₀ with hξdef
  have hξgen : ∀ z : X₀, ξ ⤳ z := fun z => genericPoint_specializes z
  obtain ⟨η, hη, y, hηy, hyη⟩ := hpos

  by_cases hξs : f.base ξ = closedPoint A₀
  · have hξx : ξ = x₀ := hbad ξ hξs (hξgen x₀)
    have h1 : η = x₀ := hcl η (hξx ▸ hξgen η)
    have h2 : y = x₀ := hcl y (hξx ▸ hξgen y)
    exact hyη (h2.trans h1.symm)

  have hqf₀ : f.QuasiFiniteAt x₀ := by
    rw [Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber]

    haveI : IsLocallyNoetherian (f.fiber (f x₀)) := by
      delta Scheme.Hom.fiber; infer_instance
    haveI : IsNoetherian (f.fiber (f x₀)) := {}
    let ι := f.fiberι (f x₀)
    have hιinj : Function.Injective ι := ι.isEmbedding.injective
    have hιsp : ∀ q : ↥(f.fiber (f x₀)), f.base (ι q) = f.base x₀ := by
      intro q
      have : ι q ∈ Set.range ι := Set.mem_range_self q
      rw [Scheme.Hom.range_fiberι] at this
      simpa using this
    have hp : ι (f.asFiber x₀) = x₀ := Scheme.Hom.fiberι_asFiber f x₀
    apply isOpen_singleton_of_forall_specializes
    · intro q hq
      apply hιinj
      rw [hp]
      refine hbad (ι q) ?_ ?_
      · rw [hιsp q]; exact hx₀
      · simpa [hp] using hq.map ι.continuous
    · intro q hq
      apply hιinj
      rw [hp]
      refine hcl (ι q) ?_
      simpa [hp] using hq.map ι.continuous

  have hqfξ : f.QuasiFiniteAt ξ := by
    have hmem : x₀ ∈ (f.quasiFiniteLocus : Set X₀) := hqf₀
    have hne' : (f.quasiFiniteLocus : Set X₀).Nonempty := ⟨x₀, hmem⟩
    have : ξ ∈ (f.quasiFiniteLocus : Set X₀) :=
      ((genericPoint_spec X₀).mem_open_set_iff f.quasiFiniteLocus.isOpen).mpr (by simpa using hne')
    exact this

  have hGF : ∀ x' : X₀, f.base x' = f.base ξ → x' = ξ := by
    intro x' hx'
    rw [Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber] at hqfξ
    let ι := f.fiberι (f ξ)
    have hιemb : IsEmbedding ι := ι.isEmbedding
    have hp : ι (f.asFiber ξ) = ξ := Scheme.Hom.fiberι_asFiber f ξ

    have hclosed : IsClosed ({f.asFiber ξ} : Set ↥(f.fiber (f ξ))) := by
      obtain ⟨q, hq, hqcl⟩ := nonempty_inter_closedPoints (Set.singleton_nonempty (f.asFiber ξ))
        hqfξ.isLocallyClosed
      rw [Set.mem_singleton_iff] at hq
      rw [← hq]
      exact hqcl

    have hx'mem : x' ∈ Set.range ι := by
      rw [Scheme.Hom.range_fiberι]
      simpa using hx'
    obtain ⟨q, hq⟩ := hx'mem
    have hsp : f.asFiber ξ ⤳ q := by
      rw [← hιemb.specializes_iff, hp, hq]
      exact hξgen x'
    have hqmem : q ∈ closure ({f.asFiber ξ} : Set ↥(f.fiber (f ξ))) :=
      specializes_iff_mem_closure.mp hsp
    rw [hclosed.closure_eq, Set.mem_singleton_iff] at hqmem
    rw [← hq, hqmem, hp]

  obtain ⟨ϖ, hϖirr⟩ := IsDiscreteValuationRing.exists_irreducible A₀
  have hϖ : maximalIdeal A₀ = Ideal.span {ϖ} := hϖirr.maximalIdeal_eq
  set R := X₀.presheaf.stalk y with hRdef
  let g := X₀.fromSpecStalk y
  have hginj : Function.Injective g := g.isEmbedding.injective
  have hgrange : Set.range g = {z | z ⤳ y} := Scheme.range_fromSpecStalk
  let ψ : A₀ →+* R := (constToStalk f y).hom
  have hbridge : ∀ p : PrimeSpectrum R, f.base (g p) = closedPoint A₀ ↔ ψ ϖ ∈ p.asIdeal :=
    fun p => base_fromSpecStalk_eq_closedPoint_iff f hϖ y p

  let p0 : PrimeSpectrum R := ⟨⊥, Ideal.isPrime_bot⟩
  have hp0gen : ∀ p : PrimeSpectrum R, p0 ⤳ p := fun p =>
    (PrimeSpectrum.le_iff_specializes p0 p).mp (fun _ h => by
      change _ ∈ (⊥ : Ideal R) at h
      rw [(Submodule.mem_bot R).mp h]; exact Submodule.zero_mem _)
  have hgp0 : g p0 = ξ := by

    obtain ⟨pξ, hpξ⟩ : ξ ∈ Set.range g := by rw [hgrange]; exact hξgen y
    have h1 : g p0 ⤳ ξ := hpξ ▸ (hp0gen pξ).map g.continuous
    have h2 : IsGenericPoint (g p0) (Set.univ : Set X₀) := by
      rw [isGenericPoint_def]
      apply Set.eq_univ_of_univ_subset
      rw [← (genericPoint_spec X₀).def, isClosed_closure.closure_subset_iff, Set.singleton_subset_iff]
      exact specializes_iff_mem_closure.mp h1
    exact h2.eq (genericPoint_spec X₀)
  have hψϖ : ψ ϖ ≠ 0 := by
    intro h0
    have : ψ ϖ ∈ p0.asIdeal := by change ψ ϖ ∈ (⊥ : Ideal R); rw [h0]; exact Submodule.zero_mem _
    have h1 : f.base (g p0) = closedPoint A₀ := (hbridge p0).mpr this
    rw [hgp0] at h1
    exact hξs h1
  have hall : ∀ P : Ideal R, P.IsPrime → P ≠ ⊥ → ψ ϖ ∈ P := by
    intro P hP hPne
    let p : PrimeSpectrum R := ⟨P, hP⟩
    have hpne : p ≠ p0 := fun h => hPne (congrArg PrimeSpectrum.asIdeal h)
    have hgpne : g p ≠ ξ := fun h => hpne (hginj (h.trans hgp0.symm))
    have hspecial : f.base (g p) = closedPoint A₀ := by
      by_contra hns
      exact hgpne (hGF (g p) (eq_of_ne_closedPoint _ _ hns hξs))
    exact (hbridge p).mp hspecial

  obtain ⟨pη, hpη⟩ : η ∈ Set.range g := by rw [hgrange]; exact hηy
  have hpηne0 : pη.asIdeal ≠ ⊥ := by
    intro h
    have : pη = p0 := PrimeSpectrum.ext h
    have hηξ : η = ξ := by rw [← hpη, this, hgp0]
    exact hξs (hηξ ▸ hη)
  have hgm : g (closedPoint R) = y := Scheme.fromSpecStalk_closedPoint
  have hpηnem : pη.asIdeal ≠ maximalIdeal R := by
    intro h
    have : pη = closedPoint R := PrimeSpectrum.ext h
    have : η = y := by rw [← hpη, this, hgm]
    exact hyη this.symm
  have hpηlt : pη.asIdeal < maximalIdeal R :=
    lt_of_le_of_ne (IsLocalRing.le_maximalIdeal pη.isPrime.ne_top) hpηnem
  haveI : pη.asIdeal.IsPrime := pη.isPrime
  exact false_of_mem_forall_prime_of_lt_of_lt (ψ ϖ) hψϖ hall pη.asIdeal (maximalIdeal R)
    hpηne0 hpηlt

end S_AlgebraicGeometry_exists_specializes_of_closed_of_specialFibre_of_flat
end P2MW
export P2MW.S_AlgebraicGeometry_exists_specializes_of_closed_of_specialFibre_of_flat (solution)
