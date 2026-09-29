-- Prove2me | solution 1 for AlgebraicGeometry.SmoothOfRelativeDimension.exists_isAffineOpen_smooth_rank_one_etaleCoordinate_of_point
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/0f0c676a-2d36-5415-8fc6-0ba767956a4a

import Mathlib
import Theorems.Thm_AlgebraicGeometry_isReduced_of_smooth_of_field
import Theorems.Thm_AlgebraicGeometry_finrank_cotangentSpace_eq_of_smoothOfRelativeDimension
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_SmoothOfRelativeDimension_exists_isAffineOpen_smooth_rank_one_etaleCoordinate_of_point

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry Opposite

namespace P2mWs2AffEtale

theorem isDomain_of_isPrincipal_maximalIdeal
    (A : Type*) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [IsReduced A]
    (h : (IsLocalRing.maximalIdeal A).IsPrincipal) : IsDomain A := by
  classical
  obtain ⟨ϖ, hϖ⟩ := h
  replace hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ} := hϖ
  have hpow : ∀ n : ℕ, IsLocalRing.maximalIdeal A ^ n = Ideal.span {ϖ ^ n} := fun n ↦ by
    rw [hϖ, Ideal.span_singleton_pow]
  have hinf : ⨅ n : ℕ, IsLocalRing.maximalIdeal A ^ n = ⊥ :=
    Ideal.iInf_pow_eq_bot_of_isLocalRing _ (IsLocalRing.maximalIdeal.isMaximal A).ne_top
  have key : ∀ a : A, a ≠ 0 → ∃ (n : ℕ) (u : A), IsUnit u ∧ a = u * ϖ ^ n := by
    intro a ha
    have hex : ∃ n : ℕ, a ∉ IsLocalRing.maximalIdeal A ^ n := by
      by_contra hcon
      push Not at hcon
      have hmem : a ∈ ⨅ n : ℕ, IsLocalRing.maximalIdeal A ^ n := Ideal.mem_iInf.mpr hcon
      rw [hinf, Ideal.mem_bot] at hmem
      exact ha hmem
    have hN := Nat.find_spec hex
    have hNmin : ∀ m < Nat.find hex, a ∈ IsLocalRing.maximalIdeal A ^ m := fun m hm ↦ by
      have := Nat.find_min hex hm
      simpa using this
    obtain ⟨k, hk⟩ : ∃ k, Nat.find hex = k + 1 := by
      refine Nat.exists_eq_add_one.mpr (Nat.pos_of_ne_zero fun h0 ↦ ?_)
      rw [h0, pow_zero, Ideal.one_eq_top] at hN
      exact hN trivial
    have hak : a ∈ Ideal.span {ϖ ^ k} := by rw [← hpow]; exact hNmin k (by omega)
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hak
    refine ⟨k, c, ?_, rfl⟩
    by_contra hcu
    have hcm : c ∈ IsLocalRing.maximalIdeal A :=
      (IsLocalRing.mem_maximalIdeal c).mpr (mem_nonunits_iff.mpr hcu)
    rw [hϖ] at hcm
    obtain ⟨d, rfl⟩ := Ideal.mem_span_singleton'.mp hcm
    apply hN
    rw [hk, hpow]
    exact Ideal.mem_span_singleton'.mpr ⟨d, by ring⟩
  have hnz : NoZeroDivisors A := by
    refine ⟨fun {a b} hab ↦ ?_⟩
    by_contra hcon
    push Not at hcon
    obtain ⟨ha, hb⟩ := hcon
    obtain ⟨n, u, hu, rfl⟩ := key a ha
    obtain ⟨m, v, hv, rfl⟩ := key b hb
    have hϖ0 : ϖ ^ (n + m) = 0 := by
      have : u * v * ϖ ^ (n + m) = 0 := by rw [← hab]; ring
      exact (hu.mul hv).mul_right_eq_zero.mp this
    have hϖ0' : ϖ = 0 := IsNilpotent.eq_zero ⟨n + m, hϖ0⟩
    subst hϖ0'
    rcases n with _ | n
    · rcases m with _ | m
      · simp only [pow_zero, mul_one] at hab
        exact (hu.mul hv).ne_zero hab
      · exact hb (by simp)
    · exact ha (by simp)
  exact NoZeroDivisors.to_isDomain A

theorem exists_notMem_isDomain_away
    {R Rp : Type*} [CommRing R] [CommRing Rp] [Algebra R Rp] [IsNoetherianRing R] [IsReduced R]
    (P : Ideal R) [P.IsPrime] [IsLocalization.AtPrime Rp P] [IsDomain Rp] :
    ∃ f : R, f ∉ P ∧ ∀ (Rf : Type*) [CommRing Rf] [Algebra R Rf] [IsLocalization.Away f Rf],
      IsDomain Rf := by
  classical
  set Q₀ : Ideal R := RingHom.ker (algebraMap R Rp) with hQ₀def
  have hQ₀prime : Q₀.IsPrime := RingHom.ker_isPrime _

  have hle : ∀ q : Ideal R, q.IsPrime → q ≤ P → Q₀ ≤ q := by
    intro q hq hqP r hr
    obtain ⟨⟨s, hs⟩, hsr⟩ := (IsLocalization.map_eq_zero_iff P.primeCompl Rp r).mp hr
    have : s * r ∈ q := by simp [hsr]
    exact (hq.mem_or_mem this).resolve_left (fun h ↦ hs (hqP h))
  have hQ₀P : Q₀ ≤ P := hle P ‹_› le_rfl

  have hpick : ∀ q ∈ minimalPrimes R, q ≠ Q₀ → ∃ g : R, g ∈ q ∧ g ∉ P := by
    intro q hq hne
    by_contra hcon
    push Not at hcon
    have hqP : q ≤ P := fun g hg ↦ hcon g hg
    exact hne (le_antisymm (hq.2 ⟨hQ₀prime, bot_le⟩ (hle q hq.1.1 hqP)) (hle q hq.1.1 hqP))
  choose g hg using hpick
  let g' : Ideal R → R := fun q ↦ if h : q ∈ minimalPrimes R ∧ q ≠ Q₀ then g q h.1 h.2 else 1
  have hfin : (minimalPrimes R).Finite := minimalPrimes.finite_of_isNoetherianRing R
  let f : R := ∏ q ∈ hfin.toFinset, g' q
  have hfP : f ∉ P := by
    refine Finset.prod_induction g' (fun a ↦ a ∉ P) (fun a b ha hb hab ↦ ?_) ?_ ?_
    · exact (‹P.IsPrime›.mem_or_mem hab).elim ha hb
    · exact fun h1 ↦ ‹P.IsPrime›.ne_top ((Ideal.eq_top_iff_one P).mpr h1)
    · intro q hq
      by_cases h : q ∈ minimalPrimes R ∧ q ≠ Q₀
      · simp only [g', dif_pos h]; exact (hg q h.1 h.2).2
      · simp only [g', dif_neg h]
        exact fun h1 ↦ ‹P.IsPrime›.ne_top ((Ideal.eq_top_iff_one P).mpr h1)
  have hfq : ∀ q ∈ minimalPrimes R, q ≠ Q₀ → f ∈ q := by
    intro q hq hne
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem g' (hfin.mem_toFinset.mpr hq)
    change f = _ at hc
    rw [hc]
    refine q.mul_mem_right c ?_
    simp only [g', dif_pos (show q ∈ minimalPrimes R ∧ q ≠ Q₀ from ⟨hq, hne⟩)]
    exact (hg q hq hne).1

  have hfr : ∀ r ∈ Q₀, f * r = 0 := by
    intro r hr
    have hmem : f * r ∈ sInf (minimalPrimes R) := by
      refine Submodule.mem_sInf.mpr fun q hq ↦ ?_
      by_cases hne : q = Q₀
      · subst hne; exact Ideal.mul_mem_left _ f hr
      · exact Ideal.mul_mem_right r q (hfq q hq hne)
    have h0 : sInf (minimalPrimes R) = (⊥ : Ideal R) := by
      rw [minimalPrimes, Ideal.sInf_minimalPrimes]
      simpa [nilradical] using nilradical_eq_zero R
    rw [h0] at hmem
    simpa using hmem
  have hfQ₀ : f ∉ Q₀ := fun h ↦ hfP (hQ₀P h)
  refine ⟨f, hfP, fun Rf _ _ _ ↦ ?_⟩
  have hpowQ : ∀ (m : Submonoid.powers f) (r : R), (m : R) * r ∈ Q₀ → r ∈ Q₀ := by
    rintro ⟨m, ⟨k, rfl⟩⟩ r hmr
    rcases hQ₀prime.mem_or_mem hmr with h | h
    · exact absurd (hQ₀prime.mem_of_pow_mem k h) hfQ₀
    · exact h
  haveI : Nontrivial Rf := by
    refine ⟨⟨1, 0, fun h10 ↦ ?_⟩⟩
    obtain ⟨m, hm⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers f) Rf (1 : R)).mp
      (by simpa using h10)
    have : (1 : R) ∈ Q₀ := hpowQ m 1 (by simp [hm])
    exact hQ₀prime.ne_top ((Ideal.eq_top_iff_one _).mpr this)
  haveI : NoZeroDivisors Rf := by
    refine ⟨fun {a b} hab ↦ ?_⟩
    obtain ⟨ra, sa, rfl⟩ := IsLocalization.exists_mk'_eq (Submonoid.powers f) a
    obtain ⟨rb, sb, rfl⟩ := IsLocalization.exists_mk'_eq (Submonoid.powers f) b
    rw [← IsLocalization.mk'_mul, IsLocalization.mk'_eq_zero_iff] at hab
    obtain ⟨m, hm⟩ := hab
    have hab' : ra * rb ∈ Q₀ := hpowQ m _ (by simp [hm])
    rcases hQ₀prime.mem_or_mem hab' with h | h
    · left
      exact (IsLocalization.mk'_eq_zero_iff _ _).mpr ⟨⟨f, Submonoid.mem_powers f⟩, hfr ra h⟩
    · right
      exact (IsLocalization.mk'_eq_zero_iff _ _).mpr ⟨⟨f, Submonoid.mem_powers f⟩, hfr rb h⟩
  exact NoZeroDivisors.to_isDomain Rf

theorem appLE_top_top {X Y : Scheme} (g : X ⟶ Y) (h : (⊤ : X.Opens) ≤ g ⁻¹ᵁ ⊤) :
    g.appLE ⊤ ⊤ h = g.appTop := by
  show _ = g.app ⊤
  rw [Scheme.Hom.app_eq_appLE]
  rfl

theorem eval_algebraMap (M : Scheme.{0}) (πM : M ⟶ Spec (CommRingCat.of ℂ))
    (σ : Spec (CommRingCat.of ℂ) ⟶ M) (hσ : σ ≫ πM = 𝟙 _) (U : M.Opens) (hσU : ⊤ ≤ σ ⁻¹ᵁ U)
    (z : ℂ) :
    (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom ((σ.appLE U ⊤ hσU).hom
      ((M.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom
          (πM.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom z)))) = z := by
  have h1 : M.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op ≫ σ.appLE U ⊤ hσU = σ.appTop := by
    rw [Scheme.Hom.map_appLE]; exact appLE_top_top σ _
  have h2 : πM.appTop ≫ σ.appTop = 𝟙 _ := by
    rw [← Scheme.Hom.comp_appTop, hσ, Scheme.Hom.id_appTop]
  have h3 : (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ (πM.appTop ≫
      (M.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op ≫ σ.appLE U ⊤ hσU)) ≫
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom = 𝟙 _ := by
    rw [h1, h2]; simp
  have := congrArg (fun k ↦ k.hom z) h3
  simp only [CommRingCat.hom_comp, CommRingCat.hom_id, RingHom.comp_apply, RingHom.id_apply] at this
  exact this

theorem isStandardSmoothOfRelativeDimension_basicOpen (M : Scheme.{0})
    (πM : M ⟶ Spec (CommRingCat.of ℂ)) (V : M.Opens)
    (hV : IsAffineOpen V) (e : V ≤ πM ⁻¹ᵁ ⊤)
    (hstd : (πM.appLE ⊤ V e).hom.IsStandardSmoothOfRelativeDimension 1) (f : Γ(M, V)) :
    ((M.presheaf.map (homOfLE (le_top : M.basicOpen f ≤ ⊤)).op).hom.comp
      (πM.appTop.hom.comp
        (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom)).IsStandardSmoothOfRelativeDimension 1 := by
  haveI : IsLocalization.Away f Γ(M, M.basicOpen f) := hV.isLocalization_basicOpen f
  have h1 := (RingHom.IsStandardSmoothOfRelativeDimension.algebraMap_isLocalizationAway
      (Rᵣ := Γ(M, M.basicOpen f)) f).comp hstd
  have h2 : (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom.IsStandardSmoothOfRelativeDimension 0 :=
    RingHom.IsStandardSmoothOfRelativeDimension.equiv
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).symm.commRingCatIsoToRingEquiv
  have h3 := h1.comp h2
  have heq : ((algebraMap Γ(M, V) Γ(M, M.basicOpen f)).comp (πM.appLE ⊤ V e).hom).comp
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom =
      ((M.presheaf.map (homOfLE (le_top : M.basicOpen f ≤ ⊤)).op).hom.comp
        (πM.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom)) := by
    rw [← RingHom.comp_assoc]
    congr 1
    rw [RingHom.algebraMap_toAlgebra, ← CommRingCat.hom_comp, ← CommRingCat.hom_comp,
      Scheme.Hom.appLE_map]
    rfl
  simpa [heq] using h3

theorem exists_D_notMem
    (S : Type*) [CommRing S] [IsDomain S] [Algebra ℂ S] [Algebra.FiniteType ℂ S]
    [Module.Free S (KaehlerDifferential ℂ S)]
    (hrank : Module.rank S (KaehlerDifferential ℂ S) = 1) (σ₀ : S →ₐ[ℂ] ℂ) :
    ∃ t : S, KaehlerDifferential.D ℂ S t ∉
      (RingHom.ker σ₀.toRingHom) • (⊤ : Submodule S (KaehlerDifferential ℂ S)) := by
  by_contra hcon
  push Not at hcon
  have htop : (⊤ : Submodule S (KaehlerDifferential ℂ S)) ≤ (RingHom.ker σ₀.toRingHom) • ⊤ := by
    have : Submodule.span S (Set.range (KaehlerDifferential.D ℂ S)) ≤
        (RingHom.ker σ₀.toRingHom) • ⊤ :=
      Submodule.span_le.mpr (by rintro _ ⟨t, rfl⟩; exact hcon t)
    rwa [KaehlerDifferential.span_range_derivation] at this
  have hfg : (⊤ : Submodule S (KaehlerDifferential ℂ S)).FG := Module.Finite.fg_top
  obtain ⟨r, hr1, hr⟩ :=
    Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul _ _ hfg htop
  have hnt : Nontrivial (KaehlerDifferential ℂ S) :=
    rank_pos_iff_nontrivial.mp (by rw [hrank]; exact zero_lt_one)
  obtain ⟨ω, hω⟩ := exists_ne (0 : KaehlerDifferential ℂ S)
  have hr0 : r = 0 := (smul_eq_zero.mp (hr ω trivial)).resolve_right hω
  have h1 : σ₀ 1 = 0 := by
    have : r - 1 ∈ RingHom.ker σ₀.toRingHom := hr1
    rw [hr0, zero_sub, RingHom.mem_ker, map_neg, neg_eq_zero] at this
    exact this
  exact one_ne_zero ((map_one σ₀).symm.trans h1)

end P2mWs2AffEtale

open P2mWs2AffEtale in
theorem solution
    (M : Scheme.{0}) (πM : M ⟶ Spec (CommRingCat.of ℂ)) (hsm : SmoothOfRelativeDimension 1 πM)
    (σ : Spec (CommRingCat.of ℂ) ⟶ M) (hσ : σ ≫ πM = 𝟙 _) :
    ∃ (U : M.Opens) (hU : IsAffineOpen U) (hσU : ⊤ ≤ σ ⁻¹ᵁ U)
      (inst : Algebra ℂ ↑(M.presheaf.obj (op U))),

      (∀ z : ℂ, algebraMap ℂ ↑(M.presheaf.obj (op U)) z =
        (M.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom
          (πM.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom z))) ∧
      IsDomain ↑(M.presheaf.obj (op U)) ∧ Algebra.FiniteType ℂ ↑(M.presheaf.obj (op U)) ∧
      Algebra.Smooth ℂ ↑(M.presheaf.obj (op U)) ∧
      Module.rank ↑(M.presheaf.obj (op U)) (KaehlerDifferential ℂ ↑(M.presheaf.obj (op U))) = 1 ∧
      ∃ (σ₀ : ↑(M.presheaf.obj (op U)) →ₐ[ℂ] ℂ) (t : ↑(M.presheaf.obj (op U))),
        (∀ s : ↑(M.presheaf.obj (op U)),
          σ₀ s = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom ((σ.appLE U ⊤ hσU).hom s)) ∧
        KaehlerDifferential.D ℂ ↑(M.presheaf.obj (op U)) t ∉
          (RingHom.ker σ₀.toRingHom) • (⊤ : Submodule ↑(M.presheaf.obj (op U)) (KaehlerDifferential ℂ ↑(M.presheaf.obj (op U)))) := by
  haveI := hsm
  haveI : Smooth πM := SmoothOfRelativeDimension.smooth 1 πM
  haveI : IsReduced M := AlgebraicGeometry.isReduced_of_smooth_of_field πM
  haveI : IsLocallyNoetherian M := LocallyOfFiniteType.isLocallyNoetherian πM

  set x : ↥M := σ.base (IsLocalRing.closedPoint ℂ) with hxdef
  have hfr := AlgebraicGeometry.finrank_cotangentSpace_eq_of_smoothOfRelativeDimension πM 1 σ hσ
  have hdomx : IsDomain (M.presheaf.stalk x) :=
    isDomain_of_isPrincipal_maximalIdeal _
      (IsLocalRing.finrank_cotangentSpace_le_one_iff.mp (le_of_eq hfr))

  obtain ⟨U', hU', V, hV, hxV, e, hstd⟩ := hsm.exists_isStandardSmoothOfRelativeDimension x
  obtain rfl : U' = ⊤ := by
    refine eq_top_iff.mpr fun p _ ↦ ?_
    rw [Subsingleton.elim p (πM.base x)]
    exact e hxV

  letI : Algebra Γ(M, V) (M.presheaf.stalk x) := M.presheaf.algebra_section_stalk ⟨x, hxV⟩
  have hloc : IsLocalization.AtPrime (M.presheaf.stalk x) (hV.primeIdealOf ⟨x, hxV⟩).asIdeal :=
    hV.isLocalization_stalk ⟨x, hxV⟩
  haveI : IsNoetherianRing Γ(M, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  obtain ⟨f, hfP, hdom⟩ := exists_notMem_isDomain_away (Rp := M.presheaf.stalk x)
    (hV.primeIdealOf ⟨x, hxV⟩).asIdeal
  have hxf : x ∈ M.basicOpen f := by
    rw [M.mem_basicOpen f x hxV]
    exact (IsLocalization.AtPrime.isUnit_to_map_iff (M.presheaf.stalk x)
      (hV.primeIdealOf ⟨x, hxV⟩).asIdeal f).mpr hfP
  haveI : IsLocalization.Away f Γ(M, M.basicOpen f) := hV.isLocalization_basicOpen f
  have hdomU : IsDomain Γ(M, M.basicOpen f) := hdom _
  have hσU : ⊤ ≤ σ ⁻¹ᵁ M.basicOpen f := by
    intro p _
    show σ.base p ∈ M.basicOpen f
    rw [Subsingleton.elim p (IsLocalRing.closedPoint ℂ)]
    exact hxf

  let φ : ℂ →+* Γ(M, M.basicOpen f) :=
    (M.presheaf.map (homOfLE (le_top : M.basicOpen f ≤ ⊤)).op).hom.comp
      (πM.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom)
  letI inst : Algebra ℂ Γ(M, M.basicOpen f) := φ.toAlgebra
  have hφ : φ.IsStandardSmoothOfRelativeDimension 1 :=
    isStandardSmoothOfRelativeDimension_basicOpen M πM V hV e hstd f
  haveI hss : Algebra.IsStandardSmoothOfRelativeDimension 1 ℂ Γ(M, M.basicOpen f) :=
    (RingHom.isStandardSmoothOfRelativeDimension_algebraMap 1).mp hφ
  haveI : Algebra.IsStandardSmooth ℂ Γ(M, M.basicOpen f) :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth 1
  have hrank :
      Module.rank Γ(M, M.basicOpen f) (KaehlerDifferential ℂ Γ(M, M.basicOpen f)) = 1 := by
    simpa using Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential
      (R := ℂ) (S := Γ(M, M.basicOpen f)) 1

  let σ₀' : Γ(M, M.basicOpen f) →+* ℂ :=
    (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom.comp (σ.appLE (M.basicOpen f) ⊤ hσU).hom
  let σ₀ : Γ(M, M.basicOpen f) →ₐ[ℂ] ℂ :=
    { toRingHom := σ₀'
      commutes' := fun z ↦ by
        have h__af := eval_algebraMap M πM σ hσ (M.basicOpen f) hσU z
        simp at h__af
        exact h__af }
  obtain ⟨t, ht⟩ := exists_D_notMem Γ(M, M.basicOpen f) hrank σ₀
  exact ⟨M.basicOpen f, hV.basicOpen f, hσU, inst, fun z ↦ rfl, hdomU, inferInstance,
    inferInstance, hrank, σ₀, t, fun s ↦ rfl, ht⟩

end S_AlgebraicGeometry_SmoothOfRelativeDimension_exists_isAffineOpen_smooth_rank_one_etaleCoordinate_of_point
end P2MW
export P2MW.S_AlgebraicGeometry_SmoothOfRelativeDimension_exists_isAffineOpen_smooth_rank_one_etaleCoordinate_of_point (solution)
