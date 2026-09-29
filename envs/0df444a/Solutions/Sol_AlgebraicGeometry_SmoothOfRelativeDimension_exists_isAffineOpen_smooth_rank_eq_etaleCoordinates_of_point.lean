-- Prove2me | solution 1 for AlgebraicGeometry.SmoothOfRelativeDimension.exists_isAffineOpen_smooth_rank_eq_etaleCoordinates_of_point
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/af81fc0c-ddf7-5990-83b8-381e82be74b5

import Mathlib
import Definitions.Def_AlgebraicGeometry_KaehlerModule
import Theorems.Thm_AlgebraicGeometry_isReduced_of_smooth_of_field
import Theorems.Thm_AlgebraicGeometry_Smooth_isRegularLocalRing_stalk
import Theorems.Thm_IsRegularLocalRing_isDomain
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_SmoothOfRelativeDimension_exists_isAffineOpen_smooth_rank_eq_etaleCoordinates_of_point
p2m_attr_erase "simp" "RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite

namespace AffEtaleN

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

theorem isStandardSmoothOfRelativeDimension_basicOpen {k : Type} [Field k] (M : Scheme.{0})
    (πM : M ⟶ Spec (CommRingCat.of k)) (V : M.Opens)
    (hV : IsAffineOpen V) (e : V ≤ πM ⁻¹ᵁ ⊤) {n : ℕ}
    (hstd : (πM.appLE ⊤ V e).hom.IsStandardSmoothOfRelativeDimension n) (f : Γ(M, V)) :
    ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ πM.appLE ⊤ (M.basicOpen f) le_top).hom.IsStandardSmoothOfRelativeDimension n := by
  haveI : IsLocalization.Away f Γ(M, M.basicOpen f) := hV.isLocalization_basicOpen f
  have h1 := (RingHom.IsStandardSmoothOfRelativeDimension.algebraMap_isLocalizationAway
      (Rᵣ := Γ(M, M.basicOpen f)) f).comp hstd
  have h2 : (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom.IsStandardSmoothOfRelativeDimension 0 :=
    RingHom.IsStandardSmoothOfRelativeDimension.equiv
      (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv
  have h3 := h1.comp h2
  have heq : ((algebraMap Γ(M, V) Γ(M, M.basicOpen f)).comp (πM.appLE ⊤ V e).hom).comp
      (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom =
      ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ πM.appLE ⊤ (M.basicOpen f) le_top).hom := by
    rw [RingHom.algebraMap_toAlgebra, ← CommRingCat.hom_comp, ← CommRingCat.hom_comp, Scheme.Hom.appLE_map]
  simpa [heq] using h3

section Points
variable {K : Type} [Field K] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of K)) (U : X.Opens)

theorem appLE_congr_hom {X Y : Scheme.{0}} {p q : X ⟶ Y} (hpq : p = q) (U : Y.Opens) (V : X.Opens)
    (h : V ≤ p ⁻¹ᵁ U) (h' : V ≤ q ⁻¹ᵁ U) : p.appLE U V h = q.appLE U V h' := by subst hpq; rfl

def evalAlgHom (P : Spec (CommRingCat.of K) ⟶ X) (hP1 : P ≫ f = 𝟙 _) (hP : ⊤ ≤ P ⁻¹ᵁ U) :
    letI := f.sectionsAlgebra U
    Γ(X, U) →ₐ[K] K :=
  letI := f.sectionsAlgebra U
  { toRingHom := (P.appLE U ⊤ hP ≫ (Scheme.ΓSpecIso (CommRingCat.of K)).hom).hom
    commutes' := fun r => by
      change ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ f.appLE ⊤ U le_top ≫ P.appLE U ⊤ hP ≫
        (Scheme.ΓSpecIso (CommRingCat.of K)).hom).hom r = r
      have h1 : f.appLE ⊤ U le_top ≫ P.appLE U ⊤ hP = 𝟙 _ := by
        rw [Scheme.Hom.appLE_comp_appLE, appLE_congr_hom hP1 ⊤ ⊤ _ le_top]
        simp [Scheme.Hom.appLE]
      rw [← Category.assoc (f.appLE ⊤ U le_top), h1]
      simp }

theorem evalAlgHom_apply (P : Spec (CommRingCat.of K) ⟶ X) (hP1 : P ≫ f = 𝟙 _) (hP : ⊤ ≤ P ⁻¹ᵁ U)
    (s : Γ(X, U)) :
    evalAlgHom f U P hP1 hP s = (Scheme.ΓSpecIso (CommRingCat.of K)).hom ((P.appLE U ⊤ hP) s) := rfl

end Points

end AffEtaleN

open AffEtaleN in
theorem solution
    {k : Type} [Field k] (M : Scheme.{0}) (πM : M ⟶ Spec (CommRingCat.of k)) {n : ℕ}
    (hsm : SmoothOfRelativeDimension n πM)
    (σ : Spec (CommRingCat.of k) ⟶ M) (hσ : σ ≫ πM = 𝟙 _) :
    ∃ (U : M.Opens) (hU : IsAffineOpen U) (hσU : ⊤ ≤ σ ⁻¹ᵁ U),
      letI := πM.sectionsAlgebra U
      IsDomain Γ(M, U) ∧ Algebra.FiniteType k Γ(M, U) ∧ Algebra.Smooth k Γ(M, U) ∧
      Module.rank Γ(M, U) (KaehlerDifferential k Γ(M, U)) = n ∧
      ∃ (σ₀ : Γ(M, U) →ₐ[k] k) (t : Fin n → Γ(M, U)),
        (∀ s : Γ(M, U), σ₀ s = (Scheme.ΓSpecIso (CommRingCat.of k)).hom ((σ.appLE U ⊤ hσU) s)) ∧
        (∀ i : Fin n, σ₀ (t i) = 0) ∧
        (RingHom.ker σ₀.toRingHom) • (⊤ : Submodule Γ(M, U) (KaehlerDifferential k Γ(M, U))) ⊔
          Submodule.span Γ(M, U) (Set.range fun i : Fin n => KaehlerDifferential.D k Γ(M, U) (t i)) = ⊤ := by
  classical
  haveI := hsm
  haveI : Smooth πM := SmoothOfRelativeDimension.smooth n πM
  haveI : IsReduced M := AlgebraicGeometry.isReduced_of_smooth_of_field πM
  haveI : IsLocallyNoetherian M := LocallyOfFiniteType.isLocallyNoetherian πM

  set x : ↥M := σ.base (IsLocalRing.closedPoint k) with hxdef
  have hdomx : IsDomain (M.presheaf.stalk x) := by
    haveI := AlgebraicGeometry.Smooth.isRegularLocalRing_stalk (f := πM) x
    exact IsRegularLocalRing.isDomain _

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
    rw [Subsingleton.elim p (IsLocalRing.closedPoint k)]
    exact hxf

  letI inst : Algebra k Γ(M, M.basicOpen f) := πM.sectionsAlgebra (M.basicOpen f)
  have halg : algebraMap k Γ(M, M.basicOpen f) =
      ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ πM.appLE ⊤ (M.basicOpen f) le_top).hom := rfl
  have hφ : (algebraMap k Γ(M, M.basicOpen f)).IsStandardSmoothOfRelativeDimension n := by
    rw [halg]; exact isStandardSmoothOfRelativeDimension_basicOpen M πM V hV e hstd f
  haveI hss : Algebra.IsStandardSmoothOfRelativeDimension n k Γ(M, M.basicOpen f) :=
    (RingHom.isStandardSmoothOfRelativeDimension_algebraMap n).mp hφ
  haveI : Algebra.IsStandardSmooth k Γ(M, M.basicOpen f) :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth n
  haveI : IsDomain Γ(M, M.basicOpen f) := hdomU
  have hrank : Module.rank Γ(M, M.basicOpen f) (KaehlerDifferential k Γ(M, M.basicOpen f)) = n := by
    simpa using Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential
      (R := k) (S := Γ(M, M.basicOpen f)) n

  let σ₀ : Γ(M, M.basicOpen f) →ₐ[k] k := evalAlgHom πM (M.basicOpen f) σ hσ hσU

  obtain ⟨ι, τ, _, _, P, hP⟩ := hss.out
  letI := Fintype.ofFinite ι
  have hcard : Fintype.card ↥((Set.range P.map)ᶜ) = n := by
    have h1 := rank_eq_card_basis P.basisKaehler
    rw [hrank] at h1
    exact_mod_cast h1.symm
  let eι : ↥((Set.range P.map)ᶜ) ≃ Fin n := Fintype.equivFinOfCardEq hcard
  let t₀ : Fin n → Γ(M, M.basicOpen f) := fun i => P.val (eι.symm i)
  have hspan : Submodule.span Γ(M, M.basicOpen f)
      (Set.range fun i : Fin n => KaehlerDifferential.D k Γ(M, M.basicOpen f) (t₀ i)) = ⊤ := by
    have : (fun i : Fin n => KaehlerDifferential.D k Γ(M, M.basicOpen f) (t₀ i)) =
        ⇑(P.basisKaehler.reindex eι) := by
      funext i
      simp [t₀, Module.Basis.reindex_apply, Algebra.SubmersivePresentation.basisKaehler_apply]
    rw [this]
    exact (P.basisKaehler.reindex eι).span_eq
  let t : Fin n → Γ(M, M.basicOpen f) := fun i => t₀ i - algebraMap k _ (σ₀ (t₀ i))
  have hDt : ∀ i, KaehlerDifferential.D k Γ(M, M.basicOpen f) (t i) =
      KaehlerDifferential.D k Γ(M, M.basicOpen f) (t₀ i) := by
    intro i
    simp [t, map_sub, Derivation.map_algebraMap]
  refine ⟨M.basicOpen f, hV.basicOpen f, hσU, hdomU, inferInstance, inferInstance, hrank, σ₀, t,
    fun s => rfl, fun i => ?_, ?_⟩
  · simp [t, σ₀.commutes]
  · have : (fun i : Fin n => KaehlerDifferential.D k Γ(M, M.basicOpen f) (t i)) =
        fun i : Fin n => KaehlerDifferential.D k Γ(M, M.basicOpen f) (t₀ i) := funext hDt
    rw [this, hspan]
    simp

end
end S_AlgebraicGeometry_SmoothOfRelativeDimension_exists_isAffineOpen_smooth_rank_eq_etaleCoordinates_of_point
end P2MW
export P2MW.S_AlgebraicGeometry_SmoothOfRelativeDimension_exists_isAffineOpen_smooth_rank_eq_etaleCoordinates_of_point (solution)
