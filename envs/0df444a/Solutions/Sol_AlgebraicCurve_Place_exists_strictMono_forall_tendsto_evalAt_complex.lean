-- Prove2me | solution 1 for AlgebraicCurve.Place.exists_strictMono_forall_tendsto_evalAt_complex
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/ba196578-fee0-50b5-b3a9-20af7c35596f

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Theorems.Thm_AlgebraicCurve_Place_exists_localParam_meromorphicOrderAt_evalAt_eq_ord_complex
import Theorems.Thm_AlgebraicCurve_Place_exists_finset_forall_exists_localParam_eq_complex
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Place_exists_strictMono_forall_tendsto_evalAt_complex
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion"
p2m_attr_erase "simp" "ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom"

set_option autoImplicit false

noncomputable section

open AlgebraicCurve Filter Set Metric Topology

namespace SeqPlacesComplexValues

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem evalAt_zero (v : Place K F) : v.evalAt (0 : F) = 0 := by
  rw [v.evalAt_of_mem (zero_mem _)]
  have h0 : (⟨(0 : F), zero_mem _⟩ : v.toValuationSubring) = 0 := rfl
  rw [h0, map_zero, ← map_zero (algebraMap K v.ResidueField), v.residueInv_algebraMap]

theorem exists_ord_eq_one (v : Place K F) : ∃ t : F, v.ord t = 1 := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  exact ⟨(π : F), v.ord_coe_irreducible hπ⟩

end SeqPlacesComplexValues

open SeqPlacesComplexValues in
theorem solution
    (F : Type*) [Field F] [Algebra ℂ F]
    (hfg : ∃ x : F, Transcendental ℂ x ∧
      FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set F)) F)
    [IsCurveOver ℂ F] (w : ℕ → Place ℂ F) :
    ∃ (v : Place ℂ F) (φ : ℕ → ℕ), StrictMono φ ∧
      ∀ f : F, 0 ≤ v.ord f →
        (∀ᶠ n in Filter.atTop, 0 ≤ (w (φ n)).ord f) ∧
        Filter.Tendsto (fun n => (w (φ n)).evalAt f) Filter.atTop (𝓝 (v.evalAt f)) := by
  classical

  choose t ht using fun v : Place ℂ F => exists_ord_eq_one v
  choose ρ γ hρ hγ0 hγt hγ using fun v : Place ℂ F =>
    AlgebraicCurve.Place.exists_localParam_meromorphicOrderAt_evalAt_eq_ord_complex
      F hfg v (t v) (ht v)

  obtain ⟨S, r, hr, hcov⟩ :=
    AlgebraicCurve.Place.exists_finset_forall_exists_localParam_eq_complex
      F hfg ρ γ t hρ hγ0 hγt hγ

  choose vn hvnS zn hzn hγeq using fun n : ℕ => hcov (w n)

  obtain ⟨⟨v₀, hv₀S⟩, hinf⟩ :=
    Finite.exists_infinite_fiber (fun n : ℕ => (⟨vn n, hvnS n⟩ : (S : Set (Place ℂ F))))
  have hfreq : ∃ᶠ n in atTop, vn n = v₀ := by
    rw [Nat.frequently_atTop_iff_infinite]
    have hinf' := Set.infinite_coe_iff.mp hinf
    refine hinf'.mono ?_
    intro n hn
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Subtype.mk.injEq] at hn
    exact hn
  obtain ⟨ψ, hψ, hψv⟩ := Filter.extraction_of_frequently_atTop hfreq

  have hball : IsCompact (closedBall (0 : ℂ) (r v₀)) := isCompact_closedBall 0 (r v₀)
  have hmem : ∀ n, zn (ψ n) ∈ closedBall (0 : ℂ) (r v₀) := fun n => by
    have h := hzn (ψ n)
    rw [hψv n] at h
    rw [mem_closedBall, dist_zero_right]
    exact h
  obtain ⟨a, ha, φ₂, hφ₂, hlim⟩ := hball.tendsto_subseq hmem
  have haρ : a ∈ ball (0 : ℂ) (ρ v₀) := by
    rw [mem_closedBall, dist_zero_right] at ha
    rw [mem_ball, dist_zero_right]
    exact lt_of_le_of_lt ha (hr v₀ hv₀S).2
  have hz : Tendsto (fun n => zn (ψ (φ₂ n))) atTop (𝓝 a) := hlim

  have hw : ∀ n, w ((ψ ∘ φ₂) n) = γ v₀ (zn (ψ (φ₂ n))) := fun n => by
    have h := hγeq (ψ (φ₂ n))
    rw [hψv (φ₂ n)] at h
    exact h.symm
  refine ⟨γ v₀ a, ψ ∘ φ₂, hψ.comp hφ₂, fun f hf => ?_⟩
  by_cases hf0 : f = 0
  · subst hf0
    refine ⟨Eventually.of_forall fun n => by rw [Place.ord_zero], ?_⟩
    simp only [evalAt_zero]
    exact tendsto_const_nhds
  · obtain ⟨-, -, han⟩ := hγ v₀ f hf0 a haρ
    have hG : AnalyticAt ℂ (fun u : ℂ => (γ v₀ u).evalAt f) a := han hf
    refine ⟨?_, ?_⟩
    ·
      have h1 : ∀ᶠ u in 𝓝 a, AnalyticAt ℂ (fun u : ℂ => (γ v₀ u).evalAt f) u :=
        hG.eventually_analyticAt
      have h2 : ∀ᶠ u in 𝓝 a, u ∈ ball (0 : ℂ) (ρ v₀) := isOpen_ball.mem_nhds haρ
      have h3 : ∀ᶠ u in 𝓝 a, 0 ≤ (γ v₀ u).ord f := by
        filter_upwards [h1, h2] with u hu1 hu2
        obtain ⟨-, hord, -⟩ := hγ v₀ f hf0 u hu2
        have h4 := hu1.meromorphicOrderAt_nonneg
        rw [hord] at h4
        exact_mod_cast h4
      have h5 := hz.eventually h3
      filter_upwards [h5] with n hn
      rw [hw n]
      exact hn
    ·
      have hc : Tendsto (fun u : ℂ => (γ v₀ u).evalAt f) (𝓝 a) (𝓝 ((γ v₀ a).evalAt f)) :=
        hG.continuousAt
      refine (hc.comp hz).congr fun n => ?_
      rw [Function.comp_apply, hw n]

end
end S_AlgebraicCurve_Place_exists_strictMono_forall_tendsto_evalAt_complex
end P2MW
export P2MW.S_AlgebraicCurve_Place_exists_strictMono_forall_tendsto_evalAt_complex (solution)
