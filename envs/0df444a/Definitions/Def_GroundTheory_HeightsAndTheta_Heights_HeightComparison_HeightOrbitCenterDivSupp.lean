-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitCenterDivSupp
-- name    : GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitCenterDivSupp
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:01:51.738538+00:00
-- url     : https://prove2.me/theorems/78615476-4619-4069-9735-cb3689a527c0
-- title:
--   Height Orbit Center Div Supp
-- statement:
--   Definitions and structural lemmas for Height Orbit Center Div Supp, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/HeightOrbitCenterDivSupp.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitCenter
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_X_mem_orbitCenter_0f3e436ccb1d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_samplePoint_blockNonzero_cdc1bb3eff09

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G NumberField MvPolynomial
def OrbitCenterDivSupp.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (n : ι → ℕ) (x : Cone n (AlgebraicClosure ℚ))
    (s : MvPolynomial (Coord n) ℤ) (a : ι → ℕ),
    BlockNonzero x → Geo.IsMultiHomog (ι := blockIdx n) s a → s ∉ orbitIdeal x →
    ∀ v : FinitePlace (coordField x), s ∈ orbitCenter x v →
      orbitCenter x v ∈ Geo.divSupp (orbitIdeal x) s
theorem exists_finitePlace_two_lt_one (K : Type) [Field K] [NumberField K] :
    ∃ v : FinitePlace K, v 2 < 1 := by
  have : (Ideal.span {(2 : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime two_ne_zero).mpr Int.prime_two
  obtain ⟨Q, -, hQ, hQc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := 𝓞 K)
    (Ideal.span {(2 : ℤ)}) ⊥ (fun a ha ↦ by
      rw [Ideal.mem_comap, Ideal.mem_bot,
        map_eq_zero_iff _ (algebraMap ℤ (𝓞 K)).injective_int] at ha
      simp [ha])
  have h2 : (2 : 𝓞 K) ∈ Q := by
    have : (2 : ℤ) ∈ Q.comap (algebraMap ℤ (𝓞 K)) := hQc ▸ Ideal.mem_span_singleton_self 2
    simpa using this
  have hne : Q ≠ ⊥ := by
    rintro rfl
    rw [Ideal.mem_bot] at h2
    exact two_ne_zero h2
  refine ⟨FinitePlace.mk ⟨Q, hQ, hne⟩, ?_⟩
  rw [FinitePlace.mk_apply, show (2 : K) = algebraMap (𝓞 K) K 2 from (map_ofNat _ 2).symm]
  exact (FinitePlace.norm_lt_one_iff_mem (K := K)
    (v := (⟨Q, hQ, hne⟩ : IsDedekindDomain.HeightOneSpectrum (𝓞 K))) (2 : 𝓞 K)).mpr h2
example : ∃ v : FinitePlace (coordField samplePoint), BlockNonzero samplePoint ∧
    Geo.IsMultiHomog (ι := blockIdx (fun _ : Unit ↦ 1)) (chartMonomial (fun _ ↦ 1) 1) 1 ∧
    chartMonomial (fun _ ↦ 1) 1 ∉ orbitIdeal samplePoint ∧
    chartMonomial (fun _ ↦ 1) 1 ∈ orbitCenter samplePoint v := by
  obtain ⟨v, hv⟩ := exists_finitePlace_two_lt_one (coordField samplePoint)
  refine ⟨v, samplePoint_blockNonzero,
    (geoMultiHomog_iff _ _).mpr (isWeightedHomogeneous_chartMonomial _ _),
    chartMonomial_notMem_orbitIdeal _ _ (fun _ ↦ by simp [samplePoint]) 1, ?_⟩
  have hX : chartMonomial (n := fun _ : Unit ↦ 1) (fun _ ↦ 1) 1 = X ⟨(), 1⟩ := by
    simp [chartMonomial]
  rw [hX]
  refine X_mem_orbitCenter _ _ () 1 ?_
  have h1 : coordVec samplePoint () 1 = 2 :=
    Subtype.ext (by simp [coordVec, samplePoint]; rfl)
  have h0 : coordVec samplePoint () 0 = 1 := Subtype.ext (by simp [coordVec, samplePoint])
  rw [h1]
  calc v 2 < 1 := hv
    _ = v (coordVec samplePoint () 0) := by rw [h0, map_one]
    _ ≤ ⨆ j, v (coordVec samplePoint () j) :=
      le_ciSup (f := fun j ↦ v (coordVec samplePoint () j)) (Set.finite_range _).bddAbove 0
end GroundTheory.Heights₂.Heights


