-- Prove2me | solution 1 for AdicCompletion.isNoetherianRing_of_noetherian_local
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-04T16:53:04.825976+00:00
-- url     : https://prove2.me/submissions/892bb916-71e9-46c9-b515-4ad3db659f7f

import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 350000
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace PhilipponMultiplicity.NoetherianCompletion

open scoped Topology

variable {R : Type*} [CommRing R]

theorem exists_powerSeriesMap (I : Ideal R) (hI : I.FG)
    {σ : Type*} [Finite σ] (a : σ → R) (ha : ∀ i, a i ∈ I) :
    ∃ f : MvPowerSeries σ R →+* AdicCompletion I R,
      (∀ r : R, f (MvPowerSeries.C r) = algebraMap R (AdicCompletion I R) r) ∧
      (∀ i : σ, f (MvPowerSeries.X i) = algebraMap R (AdicCompletion I R) (a i)) := by
  let S := AdicCompletion I R
  let J := I.map (algebraMap R S)
  letI : UniformSpace R := ⊥
  letI : WithIdeal S := ⟨J⟩
  letI : IsAdicComplete J S := AdicCompletion.isAdicComplete_self I hI
  have hcomplete : CompleteSpace S ∧ T2Space S :=
    (IsAdic.isAdicComplete_iff (I := J) rfl).mp inferInstance
  letI : CompleteSpace S := hcomplete.1
  letI : T2Space S := hcomplete.2
  have hcont : Continuous (algebraMap R S) := continuous_of_discreteTopology
  have heval : MvPowerSeries.HasEval (fun i => algebraMap R S (a i)) := by
    constructor
    · intro i
      exact WithIdeal.isTopologicallyNilpotent_of_mem (Ideal.mem_map_of_mem _ (ha i))
    · simp only [Filter.cofinite_eq_bot]
      exact Filter.tendsto_bot
  refine ⟨MvPowerSeries.eval₂Hom hcont heval, ?_, ?_⟩
  · intro r
    simp [MvPowerSeries.coe_eval₂Hom, S]
  · intro i
    simp [MvPowerSeries.coe_eval₂Hom, S]

theorem powerSeriesMap_surjective (I : Ideal R) (hI : I.FG)
    {σ : Type*} [Finite σ] (a : σ → R)
    (ha : Ideal.span (Set.range a) = I)
    (f : MvPowerSeries σ R →+* AdicCompletion I R)
    (hC : ∀ r : R, f (MvPowerSeries.C r) = algebraMap R (AdicCompletion I R) r)
    (hX : ∀ i : σ, f (MvPowerSeries.X i) = algebraMap R (AdicCompletion I R) (a i)) :
    Function.Surjective f := by
  let S := AdicCompletion I R
  let J : Ideal (MvPowerSeries σ R) := Ideal.span (Set.range MvPowerSeries.X)
  have hmap : J.map f = I.map (algebraMap R S) := by
    change (Ideal.span (Set.range MvPowerSeries.X)).map f = _
    rw [Ideal.map_span, ← Set.range_comp]
    simp only [Function.comp_def, hX]
    simpa only [Ideal.map_span, ← Set.range_comp, Function.comp_def, S] using
      congrArg (Ideal.map (algebraMap R S)) ha
  letI : IsAdicComplete (I.map (algebraMap R S)) S :=
    AdicCompletion.isAdicComplete_self I hI
  letI : IsHausdorff (J.map f) S := hmap ▸ inferInstance
  apply surjective_of_mk_map_comp_surjective (I := J) f
  intro q
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective q
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalOneₐ I y)
  refine ⟨MvPowerSeries.C r, ?_⟩
  change Ideal.Quotient.mk (J.map f) (f (MvPowerSeries.C r)) =
    Ideal.Quotient.mk (J.map f) y
  rw [hC, Ideal.Quotient.eq, hmap]
  change algebraMap R (AdicCompletion I R) r - y ∈
    I.map (algebraMap R (AdicCompletion I R))
  rw [← AdicCompletion.ker_evalOneₐ_eq_map (I := I) hI]
  change AdicCompletion.evalOneₐ I (algebraMap R S r - y) = 0
  rw [map_sub]
  change Ideal.Quotient.mk I r - AdicCompletion.evalOneₐ I y = 0
  rw [hr, sub_self]

theorem isNoetherianRing_completion [IsNoetherianRing R] (I : Ideal R) :
    IsNoetherianRing (AdicCompletion I R) := by
  obtain ⟨n, a, ha⟩ := Submodule.fg_iff_exists_fin_generating_family.mp I.fg_of_isNoetherianRing
  have hmem : ∀ i, a i ∈ I := fun i => ha ▸ Ideal.subset_span (Set.mem_range_self i)
  obtain ⟨f, hC, hX⟩ := exists_powerSeriesMap I I.fg_of_isNoetherianRing a hmem
  exact isNoetherianRing_of_surjective (MvPowerSeries (Fin n) R) (AdicCompletion I R) f
    (powerSeriesMap_surjective I I.fg_of_isNoetherianRing a ha f hC hX)

end PhilipponMultiplicity.NoetherianCompletion

end

theorem solution
    (R : Type*) [CommRing R] [IsNoetherianRing R] [IsLocalRing R] :
    IsNoetherianRing (AdicCompletion (IsLocalRing.maximalIdeal R) R) := by
  exact PhilipponMultiplicity.NoetherianCompletion.isNoetherianRing_completion
    (IsLocalRing.maximalIdeal R)
