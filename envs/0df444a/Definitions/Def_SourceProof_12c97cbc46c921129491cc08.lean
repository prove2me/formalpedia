-- Prove2me | Definitions.Def_SourceProof_12c97cbc46c921129491cc08
-- name    : SourceProof_12c97cbc46c921129491cc08
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T19:40:45.140648+00:00
-- url     : https://prove2.me/theorems/14a476d3-b361-4782-9398-c70af1e57862
-- title:
--   LevyStochCalc source module: SourceProof_12c97cbc46c921129491cc08
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.stronglyMeasurable_clip` comes from the `LevyStochCalc.Brownian.VectorItoStopped` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_VectorItoStopped_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Stopping a vector Itô process

Cutting the coefficients of a vector Itô process off at a stopping time of finite range leaves a
vector Itô process, whose version is the original one evaluated at the clipped time.

## Main statements

* `LevyStochCalc.Brownian.Ito.clipTime` — the horizon clipped at a stopping time.
* `LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_stopped_clip` — the Itô integral of a
  stopped integrand is the integral evaluated at the clipped horizon.
* `LevyStochCalc.Brownian.Ito.IsVectorItoVersion.stopped` — the stopped version.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

section Clip

variable {Ω : Type u}

variable {τ : Ω → WithTop ℝ} {t : ℝ} {ω : Ω}

end Clip

section StoppedIntegral

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  (W : LevyStochCalc.Brownian.BrownianMotion P) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
  (hℱ : IsBrownianFiltration W ℱ) (τ : Ω → WithTop ℝ)

end StoppedIntegral

section StoppedDrift

variable {Ω : Type u}

end StoppedDrift

section StoppedVersion

open LevyStochCalc.Brownian.Multidim

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {n d : ℕ} (W : Multidim.MultidimBrownianMotion P d)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
  (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ)

omit [IsProbabilityMeasure P] in

theorem _root_.Prove2MeSourceProof.h_12c97cbc46c921129491cc08 {X : ℝ → Ω → Fin n → ℝ} {τ : Ω → WithTop ℝ}
    (hτ : MeasureTheory.IsStoppingTime ℱ τ)
    (hX : ∀ r : ℝ, @MeasureTheory.StronglyMeasurable Ω (Fin n → ℝ) _ (ℱ r) (X r))
    (J : Finset ℝ)
    (hτJ : ∀ ω, (∃ c ∈ J, τ ω = ((c : ℝ) : WithTop ℝ)) ∨ τ ω = ⊤)
    (t : ℝ) :
    @MeasureTheory.StronglyMeasurable Ω (Fin n → ℝ) _ (ℱ t)
      (fun ω => X (clipTime τ t ω) ω) := by
  classical
  set Jt : Finset ℝ := J.filter (fun c => c ≤ t) with hJtdef
  have hJtle : ∀ c ∈ Jt, c ≤ t := fun c hc => (Finset.mem_filter.mp hc).2
  have hdec : (fun ω => X (LevyStochCalc.Brownian.Ito.clipTime τ t ω) ω)
      = fun ω => Set.indicator {ω | ∀ c ∈ Jt, τ ω ≠ ((c : ℝ) : WithTop ℝ)}
            (fun ω => X t ω) ω
          + ∑ c ∈ Jt, Set.indicator {ω | τ ω = ((c : ℝ) : WithTop ℝ)} (fun ω => X c ω) ω := by
    funext ω
    rcases hτJ ω with ⟨c₀, hc₀J, hc₀⟩ | htop
    · by_cases hle : c₀ ≤ t
      · have hc₀Jt : c₀ ∈ Jt := Finset.mem_filter.mpr ⟨hc₀J, hle⟩
        have hnot : ω ∉ {ω | ∀ c ∈ Jt, τ ω ≠ ((c : ℝ) : WithTop ℝ)} := by
          intro hcon
          exact hcon c₀ hc₀Jt hc₀
        have hsum : ∑ c ∈ Jt, Set.indicator {ω | τ ω = ((c : ℝ) : WithTop ℝ)}
            (fun ω => X c ω) ω = X c₀ ω := by
          refine (Finset.sum_eq_single c₀ ?_ ?_).trans ?_
          · intro c _ hne
            refine Set.indicator_of_notMem ?_ _
            intro hmem
            exact hne (by exact_mod_cast (hmem.symm.trans hc₀ : _))
          · intro hcon
            exact absurd hc₀Jt hcon
          · exact Set.indicator_of_mem (by simpa using hc₀) _
        rw [Set.indicator_of_notMem hnot, hsum, LevyStochCalc.Brownian.Ito.clipTime_eq_min hc₀, min_eq_right hle]
        simp
      · have hmemc : ω ∈ {ω | ∀ c ∈ Jt, τ ω ≠ ((c : ℝ) : WithTop ℝ)} := by
          intro c hc hcon
          have : c₀ = c := by exact_mod_cast (hc₀.symm.trans hcon : _)
          exact hle (this ▸ hJtle c hc)
        have hsum : ∑ c ∈ Jt, Set.indicator {ω | τ ω = ((c : ℝ) : WithTop ℝ)}
            (fun ω => X c ω) ω = 0 :=
          Finset.sum_eq_zero fun c hc => by
            refine Set.indicator_of_notMem ?_ _
            exact hmemc c hc
        rw [Set.indicator_of_mem hmemc, hsum, LevyStochCalc.Brownian.Ito.clipTime_eq_min hc₀,
          min_eq_left (le_of_not_ge hle)]
        simp
    · have hmemc : ω ∈ {ω | ∀ c ∈ Jt, τ ω ≠ ((c : ℝ) : WithTop ℝ)} := by
        intro c _ hcon
        rw [htop] at hcon
        exact (WithTop.coe_ne_top hcon.symm : _)
      have hsum : ∑ c ∈ Jt, Set.indicator {ω | τ ω = ((c : ℝ) : WithTop ℝ)}
          (fun ω => X c ω) ω = 0 :=
        Finset.sum_eq_zero fun c hc => by
          refine Set.indicator_of_notMem ?_ _
          exact hmemc c hc
      rw [Set.indicator_of_mem hmemc, hsum, LevyStochCalc.Brownian.Ito.clipTime_eq_self_of_top htop]
      simp
  rw [hdec]
  letI : MeasurableSpace Ω := ℱ t
  have hsetc : MeasurableSet {ω | ∀ c ∈ Jt, τ ω ≠ ((c : ℝ) : WithTop ℝ)} := by
    have : {ω | ∀ c ∈ Jt, τ ω ≠ ((c : ℝ) : WithTop ℝ)}
        = ⋂ c ∈ Jt, {ω | τ ω = ((c : ℝ) : WithTop ℝ)}ᶜ := by
      ext ω; simp [Set.mem_iInter]
    rw [this]
    refine MeasurableSet.biInter (Jt.countable_toSet) fun c hc => ?_
    exact (ℱ.mono (hJtle c hc) _ (hτ.measurableSet_eq c)).compl
  refine ((hX t).indicator hsetc).add ?_
  have hfun : (fun ω => ∑ c ∈ Jt,
        Set.indicator {ω | τ ω = ((c : ℝ) : WithTop ℝ)} (fun ω => X c ω) ω)
      = ∑ c ∈ Jt, Set.indicator {ω | τ ω = ((c : ℝ) : WithTop ℝ)} (fun ω => X c ω) := by
    funext ω
    simp
  rw [hfun]
  refine Finset.stronglyMeasurable_sum _ fun c hc => ?_
  exact ((hX c).mono (ℱ.mono (hJtle c hc))).indicator
    (ℱ.mono (hJtle c hc) _ (hτ.measurableSet_eq c))
end StoppedVersion

end LevyStochCalc.Brownian.Ito


