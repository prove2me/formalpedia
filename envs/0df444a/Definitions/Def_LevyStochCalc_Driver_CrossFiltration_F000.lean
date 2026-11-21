-- Prove2me | Definitions.Def_LevyStochCalc_Driver_CrossFiltration_F000
-- name    : LevyStochCalc_Driver_CrossFiltration_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T07:18:10.821849+00:00
-- url     : https://prove2.me/theorems/27490931-662a-4424-9848-c6989dea3f55
-- title:
--   Source declarations: LevyStochCalc.Driver.CrossFiltration
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Driver.CrossFiltration. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Driver_Joint_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Two enlargements of the joint filtration

Independence of the Brownian motion from the Poisson random measure lets either driver's whole
path join the other's past without disturbing it: `N` is a Poisson random measure for the Poisson
past enlarged by all of `σ(W)`, and every coordinate of `W` is a Brownian motion for the Brownian
past enlarged by all of `σ(N)`. An increment of one driver is then measurable at every time of
the other's enlargement.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace LevyStochCalc.Driver

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d : ℕ}

namespace LevyDriver

variable (D : LevyDriver.{u, v, w} P d ν)

section Poisson

/-- The Poisson past, joined with the whole Brownian path. -/
noncomputable def crossPoissonFiltration : Filtration ℝ ‹MeasurableSpace Ω› where
  seq s := (⨆ i, Brownian.sigmaBrownian (D.W.W i)) ⊔ Poisson.naturalFiltration D.N s
  mono' _ _ hst := sup_le_sup_left ((Poisson.naturalFiltration D.N).mono hst) _
  le' s := sup_le (iSup_le fun _ => Brownian.sigmaBrownian_le _)
    ((Poisson.naturalFiltration D.N).le s)
theorem crossPoissonFiltration_apply (s : ℝ) :
    D.crossPoissonFiltration s
      = (⨆ i, Brownian.sigmaBrownian (D.W.W i)) ⊔ Poisson.naturalFiltration D.N s := rfl
theorem filtration_le_crossPoisson (s : ℝ) :
    D.filtration s ≤ D.crossPoissonFiltration s := by
  rw [filtration_apply, crossPoissonFiltration_apply]
  exact sup_le_sup (D.W.naturalFiltration_le_iSup_sigmaBrownian s) le_rfl
/-- `N` is a Poisson random measure for the Poisson past joined with the whole Brownian path. -/
theorem isPoissonFiltration_crossPoisson :
    Poisson.IsPoissonFiltration D.N D.crossPoissonFiltration where
  measurable _ _ hB hBm :=
    ((Poisson.isPoissonFiltration_natural D.N).measurable hB hBm).mono le_sup_right le_rfl
  indep_future := by
    intro s hs
    have hfut : (⨆ B ∈ {B : Set (ℝ × E) | B ⊆ Set.Ioi s ×ˢ Set.univ ∧ MeasurableSet B},
        MeasurableSpace.comap (fun ω => D.N.N ω B) inferInstance) ≤ sigmaPoisson D.N :=
      iSup₂_le fun B hB => comap_count_le_sigmaPoisson D.N hB.2
    refine indep_of_indep_of_le_left ?_ (le_of_eq (sup_comm _ _))
    refine _root_.Prove2MeSourceProof.h_fa5eb32f3be3b75875b08ef5
      ((naturalFiltration_le_sigmaPoisson _ s).trans (sigmaPoisson_le _))
      (iSup_le fun _ => Brownian.sigmaBrownian_le _) (hfut.trans (sigmaPoisson_le _))
      ((Poisson.isPoissonFiltration_natural D.N).indep_future hs) ?_
    exact indep_of_indep_of_le_right D.indep
      (sup_le (naturalFiltration_le_sigmaPoisson _ s) hfut)
/-- A Brownian increment is measurable at every time of the Poisson enlargement. -/
theorem measurable_increment_crossPoisson (i : Fin d) (s p q : ℝ) :
    Measurable[D.crossPoissonFiltration s] fun ω => (D.W.W i).W q ω - (D.W.W i).W p ω := by
  refine Measurable.of_comap_le ?_
  exact (Brownian.comap_increment_le_sigmaBrownian (D.W.W i) p q).trans
    ((le_iSup (fun k => Brownian.sigmaBrownian (D.W.W k)) i).trans le_sup_left)
end Poisson

section BrownianSide

/-- The Brownian past, joined with the whole Poisson path. -/
noncomputable def crossBrownianFiltration : Filtration ℝ ‹MeasurableSpace Ω› where
  seq s := D.W.naturalFiltration s ⊔ sigmaPoisson D.N
  mono' _ _ hst := sup_le_sup_right (D.W.naturalFiltration.mono hst) _
  le' s := sup_le (D.W.naturalFiltration.le s) (sigmaPoisson_le _)
theorem crossBrownianFiltration_apply (s : ℝ) :
    D.crossBrownianFiltration s = D.W.naturalFiltration s ⊔ sigmaPoisson D.N := rfl
theorem filtration_le_crossBrownian (s : ℝ) :
    D.filtration s ≤ D.crossBrownianFiltration s := by
  rw [filtration_apply, crossBrownianFiltration_apply]
  exact sup_le_sup le_rfl (naturalFiltration_le_sigmaPoisson D.N s)
/-- Every coordinate is a Brownian motion for the Brownian past joined with the whole Poisson
path. -/
theorem isBrownianFiltration_crossBrownian (j : Fin d) :
    Brownian.IsBrownianFiltration (D.W.W j) D.crossBrownianFiltration :=
  ((_root_.Prove2MeSourceProof.h_947c94e08f8784ad6039b2d1 D.W) j).of_le_sup
    (fun t => (((_root_.Prove2MeSourceProof.h_947c94e08f8784ad6039b2d1 D.W) j).measurable t).mono le_sup_left le_rfl)
    (m := fun _ => sigmaPoisson D.N) (fun _ => sigmaPoisson_le _) (fun _ => le_rfl)
    (fun s _ => indep_of_indep_of_le_right D.indep.symm
      (sup_le (D.W.naturalFiltration_le_iSup_sigmaBrownian s)
        (iSup₂_le fun t _ => (Brownian.comap_increment_le_sigmaBrownian (D.W.W j) s t).trans
          (le_iSup (fun i => Brownian.sigmaBrownian (D.W.W i)) j))))
/-- A compensated mass is measurable at every time of the Brownian enlargement. -/
theorem stronglyMeasurable_compensated_crossBrownian (s : ℝ) {B : Set (ℝ × E)}
    (hB : MeasurableSet B) :
    StronglyMeasurable[D.crossBrownianFiltration s] fun ω => D.N.compensated B ω := by
  have hg : @Measurable Ω ℝ≥0∞ (MeasurableSpace.comap (fun ω => D.N.N ω B) inferInstance) _
      (fun ω => D.N.N ω B) := fun u hu => ⟨u, hu, rfl⟩
  exact (((hg.ennreal_toReal).sub_const _).stronglyMeasurable).mono
    ((comap_count_le_sigmaPoisson D.N hB).trans le_sup_right)
end BrownianSide

end LevyDriver

end LevyStochCalc.Driver


