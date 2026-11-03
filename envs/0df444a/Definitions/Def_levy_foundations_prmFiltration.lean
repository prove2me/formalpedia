-- Prove2me | Definitions.Def_levy_foundations_prmFiltration
-- name    : levy_foundations_prmFiltration
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-27T07:52:22.842005+00:00
-- url     : https://prove2.me/theorems/12396bca-e88f-4cdb-bc09-1a339425a617
-- title:
--   Natural filtration of time-space Poisson observations
-- statement:
--   At time t, record all finite-intensity Poisson random-measure evaluations with time coordinate at most t. These σ-algebras are increasing and subordinate to the ambient measurable structure.
-- source:
--   Inspired by Shmuel Link, LeanLevy (MIT), commit 7e73fd9b23ad52956ec2756a815889a783131ce4. Independently formulated Prove2Me draft; remote elaboration and proof pending. PoissonMartingale.lean lines 85–94. Relies on separate monotonicity and ambient-measurability theorems.

import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Distributions.Poisson.Basic
import Definitions.Def_levy_foundations_prmEvalSigma
import Theorems.Thm_levy_foundations_prmEvalSigmaMono
import Theorems.Thm_levy_foundations_prmEvalSigmaLe

open MeasureTheory
open scoped NNReal
namespace LevyFoundations
noncomputable def prmFiltration {Ω E : Type*}
    [MeasurableSpace Ω] [MeasurableSpace E]
    (K : ℕ → Ω → ℕ) (X : ℕ → ℕ → Ω → ℝ × E)
    (m : Measure E) [SigmaFinite m]
    (hK : ∀ k, Measurable (K k))
    (hX : ∀ k n, Measurable (X k n)) :
    MeasureTheory.Filtration ℝ≥0 ‹MeasurableSpace Ω› where
  seq t := prmEvalSigma K X (volume.prod m)
    (Set.Iic (t : ℝ) ×ˢ Set.univ)
  mono' s t hst := by
    exact levy_foundations_prmEvalSigmaMono K X (volume.prod m)
      (Set.prod_mono (Set.Iic_subset_Iic.mpr
        (by exact_mod_cast hst)) (subset_refl _))
  le' t := by
    exact levy_foundations_prmEvalSigmaLe K X (volume.prod m)
      (Set.Iic (t : ℝ) ×ˢ Set.univ) hK hX
end LevyFoundations


