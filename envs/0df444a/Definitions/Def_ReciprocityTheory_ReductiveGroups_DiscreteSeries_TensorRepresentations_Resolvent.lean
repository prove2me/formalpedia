-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_Resolvent
-- name    : ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_Resolvent
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:40:11.345252+00:00
-- url     : https://prove2.me/theorems/cae93994-abdb-45c2-b430-b2abbb9afe88
-- title:
--   Resolvent
-- statement:
--   Definitions and structural lemmas for Resolvent, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/Resolvent.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_PartialTrace
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_GelfandHW
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
namespace ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ} {M : Type*} [AddCommGroup M] [Module ℂ M]
def HasGelfandChar (E : Fin n → Fin n → Module.End ℂ M) (μ : Fin n → ℝ) (S : Submodule ℂ M) : Prop :=
  ∀ k : ℕ, ∀ x ∈ S, gelfand E k x = gval (icShift μ) k • x ∧
    gelfand (antiE E) k x = gval (icShift (-μ)) k • x
def resSeries (a : Fin n → ℂ) : PowerSeries ℂ :=
  ∏ s, (1 + PowerSeries.X * (1 - PowerSeries.C (a s) * PowerSeries.X)⁻¹) - 1
def poleV (μ : Fin n → ℝ) : Fin n → ℂ := fun s => ((μ s + (1 - (n : ℝ)) / 2 : ℝ) : ℂ)
def poleVd (μ : Fin n → ℝ) : Fin n → ℂ := fun s => ((-μ s + (1 - (n : ℝ)) / 2 : ℝ) : ℂ)
end ReciprocityTheory.ChartRestriction.DS


