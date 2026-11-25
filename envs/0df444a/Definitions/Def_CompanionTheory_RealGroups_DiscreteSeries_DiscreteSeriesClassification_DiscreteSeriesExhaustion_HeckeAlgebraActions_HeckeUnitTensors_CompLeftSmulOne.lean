-- Prove2me | Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_HeckeUnitTensors_CompLeftSmulOne
-- name    : CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_HeckeUnitTensors_CompLeftSmulOne
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T14:17:49.55191+00:00
-- url     : https://prove2.me/theorems/b6ce2949-6da5-48b8-a9bd-0e689c6e1eb1
-- title:
--   Comp Left Smul One
-- statement:
--   Definitions and structural lemmas for Comp Left Smul One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/RealGroups/DiscreteSeries/DiscreteSeriesClassification/DiscreteSeriesExhaustion/HeckeAlgebraActions/HeckeUnitTensors/CompLeftSmulOne.lean

import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_HeckeUnitTensors_ContOfFnProd
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
namespace CompanionTheory.RgExh.Hk.UnitPf
open Formalism.REAL (qdet qminor Tm GlRel)
open Formalism.QuantumDeterminants (capP)
open ReciprocityTheory.ChartRestriction.DS.Lap.Capelli (cminor)
open CompanionTheory.RgExh
variable {m : ℕ} (X : GMod (m + 1)) (χ : Fin (m + 1) → ℂ) (s : Fin (m + 1))
def omg : ℂ := cn (m + 1) - χ s
def kap : ℂ := ∏ t ∈ univ.erase s, (χ t - χ s)
def Pr : Module.End ℂ (Fin (m + 1) → X.V) := (kap χ s)⁻¹ • qdet (tensE X) (omg χ s)
variable {X χ s}
end CompanionTheory.RgExh.Hk.UnitPf


