-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_GramReDetLe
-- name    : ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_GramReDetLe
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-24T15:14:57.182705+00:00
-- url     : https://prove2.me/theorems/870480be-fab2-4fd6-a27e-fa2c497b6950
-- title:
--   Gram Re Det Le
-- statement:
--   Definitions and structural lemmas for Gram Re Det Le, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/GramReDetLe.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_LinIndToLp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix InnerProductSpace
open scoped ComplexConjugate
namespace ReciprocityTheory.ChartRestriction.DS.Xi.GSB
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B ReciprocityTheory.ChartRestriction.DS.Xi.GS
variable {n m : ℕ}
end ReciprocityTheory.ChartRestriction.DS.Xi.GSB
namespace ReciprocityTheory.ChartRestriction.DS.Xi.GSB
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B ReciprocityTheory.ChartRestriction.DS.Xi.GS
def linA {k r : ℕ} (A : Mat k r) :
    EuclideanSpace ℂ (Fin (2 * r + k + 1)) →ₗ[ℂ] EuclideanSpace ℂ (Fin (2 * r + k + 1)) :=
  (WithLp.linearEquiv 2 ℂ (Fin (2 * r + k + 1) → ℂ)).symm.toLinearMap ∘ₗ Matrix.toLin' A ∘ₗ
    (WithLp.linearEquiv 2 ℂ (Fin (2 * r + k + 1) → ℂ)).toLinearMap
end ReciprocityTheory.ChartRestriction.DS.Xi.GSB


