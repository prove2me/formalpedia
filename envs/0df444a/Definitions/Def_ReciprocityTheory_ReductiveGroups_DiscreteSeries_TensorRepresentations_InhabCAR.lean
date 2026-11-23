-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_InhabCAR
-- name    : ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_InhabCAR
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:45:20.326445+00:00
-- url     : https://prove2.me/theorems/9e4bb5a6-76ff-4ebb-be73-eb6de6a4a844
-- title:
--   Inhab CAR
-- statement:
--   Definitions and structural lemmas for Inhab CAR, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TensorRepresentations/InhabCAR.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_CarSumSqZeroOfAnti
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
variable {n : ℕ}
abbrev Fock (n : ℕ) := ExteriorAlgebra ℂ (Fin n × Fin n → ℂ)
def cpFock (i a : Fin n) : Module.End ℂ (Fock n) :=
  LinearMap.mulLeft ℂ (ExteriorAlgebra.ι ℂ (Pi.single (i, a) (1 : ℂ)))
def cmFock (i a : Fin n) : Module.End ℂ (Fock n) :=
  CliffordAlgebra.contractLeft (LinearMap.proj (R := ℂ) (φ := fun _ : Fin n × Fin n => ℂ) (i, a))
def cpOne : Module.End ℂ (EuclideanSpace ℂ (Fin 2)) := Matrix.toEuclideanLin !![0, 0; 1, 0]
def cmOne : Module.End ℂ (EuclideanSpace ℂ (Fin 2)) := Matrix.toEuclideanLin !![0, 1; 0, 0]
end ReciprocityTheory.ChartRestriction.DS


