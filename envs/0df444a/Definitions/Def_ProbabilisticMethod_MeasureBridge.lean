-- Prove2me | Definitions.Def_ProbabilisticMethod_MeasureBridge
-- name    : ProbabilisticMethod_MeasureBridge
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T20:59:48.431997+00:00
-- url     : https://prove2.me/theorems/3bfbb602-aca9-4aca-ab69-88918a171ea2
-- title:
--   Measure Bridge
-- statement:
--   Definitions and structural lemmas for Measure Bridge, from Brian Sanders (Egly443/lean-probabilistic-method; see pinned Apache-2.0 LICENSE and source headers)'s pinned The finite probabilistic method for graphs development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Egly443/lean-probabilistic-method/blob/841e3042ef057564ae3cbd2322e0f369bbf64d34/ProbabilisticMethod/MeasureBridge.lean

module
public import Definitions.Def_ProbabilisticMethod_RandomGraph
public import Mathlib.Probability.Combinatorics.BinomialRandomGraph.Defs
set_option autoImplicit true
@[expose] public section
public section
@[expose] section
open MeasureTheory ProbabilityTheory unitInterval
open scoped Finset
namespace Finset
variable {α : Type*} [DecidableEq α] [Countable α]
end Finset
namespace SimpleGraph
variable {V : Type*}
section Fintype
variable [Fintype V] [DecidableEq V]
end Fintype
section Finite
variable [Finite V]
end Finite
end SimpleGraph


