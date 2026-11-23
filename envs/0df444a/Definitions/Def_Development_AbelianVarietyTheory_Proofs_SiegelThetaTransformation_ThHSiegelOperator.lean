-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ThHSiegelOperator
-- name    : Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ThHSiegelOperator
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:46:19.38397+00:00
-- url     : https://prove2.me/theorems/7a14521c-b5a8-4481-8a4c-48a7acad6f46
-- title:
--   Th HSiegel Operator
-- statement:
--   Definitions and structural lemmas for Th HSiegel Operator, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ThHSiegelOperator.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianThetaSummableAndDeterminesTestFn
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical
namespace GlobalTheory.SW.SiegelOp
variable {E : Type} [Field E] [NumberField E] (Ψ : Finset (E →+* ℂ)) {n N : ℕ}
def cons0 (x : Matrix (Fin n) (Fin N) E) : Matrix (Fin n) (Fin (N + 1)) E :=
  Matrix.of fun k => Fin.cons 0 (x k)
noncomputable def col (x : Matrix (Fin n) (Fin (N + 1)) E) : ℝ :=
  ∑ τ : Ψ, ∑ k, normSq (τ.1 (x k 0))
end GlobalTheory.SW.SiegelOp


