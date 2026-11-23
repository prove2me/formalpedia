-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_InvariantPolynomialEqAevalPairings
-- name    : Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_InvariantPolynomialEqAevalPairings
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:34:40.304297+00:00
-- url     : https://prove2.me/theorems/e3f2368b-4288-48bc-b118-adb7d163e1a8
-- title:
--   Invariant Polynomial Eq Aeval Pairings
-- statement:
--   Definitions and structural lemmas for Invariant Polynomial Eq Aeval Pairings, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/InvariantPolynomialEqAevalPairings.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
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
namespace GlobalTheory.PairingInvariants
variable {T : Type} {n N : ℕ}
noncomputable def act (g h : T → Matrix (Fin n) (Fin n) ℂ) (z : T × Bool × Fin n × Fin N → ℂ) :
    T × Bool × Fin n × Fin N → ℂ :=
  fun v => ∑ l, (if v.2.1 then g v.1 v.2.2.1 l else h v.1 v.2.2.1 l) * z (v.1, v.2.1, l, v.2.2.2)
noncomputable def base (z : T × Bool × Fin n × Fin N → ℂ) : T × Bool × Fin n × Fin N → ℂ :=
  fun v => if v.2.1 then (if v.2.2.1.val = v.2.2.2.val then 1 else 0) else
    if h : v.2.2.1.val < N then
      ∑ l, z (v.1, false, l, v.2.2.2) * z (v.1, true, l, ⟨v.2.2.1.val, h⟩) else 0
end GlobalTheory.PairingInvariants


