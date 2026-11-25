-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_CompEqZeroOfNotDle
-- name    : Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_CompEqZeroOfNotDle
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T01:25:34.931047+00:00
-- url     : https://prove2.me/theorems/de3fcc83-fcaa-4131-a423-a738c8cd55fd
-- title:
--   Comp Eq Zero Of Not Dle
-- statement:
--   Definitions and structural lemmas for Comp Eq Zero Of Not Dle, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/CompEqZeroOfNotDle.lean

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_OrthogonalIsomorphismHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_CommProjectionHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.InvariantFactorPaths.PW
open Formalism.GM.M Formalism.GM.DimensionMonotonicity MvPolynomial Finset
section abstract
variable {K V : Type} [Field K] [CharZero K] [AddCommGroup V] [Module K V] {n : ℕ} (G : GlW K V n)
def lowIm : Submodule K V := ⨆ (a : Fin n) (b : Fin n) (_ : b < a), Submodule.map (G.E a b) ⊤
end abstract
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
noncomputable def lowC (p : ℕ) [Fact p.Prime] (LL : Letters N) (j : ℕ) (Cs : Finset (Fin r)) :
    Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]) :=
  ⨆ (c : Fin r) (d : Fin r) (_ : c ∈ Cs ∧ d ∈ Cs ∧ d < c), Submodule.map (glAct p LL j c d) ⊤
end Formalism.InvariantFactorPaths.PW


