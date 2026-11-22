-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MeasIterDeriv
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_MeasIterDeriv
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:37:50.823242+00:00
-- url     : https://prove2.me/theorems/fa7753c5-6d43-474e-b36a-09d57ab0afc6
-- title:
--   Meas Iter Deriv
-- statement:
--   Definitions and structural lemmas for Meas Iter Deriv, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MeasIterDeriv.lean

import Definitions.Def_Formalism_HermitianCurvature_StatementLE
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.FourierDecayAlt.P.LEx2.A3
open Formalism.FourierDecayAlt.LE
open MeasureTheory Filter Topology Finset
open scoped ComplexConjugate
noncomputable section
def DsMeas : Prop := ∀ (B : Base) (S : Step B), S.Meas → S.I4 → ∀ Y ∈ S.J, ∀ (p : ℕ) k, Measurable fun ω => S.ds Y p ω k
end
end Formalism.FourierDecayAlt.P.LEx2.A3


