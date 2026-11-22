-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ThetaLimit
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_ThetaLimit
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:45:16.399397+00:00
-- url     : https://prove2.me/theorems/115db3e6-53fe-432d-bcf2-83d40e7e3243
-- title:
--   Theta Limit
-- statement:
--   Definitions and structural lemmas for Theta Limit, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ThetaLimit.lean

import Definitions.Def_Formalism_HermitianCurvature_StatementLE
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.FourierDecayAlt.P.LEx2
open Formalism.FourierDecayAlt.LE
open MeasureTheory Filter Topology Finset
open scoped ComplexConjugate
open Polynomial in
noncomputable def mkP (m : ℕ) (c : ℕ → ℂ) : ℂ[X] := ∑ q ∈ range (m + 1), C (c q) * X ^ q
noncomputable def Fk (k : ℕ) (s : ℝ) (t : ℝ) : ℝ := Real.exp (-(k:ℝ) * t) * (1 + Real.exp (-t)) ^ (-s)
end Formalism.FourierDecayAlt.P.LEx2


