-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PProjSecDegree
-- name    : GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PProjSecDegree
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:45:04.606121+00:00
-- url     : https://prove2.me/theorems/725695a5-ee84-45ca-94e9-942652e50bea
-- title:
--   PProj Sec Degree
-- statement:
--   Definitions and structural lemmas for PProj Sec Degree, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PProjSecDegree.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsProjSecDegree
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
namespace ProjSecDegree
variable {n e : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin (e + 1)) (Fin n) ℂ)
set_option hygiene false in

local notation "𝕂" => FractionRing (MvPolynomial (Fin (e + 1)) ℂ)
set_option hygiene false in

local notation "ℝt" => MvPolynomial (Fin (e + 1)) ℂ
end ProjSecDegree
end
end GroundTheory.Heights₂.Heights


