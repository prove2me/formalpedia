-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_PStdChar
-- name    : Formalism_LocalToGlobal_GlobalTheory_GL3_PStdChar
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:19:24.083616+00:00
-- url     : https://prove2.me/theorems/12e06048-a79f-4e0c-8ef7-72945bb321e5
-- title:
--   PStd Char
-- statement:
--   Definitions and structural lemmas for PStd Char, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/GL3/PStdChar.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlock
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_Th0CharMulOpUTh0HalfPeriodEq
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_MatrixFormFourfoldBlockFirstBlockEmb
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SC
open Formalism.L2.Th1.H
open Formalism.L2.Th1.F (cmTheta thetaZeroCharacter semiChar herm)
section Main
variable (L : PeriodPair) (d : ℕ)
local notation "EE" => Formalism.L2.Th1.F.altE L
def q1 (w : ℂ) : ℝ := Real.sqrt d / 2 * (herm L w w).re
def aa (w : ℂ) : ℂ := Complex.exp ((Real.pi : ℂ) * Complex.I * ((q1 L d w : ℝ) : ℂ))
def io (w : ℂ) : Unit → ℂ := fun _ => w
variable {L d}
variable (hst : ∀ x ∈ L.lattice, cmTheta 1 d * x ∈ L.lattice)
include hst
variable {ω₀ : ℂ} (h0 : ω₀ ∈ L.lattice) (hθ : cmTheta 1 d * (ω₀ / 2) ∉ L.lattice)
  (hθ' : (1 - cmTheta 1 d) * (ω₀ / 2) ∉ L.lattice)
include h0 hθ hθ'
end Main
end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SC
end


