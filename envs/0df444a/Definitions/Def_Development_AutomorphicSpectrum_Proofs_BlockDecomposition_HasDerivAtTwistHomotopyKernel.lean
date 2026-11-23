-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HasDerivAtTwistHomotopyKernel
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HasDerivAtTwistHomotopyKernel
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T21:21:21.596121+00:00
-- url     : https://prove2.me/theorems/9d65181e-138e-4b4c-9dc8-27ad44eb794a
-- title:
--   Has Deriv At Twist Homotopy Kernel
-- statement:
--   Definitions and structural lemmas for Has Deriv At Twist Homotopy Kernel, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/HasDerivAtTwistHomotopyKernel.lean

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_DiscreteSeriesTopClasses_IsInvOne
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_StandardBasisDerivatives_ArchimedeanBasisDerivatives_StBasDeriv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Matrix Finset
open scoped ContDiff
open PositivityTheory.RgTw
namespace GlobalTheory.CompanionTheory.TwistHomotopy
variable {n : ℕ}
def kern (F : ℝ → ℝ) (a : ℝ) (j : ℕ) (x v : ℝ) : ℝ :=
  Real.exp (a * v) * iteratedDeriv j F (Real.exp (2 * v) * x)
def homot (F : ℝ → ℝ) (a : ℝ) (j : ℕ) (v₁ v₂ x : ℝ) : ℝ := ∫ v in v₂..v₁, kern F a j x v
def ex (N k : ℕ) : ℝ := 2 * (k : ℝ) - N
end GlobalTheory.CompanionTheory.TwistHomotopy


