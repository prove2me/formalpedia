-- Prove2me | Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_NumericalZeroDensityBound
-- name    : Formalism_GL3MeanSquares_HookFormulaTorsion_NumericalZeroDensityBound
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:37:31.79314+00:00
-- url     : https://prove2.me/theorems/b8f7e5b3-28b3-481c-8b58-a18fe03d23d7
-- title:
--   Numerical Zero Density Bound
-- statement:
--   Definitions and structural lemmas for Numerical Zero Density Bound, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/NumericalZeroDensityBound.lean

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_SecondEstimateOfIntervalHypothesis
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_WeightedVonMangoldtSumIdentity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter
namespace Formalism.HermitianLattices.ZeroFreeRegionGL2
open Finset ArithmeticFunction in
noncomputable def SS {t : ℕ} (θ : DirichletCharacter ℂ t) (x : ℝ) (q : ℕ) : ℝ :=
  ‖∑ n ∈ Icc 1 ⌊x ^ 400⌋₊, ((cN x n : ℝ) : ℂ) * θ (n : ZMod t) * ((jacobiSym (n : ℤ) q : ℤ) : ℂ)‖
open Classical in
noncomputable def badSet {t : ℕ} [NeZero t] (θ : DirichletCharacter ℂ t) (Q : ℝ) (P : Finset ℕ) :
    Finset ℕ :=
  P.filter (fun q => ∃ h : Fact q.Prime, ¬ ZeroFreeBox Q (@tw t θ q h))
end Formalism.HermitianLattices.ZeroFreeRegionGL2


