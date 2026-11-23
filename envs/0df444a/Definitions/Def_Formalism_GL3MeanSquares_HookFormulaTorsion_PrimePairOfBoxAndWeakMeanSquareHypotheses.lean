-- Prove2me | Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_PrimePairOfBoxAndWeakMeanSquareHypotheses
-- name    : Formalism_GL3MeanSquares_HookFormulaTorsion_PrimePairOfBoxAndWeakMeanSquareHypotheses
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T07:03:10.449885+00:00
-- url     : https://prove2.me/theorems/f10832aa-f991-4875-ae32-5372f1d40aaa
-- title:
--   Prime Pair Of Box And Weak Mean Square Hypotheses
-- statement:
--   Definitions and structural lemmas for Prime Pair Of Box And Weak Mean Square Hypotheses, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/PrimePairOfBoxAndWeakMeanSquareHypotheses.lean

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_PrimePairOfBoxAndWeakMeanSquareHypotheses
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_WeightedVonMangoldtSumIdentity
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_NumericalZeroDensityBound
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
noncomputable def p2m_PrimePair_SS {t : ℕ} (θ : DirichletCharacter ℂ t) (x : ℝ) (q : ℕ) : ℝ :=
  ‖∑ n ∈ Icc 1 ⌊x ^ 400⌋₊, ((cN x n : ℝ) : ℂ) * θ (n : ZMod t) * ((jacobiSym (n : ℤ) q : ℤ) : ℂ)‖
open Classical in
noncomputable def p2m_PrimePair_badSet {t : ℕ} [NeZero t] (θ : DirichletCharacter ℂ t) (Q : ℝ) (P : Finset ℕ) :
    Finset ℕ :=
  P.filter (fun q => ∃ h : Fact q.Prime, ¬ ZeroFreeBox Q (@tw t θ q h))
end Formalism.HermitianLattices.ZeroFreeRegionGL2
namespace Formalism.HermitianLattices.WeakMeanSquareEstimates
open Formalism.HermitianLattices.ZeroFreeRegionGL2
end Formalism.HermitianLattices.WeakMeanSquareEstimates
namespace Formalism.HermitianLattices.ZeroFreeRegionGL2
end Formalism.HermitianLattices.ZeroFreeRegionGL2


