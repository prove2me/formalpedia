-- Prove2me | Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_FinsuppZmodOneEqSingle
-- name    : Formalism_GL3MeanSquares_HookFormulaTorsion_FinsuppZmodOneEqSingle
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:02:21.28592+00:00
-- url     : https://prove2.me/theorems/1c87af5b-1b85-422f-ab41-47d6d360927a
-- title:
--   Finsupp Zmod One Eq Single
-- statement:
--   Definitions and structural lemmas for Finsupp Zmod One Eq Single, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/HookFormulaTorsion/FinsuppZmodOneEqSingle.lean

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_InvariantSeriesBidegreeOneOne
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_TaylorLogMetric
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_CocycleIsCoboundary
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.HermitianLattices.IntegralLatticeDensity
namespace LemE
open MvPowerSeries Finset Formalism.G Formalism.FG
noncomputable abbrev s1 (n : ℕ) : ZMod 1 →₀ ℕ := Finsupp.single 0 n
noncomputable abbrev mon (k m : ℕ) : Fin 2 × ZMod 1 →₀ ℕ :=
  Finsupp.single ((0 : Fin 2), (0 : ZMod 1)) k + Finsupp.single ((1 : Fin 2), (0 : ZMod 1)) m
section Generic
variable {K : Type} [Field K] {τ : Type}
end Generic
section Padic
variable {p : ℕ} [hp : Fact p.Prime]
end Padic
section Main
variable {p : ℕ} [hp : Fact p.Prime]
def Good (f : MvPowerSeries (ZMod 1) ℚ_[p]) (N : ℕ) (z : ℚ_[p] × ℚ_[p]) : Prop :=
  ‖z.1‖ ≤ 1 ∧ ‖z.2 - coeff (s1 1) f‖ ≤ 1 ∧
    ∀ d ≤ N, ‖coeff (s1 d) f - z.1 * coeff (s1 d) (g0 p) -
      z.2 * coeff (s1 d) (shiftLog ℚ_[p] p 1 0)‖ ≤ 1
end Main
end LemE
end Formalism.HermitianLattices.IntegralLatticeDensity


