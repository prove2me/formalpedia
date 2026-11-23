-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_JacquetShalikaBounds_AbsoluteRigidity_NonnegativeCoefficients_DirichletSeriesUnbounded
-- name    : Development_WeilBound_RepresentationTheoryGL_JacquetShalikaBounds_AbsoluteRigidity_NonnegativeCoefficients_DirichletSeriesUnbounded
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:06:00.343735+00:00
-- url     : https://prove2.me/theorems/18cdd742-9a09-4771-bbf2-9c3bf528f6c8
-- title:
--   Dirichlet Series Unbounded
-- statement:
--   Definitions and structural lemmas for Dirichlet Series Unbounded, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/JacquetShalikaBounds/AbsoluteRigidity/NonnegativeCoefficients/DirichletSeriesUnbounded.lean

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_JacquetShalikaBounds_AbsoluteRigidity_NewtonLow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped ComplexConjugate
namespace PositivityTheory.RgJS
namespace DirichletSeriesUnbounded₂
variable {W X : Type} (q : W → ℕ) {d : X → ℕ} (A : ∀ x, W → Fin (d x) → ℂ) {ι : Type} [Fintype ι] (x : ι → X)
def PP (p : W × ℕ) : ℂ := ∑ i, ∑ a, A (x i) p.1 a ^ (p.2 + 1)
def cc (p : W × ℕ) : ℝ := ‖PP A x p‖ ^ 2 / ((p.2 : ℝ) + 1)
def ll (p : W × ℕ) : ℝ := ((p.2 : ℝ) + 1) * Real.log (q p.1)
end DirichletSeriesUnbounded₂
end PositivityTheory.RgJS


