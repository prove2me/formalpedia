-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_JacquetShalikaBounds_AbsoluteRigidity_EulerLogarithms_EulerProductLogBound
-- name    : Development_WeilBound_RepresentationTheoryGL_JacquetShalikaBounds_AbsoluteRigidity_EulerLogarithms_EulerProductLogBound
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:05:33.99495+00:00
-- url     : https://prove2.me/theorems/68727e90-0f6a-4e80-87c1-55202166b1a2
-- title:
--   Euler Product Log Bound
-- statement:
--   Definitions and structural lemmas for Euler Product Log Bound, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/JacquetShalikaBounds/AbsoluteRigidity/EulerLogarithms/EulerProductLogBound.lean

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
namespace EulerProductLogLemmas
variable {W : Type} {A B : Type} [Fintype A] [Fintype B]
def zz (q : W → ℕ) (α : W → A → ℂ) (β : W → B → ℂ) (s : ℂ) (w : W) (a : A) (b : B) : ℂ :=
  α w a * conj (β w b) * (q w : ℂ) ^ (-s)
def maj (q : W → ℕ) (s : ℂ) (C : ℝ) (p : W × ℕ) : ℝ := C * ((q p.1 : ℝ) ^ (1 - s.re)) ^ (p.2 + 1)
end EulerProductLogLemmas
end PositivityTheory.RgJS


