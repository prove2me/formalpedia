-- Prove2me | Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_MaxFlowValueAttained
-- name    : Formalism_IncomingBounds_FlowDegreeBounds_MaxFlowValueAttained
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:01:18.780802+00:00
-- url     : https://prove2.me/theorems/60147abd-b8b8-4a1b-901d-de40f7046a68
-- title:
--   Max Flow Value Attained
-- statement:
--   Definitions and structural lemmas for Max Flow Value Attained, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/IncomingBounds/FlowDegreeBounds/MaxFlowValueAttained.lean

import Mathlib
import Definitions.Def_Formalism_IncomingBounds_IncomingBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Set
open scoped Pointwise
namespace Formalism.IncomingBounds
namespace FlowLoadBounds
variable {l d : ℕ} [NeZero d]
def dpLoad (l d : ℕ) [NeZero d] (x : ZMod d → ℕ → ℝ) (s : ZMod d) : ℝ :=
  (∑ i ∈ oddLevels d, (l : ℝ) ^ i * x s i) + ∑ i ∈ oddLevels d, x (s - (i : ZMod d)) i
def trunc (d : ℕ) [NeZero d] (x : ZMod d → ℕ → ℝ) : ZMod d → ℕ → ℝ :=
  fun s i => if i ∈ oddLevels d then x s i else 0
def box (d : ℕ) (R : ℝ) : Set (ZMod d → ℕ → ℝ) := Set.pi univ fun _ => Set.pi univ fun _ => Icc 0 R
def Kset (l d : ℕ) [NeZero d] : Set ((ZMod d → ℝ) × ℝ) :=
  {q | ∃ x : ZMod d → ℕ → ℝ, (∀ s i, 0 ≤ x s i) ∧ (∀ s, dpLoad l d x s ≤ q.1 s) ∧
    q.2 ≤ flowVal d x}
def gmap (l d : ℕ) [NeZero d] (x : ZMod d → ℕ → ℝ) : (ZMod d → ℝ) × ℝ :=
  (fun s => dpLoad l d x s, flowVal d x)
def Cset (d : ℕ) : Set ((ZMod d → ℝ) × ℝ) := {q | (∀ s, 0 ≤ q.1 s) ∧ q.2 ≤ 0}
end FlowLoadBounds
open FlowLoadBounds
end Formalism.IncomingBounds


