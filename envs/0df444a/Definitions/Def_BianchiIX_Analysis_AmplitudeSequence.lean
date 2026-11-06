-- Prove2me | Definitions.Def_BianchiIX_Analysis_AmplitudeSequence
-- name    : BianchiIX_Analysis_AmplitudeSequence
-- status  : Definition
-- author  : @trppppp
-- created : 2026-11-04T20:01:36.902644+00:00
-- url     : https://prove2.me/theorems/9f2a9eb5-b9fd-4d2d-9438-09636cc2eaee
-- title:
--   The superexponentially decreasing era amplitudes
-- statement:
--   For $B\in\mathbb R$ and $m\in\mathbb N$, define
--   $$M_m(B)=B^{(4/3)^m},$$
--   where the outer power is the real power.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Analysis/AmplitudeSequence.lean

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

noncomputable section

namespace BianchiIX

open Filter
open scoped Topology

def eraAmplitude (B : ℝ) (m : ℕ) : ℝ := B ^ ((4 / 3 : ℝ) ^ m)

























end BianchiIX


