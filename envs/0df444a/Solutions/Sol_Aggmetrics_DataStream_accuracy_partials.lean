-- Prove2me | solution 1 for Aggmetrics.DataStream.accuracy_partials
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T10:31:45.670298+00:00
-- url     : https://prove2.me/submissions/ebbfdb32-8121-403f-992f-52a924bbd7c6

import Definitions.Def_Aggmetrics_DataStream
import Definitions.Def_Aggmetrics_DataStreamDelay
import Definitions.Def_Aggmetrics_DataStreamDrift

set_option autoImplicit true
open Finset Matrix MeasureTheory ProbabilityTheory Filter
open Aggmetrics Aggmetrics.DataStream
namespace Aggmetrics.DataStream
theorem _root_.solution (R S π : ℝ) :
    HasDerivAt (fun y => accuracy y S π) π R ∧ HasDerivAt (fun y => accuracy R y π) (1 - π) S ∧
      HasDerivAt (fun y => accuracy R S y) (R - S) π := by
  refine ⟨?_, ?_, ?_⟩
  · have h := ((hasDerivAt_id R).const_mul π).add_const ((1 - π) * S)
    convert h using 1 <;> first | rfl | simp [accuracy, sub_eq_add_neg]
  · have h := ((hasDerivAt_id S).const_mul (1 - π)).const_add (π * R)
    convert h using 1 <;> first | rfl | simp [accuracy, sub_eq_add_neg]
  · have h1 := ((hasDerivAt_id π).mul_const R)
    have h2 := (((hasDerivAt_id π).const_sub 1).mul_const S)
    have h := h1.add h2
    convert h using 1 <;> first | rfl | simp [accuracy, sub_eq_add_neg]
end Aggmetrics.DataStream
