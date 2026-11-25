-- Prove2me | Definitions.Def_SourceProof_52204861332fb91251d9b5c4
-- name    : SourceProof_52204861332fb91251d9b5c4
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T16:14:01.533428+00:00
-- url     : https://prove2.me/theorems/fb6354ec-8aff-4cc1-99f4-99584b0ad72d
-- title:
--   StochLean source theorem: StochLean.monotone_quadraticVariationSum_stop_ceilingPoint

import Definitions.Def_SourceProof_6af35797996d9e85a3ece1b8
import Definitions.Def_SourceProof_d457938a9849bc7c8daf848d
import Definitions.Def_SourceProof_e64beb7d64332a523896d46b
import Definitions.Def_SourceProof_f59fc4a394228730cfab87fb
import Mathlib.Tactic.Order
import Mathlib.Topology.MetricSpace.Pseudo.Basic

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Monotone endpoint-projected square sums

Partial-cell square sums need not increase in time. At partition endpoints
they equal completed-cell sums; composing with the monotone upper endpoint
projection therefore gives genuinely increasing approximants, even for jumps.
-/

@[expose] public section

open Finset Set
open scoped NNReal

namespace StochLean

variable {T : ℝ≥0}

theorem _root_.Prove2MeSourceProof.h_52204861332fb91251d9b5c4
    (π : TimePartition T) (f : ℝ≥0 → ℝ) :
    Monotone (fun s ↦ quadraticVariationSum π (fun t ↦ f (min t (π.ceilingPoint s)))) := by
  intro s t hst
  change StochLean.quadraticVariationSum π (fun u ↦ f (min u (π.ceilingPoint s))) ≤
    StochLean.quadraticVariationSum π (fun u ↦ f (min u (π.ceilingPoint t)))
  rw [_root_.Prove2MeSourceProof.h_d457938a9849bc7c8daf848d π f ((_root_.Prove2MeSourceProof.h_f59fc4a394228730cfab87fb π) s),
    _root_.Prove2MeSourceProof.h_d457938a9849bc7c8daf848d π f ((_root_.Prove2MeSourceProof.h_f59fc4a394228730cfab87fb π) t)]
  exact _root_.Prove2MeSourceProof.h_6af35797996d9e85a3ece1b8 π f ((_root_.Prove2MeSourceProof.h_e64beb7d64332a523896d46b π) hst)
end StochLean


