-- Prove2me | Definitions.Def_MarkovProcess_V3H_FiniteTime_DenseTimeFiniteShift_11c70184
-- name    : MarkovProcess_V3H_FiniteTime_DenseTimeFiniteShift_11c70184
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-30T07:34:58.337989+00:00
-- url     : https://prove2.me/theorems/51d00e92-0678-491f-b4f3-236c51ddf085
-- title:
--   MarkovProcess: MarkovProcess_V3H_FiniteTime_DenseTimeFiniteShift_11c70184
-- statement:
--   Source-preserving definitions and embedded lemmas from the pinned Scott Armstrong MarkovProcess Lean library.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/tree/1f8060caa137731fa08029592019eeaf9d997fe5

import Definitions.Def_MarkovProcess_V3H_DenseTime_Shift_b3e2f7d9
import Definitions.Def_MarkovProcess_V3H_Time_CountableDenseTime_721ef7df
import Mathlib.Data.NNRat.Defs
import Mathlib.Data.NNReal.Defs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Encodable
import Mathlib.Logic.Denumerable
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.Probability.Process.Filtration
import Mathlib.Topology.CompactOpen

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-!
# Finite-coordinate shifts on dense-time paths

Addition by a dense time transports finite sets of dense-time coordinates injectively.  This file
provides the resulting coordinate equivalence and relates restriction after shifting a dense-time
path to restriction on the translated finite set.  It makes no probability-law or Markov claim.
-/

namespace MarkovProcess

noncomputable section

namespace DenseTime

/-- The image of a finite dense-time set under addition by `s`. -/
def addFinset (s : DenseTime) (I : Finset DenseTime) : Finset DenseTime :=
  I.map (addOrderEmbedding s).toEmbedding

@[simp]
theorem mem_addFinset (s : DenseTime) (I : Finset DenseTime) (t : DenseTime) :
    t ∈ addFinset s I ↔ ∃ r ∈ I, s + r = t := by
  rw [addFinset, Finset.mem_map]
  constructor
  · rintro ⟨r, hr, hrt⟩
    exact ⟨r, hr, hrt⟩
  · rintro ⟨r, hr, hrt⟩
    exact ⟨r, hr, hrt⟩

/-- Addition by `s` identifies a finite dense-time set with its translated image. -/
def addFinsetEquiv (s : DenseTime) (I : Finset DenseTime) : I ≃ addFinset s I :=
  Equiv.ofBijective
    (fun t ↦ ⟨s + t, (mem_addFinset s I (s + t)).mpr ⟨t, t.property, rfl⟩⟩)
    ⟨by
      intro t u h
      apply Subtype.ext
      apply (addOrderEmbedding s).injective
      exact congrArg Subtype.val h,
    by
      intro t
      obtain ⟨r, hrI, hrt⟩ := (mem_addFinset s I t).mp t.property
      refine ⟨⟨r, hrI⟩, Subtype.ext ?_⟩
      exact hrt⟩

@[simp]
theorem p2m_embedded_7638c81ef9026835 (s : DenseTime) (I : Finset DenseTime) (t : I) :
    (addFinsetEquiv s I t : DenseTime) = s + t := rfl

end DenseTime

namespace DenseTimePath

variable {alpha : Type*}

/-- Reindex a path on a translated finite dense-time set back to the original coordinates. -/
def pullbackAddFinset (s : DenseTime) (I : Finset DenseTime)
    (path : DenseTime.addFinset s I → alpha) : I → alpha :=
  fun t ↦ path (DenseTime.addFinsetEquiv s I t)

@[simp]
theorem p2m_embedded_659110f494c0c8e8 (s : DenseTime) (I : Finset DenseTime)
    (path : DenseTime.addFinset s I → alpha) (t : I) :
    pullbackAddFinset s I path t = path (DenseTime.addFinsetEquiv s I t) := rfl

variable [MeasurableSpace alpha]





end DenseTimePath
end
end MarkovProcess


