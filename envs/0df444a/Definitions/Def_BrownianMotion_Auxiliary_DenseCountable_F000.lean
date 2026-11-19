-- Prove2me | Definitions.Def_BrownianMotion_Auxiliary_DenseCountable_F000
-- name    : BrownianMotion_Auxiliary_DenseCountable_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-18T17:03:01.810597+00:00
-- url     : https://prove2.me/theorems/68ee3c7c-1ed9-44e6-a3ac-2a0546167916
-- title:
--   Source declarations: BrownianMotion.Auxiliary.DenseCountable
-- statement:
--   Source-preserving Lean declaration bundle from BrownianMotion.Auxiliary.DenseCountable, retaining definitions, helper results, proofs and elaboration context where present.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Mathlib.Topology.Bases

/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/

/-!
# A dense countable subset of a second-countable topological space

-/

@[expose] public section

/-- A countable dense subset of a second-countable topological space. -/
def denseCountable (T : Type*) [TopologicalSpace T] [SecondCountableTopology T] : Set T :=
  (TopologicalSpace.exists_countable_dense T).choose
lemma dense_denseCountable {T : Type*} [TopologicalSpace T] [SecondCountableTopology T] :
    Dense (denseCountable T) :=
  (TopologicalSpace.exists_countable_dense T).choose_spec.2
lemma countable_denseCountable {T : Type*} [TopologicalSpace T] [SecondCountableTopology T] :
    (denseCountable T).Countable :=
  (TopologicalSpace.exists_countable_dense T).choose_spec.1


