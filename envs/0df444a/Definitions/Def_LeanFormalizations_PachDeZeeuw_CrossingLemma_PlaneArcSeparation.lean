-- Prove2me | Definitions.Def_LeanFormalizations_PachDeZeeuw_CrossingLemma_PlaneArcSeparation
-- name    : LeanFormalizations_PachDeZeeuw_CrossingLemma_PlaneArcSeparation
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-10-16T04:44:34.712591+00:00
-- url     : https://prove2.me/theorems/74d62748-13aa-49ae-a6fb-73cd0f654a7e
-- title:
--   Simple arcs in a topological space
-- statement:
--   A simple arc is a continuous injective map from the closed unit interval into a topological space.

-- Extracted dependency interfaces and their necessary proofs.
import Mathlib

set_option autoImplicit true

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/

namespace CrossingLemma.PlaneArcSeparation

open Set Topology


structure SimpleArc (X : Type*) [TopologicalSpace X] where
   
  toFun : Set.Icc (0 : ℝ) 1 → X
   
  continuous_toFun : Continuous toFun
   
  injective_toFun : Function.Injective toFun

attribute [coe] SimpleArc.toFun

instance {X : Type*} [TopologicalSpace X] :
    CoeFun (SimpleArc X) (fun _ => Set.Icc (0 : ℝ) 1 → X) := ⟨SimpleArc.toFun⟩

namespace SimpleArc

variable {X : Type*} [TopologicalSpace X]


end SimpleArc


variable {X : Type*} [TopologicalSpace X]


end CrossingLemma.PlaneArcSeparation


