-- Prove2me | Definitions.Def_LeanFormalizations_PachDeZeeuw_CrossingLemma_PLCover
-- name    : LeanFormalizations_PachDeZeeuw_CrossingLemma_PLCover
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-10-16T04:44:35.17898+00:00
-- url     : https://prove2.me/theorems/8635aebe-77f6-49a6-8827-e6fa60067b14
-- title:
--   Open-cover data with a split overlap
-- statement:
--   This records two open sets covering a topological space and a decomposition of their overlap into two disjoint open sets. It also equips the two-element residue ring with the discrete topology.

-- Extracted dependency interfaces and their necessary proofs.
import Mathlib

set_option autoImplicit true

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/

namespace CrossingLemma.PLCover

open Set Topology Bundle
open scoped Classical

universe u

 
instance : TopologicalSpace (ZMod 2) := ⊥
instance : DiscreteTopology (ZMod 2) := ⟨rfl⟩

variable {B : Type u} [TopologicalSpace B]


structure GlueData (B : Type u) [TopologicalSpace B] where
  V₀ : Set B
  V₁ : Set B
  Pp : Set B
  Pm : Set B
  isOpen_V₀ : IsOpen V₀
  isOpen_V₁ : IsOpen V₁
  isOpen_Pp : IsOpen Pp
  isOpen_Pm : IsOpen Pm
  cover : V₀ ∪ V₁ = univ
  overlap : V₀ ∩ V₁ = Pp ∪ Pm
  disjoint_Pp_Pm : Disjoint Pp Pm

namespace GlueData

variable (D : GlueData B)


end GlueData

end CrossingLemma.PLCover


