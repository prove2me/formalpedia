-- Prove2me | Definitions.Def_LeanFormalizations_Combinatorics_CombinatorialMap_PlanarEdgeBound
-- name    : LeanFormalizations_Combinatorics_CombinatorialMap_PlanarEdgeBound
-- status  : Definition
-- author  : @mysticflounder
-- created : 2026-10-16T04:45:15.177362+00:00
-- url     : https://prove2.me/theorems/ddb58e3e-212e-4480-8276-e407ee4fd22f
-- title:
--   Finite multigraphs with unordered endpoints
-- statement:
--   This records a finite vertex type, a finite edge type, and an unordered pair of endpoints for each edge. It also supplies finite types for individual face and edge cycles in a combinatorial map.

-- Extracted dependency interfaces and their necessary proofs.
import Definitions.Def_LeanFormalizations_Combinatorics_CombinatorialMap_Basic
import Mathlib
import Mathlib.Data.Sym.Sym2

set_option autoImplicit true

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/


open scoped BigOperators

namespace CombinatorialMap

variable {D : Type*} {M : CombinatorialMap D}

noncomputable instance instFintypeFaceSameCycle [Fintype D] {w : D} :
    Fintype {u | M.facePerm.SameCycle w u} :=
  Fintype.ofFinite _


noncomputable instance instFintypeEdgeSameCycle [Fintype D] {w : D} :
    Fintype {u | M.edgePerm.SameCycle w u} :=
  Fintype.ofFinite _


end CombinatorialMap


structure AbstractPlanarizedMultigraph where
  Vertex : Type
  Edge : Type
  vertexFintype : Fintype Vertex
  edgeFintype : Fintype Edge
  edgeVerts : Edge → Sym2 Vertex

attribute [instance] AbstractPlanarizedMultigraph.vertexFintype
attribute [instance] AbstractPlanarizedMultigraph.edgeFintype


