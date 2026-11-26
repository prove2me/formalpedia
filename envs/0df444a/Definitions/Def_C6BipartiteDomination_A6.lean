-- Prove2me | Definitions.Def_C6BipartiteDomination_A6
-- name    : C6BipartiteDomination_A6
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T21:44:36.744798+00:00
-- url     : https://prove2.me/theorems/0f3a8ca4-8102-4912-a2f5-37711db7585b
-- title:
--   A6
-- statement:
--   Definitions and structural lemmas for A6, from shouanrenhechun and contributors (shouanrenhechun/Myproofone; see pinned Apache-2.0 LICENSE and source headers)'s pinned Bipartite domination constant c_6 = 8/15 for graphs of maximum degree at most six development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/shouanrenhechun/Myproofone/blob/1ea9e19dd469cb34f9a5ab28e2bed848682905bd/C6BipartiteDomination/A6.lean

import Definitions.Def_C6BipartiteDomination_A5
set_option autoImplicit true
namespace C6BipartiteDomination
open Finset BigOperators
noncomputable section
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V)
noncomputable def degreeTo (A : Finset V) (v : V) : ℕ := by
  classical
  exact (A.filter fun u => G.Adj v u).card
noncomputable def WBPart (D : Finset V) : Finset V :=
  (Finset.univ \ D) \ W0Part G D
noncomputable def PPart (D : Finset V) : Finset V := by
  classical
  exact (BPart G D).biUnion (fun b => privateExternalNeighbors G D b)
noncomputable def SPart (D : Finset V) : Finset V := WBPart G D \ PPart G D
noncomputable def xCharge (D : Finset V) (b : V) : ℕ :=
  (privateExternalNeighbors G D b).card - 2
noncomputable def sCharge (D : Finset V) (b : V) : ℕ :=
  degreeTo G (SPart G D) b
noncomputable def betaCharge (D : Finset V) (w : V) : ℕ :=
  degreeTo G (BPart G D) w
noncomputable def kCharge (D : Finset V) (w : V) : ℕ :=
  degreeTo G (Z0Part G D) w
noncomputable def vertexCharge (D : Finset V) (b : V) : ℤ :=
  9 + 8 * (xCharge G D b : ℤ) - 3 * (sCharge G D b : ℤ)
noncomputable def externalCharge (D : Finset V) (w : V) : ℤ :=
  8 + 3 * (betaCharge G D w : ℤ) - 7 * (kCharge G D w : ℤ)
noncomputable def incidenceTotal (D : Finset V) : ℕ :=
  ∑ w ∈ SPart G D, kCharge G D w
end
end C6BipartiteDomination


