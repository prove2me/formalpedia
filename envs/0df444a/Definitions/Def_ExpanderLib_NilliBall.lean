-- Prove2me | Definitions.Def_ExpanderLib_NilliBall
-- name    : ExpanderLib_NilliBall
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T14:58:52.832916+00:00
-- url     : https://prove2.me/theorems/14874688-e082-43d1-9212-00d0fa180c49
-- title:
--   Nilli Ball
-- statement:
--   Definitions and structural lemmas for Nilli Ball, from Juan Pablo Traverso Gianini (jtraverso/expander-spectral; see pinned Apache-2.0 LICENSE and source headers)'s pinned The expander mixing lemma and the Alon-Boppana bound development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/expander-spectral/blob/f96a99893d4d31495af5f8d9e6181f7b4c91e0ba/ExpanderLib/NilliBall.lean

module
public import Mathlib
set_option autoImplicit true
@[expose] public section
@[expose] public section
open SimpleGraph Matrix Finset
namespace Expanders
section Dist
variable {V : Type*} {G : SimpleGraph V}
end Dist
variable {V : Type*} [Fintype V]
open Classical in
/-- Nilli's test vector: `(s⁻¹) ^ h v` on `B`, and `0` outside `B`. -/
noncomputable def nilliVec (s : ℝ) (B : Finset V) (h : V → ℕ) : V → ℝ :=
  fun v => if v ∈ B then s⁻¹ ^ h v else 0
section Ball
variable (G : SimpleGraph V) [DecidableRel G.Adj] {d k : ℕ} (B : Finset V) (h : V → ℕ)
end Ball
open Classical in
/-- The ball of radius `k + 1` around `u` (within the connected component of `u`). -/
noncomputable def vertexBall (G : SimpleGraph V) (u : V) (k : ℕ) : Finset V :=
  Finset.univ.filter (fun v => G.Reachable u v ∧ G.dist u v ≤ k + 1)
section VertexBall
variable {G : SimpleGraph V} {u : V} {k : ℕ}
end VertexBall
end Expanders


