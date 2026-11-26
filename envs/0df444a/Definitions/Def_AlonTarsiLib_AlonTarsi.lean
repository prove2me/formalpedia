-- Prove2me | Definitions.Def_AlonTarsiLib_AlonTarsi
-- name    : AlonTarsiLib_AlonTarsi
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T02:22:51.780472+00:00
-- url     : https://prove2.me/theorems/0c4afe16-5765-5a50-b4f6-6796a4364123
-- title:
--   Alon Tarsi
-- statement:
--   Definitions and structural lemmas for Alon Tarsi, from Juan Pablo Traverso Gianini (jtraverso/alon-tarsi-choosability; see pinned Apache-2.0 LICENSE and source headers)'s pinned The Alon-Tarsi theorem and 3-choosability of planar bipartite graphs development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/alon-tarsi-choosability/blob/4ab98b11f340ea2160b34d0b57ef7102452b98cc/AlonTarsiLib/AlonTarsi.lean

module
public import Mathlib
public import Definitions.Def_LeanPool_K5MinorFreeChoosability_Planar_Embedding
public import Definitions.Def_AlonTarsiLib_GraphPolynomial
public import Definitions.Def_AlonTarsiLib_PlanarSparse
set_option autoImplicit true
@[expose] public section
@[expose] public section
open Finset SimpleGraph
namespace AlonTarsi
variable {V : Type*} [Fintype V] [DecidableEq V]
def IsOrientation (G : SimpleGraph V) (D : V → V → Prop) : Prop :=
  (∀ u v, D u v → G.Adj u v) ∧ (∀ u v, G.Adj u v → D u v ∨ D v u) ∧ ∀ u v, D u v → ¬ D v u
open Classical in
/-- The number of Eulerian subdigraphs of `D` (sets of arcs with in-degree equal to out-degree at
every vertex) whose number of arcs has parity `r`. -/
noncomputable def eulerianCount (D : V → V → Prop) (r : ℕ) : ℕ :=
  #{F ∈ (univ.filter fun p : V × V => D p.1 p.2).powerset |
    (∀ v, #{p ∈ F | p.1 = v} = #{p ∈ F | p.2 = v}) ∧ F.card % 2 = r}
end AlonTarsi


