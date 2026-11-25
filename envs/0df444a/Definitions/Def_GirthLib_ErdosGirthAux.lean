-- Prove2me | Definitions.Def_GirthLib_ErdosGirthAux
-- name    : GirthLib_ErdosGirthAux
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T21:27:25.641384+00:00
-- url     : https://prove2.me/theorems/38537750-e0a6-469d-8de2-3dd275fb2212
-- title:
--   Erdos Girth Aux
-- statement:
--   Definitions and structural lemmas for Erdos Girth Aux, from Juan Pablo Traverso Gianini (jtraverso/erdos-girth-chromatic; see pinned Apache-2.0 LICENSE and source headers)'s pinned Graphs of large girth and large chromatic number: Erdos, Mycielski and Tutte development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/erdos-girth-chromatic/blob/05407c110b29ebb412667c688b2758d23bc744dd/GirthLib/ErdosGirthAux.lean

module
public import Mathlib
set_option autoImplicit true
@[expose] public section
@[expose] public section
open Finset SimpleGraph
namespace ErdosGirth
noncomputable def pairs (m : ℕ) : Finset (Sym2 (Fin m)) := univ.filter (fun e => ¬ e.IsDiag)
noncomputable def wt (m : ℕ) (p : ℝ) (S : Finset (Sym2 (Fin m))) : ℝ :=
  (∏ _e ∈ S, p) * ∏ _e ∈ pairs m \ S, (1 - p)
open Classical in
/-- Weighted count of the cycles of length at most `g` based at `u` all of whose edges lie in
`S`, counted as closed walks of the complete graph. -/
noncomputable def cyc (m g : ℕ) (S : Finset (Sym2 (Fin m))) (u : Fin m) : ℝ :=
  ∑ ℓ ∈ range (g + 1), ∑ c ∈ (⊤ : SimpleGraph (Fin m)).finsetWalkLength ℓ u u,
    if c.IsCycle ∧ c.edges.toFinset ⊆ S then 1 else 0
noncomputable def edgesIn {m : ℕ} (T : Finset (Fin m)) : Finset (Sym2 (Fin m)) :=
  T.offDiag.image Sym2.mk.uncurry
noncomputable def indep (m t : ℕ) (S : Finset (Sym2 (Fin m))) : ℝ :=
  ∑ T ∈ powersetCard t (univ : Finset (Fin m)), if Disjoint (edgesIn T) S then 1 else 0
noncomputable def gr {m : ℕ} (S : Finset (Sym2 (Fin m))) : SimpleGraph (Fin m) :=
  SimpleGraph.fromEdgeSet (S : Set (Sym2 (Fin m)))
end ErdosGirth


