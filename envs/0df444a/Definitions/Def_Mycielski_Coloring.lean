-- Prove2me | Definitions.Def_Mycielski_Coloring
-- name    : Mycielski_Coloring
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T21:25:18.895414+00:00
-- url     : https://prove2.me/theorems/5d689d47-c1c9-42c9-b278-3db14bce9397
-- title:
--   Coloring
-- statement:
--   Definitions and structural lemmas for Coloring, from Juan Pablo Traverso Gianini (jtraverso/erdos-girth-chromatic; see pinned Apache-2.0 LICENSE and source headers)'s pinned Graphs of large girth and large chromatic number: Erdos, Mycielski and Tutte development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/erdos-girth-chromatic/blob/05407c110b29ebb412667c688b2758d23bc744dd/Mycielski/Coloring.lean

module
public import Definitions.Def_Mycielski_Basic
public import Mathlib.Logic.Equiv.Fin.Basic
public import Theorems.Thm_Mycielski_apex_adj_shadow
public import Theorems.Thm_Mycielski_not_shadow_adj_shadow
public import Theorems.Thm_Mycielski_original_adj_original
public import Theorems.Thm_Mycielski_original_adj_shadow
public import Theorems.Thm_Mycielski_shadow_adj_apex
public import Theorems.Thm_Mycielski_shadow_adj_original
attribute [local simp] Mycielski.apex_adj_shadow
attribute [local simp] Mycielski.not_shadow_adj_shadow
attribute [local simp] Mycielski.original_adj_original
attribute [local simp] Mycielski.original_adj_shadow
attribute [local simp] Mycielski.shadow_adj_apex
attribute [local simp] Mycielski.shadow_adj_original


set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace Mycielski
open SimpleGraph
universe u v
def liftColoring {V : Type u} {C : Type v} {G : SimpleGraph V}
    (c : G.Coloring C) : (graph G).Coloring (Option C) :=
  Coloring.mk
    (fun x => match x with
      | none => none
      | some (v, _) => some (c v)) (by
        have hc : ∀ {v w}, G.Adj v w → c v ≠ c w := c.valid
        rintro (_ | ⟨v, bv⟩) (_ | ⟨w, bw⟩) <;>
          (try cases bv) <;> (try cases bw) <;>
          simp only [graph, Adj] <;> aesop)
noncomputable def lowerColoring {V : Type u} {C : Type v} {G : SimpleGraph V}
    (c : (graph G).Coloring C) : G.Coloring {a : C // a ≠ c none} := by
  classical
  let f : V → C := fun v =>
    if c (original v) = c none then c (shadow v) else c (original v)
  have hf (v : V) : f v ≠ c none := by
    dsimp [f]
    split
    · exact c.valid (shadow_adj_apex G v)
    · assumption
  refine Coloring.mk (fun v => ⟨f v, hf v⟩) ?_
  intro v w hvw heq
  have heq' : f v = f w := congrArg Subtype.val heq
  dsimp [f] at heq'
  split_ifs at heq' with hv hw hw
  · exact c.valid ((original_adj_original G v w).mpr hvw) (hv.trans hw.symm)
  · exact c.valid ((shadow_adj_original G v w).mpr hvw) heq'
  · exact c.valid ((original_adj_shadow G v w).mpr hvw) heq'
  · exact c.valid ((original_adj_original G v w).mpr hvw) heq'
end Mycielski


