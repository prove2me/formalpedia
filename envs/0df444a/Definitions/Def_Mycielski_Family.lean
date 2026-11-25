-- Prove2me | Definitions.Def_Mycielski_Family
-- name    : Mycielski_Family
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T21:25:49.180846+00:00
-- url     : https://prove2.me/theorems/cda4e96f-c7ff-4cc7-9b4a-de8b53ceb04d
-- title:
--   Family
-- statement:
--   Definitions and structural lemmas for Family, from Juan Pablo Traverso Gianini (jtraverso/erdos-girth-chromatic; see pinned Apache-2.0 LICENSE and source headers)'s pinned Graphs of large girth and large chromatic number: Erdos, Mycielski and Tutte development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/erdos-girth-chromatic/blob/05407c110b29ebb412667c688b2758d23bc744dd/Mycielski/Family.lean

module
public import Definitions.Def_Mycielski_Coloring
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace Mycielski
open SimpleGraph
def FamilyVertex : ℕ → Type
  | 0 => Fin 2
  | n + 1 => Vertex (FamilyVertex n)
instance familyVertexFintype : (n : ℕ) → Fintype (FamilyVertex n)
  | 0 => inferInstanceAs (Fintype (Fin 2))
  | n + 1 => by
    letI := familyVertexFintype n
    exact inferInstanceAs (Fintype (Vertex (FamilyVertex n)))
instance familyVertexNonempty : (n : ℕ) → Nonempty (FamilyVertex n)
  | 0 => ⟨(0 : Fin 2)⟩
  | _ + 1 => ⟨none⟩
def family : (n : ℕ) → SimpleGraph (FamilyVertex n)
  | 0 => ⊤
  | n + 1 => graph (family n)
end Mycielski


