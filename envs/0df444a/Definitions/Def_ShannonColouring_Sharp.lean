-- Prove2me | Definitions.Def_ShannonColouring_Sharp
-- name    : ShannonColouring_Sharp
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T14:41:39.239824+00:00
-- url     : https://prove2.me/theorems/8593a4a6-41fe-5bee-947f-b93e8fe7d686
-- title:
--   Sharp
-- statement:
--   Definitions and structural lemmas for Sharp, from Juan Pablo Traverso Gianini (jtraverso/shannon-edge-colouring; see pinned Apache-2.0 LICENSE and source headers)'s pinned Shannon's theorem on edge colourings of multigraphs and its sharpness development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/shannon-edge-colouring/blob/d590cfeb50d88710b454905f896aab928fcb5156/ShannonColouring/Sharp.lean

module
public import Definitions.Def_ShannonColouring_Defs
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace ShannonColouring
abbrev ShannonTriangleEdge (Δ : ℕ) : Type := Fin (Δ / 2) ⊕ Fin (Δ / 2) ⊕ Fin ((Δ + 1) / 2)
def shannonTriangle (Δ : ℕ) : ShannonTriangleEdge Δ → Fin 3 × Fin 3
  | .inl _ => (0, 1)
  | .inr (.inl _) => (0, 2)
  | .inr (.inr _) => (1, 2)
end ShannonColouring


