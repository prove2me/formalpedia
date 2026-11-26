-- Prove2me | Definitions.Def_ChoosabilityLib_ERTGallai
-- name    : ChoosabilityLib_ERTGallai
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T02:30:34.861172+00:00
-- url     : https://prove2.me/theorems/6c53c391-cd27-5407-bfb9-97c1247f152b
-- title:
--   ERTGallai
-- statement:
--   Definitions and structural lemmas for ERTGallai, from Juan Pablo Traverso Gianini (jtraverso/brooks; see pinned Apache-2.0 LICENSE and source headers)'s pinned Erdos-Rubin-Taylor degree-choosability, block-cut trees, and Brooks' theorem development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/brooks/blob/b99e6f500256586626396de9c2d6fd4d96119d60/ChoosabilityLib/ERTGallai.lean

module
public import Definitions.Def_ChoosabilityLib_ERTBasic
set_option autoImplicit true
@[expose] public section
@[expose] public section
open Finset SimpleGraph
namespace ErdosRubinTaylor
variable {V : Type*} {G : SimpleGraph V}
def Gallai (G : SimpleGraph V) (T : Set V) : Prop :=
  ∀ S ⊆ T, 3 ≤ S.ncard → (∀ x ∈ S, (G.induce (S \ {x})).Connected) →
    IsCliqueOn G S ∨ ∃ n, Odd n ∧ Nonempty (G.induce S ≃g cycleGraph n)
section fintype
variable [Fintype V]
end fintype
end ErdosRubinTaylor


