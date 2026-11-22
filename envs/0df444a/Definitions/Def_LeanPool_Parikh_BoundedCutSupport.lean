-- Prove2me | Definitions.Def_LeanPool_Parikh_BoundedCutSupport
-- name    : LeanPool_Parikh_BoundedCutSupport
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T09:48:29.183068+00:00
-- url     : https://prove2.me/theorems/53b8ca92-2952-4874-81f2-0ac960c12fd8
-- title:
--   Bounded Cut Support
-- statement:
--   Definitions and structural lemmas for Bounded Cut Support, from Umang Mathur; LeanPool contributors's pinned Parikh's theorem and a certified semilinear grammar compiler development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Parikh/BoundedCutSupport.lean

module
public import Definitions.Def_LeanPool_Parikh_GrammarTrees
public import Definitions.Def_LeanPool_Parikh_ParseTreePaths
public import Mathlib.Algebra.Order.Group.Nat
set_option autoImplicit true
@[expose] public section
public section
@[expose] section
namespace Parikh
variable {T N : Type*}
namespace ParseTree
end ParseTree
end Parikh


