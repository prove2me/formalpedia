-- Prove2me | Definitions.Def_ChoosabilityLib_ERTChoosable
-- name    : ChoosabilityLib_ERTChoosable
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T02:34:17.813223+00:00
-- url     : https://prove2.me/theorems/1692ef1f-01d2-57b4-b93e-3128a80f765b
-- title:
--   ERTChoosable
-- statement:
--   Definitions and structural lemmas for ERTChoosable, from Juan Pablo Traverso Gianini (jtraverso/brooks; see pinned Apache-2.0 LICENSE and source headers)'s pinned Erdos-Rubin-Taylor degree-choosability, block-cut trees, and Brooks' theorem development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/brooks/blob/b99e6f500256586626396de9c2d6fd4d96119d60/ChoosabilityLib/ERTChoosable.lean

module
public import Definitions.Def_ChoosabilityLib_ERTBasic
public import Definitions.Def_BrooksLib_Brooks
set_option autoImplicit true
@[expose] public section
@[expose] public section
open Finset SimpleGraph
namespace ErdosRubinTaylor
variable {V : Type*}
variable [Fintype V]
end ErdosRubinTaylor


