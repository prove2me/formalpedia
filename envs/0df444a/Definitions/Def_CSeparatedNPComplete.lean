-- Prove2me | Definitions.Def_CSeparatedNPComplete
-- name    : CSeparatedNPComplete
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T06:48:07.153308+00:00
-- url     : https://prove2.me/theorems/ca61ff79-5958-5ef9-95c5-222ed3243176
-- title:
--   CSeparated NPComplete
-- statement:
--   Definitions and structural lemmas for CSeparated NPComplete, from Tomislav Prusina (tomo61098/c-separated-np-complete-lean; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Fixed-threshold Gaussian c-separation gadget equivalence and square-partition reduction development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/tomo61098/c-separated-np-complete-lean/blob/d70de3f969dd580506e0835f7d7773890b0a6eaa/CSeparatedNPComplete.lean

module
public import Definitions.Def_CSeparatedNPComplete_Karamata
public import Definitions.Def_CSeparatedNPComplete_CrossGadget
public import Definitions.Def_CSeparatedNPComplete_Gadget
public import Definitions.Def_CSeparatedNPComplete_Reciprocal
public import Definitions.Def_CSeparatedNPComplete_SquarePartition
public import Definitions.Def_CSeparatedNPComplete_SquareReduction
public import Definitions.Def_CSeparatedNPComplete_SquarePartitionResults
public import Definitions.Def_CSeparatedNPComplete_PartitionEquivalence
public import Definitions.Def_CSeparatedNPComplete_PolynomialCertificate
set_option autoImplicit true
@[expose] public section


