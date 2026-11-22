-- Prove2me | Definitions.Def_LeanPool_NemytskiiLebesgue_Frechet
-- name    : LeanPool_NemytskiiLebesgue_Frechet
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T18:33:54.993318+00:00
-- url     : https://prove2.me/theorems/a0083007-7a32-4eb8-ac5c-8a5ea0a6a500
-- title:
--   Frechet
-- statement:
--   Definitions and structural lemmas for Frechet, from Petr Girg; Petr Nečesal; Martin Dvořák; Jakub Psutka; LeanPool contributors's pinned Nemytskii operators on Lebesgue spaces development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/NemytskiiLebesgue/Frechet.lean

module
public import Mathlib.Analysis.Calculus.MeanValue
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Continuity
set_option autoImplicit true
@[expose] public section
public section
@[expose] section
namespace NemytskiiLebesgue
open scoped NemytskiiLebesgue
open MeasureTheory _root_.Filter
open scoped ENNReal Topology
end NemytskiiLebesgue


