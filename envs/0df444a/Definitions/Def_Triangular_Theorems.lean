-- Prove2me | Definitions.Def_Triangular_Theorems
-- name    : Triangular_Theorems
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T18:25:42.913251+00:00
-- url     : https://prove2.me/theorems/bd5a8505-e345-4f9a-8080-34ae30aacf15
-- title:
--   Theorems
-- statement:
--   Definitions and structural lemmas for Theorems, from Joris Roos's pinned The triangular Hilbert transform and Carleson’s theorem development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/roos-j/lean-triangular/blob/670ecd489621258be7e18ae71dbb3c43a1afec04/Triangular/Theorems.lean

module
public import Definitions.Def_Triangular_Defs
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
public import Definitions.Def_Triangular_Auto_Carleson
set_option autoImplicit true
@[expose] public section
public section
@[expose] section
namespace Triangular
open MeasureTheory SchwartzMap Topology Filter Function
end Triangular
end


