-- Prove2me | Definitions.Def_proofs_PhosphorylationSharpness_Conversion
-- name    : proofs_PhosphorylationSharpness_Conversion
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T07:20:02.756199+00:00
-- url     : https://prove2.me/theorems/8ff19484-88ce-4152-959a-626dbc709a69
-- title:
--   Conversion
-- statement:
--   Definitions and structural lemmas for Conversion, from mmislan (mmislan/palomar-p080-phosphorylation-attainment; see pinned Apache-2.0 LICENSE)'s pinned Sharp lower bound on positive equilibria in sequential distributive phosphorylation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/mmislan/palomar-p080-phosphorylation-attainment/blob/44cb5b18313448ede0f9e0df869c538602ffc66d/proofs/PhosphorylationSharpness/Conversion.lean

import Definitions.Def_proofs_PhosphorylationSharpness_Recurrence
set_option autoImplicit true
namespace PhosphorylationSharpness
noncomputable section
open Polynomial Filter
open scoped Topology
def conversionNumerator (p q : ℝ[X]) (r : ℝ) : ℝ[X] :=
  C (q.eval r)*(X*p) - C (r*p.eval r)*q
def quotient (p q : ℝ[X]) (r : ℝ) : ℝ[X] :=
  conversionNumerator p q r /ₘ (X-C r)
def rawD (p q : ℝ[X]) (r : ℝ) : ℝ[X] := C 4*quotient p q r
def rawB (p q : ℝ[X]) (r : ℝ) : ℝ[X] :=
  C r*rawD p q r + C (4*r*p.eval r-2*q.eval r)*p - C (2*q.eval r)*q
end
end PhosphorylationSharpness


