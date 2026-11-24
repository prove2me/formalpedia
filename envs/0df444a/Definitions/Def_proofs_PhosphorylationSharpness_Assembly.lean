-- Prove2me | Definitions.Def_proofs_PhosphorylationSharpness_Assembly
-- name    : proofs_PhosphorylationSharpness_Assembly
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T07:21:03.498981+00:00
-- url     : https://prove2.me/theorems/92baae2f-6f1d-4293-8c8a-311bea3cf12a
-- title:
--   Assembly
-- statement:
--   Definitions and structural lemmas for Assembly, from mmislan (mmislan/palomar-p080-phosphorylation-attainment; see pinned Apache-2.0 LICENSE)'s pinned Sharp lower bound on positive equilibria in sequential distributive phosphorylation development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/mmislan/palomar-p080-phosphorylation-attainment/blob/44cb5b18313448ede0f9e0df869c538602ffc66d/proofs/PhosphorylationSharpness/Assembly.lean

import Definitions.Def_proofs_PhosphorylationSharpness_Conversion
import Definitions.Def_proofs_PhosphorylationSharpness_Source
set_option autoImplicit true
namespace PhosphorylationSharpness
noncomputable section
open Polynomial Filter
open scoped Topology BigOperators
def rootS (x d : ℝ) : ℝ := (x-1)/(2*ratio x*d)
def rootF (x : ℝ) : ℝ := 4/(x+1)
end
end PhosphorylationSharpness


