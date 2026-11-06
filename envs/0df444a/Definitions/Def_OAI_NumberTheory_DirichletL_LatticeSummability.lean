-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_LatticeSummability
-- name    : OAI_NumberTheory_DirichletL_LatticeSummability
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T19:35:39.960784+00:00
-- url     : https://prove2.me/theorems/42c729f7-e2b5-4983-85e7-5d918789de72
-- title:
--   Lattice Summability
-- statement:
--   Definitions and structural lemmas for Lattice Summability, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/LatticeSummability.lean

import Definitions.Def_OAI_NumberTheory_DirichletL_EisensteinTheta
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Summable
set_option autoImplicit false
namespace OAI
noncomputable section
namespace SevenEighths.LatticeSummability
open EisensteinTheta
end SevenEighths.LatticeSummability
end
end OAI


