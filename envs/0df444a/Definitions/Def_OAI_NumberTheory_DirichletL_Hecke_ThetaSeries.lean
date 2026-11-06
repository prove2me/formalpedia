-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_ThetaSeries
-- name    : OAI_NumberTheory_DirichletL_Hecke_ThetaSeries
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T19:42:03.258776+00:00
-- url     : https://prove2.me/theorems/bd707d05-3341-4784-abd2-c10dfeaaf1df
-- title:
--   Theta Series
-- statement:
--   Definitions and structural lemmas for Theta Series, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Hecke/ThetaSeries.lean

import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_Theta
import Definitions.Def_OAI_NumberTheory_DirichletL_LatticeSummability
set_option autoImplicit false
namespace OAI
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace SevenEighths.HeckeTheta
open EisensteinTheta LatticeSummability
end SevenEighths.HeckeTheta
end
end OAI


