-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_FamilySeries
-- name    : OAI_NumberTheory_DirichletL_Hecke_FamilySeries
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T19:43:49.213204+00:00
-- url     : https://prove2.me/theorems/4c029651-ee98-4e54-8de5-4a867b87e4f5
-- title:
--   Family Series
-- statement:
--   Definitions and structural lemmas for Family Series, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Hecke/FamilySeries.lean

import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_Family
import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_ThetaSeries
import Definitions.Def_OAI_NumberTheory_DirichletL_Continuation
set_option autoImplicit false
namespace OAI
noncomputable section
namespace SevenEighths.HeckeTheta
open EisensteinTheta
end SevenEighths.HeckeTheta
namespace SevenEighths.HeckeFamily
open EisensteinTheta
end SevenEighths.HeckeFamily
end
end OAI


