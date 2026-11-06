-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_Detector_GramCommonSum
-- name    : OAI_NumberTheory_DirichletL_Detector_GramCommonSum
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T19:50:57.128655+00:00
-- url     : https://prove2.me/theorems/e562e49d-7df7-47c8-9fe0-4b17d0b6b55f
-- title:
--   Gram Common Sum
-- statement:
--   Definitions and structural lemmas for Gram Common Sum, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Detector/GramCommonSum.lean

import Definitions.Def_OAI_NumberTheory_DirichletL_Detector_GramCommonParam
set_option autoImplicit false
namespace OAI
noncomputable section
open scoped Classical
namespace SevenEighths.ProbeGramCommon
open CenteredMomentCorrelation
variable {A : Type*} [CommRing A] [IsDomain A]
end SevenEighths.ProbeGramCommon
end
end OAI


