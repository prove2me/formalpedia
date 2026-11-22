-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrderIndexAndStrata
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_OrderIndexAndStrata
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:24:43.299817+00:00
-- url     : https://prove2.me/theorems/dab4f0fd-1e76-4de2-bea1-e4f033b32397
-- title:
--   Order Index And Strata
-- statement:
--   Definitions and structural lemmas for Order Index And Strata, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OrderIndexAndStrata.lean

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PointwiseStabiliserParametrisationBijective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedVariables false
namespace Formalism.FourierDecayAlt.P.OrderIndexAndStrata
open Matrix Finset
open Formalism.DoubleCosetMeasures (IsUpUni)
open Formalism.FourierDecayAlt.S3
noncomputable def tb : MassData Unit where
  g := fun _ => 5
  glk := fun _ => 6
  uk := fun _ => 2
  nn := fun _ => 4
  gg := fun _ => 48
  μKp := fun _ => 6
  μKnatp := fun _ => 3
  μKppp := fun _ => 1
  μSp := fun _ => 3
  μSp' := fun _ => 6
  μSppp := fun _ => 1
  μSppp' := fun _ => 2
  Mp := fun _ => 1
  localVolumeAtPlace := fun _ => 1
  μKo := 2
  μSo := 1
  μSo' := 1
  Mo := 4
  localVolumeArchimedean := 1
  μH := 6
  μH' := 6
  μHpp := 2
  μHpp' := 2
  μN := 1/2
  μN' := 1
  volZZ := 1
  volPP := 1
  al := 1
  volG := 6
  volHa := 2
  volHa' := 3
  volNa := 1
  volNa' := 1
  volB := 1
  volH := 1
  volH' := 1
  volN := 2
  volN' := 1
  Coo := 1
  deg := 1
  dimπ := 1
  dimπ' := 1
  ρ0 := 1/3
  ρ0' := 1/2
  d := 1
  d' := 3/2
  n0c := 1
  supdens := 1
  e1 := 1
  δ := 0
  Kgs2 := 4/5
  KV := 1/2
  Sig := 1/6
  KtopV := 1/2
  IntN := 1
  IntC := 1
  IntOO := 1
end Formalism.FourierDecayAlt.P.OrderIndexAndStrata


