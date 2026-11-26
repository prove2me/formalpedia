-- Prove2me | Definitions.Def_FourierJacobi_Analysis_I2Master
-- name    : FourierJacobi_Analysis_I2Master
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:07:45.491082+00:00
-- url     : https://prove2.me/theorems/fc115e38-39d4-5ecd-9c62-0e1c79945d11
-- title:
--   I2 Master
-- statement:
--   Definitions and structural lemmas for I2 Master, from Abhishek Saha (abhisaha-git/fourier-jacobi-core-evaluation; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Explicit Fourier-Jacobi Haar-core evaluation and Abel limits development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I2Master.lean

import Definitions.Def_FourierJacobi_Analysis_I2Ambient
import Definitions.Def_FourierJacobi_Analysis_I2Partition
set_option autoImplicit false
noncomputable section
namespace FourierJacobi.Analysis
open scoped Classical
set_option maxHeartbeats 8000000
set_option maxRecDepth 4096
set_option linter.unusedVariables false
end FourierJacobi.Analysis


