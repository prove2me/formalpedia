-- Prove2me | Definitions.Def_FourierJacobi_Analysis_I2Assembly
-- name    : FourierJacobi_Analysis_I2Assembly
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T10:44:06.029945+00:00
-- url     : https://prove2.me/theorems/bf4d68b4-75b9-473c-a6f2-7ceed729e843
-- title:
--   I2 Assembly
-- statement:
--   Definitions and structural lemmas for I2 Assembly, from Abhishek Saha (abhisaha-git/fourier-jacobi-core-evaluation; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Explicit Fourier-Jacobi Haar-core evaluation and Abel limits development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I2Assembly.lean

import Definitions.Def_FourierJacobi_Analysis_I2Complete
import Definitions.Def_FourierJacobi_Analysis_I2Predicates
import Definitions.Def_FourierJacobi_Analysis_CoreParameters
set_option autoImplicit false
noncomputable section
namespace FourierJacobi.Analysis
open FourierJacobi.Valuations
set_option maxHeartbeats 8000000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
def i2DepthWeight (q : ℂ) (ν : Fin 25) (p : I2SpatialRow ν) (c : ℕ) : ℂ := by
  classical
  exact if i2DepthPredicate ν c then collisionWeight q 2 p.val.2.1 p.val.2.2 c else 0
def i2BareTerm (q t d U V T : ℂ) (ν : Fin 25) (p : I2SpatialRow ν) : ℂ :=
  -q * shellMonomial t d U V T 2 p.val (i2DepthAt ν)
def i2RowFamily (q t d U V T : ℂ) (ν : Fin 25) (p : I2SpatialRow ν × ℕ) : ℂ := by
  classical
  exact if i2DepthPredicate ν p.2 then
    masterTerm q t d U V T 2 (p.1.val.1, p.1.val.2.1, p.1.val.2.2, p.2) else 0
end FourierJacobi.Analysis


