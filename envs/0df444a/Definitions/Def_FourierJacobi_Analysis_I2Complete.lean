-- Prove2me | Definitions.Def_FourierJacobi_Analysis_I2Complete
-- name    : FourierJacobi_Analysis_I2Complete
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T10:28:34.123819+00:00
-- url     : https://prove2.me/theorems/f80164e1-0f87-40ea-bb33-13595a3c57cd
-- title:
--   I2 Complete
-- statement:
--   Definitions and structural lemmas for I2 Complete, from Abhishek Saha (abhisaha-git/fourier-jacobi-core-evaluation; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Explicit Fourier-Jacobi Haar-core evaluation and Abel limits development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I2Complete.lean

import Definitions.Def_FourierJacobi_Analysis_I2Domains
import Definitions.Def_FourierJacobi_Analysis_I2Convergence
set_option autoImplicit false
noncomputable section
namespace FourierJacobi.Analysis
open FourierJacobi.Valuations
set_option maxHeartbeats 8000000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
def i2DepthAt (ν : Fin 25) : ℕ :=
  if ν.val = 5 ∨ ν.val = 21 then 1
  else if ν.val = 6 ∨ ν.val = 22 then 2 else 0
def i2DepthMass (q : ℂ) (ν : Fin 25) : ℂ :=
  if ν.val = 4 ∨ ν.val = 20 then (q - 2) / (q - 1)
  else if ν.val = 5 ∨ ν.val = 21 then q⁻¹
  else if ν.val = 6 ∨ ν.val = 22 then q⁻¹ ^ 2 / (1 - q⁻¹) else 1
def i2SpatialTerm (q t d U V T : ℂ) (ν : Fin 25) (p : ℤ × ℤ × ℤ) : ℂ :=
  -q * shellMonomial t d U V T 2 p (i2DepthAt ν) * i2DepthMass q ν
def i2RegionTerm (ν : Fin 25) (t d U V : ℂ) : ℂ :=
  let P := 1 - d * V * t
  let N := 1 - V * t / d
  let E := 1 - V ^ 2 * t ^ 2
  let F := 1 - U * t ^ 2
  let G := 1 - U * t ^ 4
  match ν.val with
  | 0 => Algebra.regionTerm25 t d U V P N E F G
  | 1 => Algebra.regionTerm26 t d U V P N E F G
  | 2 => Algebra.regionTerm27 t d U V P N E F G
  | 3 => Algebra.regionTerm28 t d U V P N E F G
  | 4 => Algebra.regionTerm29 t d U V P N E F G
  | 5 => Algebra.regionTerm30 t d U V P N E F G
  | 6 => Algebra.regionTerm31 t d U V P N E F G
  | 7 => Algebra.regionTerm32 t d U V P N E F G
  | 8 => Algebra.regionTerm33 t d U V P N E F G
  | 9 => Algebra.regionTerm34 t d U V P N E F G
  | 10 => Algebra.regionTerm35 t d U V P N E F G
  | 11 => Algebra.regionTerm36 t d U V P N E F G
  | 12 => Algebra.regionTerm37 t d U V P N E F G
  | 13 => Algebra.regionTerm38 t d U V P N E F G
  | 14 => Algebra.regionTerm39 t d U V P N E F G
  | 15 => Algebra.regionTerm40 t d U V P N E F G
  | 16 => Algebra.regionTerm41 t d U V P N E F G
  | 17 => Algebra.regionTerm42 t d U V P N E F G
  | 18 => Algebra.regionTerm43 t d U V P N E F G
  | 19 => Algebra.regionTerm44 t d U V P N E F G
  | 20 => Algebra.regionTerm45 t d U V P N E F G
  | 21 => Algebra.regionTerm46 t d U V P N E F G
  | 22 => Algebra.regionTerm47 t d U V P N E F G
  | 23 => Algebra.regionTerm48 t d U V P N E F G
  | _ => Algebra.regionTerm49 t d U V P N E F G
end FourierJacobi.Analysis


