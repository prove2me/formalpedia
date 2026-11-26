-- Prove2me | Definitions.Def_FourierJacobi_Analysis_I2Ambient
-- name    : FourierJacobi_Analysis_I2Ambient
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T10:49:12.271338+00:00
-- url     : https://prove2.me/theorems/270b673f-93ee-500c-9da3-2cd73884e468
-- title:
--   I2 Ambient
-- statement:
--   Definitions and structural lemmas for I2 Ambient, from Abhishek Saha (abhisaha-git/fourier-jacobi-core-evaluation; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Explicit Fourier-Jacobi Haar-core evaluation and Abel limits development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I2Ambient.lean

import Definitions.Def_FourierJacobi_Analysis_I2Assembly
import Mathlib.Data.Fintype.Fin
set_option autoImplicit false
noncomputable section
namespace FourierJacobi.Analysis
open scoped Classical
set_option maxHeartbeats 8000000
set_option maxRecDepth 4096
set_option linter.unusedVariables false
def i2Offset (ν : Fin 25) : Fin 50 := ⟨25 + ν.val, by omega⟩
def i2SpaceLatticeEquiv (ν : Fin 25) : (I2SpatialRow ν × ℕ) ≃
    {p : LatticeIndex // i2SpatialPredicate ν (p.1,p.2.1,p.2.2.1)} where
  toFun p := ⟨(p.1.val.1,p.1.val.2.1,p.1.val.2.2,p.2),p.1.property⟩
  invFun p := (⟨(p.val.1,p.val.2.1,p.val.2.2.1),p.property⟩,p.val.2.2.2)
  left_inv p := by
    rcases p with ⟨⟨⟨k,j,h⟩,hp⟩,c⟩
    rfl
  right_inv p := by
    rcases p with ⟨⟨k,j,h,c⟩,hp⟩
    rfl
def i2RowTerm (q t d U V T : ℂ) (ν : Fin 25) (p : LatticeIndex) : ℂ := by
  classical
  exact if i2SpatialPredicate ν (p.1,p.2.1,p.2.2.1) ∧ i2DepthPredicate ν p.2.2.2
    then masterTerm q t d U V T 2 p else 0
end FourierJacobi.Analysis


