-- Prove2me | Definitions.Def_FourierJacobi_Analysis_I0Master
-- name    : FourierJacobi_Analysis_I0Master
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T10:18:13.919801+00:00
-- url     : https://prove2.me/theorems/5d6d3f9a-5e1c-46e5-a151-5325a67dd351
-- title:
--   I0 Master
-- statement:
--   Definitions and structural lemmas for I0 Master, from Abhishek Saha (abhisaha-git/fourier-jacobi-core-evaluation; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Explicit Fourier-Jacobi Haar-core evaluation and Abel limits development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I0Master.lean

import Definitions.Def_FourierJacobi_Analysis_I0Complete
import Definitions.Def_FourierJacobi_Analysis_MasterSeries
import Definitions.Def_FourierJacobi_Analysis_CoreParameters
set_option autoImplicit false
noncomputable section
namespace FourierJacobi.Analysis
set_option maxHeartbeats 2000000
def latticeDepthEquiv : ((ℤ × ℤ × ℤ) × ℕ) ≃ LatticeIndex where
  toFun p := (p.1.1, p.1.2.1, p.1.2.2, p.2)
  invFun p := ((p.1, p.2.1, p.2.2.1), p.2.2.2)
  left_inv _ := rfl
  right_inv _ := rfl
end FourierJacobi.Analysis


