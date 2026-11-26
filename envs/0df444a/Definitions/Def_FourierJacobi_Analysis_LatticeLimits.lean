-- Prove2me | Definitions.Def_FourierJacobi_Analysis_LatticeLimits
-- name    : FourierJacobi_Analysis_LatticeLimits
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:09:48.8258+00:00
-- url     : https://prove2.me/theorems/8a327151-b7d8-470d-b3b0-6171a618fdd0
-- title:
--   Lattice Limits
-- statement:
--   Definitions and structural lemmas for Lattice Limits, from Abhishek Saha (abhisaha-git/fourier-jacobi-core-evaluation; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Explicit Fourier-Jacobi Haar-core evaluation and Abel limits development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/LatticeLimits.lean

import Definitions.Def_FourierJacobi_Analysis_LatticeCore
import Definitions.Def_FourierJacobi_Analysis_PaperDomain
set_option autoImplicit false
noncomputable section
namespace FourierJacobi.Analysis
open FourierJacobi.Algebra Filter
open scoped Topology
set_option maxHeartbeats 4000000
end FourierJacobi.Analysis


