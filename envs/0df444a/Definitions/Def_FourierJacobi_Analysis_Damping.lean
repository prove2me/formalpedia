-- Prove2me | Definitions.Def_FourierJacobi_Analysis_Damping
-- name    : FourierJacobi_Analysis_Damping
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T09:58:58.106568+00:00
-- url     : https://prove2.me/theorems/e2702603-e289-4c98-946e-b642b74b9bfe
-- title:
--   Damping
-- statement:
--   Definitions and structural lemmas for Damping, from Abhishek Saha (abhisaha-git/fourier-jacobi-core-evaluation; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Explicit Fourier-Jacobi Haar-core evaluation and Abel limits development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/Damping.lean

import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
namespace FourierJacobi
namespace Analysis
open MeasureTheory Filter
open scoped Topology
end Analysis
end FourierJacobi


