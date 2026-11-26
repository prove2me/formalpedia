-- Prove2me | Definitions.Def_Eden_PeriodicGlobalGrowth
-- name    : Eden_PeriodicGlobalGrowth
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T14:36:34.758915+00:00
-- url     : https://prove2.me/theorems/fde2d1b5-8fec-5975-b26e-1e4e15d7e2a6
-- title:
--   Periodic Global Growth
-- statement:
--   Definitions and structural lemmas for Periodic Global Growth, from Matthew J. Colbrook (MColbrook/Eden_conjecture; see pinned Apache-2.0 LICENSE, NOTICE.md, and formalization.yaml)'s pinned Counterexample to the unrestricted form of Eden's conjecture development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PeriodicGlobalGrowth.lean

import Definitions.Def_Eden_PeriodicGap
import Definitions.Def_Eden_ExteriorCocycle
set_option autoImplicit true
noncomputable section
open Set Filter Topology
namespace Eden
def periodicIntegerGrowthValues (c : ℝ) (k : ℕ) (t : ℝ) : Set ℝ :=
  (fun p => singularValueFunction (fderiv ℝ (evolution c t) p).toLinearMap k) ''
    periodicEquilibriumSet c
def periodicGlobalLogGrowth (c : ℝ) (k : ℕ) (t : ℝ) : ℝ :=
  Real.log (sSup (periodicIntegerGrowthValues c k t))
def periodicGlobalGrowthRate (c : ℝ) (k : ℕ) : ℝ :=
  limUnder atTop (fun t : ℝ => periodicGlobalLogGrowth c k t / t)
end Eden


