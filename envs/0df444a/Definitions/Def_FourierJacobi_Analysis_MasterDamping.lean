-- Prove2me | Definitions.Def_FourierJacobi_Analysis_MasterDamping
-- name    : FourierJacobi_Analysis_MasterDamping
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T10:23:52.54281+00:00
-- url     : https://prove2.me/theorems/4a17dd0f-123c-5036-a436-26237de9a31f
-- title:
--   Master Damping
-- statement:
--   Definitions and structural lemmas for Master Damping, from Abhishek Saha (abhisaha-git/fourier-jacobi-core-evaluation; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Explicit Fourier-Jacobi Haar-core evaluation and Abel limits development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/MasterDamping.lean

import Definitions.Def_FourierJacobi_Analysis_MasterSeries
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Tactic.FunProp
set_option autoImplicit false
noncomputable section
namespace FourierJacobi.Analysis
open FourierJacobi.Valuations Filter
open scoped Topology
def shellHeight (r : ℤ) (p : ℤ × ℤ × ℤ) : ℕ :=
  (-entryMinimum r p.1 p.2.1 p.2.2).toNat
end FourierJacobi.Analysis


