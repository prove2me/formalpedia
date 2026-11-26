-- Prove2me | Definitions.Def_FourierJacobi_Analysis_LatticeCore
-- name    : FourierJacobi_Analysis_LatticeCore
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:08:56.223797+00:00
-- url     : https://prove2.me/theorems/15be07cb-9da1-5be4-90cb-59951cb4f41f
-- title:
--   Lattice Core
-- statement:
--   Definitions and structural lemmas for Lattice Core, from Abhishek Saha (abhisaha-git/fourier-jacobi-core-evaluation; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Explicit Fourier-Jacobi Haar-core evaluation and Abel limits development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/LatticeCore.lean

import Definitions.Def_FourierJacobi_Analysis_I0Master
import Definitions.Def_FourierJacobi_Analysis_I1Assembly
import Definitions.Def_FourierJacobi_Analysis_I2Master
import Definitions.Def_FourierJacobi_Analysis_MasterDamping
import Definitions.Def_FourierJacobi_Analysis_RationalLimits
import Mathlib.Algebra.BigOperators.Field
set_option autoImplicit false
noncomputable section
namespace FourierJacobi.Analysis
open FourierJacobi.Algebra Filter
open scoped Topology
set_option maxHeartbeats 4000000
def latticeCore (q : ℝ) (a b d : ℂ) (T : ℝ) : ℂ :=
  (∑ i : Fin 8, weylWeights (inverseSqrt q : ℂ) a b i *
    ∑ r : Fin 3, ∑' p : LatticeIndex,
      masterTerm (q : ℂ) (inverseSqrt q : ℂ) d (weylU a b i) (weylV a b i)
        (T : ℂ) (r.val : ℤ) p) / paperC q
def weightedLatticeTerm (q : ℝ) (a b d : ℂ) (T : ℝ)
    (p : Fin 8 × Fin 3 × LatticeIndex) : ℂ :=
  (weylWeights (inverseSqrt q : ℂ) a b p.1 / paperC q) *
    masterTerm (q : ℂ) (inverseSqrt q : ℂ) d (weylU a b p.1) (weylV a b p.1)
      (T : ℂ) (p.2.1.val : ℤ) p.2.2
end FourierJacobi.Analysis


