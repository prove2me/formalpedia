-- Prove2me | Definitions.Def_FourierJacobi_Analysis_CentralWeylSeries
-- name    : FourierJacobi_Analysis_CentralWeylSeries
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:10:09.986192+00:00
-- url     : https://prove2.me/theorems/dc732487-39b0-54e8-8fec-ed1560e4177f
-- title:
--   Central Weyl Series
-- statement:
--   Definitions and structural lemmas for Central Weyl Series, from Abhishek Saha (abhisaha-git/fourier-jacobi-core-evaluation; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Explicit Fourier-Jacobi Haar-core evaluation and Abel limits development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/CentralWeylSeries.lean

import Definitions.Def_FourierJacobi_Analysis_LatticeLimits
set_option autoImplicit false
noncomputable section
namespace FourierJacobi.Analysis
open FourierJacobi.Algebra
def centralWeightedTerm (q : ℝ) (a b d : ℂ) (T : ℝ) (r : Fin 3)
    (p : LatticeIndex) : ℂ := ∑ i : Fin 8, weightedLatticeTerm q a b d T (i,r,p)
def centralLatticeCore (q : ℝ) (a b d : ℂ) (T : ℝ) (r : Fin 3) : ℂ :=
  ∑ i : Fin 8, (weylWeights (inverseSqrt q : ℂ) a b i / paperC q) *
    ∑' p : LatticeIndex, masterTerm (q : ℂ) (inverseSqrt q : ℂ) d
      (weylU a b i) (weylV a b i) (T : ℂ) (r.val : ℤ) p
end FourierJacobi.Analysis


