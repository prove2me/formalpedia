-- Prove2me | Definitions.Def_FourierJacobi_Analysis_RationalLimits
-- name    : FourierJacobi_Analysis_RationalLimits
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T10:24:44.57439+00:00
-- url     : https://prove2.me/theorems/9f3b35aa-16fd-55bf-8973-49306858d666
-- title:
--   Rational Limits
-- statement:
--   Definitions and structural lemmas for Rational Limits, from Abhishek Saha (abhisaha-git/fourier-jacobi-core-evaluation; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Explicit Fourier-Jacobi Haar-core evaluation and Abel limits development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/RationalLimits.lean

import Definitions.Def_FourierJacobi_Analysis_CoreParameters
import Mathlib.Tactic.FunProp
set_option autoImplicit false
noncomputable section
namespace FourierJacobi.Analysis
open FourierJacobi.Algebra Filter
open scoped Topology
set_option maxHeartbeats 4000000
def dampedRational (t : ℝ) (a b d : ℂ) (T : ℝ) : ℂ :=
  (∑ i : Fin 8, weylWeights (t : ℂ) a b i *
    ∑ ν : Fin 50, regionTerms (t : ℂ) d
      ((T : ℂ) * weylU a b i) ((T : ℂ) * weylV a b i) ν) /
    poincare (t : ℂ)
end FourierJacobi.Analysis


