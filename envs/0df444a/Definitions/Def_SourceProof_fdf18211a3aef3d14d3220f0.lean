-- Prove2me | Definitions.Def_SourceProof_fdf18211a3aef3d14d3220f0
-- name    : SourceProof_fdf18211a3aef3d14d3220f0
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:02:10.380676+00:00
-- url     : https://prove2.me/theorems/3bbe88cf-41e6-466b-a60f-d6c9d9192992
-- title:
--   StochLean source theorem: ProbabilityTheory.LevyTriplet.weighted_probChar_eq_neg_secondDifference

import Definitions.Def_SourceProof_aa8efee0d1e9dbf694c57465

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-!
# Lévy triplets and the fixed truncation convention

This module fixes the data and truncation convention used by the real Lévy--Khintchine layer.  It
does not store an infinitely-divisible law or a representation theorem inside the triplet.
-/

@[expose] public section

open Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

namespace LevyTriplet

theorem _root_.Prove2MeSourceProof.h_fdf18211a3aef3d14d3220f0 (s t x : ℝ) :
    (secondDifferenceWeight s x : ℝ) •
        Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) =
      -(levyExponentIntegrand (t + s) x + levyExponentIntegrand (t - s) x -
        2 * levyExponentIntegrand t x) := by
  rw [_root_.Prove2MeSourceProof.h_aa8efee0d1e9dbf694c57465]
  simp only [NNReal.smul_def, Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_ofNat]
  simp only [ProbabilityTheory.levyExponentIntegrand]
  have hplus : ((((t + s) * x : ℝ) : ℂ) * Complex.I) =
      (((t * x : ℝ) : ℂ) * Complex.I) + (((s * x : ℝ) : ℂ) * Complex.I) := by
    push_cast
    ring
  have hminus : ((((t - s) * x : ℝ) : ℂ) * Complex.I) =
      (((t * x : ℝ) : ℂ) * Complex.I) + (((-s * x : ℝ) : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [hplus, hminus, Complex.exp_add, Complex.exp_add]
  push_cast
  simp only [Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg, neg_mul]
  rw [show -((s : ℂ) * x * Complex.I) = (-((s : ℂ) * x)) * Complex.I by ring,
    Complex.exp_mul_I]
  simp only [Complex.cos_neg, Complex.sin_neg]
  ring
end LevyTriplet

namespace CompoundPoisson

end CompoundPoisson

namespace LevyTriplet

end LevyTriplet

end ProbabilityTheory


