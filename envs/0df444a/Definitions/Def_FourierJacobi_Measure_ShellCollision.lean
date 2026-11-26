-- Prove2me | Definitions.Def_FourierJacobi_Measure_ShellCollision
-- name    : FourierJacobi_Measure_ShellCollision
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T11:41:36.369013+00:00
-- url     : https://prove2.me/theorems/f6ad99a3-f7ae-4bd0-96b9-7ebb905244ed
-- title:
--   Shell Collision
-- statement:
--   Definitions and structural lemmas for Shell Collision, from Abhishek Saha (abhisaha-git/fourier-jacobi-core-evaluation; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Explicit Fourier-Jacobi Haar-core evaluation and Abel limits development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/ShellCollision.lean

import Definitions.Def_FourierJacobi_Measure_IntegerShells
set_option autoImplicit false
noncomputable section
open MeasureTheory ValuativeRel FourierJacobi.Valuations
namespace FourierJacobi.Measure
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
local instance shellCollision_t2Space : T2Space K := by
  let := IsTopologicalAddGroup.rightUniformSpace K
  let := isUniformAddGroup_of_addCommGroup (G := K)
  infer_instance
def shellCollisionTail (a : K) (n : ℤ) (c : ℕ) : Set K :=
  integerShell K n ∩ ((fun x : K => x - a) ⁻¹' integerBall K (n + c))
def shellCollisionDepth (a : K) (n : ℤ) (c : ℕ) : Set K :=
  shellCollisionTail K a n c \ shellCollisionTail K a n (c + 1)
variable [MeasurableSpace K] [BorelSpace K]
def shellConditionalMass (n : ℤ) (s : Set K) : ℝ :=
  (additiveHaar K).real (s ∩ integerShell K n) /
    (additiveHaar K).real (integerShell K n)
end FourierJacobi.Measure


