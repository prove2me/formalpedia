-- Prove2me | Definitions.Def_FourierJacobi_Measure_JointCollision
-- name    : FourierJacobi_Measure_JointCollision
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:33:07.541552+00:00
-- url     : https://prove2.me/theorems/7e336cc3-1f2a-48b6-bbdf-7d93f2ab8af1
-- title:
--   Joint Collision
-- statement:
--   Definitions and structural lemmas for Joint Collision, from Abhishek Saha (abhisaha-git/fourier-jacobi-core-evaluation; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Explicit Fourier-Jacobi Haar-core evaluation and Abel limits development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Measure/JointCollision.lean

import Definitions.Def_FourierJacobi_Measure_ShellCollision
import Definitions.Def_FourierJacobi_Valuations_KernelIndices
set_option autoImplicit false
noncomputable section
open MeasureTheory ValuativeRel FourierJacobi.Valuations
namespace FourierJacobi.Measure
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
local instance jointCollision_t2Space : T2Space K := by
  let := IsTopologicalAddGroup.rightUniformSpace K
  let := isUniformAddGroup_of_addCommGroup (G := K)
  infer_instance
def jointCollisionDepth (z : K) (j h s : ℤ) (c : ℕ) : Set (K × K) :=
  {p | localFieldValuation K p.1 = (h : WithTop ℤ) ∧
    localFieldValuation K p.2 = (j : WithTop ℤ) ∧
    localFieldValuation K (p.1 ^ 2 - p.2 * z) =
      ((j + s + (c : ℤ) : ℤ) : WithTop ℤ)}
def sourceJointCollisionDepth (z : K) (j h : ℤ) (c : ℕ) : Set (K × K) :=
  {p | localFieldValuation K p.1 = (j : WithTop ℤ) ∧
    localFieldValuation K p.2 = (h : WithTop ℤ) ∧
    localFieldValuation K (p.2 ^ 2 / (p.1 * z) - 1) = ((c : ℤ) : WithTop ℤ)}
def shellCollisionProbability (c : ℕ) : ℝ :=
  if c = 0 then (residueCardinality K - 2) / (residueCardinality K - 1)
  else (residueCardinality K : ℝ) ^ (-(c : ℤ))
variable [MeasurableSpace K] [BorelSpace K]
local instance jointCollision_secondCountable : SecondCountableTopology K :=
  FourierJacobi.Valuations.kernelField_secondCountable K
local instance jointCollision_additiveHaar_sigmaFinite : SigmaFinite (additiveHaar K) := by
  unfold additiveHaar
  infer_instance
end FourierJacobi.Measure


