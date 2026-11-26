-- Prove2me | Definitions.Def_FourierJacobi_Analysis_ExplicitKernel
-- name    : FourierJacobi_Analysis_ExplicitKernel
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:33:21.509378+00:00
-- url     : https://prove2.me/theorems/2cf93d24-6008-4621-961c-022dfba2b9bf
-- title:
--   Explicit Kernel
-- statement:
--   Definitions and structural lemmas for Explicit Kernel, from Abhishek Saha (abhisaha-git/fourier-jacobi-core-evaluation; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Explicit Fourier-Jacobi Haar-core evaluation and Abel limits development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/ExplicitKernel.lean

import Definitions.Def_FourierJacobi_Valuations_KernelIndices
import Definitions.Def_FourierJacobi_Algebra_UnitaryFinite
set_option autoImplicit false
noncomputable section
set_option maxHeartbeats 1000000
namespace FourierJacobi.Analysis
open FourierJacobi.Algebra FourierJacobi.Valuations
@[irreducible] def weylKernelAtIndices (t a b : ℂ) (n B : ℤ) : ℂ :=
  (poincare t)⁻¹ * ∑ i : Fin 8,
    weylWeights t a b i * t ^ (6 * n + 4 * B) *
      (weylU a b i) ^ n * (weylV a b i) ^ B
section LocalField
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
def explicitWeylKernel (t a b : ℂ) (p : KernelPoint K) : ℂ :=
  ((fun nb : ℤ × ℤ => weylKernelAtIndices t a b nb.1 nb.2) ∘
    (fun s : KernelPoint K => (kernelN K s, kernelB K s))) p
section Measurability
variable [MeasurableSpace K] [BorelSpace K]
end Measurability
end LocalField
end FourierJacobi.Analysis


