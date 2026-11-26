-- Prove2me | Definitions.Def_FourierJacobi_Valuations_KernelShells
-- name    : FourierJacobi_Valuations_KernelShells
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:33:28.040831+00:00
-- url     : https://prove2.me/theorems/c3f20251-d500-50f7-88a1-c956f7868570
-- title:
--   Kernel Shells
-- statement:
--   Definitions and structural lemmas for Kernel Shells, from Abhishek Saha (abhisaha-git/fourier-jacobi-core-evaluation; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Explicit Fourier-Jacobi Haar-core evaluation and Abel limits development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Valuations/KernelShells.lean

import Definitions.Def_FourierJacobi_Valuations_KernelIndices
set_option autoImplicit false
noncomputable section
namespace FourierJacobi.Valuations
open FourierJacobi.LocalMatrix
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
def KernelShellCoordinates (p : KernelPoint K) (r k j h c : ℤ) : Prop :=
  kernelEntryIndex K p = entryMinimum r k j h ∧
  kernelMinorIndex K p = minorMinimum r k j h c ∧
  kernelEll K p = (cartanIndices r k j h c).1 ∧
  kernelN K p = (cartanIndices r k j h c).1 / 2 ∧
  kernelB K p = (cartanIndices r k j h c).2 ∧
  kernelHeight K p = (cartanIndices r k j h c).1 / 2 +
    (cartanIndices r k j h c).2 ∧
  kernelHeight K p = -entryMinimum r k j h
end FourierJacobi.Valuations


