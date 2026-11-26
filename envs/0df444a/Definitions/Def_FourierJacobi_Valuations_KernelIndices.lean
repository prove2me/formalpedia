-- Prove2me | Definitions.Def_FourierJacobi_Valuations_KernelIndices
-- name    : FourierJacobi_Valuations_KernelIndices
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:32:35.466382+00:00
-- url     : https://prove2.me/theorems/47dc3d24-efd5-5ac6-9521-c38b491fd61d
-- title:
--   Kernel Indices
-- statement:
--   Definitions and structural lemmas for Kernel Indices, from Abhishek Saha (abhisaha-git/fourier-jacobi-core-evaluation; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Explicit Fourier-Jacobi Haar-core evaluation and Abel limits development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Valuations/KernelIndices.lean

import Definitions.Def_FourierJacobi_Valuations_LocalMatrix
import Definitions.Def_FourierJacobi_Measure_IntegerShells
import Mathlib.MeasureTheory.Constructions.BorelSpace.WithTop
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Theorems.Thm_FourierJacobi_Valuations_actual_minima_finite

set_option autoImplicit false
noncomputable section
namespace FourierJacobi.Valuations
open FourierJacobi.LocalMatrix
variable {K : Type*} [Field K]
def actualEntryInteger (v : AddValuation K (WithTop ℤ)) (a : Kˣ) (x y z : K) : ℤ :=
  (matrixMinimum v (g a x y z)).untop
    (actual_minima_finite v a x y z (Units.ne_zero a)).1
def actualMinorInteger (v : AddValuation K (WithTop ℤ)) (a : Kˣ) (x y z : K) : ℤ :=
  (matrixMinimum v (secondCompound (g a x y z))).untop
    (actual_minima_finite v a x y z (Units.ne_zero a)).2
section LocalField
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
abbrev KernelPoint := Kˣ × K × K × K
def kernelEntryIndex (p : KernelPoint K) : ℤ :=
  actualEntryInteger (localFieldValuation K) p.1 p.2.1 p.2.2.1 p.2.2.2
def kernelMinorIndex (p : KernelPoint K) : ℤ :=
  actualMinorInteger (localFieldValuation K) p.1 p.2.1 p.2.2.1 p.2.2.2
def kernelN (p : KernelPoint K) : ℤ := kernelEntryIndex K p - kernelMinorIndex K p
def kernelB (p : KernelPoint K) : ℤ := kernelMinorIndex K p - 2 * kernelEntryIndex K p
def kernelEll (p : KernelPoint K) : ℤ := 2 * kernelN K p
def kernelHeight (p : KernelPoint K) : ℤ := kernelN K p + kernelB K p
section Measurability
variable [MeasurableSpace K] [BorelSpace K]
local instance kernelField_t2Space : T2Space K := by
  let := IsTopologicalAddGroup.rightUniformSpace K
  let := isUniformAddGroup_of_addCommGroup (G := K)
  infer_instance
local instance kernelField_secondCountable : SecondCountableTopology K := by
  let := IsTopologicalAddGroup.rightUniformSpace K
  let := isUniformAddGroup_of_addCommGroup (G := K)
  let : (Valued.v (R := K) (Γ₀ := ValuativeRel.ValueGroupWithZero K)).RankOne :=
    { hom' := ValuativeRel.IsRankLeOne.nonempty.some.emb (R := K) |>.comp
        MonoidWithZeroHom.ValueGroup₀.embedding
      strictMono' := ValuativeRel.IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  let : NontriviallyNormedField K := Valued.toNontriviallyNormedField
    (L := K) (Γ₀ := ValuativeRel.ValueGroupWithZero K)
  let : ProperSpace K := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace K
  infer_instance
end Measurability
end LocalField
end FourierJacobi.Valuations


