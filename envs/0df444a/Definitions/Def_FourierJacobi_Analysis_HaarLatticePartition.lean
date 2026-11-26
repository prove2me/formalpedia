-- Prove2me | Definitions.Def_FourierJacobi_Analysis_HaarLatticePartition
-- name    : FourierJacobi_Analysis_HaarLatticePartition
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:34:55.704864+00:00
-- url     : https://prove2.me/theorems/c0b08600-91c4-57b3-ab7b-09d45685f8f4
-- title:
--   Haar Lattice Partition
-- statement:
--   Definitions and structural lemmas for Haar Lattice Partition, from Abhishek Saha (abhisaha-git/fourier-jacobi-core-evaluation; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Explicit Fourier-Jacobi Haar-core evaluation and Abel limits development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/HaarLatticePartition.lean

import Definitions.Def_FourierJacobi_Analysis_HaarKernel
import Definitions.Def_FourierJacobi_Analysis_MasterSeries
import Definitions.Def_FourierJacobi_Valuations_KernelShells
set_option autoImplicit false
noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory Filter ValuativeRel
namespace FourierJacobi.Analysis
open FourierJacobi.Valuations
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
def CentralRepresentative (r : ℤ) (z : K) : Prop :=
  (r = 0 ∧ z = 0) ∨ (r ≠ 0 ∧ localFieldValuation K z = ((-r : ℤ) : WithTop ℤ))
def haarLatticeCell (r : ℤ) (z : K) (i : LatticeIndex) : Set (HaarPoint K) :=
  {p | localFieldValuation K (p.1 : K) = (i.1 : WithTop ℤ) ∧
    localFieldValuation K p.2.1 = (i.2.1 : WithTop ℤ) ∧
    localFieldValuation K p.2.2 = (i.2.2.1 : WithTop ℤ) ∧
    if r = 0 ∨ 2*i.2.2.1 ≠ i.2.1-r then i.2.2.2 = 0
    else localFieldValuation K (p.2.2^2/(p.2.1*z)-1) =
      ((i.2.2.2 : ℤ) : WithTop ℤ)}
section Measurability
variable [MeasurableSpace K] [BorelSpace K]
local instance _p2m_local_instance_9fc63f53e5_126 : SecondCountableTopology K := kernelField_secondCountable K
local instance _p2m_local_instance_9fc63f53e5_127 : T2Space K := kernelField_t2Space K
end Measurability
end FourierJacobi.Analysis


