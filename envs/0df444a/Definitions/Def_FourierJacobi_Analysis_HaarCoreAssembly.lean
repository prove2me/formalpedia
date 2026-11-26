-- Prove2me | Definitions.Def_FourierJacobi_Analysis_HaarCoreAssembly
-- name    : FourierJacobi_Analysis_HaarCoreAssembly
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:37:18.950766+00:00
-- url     : https://prove2.me/theorems/a4e32b4c-d5f5-4dfa-a942-45fac400d135
-- title:
--   Haar Core Assembly
-- statement:
--   Definitions and structural lemmas for Haar Core Assembly, from Abhishek Saha (abhisaha-git/fourier-jacobi-core-evaluation; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Explicit Fourier-Jacobi Haar-core evaluation and Abel limits development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/HaarCoreAssembly.lean

import Definitions.Def_FourierJacobi_Analysis_CentralWeylSeries
import Definitions.Def_FourierJacobi_Analysis_FiberIntegration
import Definitions.Def_FourierJacobi_Analysis_HaarCellMaster
set_option autoImplicit false
noncomputable section
namespace FourierJacobi.Analysis
open MeasureTheory FourierJacobi.Algebra FourierJacobi.Valuations FourierJacobi.Measure
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [MeasurableSpace K] [BorelSpace K]
local notation "qK" => (residueCardinality K : ℝ)
local instance _p2m_local_instance_bcb4d405dd_25 : T2Space K := kernelField_t2Space K
local instance _p2m_local_instance_bcb4d405dd_26 : SecondCountableTopology K := kernelField_secondCountable K
local instance _p2m_local_instance_bcb4d405dd_27 : BorelSpace Kˣ := coreUnits_borelSpace K
end FourierJacobi.Analysis


