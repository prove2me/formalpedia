-- Prove2me | Definitions.Def_FourierJacobi_Analysis_HaarKernel
-- name    : FourierJacobi_Analysis_HaarKernel
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:34:19.055233+00:00
-- url     : https://prove2.me/theorems/66359a0a-2b52-4b68-a6af-65a02337f61a
-- title:
--   Haar Kernel
-- statement:
--   Definitions and structural lemmas for Haar Kernel, from Abhishek Saha (abhisaha-git/fourier-jacobi-core-evaluation; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Explicit Fourier-Jacobi Haar-core evaluation and Abel limits development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/HaarKernel.lean

import Definitions.Def_FourierJacobi_Analysis_ExplicitKernel
import Definitions.Def_FourierJacobi_Measure_PaperMultiplicativeHaar
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Theorems.Thm_FourierJacobi_Valuations_localFieldValuation_ne_top

set_option autoImplicit false
noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory
namespace FourierJacobi.Analysis
open FourierJacobi.Algebra FourierJacobi.Valuations
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
def coreScaleExponent (a : Kˣ) : ℤ :=
  (localFieldValuation K (a : K)).untop
    ((localFieldValuation_ne_top K (a : K)).mpr (Units.ne_zero a))
def coreLocalAbs (q : ℝ) (a : Kˣ) : ℝ := q ^ (-coreScaleExponent K a)
abbrev HaarPoint := Kˣ × K × K
def coreAtCentral (z : K) (p : HaarPoint K) : KernelPoint K :=
  (p.1, p.2.1, p.2.2, z)
def explicitCoreIntegrand (q : ℝ) (a b d : ℂ) (T : ℝ) (z : K)
    (p : HaarPoint K) : ℂ :=
  d ^ (coreScaleExponent K p.1) *
    (Real.rpow (coreLocalAbs K q p.1) (3 / 2) : ℂ) *
      (T : ℂ) ^ (kernelHeight K (coreAtCentral K z p)) *
        explicitWeylKernel K (inverseSqrt q : ℂ) a b (coreAtCentral K z p)
def coreCentral (π : Kˣ) (r : Fin 3) : K :=
  if r = 0 then 0 else (π : K) ^ (-(r.val : ℤ))
def coreIntegralPrefactor (q : ℝ) (r : Fin 3) : ℂ :=
  if r = 0 then (1 - (q : ℂ)⁻¹)⁻¹
  else if r = 1 then (q : ℂ)
  else -(q : ℂ) / (1 - (q : ℂ)⁻¹)
section Measurability
variable [MeasurableSpace K] [BorelSpace K]
theorem coreUnits_borelSpace : BorelSpace Kˣ := by
  refine ⟨?_⟩
  change MeasurableSpace.comap (Units.val : Kˣ → K) ‹MeasurableSpace K› = borel Kˣ
  rw [BorelSpace.measurable_eq (α := K)]
  rw [(Units.isEmbedding_val₀ (G₀ := K)).eq_induced, borel_comap]
local instance _p2m_local_instance_d9a05d5624_103 : BorelSpace Kˣ := coreUnits_borelSpace K
def kernelCartanFiber (n B : ℤ) : Set (KernelPoint K) :=
  {p | kernelN K p = n ∧ kernelB K p = B}
def explicitHaarCoreShell (μ : Measure K) (ν : Measure Kˣ)
    (q : ℝ) (a b d : ℂ) (T : ℝ) (π : Kˣ) (r : Fin 3) : ℂ :=
  coreIntegralPrefactor q r * ∫ p : HaarPoint K,
    explicitCoreIntegrand K q a b d T (coreCentral K π r) p ∂ν.prod (μ.prod μ)
def explicitHaarCore (μ : Measure K) (ν : Measure Kˣ)
    (q : ℝ) (a b d : ℂ) (T : ℝ) (π : Kˣ) : ℂ :=
  ∑ r : Fin 3, explicitHaarCoreShell K μ ν q a b d T π r
def paperExplicitHaarCore (a b d : ℂ) (T : ℝ) (π : Kˣ) : ℂ :=
  explicitHaarCore K (FourierJacobi.Measure.additiveHaar K)
    (FourierJacobi.Measure.paperMultiplicativeHaar K)
    (FourierJacobi.Measure.residueCardinality K : ℝ) a b d T π
end Measurability
end FourierJacobi.Analysis


