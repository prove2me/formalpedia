-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_DensityOfFourierPairingIntegrable
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_DensityOfFourierPairingIntegrable
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:34:56.214919+00:00
-- url     : https://prove2.me/theorems/8602b7b5-943f-4cb9-b8ea-027fcca4fd78
-- title:
--   Density Of Fourier Pairing Integrable
-- statement:
--   Definitions and structural lemmas for Density Of Fourier Pairing Integrable, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/DensityOfFourierPairingIntegrable.lean

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SecondCountableHermC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Real Complex SchwartzMap FourierTransform
open scoped ENNReal NNReal RealInnerProductSpace Topology ContDiff Manifold
noncomputable section
namespace GlobalTheory.CompanionTheory.WhitFree.AvgInf.Dens
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
def chf (m : Measure V) (ξ : V) : ℂ := ∫ y, Complex.exp (2 * π * I * ((⟪y, ξ⟫ : ℝ) : ℂ)) ∂m
section Pair
variable {T : Type} [AddCommGroup T] [Module ℝ T] [FiniteDimensional ℝ T] [TopologicalSpace T]
  [IsTopologicalAddGroup T] [ContinuousSMul ℝ T] [T2Space T] [LocallyCompactSpace T]
  [SecondCountableTopology T] [MeasurableSpace T] [BorelSpace T]
end Pair
section Transport
variable {T : Type} [AddCommGroup T] [Module ℝ T] [FiniteDimensional ℝ T] [TopologicalSpace T]
  [IsTopologicalAddGroup T] [ContinuousSMul ℝ T] [T2Space T] [LocallyCompactSpace T]
  [SecondCountableTopology T] [MeasurableSpace T] [BorelSpace T]
  {X H : Type} [MeasurableSpace X] [MeasurableSpace H]
end Transport
section Herm
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch
instance moduleHermC (n : ℕ) : Module ℝ (hermC n) :=
  inferInstanceAs (Module ℝ (selfAdjoint (Matrix (Fin n) (Fin n) ℂ)))
theorem coe_smul_hermC {n : ℕ} (r : ℝ) (b : hermC n) :
    ((r • b : hermC n) : Matrix (Fin n) (Fin n) ℂ) = r • (b : Matrix (Fin n) (Fin n) ℂ) := rfl
def coeHermC (n : ℕ) : hermC n →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ where
  toFun b := b
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
instance finiteHermC (n : ℕ) : FiniteDimensional ℝ (hermC n) :=
  FiniteDimensional.of_injective (coeHermC n) Subtype.val_injective
instance contSMulHermC (n : ℕ) : ContinuousSMul ℝ (hermC n) :=
  ⟨Continuous.subtype_mk (continuous_fst.smul (continuous_subtype_val.comp continuous_snd)) _⟩
variable {W : Type} [Fintype W]
def pairC (n : ℕ) (c : W → ℝ) : (W → hermC n) →ₗ[ℝ] (W → hermC n) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun u v => ∑ w, c w * (Matrix.trace ((u w : Matrix (Fin n) (Fin n) ℂ) *
      (v w : Matrix (Fin n) (Fin n) ℂ))).re)
    (fun u u' v => by
      simp [Matrix.add_mul, Matrix.trace_add, mul_add, Finset.sum_add_distrib])
    (fun r u v => by
      simp [coe_smul_hermC, Matrix.trace_smul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun w _ => ?_
      ring)
    (fun u v v' => by
      simp [Matrix.mul_add, Matrix.trace_add, mul_add, Finset.sum_add_distrib])
    (fun r u v => by
      simp [coe_smul_hermC, Matrix.trace_smul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun w _ => ?_
      ring)
end Herm
end GlobalTheory.CompanionTheory.WhitFree.AvgInf.Dens


