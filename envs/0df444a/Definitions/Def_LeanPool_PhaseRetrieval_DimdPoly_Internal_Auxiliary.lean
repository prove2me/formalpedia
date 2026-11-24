-- Prove2me | Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Auxiliary
-- name    : LeanPool_PhaseRetrieval_DimdPoly_Internal_Auxiliary
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T02:23:08.779855+00:00
-- url     : https://prove2.me/theorems/5850d771-b583-4156-959f-c0d2b46c8496
-- title:
--   Auxiliary
-- statement:
--   Definitions and structural lemmas for Auxiliary, from Susanna Bertolini, Jaume de Dios Pont (susannabertolini/PhaseRetrieval), and Lean Pool contributors (see pinned LICENSE and NOTICE)'s pinned Stable phase retrieval for finite Hermite-Fock polynomials development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PhaseRetrieval/DimdPoly/Internal/Auxiliary.lean

module
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_PhaseStability
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.Tactic.NormNum.Parity
public import Theorems.Thm_HermitekLEAN_hermiteCoeff_phi0
public import Theorems.Thm_HermitekLEAN_qkn_real
attribute [local simp] HermitekLEAN.hermiteCoeff_phi0
attribute [local simp] HermitekLEAN.qkn_real


set_option autoImplicit true
@[expose] public section
@[expose] public section
open scoped BigOperators
noncomputable section
namespace DimdPolyLEAN
def explicitGaussianDensity (d : Nat) (z : Fin d -> ℂ) : ℝ :=
  (1 / Real.pi ^ d) * Real.exp (-Finset.sum Finset.univ (fun q : Fin d => ‖z q‖ ^ 2))
def explicitGamma (d : Nat) : MeasureTheory.Measure (Fin d -> ℂ) :=
  MeasureTheory.volume.withDensity fun z => ENNReal.ofReal (explicitGaussianDensity d z)
def explicitComplexHermite (m n : Nat) (z : ℂ) : ℂ :=
  Finset.sum (Finset.range (min m n + 1)) fun j =>
    ((-1 : ℂ) ^ j) * (Nat.factorial j : ℂ) *
      (Nat.choose m j : ℂ) * (Nat.choose n j : ℂ) *
      z ^ (m - j) * (star z) ^ (n - j)
def explicitPhi1D (k n : Nat) (z : ℂ) : ℂ :=
  (((Real.sqrt ((Nat.factorial n : ℝ) * (Nat.factorial k : ℝ))) : ℂ)⁻¹) *
    explicitComplexHermite n k z
def explicitPhi {d : Nat} (kappa alpha : Fin d -> Nat) (z : Fin d -> ℂ) : ℂ :=
  Finset.prod Finset.univ fun q : Fin d => explicitPhi1D (kappa q) (alpha q) (z q)
def explicitPkappaNorm {d : Nat} (F : Finsupp (Fin d -> Nat) ℂ) : ℝ :=
  Real.sqrt (Finset.sum F.support fun alpha => ‖F alpha‖ ^ 2)
def explicitEvalPkappa {d : Nat} (kappa : Fin d -> Nat) (F : Finsupp (Fin d -> Nat) ℂ) :
    (Fin d -> ℂ) -> ℂ :=
  fun z => F.sum fun alpha c => c * explicitPhi kappa alpha z
def explicitGaussianL2DistanceSq
    {d : ℕ} (P Q : (Fin d -> ℂ) -> ℂ) : ℝ :=
  ∫ z, ‖P z - Q z‖ ^ 2 ∂ explicitGamma d
def explicitModulusDistanceSq
    {d : ℕ} (P Q : (Fin d -> ℂ) -> ℂ) : ℝ :=
  ∫ z, (‖P z‖ - ‖Q z‖) ^ 2 ∂ explicitGamma d
def UnitPhase : Type :=
  { θ : ℂ // ‖θ‖ = 1 }
instance : TopologicalSpace UnitPhase :=
  inferInstanceAs (TopologicalSpace { θ : ℂ // ‖θ‖ = 1 })
instance : MetricSpace UnitPhase :=
  inferInstanceAs (MetricSpace { θ : ℂ // ‖θ‖ = 1 })
instance : CompactSpace UnitPhase := by
  change CompactSpace { θ : ℂ // ‖θ‖ = 1 }
  apply isCompact_iff_compactSpace.mp
  have h : IsCompact (Metric.sphere (0 : ℂ) 1) := isCompact_sphere (0 : ℂ) 1
  have hset : {z : ℂ | ‖z‖ = 1} = Metric.sphere (0 : ℂ) 1 := by
    ext z
    change (‖z‖ = 1) ↔ z ∈ Metric.sphere (0 : ℂ) 1
    rw [Metric.mem_sphere, dist_zero_right]
  change IsCompact ({z : ℂ | ‖z‖ = 1} : Set ℂ)
  rw [hset]
  exact h
instance : Inhabited UnitPhase :=
  ⟨⟨1, by simp⟩⟩
def explicitPhaseOptimizedDistanceSq
    {d : ℕ} (P Q : (Fin d -> ℂ) -> ℂ) : ℝ :=
  sInf (Set.range fun θ : UnitPhase =>
    explicitGaussianL2DistanceSq P (fun z => θ.1 * Q z))
def explicitHermiteLpPolys
    {d : ℕ} (κ : Fin d -> ℕ) :
    Set (MeasureTheory.Lp ℂ 2 (explicitGamma d)) :=
  { f |
    ∃ P : (Fin d -> ℂ) -> ℂ,
      P ∈ Set.range (explicitEvalPkappa κ) ∧
        ∃ hP : MeasureTheory.MemLp P 2 (explicitGamma d), hP.toLp P = f }
def explicitClosureOfHermitePolys
    {d : ℕ} (κ : Fin d -> ℕ) : Set ((Fin d -> ℂ) -> ℂ) :=
  { Q |
    ∃ hQ : MeasureTheory.MemLp Q 2 (explicitGamma d),
      hQ.toLp Q ∈ closure (explicitHermiteLpPolys κ) }
def explicitSequentialClosureOfHermitePolys
    {d : ℕ} (κ : Fin d -> ℕ) : Set ((Fin d -> ℂ) -> ℂ) :=
  { Q |
    MeasureTheory.MemLp Q 2 (explicitGamma d) ∧
      ∃ Qn : ℕ -> (Fin d -> ℂ) -> ℂ,
        (∀ n, Qn n ∈ Set.range (explicitEvalPkappa κ)) ∧
          Filter.Tendsto
            (fun n => explicitGaussianL2DistanceSq (Qn n) Q)
            Filter.atTop (nhds (0 : ℝ)) }
end DimdPolyLEAN


