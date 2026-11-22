-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialTriangular_SortedSpec
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialTriangular_SortedSpec
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:31:18.855695+00:00
-- url     : https://prove2.me/theorems/d4474826-5c8b-4a3d-adf5-90d3ec448860
-- title:
--   Sorted Spec
-- statement:
--   Definitions and structural lemmas for Sorted Spec, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExponentialTriangular/SortedSpec.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ExpTri
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
namespace PI.ET
def SortedSpec {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (d : Fin n → ℝ) : Prop :=
  Antitone d ∧ ∃ W ∈ Matrix.unitaryGroup (Fin n) ℂ,
    A = W * Matrix.diagonal (fun i => (d i : ℂ)) * Wᴴ
def psum {n : ℕ} (f : Fin n → ℝ) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < k), f i
def SpecExists : Prop :=
  ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ), Aᴴ = A → ∃ d : Fin n → ℝ, SortedSpec A d
def HSEq : Prop :=
  ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) (d : Fin n → ℝ), SortedSpec A d →
    ∑ i, ∑ j, ‖A i j‖ ^ 2 = ∑ i, d i ^ 2
def KyFanDet : Prop :=
  ∀ (n k : ℕ) (hk : k ≤ n) (p : Fin n → ℝ) (W : Matrix (Fin n) (Fin n) ℂ)
    (V : Matrix (Fin n) (Fin k) ℂ),
    Antitone p → (∀ i, 0 < p i) → W ∈ Matrix.unitaryGroup (Fin n) ℂ → Vᴴ * V = 1 →
    ‖(Vᴴ * (W * Matrix.diagonal (fun i => (p i : ℂ)) * Wᴴ) * V).det‖ ≤
      ∏ i : Fin k, p (Fin.castLE hk i)
def Horn : Prop :=
  ∀ (n : ℕ) (X Y Z U : Matrix (Fin n) (Fin n) ℂ) (ξ η ζ : Fin n → ℝ),
    SortedSpec X ξ → SortedSpec Y η → SortedSpec Z ζ → U ∈ Matrix.unitaryGroup (Fin n) ℂ →
    NormedSpace.exp X * NormedSpace.exp Y = U * NormedSpace.exp Z →
    (∀ k ≤ n, psum ζ k ≤ psum (fun i => ξ i + η i) k) ∧ ∑ i, ζ i = ∑ i, (ξ i + η i)
def AbelSq : Prop :=
  ∀ (n : ℕ) (a b : Fin n → ℝ), Antitone a → (∀ k ≤ n, psum a k ≤ psum b k) →
    ∑ i, a i = ∑ i, b i → ∑ i, a i ^ 2 ≤ ∑ i, b i ^ 2
def EuclTri : Prop :=
  ∀ (n : ℕ) (a b : Fin n → ℝ),
    Real.sqrt (∑ i, (a i + b i) ^ 2) ≤ Real.sqrt (∑ i, a i ^ 2) + Real.sqrt (∑ i, b i ^ 2)
end PI.ET


