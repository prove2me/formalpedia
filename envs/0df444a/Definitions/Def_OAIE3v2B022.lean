-- Prove2me | Definitions.Def_OAIE3v2B022
-- name    : OAIE3v2B022
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T09:59:38.506188+00:00
-- url     : https://prove2.me/theorems/04b202ac-3957-4f79-aae4-08e316ba443d
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 23 of 311
-- statement:
--   Definitions bundle 23 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports no other bundle of this split.
--
--   Modules: `Dynamics/CurrentLayerBudget.lean`, `Dynamics/FastTerminalBudget.lean`, `Dynamics/FormalGeometryBudget.lean`, `Dynamics/FormalStageBudget.lean`, `Dynamics/ReducedRelativeBudget.lean`, `Dynamics/StepOneSplittingBudget.lean`, `Dynamics/UniformFormalInductionIteration.lean`, `Estimates/BlockQuotientTriangular.lean`, `Estimates/CyclicCutNeighborhood.lean`, `Estimates/FormalInductionTerminal.lean`, `Estimates/NativeWeightPairRemoval.lean`, `Estimates/RationalFormalStageGeometry.lean`, `Estimates/StepDropTerminalContainment.lean`, `Fourier/JoinedFrequencyQuotientInjectivity.lean`, `Geometry/HorizontalCoordinateBounds.lean`, `Geometry/QuantitativeMetricPartition.lean`, `Geometry/RealSubspaceCoordinateRetraction.lean`, `Lattices/ScalarResidueInteriorCell.lean`, `Linear/QuotientActionMatrix.lean`, `Linear/RankQuotientHeightBudget.lean`, `Linear/StepDropBasisBudget.lean`, `Nilpotent/AmbientBracketCorrectionPolynomials.lean`, `Nilpotent/BracketStepBudget.lean`, `Nilpotent/ControlledBracketToCurrentLayer.lean`, `Nilpotent/SquarefreeBracketHeight.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.QuantitativeMetricPartition
namespace OAI

section

namespace Erdos3

open scoped NNReal

theorem shifted_power_self_mono {p : ℝ} (hp : 0 ≤ p) {C D : ℕ} (hC : 1 ≤ C) (hCD : C ≤ D) :
    (p + C) ^ C ≤ (p + D) ^ D := by
  have hD : (1 : ℝ) ≤ D := by exact_mod_cast hC.trans hCD
  apply (pow_le_pow_left₀ (by positivity) (add_le_add le_rfl (Nat.cast_le.mpr hCD)) C).trans
  exact pow_le_pow_right₀ (by linarith) hCD

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CyclicCutNeighborhood
namespace OAI

section

open scoped BigOperators

namespace Erdos3

def quarterLower (N : ℕ) (i : Fin 4) : ℕ := i.val * N / 4

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.SquarefreeBracketHeight
namespace OAI

section

namespace Erdos3

open Module
open scoped Matrix TensorProduct

variable {L ι κ ν : Type*} [LieRing L] [LieAlgebra ℚ L]
  {E V : Submodule ℚ L}

noncomputable def realBracketSystem (f : Basis ι ℚ (L ⧸ V)) (k : κ → L) :
    (ℝ ⊗[ℚ] L) →ₗ[ℝ] (κ × ι → ℝ) :=
  LinearMap.pi (fun bi => ((f.baseChange ℝ).coord bi.2).comp
    ((V.mkQ.baseChange ℝ).comp
      ({
        toFun := fun x => ⁅x, (1 : ℝ) ⊗ₜ[ℚ] k bi.1⁆
        map_add' := fun x y => add_lie x y _
        map_smul' := fun r x => smul_lie r x _ } :
          (ℝ ⊗[ℚ] L) →ₗ[ℝ] (ℝ ⊗[ℚ] L))))

@[simp] theorem realBracketSystem_apply (f : Basis ι ℚ (L ⧸ V)) (k : κ → L)
    (x : ℝ ⊗[ℚ] L) (bi : κ × ι) :
    realBracketSystem f k x bi =
      (f.baseChange ℝ).repr (V.mkQ.baseChange ℝ ⁅x, (1 : ℝ) ⊗ₜ[ℚ] k bi.1⁆) bi.2 := rfl

noncomputable def bracketSystemLift [Fintype ν] (e : Basis ν ℚ E) :
    (ν → ℝ) →ₗ[ℝ] (ℝ ⊗[ℚ] L) :=
  (E.subtype.baseChange ℝ).comp (e.baseChange ℝ).equivFun.symm.toLinearMap

theorem bracketSystemLift_mem [Fintype ν] (e : Basis ν ℚ E) (x : ν → ℝ) :
    bracketSystemLift e x ∈ E.baseChange ℝ := ⟨(e.baseChange ℝ).equivFun.symm x, rfl⟩

theorem bracketSystemLift_single [Fintype ν] [DecidableEq ν] (e : Basis ν ℚ E) (n : ν) :
    bracketSystemLift e (Pi.single n 1) = (1 : ℝ) ⊗ₜ[ℚ] (e n : L) := by
  simp [bracketSystemLift, Basis.equivFun_symm_apply]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.CurrentLayerBudget
namespace OAI

section

namespace Erdos3

def currentLayerConstructionBudget (p : ℝ) : ℝ := 2 * p + 2

def currentLayerRemovalBudget (p : ℝ) : ℝ :=
  2 * (p + 2) ^ 3 + (currentLayerConstructionBudget p + 2) ^ 36 +
    (currentLayerConstructionBudget p + 2) ^ 18 + currentLayerConstructionBudget p + 5 * p + 10

theorem currentLayerConstructionBudget_nonneg {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ currentLayerConstructionBudget p := by unfold currentLayerConstructionBudget; positivity

theorem currentLayerRemovalBudget_nonneg {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ currentLayerRemovalBudget p := by
  unfold currentLayerRemovalBudget currentLayerConstructionBudget
  positivity

theorem le_currentLayerConstructionBudget {p : ℝ} (hp : 0 ≤ p) :
    p ≤ currentLayerConstructionBudget p := by unfold currentLayerConstructionBudget; linarith

theorem current_layer_construction_budget_bounds {p M : ℝ} (hM : 0 ≤ M)
    (n j l : ℕ) (hn : (n : ℝ) ≤ p) (hj : 1 ≤ j) (hjp : (j : ℝ) ≤ p)
    (hl : (l : ℝ) ≤ Real.exp p) (hMp : M ≤ Real.exp p) :
    ((l * j : ℕ) : ℝ) ≤ Real.exp (currentLayerConstructionBudget p) ∧
      (n : ℝ) / j * M ≤ Real.exp (currentLayerConstructionBudget p) := by
  have hpE : p ≤ Real.exp p := by linarith [Real.add_one_le_exp p]
  have hjR : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hexp : Real.exp (2 * p) ≤ Real.exp (currentLayerConstructionBudget p) := by
    apply Real.exp_le_exp.mpr
    unfold currentLayerConstructionBudget
    linarith
  constructor
  · rw [Nat.cast_mul]
    calc
      _ ≤ Real.exp p * Real.exp p := mul_le_mul hl (hjp.trans hpE) (Nat.cast_nonneg _) (Real.exp_nonneg _)
      _ = Real.exp (2 * p) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := hexp
  · have hdiv : (n : ℝ) / j ≤ n := div_le_self (Nat.cast_nonneg _) hjR
    calc
      _ ≤ (n : ℝ) * M := mul_le_mul_of_nonneg_right hdiv hM
      _ ≤ Real.exp p * Real.exp p := mul_le_mul (hn.trans hpE) hMp hM (Real.exp_nonneg _)
      _ = Real.exp (2 * p) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := hexp

theorem current_layer_coordinate_factor_bound {p : ℝ} (hp : 0 ≤ p)
    (n H : ℕ) (hn : (n : ℝ) ≤ p) (hH : (H : ℝ) ≤ Real.exp p) :
    ((n : ℝ) + 1) * (H + 1) ≤ Real.exp (2 * p + 1) := by
  have hplus : Real.exp p + 1 ≤ Real.exp (p + 1) := by
    calc
      _ ≤ Real.exp p * 2 := by linarith [Real.one_le_exp hp]
      _ ≤ Real.exp p * Real.exp 1 :=
        mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp (1 : ℝ)]) (Real.exp_nonneg _)
      _ = _ := (Real.exp_add _ _).symm
  have hnplus : (n : ℝ) + 1 ≤ Real.exp p := by linarith [Real.add_one_le_exp p]
  have hHplus : (H : ℝ) + 1 ≤ Real.exp (p + 1) := by linarith
  calc
    _ ≤ Real.exp p * Real.exp (p + 1) :=
      mul_le_mul hnplus hHplus (by positivity) (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem current_layer_removal_budget_bounds {p M : ℝ} (hp : 0 ≤ p)
    (a b j J Q l D E : ℕ) (ha : (a : ℝ) ≤ p) (hb : (b : ℝ) ≤ p) (hj : (j : ℝ) ≤ p)
    (hJ : (J : ℝ) ≤ Real.exp p) (hQ : (Q : ℝ) ≤ Real.exp p)
    (hl : (l : ℝ) ≤ Real.exp p) (hM : M ≤ Real.exp p)
    (hD : (D : ℝ) ≤ Real.exp ((p + 2) ^ 3))
    (hE : (E : ℝ) ≤ Real.exp ((p + 2) ^ 3)) :
    p ≤ currentLayerRemovalBudget p ∧
      ((l * D * E : ℕ) : ℝ) * Real.exp ((currentLayerConstructionBudget p + 2) ^ 36) ≤
        Real.exp (currentLayerRemovalBudget p) ∧
      M + j * ((((a : ℝ) + 1) * (Q + 1)) * (((b : ℝ) + 1) * (J + 1)) *
        Real.exp ((currentLayerConstructionBudget p + 2) ^ 18 + currentLayerConstructionBudget p)) ≤
        Real.exp (currentLayerRemovalBudget p) ∧
      Real.exp ((currentLayerConstructionBudget p + 2) ^ 36) ≤ Real.exp (currentLayerRemovalBudget p) ∧
      (((b : ℝ) + 1) * (J + 1)) *
        Real.exp ((currentLayerConstructionBudget p + 2) ^ 18 + currentLayerConstructionBudget p) ≤
        Real.exp (currentLayerRemovalBudget p) ∧
      (E : ℝ) * Real.exp ((currentLayerConstructionBudget p + 2) ^ 36) ≤
        Real.exp (currentLayerRemovalBudget p) := by
  let t := currentLayerConstructionBudget p
  let u := (p + 2) ^ 3
  let r := (t + 2) ^ 36
  let v := (t + 2) ^ 18 + t
  have ht : 0 ≤ t := currentLayerConstructionBudget_nonneg hp
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hq : currentLayerRemovalBudget p = 2 * u + r + v + 5 * p + 10 := by
    dsimp [currentLayerRemovalBudget, u, r, v, t]
    ring
  have hpq : p ≤ currentLayerRemovalBudget p := by rw [hq]; linarith
  have hdenExp : p + u + u + r ≤ currentLayerRemovalBudget p := by rw [hq]; linarith
  have hsizeExp : 5 * p + 2 + v + 1 ≤ currentLayerRemovalBudget p := by rw [hq]; linarith
  have hrq : r ≤ currentLayerRemovalBudget p := by rw [hq]; linarith
  have hcorrExp : 2 * p + 1 + v ≤ currentLayerRemovalBudget p := by rw [hq]; linarith
  have hgridExp : u + r ≤ currentLayerRemovalBudget p := by rw [hq]; linarith
  have hfQ := current_layer_coordinate_factor_bound hp a Q ha hQ
  have hfJ := current_layer_coordinate_factor_bound hp b J hb hJ
  have hpE : p ≤ Real.exp p := by linarith [Real.add_one_le_exp p]
  have hcorr : (((b : ℝ) + 1) * (J + 1)) * Real.exp v ≤ Real.exp (2 * p + 1 + v) := by
    calc
      _ ≤ Real.exp (2 * p + 1) * Real.exp v := mul_le_mul_of_nonneg_right hfJ (Real.exp_nonneg _)
      _ = _ := (Real.exp_add _ _).symm
  refine ⟨hpq, ?_, ?_, Real.exp_le_exp.mpr hrq,
    hcorr.trans (Real.exp_le_exp.mpr hcorrExp), ?_⟩
  · rw [Nat.cast_mul, Nat.cast_mul]
    calc
      _ ≤ (Real.exp p * Real.exp u * Real.exp u) * Real.exp r := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
        exact mul_le_mul (mul_le_mul hl hD (Nat.cast_nonneg _) (Real.exp_nonneg _)) hE
          (Nat.cast_nonneg _) (by positivity)
      _ = Real.exp (p + u + u + r) := by rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      _ ≤ _ := Real.exp_le_exp.mpr hdenExp
  · have hproduct : j * ((((a : ℝ) + 1) * (Q + 1)) * (((b : ℝ) + 1) * (J + 1)) * Real.exp v) ≤
        Real.exp (5 * p + 2 + v) := by
      calc
        _ ≤ Real.exp p * ((Real.exp (2 * p + 1) * Real.exp (2 * p + 1)) * Real.exp v) := by
          apply mul_le_mul (hj.trans hpE) _ (by positivity) (Real.exp_nonneg _)
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul hfQ hfJ (by positivity) (Real.exp_nonneg _)) (Real.exp_nonneg _)
        _ = _ := by rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
    have hM' : M ≤ Real.exp (5 * p + 2 + v) := hM.trans (Real.exp_le_exp.mpr (by linarith))
    calc
      _ ≤ Real.exp (5 * p + 2 + v) * 2 := by linarith
      _ ≤ Real.exp (5 * p + 2 + v) * Real.exp 1 :=
        mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp (1 : ℝ)]) (Real.exp_nonneg _)
      _ = Real.exp (5 * p + 2 + v + 1) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr hsizeExp
  · calc
      _ ≤ Real.exp u * Real.exp r := mul_le_mul_of_nonneg_right hE (Real.exp_nonneg _)
      _ = Real.exp (u + r) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr hgridExp

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.FastTerminalBudget
namespace OAI

section

namespace Erdos3

def doublePowerParameter (a b : ℕ) (p : ℝ) : ℝ := p + (3 * p + 2) ^ a + (p + 2) ^ b + 2

theorem doublePowerParameter_controls (a b : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    p ≤ doublePowerParameter a b p ∧ (3 * p + 2) ^ a ≤ doublePowerParameter a b p ∧
      (p + 2) ^ b ≤ doublePowerParameter a b p := by
  have h₁ : 0 ≤ (3 * p + 2) ^ a := by positivity
  have h₂ : 0 ≤ (p + 2) ^ b := by positivity
  have hlast : p + (3 * p + 2) ^ a + (p + 2) ^ b ≤ doublePowerParameter a b p :=
    le_add_of_nonneg_right (by norm_num)
  refine ⟨?_, ?_, ?_⟩
  · exact ((le_add_of_nonneg_right h₁).trans (le_add_of_nonneg_right h₂)).trans hlast
  · exact ((le_add_of_nonneg_left hp).trans (le_add_of_nonneg_right h₂)).trans hlast
  · exact (le_add_of_nonneg_left (add_nonneg hp h₁)).trans hlast

end Erdos3

end

section

namespace Erdos3

def fastTerminalParameter (p : ℝ) : ℝ := doublePowerParameter 294 7 p

theorem fastTerminalParameter_controls {p : ℝ} (hp : 0 ≤ p) :
    p ≤ fastTerminalParameter p ∧ (3 * p + 2) ^ 294 ≤ fastTerminalParameter p ∧
      (p + 2) ^ 7 ≤ fastTerminalParameter p :=
  doublePowerParameter_controls 294 7 hp

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.QuotientActionMatrix
namespace OAI

section

namespace Erdos3

open Module
open scoped Matrix

variable {K V W ι κ : Type*} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W] [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem quotient_basis_representative (e : Basis ι K V) (f : Basis κ K W)
    (q : V →ₗ[K] W) (D : Matrix κ ι K) (S : Matrix ι κ K)
    (hD : LinearMap.toMatrix e f q = D) (hDS : D * S = 1) (y : κ → K) :
    f.equivFun.symm y = q (e.equivFun.symm (S *ᵥ y)) := by
  apply f.equivFun.injective
  rw [LinearEquiv.apply_symm_apply]
  change y = f.repr (q (e.equivFun.symm (S *ᵥ y)))
  rw [← LinearMap.toMatrix_mulVec_repr e f q, hD]
  change y = D *ᵥ e.equivFun (e.equivFun.symm (S *ᵥ y))
  rw [LinearEquiv.apply_symm_apply, Matrix.mulVec_mulVec, hDS, Matrix.one_mulVec]

theorem quotient_action_matrix (e : Basis ι K V) (f : Basis κ K W)
    (q : V →ₗ[K] W) (A : V →ₗ[K] V) (B : W →ₗ[K] W)
    (hAB : ∀ x, q (A x) = B (q x)) (S : Matrix ι κ K)
    (hS : LinearMap.toMatrix e f q * S = 1) :
    LinearMap.toMatrix f f B = LinearMap.toMatrix e f q * LinearMap.toMatrix e e A * S := by
  let L := Matrix.toLin f e S
  have hqL : q.comp L = LinearMap.id := by
    apply (LinearMap.toMatrix f f).injective
    rw [LinearMap.toMatrix_comp f e f, LinearMap.toMatrix_id]
    change LinearMap.toMatrix e f q * LinearMap.toMatrix f e (Matrix.toLin f e S) = 1
    rw [LinearMap.toMatrix_toLin, hS]
  have he : B = q.comp (A.comp L) := by
    ext x
    change B x = q (A (L x))
    rw [hAB, show q (L x) = x from DFunLike.congr_fun hqL x]
  rw [he, LinearMap.toMatrix_comp f e f, LinearMap.toMatrix_comp f e e]
  change LinearMap.toMatrix e f q *
    (LinearMap.toMatrix e e A * LinearMap.toMatrix f e (Matrix.toLin f e S)) = _
  rw [LinearMap.toMatrix_toLin, Matrix.mul_assoc]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.AmbientBracketCorrectionPolynomials
namespace OAI

section

namespace Erdos3

open Module
open scoped Matrix TensorProduct NNReal

variable {L μ ν : Type*} [LieRing L] [LieAlgebra ℚ L] {E : Submodule ℚ L}

noncomputable def bracketLiftMatrix (b : Basis μ ℚ L) (e : Basis ν ℚ E) : Matrix μ ν ℚ :=
  fun i j => b.repr (e j : L) i

theorem bracketSystemLift_coordinates [Fintype μ] [Fintype ν]
    (b : Basis μ ℚ L) (e : Basis ν ℚ E) (x : ν → ℝ) :
    (b.baseChange ℝ).equivFun (bracketSystemLift e x) =
      (fun i j => (bracketLiftMatrix b e i j : ℝ)) *ᵥ x := by
  classical
  have h : (b.baseChange ℝ).equivFun.toLinearMap.comp (bracketSystemLift e) =
      Matrix.mulVecLin (fun i j => (bracketLiftMatrix b e i j : ℝ)) := by
    apply (Pi.basisFun ℝ ν).ext
    intro j
    change (b.baseChange ℝ).equivFun (bracketSystemLift e (Pi.single j 1)) =
      Matrix.of (fun i n => (bracketLiftMatrix b e i n : ℝ)) *ᵥ Pi.single j 1
    rw [bracketSystemLift_single, Matrix.mulVec_single_one]
    funext i
    simp only [Basis.equivFun_apply, Basis.baseChange_repr_tmul, Matrix.col_apply,
      Matrix.of_apply, bracketLiftMatrix]
    simp [Algebra.smul_def]
  exact DFunLike.congr_fun h x

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.HorizontalCoordinateBounds
namespace OAI

section

namespace Erdos3

open Module
open scoped Matrix TensorProduct NNReal

variable {L ι μ ν : Type*} [LieRing L] [LieAlgebra ℚ L]
  {E V : Submodule ℚ L}

theorem exists_subspace_basis_coordinates [Fintype ν] (e : Basis ν ℚ E)
    (x : ℝ ⊗[ℚ] L) (hx : x ∈ E.baseChange ℝ) :
    ∃ v : ν → ℝ, bracketSystemLift e v = x := by
  obtain ⟨y, rfl⟩ := hx
  refine ⟨(e.baseChange ℝ).equivFun y, ?_⟩
  simp only [bracketSystemLift, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.RealSubspaceCoordinateRetraction
namespace OAI

section

namespace Erdos3

open Module
open scoped TensorProduct

variable {ι κ V W E : Type*} [AddCommGroup V] [Module ℚ V]
  [AddCommGroup W] [Module ℚ W] [AddCommGroup E] [Module ℝ E]

theorem scalarExtension_basis_coordinates (e : Basis ι ℚ V) (f : Basis κ ℚ W)
    (q : V →ₗ[ℚ] W) (i : κ) (j : ι) :
    (f.baseChange ℝ).repr (q.baseChange ℝ ((e.baseChange ℝ) j)) i =
      (f.repr (q (e j)) i : ℝ) := by
  simp only [Basis.baseChange_apply, LinearMap.baseChange_tmul, Basis.baseChange_repr_tmul]
  simp [Algebra.smul_def]

theorem scalarExtension_equiv_matrix [Fintype ι] [DecidableEq ι] [Fintype κ]
    (e : Basis ι ℚ V) (f : Basis κ ℚ W) (b : Basis κ ℝ E)
    (q : V →ₗ[ℚ] W) (u : (ℝ ⊗[ℚ] W) ≃ₗ[ℝ] E)
    (hu : ∀ x i, b.repr (u x) i = (f.baseChange ℝ).repr x i) :
    LinearMap.toMatrix (e.baseChange ℝ) b (u.toLinearMap.comp (q.baseChange ℝ)) =
      (LinearMap.toMatrix e f q).map (Rat.castHom ℝ) := by
  ext i j
  simp only [LinearMap.toMatrix_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
    hu, scalarExtension_basis_coordinates, Matrix.map_apply, Rat.coe_castHom]

end Erdos3

end

section

namespace Erdos3

open Module
open scoped Matrix TensorProduct NNReal

variable {L μ κ : Type*} [LieRing L] [LieAlgebra ℚ L]
  [Fintype μ] [Fintype κ] {E : Submodule ℚ L}

noncomputable def realSubspaceCoordinateMap (b : Basis μ ℚ L) (Q : Matrix κ μ ℚ) :
    (ℝ ⊗[ℚ] L) →ₗ[ℝ] (κ → ℝ) :=
  (Matrix.mulVecLin (fun i j => (Q i j : ℝ))).comp (b.baseChange ℝ).equivFun.toLinearMap

omit [Fintype κ] in
@[simp] theorem realSubspaceCoordinateMap_apply (b : Basis μ ℚ L) (Q : Matrix κ μ ℚ)
    (x : ℝ ⊗[ℚ] L) :
    realSubspaceCoordinateMap b Q x =
      (fun i j => (Q i j : ℝ)) *ᵥ (b.baseChange ℝ).equivFun x := rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FormalInductionTerminal
namespace OAI

section

namespace Erdos3

open Module
open scoped TensorProduct

theorem real_bracket_mem_of_basis {κ K L : Type*} [Fintype κ]
    [AddCommGroup K] [Module ℝ K] [LieRing L] [LieAlgebra ℝ L]
    (b : Basis κ ℝ K) (I : K →ₗ[ℝ] L) (W : Submodule ℝ L) (p : L)
    (h : ∀ k, ⁅p, I (b k)⁆ ∈ W) (x : K) : ⁅p, I x⁆ ∈ W := by
  classical
  rw [← b.sum_repr x, map_sum, lie_sum]
  apply W.sum_mem
  intro k _
  rw [map_smul, lie_smul]
  exact W.smul_mem _ (h k)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.StepDropTerminalContainment
namespace OAI

section

namespace Erdos3

open Module
open scoped TensorProduct

def rightLieLinear {R L : Type*} [Field R] [LieRing L] [LieAlgebra R L] (k : L) : L →ₗ[R] L where
  toFun x := ⁅x, k⁆
  map_add' x y := add_lie x y k
  map_smul' a x := smul_lie a x k

@[simp] theorem rightLieLinear_apply {R L : Type*} [Field R] [LieRing L] [LieAlgebra R L]
    (k x : L) : rightLieLinear (R := R) k x = ⁅x, k⁆ := rfl

variable {L ι κ : Type*} [LieRing L] [LieAlgebra ℚ L]

theorem rightLieLinear_baseChange (k : L) :
    (rightLieLinear (R := ℚ) k).baseChange ℝ = rightLieLinear (R := ℝ) ((1 : ℝ) ⊗ₜ[ℚ] k) := by
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul r x =>
    simp only [LinearMap.baseChange_tmul, rightLieLinear_apply,
      LieAlgebra.ExtendScalars.bracket_tmul, mul_one]

end Erdos3

end

section

namespace Erdos3

open Module
open scoped Matrix

variable {L μ υ χ κ ν : Type*} [LieRing L] [LieAlgebra ℚ L]

theorem stepDrop_quotient_mem_iff {ρ : Type*} (V : Submodule ℚ L)
    (f : Basis ρ ℚ (L ⧸ V)) (x : L) :
    x ∈ V ↔ ∀ i, f.repr (V.mkQ x) i = 0 := by
  simp only [Submodule.mkQ_apply]
  constructor
  · intro hx i
    rw [(Submodule.Quotient.mk_eq_zero V).mpr hx, map_zero]
    rfl
  · intro h
    apply (Submodule.Quotient.mk_eq_zero V).mp
    apply f.repr.injective
    ext i
    simpa only [map_zero, Finsupp.zero_apply] using h i

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RankQuotientHeightBudget
namespace OAI

section

namespace Erdos3

open Module
open scoped Matrix

variable {L μ υ χ κ ν : Type*} [LieRing L] [LieAlgebra ℚ L]
  [Fintype μ] [Fintype υ] [Fintype χ] [Fintype κ] [Fintype ν]

def stepDropBracketHeight (n H : ℕ) : ℕ :=
  (n + 1) * (((n ^ 2 + 1) * (H * H) ^ (n ^ 2)) * H) ^ n

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RationalFormalStageGeometry
namespace OAI

section

namespace Erdos3

def formalBracketMatrixHeight (n H : ℕ) : ℕ :=
  (n + 1) * (((n ^ 2 + 1) * (H * H * H) ^ (n ^ 2)) * H) ^ n

def formalCurrentMatrixHeight (n H : ℕ) : ℕ := (n + 1) * (H * H) ^ n

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.FormalGeometryBudget
namespace OAI

section

namespace Erdos3

theorem formalBracketMatrixHeight_le_exp (n H : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hn : (n : ℝ) ≤ p) (hH : (H : ℝ) ≤ Real.exp p) :
    (formalBracketMatrixHeight n H : ℝ) ≤ Real.exp ((p + 2) ^ 5) := by
  have hh : (H : ℝ) * H * H ≤ Real.exp (3 * p) := by
    calc
      _ ≤ Real.exp p * Real.exp p * Real.exp p :=
        mul_le_mul (mul_le_mul hH hH (Nat.cast_nonneg _) (Real.exp_nonneg _)) hH
          (Nat.cast_nonneg _) (by positivity)
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hpow := pow_le_pow_left₀
    (mul_nonneg (mul_nonneg (Nat.cast_nonneg H) (Nat.cast_nonneg H)) (Nat.cast_nonneg H)) hh (n ^ 2)
  rw [← Real.exp_nat_mul] at hpow
  have hinner : (((n ^ 2 + 1) * (H * H * H) ^ (n ^ 2)) * H : ℕ) ≤
      Real.exp ((n : ℝ) ^ 2 + n ^ 2 * (3 * p) + p) := by
    push_cast
    rw [Real.exp_add, Real.exp_add]
    apply mul_le_mul _ hH (Nat.cast_nonneg H) (by positivity)
    exact mul_le_mul (Real.add_one_le_exp ((n : ℝ) ^ 2))
      (by simpa only [Nat.cast_pow] using hpow) (by positivity) (Real.exp_nonneg _)
  have hout := pow_le_pow_left₀
    (Nat.cast_nonneg (((n ^ 2 + 1) * (H * H * H) ^ (n ^ 2)) * H)) hinner n
  rw [← Real.exp_nat_mul] at hout
  have htotal : (formalBracketMatrixHeight n H : ℝ) ≤
      Real.exp ((n : ℝ) + n * (n ^ 2 + n ^ 2 * (3 * p) + p)) := by
    unfold formalBracketMatrixHeight
    rw [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_pow, Real.exp_add]
    exact mul_le_mul (Real.add_one_le_exp n) hout (by positivity) (Real.exp_nonneg _)
  apply htotal.trans (Real.exp_le_exp.mpr ?_)
  calc
    (n : ℝ) + n * (n ^ 2 + n ^ 2 * (3 * p) + p) ≤
        p + p * (p ^ 2 + p ^ 2 * (3 * p) + p) := by gcongr
    _ ≤ (p + 2) ^ 5 := by
      have h : 0 ≤ p ^ 5 + 7 * p ^ 4 + 39 * p ^ 3 + 79 * p ^ 2 + 79 * p + 32 := by positivity
      nlinarith

theorem formalCurrentMatrixHeight_le_exp (n H : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hn : (n : ℝ) ≤ p) (hH : (H : ℝ) ≤ Real.exp p) :
    (formalCurrentMatrixHeight n H : ℝ) ≤ Real.exp ((p + 2) ^ 3) := by
  have hh : (H : ℝ) * H ≤ Real.exp (2 * p) := by
    rw [show 2 * p = p + p by ring, Real.exp_add]
    exact mul_le_mul hH hH (Nat.cast_nonneg _) (Real.exp_nonneg _)
  have hpow := pow_le_pow_left₀ (mul_nonneg (Nat.cast_nonneg H) (Nat.cast_nonneg H)) hh n
  rw [← Real.exp_nat_mul] at hpow
  have htotal : (formalCurrentMatrixHeight n H : ℝ) ≤ Real.exp ((n : ℝ) + n * (2 * p)) := by
    unfold formalCurrentMatrixHeight
    push_cast
    rw [Real.exp_add]
    exact mul_le_mul (Real.add_one_le_exp n) hpow (by positivity) (Real.exp_nonneg _)
  apply htotal.trans (Real.exp_le_exp.mpr ?_)
  have hnp : (n : ℝ) * (2 * p) ≤ p * (2 * p) := mul_le_mul_of_nonneg_right hn (by positivity)
  have h : 0 ≤ p ^ 3 + 4 * p ^ 2 + 11 * p + 8 := by positivity
  nlinarith

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.BracketStepBudget
namespace OAI

section

namespace Erdos3

def bracketConstructionBudget (p : ℝ) : ℝ := (p + 2) ^ 3 + 3 * p + 2

def bracketCorrectionBudget (p : ℝ) : ℝ :=
  (bracketConstructionBudget p + 2) ^ 36 + (bracketConstructionBudget p + 2) ^ 18 +
    bracketConstructionBudget p + (p + 2) ^ 3 + 2 * p + 1

theorem bracketConstructionBudget_nonneg {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ bracketConstructionBudget p := by unfold bracketConstructionBudget; positivity

theorem bracketCorrectionBudget_nonneg {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ bracketCorrectionBudget p := by
  have hq := bracketConstructionBudget_nonneg hp
  unfold bracketCorrectionBudget
  positivity

theorem bracket_construction_budget_bounds {p : ℝ} (hp : 0 ≤ p) :
    p ≤ bracketConstructionBudget p ∧ (p + 2) ^ 2 ≤ bracketConstructionBudget p ∧
      (p + 2) ^ 3 + p ≤ bracketConstructionBudget p ∧
      3 * p + 1 ≤ bracketConstructionBudget p := by
  have hc : 0 ≤ (p + 2) ^ 3 := by positivity
  have hpow : (p + 2) ^ 2 ≤ (p + 2) ^ 3 :=
    pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ p + 2) (by decide : 2 ≤ 3)
  unfold bracketConstructionBudget
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

theorem bracket_correction_budget_bounds {p : ℝ} (hp : 0 ≤ p)
    (n J D : ℕ) (hn : (n : ℝ) ≤ p) (hJ : (J : ℝ) ≤ Real.exp p)
    (hD : (D : ℝ) ≤ Real.exp ((p + 2) ^ 3)) :
    (((n : ℝ) + 1) * (J + 1)) *
        Real.exp ((bracketConstructionBudget p + 2) ^ 18 + bracketConstructionBudget p) ≤
        Real.exp (bracketCorrectionBudget p) ∧
      (D : ℝ) * Real.exp ((bracketConstructionBudget p + 2) ^ 36) ≤
        Real.exp (bracketCorrectionBudget p) := by
  have hq := bracketConstructionBudget_nonneg hp
  have h36 : 0 ≤ (bracketConstructionBudget p + 2) ^ 36 := by positivity
  have h18 : 0 ≤ (bracketConstructionBudget p + 2) ^ 18 := by positivity
  have h3 : 0 ≤ (p + 2) ^ 3 := by positivity
  constructor
  · calc
      _ ≤ Real.exp (2 * p + 1) *
          Real.exp ((bracketConstructionBudget p + 2) ^ 18 + bracketConstructionBudget p) :=
        mul_le_mul_of_nonneg_right (current_layer_coordinate_factor_bound hp n J hn hJ)
          (Real.exp_nonneg _)
      _ = Real.exp (2 * p + 1 +
          ((bracketConstructionBudget p + 2) ^ 18 + bracketConstructionBudget p)) :=
        (Real.exp_add _ _).symm
      _ ≤ _ := by apply Real.exp_le_exp.mpr; unfold bracketCorrectionBudget; linarith
  · calc
      _ ≤ Real.exp ((p + 2) ^ 3) * Real.exp ((bracketConstructionBudget p + 2) ^ 36) :=
        mul_le_mul_of_nonneg_right hD (Real.exp_nonneg _)
      _ = Real.exp ((p + 2) ^ 3 + (bracketConstructionBudget p + 2) ^ 36) :=
        (Real.exp_add _ _).symm
      _ ≤ _ := by apply Real.exp_le_exp.mpr; unfold bracketCorrectionBudget; linarith

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.ReducedRelativeBudget
namespace OAI

section

namespace Erdos3

def reducedRelativeParameter (s : ℕ) (p : ℝ) : ℝ :=
  2 * p + 2 * (p + (s + 2)) ^ (s + 2) + 4

theorem reducedRelativeParameter_controls (s : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ reducedRelativeParameter s p ∧ p ≤ reducedRelativeParameter s p ∧
      2 * p ≤ reducedRelativeParameter s p ∧
      p + 2 * (p + (s + 2)) ^ (s + 2) + 2 ≤ reducedRelativeParameter s p + 2 := by
  have hd : 0 ≤ (p + (s + 2)) ^ (s + 2) := by positivity
  unfold reducedRelativeParameter
  exact ⟨by positivity, by linarith, by linarith, by linarith⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.JoinedFrequencyQuotientInjectivity
namespace OAI

section

namespace Erdos3

open Module

variable {ι V : Type*} [AddCommGroup V] [Module ℚ V]

noncomputable def frequencyKernelProjection (η : V →ₗ[ℚ] ℚ) (v : V) : V →ₗ[ℚ] V :=
  LinearMap.id - η.smulRight v

@[simp] theorem frequencyKernelProjection_apply (η : V →ₗ[ℚ] ℚ) (v x : V) :
    frequencyKernelProjection η v x = x - η x • v := rfl

theorem frequencyKernelProjection_range (η : V →ₗ[ℚ] ℚ) (v : V) (hv : η v = 1) :
    LinearMap.range (frequencyKernelProjection η v) = LinearMap.ker η := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    change η (y - η y • v) = 0
    simp only [map_sub, map_smul, hv, smul_eq_mul, mul_one, sub_self]
  · intro hx
    refine ⟨x, ?_⟩
    change x - η x • v = x
    rw [show η x = 0 from hx, zero_smul, sub_zero]

theorem frequencyKernel_spanning (b : Basis ι ℚ V) (η : V →ₗ[ℚ] ℚ) (v : V) (hv : η v = 1) :
    Submodule.span ℚ (Set.range (fun i => b i - η (b i) • v)) = LinearMap.ker η := by
  change Submodule.span ℚ (Set.range (frequencyKernelProjection η v ∘ b)) = _
  rw [Set.range_comp, ← Submodule.map_span, b.span_eq, Submodule.map_top,
    frequencyKernelProjection_range η v hv]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ScalarResidueInteriorCell
namespace OAI

section

namespace Erdos3

def residueCellCount (L N : ℕ) : ℕ := 2 * L / N + 1

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.BlockQuotientTriangular
namespace OAI

section

namespace Erdos3

open scoped Matrix

variable {K ι κ : Type*} [Field K] [Fintype ι] [DecidableEq ι] [DecidableEq κ]

theorem block_quotient_unitriangular (ω : ι → ℕ) (ν : κ → ℕ)
    (D : Matrix κ ι K) (M : Matrix ι ι K) (S : Matrix ι κ K)
    (hD : ∀ k i, ν k ≠ ω i → D k i = 0)
    (hS : ∀ i k, ω i ≠ ν k → S i k = 0)
    (hDS : D * S = 1)
    (hM : ∀ i j, ω i ≤ ω j → M i j = (1 : Matrix ι ι K) i j)
    (a b : κ) (hab : ν a ≤ ν b) :
    (D * M * S) a b = (1 : Matrix κ κ K) a b := by
  have he : (D * M * S) a b = (D * (1 : Matrix ι ι K) * S) a b := by
    simp only [Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : ω j = ν b
    · apply congrArg (fun x => x * S j b)
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : ν a = ω i
      · rw [hM i j (by omega)]
      · rw [hD a i hi, zero_mul, zero_mul]
    · rw [hS j b hj, mul_zero, mul_zero]
  rw [he, Matrix.mul_one, hDS]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.ControlledBracketToCurrentLayer
namespace OAI

section

namespace Erdos3

def bracketTransitionBudget (p : ℝ) : ℝ :=
  4 * p + (p + 2) ^ 8 + (p + 2) ^ 9 + 1

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.FormalStageBudget
namespace OAI

section

namespace Erdos3

theorem bracketTransitionBudget_nonneg {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ bracketTransitionBudget p := by unfold bracketTransitionBudget; positivity

theorem le_bracketTransitionBudget {p : ℝ} (hp : 0 ≤ p) :
    p ≤ bracketTransitionBudget p := by
  have h8 : 0 ≤ (p + 2) ^ 8 := by positivity
  have h9 : 0 ≤ (p + 2) ^ 9 := by positivity
  unfold bracketTransitionBudget
  linarith

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.StepOneSplittingBudget
namespace OAI

section

namespace Erdos3

theorem stepOne_linear_budget {p : ℝ} (hp : 0 ≤ p) :
    3 * p + 1 ≤ (p + 2) ^ 4 := by
  have hs : 3 * p + 1 ≤ (p + 2) ^ 2 := by nlinarith [sq_nonneg p]
  exact hs.trans (pow_le_pow_right₀ (by linarith : 1 ≤ p + 2) (by decide : 2 ≤ 4))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.UniformFormalInductionIteration
namespace OAI

section

namespace Erdos3

noncomputable def formalIterationBudget (C : ℕ) (p : ℝ) : ℕ → ℝ
  | 0 => p
  | n + 1 => (formalIterationBudget C p n + C) ^ C

@[simp] theorem formalIterationBudget_zero (C : ℕ) (p : ℝ) : formalIterationBudget C p 0 = p := rfl

@[simp] theorem formalIterationBudget_succ (C : ℕ) (p : ℝ) (n : ℕ) :
    formalIterationBudget C p (n + 1) = (formalIterationBudget C p n + C) ^ C := rfl

theorem formalIterationBudget_nonneg (C : ℕ) {p : ℝ} (hp : 0 ≤ p) (n : ℕ) :
    0 ≤ formalIterationBudget C p n := by
  induction n with
  | zero => exact hp
  | succ n ih => exact pow_nonneg (add_nonneg ih (Nat.cast_nonneg C)) C

theorem formalIterationBudget_monotone {C : ℕ} (hC : 2 ≤ C) {p : ℝ} (hp : 0 ≤ p) :
    Monotone (formalIterationBudget C p) := by
  apply monotone_nat_of_le_succ
  intro n
  have hn := formalIterationBudget_nonneg C hp n
  have hCr : (2 : ℝ) ≤ C := Nat.cast_le.mpr hC
  calc
    formalIterationBudget C p n ≤ formalIterationBudget C p n + C := le_add_of_nonneg_right (Nat.cast_nonneg C)
    _ ≤ (formalIterationBudget C p n + C) ^ C := by
      simpa only [pow_one] using pow_le_pow_right₀
        (by linarith : (1 : ℝ) ≤ formalIterationBudget C p n + C) (show 1 ≤ C by omega)

theorem formalIterationBudget_ge {C : ℕ} (hC : 2 ≤ C) {p : ℝ} (hp : 0 ≤ p) (n : ℕ) :
    p ≤ formalIterationBudget C p n := formalIterationBudget_monotone hC hp (Nat.zero_le n)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeWeightPairRemoval
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem star_finite_expect {X : Type*} (S : Finset X) (f : X → ℂ) :
    star (𝔼 u ∈ S, f u) = 𝔼 u ∈ S, star (f u) := by
  simp [Finset.expect]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.StepDropBasisBudget
namespace OAI

section

namespace Erdos3

open Module

theorem stepDropBracketHeight_le_exp (n H : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hn : (n : ℝ) ≤ p) (hH : (H : ℝ) ≤ Real.exp p) :
    (stepDropBracketHeight n H : ℝ) ≤ Real.exp ((p + 2) ^ 5) := by
  have hh : (H : ℝ) * H ≤ Real.exp (2 * p) := by
    rw [show 2 * p = p + p by ring, Real.exp_add]
    exact mul_le_mul hH hH (Nat.cast_nonneg _) (Real.exp_nonneg _)
  have hpow := pow_le_pow_left₀ (mul_nonneg (Nat.cast_nonneg H) (Nat.cast_nonneg H)) hh (n ^ 2)
  rw [← Real.exp_nat_mul] at hpow
  have hinner : (((n ^ 2 + 1) * (H * H) ^ (n ^ 2)) * H : ℕ) ≤
      Real.exp ((n : ℝ) ^ 2 + n ^ 2 * (2 * p) + p) := by
    push_cast
    rw [Real.exp_add, Real.exp_add]
    apply mul_le_mul _ hH (Nat.cast_nonneg H) (by positivity)
    exact mul_le_mul (Real.add_one_le_exp ((n : ℝ) ^ 2))
      (by simpa only [Nat.cast_pow] using hpow) (by positivity) (Real.exp_nonneg _)
  have hout := pow_le_pow_left₀
    (Nat.cast_nonneg (((n ^ 2 + 1) * (H * H) ^ (n ^ 2)) * H)) hinner n
  rw [← Real.exp_nat_mul] at hout
  have htotal : (stepDropBracketHeight n H : ℝ) ≤
      Real.exp ((n : ℝ) + n * (n ^ 2 + n ^ 2 * (2 * p) + p)) := by
    unfold stepDropBracketHeight
    rw [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_pow, Real.exp_add]
    exact mul_le_mul (Real.add_one_le_exp n) hout (by positivity) (Real.exp_nonneg _)
  apply htotal.trans (Real.exp_le_exp.mpr ?_)
  calc
    (n : ℝ) + n * (n ^ 2 + n ^ 2 * (2 * p) + p) ≤
        p + p * (p ^ 2 + p ^ 2 * (2 * p) + p) := by gcongr
    _ ≤ (p + 2) ^ 5 := by
      have h : 0 ≤ p ^ 5 + 8 * p ^ 4 + 39 * p ^ 3 + 79 * p ^ 2 + 79 * p + 32 := by positivity
      nlinarith

end Erdos3

end

end OAI
end


