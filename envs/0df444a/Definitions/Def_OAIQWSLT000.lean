-- Prove2me | Definitions.Def_OAIQWSLT000
-- name    : OAIQWSLT000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-23T13:56:58.642718+00:00
-- url     : https://prove2.me/theorems/eb197b86-b883-4b06-ac7c-c18d52fc7405
-- title:
--   OpenAI sharp Lieb–Thirring split: definitions bundle OAIQWSLT000
-- statement:
--   The definitions bundle of the split of OpenAI's proof of `OAI.SharpLiebThirring.sharp_lieb_thirring`, the sharp one-dimensional Lieb–Thirring inequality as stated in the published goal bundle `Def_LiebThirring`.
--
--   The bundle holds OpenAI's Lean definitions, structures and predicates from the modules `ActionBounds`, `ActionPenalty`, `BoundState`, `BoundaryValues`, `Continuation`, `CubeFlags`, `CutoffEnergy`, `EquivariantFlags`, `FieldFlow`, `FieldLimit`, `FieldPrimitive`, `FieldRegularity`, `FiniteParity`, `FlagGeometry`, `FreeLocus`, `Gamma`, `GenericPosition`, `InitialOrbit`, `IntervalAction`, `MatrixFlow`, `MatrixOrder`, `MatrixTangent`, `RankOne`, `ResolventCalculus`, `RowSigns`, `SobolevProjection` of `lean/OAI/Analysis/LiebThirring` (OpenAI, *Sharp one-dimensional Lieb–Thirring constants*, OpenAI Math Release, September 23, 2026, result family 262, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0). They are ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas their bodies use. It imports no other bundle of this split.
--
--   It builds on the published goal bundle `Def_LiebThirring` (the space `H1`, the Schrödinger form, negative eigenfunctions and the eigenvalue moments). Among its definitions:
--   - the one-bound-state profile, potential and bound state, with their cutoffs and scalings (`profile`, `potential`, `boundState`, `normalizedBoundState`, `cutoff`, `smoothH1`, `scaleH1`, `C1L2`);
--   - the regularized matrix field and its primitive (the paper's Section 3) and the matrix path with prescribed endpoints (Section 5) (`matrixField`, `truncatedField`, `fieldPrimitive`, `regularizedPrimitive`, `matrixForcing`, `flowRhs`, `Sym`);
--   - the Hilbert–Schmidt square of a matrix (`hsSquared`), which the standalone statement `OAI.SharpLiebThirring.MatrixProof.hilbertSchmidt_cfc_sub_le` writes out;
--   - resolvent and divided-difference calculus for Hermitian matrices (`resolventMatrix`, `resolventDifference`, `dividedPrimitive`, `quadraticMatrix`, `quadraticTangent`);
--   - action densities and defects (`actionDensity`, `betaAction`, `actionDefect`, `constraintDefect`);
--   - the combinatorics of cube flags, sign rows and lower-triangular coordinates (`Flag.vertex`, `Flag.step`, `Orbit`, `LowerSpace`, `rowSign`, `freeLocus`).
--
--   The theorems the definitions do not need are proved in the solutions of this split. The split exists because the single-file proof takes longer than the platform's verifier allows.
-- source:
--   OpenAI, Sharp one-dimensional Lieb–Thirring constants, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 262; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Sharp-One-Dimensional-Lieb-Thirring-Constants-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis/LiebThirring at commit adc7f12

import Mathlib
import Definitions.Def_LiebThirring

section
-- module Solutions.OAIQW_LiebThirring.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. -/
section OAICompat434
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    (if hp : p then a hp else b hp) = a h := dif_pos h
theorem dite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : ¬p) :
    (if hp : p then a hp else b hp) = b h := dif_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQW_LiebThirring.MatrixOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3 u4 u5

noncomputable section
open MeasureTheory
open scoped ENNReal Matrix.Norms.L2Operator
open Matrix
namespace SharpLiebThirring


/-! ## The matrix field and action -/

/-- The regularized primitive, including beta = 0 without a special convention. -/
def regularizedPrimitive (σ δ y : ℝ) : ℝ :=
  ∫ t in 0..y, (max t 0 + δ) ^ (σ - 3 / 2)

def fieldNormalization (σ : ℝ) : ℝ :=
  σ / ∫ s : ℝ, (1 + s ^ 2) ^ (σ - 3 / 2)

def scalarMu (σ δ z : ℝ) : ℝ :=
  fieldNormalization σ * ∫ s : ℝ,
    regularizedPrimitive σ δ (s ^ 2 + z) - regularizedPrimitive σ δ (s ^ 2)

section FieldDefinitions
variable {N : ℕ}

def matrixX (k : Fin N → ℝ) (B : Matrix (Fin N) (Fin N) ℝ) (s : ℝ) :
    Matrix (Fin N) (Fin N) ℝ :=
  Matrix.diagonal (fun i ↦ (k i) ^ 2) - (2 * s) • B + (s ^ 2) • 1

/-- The symmetric cutoff is part of the definition, not replaced
by a potentially non-absolutely-convergent whole-line Bochner integral. -/
def truncatedField (σ δ : ℝ) (k : Fin N → ℝ) (B : Matrix (Fin N) (Fin N) ℝ)
    (R : ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  fieldNormalization σ • ∫ s in (-R)..R,
    cfc (regularizedPrimitive σ δ) (matrixX k B s) -
      regularizedPrimitive σ δ (s ^ 2) • 1

/-- The symmetric-cutoff limit, whose convergence and local regularity are proved below. -/
def matrixField (σ δ : ℝ) (k : Fin N → ℝ) (B : Matrix (Fin N) (Fin N) ℝ) :
    Matrix (Fin N) (Fin N) ℝ :=
  Filter.limUnder Filter.atTop (truncatedField σ δ k B)

def fieldPrimitive (σ δ : ℝ) (k : Fin N → ℝ) (B : Matrix (Fin N) (Fin N) ℝ) : ℝ :=
  -(∫ t in (0 : ℝ)..1, Matrix.trace (B * matrixField σ δ k (t • B)))

end FieldDefinitions

def LowerTriangular {N : ℕ} (C : Matrix (Fin N) (Fin N) ℝ) : Prop :=
  ∀ i j, i < j → C i j = 0


open Matrix Unitary
namespace MatrixProof
variable {n : Type u1} [Fintype n] [DecidableEq n]

lemma hermitian_unitary_conjugate {A : Matrix n n ℂ} (hA : A.IsHermitian)
    (U : unitary (Matrix n n ℂ)) : (conjStarAlgAut ℂ (Matrix n n ℂ) U A).IsHermitian := by
  change star (conjStarAlgAut ℂ (Matrix n n ℂ) U A) = conjStarAlgAut ℂ (Matrix n n ℂ) U A
  rw [← map_star, hA.star_eq]


/-- The squared Hilbert--Schmidt norm, without changing the ambient matrix norm. -/
def hsSquared (A : Matrix n n ℂ) : ℝ := ∑ i, ∑ j, Complex.normSq (A i j)

open MeasureTheory
open scoped Matrix.Norms.L2Operator NNReal

/-- Real trace pairing as a continuous linear functional. -/
def tracePairCLM (M : Matrix n n ℂ) : Matrix n n ℂ →L[ℝ] ℝ :=
  (Complex.reCLM).comp
    ((Matrix.traceLinearMap n ℝ ℂ).toContinuousLinearMap.comp
      ((LinearMap.mulLeft ℝ M).toContinuousLinearMap))

@[simp] lemma tracePairCLM_apply (M Z : Matrix n n ℂ) :
    tracePairCLM M Z = (trace (M * Z)).re := rfl


/-- In a fixed eigenbasis of B, the unitary exp(itB). -/
def phaseUnitary (z : n → ℝ) (t : ℝ) : unitary (Matrix n n ℂ) :=
  ⟨diagonal (fun i ↦ Complex.exp ((t * z i : ℝ) * Complex.I)), by
    constructor
    · simp only [star_eq_conjTranspose, diagonal_conjTranspose, diagonal_mul_diagonal]
      rw [← diagonal_one]
      congr 1
      funext i
      simp only [Pi.star_apply]
      rw [Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
      simp
    · simp only [star_eq_conjTranspose, diagonal_conjTranspose, diagonal_mul_diagonal]
      rw [← diagonal_one]
      congr 1
      funext i
      simp only [Pi.star_apply]
      rw [Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
      simp⟩

/-- Entry evaluation is a continuous linear functional even for the operator norm. -/
def entryCLM (i j : n) : Matrix n n ℂ →L[ℝ] ℂ :=
  ({ toFun := fun D ↦ D i j
     map_add' := fun _ _ ↦ rfl
     map_smul' := fun _ _ ↦ rfl } : Matrix n n ℂ →ₗ[ℝ] ℂ).toContinuousLinearMap

omit [DecidableEq n] in
@[simp] lemma entryCLM_apply (i j : n) (D : Matrix n n ℂ) : entryCLM i j D = D i j := rfl

end MatrixProof

open MeasureTheory Set Filter
open scoped Topology
namespace ScalarProof

lemma derivative_continuous (σ : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    Continuous (fun t : ℝ ↦ (max t 0 + δ) ^ (σ - 3 / 2)) := by
  apply Continuous.rpow_const
  · fun_prop
  · intro t
    left
    positivity

lemma primitive_hasDerivAt (σ : ℝ) {δ : ℝ} (hδ : 0 < δ) (y : ℝ) :
    HasDerivAt (regularizedPrimitive σ δ) ((max y 0 + δ) ^ (σ - 3 / 2)) y := by
  have hc := derivative_continuous σ hδ
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable _ _)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt

lemma primitive_differentiable (σ : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    Differentiable ℝ (regularizedPrimitive σ δ) :=
  fun y ↦ (primitive_hasDerivAt σ hδ y).differentiableAt

@[simp] lemma primitive_zero (σ δ : ℝ) : regularizedPrimitive σ δ 0 = 0 := by
  simp [regularizedPrimitive]

lemma normalization_integrable {σ : ℝ} (hσ : σ < 1) :
    Integrable (fun s : ℝ ↦ (1 + s ^ 2) ^ (σ - 3 / 2)) := by
  have h : (Module.finrank ℝ ℝ : ℝ) < 3 - 2 * σ := by
    norm_num only [Module.finrank_self, Nat.cast_one]
    linarith
  have he := integrable_rpow_neg_one_add_norm_sq (E := ℝ) (μ := volume) h
  convert he using 1
  ext s
  congr 1
  · simp
  · ring

@[simp] lemma mu_zero (σ δ : ℝ) : scalarMu σ δ 0 = 0 := by
  simp [scalarMu]


/-- Normalized Gamma mixing density, used only on the positive half-line. -/
def gammaWeight (σ v : ℝ) : ℝ :=
  (Real.Gamma (1 - σ))⁻¹ * (v ^ (-σ) * Real.exp (-v))

/-- The scalar difference whose positive-matrix functional calculus is integrated. -/
def resolventDifference (β δ y v : ℝ) : ℝ :=
  v ^ β * ((δ + v)⁻¹ - (y + δ + v)⁻¹)


/-- The normalization constant for the resolvent representation. -/
def resolventNormalization (β : ℝ) : ℝ :=
  (∫ v in Ioi (0 : ℝ), v ^ β / (1 + v) ^ 2)⁻¹

end ScalarProof

open scoped MatrixOrder ComplexOrder


end SharpLiebThirring

end

end OAI
end

section
-- module Solutions.OAIQW_LiebThirring.ResolventCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u6 u7 u8 u9 u10 u11

noncomputable section
open MeasureTheory
open scoped ENNReal Matrix.Norms.L2Operator
open Matrix


open Matrix Unitary MeasureTheory Set
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
namespace SharpLiebThirring.MatrixProof
variable {n : Type u6} [Fintype n] [DecidableEq n]

/-- Finite spectral synthesis as a real continuous linear map. -/
def spectralCLM {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    (n → ℝ) →L[ℝ] Matrix n n ℂ :=
  ({ toFun := fun x ↦ conjStarAlgAut ℂ (Matrix n n ℂ) hA.eigenvectorUnitary
        (diagonal (fun i ↦ (x i : ℂ)))
     map_add' := by
       intro x y
       simp only [Pi.add_apply, Complex.ofReal_add, conjStarAlgAut_apply]
       rw [show diagonal (fun i ↦ (x i : ℂ) + (y i : ℂ)) =
         diagonal (fun i ↦ (x i : ℂ)) + diagonal (fun i ↦ (y i : ℂ)) from
         (diagonal_add _ _).symm]
       simp only [mul_add, add_mul]
     map_smul' := by
       intro r x
       simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul]
       rw [show diagonal (fun i ↦ (r : ℂ) * (x i : ℂ)) =
         r • diagonal (fun i ↦ (x i : ℂ)) by ext i j; simp [diagonal_apply]]
       simp [conjStarAlgAut_apply] } : (n → ℝ) →ₗ[ℝ] Matrix n n ℂ).toContinuousLinearMap

@[simp] lemma spectralCLM_apply {A : Matrix n n ℂ} (hA : A.IsHermitian) (x : n → ℝ) :
    spectralCLM hA x = conjStarAlgAut ℂ (Matrix n n ℂ) hA.eigenvectorUnitary
      (diagonal (fun i ↦ (x i : ℂ))) := rfl

open ScalarProof

def resolventMatrix (β δ : ℝ) (A : Matrix n n ℂ) (v : ℝ) : Matrix n n ℂ :=
  v ^ β • ((δ + v)⁻¹ • 1 - (A + (δ + v) • 1)⁻¹)

end SharpLiebThirring.MatrixProof


namespace SharpLiebThirring.MatrixProof
open ScalarProof Matrix MeasureTheory Set
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder Topology
variable {n : Type u9} [Fintype n] [DecidableEq n]

def resolventTangentKernel (β δ : ℝ) (Y Z : Matrix n n ℂ) (v : ℝ) : Matrix n n ℂ :=
  v ^ β • ((Y + (δ + v) • 1)⁻¹ * Z * (Y + (δ + v) • 1)⁻¹)

end SharpLiebThirring.MatrixProof


namespace SharpLiebThirring.ScalarProof
open MeasureTheory Set

def dividedPrimitive (σ δ x y : ℝ) : ℝ :=
  ∫ τ in Icc (0 : ℝ) 1, (τ * x + (1 - τ) * y + δ) ^ (σ - 3 / 2)

end SharpLiebThirring.ScalarProof

noncomputable section
open Matrix Unitary MeasureTheory Set
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder CStarAlgebra
namespace SharpLiebThirring.MatrixProof
variable {n : Type u10} [Fintype n] [DecidableEq n]

def diagonalStarAlgHom : (n → ℂ) →⋆ₐ[ℝ] Matrix n n ℂ :=
  { diagonalAlgHom ℝ with
    map_star' := by
      intro x
      ext i j
      by_cases hij : i = j
      · subst j; simp [star_apply]
      · simp [star_apply, hij, Ne.symm hij] }

end SharpLiebThirring.MatrixProof


namespace SharpLiebThirring.ScalarProof
open MeasureTheory Set

def quadraticDividedIntegrand (σ δ d x y s τ : ℝ) : ℝ :=
  (max (τ * ((s - x) ^ 2 + d) + (1 - τ) * ((s - y) ^ 2 + d)) 0 + δ) ^ (σ - 3 / 2)

end SharpLiebThirring.ScalarProof

end
end

end OAI
end

section
-- module Solutions.OAIQW_LiebThirring.MatrixTangent
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u12 u13 u14 u15

noncomputable section
open MeasureTheory
open scoped ENNReal Matrix.Norms.L2Operator
open Matrix
open Matrix Unitary MeasureTheory Set
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
noncomputable section
open Matrix Unitary MeasureTheory Set
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder CStarAlgebra


namespace SharpLiebThirring.MatrixProof
open ScalarProof MeasureTheory Set Filter Unitary
open scoped Matrix.Norms.L2Operator NNReal Topology
variable {n : Type u12} [Fintype n] [DecidableEq n]

/-- The Schur action obtained by one Gaussian average. -/
def gaussianSchur (z : n → ℝ) (v h : ℝ) (D : Matrix n n ℂ) : Matrix n n ℂ :=
  fun i j ↦ (Real.exp (-v * h * (z i - z j) ^ 2) : ℂ) * D i j

def powerSchur (σ : ℝ) (z : n → ℝ) (h : ℝ) (D : Matrix n n ℂ) : Matrix n n ℂ :=
  fun i j ↦ (((1 + h * (z i - z j) ^ 2) ^ (σ - 1) : ℝ) : ℂ) * D i j

end SharpLiebThirring.MatrixProof


namespace SharpLiebThirring.MatrixProof
open ScalarProof MeasureTheory Set
open scoped Matrix.Norms.L2Operator
variable {n : Type u13} [Fintype n] [DecidableEq n]

def tangentSchur (σ a : ℝ) (z : n → ℝ) (D : Matrix n n ℂ) : Matrix n n ℂ :=
  ∫ τ in Icc (0 : ℝ) 1, powerSchur σ z (τ * (1 - τ) / a) D

end SharpLiebThirring.MatrixProof


namespace SharpLiebThirring.MatrixProof
open ScalarProof Matrix MeasureTheory Set
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
variable {n : Type u14} [Fintype n] [DecidableEq n]

def quadraticTangent (σ δ d : ℝ) (z : n → ℝ) (Z : Matrix n n ℂ) (s : ℝ) : Matrix n n ℂ :=
  fun i j ↦ (dividedPrimitive σ δ ((s - z i) ^ 2 + d) ((s - z j) ^ 2 + d) : ℂ) * Z i j

end SharpLiebThirring.MatrixProof

end
end

end OAI
end

section
-- module Solutions.OAIQW_LiebThirring.FieldLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u16 u17 u18

noncomputable section
open MeasureTheory
open scoped ENNReal Matrix.Norms.L2Operator
open Matrix
open Matrix Unitary MeasureTheory Set
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
noncomputable section
open Matrix Unitary MeasureTheory Set
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder CStarAlgebra


noncomputable section
open MeasureTheory Set Filter
open scoped Topology

namespace SharpLiebThirring.ScalarProof

lemma derivative_lipschitz_on_positive {σ δ a : ℝ} (hσ : σ < 1) (hδ : 0 < δ)
    (ha : 0 < a) {x y : ℝ} (hx : a ≤ x) (hy : a ≤ y) :
    ‖(x + δ) ^ (σ - 3 / 2) - (y + δ) ^ (σ - 3 / 2)‖ ≤
      (3 / 2 - σ) * (a + δ) ^ (σ - 5 / 2) * ‖x - y‖ := by
  have hd : ∀ t ∈ Ici a, HasDerivWithinAt (fun t : ℝ ↦ (t + δ) ^ (σ - 3 / 2))
      ((σ - 3 / 2) * (t + δ) ^ (σ - 5 / 2)) (Ici a) t := by
    intro t ht
    change a ≤ t at ht
    have hp : t + δ ≠ 0 := by linarith
    convert! (((hasDerivAt_id t).add_const δ).rpow_const (p := σ - 3 / 2)
      (Or.inl hp)).hasDerivWithinAt using 1
    simp only [id_eq]
    ring_nf
  have hb : ∀ t ∈ Ici a, ‖(σ - 3 / 2) * (t + δ) ^ (σ - 5 / 2)‖ ≤
      (3 / 2 - σ) * (a + δ) ^ (σ - 5 / 2) := by
    intro t ht
    change a ≤ t at ht
    rw [norm_mul, Real.norm_eq_abs, abs_of_neg (show σ - 3 / 2 < 0 by linarith),
      Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by linarith) _)]
    have hr := Real.rpow_le_rpow_of_nonpos (show 0 < a + δ by linarith)
      (show a + δ ≤ t + δ by linarith) (show σ - 5 / 2 ≤ 0 by linarith)
    nlinarith
  exact (convex_Ici a).norm_image_sub_le_of_norm_hasDerivWithin_le hd hb hy hx

lemma primitive_taylor_bound {σ δ a x r y : ℝ} (hσ : σ < 1) (hδ : 0 < δ)
    (ha : 0 < a) (hr : 0 ≤ r) (hxr : a ≤ x - r) (hy : |y| ≤ r) :
    ‖regularizedPrimitive σ δ (x + y) - regularizedPrimitive σ δ x -
      (x + δ) ^ (σ - 3 / 2) * y‖ ≤
      (3 / 2 - σ) * (a + δ) ^ (σ - 5 / 2) * r ^ 2 := by
  let L := (3 / 2 - σ) * (a + δ) ^ (σ - 5 / 2)
  have hL : 0 ≤ L := mul_nonneg (by linarith) (Real.rpow_nonneg (by linarith) _)
  have hx : a ≤ x := by linarith
  have hxy : x + y ∈ Icc (x - r) (x + r) := by
    constructor <;> linarith [(abs_le.1 hy).1, (abs_le.1 hy).2]
  have hxx : x ∈ Icc (x - r) (x + r) := ⟨by linarith, by linarith⟩
  have hd (t : ℝ) (ht : t ∈ Icc (x - r) (x + r)) :
      HasDerivWithinAt (fun t : ℝ ↦ regularizedPrimitive σ δ t -
        regularizedPrimitive σ δ x - (x + δ) ^ (σ - 3 / 2) * (t - x))
        ((t + δ) ^ (σ - 3 / 2) - (x + δ) ^ (σ - 3 / 2)) (Icc (x - r) (x + r)) t := by
    have ht₀ : 0 ≤ t := by have := ht.1; linarith
    convert! (((primitive_hasDerivAt σ hδ t).sub_const (regularizedPrimitive σ δ x)).sub
      (((hasDerivAt_id t).sub_const x).const_mul ((x + δ) ^ (σ - 3 / 2)))).hasDerivWithinAt
      using 1
    simp [max_eq_left ht₀]
  have hb (t : ℝ) (ht : t ∈ Icc (x - r) (x + r)) :
      ‖(t + δ) ^ (σ - 3 / 2) - (x + δ) ^ (σ - 3 / 2)‖ ≤ L * r := by
    refine (derivative_lipschitz_on_positive hσ hδ ha (hxr.trans ht.1) hx).trans ?_
    apply mul_le_mul_of_nonneg_left _ hL
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith [ht.1, ht.2]
  have hm := (convex_Icc (x - r) (x + r)).norm_image_sub_le_of_norm_hasDerivWithin_le
    hd hb hxx hxy
  simp only [sub_self, mul_zero, sub_zero, add_sub_cancel_left, Real.norm_eq_abs] at hm
  refine hm.trans ((mul_le_mul_of_nonneg_left hy (mul_nonneg hL hr)).trans_eq ?_)
  dsimp [L]
  ring

end SharpLiebThirring.ScalarProof

namespace SharpLiebThirring.MatrixProof
open ScalarProof Matrix
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
variable {n : Type u16} [Fintype n] [DecidableEq n]

lemma cfc_scalar_add (f : ℝ → ℝ) (hf : Continuous f) (x : ℝ)
    {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    cfc f (x • 1 + A) = cfc (fun y : ℝ ↦ f (x + y)) A := by
  have h := cfc_comp' f (fun y : ℝ ↦ x + y) A hf.continuousOn (by fun_prop) hA
  erw [cfc_const_add x id A (by fun_prop) hA, cfc_id ℝ A hA,
    Algebra.algebraMap_eq_smul_one] at h
  exact h.symm

lemma spectrum_abs_le_matrix_norm {A : Matrix n n ℂ} {y : ℝ} (hy : y ∈ spectrum ℝ A) :
    |y| ≤ ‖A‖ := by
  cases isEmpty_or_nonempty n with
  | inl h =>
      have h1 : (1 : Matrix n n ℂ) = 0 := Subsingleton.elim _ _
      have hy0 : y = 0 := by simpa [h1] using spectrum.norm_le_norm_mul_of_mem hy
      simp [hy0]
  | inr h => simpa using spectrum.norm_le_norm_mul_of_mem hy

lemma primitive_cfc_taylor_bound {σ δ a x r : ℝ} (hσ : σ < 1) (hδ : 0 < δ)
    (ha : 0 < a) (hr : 0 ≤ r) (hxr : a ≤ x - r)
    {A : Matrix n n ℂ} (hA : A.IsHermitian) (hAr : ‖A‖ ≤ r) :
    ‖cfc (regularizedPrimitive σ δ) (x • 1 + A) -
        regularizedPrimitive σ δ x • 1 - (x + δ) ^ (σ - 3 / 2) • A‖ ≤
      (3 / 2 - σ) * (a + δ) ^ (σ - 5 / 2) * r ^ 2 := by
  have hc := (primitive_differentiable σ hδ).continuous
  have he : cfc (fun y : ℝ ↦ regularizedPrimitive σ δ (x + y) -
      regularizedPrimitive σ δ x - (x + δ) ^ (σ - 3 / 2) * y) A =
      cfc (regularizedPrimitive σ δ) (x • 1 + A) -
        regularizedPrimitive σ δ x • 1 - (x + δ) ^ (σ - 3 / 2) • A := by
    erw [cfc_sub (fun y : ℝ ↦ regularizedPrimitive σ δ (x + y) -
      regularizedPrimitive σ δ x) (fun y : ℝ ↦ (x + δ) ^ (σ - 3 / 2) * y) A
      (by fun_prop) (by fun_prop),
      cfc_sub (fun y : ℝ ↦ regularizedPrimitive σ δ (x + y))
        (fun _ : ℝ ↦ regularizedPrimitive σ δ x) A (by fun_prop) (by fun_prop),
      cfc_const (regularizedPrimitive σ δ x) A hA,
      cfc_const_mul_id ((x + δ) ^ (σ - 3 / 2)) A hA,
      Algebra.algebraMap_eq_smul_one, ← cfc_scalar_add _ hc x hA]
  rw [← he]
  have hb : 0 ≤ (3 / 2 - σ) * (a + δ) ^ (σ - 5 / 2) * r ^ 2 := by
    have : 0 ≤ 3 / 2 - σ := by linarith
    positivity
  apply norm_cfc_le hb
  intro y hy
  exact primitive_taylor_bound hσ hδ ha hr hxr
    ((spectrum_abs_le_matrix_norm hy).trans hAr)

end SharpLiebThirring.MatrixProof

namespace SharpLiebThirring.MatrixProof
open ScalarProof Matrix
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
variable {n : Type u17} [Fintype n] [DecidableEq n]

lemma quadratic_taylor_weight {σ δ s A : ℝ} (hσ : σ < 1) (hδ : 0 < δ)
    (hs : 1 ≤ s) :
    (s ^ 2 / 2 + δ) ^ (σ - 5 / 2) * (A * s) ^ 2 ≤
      (1 / 4 : ℝ) ^ (σ - 5 / 2) * A ^ 2 * (1 + s ^ 2) ^ (σ - 3 / 2) := by
  have hs2 : 1 ≤ s ^ 2 := by nlinarith
  have hb : 0 < (1 + s ^ 2) / 4 := by positivity
  have hle : (1 + s ^ 2) / 4 ≤ s ^ 2 / 2 + δ := by nlinarith
  have hr := Real.rpow_le_rpow_of_nonpos hb hle (by linarith : σ - 5 / 2 ≤ 0)
  have he : ((1 + s ^ 2) / 4) ^ (σ - 5 / 2) =
      (1 / 4 : ℝ) ^ (σ - 5 / 2) * (1 + s ^ 2) ^ (σ - 5 / 2) := by
    rw [show (1 + s ^ 2) / 4 = (1 / 4 : ℝ) * (1 + s ^ 2) by ring,
      Real.mul_rpow (by positivity) (by positivity)]
  have he2 : (1 + s ^ 2) ^ (σ - 5 / 2) * (1 + s ^ 2) =
      (1 + s ^ 2) ^ (σ - 3 / 2) := by
    rw [← Real.rpow_add_one (by positivity)]
    congr 1
    ring
  calc
    _ ≤ ((1 + s ^ 2) / 4) ^ (σ - 5 / 2) * (A * s) ^ 2 :=
      mul_le_mul_of_nonneg_right hr (sq_nonneg _)
    _ = (1 / 4 : ℝ) ^ (σ - 5 / 2) * A ^ 2 *
        ((1 + s ^ 2) ^ (σ - 5 / 2) * s ^ 2) := by rw [he]; ring
    _ ≤ (1 / 4 : ℝ) ^ (σ - 5 / 2) * A ^ 2 *
        ((1 + s ^ 2) ^ (σ - 5 / 2) * (1 + s ^ 2)) := by gcongr; linarith
    _ = _ := by rw [he2]

lemma quadratic_derivative_weight {σ δ s : ℝ} (hσ : σ < 1) (hδ : 0 < δ)
    (hs : 1 ≤ s) :
    (s ^ 2 + δ) ^ (σ - 3 / 2) ≤
      (1 / 2 : ℝ) ^ (σ - 3 / 2) * (1 + s ^ 2) ^ (σ - 3 / 2) := by
  have hs2 : 1 ≤ s ^ 2 := by nlinarith
  have hr := Real.rpow_le_rpow_of_nonpos (by positivity : 0 < (1 + s ^ 2) / 2)
    (by nlinarith : (1 + s ^ 2) / 2 ≤ s ^ 2 + δ) (by linarith : σ - 3 / 2 ≤ 0)
  simpa only [show (1 + s ^ 2) / 2 = (1 / 2 : ℝ) * (1 + s ^ 2) by ring,
    Real.mul_rpow (by positivity : 0 ≤ (1 / 2 : ℝ)) (by positivity : 0 ≤ 1 + s ^ 2)] using hr

def quadraticMatrix (C B : Matrix n n ℂ) (s : ℝ) : Matrix n n ℂ :=
  s ^ 2 • 1 + (C - (2 * s) • B)

def pairedFieldIntegrand (σ δ : ℝ) (C B : Matrix n n ℂ) (s : ℝ) : Matrix n n ℂ :=
  cfc (regularizedPrimitive σ δ) (quadraticMatrix C B s) +
    cfc (regularizedPrimitive σ δ) (quadraticMatrix C B (-s)) -
    (2 * regularizedPrimitive σ δ (s ^ 2)) • 1

lemma pairedFieldIntegrand_even (σ δ : ℝ) (C B : Matrix n n ℂ) :
    Function.Even (pairedFieldIntegrand σ δ C B) := by
  intro s
  simp only [pairedFieldIntegrand, neg_neg, neg_sq, add_comm]

omit [Fintype n] in
lemma quadraticMatrix_hermitian {C B : Matrix n n ℂ}
    (hC : C.IsHermitian) (hB : B.IsHermitian) (s : ℝ) :
    (quadraticMatrix C B s).IsHermitian :=
  ((isHermitian_one (n := n) (α := ℂ)).smul (isSelfAdjoint_iff.2 rfl : IsSelfAdjoint (s ^ 2))).add (hC.sub (hB.smul (isSelfAdjoint_iff.2 rfl : IsSelfAdjoint (2 * s))))

lemma perturbed_norm_le {C B : Matrix n n ℂ} {s : ℝ} (hs : 1 ≤ |s|) :
    ‖C - (2 * s) • B‖ ≤ (‖C‖ + 2 * ‖B‖) * |s| := by
  calc
    _ ≤ ‖C‖ + ‖(2 * s) • B‖ := norm_sub_le _ _
    _ = ‖C‖ + 2 * |s| * ‖B‖ := by simp [norm_smul]
    _ ≤ _ := by nlinarith [norm_nonneg C, norm_nonneg B]

lemma pairedFieldIntegrand_bound {σ δ : ℝ} (hσ : σ < 1) (hδ : 0 < δ)
    {C B : Matrix n n ℂ} (hC : C.IsHermitian) (hB : B.IsHermitian)
    {s : ℝ} (hs : max 1 (2 * (‖C‖ + 2 * ‖B‖)) ≤ s) :
    ‖pairedFieldIntegrand σ δ C B s‖ ≤
      (2 * (3 / 2 - σ) * (1 / 4 : ℝ) ^ (σ - 5 / 2) * (‖C‖ + 2 * ‖B‖) ^ 2 +
        2 * ‖C‖ * (1 / 2 : ℝ) ^ (σ - 3 / 2)) * (1 + s ^ 2) ^ (σ - 3 / 2) := by
  have hs1 : 1 ≤ s := (le_max_left _ _).trans hs
  have hsA : 2 * (‖C‖ + 2 * ‖B‖) ≤ s := (le_max_right _ _).trans hs
  have hs0 : 0 < s := by linarith
  let A := ‖C‖ + 2 * ‖B‖
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hxr : s ^ 2 / 2 ≤ s ^ 2 - A * s := by dsimp [A]; nlinarith
  have hn₁ : ‖C - (2 * s) • B‖ ≤ A * s := by
    simpa only [abs_of_pos hs0] using (perturbed_norm_le (C := C) (B := B)
      (s := s) (by rwa [abs_of_pos hs0]))
  have hn₂ : ‖C - (2 * -s) • B‖ ≤ A * s := by
    simpa only [abs_neg, abs_of_pos hs0] using (perturbed_norm_le (C := C) (B := B)
      (s := -s) (by rwa [abs_neg, abs_of_pos hs0]))
  have ht₁ := primitive_cfc_taylor_bound hσ hδ (by positivity : 0 < s ^ 2 / 2)
    (mul_nonneg hA hs0.le) hxr (hC.sub (hB.smul (isSelfAdjoint_iff.2 rfl : IsSelfAdjoint (2 * s)))) hn₁
  have ht₂ := primitive_cfc_taylor_bound hσ hδ (by positivity : 0 < s ^ 2 / 2)
    (mul_nonneg hA hs0.le) hxr (hC.sub (hB.smul (isSelfAdjoint_iff.2 rfl : IsSelfAdjoint (2 * -s)))) hn₂
  let E₁ := cfc (regularizedPrimitive σ δ) (quadraticMatrix C B s) -
    regularizedPrimitive σ δ (s ^ 2) • (1 : Matrix n n ℂ) -
    (s ^ 2 + δ) ^ (σ - 3 / 2) • (C - (2 * s) • B)
  let E₂ := cfc (regularizedPrimitive σ δ) (quadraticMatrix C B (-s)) -
    regularizedPrimitive σ δ (s ^ 2) • (1 : Matrix n n ℂ) -
    (s ^ 2 + δ) ^ (σ - 3 / 2) • (C - (2 * -s) • B)
  have he : pairedFieldIntegrand σ δ C B s =
      E₁ + E₂ + (2 * (s ^ 2 + δ) ^ (σ - 3 / 2)) • C := by
    dsimp [pairedFieldIntegrand, E₁, E₂]
    module
  have ht₂' : ‖E₂‖ ≤ (3 / 2 - σ) * (s ^ 2 / 2 + δ) ^ (σ - 5 / 2) * (A * s) ^ 2 := by
    simpa only [E₂, quadraticMatrix, neg_sq] using ht₂
  have hw := quadratic_taylor_weight (A := A) hσ hδ hs1
  have hd := quadratic_derivative_weight hσ hδ hs1
  have hr : 0 ≤ (s ^ 2 + δ) ^ (σ - 3 / 2) := Real.rpow_nonneg (by positivity) _
  have hp : 0 ≤ 3 / 2 - σ := by linarith
  rw [he]
  calc
    _ ≤ ‖E₁‖ + ‖E₂‖ + ‖(2 * (s ^ 2 + δ) ^ (σ - 3 / 2)) • C‖ :=
      by linarith [norm_add_le E₁ E₂, norm_add_le (E₁ + E₂) ((2 * (s ^ 2 + δ) ^ (σ - 3 / 2)) • C)]
    _ ≤ 2 * ((3 / 2 - σ) * (s ^ 2 / 2 + δ) ^ (σ - 5 / 2) * (A * s) ^ 2) +
        2 * (s ^ 2 + δ) ^ (σ - 3 / 2) * ‖C‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by norm_num) hr)]
      have ht₁' : ‖E₁‖ ≤ (3 / 2 - σ) * (s ^ 2 / 2 + δ) ^ (σ - 5 / 2) * (A * s) ^ 2 := ht₁
      linarith
    _ ≤ _ := by dsimp [A] at *; nlinarith [mul_le_mul_of_nonneg_left hw (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hp),
      mul_le_mul_of_nonneg_left hd (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (norm_nonneg C))]

end SharpLiebThirring.MatrixProof

namespace SharpLiebThirring.MatrixProof
open ScalarProof Matrix
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
variable {n : Type u18} [Fintype n] [DecidableEq n]

lemma continuous_quadratic_cfc {δ : ℝ} (hδ : 0 < δ) (σ : ℝ)
    {C B : Matrix n n ℂ} (hC : C.IsHermitian) (hB : B.IsHermitian) :
    Continuous (fun s : ℝ ↦ cfc (regularizedPrimitive σ δ) (quadraticMatrix C B s)) := by
  exact Continuous.cfc_of_mem_nhdsSet (s := Set.univ) _ (Filter.univ_mem) (by
    unfold quadraticMatrix
    fun_prop) (fun s ↦ quadraticMatrix_hermitian hC hB s)
      (primitive_differentiable σ hδ).continuous.continuousOn

lemma continuous_pairedFieldIntegrand {δ : ℝ} (hδ : 0 < δ) (σ : ℝ)
    {C B : Matrix n n ℂ} (hC : C.IsHermitian) (hB : B.IsHermitian) :
    Continuous (pairedFieldIntegrand σ δ C B) := by
  unfold pairedFieldIntegrand
  exact ((continuous_quadratic_cfc hδ σ hC hB).add
    ((continuous_quadratic_cfc hδ σ hC hB).comp continuous_neg)).sub
    (((continuous_const.mul ((primitive_differentiable σ hδ).continuous.comp
      (continuous_pow 2)))).smul continuous_const)

lemma integrable_pairedFieldIntegrand {σ δ : ℝ} (hσ : σ < 1) (hδ : 0 < δ)
    {C B : Matrix n n ℂ} (hC : C.IsHermitian) (hB : B.IsHermitian) :
    Integrable (pairedFieldIntegrand σ δ C B) := by
  apply MeasureTheory.LocallyIntegrable.integrable_of_isBigO_atTop_of_norm_isNegInvariant
    (continuous_pairedFieldIntegrand hδ σ hC hB).locallyIntegrable
    (g := fun s : ℝ ↦ (1 + s ^ 2) ^ (σ - 3 / 2))
  · exact Filter.Eventually.of_forall (fun s ↦ congrArg norm
      ((pairedFieldIntegrand_even σ δ C B s).symm))
  · apply Asymptotics.IsBigO.of_bound
      (2 * (3 / 2 - σ) * (1 / 4 : ℝ) ^ (σ - 5 / 2) * (‖C‖ + 2 * ‖B‖) ^ 2 +
        2 * ‖C‖ * (1 / 2 : ℝ) ^ (σ - 3 / 2))
    filter_upwards [eventually_ge_atTop (max 1 (2 * (‖C‖ + 2 * ‖B‖)))] with s hs
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by positivity : 0 ≤ 1 + s ^ 2) _)]
    exact pairedFieldIntegrand_bound hσ hδ hC hB hs
  · exact (normalization_integrable hσ).integrableAtFilter atTop

def fieldIntegrand (σ δ : ℝ) (C B : Matrix n n ℂ) (s : ℝ) : Matrix n n ℂ :=
  cfc (regularizedPrimitive σ δ) (quadraticMatrix C B s) -
    regularizedPrimitive σ δ (s ^ 2) • 1

def hermitianField (σ δ : ℝ) (C B : Matrix n n ℂ) : Matrix n n ℂ :=
  (fieldNormalization σ / 2) • ∫ s : ℝ, pairedFieldIntegrand σ δ C B s

lemma continuous_fieldIntegrand {δ : ℝ} (hδ : 0 < δ) (σ : ℝ)
    {C B : Matrix n n ℂ} (hC : C.IsHermitian) (hB : B.IsHermitian) :
    Continuous (fieldIntegrand σ δ C B) :=
  (continuous_quadratic_cfc hδ σ hC hB).sub
    (((primitive_differentiable σ hδ).continuous.comp (continuous_pow 2)).smul continuous_const)

lemma cutoff_paired_identity {δ : ℝ} (hδ : 0 < δ) (σ : ℝ)
    {C B : Matrix n n ℂ} (hC : C.IsHermitian) (hB : B.IsHermitian) (R : ℝ) :
    (∫ s in -R..R, pairedFieldIntegrand σ δ C B s) =
      (2 : ℝ) • ∫ s in -R..R, fieldIntegrand σ δ C B s := by
  have hc := continuous_fieldIntegrand hδ σ hC hB
  have he : pairedFieldIntegrand σ δ C B = fun s ↦
      fieldIntegrand σ δ C B s + fieldIntegrand σ δ C B (-s) := by
    funext s
    simp only [pairedFieldIntegrand, fieldIntegrand, neg_sq]
    module
  rw [he]
  dsimp only
  erw [intervalIntegral.integral_add (hc.intervalIntegrable _ _)
    ((hc.comp continuous_neg).intervalIntegrable _ _)]
  have hn := intervalIntegral.integral_comp_neg (f := fieldIntegrand σ δ C B) (a := -R) (b := R)
  simp only [neg_neg] at hn
  simp only [Function.comp_apply]
  erw [hn]
  module

lemma hermitianField_cutoff_limit {σ δ : ℝ} (hσ : σ < 1) (hδ : 0 < δ)
    {C B : Matrix n n ℂ} (hC : C.IsHermitian) (hB : B.IsHermitian) :
    Tendsto (fun R : ℝ ↦ fieldNormalization σ • ∫ s in -R..R, fieldIntegrand σ δ C B s)
      atTop (𝓝 (hermitianField σ δ C B)) := by
  have hi := integrable_pairedFieldIntegrand hσ hδ hC hB
  have ht := intervalIntegral_tendsto_integral hi tendsto_neg_atTop_atBot tendsto_id
  have hh := ht.const_smul (fieldNormalization σ / 2)
  simp only [id_eq] at hh
  convert! hh using 1
  funext R
  rw [cutoff_paired_identity hδ σ hC hB, smul_smul]
  congr 1
  ring

end SharpLiebThirring.MatrixProof

end
end
end

end OAI
end

section
-- module Solutions.OAIQW_LiebThirring.RankOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u19 u20 u21 u22 u23 u24

noncomputable section
open MeasureTheory
open scoped ENNReal Matrix.Norms.L2Operator
open Matrix
open Matrix Unitary MeasureTheory Set
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
noncomputable section
open Matrix Unitary MeasureTheory Set
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder CStarAlgebra
noncomputable section
open MeasureTheory Set Filter
open scoped Topology


namespace SharpLiebThirring.MatrixProof
open ScalarProof Matrix
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
variable {n : Type u19} [Fintype n] [DecidableEq n]

/-- A diagonal entry after unitary conjugation is a positive unital state. -/
def unitaryState (U : unitary (Matrix n n ℂ)) (i : n) : Matrix n n ℂ →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A ↦ (conjStarAlgAut ℂ (Matrix n n ℂ) U A i i).re
      map_add' := by intros; simp only [map_add, Matrix.add_apply, Complex.add_re]
      map_smul' := by intros; simp }

@[simp] lemma unitaryState_apply (U : unitary (Matrix n n ℂ)) (i : n) (A : Matrix n n ℂ) :
    unitaryState U i A = (conjStarAlgAut ℂ (Matrix n n ℂ) U A i i).re := rfl

@[simp] lemma unitaryState_one (U : unitary (Matrix n n ℂ)) (i : n) :
    unitaryState U i 1 = 1 := by simp

end SharpLiebThirring.MatrixProof

namespace SharpLiebThirring.MatrixProof
open ScalarProof Matrix MeasureTheory Set
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder Topology
variable {n : Type u20} [Fintype n] [DecidableEq n]

def diagonalFieldIntegrand (σ δ d : ℝ) (z : n → ℝ) (s : ℝ) : Matrix n n ℂ :=
  diagonal (fun i ↦ ((regularizedPrimitive σ δ ((s - z i) ^ 2 + d) -
    regularizedPrimitive σ δ (s ^ 2) : ℝ) : ℂ))

end SharpLiebThirring.MatrixProof

namespace SharpLiebThirring.MatrixProof
open ScalarProof Matrix MeasureTheory Set
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder Topology
variable {n : Type u22} [Fintype n] [DecidableEq n]

def vectorMass (a : n → ℂ) : ℝ := ∑ i, Complex.normSq (a i)

end SharpLiebThirring.MatrixProof
namespace SharpLiebThirring.MatrixProof
open ScalarProof Matrix MeasureTheory Set
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder Topology
variable {n : Type u23} [Fintype n] [DecidableEq n]

def unitaryConjCLM (U : unitary (Matrix n n ℂ)) : Matrix n n ℂ →L[ℝ] Matrix n n ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := conjStarAlgAut ℂ (Matrix n n ℂ) U
      map_add' := by intros; exact map_add _ _ _
      map_smul' := by intros; simp }

@[simp] lemma unitaryConjCLM_apply (U : unitary (Matrix n n ℂ)) (A : Matrix n n ℂ) :
    unitaryConjCLM U A = conjStarAlgAut ℂ (Matrix n n ℂ) U A := rfl

end SharpLiebThirring.MatrixProof
namespace SharpLiebThirring.MatrixProof
open ScalarProof Matrix MeasureTheory Set
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder Topology
variable {n : Type u24} [Fintype n] [DecidableEq n]

def complexify : Matrix n n ℝ →⋆ₐ[ℝ] Matrix n n ℂ :=
  { (Algebra.ofId ℝ ℂ).mapMatrix with
    map_star' := by
      intro A
      ext i j
      simp [Matrix.star_apply] }

@[simp] lemma complexify_apply (A : Matrix n n ℝ) (i j : n) : complexify A i j = (A i j : ℂ) := rfl

def complexifyCLM : Matrix n n ℝ →L[ℝ] Matrix n n ℂ :=
  complexify.toLinearMap.toContinuousLinearMap

@[simp] lemma complexifyCLM_apply (A : Matrix n n ℝ) : complexifyCLM A = complexify A := rfl

def realPartCLM : Matrix n n ℂ →L[ℝ] Matrix n n ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A ↦ A.map Complex.re
      map_add' := by intros; ext i j; simp
      map_smul' := by intros; ext i j; simp }

@[simp] lemma realPartCLM_complexify (A : Matrix n n ℝ) : realPartCLM (complexify A) = A := by
  ext i j
  exact Complex.ofReal_re _

lemma complexify_hermitian {A : Matrix n n ℝ} (hA : A.IsHermitian) : (complexify A).IsHermitian := by
  change star (complexify A) = complexify A
  rw [← map_star, hA.star_eq]

lemma complexify_cfc {A : Matrix n n ℝ} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    complexify (cfc f A) = cfc f (complexify A) :=
  StarAlgHomClass.map_cfc complexify f A (A.finite_real_spectrum.continuousOn f)
    complexifyCLM.continuous hA (complexify_hermitian hA)

lemma matrixX_hermitian {N : ℕ} (k : Fin N → ℝ) {B : Matrix (Fin N) (Fin N) ℝ}
    (hB : B.IsHermitian) (s : ℝ) : (matrixX k B s).IsHermitian := by
  exact ((isHermitian_diagonal (fun i ↦ k i ^ 2)).sub (hB.smul (isSelfAdjoint_iff.2 rfl : IsSelfAdjoint (2 * s)))).add
    (isHermitian_one.smul (isSelfAdjoint_iff.2 rfl : IsSelfAdjoint (s ^ 2)))

lemma complexify_matrixX {N : ℕ} (k : Fin N → ℝ) (B : Matrix (Fin N) (Fin N) ℝ) (s : ℝ) :
    complexify (matrixX k B s) = quadraticMatrix (complexify (diagonal (fun i ↦ k i ^ 2)))
      (complexify B) s := by
  simp only [matrixX, quadraticMatrix, map_add, map_sub, map_smul, map_one]
  abel

lemma complexify_truncatedField {N : ℕ} {σ δ : ℝ} (hδ : 0 < δ) (k : Fin N → ℝ)
    {B : Matrix (Fin N) (Fin N) ℝ} (hB : B.IsHermitian) (R : ℝ) :
    complexify (truncatedField σ δ k B R) = fieldNormalization σ • ∫ s in -R..R,
      fieldIntegrand σ δ (complexify (diagonal (fun i ↦ k i ^ 2))) (complexify B) s := by
  have hc : Continuous (fun s ↦ cfc (regularizedPrimitive σ δ) (matrixX k B s) -
      regularizedPrimitive σ δ (s ^ 2) • (1 : Matrix (Fin N) (Fin N) ℝ)) := by
    have hx : Continuous (fun s ↦ cfc (regularizedPrimitive σ δ) (matrixX k B s)) :=
      Continuous.cfc_of_mem_nhdsSet (s := Set.univ) _ Filter.univ_mem
        (by unfold matrixX; fun_prop) (matrixX_hermitian k hB)
        (primitive_differentiable σ hδ).continuous.continuousOn
    exact hx.sub (((primitive_differentiable σ hδ).continuous.comp (continuous_pow 2)).smul continuous_const)
  change complexifyCLM (truncatedField σ δ k B R) = _
  rw [truncatedField, map_smul, ← complexifyCLM.intervalIntegral_comp_comm (hc.intervalIntegrable _ _)]
  congr 1
  apply intervalIntegral.integral_congr
  intro s hs
  simp only [complexifyCLM_apply, map_sub, map_smul, map_one,
    complexify_cfc (matrixX_hermitian k hB s), complexify_matrixX, fieldIntegrand]

lemma complexify_matrixField {N : ℕ} {σ δ : ℝ} (hσ : σ < 1) (hδ : 0 < δ)
    (k : Fin N → ℝ) {B : Matrix (Fin N) (Fin N) ℝ} (hB : B.IsHermitian) :
    complexify (matrixField σ δ k B) =
      hermitianField σ δ (complexify (diagonal (fun i ↦ k i ^ 2))) (complexify B) := by
  have hC := complexify_hermitian (isHermitian_diagonal (fun i ↦ k i ^ 2))
  have hl := hermitianField_cutoff_limit hσ hδ hC (complexify_hermitian hB)
  have ht : Tendsto (fun R ↦ complexify (truncatedField σ δ k B R)) atTop (𝓝
      (hermitianField σ δ (complexify (diagonal (fun i ↦ k i ^ 2))) (complexify B))) := by
    simpa only [complexify_truncatedField hδ k hB] using hl
  have hr := realPartCLM.continuous.continuousAt.tendsto.comp ht
  change Tendsto (fun R ↦ realPartCLM (complexify (truncatedField σ δ k B R))) atTop
    (𝓝 (realPartCLM (hermitianField σ δ
      (complexify (diagonal (fun i ↦ k i ^ 2))) (complexify B)))) at hr
  simp only [realPartCLM_complexify] at hr
  have he : matrixField σ δ k B = realPartCLM
      (hermitianField σ δ (complexify (diagonal (fun i ↦ k i ^ 2))) (complexify B)) := hr.limUnder_eq
  have hh := complexifyCLM.continuous.continuousAt.tendsto.comp hr
  change Tendsto (fun R ↦ complexify (truncatedField σ δ k B R)) atTop
    (𝓝 (complexify (realPartCLM (hermitianField σ δ
      (complexify (diagonal (fun i ↦ k i ^ 2))) (complexify B))))) at hh
  rw [he]
  exact tendsto_nhds_unique hh ht

end SharpLiebThirring.MatrixProof

end
end
end

end OAI
end

section
-- module Solutions.OAIQW_LiebThirring.FieldRegularity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u25 u26 u27 u28 u29 u30 u31

noncomputable section
open MeasureTheory
open scoped ENNReal Matrix.Norms.L2Operator
open Matrix
open Matrix Unitary MeasureTheory Set
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
noncomputable section
open Matrix Unitary MeasureTheory Set
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder CStarAlgebra
noncomputable section
open MeasureTheory Set Filter
open scoped Topology

namespace SharpLiebThirring.MatrixProof
open Matrix
open scoped Matrix.Norms.L2Operator
variable {n : Type u25} [Fintype n] [DecidableEq n]

def flattenCLM : Matrix n n ℂ →L[ℝ] EuclideanSpace ℂ (n × n) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A ↦ WithLp.toLp 2 (fun ij ↦ A ij.1 ij.2)
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }

def unflattenCLM : EuclideanSpace ℂ (n × n) →L[ℝ] Matrix n n ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v i j ↦ v (i, j)
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }

omit [DecidableEq n] in
@[simp] lemma unflatten_flatten (A : Matrix n n ℂ) : unflattenCLM (flattenCLM A) = A := rfl

end SharpLiebThirring.MatrixProof

open scoped NNReal
namespace SharpLiebThirring.ScalarProof
open Set

/-- The second scalar primitive used for the matrix trace potential. -/
def secondPrimitive (σ δ y : ℝ) : ℝ := ∫ t in 0..y, regularizedPrimitive σ δ t

end SharpLiebThirring.ScalarProof

namespace SharpLiebThirring.MatrixProof
open Matrix ScalarProof Asymptotics Filter
open scoped Matrix.Norms.L2Operator Topology
variable {n : Type u27} [Fintype n] [DecidableEq n]

def hermitianInclusion : selfAdjoint (Matrix n n ℂ) →L[ℝ] Matrix n n ℂ :=
  { toFun := Subtype.val
    map_add' := fun _ _ ↦ rfl
    map_smul' := fun _ _ ↦ rfl
    cont := continuous_subtype_val }

end SharpLiebThirring.MatrixProof

namespace SharpLiebThirring.MatrixProof
open Matrix ScalarProof
open scoped Matrix.Norms.L2Operator
variable {n : Type u28} [Fintype n] [DecidableEq n]

def matrixNormBridge (n : Type u29) [Fintype n] [DecidableEq n] : ℝ :=
  ‖(unflattenCLM : EuclideanSpace ℂ (n × n) →L[ℝ] Matrix n n ℂ)‖ *
    ‖(flattenCLM : Matrix n n ℂ →L[ℝ] EuclideanSpace ℂ (n × n))‖

end SharpLiebThirring.MatrixProof

namespace SharpLiebThirring.MatrixProof
open Matrix ScalarProof
open scoped Matrix.Norms.L2Operator
variable {n : Type u30} [Fintype n] [DecidableEq n]

def quadraticRemainder (σ δ : ℝ) (C B : Matrix n n ℂ) (s : ℝ) : Matrix n n ℂ :=
  cfc (regularizedPrimitive σ δ) (quadraticMatrix C B s) -
    regularizedPrimitive σ δ (s ^ 2) • 1 -
    (s ^ 2 + δ) ^ (σ - 3 / 2) • (C - (2 * s) • B)

end SharpLiebThirring.MatrixProof

namespace SharpLiebThirring.MatrixProof
open Matrix ScalarProof MeasureTheory
open scoped Matrix.Norms.L2Operator NNReal
variable {n : Type u31} [Fintype n] [DecidableEq n]

def fieldLipEnvelope (σ δ M : ℝ) (C : Matrix n n ℂ) (s : ℝ) : ℝ :=
  (Set.Icc (-max 1 (2 * (‖C‖ + 2 * M))) (max 1 (2 * (‖C‖ + 2 * M)))).indicator
    (fun s : ℝ ↦ 4 * matrixNormBridge n * δ ^ (σ - 3 / 2) * |s|) s +
  4 * matrixNormBridge n * (3 / 2 - σ) * (‖C‖ + 2 * M) *
    (1 / 4 : ℝ) ^ (σ - 5 / 2) * (1 + s ^ 2) ^ (σ - 3 / 2)

end SharpLiebThirring.MatrixProof

end
end
end

end OAI
end

section
-- module Solutions.OAIQW_LiebThirring.FieldPrimitive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u32 u33 u34

noncomputable section
open MeasureTheory
open scoped ENNReal Matrix.Norms.L2Operator
open Matrix
open Matrix Unitary MeasureTheory Set
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
noncomputable section
open Matrix Unitary MeasureTheory Set
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder CStarAlgebra
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
open scoped NNReal


namespace SharpLiebThirring.MatrixProof
open Matrix ScalarProof MeasureTheory Filter
open scoped Matrix.Norms.L2Operator Topology
variable {n : Type u32} [Fintype n] [DecidableEq n]

-- Select the inherited subspace seminorm, avoiding the duplicate subgroup
-- class instance during elaboration of iterated continuous-linear maps.
local instance instSeminormedAddCommGroupSubtypeMatrixComplexMemAddSubgroupSelfAdjoint_solutions : SeminormedAddCommGroup (selfAdjoint (Matrix n n ℂ)) :=
  (inferInstance : NormedAddCommGroup (selfAdjoint (Matrix n n ℂ))).toSeminormedAddCommGroup
local instance instNormedSpaceRealSubtypeMatrixComplexMemAddSubgroupSelfAdjoint_solutions : NormedSpace ℝ (selfAdjoint (Matrix n n ℂ)) := inferInstance

def traceGradientMap : Matrix n n ℂ →L[ℝ] (selfAdjoint (Matrix n n ℂ) →L[ℝ] ℝ) :=
  LinearMap.toContinuousLinearMap
  { toFun := fun M ↦ (tracePairCLM M).comp hermitianInclusion
    map_add' := by
      intro M N
      ext H
      simp [tracePairCLM_apply, hermitianInclusion, add_mul, trace_add]
    map_smul' := by
      intro r M
      ext H
      simp [tracePairCLM_apply, hermitianInclusion, trace_smul] }

@[simp] lemma traceGradientMap_apply (M : Matrix n n ℂ) (B : selfAdjoint (Matrix n n ℂ)) :
    traceGradientMap M B = (trace (M * (B : Matrix n n ℂ))).re := rfl

def traceGradientNorm : ℝ := ‖traceGradientMap (n := n)‖

def quadraticSelfAdjoint (C : selfAdjoint (Matrix n n ℂ)) (s : ℝ)
    (B : selfAdjoint (Matrix n n ℂ)) : selfAdjoint (Matrix n n ℂ) :=
  C - (2 * s) • B + (s ^ 2) • 1

@[simp] lemma quadraticSelfAdjoint_coe (C : selfAdjoint (Matrix n n ℂ)) (s : ℝ)
    (B : selfAdjoint (Matrix n n ℂ)) :
    (quadraticSelfAdjoint C s B : Matrix n n ℂ) = quadraticMatrix C B s := by
  simp [quadraticSelfAdjoint, quadraticMatrix, add_comm]

/-- Paired trace potential. At s=0 the assigned value is immaterial to its integral. -/
def pairedTracePotential (σ δ : ℝ) (C : selfAdjoint (Matrix n n ℂ))
    (B : selfAdjoint (Matrix n n ℂ)) (s : ℝ) : ℝ :=
  -( (trace (cfc (secondPrimitive σ δ) (quadraticMatrix (C : Matrix n n ℂ) (B : Matrix n n ℂ) s))).re -
    (trace (cfc (secondPrimitive σ δ) (quadraticMatrix (C : Matrix n n ℂ) (B : Matrix n n ℂ) (-s)))).re) / (2 * s) -
      2 * regularizedPrimitive σ δ (s ^ 2) * (trace (B : Matrix n n ℂ)).re

end SharpLiebThirring.MatrixProof

namespace SharpLiebThirring.MatrixProof
open Matrix ScalarProof MeasureTheory Filter
open scoped Matrix.Norms.L2Operator Topology
variable {n : Type u33} [Fintype n] [DecidableEq n]

-- Select the inherited subspace seminorm, avoiding the duplicate subgroup
-- class instance during elaboration of iterated continuous-linear maps.
local instance instSeminormedAddCommGroupSubtypeMatrixComplexMemAddSubgroupSelfAdjoint_solutions_1 : SeminormedAddCommGroup (selfAdjoint (Matrix n n ℂ)) :=
  (inferInstance : NormedAddCommGroup (selfAdjoint (Matrix n n ℂ))).toSeminormedAddCommGroup
local instance instNormedSpaceRealSubtypeMatrixComplexMemAddSubgroupSelfAdjoint_solutions_1 : NormedSpace ℝ (selfAdjoint (Matrix n n ℂ)) := inferInstance

def fieldGradientEnvelope (σ δ M : ℝ) (C : Matrix n n ℂ) (s : ℝ) : ℝ :=
  traceGradientNorm (n := n) *
    (‖pairedFieldIntegrand σ δ (C : Matrix n n ℂ) 0 s‖ + fieldLipEnvelope σ δ M (C : Matrix n n ℂ) s * M)

def hermitianPotential (σ δ : ℝ) (C B : selfAdjoint (Matrix n n ℂ)) : ℝ :=
  (fieldNormalization σ / 2) * ∫ s : ℝ, pairedTracePotential σ δ C B s

end SharpLiebThirring.MatrixProof

namespace SharpLiebThirring.MatrixProof
open Matrix ScalarProof MeasureTheory Filter
open scoped Matrix.Norms.L2Operator Topology
variable {n : Type u34} [Fintype n] [DecidableEq n]

local instance instSeminormedAddCommGroupSubtypeMatrixComplexMemAddSubgroupSelfAdjoint_solutions_2 : SeminormedAddCommGroup (selfAdjoint (Matrix n n ℂ)) :=
  (inferInstance : NormedAddCommGroup (selfAdjoint (Matrix n n ℂ))).toSeminormedAddCommGroup
local instance instNormedSpaceRealSubtypeMatrixComplexMemAddSubgroupSelfAdjoint_solutions_2 : NormedSpace ℝ (selfAdjoint (Matrix n n ℂ)) := inferInstance

end SharpLiebThirring.MatrixProof

namespace SharpLiebThirring.MatrixProof
open Matrix ScalarProof MeasureTheory Filter
open scoped Matrix.Norms.L2Operator Topology
variable {N : ℕ}

def realHermitianComplexify (B : selfAdjoint (Matrix (Fin N) (Fin N) ℝ)) :
    selfAdjoint (Matrix (Fin N) (Fin N) ℂ) := ⟨complexify B, complexify_hermitian B.prop⟩

@[simp] lemma realHermitianComplexify_coe (B : selfAdjoint (Matrix (Fin N) (Fin N) ℝ)) :
    (realHermitianComplexify B : Matrix (Fin N) (Fin N) ℂ) = complexify B := rfl

lemma realHermitianComplexify_continuous : Continuous (realHermitianComplexify (N := N)) :=
  (complexifyCLM.continuous.comp continuous_subtype_val).subtype_mk _

end SharpLiebThirring.MatrixProof

end
end
end

end OAI
end

section
-- module Solutions.OAIQW_LiebThirring.ActionPenalty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u35

noncomputable section
open MeasureTheory
open scoped ENNReal Matrix.Norms.L2Operator
open Matrix
open Matrix Unitary MeasureTheory Set
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
noncomputable section
open Matrix Unitary MeasureTheory Set
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder CStarAlgebra
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
open scoped NNReal


namespace SharpLiebThirring.ActionProof
open Matrix MatrixProof Set
open scoped Matrix.Norms.L2Operator
variable {N : ℕ}

def actionDefect (σ : ℝ) (k : Fin N → ℝ)
    (z : selfAdjoint (Matrix (Fin N) (Fin N) ℝ) × (Fin N → ℝ)) : ℝ :=
  (∑ i, z.2 i ^ 2) ^ (1 + 1 / σ) -
    ∑ i, z.2 i * ((diagonal (fun i ↦ k i ^ 2) - (z.1 : Matrix (Fin N) (Fin N) ℝ) ^ 2) *ᵥ z.2) i

def constraintDefect (σ δ : ℝ) (k : Fin N → ℝ)
    (z : selfAdjoint (Matrix (Fin N) (Fin N) ℝ) × (Fin N → ℝ)) : ℝ :=
  ∑ i, ∑ j, (matrixField σ δ k z.1 i j - z.2 i * z.2 j) ^ 2

end SharpLiebThirring.ActionProof

end
end
end

end OAI
end

section
-- module Solutions.OAIQW_LiebThirring.BoundaryValues
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u36

noncomputable section
open MeasureTheory
open scoped ENNReal Matrix.Norms.L2Operator
open Matrix
open Matrix Unitary MeasureTheory Set
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
noncomputable section
open Matrix Unitary MeasureTheory Set
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder CStarAlgebra
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
open scoped NNReal

namespace SharpLiebThirring.MatrixProof
open Matrix ScalarProof MeasureTheory Filter
open scoped Matrix.Norms.L2Operator Topology
variable {N : ℕ}

local instance instSeminormedAddCommGroupSubtypeMatrixFinComplexMemAddSubgroupSelfAdjoint_solutions : SeminormedAddCommGroup (selfAdjoint (Matrix (Fin N) (Fin N) ℂ)) :=
  (inferInstance : NormedAddCommGroup (selfAdjoint (Matrix (Fin N) (Fin N) ℂ))).toSeminormedAddCommGroup
local instance instNormedSpaceRealSubtypeMatrixFinComplexMemAddSubgroupSelfAdjoint_solutions : NormedSpace ℝ (selfAdjoint (Matrix (Fin N) (Fin N) ℂ)) := inferInstance

@[simp] lemma realHermitianComplexify_smul (t : ℝ)
    (B : selfAdjoint (Matrix (Fin N) (Fin N) ℝ)) :
    realHermitianComplexify (t • B) = t • realHermitianComplexify B := by
  apply Subtype.ext
  exact map_smul complexify t (B : Matrix (Fin N) (Fin N) ℝ)

def realHermitianComplexifyCLM :
    selfAdjoint (Matrix (Fin N) (Fin N) ℝ) →L[ℝ] selfAdjoint (Matrix (Fin N) (Fin N) ℂ) :=
  { toFun := realHermitianComplexify
    map_add' := by
      intro A B
      apply Subtype.ext
      exact map_add complexify (A : Matrix (Fin N) (Fin N) ℝ) (B : Matrix (Fin N) (Fin N) ℝ)
    map_smul' := realHermitianComplexify_smul
    cont := realHermitianComplexify_continuous }

@[simp] lemma realHermitianComplexifyCLM_apply (B : selfAdjoint (Matrix (Fin N) (Fin N) ℝ)) :
    realHermitianComplexifyCLM B = realHermitianComplexify B := rfl

def realK2SelfAdjoint (k : Fin N → ℝ) : selfAdjoint (Matrix (Fin N) (Fin N) ℂ) :=
  ⟨complexify (diagonal (fun i ↦ k i ^ 2)), complexify_hermitian (isHermitian_diagonal _)⟩

end SharpLiebThirring.MatrixProof
namespace SharpLiebThirring.MatrixProof
open Matrix ScalarProof MeasureTheory Filter
open scoped Matrix.Norms.L2Operator Topology
variable {N : ℕ}

lemma hermitian_integral {f : ℝ → Matrix (Fin N) (Fin N) ℂ}
    (hf : ∀ x, (f x).IsHermitian) : (∫ x, f x).IsHermitian := by
  change star (∫ x, f x) = ∫ x, f x
  have hh := (starL ℝ : Matrix (Fin N) (Fin N) ℂ ≃L[ℝ] Matrix (Fin N) (Fin N) ℂ).integral_comp_comm (μ := volume) f
  change (∫ x, star (f x)) = star (∫ x, f x) at hh
  rw [← hh]
  apply integral_congr_ae
  exact Eventually.of_forall (fun x ↦ hf x)

lemma hermitianField_isHermitian (σ δ : ℝ) (C B : Matrix (Fin N) (Fin N) ℂ) :
    (hermitianField σ δ C B).IsHermitian := by
  apply Matrix.IsHermitian.smul _ (IsSelfAdjoint.all _)
  apply hermitian_integral
  intro s
  exact ((cfc_predicate (regularizedPrimitive σ δ) (quadraticMatrix C B s)).add
    (cfc_predicate (regularizedPrimitive σ δ) (quadraticMatrix C B (-s)))).sub
      (isHermitian_one.smul (IsSelfAdjoint.all _))

lemma matrixField_isHermitian {σ δ : ℝ} (hσ : σ < 1) (hδ : 0 < δ)
    (k : Fin N → ℝ) {B : Matrix (Fin N) (Fin N) ℝ} (hB : B.IsHermitian) :
    (matrixField σ δ k B).IsHermitian := by
  have hh := hermitianField_isHermitian σ δ
    (complexify (diagonal (fun i ↦ k i ^ 2))) (complexify B)
  rw [← complexify_matrixField hσ hδ k hB] at hh
  change star (matrixField σ δ k B) = matrixField σ δ k B
  ext i j
  have he := congrFun (congrFun hh i) j
  simpa [complexify, conjTranspose_apply] using congrArg Complex.re he

end SharpLiebThirring.MatrixProof

end
end
end

end OAI
end

section
-- module Solutions.OAIQW_LiebThirring.ActionBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal Matrix.Norms.L2Operator
open Matrix
open Matrix Unitary MeasureTheory Set
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
noncomputable section
open Matrix Unitary MeasureTheory Set
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder CStarAlgebra
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
open scoped NNReal


namespace SharpLiebThirring.SpectralProof
open Matrix MeasureTheory
open scoped Matrix.Norms.L2Operator

def actionYoungConstant (σ : ℝ) : ℝ := σ ^ σ / (1 + σ) ^ (1 + σ)

end SharpLiebThirring.SpectralProof

namespace SharpLiebThirring.ActionProof
open Matrix MatrixProof MeasureTheory
open scoped Matrix.Norms.L2Operator
variable {N : ℕ}

/-- Real entry evaluation on the actual symmetric-matrix normed space. -/
def realSelfAdjointEntryCLM (i j : Fin N) :
    selfAdjoint (Matrix (Fin N) (Fin N) ℝ) →L[ℝ] ℝ :=
  { toFun := fun B ↦ (B : Matrix (Fin N) (Fin N) ℝ) i j
    map_add' := fun _ _ ↦ rfl
    map_smul' := fun _ _ ↦ rfl
    cont := by
      have hc : Continuous (fun A : Matrix (Fin N) (Fin N) ℝ ↦ A i j) :=
        (({ toFun := fun A : Matrix (Fin N) (Fin N) ℝ ↦ A i j
            map_add' := fun _ _ ↦ rfl
            map_smul' := fun _ _ ↦ rfl } : Matrix (Fin N) (Fin N) ℝ →ₗ[ℝ] ℝ).toContinuousLinearMap).continuous
      exact hc.comp continuous_subtype_val }

end SharpLiebThirring.ActionProof

end
end
end

end OAI
end

section
-- module Solutions.OAIQW_LiebThirring.BoundState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal Matrix.Norms.L2Operator
open Matrix
open Matrix Unitary MeasureTheory Set
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
noncomputable section
open Matrix Unitary MeasureTheory Set
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder CStarAlgebra
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
open scoped NNReal


namespace SharpLiebThirring.ExtremizerProof
open MeasureTheory Set Filter
open scoped Topology ENNReal

/-- The positive, unnormalized bound state. -/
def profile (r x : ℝ) : ℝ := (Real.cosh (r * x)) ^ (-1 / r)

def potential (r x : ℝ) : ℝ := (r + 1) * (Real.cosh (r * x))⁻¹ ^ 2

def profileDerivative (r x : ℝ) : ℝ := -Real.tanh (r * x) * profile r x

lemma profile_pos (r x : ℝ) : 0 < profile r x :=
  Real.rpow_pos_of_pos (Real.cosh_pos _) _

lemma profile_continuous (r : ℝ) : Continuous (profile r) := by
  exact (Real.continuous_cosh.comp (continuous_const.mul continuous_id)).rpow_const
    (fun _ ↦ Or.inl (ne_of_gt (Real.cosh_pos _)))

lemma profile_contDiff (r : ℝ) : ContDiff ℝ ⊤ (profile r) := by
  exact (Real.contDiff_cosh.comp (contDiff_const.mul contDiff_id)).rpow_const_of_ne
    (fun _ ↦ ne_of_gt (Real.cosh_pos _))

lemma profile_hasDerivAt {r : ℝ} (hr : 0 < r) (x : ℝ) :
    HasDerivAt (profile r) (profileDerivative r x) x := by
  have hh := ((Real.hasDerivAt_cosh (r*x)).comp x ((hasDerivAt_id x).const_mul r)).rpow_const (p := -1 / r)
    (Or.inl (ne_of_gt (Real.cosh_pos _)))
  convert! hh using 1
  unfold profileDerivative profile
  simp only [Function.comp_apply]
  rw [Real.tanh_eq_sinh_div_cosh, Real.rpow_sub (Real.cosh_pos _), Real.rpow_one]
  field_simp

lemma tanh_hasDerivAt (x : ℝ) :
    HasDerivAt Real.tanh ((Real.cosh x)⁻¹ ^ 2) x := by
  have hh := (Real.hasDerivAt_sinh x).div (Real.hasDerivAt_cosh x) (ne_of_gt (Real.cosh_pos x))
  convert! hh using 1
  · funext t
    exact Real.tanh_eq_sinh_div_cosh t
  · have hx := Real.cosh_sq_sub_sinh_sq x
    field_simp
    nlinarith

lemma profileDerivative_continuous (r : ℝ) : Continuous (profileDerivative r) := by
  have ht : Continuous Real.tanh := continuous_iff_continuousAt.mpr
    (fun x ↦ (tanh_hasDerivAt x).continuousAt)
  exact ((ht.comp (continuous_const.mul continuous_id)).neg).mul
    (profile_continuous r)

lemma cosh_lower_exponential (x : ℝ) : Real.exp |x| / 2 ≤ Real.cosh x := by
  rw [← Real.cosh_abs x, Real.cosh_eq]
  have hh := Real.exp_pos (-|x|)
  linarith

lemma profile_exponential_bound {r : ℝ} (hr : 0 < r) (x : ℝ) :
    profile r x ≤ 2 ^ (1 / r) * Real.exp (-|x|) := by
  have he : 0 < Real.exp |r*x| / 2 := by positivity
  have hp : -1 / r ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by norm_num) hr.le
  have hh := Real.rpow_le_rpow_of_nonpos he (cosh_lower_exponential (r*x)) hp
  change (Real.cosh (r*x)) ^ (-1 / r) ≤ _
  apply hh.trans_eq
  rw [Real.div_rpow (Real.exp_pos _).le (by norm_num), ← Real.exp_mul,
    abs_mul, abs_of_pos hr]
  have hmul : r * |x| * (-1 / r) = -|x| := by field_simp
  rw [hmul]
  have hpow : (2 : ℝ) ^ (-1 / r) = (2 ^ (1 / r))⁻¹ := by
    rw [show -1 / r = -(1 / r) by ring, Real.rpow_neg (by norm_num)]
  rw [hpow, div_inv_eq_mul, mul_comm]

lemma profileDerivative_exponential_bound {r : ℝ} (hr : 0 < r) (x : ℝ) :
    |profileDerivative r x| ≤ 2 ^ (1 / r) * Real.exp (-|x|) := by
  unfold profileDerivative
  rw [abs_mul, abs_neg, abs_of_pos (profile_pos r x)]
  exact (mul_le_of_le_one_left (profile_pos r x).le (Real.abs_tanh_lt_one _).le).trans
    (profile_exponential_bound hr x)

lemma integrable_exp_neg_abs {c : ℝ} (hc : 0 < c) :
    Integrable (fun x : ℝ ↦ Real.exp (-c * |x|)) := by
  have hp : IntegrableOn (fun x : ℝ ↦ Real.exp (-c * |x|)) (Ioi 0) := by
    apply (integrableOn_exp_mul_Ioi (neg_neg_of_pos hc) 0).congr_fun
    · intro x hx
      dsimp only
      rw [abs_of_pos (show 0 < x from hx)]
    · exact measurableSet_Ioi
  have hn : IntegrableOn (fun x : ℝ ↦ Real.exp (-c * |x|)) (Iic 0) := by
    apply (integrableOn_exp_mul_Iic hc 0).congr_fun
    · intro x hx
      dsimp only
      rw [abs_of_nonpos (show x ≤ 0 from hx)]
      congr 1
      ring
    · exact measurableSet_Iic
  have hh := hn.union hp
  simpa using hh

lemma memLp_exp_neg_abs {p : ℝ≥0∞} (hp : p ≠ 0) (hp' : p ≠ ⊤) :
    MemLp (fun x : ℝ ↦ Real.exp (-|x|)) p volume := by
  have hc : Continuous (fun x : ℝ ↦ Real.exp (-|x|)) := by fun_prop
  apply (integrable_norm_rpow_iff hc.aestronglyMeasurable hp hp').mp
  have hh := integrable_exp_neg_abs (ENNReal.toReal_pos hp hp')
  convert! hh using 1
  funext x
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_mul]
  congr 1
  ring

lemma profile_memLp (r : ℝ) (hr : 0 < r) {p : ℝ≥0∞} (hp : p ≠ 0) (hp' : p ≠ ⊤) :
    MemLp (profile r) p volume := by
  apply ((memLp_exp_neg_abs hp hp').const_mul (2 ^ (1 / r))).mono'
    (profile_continuous r).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun x ↦ by
    rw [Real.norm_eq_abs, abs_of_pos (profile_pos r x)]
    exact profile_exponential_bound hr x)

lemma profileDerivative_memLp (r : ℝ) (hr : 0 < r) {p : ℝ≥0∞} (hp : p ≠ 0) (hp' : p ≠ ⊤) :
    MemLp (profileDerivative r) p volume := by
  apply ((memLp_exp_neg_abs hp hp').const_mul (2 ^ (1 / r))).mono'
    (profileDerivative_continuous r).aestronglyMeasurable
  exact Filter.Eventually.of_forall (profileDerivative_exponential_bound hr)

end SharpLiebThirring.ExtremizerProof

namespace SharpLiebThirring.SobolevProof
open MeasureTheory Set Filter
open scoped Topology ENNReal ContDiff

/-- Fixed smooth compact cutoff, equal to one on [-1,1]. -/
def baseCutoff : ContDiffBump (0 : ℝ) := ⟨1, 2, by norm_num, by norm_num⟩

def cutoff (n : ℕ) (x : ℝ) : ℝ := baseCutoff ((n + 1 : ℝ)⁻¹ * x)

def cutoffDerivative (n : ℕ) (x : ℝ) : ℝ :=
  deriv (baseCutoff : ℝ → ℝ) ((n + 1 : ℝ)⁻¹ * x) * (n + 1 : ℝ)⁻¹

lemma baseCutoff_smooth : ContDiff ℝ ∞ (baseCutoff : ℝ → ℝ) := baseCutoff.contDiff

lemma scale_pos (n : ℕ) : 0 < (n + 1 : ℝ) := by positivity

lemma cutoff_contDiff (n : ℕ) : ContDiff ℝ ∞ (cutoff n) :=
  baseCutoff_smooth.comp (contDiff_const.mul contDiff_id)

lemma cutoff_compact (n : ℕ) : HasCompactSupport (cutoff n) := by
  change HasCompactSupport (fun x : ℝ ↦ baseCutoff ((n + 1 : ℝ)⁻¹ * x))
  simpa only [smul_eq_mul] using baseCutoff.hasCompactSupport.comp_smul
    (inv_ne_zero (ne_of_gt (scale_pos n)))

lemma cutoff_hasDerivAt (n : ℕ) (x : ℝ) :
    HasDerivAt (cutoff n) (cutoffDerivative n x) x := by
  change HasDerivAt (fun y : ℝ ↦ baseCutoff ((n + 1 : ℝ)⁻¹ * y))
    (deriv (baseCutoff : ℝ → ℝ) ((n + 1 : ℝ)⁻¹ * x) * (n + 1 : ℝ)⁻¹) x
  convert!
    (((baseCutoff_smooth.differentiable (by norm_num)) _).hasDerivAt.comp x
      ((hasDerivAt_id x).const_mul (n + 1 : ℝ)⁻¹)) using 1; simp only [id_eq, mul_one]

lemma cutoffDerivative_continuous (n : ℕ) : Continuous (cutoffDerivative n) := by
  exact (((baseCutoff_smooth.continuous_deriv (by norm_num)).comp
    (continuous_const.mul continuous_id)).mul continuous_const)

end SharpLiebThirring.SobolevProof

namespace SharpLiebThirring.SobolevProof
open MeasureTheory
open scoped ContDiff

/-- Classical smooth L² functions with L² derivative belong to the exact weak H¹ domain. -/
def smoothH1 (f f' : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hd : ∀ x, HasDerivAt f (f' x) x) (hfc : Continuous f')
    (hf2 : MemLp f 2 volume) (hf'2 : MemLp f' 2 volume) : H1 where
  val := f
  grad := f'
  val_memLp := hf2
  grad_memLp := hf'2
  weak_derivative := by
    intro φ hφ hφc
    apply integral_mul_deriv_eq_deriv_mul_of_integrable
    · exact fun x _ ↦ hd x
    · exact fun x _ ↦ ((hφ.differentiable (by norm_num)) x).hasDerivAt
    · exact (hf.continuous.mul (hφ.continuous_deriv (by norm_num))).integrable_of_hasCompactSupport
        hφc.deriv.mul_left
    · exact (hfc.mul hφ.continuous).integrable_of_hasCompactSupport hφc.mul_left
    · exact (hf.continuous.mul hφ.continuous).integrable_of_hasCompactSupport hφc.mul_left

end SharpLiebThirring.SobolevProof

namespace SharpLiebThirring.ExtremizerProof
open MeasureTheory Set Filter
open scoped Topology ENNReal ContDiff

def profileSecond (r x : ℝ) : ℝ := (1 - potential r x) * profile r x

/-- The exact unnormalized extremizing bound state, as an element of the weak form domain. -/
def boundState (r : ℝ) (hr : 0 < r) : H1 :=
  SobolevProof.smoothH1 (fun x ↦ (profile r x : ℂ)) (fun x ↦ (profileDerivative r x : ℂ))
    (Complex.ofRealCLM.contDiff.comp ((profile_contDiff r).of_le le_top))
    (fun x ↦ (profile_hasDerivAt hr x).ofReal_comp)
    (Complex.continuous_ofReal.comp (profileDerivative_continuous r))
    (profile_memLp r hr (by norm_num) (by norm_num)).ofReal
    (profileDerivative_memLp r hr (by norm_num) (by norm_num)).ofReal

end SharpLiebThirring.ExtremizerProof

namespace SharpLiebThirring
open MeasureTheory

/-- Scalar multiplication in the weak form domain, without choosing pointwise representatives. -/
def scaleH1 (c : ℂ) (u : H1) : H1 where
  val := fun x ↦ c * u.val x
  grad := fun x ↦ c * u.grad x
  val_memLp := u.val_memLp.const_mul c
  grad_memLp := u.grad_memLp.const_mul c
  weak_derivative := by
    intro φ hφ hφc
    simp only [mul_assoc, integral_const_mul, u.weak_derivative φ hφ hφc, mul_neg]

end SharpLiebThirring

namespace SharpLiebThirring.ExtremizerProof
open MeasureTheory

def normalizedBoundState (r : ℝ) (hr : 0 < r) : H1 :=
  scaleH1 (((Real.sqrt (∫ x : ℝ, profile r x ^ 2))⁻¹ : ℝ) : ℂ) (boundState r hr)

end SharpLiebThirring.ExtremizerProof

end
end
end

end OAI
end

section
-- module Solutions.OAIQW_LiebThirring.CubeFlags
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u37 u38

/-! Equivariant cubical barycentric flags. A codimension-one face of a full
flag has one canonical neighboring flag; this avoids any orientation choices. -/
noncomputable section
open Finset
namespace SharpLiebThirring.CubeFlags

/-- A maximal flag in the barycentric subdivision of an integer cube. -/
@[ext] structure Flag (n : ℕ) where
  base : Fin n → ℤ
  corner : Fin n → Bool
  order : Equiv.Perm (Fin n)

/-- Twice the barycenter of the `k`th cubical face in a maximal flag. -/
def Flag.vertex {n : ℕ} (F : Flag n) (k : Fin (n + 1)) (i : Fin n) : ℤ :=
  2 * F.base i + if (F.order.symm i).val < k.val then 1 else if F.corner i then 2 else 0

/-- The real vertex obtained by rescaling the half-integer grid. -/
def Flag.point {n : ℕ} (F : Flag n) (k : Fin (n + 1)) : Fin n → ℝ :=
  fun i ↦ (F.vertex k i : ℝ) / 2

/-- Toggle the endpoint chosen in coordinate `i`. -/
def Flag.flip {n : ℕ} (F : Flag n) (i : Fin n) : Flag n :=
  { F with corner := Function.update F.corner i (!(F.corner i)) }

@[simp] lemma Flag.flip_base {n : ℕ} (F : Flag n) (i : Fin n) : (F.flip i).base = F.base := rfl
@[simp] lemma Flag.flip_order {n : ℕ} (F : Flag n) (i : Fin n) : (F.flip i).order = F.order := rfl

/-- Across the final facet, pass to the neighboring cube and toggle its endpoint. -/
def Flag.cross {n : ℕ} (F : Flag n) (i : Fin n) : Flag n :=
  { F.flip i with base := Function.update F.base i (F.base i + if F.corner i then 1 else -1) }

@[simp] lemma Flag.cross_order {n : ℕ} (F : Flag n) (i : Fin n) : (F.cross i).order = F.order := rfl

/-- Swap the order of two successive face expansions. -/
def Flag.swap {n : ℕ} (F : Flag n) (i j : Fin n) : Flag n :=
  { F with order := (Equiv.swap i j).trans F.order }

/-- The other maximal flag sharing the facet obtained by deleting vertex `j`. -/
def Flag.neighbor {n : ℕ} [NeZero n] (F : Flag n) (j : Fin (n + 1)) : Flag n :=
  if h₀ : j.val = 0 then F.flip (F.order ⟨0, NeZero.pos n⟩)
  else if hₙ : j.val = n then F.cross (F.order ⟨n - 1, by omega⟩)
  else F.swap ⟨j.val - 1, by omega⟩ ⟨j.val, by omega⟩

def Flag.step {n : ℕ} (F : Flag n) (i : Fin n) : ℝ :=
  if F.corner (F.order i) then -1 / 2 else 1 / 2

/-- Coordinate reflections preserve the entire flag subdivision. -/
def Flag.reflect {n : ℕ} (s : Fin n → Bool) (F : Flag n) : Flag n where
  base i := if s i then -F.base i - 1 else F.base i
  corner i := xor (s i) (F.corner i)
  order := F.order

lemma Flag.reflect_false {n : ℕ} (F : Flag n) : F.reflect (fun _ ↦ false) = F := by
  ext i <;> simp [reflect]

lemma Flag.reflect_reflect {n : ℕ} (s t : Fin n → Bool) (F : Flag n) :
    (F.reflect t).reflect s = F.reflect (fun i ↦ xor (s i) (t i)) := by
  ext i <;> simp only [reflect]
  · rcases Bool.eq_false_or_eq_true (s i) with hs | hs <;>
      rcases Bool.eq_false_or_eq_true (t i) with ht | ht <;> simp [hs, ht]
  · exact (Bool.xor_assoc _ _ _).symm

lemma Flag.reflect_vertex {n : ℕ} (s : Fin n → Bool) (F : Flag n)
    (k : Fin (n + 1)) (i : Fin n) :
    (F.reflect s).vertex k i = if s i then -F.vertex k i else F.vertex k i := by
  simp only [vertex, reflect]
  rcases Bool.eq_false_or_eq_true (s i) with hs | hs <;>
    rcases Bool.eq_false_or_eq_true (F.corner i) with hc | hc <;>
    simp [hs, hc] <;> split_ifs <;> omega

/-- Coordinate reflections form an elementary two-group. -/
@[ext] structure Signs (n : ℕ) where
  val : Fin n → Bool

def Signs.equiv (n : ℕ) : Signs n ≃ (Fin n → Bool) where
  toFun := Signs.val
  invFun := Signs.mk
  left_inv _ := rfl
  right_inv _ := rfl

instance instFintypeSigns {n : ℕ} : Fintype (Signs n) := Fintype.ofEquiv _ (Signs.equiv n).symm
instance instDecidableEqSigns {n : ℕ} : DecidableEq (Signs n) := Classical.decEq _

instance instCommGroupSigns {n : ℕ} : CommGroup (Signs n) where
  mul s t := ⟨fun i ↦ xor (s.val i) (t.val i)⟩
  one := ⟨fun _ ↦ false⟩
  inv s := s
  mul_assoc s t u := by ext i; exact Bool.xor_assoc _ _ _
  one_mul s := by ext i; exact Bool.false_xor _
  mul_one s := by ext i; exact Bool.xor_false _
  inv_mul_cancel s := by ext i; exact Bool.xor_self _
  mul_comm s t := by ext i; exact Bool.xor_comm _ _

@[simp] lemma Signs.mul_val {n : ℕ} (s t : Signs n) (i : Fin n) :
    (s * t).val i = xor (s.val i) (t.val i) := rfl
@[simp] lemma Signs.one_val {n : ℕ} (i : Fin n) : (1 : Signs n).val i = false := rfl
@[simp] lemma Signs.inv_eq {n : ℕ} (s : Signs n) : s⁻¹ = s := rfl

instance instMulActionSignsFlag {n : ℕ} : MulAction (Signs n) (Flag n) where
  smul s F := F.reflect s.val
  one_smul := Flag.reflect_false
  mul_smul s t F := (F.reflect_reflect s.val t.val).symm

instance instIsCancelSMulSignsFlag {n : ℕ} : IsCancelSMul (Signs n) (Flag n) where
  right_cancel' s t F he := by
    ext i
    have hb := congrArg (fun G : Flag n ↦ G.base i) he
    change (if s.val i then -F.base i - 1 else F.base i) =
      (if t.val i then -F.base i - 1 else F.base i) at hb
    rcases Bool.eq_false_or_eq_true (s.val i) with hs | hs <;>
      rcases Bool.eq_false_or_eq_true (t.val i) with ht | ht <;>
      simp_all <;> omega

/-- Distance, with the corner sign, from the chosen endpoint of a coordinate. -/
def Flag.depth {n : ℕ} (F : Flag n) (i : Fin n) (x : Fin n → ℝ) : ℝ :=
  if F.corner i then (F.base i : ℝ) + 1 - x i else x i - F.base i

end SharpLiebThirring.CubeFlags

end

end OAI
end

section
-- module Solutions.OAIQW_LiebThirring.FlagGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u39

noncomputable section
open Finset


namespace SharpLiebThirring.CubeFlags

/-- Coordinate reflection as an isometric linear equivalence in the sup norm. -/
def Signs.linearIsometry {n : ℕ} (s : Signs n) :
    (Fin n → ℝ) ≃ₗᵢ[ℝ] (Fin n → ℝ) where
  toFun x i := if s.val i then -x i else x i
  invFun x i := if s.val i then -x i else x i
  left_inv x := by
    funext i
    rcases Bool.eq_false_or_eq_true (s.val i) with hs | hs <;> simp [hs]
  right_inv x := by
    funext i
    rcases Bool.eq_false_or_eq_true (s.val i) with hs | hs <;> simp [hs]
  map_add' x y := by
    funext i
    rcases Bool.eq_false_or_eq_true (s.val i) with hs | hs <;> simp [hs, add_comm]
  map_smul' a x := by
    funext i
    rcases Bool.eq_false_or_eq_true (s.val i) with hs | hs <;> simp [hs]
  norm_map' x := by
    simp only [Pi.norm_def]
    congr 1
    apply Finset.sup_congr rfl
    intro i _
    change ‖(if s.val i then -x i else x i)‖₊ = ‖x i‖₊
    rcases Bool.eq_false_or_eq_true (s.val i) with hs | hs <;> simp [hs]

instance instMulActionSignsForallFinReal {n : ℕ} : MulAction (Signs n) (Fin n → ℝ) where
  smul s x := s.linearIsometry x
  one_smul x := by
    ext i
    change (if (1 : Signs n).val i then -x i else x i) = x i
    simp
  mul_smul s t x := by
    ext i
    change (if (s * t).val i then -x i else x i) =
      if s.val i then -(if t.val i then -x i else x i) else (if t.val i then -x i else x i)
    simp only [Signs.mul_val]
    rcases Bool.eq_false_or_eq_true (s.val i) with hs | hs <;>
      rcases Bool.eq_false_or_eq_true (t.val i) with ht | ht <;> simp [hs, ht]

instance instIsIsometricSMulSignsForallFinReal {n : ℕ} : IsIsometricSMul (Signs n) (Fin n → ℝ) where
  isometry_smul s := s.linearIsometry.isometry

instance instMulActionSignsForallFinInt {n : ℕ} : MulAction (Signs n) (Fin n → ℤ) where
  smul s x i := if s.val i then -x i else x i
  one_smul x := by
    ext i
    change (if (1 : Signs n).val i then -x i else x i) = x i
    simp
  mul_smul s t x := by
    ext i
    change (if (s * t).val i then -x i else x i) =
      if s.val i then -(if t.val i then -x i else x i) else (if t.val i then -x i else x i)
    simp only [Signs.mul_val]
    rcases Bool.eq_false_or_eq_true (s.val i) with hs | hs <;>
      rcases Bool.eq_false_or_eq_true (t.val i) with ht | ht <;> simp [hs, ht]

lemma Flag.vertex_smul {n : ℕ} (s : Signs n) (F : Flag n) (k : Fin (n + 1)) :
    (s • F).vertex k = s • F.vertex k := by
  ext i
  exact F.reflect_vertex s.val k i

/-- The common final vertex is the cube center. -/
def Flag.center {n : ℕ} (F : Flag n) : Fin n → ℝ := F.point (Fin.last n)

@[simp] lemma Flag.center_apply {n : ℕ} (F : Flag n) (i : Fin n) :
    F.center i = (F.base i : ℝ) + 1 / 2 := by
  simp only [center, point, vertex, Fin.val_last, (F.order.symm i).isLt, ↓reduceIte]
  push_cast
  ring

/-- The spatially truncated cylinder of cubical flags used in continuation. -/
def nearCylinder {n : ℕ} (K : Set (Fin n → ℝ)) (h r : ℝ) (t : Fin n) (m : ℕ) : Set (Flag n) :=
  {F | (∃ x ∈ K, dist (h • F.center) x < r) ∧ 0 ≤ F.base t ∧ F.base t < (m : ℤ)}

end SharpLiebThirring.CubeFlags

namespace SharpLiebThirring.CubeFlags

/-- Embed the twice-barycenter lattice at mesh size `h`. -/
def gridPoint {n : ℕ} (h : ℝ) (z : Fin n → ℤ) : Fin n → ℝ :=
  fun i ↦ h * (z i : ℝ) / 2

section VertexComplex
variable {n : ℕ} (H : Subgroup (Signs n)) (D : SubMulAction H (Flag n))

/-- All vertices of a group-invariant collection of cubical flags. -/
def vertices : SubMulAction H (Fin n → ℤ) where
  carrier := {z | ∃ F : D, ∃ k, F.val.vertex k = z}
  smul_mem' s z hz := by
    obtain ⟨F, k, rfl⟩ := hz
    refine ⟨s • F, k, ?_⟩
    exact F.val.vertex_smul s.val k

instance verticesFintype [Fintype D] : Fintype (vertices H D) := by
  have hfin : Set.Finite (vertices H D : Set (Fin n → ℤ)) := by
    have he : (vertices H D : Set (Fin n → ℤ)) = Set.range
        (fun p : D × Fin (n + 1) ↦ p.1.val.vertex p.2) := by
      ext z
      constructor
      · rintro ⟨F, k, rfl⟩
        exact ⟨(F, k), rfl⟩
      · rintro ⟨⟨F, k⟩, rfl⟩
        exact ⟨F, k, rfl⟩
    rw [he]
    exact Set.finite_range _
  exact hfin.fintype

def flagVertex (F : D) (k : Fin (n + 1)) : vertices H D := ⟨F.val.vertex k, F, k, rfl⟩

end VertexComplex
end SharpLiebThirring.CubeFlags

end

end OAI
end

section
-- module Solutions.OAIQW_LiebThirring.FiniteParity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u40 u41 u42 u43 u44 u45 u46 u47 u48 u49 u50 u51 u52 u53 u54 u55 u56 u57 u58 u59 u60 u61 u62 u63 u64 u65 u66 u67

noncomputable section
open Finset


/-! Finite parity for the PL continuation argument.
The argument constructs continuation without assuming a topological degree theorem. -/
noncomputable section
open Finset
namespace SharpLiebThirring.PLParity


section AffineFiber
attribute [local instance] Classical.propDecidable
variable {ι : Type u42} {V : Type u43} [Fintype ι]
  [AddCommGroup V] [Module ℝ V]

/-- Total affine weights and their vector sum. -/
def augmentedMap (v : ι → V) : (ι → ℝ) →ₗ[ℝ] ℝ × V where
  toFun w := (∑ i, w i, ∑ i, w i • v i)
  map_add' a b := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c a := by simp [Finset.mul_sum, Finset.smul_sum, smul_smul]

@[simp] lemma augmentedMap_apply (v : ι → V) (w : ι → ℝ) :
    augmentedMap v w = (∑ i, w i, ∑ i, w i • v i) := rfl

/-- A facet is selected when its affine image contains zero. -/
def facetHit (v : ι → V) (i : ι) : Prop :=
  ∃ w : ι → ℝ, augmentedMap v w = (1, 0) ∧ w i = 0 ∧ ∀ j, 0 ≤ w j

lemma facetHit_linearEquiv (v : ι → V) (A : V ≃ₗ[ℝ] V) (i : ι) :
    facetHit (fun j ↦ A (v j)) i ↔ facetHit v i := by
  constructor <;> rintro ⟨w, hw, hi, hn⟩ <;> refine ⟨w, ?_, hi, hn⟩
  · apply Prod.ext
    · simpa only [augmentedMap_apply] using congrArg Prod.fst hw
    · change ∑ j, w j • v j = 0
      apply A.injective
      simpa only [augmentedMap_apply, map_sum, map_smul, map_zero] using congrArg Prod.snd hw
  · apply Prod.ext
    · simpa only [augmentedMap_apply] using congrArg Prod.fst hw
    · change ∑ j, w j • A (v j) = 0
      have hh := congrArg A (congrArg Prod.snd hw)
      simpa only [augmentedMap_apply, map_sum, map_smul, map_zero] using hh

end AffineFiber
end SharpLiebThirring.PLParity


/-! Free-action double counting for continuation modulo two. -/
noncomputable section
open Finset
namespace SharpLiebThirring.PLParity
attribute [local instance] Classical.propDecidable

section OrbitSum
variable {G : Type u45} {X : Type u46} [Group G] [MulAction G X] [IsCancelSMul G X]

omit [IsCancelSMul G X] in
lemma orbit_mk_smul (g : G) (x : X) :
    (Quotient.mk'' (g • x) : Quotient (MulAction.orbitRel G X)) = Quotient.mk'' x :=
  Quotient.sound' (MulAction.orbitRel_apply.mpr (MulAction.mem_orbit_iff.mpr ⟨g, rfl⟩))

/-- Reconstruct a point in a free orbit from its representative and a group element. -/
def orbitProductEquiv : (Quotient (MulAction.orbitRel G X) × G) ≃ X :=
  Equiv.ofBijective (fun z ↦ z.2 • z.1.out) (by
    constructor
    · rintro ⟨q, g⟩ ⟨r, h⟩ he
      have hq : q = r := by
        have hh := congrArg (fun x : X ↦ (Quotient.mk'' x : Quotient (MulAction.orbitRel G X))) he
        simpa only [orbit_mk_smul, Quotient.out_eq'] using hh
      subst r
      have hg : g = h := IsCancelSMul.right_cancel g h q.out he
      subst h
      rfl
    · intro x
      let q : Quotient (MulAction.orbitRel G X) := Quotient.mk'' x
      have hr : (MulAction.orbitRel G X) x q.out :=
        Quotient.exact' (by rw [Quotient.out_eq'])
      obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp hr)
      exact ⟨(q, g), hg⟩)

end OrbitSum

section Incidence
variable {G : Type u47} {T : Type u48} {F : Type u49} [Group G] [Fintype G] [Fintype T] [Fintype F]
  [MulAction G T] [MulAction G F] [IsCancelSMul G T] [IsCancelSMul G F]

def rowDegree (R : T → F → Prop) (t : T) : ℕ := Fintype.card {f // R t f}
def colDegree (R : T → F → Prop) (f : F) : ℕ := Fintype.card {t // R t f}

end Incidence
section HalfEdges
variable {G : Type u50} {T : Type u51} {H : Type u52} [Group G] [Fintype G] [Fintype T] [Fintype H]
  [MulAction G T] [MulAction G H] [IsCancelSMul G T] [IsCancelSMul G H]

omit [Fintype G] [Fintype T] [Fintype H] [MulAction G T]
  [IsCancelSMul G T] [IsCancelSMul G H] in
lemma orbit_map_respects (f : H → H) (hf : ∀ g : G, ∀ h, f (g • h) = g • f h)
    {a b : H} (hab : (MulAction.orbitRel G H) a b) :
    (MulAction.orbitRel G H) (f a) (f b) := by
  obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp hab)
  apply MulAction.orbitRel_apply.mpr
  apply MulAction.mem_orbit_iff.mpr
  refine ⟨g, ?_⟩
  rw [← hf, hg]

/-- An equivariant involution descends to orbit classes. -/
def orbitMap (f : H → H) (hf : ∀ g : G, ∀ h, f (g • h) = g • f h) :
    Quotient (MulAction.orbitRel G H) → Quotient (MulAction.orbitRel G H) :=
  Quotient.map f (by intro a b hab; exact orbit_map_respects f hf hab)


end HalfEdges
end SharpLiebThirring.PLParity

namespace SharpLiebThirring.PLParity
namespace FinitePairing
attribute [local instance] Classical.propDecidable

@[ext] structure CellFacet (X : Type u54) (J : Type u55) where
  cell : X
  facet : J

instance instFintypeCellFacet {X : Type u56} {J : Type u57} [Fintype X] [Fintype J] : Fintype (CellFacet X J) :=
  Fintype.ofEquiv (X × J) ⟨fun p ↦ ⟨p.1, p.2⟩, fun p ↦ (p.cell, p.facet),
    fun _ ↦ rfl, fun _ ↦ rfl⟩

instance instMulActionCellFacet {G : Type u58} {X : Type u59} {J : Type u60} [Group G] [MulAction G X] : MulAction G (CellFacet X J) where
  smul g p := ⟨g • p.cell, p.facet⟩
  one_smul p := by
    apply CellFacet.ext
    · exact one_smul _ _
    · rfl
  mul_smul g h p := by
    apply CellFacet.ext
    · exact mul_smul g h p.cell
    · rfl

instance instIsCancelSMulCellFacet {G : Type u61} {X : Type u62} {J : Type u63} [Group G] [MulAction G X] [IsCancelSMul G X] :
    IsCancelSMul G (CellFacet X J) where
  right_cancel' g h p he := IsCancelSMul.right_cancel g h p.cell
    (congrArg CellFacet.cell he)

variable {G : Type u64} {X : Type u65} {J : Type u66} [Group G] [MulAction G X]
variable (D : SubMulAction G X)
variable (hit : X → J → Prop) (hHit : ∀ g : G, ∀ x j, hit (g • x) j ↔ hit x j)
variable (nbr : X → J → X)
variable (hInv : ∀ x j, nbr (nbr x j) j = x)
variable (hNbr : ∀ g : G, ∀ x j, nbr (g • x) j = g • nbr x j)
variable (hAdj : ∀ x j, hit x j → hit (nbr x j) j)

/-- Selected simplex-facet incidences in a finite invariant domain. -/
def selected : SubMulAction G (CellFacet D J) where
  carrier := {p | hit p.cell.val p.facet}
  smul_mem' g p hp := (hHit g p.cell.val p.facet).mpr hp

instance selectedFintype [Fintype D] [Fintype J] : Fintype (selected D hit hHit) :=
  Fintype.ofFinite _

/-- Pair an interior selected facet with its neighbor, and keep boundary facets fixed. -/
def pairing (p : selected D hit hHit) : selected D hit hHit :=
  if hn : nbr p.val.cell.val p.val.facet ∈ D then
    ⟨⟨⟨nbr p.val.cell.val p.val.facet, hn⟩, p.val.facet⟩,
      hAdj p.val.cell.val p.val.facet p.property⟩
  else p

end FinitePairing
end SharpLiebThirring.PLParity

namespace SharpLiebThirring.CubeFlags
open SharpLiebThirring.PLParity
section PLComplex
variable {n : ℕ} [NeZero n] (H : Subgroup (Signs n)) (D : SubMulAction H (Flag n))
variable {V : Type u67} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
variable (ρ : H →* (V ≃ₗ[ℝ] V))
attribute [local instance] Classical.propDecidable

/-- Extend finite equivariant vertex data by zero outside the invariant complex. -/
def extendValues (a : vertices H D → V) (z : Fin n → ℤ) : V :=
  if hz : z ∈ vertices H D then a ⟨z, hz⟩ else 0

omit [NeZero n] [FiniteDimensional ℝ V] in
lemma extendValues_equivariant (a : vertices H D → V)
    (ha : ∀ s : H, ∀ z, a (s • z) = ρ s (a z)) (s : H) (z : Fin n → ℤ) :
    extendValues H D a (s • z) = ρ s (extendValues H D a z) := by
  by_cases hz : z ∈ vertices H D
  · have hsz : s • z ∈ vertices H D := (vertices H D).smul_mem s hz
    simp only [extendValues, dite_eq_left hz, dite_eq_left hsz]
    exact ha s ⟨z, hz⟩
  · have hsz : s • z ∉ vertices H D := fun h ↦ hz (((vertices H D).smul_mem_iff' s).mp h)
    simp only [extendValues, dite_eq_right hz, dite_eq_right hsz, map_zero]

def cellHit (a : vertices H D → V) (F : Flag n) (j : Fin (n + 1)) : Prop :=
  facetHit (fun k ↦ extendValues H D a (F.vertex k)) j

omit [NeZero n] [FiniteDimensional ℝ V] in
lemma cellHit_equivariant (a : vertices H D → V)
    (ha : ∀ s : H, ∀ z, a (s • z) = ρ s (a z)) (s : H) (F : Flag n) (j : Fin (n + 1)) :
    cellHit H D a (s • F) j ↔ cellHit H D a F j := by
  unfold cellHit
  have he (k : Fin (n + 1)) : extendValues H D a ((s • F).vertex k) =
      ρ s (extendValues H D a (F.vertex k)) := by
    rw [show (s • F).vertex k = s • F.vertex k from F.vertex_smul s.val k]
    exact extendValues_equivariant H D ρ a ha s _
  simp only [he]
  exact facetHit_linearEquiv _ (ρ s) _

end PLComplex
end SharpLiebThirring.CubeFlags

end
end
end

end OAI
end

section
-- module Solutions.OAIQW_LiebThirring.GenericPosition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u68 u69 u70 u71 u72 u73 u74 u75 u76 u77 u78 u79 u80 u81 u82 u83 u84 u85 u86 u87 u88 u89 u90 u91 u92 u93 u94 u191 u192

noncomputable section
open Finset
noncomputable section
open Finset
noncomputable section
open Finset


section


/-! Generic vertex positions for the piecewise-linear continuation argument. -/

open Set Finset Filter
namespace SharpLiebThirring.PLParity

variable {V : Type u68} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- Put a new extension vector before the previous extension vectors. -/
def sumFinSuccEmbedding (ι : Type u70) (n : ℕ) :
    ι ⊕ Fin (n + 1) ↪ Option (ι ⊕ Fin n) where
  toFun := Sum.elim (fun i ↦ some (Sum.inl i))
    (Fin.cases none (fun j ↦ some (Sum.inr j)))
  inj' := by
    intro i j
    rcases i with i | i <;> rcases j with j | j
    · simp
    · refine Fin.cases ?_ (fun j ↦ ?_) j <;> simp
    · refine Fin.cases ?_ (fun i ↦ ?_) i <;> simp
    · refine Fin.cases ?_ (fun i ↦ ?_) i <;>
        refine Fin.cases ?_ (fun j ↦ ?_) j <;> simp

section VertexEvaluation
variable {Q : Type u83} {ι : Type u84} [Fintype Q] [Fintype ι]

/-- On distinct vertex orbits, equivariant vertex values may be varied independently. -/
def vertexEvaluation (e : ι → Q) (A : ι → V ≃ₗ[ℝ] V) :
    (Q → V) →ₗ[ℝ] (ι → V) where
  toFun w i := A i (w (e i))
  map_add' w z := by ext i; simp
  map_smul' c w := by ext i; simp

attribute [local instance] Classical.propDecidable

/-- Extend vertex values on the free orbits while retaining the prescribed orbits. -/
def mixedVertexEvaluation (P : Q → Prop) (b : Q → V) (e : ι → Q)
    (A : ι → V ≃ₗ[ℝ] V) (a : {q // ¬ P q} → V) (i : ι) : V :=
  A i (if h : P (e i) then b (e i) else a ⟨e i, h⟩)

end VertexEvaluation

end SharpLiebThirring.PLParity

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQW_LiebThirring.EquivariantFlags
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u95 u96 u97 u98 u99 u100 u101 u102 u193 u194

noncomputable section
open Finset
noncomputable section
open Finset
noncomputable section
open Finset
section
open Set Finset Filter


namespace SharpLiebThirring.PLParity
section EquivariantAssignment
variable {G : Type u95} {X : Type u96} [Group G] [MulAction G X] [IsCancelSMul G X]

abbrev Orbit := Quotient (MulAction.orbitRel G X)

omit [IsCancelSMul G X] in
lemma assignment_orbit_smul (g : G) (x : X) :
    (Quotient.mk'' (g • x) : Orbit (G := G) (X := X)) = Quotient.mk'' x :=
  Quotient.sound' (MulAction.orbitRel_apply.mpr (MulAction.mem_orbit_iff.mpr ⟨g, rfl⟩))

def assignmentEquiv : (Orbit (G := G) (X := X) × G) ≃ X :=
  Equiv.ofBijective (fun z ↦ z.2 • z.1.out) (by
    constructor
    · rintro ⟨q, g⟩ ⟨r, h⟩ he
      have hq : q = r := by
        have hh := congrArg (fun x : X ↦ (Quotient.mk'' x : Orbit (G := G) (X := X))) he
        simpa only [assignment_orbit_smul, Quotient.out_eq'] using hh
      subst r
      have hg : g = h := IsCancelSMul.right_cancel g h q.out he
      subst h
      rfl
    · intro x
      let q : Orbit (G := G) (X := X) := Quotient.mk'' x
      have hr : (MulAction.orbitRel G X) x q.out :=
        Quotient.exact' (by rw [Quotient.out_eq'])
      obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp hr)
      exact ⟨(q, g), hg⟩)

def orbitLabel (x : X) : Orbit (G := G) (X := X) := assignmentEquiv.symm x |>.1
def orbitTransport (x : X) : G := assignmentEquiv.symm x |>.2

variable {V : Type u97} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
variable (ρ : G →* (V ≃ₗ[ℝ] V))

def equivariantAssignment (a : Orbit (G := G) (X := X) → V) (x : X) : V :=
  ρ (orbitTransport x) (a (orbitLabel x))

end EquivariantAssignment
end SharpLiebThirring.PLParity


namespace SharpLiebThirring.CubeFlags
open Finset

def spatial {d : ℕ} : (Fin (d + 1) → ℝ) →ₗ[ℝ] (Fin d → ℝ) where
  toFun := Fin.init
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def embedSpatial {d : ℕ} : (Fin d → ℝ) →ₗ[ℝ] (Fin (d + 1) → ℝ) where
  toFun x := Fin.snoc x 0
  map_add' x y := by ext i; refine Fin.lastCases ?_ (fun j ↦ ?_) i <;> simp
  map_smul' a x := by ext i; refine Fin.lastCases ?_ (fun j ↦ ?_) i <;> simp

@[simp] lemma spatial_embed {d : ℕ} (x : Fin d → ℝ) : spatial (embedSpatial x) = x := by
  ext i
  change (Fin.snoc (α := fun _ : Fin (d + 1) ↦ ℝ) x 0) i.castSucc = x i
  simp only [Fin.snoc_castSucc]

/-- A bottom flag with its cube chosen within one mesh of any given spatial point. -/
def bottomSeed {d : ℕ} (h : ℝ) (p : Fin d → ℝ) : Flag (d + 1) where
  base := Fin.snoc (fun i ↦ ⌊p i / h⌋) 0
  corner := fun _ ↦ false
  order := Equiv.refl _

end SharpLiebThirring.CubeFlags

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQW_LiebThirring.InitialOrbit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u103 u104 u105 u106 u107 u108 u109 u110 u111 u112 u113 u114 u115

noncomputable section
open Finset
noncomputable section
open Finset
noncomputable section
open Finset
section
open Set Finset Filter


/-! Disjoint equivariant coordinate balls for the unique initial zero orbit. -/

open Set Finset
namespace SharpLiebThirring.PLParity
section OrbitBalls
attribute [local instance] Classical.propDecidable
variable {G : Type u103} {E : Type u104} [Group G] [MetricSpace E] [MulAction G E]
  [IsIsometricSMul G E]

variable (p : E) (R : ℝ)

def orbitBall : Set E := {x | ∃ g : G, dist x (g • p) < R}

noncomputable def ballLabel (x : E) : G :=
  if hx : x ∈ orbitBall (G := G) p R then hx.choose else 1

end OrbitBalls
end SharpLiebThirring.PLParity

namespace SharpLiebThirring.CubeFlags
open Finset SharpLiebThirring.PLParity

instance signsSubgroupIsIsometric {n : ℕ} (H : Subgroup (Signs n)) :
    IsIsometricSMul H (Fin n → ℝ) where
  isometry_smul s := s.val.linearIsometry.isometry

section Model
variable {d : ℕ} (H : Subgroup (Signs (d + 1)))
variable {V : Type u110} [NormedAddCommGroup V] [NormedSpace ℝ V]
variable (ρ : H →* (V ≃ₗ[ℝ] V)) (L : (Fin d → ℝ) ≃ₗ[ℝ] V)
variable (p : Fin (d + 1) → ℝ) (R : ℝ)

def affineOrbitModel (q : Fin d → ℝ) (x : Fin (d + 1) → ℝ) : V :=
  let s := ballLabel (G := H) p R x
  ρ s (L (spatial (s⁻¹ • x) - q))

end Model
end SharpLiebThirring.CubeFlags

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQW_LiebThirring.FreeLocus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u116 u117 u118 u119 u120 u121 u122 u123 u124 u125 u126 u127 u128 u129 u130 u131 u132 u133 u134 u135

noncomputable section
open Finset
noncomputable section
open Finset
noncomputable section
open Finset

section


/-! Analytic compactness and free-locus facts for the PL continuation proof. -/

open Set Finset
namespace SharpLiebThirring.PLParity

section FreeLocus
variable {G : Type u120} {E : Type u121} [Group G] [MulAction G E]

def freeLocus : Set E := {x | ∀ g : G, g • x = x → g = 1}

end FreeLocus
end SharpLiebThirring.PLParity

namespace SharpLiebThirring.CubeFlags
open Finset SharpLiebThirring.PLParity

def Flag.combination {n : ℕ} (h : ℝ) (F : Flag n) (w : Fin (n + 1) → ℝ) : Fin n → ℝ :=
  h • ∑ k, w k • F.point k

end SharpLiebThirring.CubeFlags
end

end
end
end

end OAI
end

section
-- module Solutions.OAIQW_LiebThirring.Continuation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u143 u144 u145 u146 u147

noncomputable section
open Finset
noncomputable section
open Finset
noncomputable section
open Finset


namespace SharpLiebThirring.CubeFlags
open Finset SharpLiebThirring.PLParity

/-- A continuous cutoff equal to one on the inner half ball. -/
def radialCut (R t : ℝ) : ℝ := max 0 (min 1 (2 - 2*t/R))

section Flatten
variable {d : ℕ} (H : Subgroup (Signs (d + 1)))
variable {V : Type u143} [NormedAddCommGroup V] [NormedSpace ℝ V]
variable (ρ : H →* (V ≃ₗ[ℝ] V)) (L : (Fin d → ℝ) ≃ₗ[ℝ] V)
variable (p : Fin d → ℝ) (R : ℝ) (f : (Fin (d + 1) → ℝ) → V)

def localAffine (s : H) (x : Fin (d + 1) → ℝ) : V :=
  ρ s (L (spatial (s⁻¹ • x) - p))

def flattenTerm (s : H) (x : Fin (d + 1) → ℝ) : V :=
  radialCut R (dist x (s • embedSpatial p)) • (localAffine H ρ L p s x - f x)

def flattenInitial (x : Fin (d + 1) → ℝ) : V := by
  classical
  exact f x + ∑ s : H, flattenTerm H ρ L p R f s x

end Flatten
end SharpLiebThirring.CubeFlags

end
end
end

end OAI
end

section
-- module Solutions.OAIQW_LiebThirring.RowSigns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Finset
noncomputable section
open Finset
noncomputable section
open Finset

namespace SharpLiebThirring.ContinuationGap
open Matrix Set

abbrev LowerSpace (N : ℕ) :=
  {C : Matrix (Fin N) (Fin N) ℝ // ∀ i j, i < j → C i j = 0}

def rowSign {N : ℕ} (s : Fin N → ℝ) (C : LowerSpace N) : LowerSpace N :=
  ⟨fun i j ↦ s i * C.val i j, by
    intro i j hij
    change s i * C.val i j = 0
    rw [C.prop i j hij, mul_zero]⟩

def signConjugate {N : ℕ} (s : Fin N → ℝ) (Z : Matrix (Fin N) (Fin N) ℝ) :
    Matrix (Fin N) (Fin N) ℝ := fun i j ↦ s i * Z i j * s j

def NonzeroRows {N : ℕ} (C : LowerSpace N) : Prop := ∀ i, ∃ j, C.val i j ≠ 0

end SharpLiebThirring.ContinuationGap
namespace SharpLiebThirring.PathTopology
open Matrix SharpLiebThirring.CubeFlags SharpLiebThirring.ContinuationGap

abbrev LowerIndex (N : ℕ) := {a : Fin N × Fin N // a.2 ≤ a.1}
abbrev lowerDim (N : ℕ) := Fintype.card (LowerIndex N)
noncomputable def indexEquiv (N : ℕ) : LowerIndex N ≃ Fin (lowerDim N) := Fintype.equivFin _

def diagonalIndex {N : ℕ} (i : Fin N) : Fin (lowerDim N) := indexEquiv N ⟨(i,i),le_refl _⟩
def rowIndex {N : ℕ} (a : Fin (lowerDim N)) : Fin N := ((indexEquiv N).symm a).val.1
def colIndex {N : ℕ} (a : Fin (lowerDim N)) : Fin N := ((indexEquiv N).symm a).val.2

@[simp] lemma rowIndex_diagonal {N : ℕ} (i : Fin N) : rowIndex (diagonalIndex i) = i := by
  simp [rowIndex,diagonalIndex]
@[simp] lemma colIndex_diagonal {N : ℕ} (i : Fin N) : colIndex (diagonalIndex i) = i := by
  simp [colIndex,diagonalIndex]
lemma colIndex_le_rowIndex {N : ℕ} (a : Fin (lowerDim N)) : colIndex a ≤ rowIndex a :=
  ((indexEquiv N).symm a).prop

/-- Exact linear coordinates on the entire lower-triangular coefficient space;
no nonvanishing or invertibility restriction is imposed. -/
def lowerOfCoords {N : ℕ} (x : Fin (lowerDim N) → ℝ) : LowerSpace N :=
  ⟨fun i j ↦ if h : j ≤ i then x (indexEquiv N ⟨(i,j),h⟩) else 0,
    by intro i j hij; simp only [not_le.mpr hij,↓reduceDIte]⟩
def lowerCoords {N : ℕ} (C : LowerSpace N) : Fin (lowerDim N) → ℝ :=
  fun a ↦ C.val (rowIndex a) (colIndex a)

@[simp] lemma lowerCoords_lowerOfCoords {N : ℕ} (x : Fin (lowerDim N) → ℝ) :
    lowerCoords (lowerOfCoords x) = x := by
  funext a
  have he : (⟨(rowIndex a,colIndex a),colIndex_le_rowIndex a⟩ : LowerIndex N) = (indexEquiv N).symm a := rfl
  simp only [lowerCoords,lowerOfCoords,colIndex_le_rowIndex,↓reduceDIte,he,Equiv.apply_symm_apply]

@[simp] lemma lowerOfCoords_lowerCoords {N : ℕ} (C : LowerSpace N) :
    lowerOfCoords (lowerCoords C) = C := by
  apply Subtype.ext
  funext i j
  dsimp [lowerOfCoords]
  split_ifs with h
  · simp [lowerCoords,rowIndex,colIndex]
  · exact (C.prop i j (lt_of_not_ge h)).symm

lemma continuous_lowerCoords {N : ℕ} : Continuous (lowerCoords (N := N)) := by
  apply continuous_pi
  intro a
  exact (continuous_apply _).comp ((continuous_apply _).comp continuous_subtype_val)
lemma continuous_lowerOfCoords {N : ℕ} : Continuous (lowerOfCoords (N := N)) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  by_cases h : j ≤ i
  · simpa only [lowerOfCoords,h,↓reduceDIte] using (continuous_apply (indexEquiv N ⟨(i,j),h⟩))
  · simpa only [lowerOfCoords,h,↓reduceDIte] using (continuous_const : Continuous (fun _ : Fin (lowerDim N) → ℝ ↦ (0 : ℝ)))

/-- Coordinate reflections that flip whole rows and fix the homotopy time. -/
def rowSubgroup (N : ℕ) : Subgroup (Signs (lowerDim N + 1)) where
  carrier := {s | s.val (Fin.last (lowerDim N)) = false ∧
    ∀ a : Fin (lowerDim N), s.val a.castSucc = s.val (diagonalIndex (rowIndex a)).castSucc}
  one_mem' := ⟨rfl,fun _ ↦ rfl⟩
  mul_mem' hs ht := ⟨by simp only [Signs.mul_val,hs.1,ht.1,Bool.false_xor],
    fun a ↦ by simp only [Signs.mul_val,hs.2 a,ht.2 a]⟩
  inv_mem' hs := hs

def rowBool {N : ℕ} (s : rowSubgroup N) (i : Fin N) : Bool :=
  s.val.val (diagonalIndex i).castSucc

@[simp] lemma rowBool_one {N : ℕ} (i : Fin N) : rowBool (1 : rowSubgroup N) i = false := rfl
@[simp] lemma rowBool_mul {N : ℕ} (s t : rowSubgroup N) (i : Fin N) :
    rowBool (s*t) i = xor (rowBool s i) (rowBool t i) := rfl

def rowElement {N : ℕ} (s : Fin N → Bool) : rowSubgroup N :=
  ⟨⟨Fin.snoc (fun a ↦ s (rowIndex a)) false⟩,by
    constructor
    · simp only [Fin.snoc_last]
    · intro a
      simp only [Fin.snoc_castSucc,rowIndex_diagonal]⟩
@[simp] lemma rowBool_rowElement {N : ℕ} (s : Fin N → Bool) : rowBool (rowElement s) = s := by
  funext i
  simp only [rowBool,rowElement,Fin.snoc_castSucc,rowIndex_diagonal]

def signValue (b : Bool) : ℝ := if b then -1 else 1
@[simp] lemma signValue_false : signValue false = 1 := rfl
@[simp] lemma signValue_true : signValue true = -1 := rfl

def conjugateSigns {N : ℕ} (s : rowSubgroup N) : Signs (lowerDim N) :=
  ⟨fun a ↦ xor (rowBool s (rowIndex a)) (rowBool s (colIndex a))⟩

def conjugateRepresentation (N : ℕ) : rowSubgroup N →* ((Fin (lowerDim N) → ℝ) ≃ₗ[ℝ] (Fin (lowerDim N) → ℝ)) where
  toFun s := (conjugateSigns s).linearIsometry.toLinearEquiv
  map_one' := by
    ext x a
    simp only [conjugateSigns,Signs.linearIsometry,rowBool_one,Bool.false_xor,Bool.false_eq_true,↓reduceIte]
    rfl
  map_mul' s t := by
    ext x a
    change (if xor (rowBool (s*t) (rowIndex a)) (rowBool (s*t) (colIndex a)) then -x a else x a) =
      if xor (rowBool s (rowIndex a)) (rowBool s (colIndex a)) then
        -(if xor (rowBool t (rowIndex a)) (rowBool t (colIndex a)) then -x a else x a) else
        if xor (rowBool t (rowIndex a)) (rowBool t (colIndex a)) then -x a else x a
    simp only [rowBool_mul]
    rcases Bool.eq_false_or_eq_true (rowBool s (rowIndex a)) with h₁ | h₁ <;>
      rcases Bool.eq_false_or_eq_true (rowBool s (colIndex a)) with h₂ | h₂ <;>
      rcases Bool.eq_false_or_eq_true (rowBool t (rowIndex a)) with h₃ | h₃ <;>
      rcases Bool.eq_false_or_eq_true (rowBool t (colIndex a)) with h₄ | h₄ <;> simp [h₁,h₂,h₃,h₄]

end SharpLiebThirring.PathTopology
namespace SharpLiebThirring.PathTopology
open Matrix SharpLiebThirring.CubeFlags SharpLiebThirring.ContinuationGap

/-- Lower-coordinate restriction is faithful on symmetric matrices. -/
def matrixCoords {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) : Fin (lowerDim N) → ℝ :=
  fun a ↦ A (rowIndex a) (colIndex a)

def diagonalLower {N : ℕ} (c : Fin N → ℝ) : LowerSpace N :=
  ⟨diagonal c,fun _i _j hij ↦ diagonal_apply_ne c (ne_of_lt hij)⟩
def diagonalPoint {N : ℕ} (c : Fin N → ℝ) : Fin (lowerDim N) → ℝ := lowerCoords (diagonalLower c)
@[simp] lemma lowerOfCoords_diagonalPoint {N : ℕ} (c : Fin N → ℝ) :
    lowerOfCoords (diagonalPoint c) = diagonalLower c := lowerOfCoords_lowerCoords _

def lowerEntry {N : ℕ} (i j : Fin N) : (Fin (lowerDim N) → ℝ) →L[ℝ] ℝ :=
  if h : j ≤ i then ContinuousLinearMap.proj (indexEquiv N ⟨(i,j),h⟩) else 0

def initialMap {N : ℕ} (β : ℝ) (k : Fin N → ℝ) (x : Fin (lowerDim N) → ℝ) : Fin (lowerDim N) → ℝ :=
  matrixCoords (2 • diagonal k - β • ((lowerOfCoords x).val * (lowerOfCoords x).val.transpose))

def jacobianWeight {N : ℕ} (β : ℝ) (c : Fin N → ℝ) (a : Fin (lowerDim N)) : ℝ :=
  -β * (c (colIndex a) + if rowIndex a = colIndex a then c (rowIndex a) else 0)
lemma jacobianWeight_ne_zero {N : ℕ} {β : ℝ} (hβ : β ≠ 0) (c : Fin N → ℝ)
    (hc : ∀ i, 0 < c i) (a : Fin (lowerDim N)) : jacobianWeight β c a ≠ 0 := by
  unfold jacobianWeight
  apply mul_ne_zero (neg_ne_zero.mpr hβ)
  apply ne_of_gt
  split_ifs
  · exact add_pos (hc _) (hc _)
  · simpa using hc (colIndex a)

def initialLinearEquiv {N : ℕ} (β : ℝ) (hβ : β ≠ 0) (c : Fin N → ℝ) (hc : ∀ i, 0 < c i) :
    (Fin (lowerDim N) → ℝ) ≃ₗ[ℝ] (Fin (lowerDim N) → ℝ) :=
  LinearEquiv.piCongrRight (fun a ↦ LinearEquiv.smulOfNeZero ℝ ℝ (jacobianWeight β c a) (jacobianWeight_ne_zero hβ c hc a))

end SharpLiebThirring.PathTopology
namespace SharpLiebThirring.PathTopology
open Matrix SharpLiebThirring.CubeFlags SharpLiebThirring.ContinuationGap

def spaceTimeHomeomorph (N : ℕ) : (Fin (lowerDim N + 1) → ℝ) ≃ₜ (LowerSpace N × ℝ) where
  toFun x := (lowerOfCoords (spatial x),x (Fin.last (lowerDim N)))
  invFun z := Fin.snoc (lowerCoords z.1) z.2
  left_inv x := by
    simp only [lowerCoords_lowerOfCoords]
    exact Fin.snoc_init_self x
  right_inv z := by
    change (lowerOfCoords (Fin.init (Fin.snoc (α := fun _ : Fin (lowerDim N + 1) ↦ ℝ) (lowerCoords z.1) z.2)),
      Fin.snoc (α := fun _ : Fin (lowerDim N + 1) ↦ ℝ) (lowerCoords z.1) z.2 (Fin.last (lowerDim N))) = z
    simp only [Fin.init_snoc,Fin.snoc_last,lowerOfCoords_lowerCoords]
  continuous_toFun := (continuous_lowerOfCoords.comp spatial.continuous_of_finiteDimensional).prodMk (continuous_apply _)
  continuous_invFun := by
    apply continuous_pi
    intro a
    refine Fin.lastCases ?_ (fun b ↦ ?_) a
    · simpa only [Fin.snoc_last] using (continuous_snd : Continuous (fun z : LowerSpace N × ℝ ↦ z.2))
    · simpa only [Fin.snoc_castSucc,Function.comp_def] using ((continuous_apply b).comp (continuous_lowerCoords.comp continuous_fst))

def clampTime (t : ℝ) : ℝ := max 0 (min t 1)

def homotopyCoords {N : ℕ} (Φ : ℝ → LowerSpace N → Matrix (Fin N) (Fin N) ℝ)
    (x : Fin (lowerDim N + 1) → ℝ) : Fin (lowerDim N) → ℝ :=
  matrixCoords (Φ (clampTime (x (Fin.last (lowerDim N)))) (lowerOfCoords (spatial x)))

end SharpLiebThirring.PathTopology

end
end
end

end OAI
end

section
-- module Solutions.OAIQW_LiebThirring.MatrixFlow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u148 u149 u150 u151 u152 u153 u154 u155 u156 u157

noncomputable section
open Finset
noncomputable section
open Finset
noncomputable section
open Finset

noncomputable section
open Set Metric MeasureTheory Filter
open scoped Topology NNReal
noncomputable section
open Matrix Set MeasureTheory WithLp
open scoped Matrix.Norms.L2Operator Topology
namespace SharpLiebThirring.MatrixFlow
abbrev Sym (N : ℕ) := selfAdjoint (Matrix (Fin N) (Fin N) ℝ)
def symInclude {N : ℕ} : Sym N →ₗ[ℝ] Matrix (Fin N) (Fin N) ℝ where
  toFun := Subtype.val
  map_add' := fun _ _ ↦ rfl
  map_smul' := fun _ _ ↦ rfl
instance instFiniteDimensionalRealSubtypeMatrixFinMemAddSubgroupSym {N : ℕ} : FiniteDimensional ℝ (Sym N) :=
  FiniteDimensional.of_injective symInclude Subtype.val_injective

def symDiag {N : ℕ} (k : Fin N → ℝ) : Sym N := ⟨diagonal k,isHermitian_diagonal _⟩
def symOuter {N : ℕ} (a : Fin N → ℝ) : Sym N :=
  ⟨vecMulVec a a,by ext i j; simp [vecMulVec,mul_comm]⟩
@[simp] lemma symOuter_apply {N : ℕ} (a : Fin N → ℝ) (i j : Fin N) :
    (symOuter a).val i j = a i * a j := rfl

def symEntry {N : ℕ} (i j : Fin N) : Sym N →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A ↦ A.val i j
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
@[simp] lemma symEntry_apply {N : ℕ} (i j : Fin N) (A : Sym N) : symEntry i j A = A.val i j := rfl
lemma continuous_symOuter {N : ℕ} : Continuous (symOuter : (Fin N → ℝ) → Sym N) := by
  apply Continuous.subtype_mk
  change Continuous (fun a : Fin N → ℝ ↦ vecMulVec a a)
  fun_prop

def symConj {N : ℕ} (s : Fin N → ℝ) : Sym N →L[ℝ] Sym N :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A ↦ ⟨fun i j ↦ s i * A.val i j * s j,by
        ext i j
        change s j * A.val j i * s i = s i * A.val i j * s j
        have hh : A.val j i = A.val i j := congrFun (congrFun A.prop i) j
        rw [hh]; ring⟩
      map_add' := by intro A B; apply Subtype.ext; ext i j; change s i * (_ + _) * s j = _ + _; ring
      map_smul' := by intro r A; apply Subtype.ext; ext i j; change s i * (r * _) * s j = r * _; ring }
@[simp] lemma symConj_apply {N : ℕ} (s : Fin N → ℝ) (A : Sym N) (i j : Fin N) :
    (symConj s A).val i j = s i * A.val i j * s j := rfl
lemma sign_sq {N : ℕ} (s : Fin N → ℝ) (hs : ∀ i, s i = 1 ∨ s i = -1) (i : Fin N) :
    s i * s i = 1 := by rcases hs i with h|h <;> rw [h] <;> norm_num
lemma sign_diagonal_unitary {N : ℕ} (s : Fin N → ℝ) (hs : ∀ i, s i = 1 ∨ s i = -1) :
    diagonal s ∈ unitary (Matrix (Fin N) (Fin N) ℝ) := by
  rw [Unitary.mem_iff]
  have h : star (diagonal s) = diagonal s := isHermitian_diagonal s
  rw [h,diagonal_mul_diagonal]
  have hh : diagonal (fun i ↦ s i*s i) = (1 : Matrix (Fin N) (Fin N) ℝ) := by
    simp only [sign_sq s hs,diagonal_one]
  exact ⟨hh,hh⟩

end SharpLiebThirring.MatrixFlow
namespace SharpLiebThirring.MatrixFlow
open Set Matrix
open scoped Topology
variable {N : ℕ}

/-- The outer-product forcing, viewed in the supremum-norm space on the time interval. -/
def matrixForcing (ε : ℝ) {l r : ℝ} (u : ℝ → Fin N → ℝ)
    (hu : ContinuousOn u (Icc l r)) (C : Matrix (Fin N) (Fin N) ℝ) : C(Icc l r, Sym N) :=
  ⟨fun t ↦ -ε⁻¹ • symOuter (C *ᵥ u t), by
    exact (continuous_symOuter.comp (continuous_const.matrix_mulVec hu.domRestrict)).const_smul (-ε⁻¹)⟩

def flowRhs (ε : ℝ) (M : Sym N → Sym N) (u : ℝ → Fin N → ℝ)
    (p : Matrix (Fin N) (Fin N) ℝ × ℝ) (t : ℝ) (B : Sym N) : Sym N :=
  (ε⁻¹ * p.2) • M B - ε⁻¹ • symOuter (p.1 *ᵥ u t)

end SharpLiebThirring.MatrixFlow
namespace SharpLiebThirring.MatrixFlow
open Matrix Set MeasureTheory
variable {N : ℕ}

def symCongr (C : Matrix (Fin N) (Fin N) ℝ) : Sym N →L[ℝ] Sym N :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A ↦ ⟨C * A.val * C.transpose,
        by
          change (C * A.val * C.transpose).IsHermitian
          simpa only [conjTranspose_eq_transpose_of_trivial] using isHermitian_mul_mul_conjTranspose C A.prop⟩
      map_add' := by
        intro A B; apply Subtype.ext
        change C * (A.val + B.val) * C.transpose = C * A.val * C.transpose + C * B.val * C.transpose
        rw [mul_add,add_mul]
      map_smul' := by
        intro r A; apply Subtype.ext
        change C * (r • A.val) * C.transpose = r • (C * A.val * C.transpose)
        rw [Matrix.mul_smul,Matrix.smul_mul] }
@[simp] lemma symCongr_apply (C : Matrix (Fin N) (Fin N) ℝ) (A : Sym N) :
    (symCongr C A).val = C * A.val * C.transpose := rfl

end SharpLiebThirring.MatrixFlow

end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQW_LiebThirring.FieldFlow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u158 u159 u160 u161 u162 u163 u164 u165

noncomputable section
open Finset
noncomputable section
open Finset
noncomputable section
open Finset
noncomputable section
open Set Metric MeasureTheory Filter
open scoped Topology NNReal
noncomputable section
open Matrix Set MeasureTheory WithLp
open scoped Matrix.Norms.L2Operator Topology

noncomputable section
open Set Metric
open scoped NNReal
namespace SharpLiebThirring.ODEProof

/-- A radial auxiliary cutoff; its lack of smoothness is harmless because only
Lipschitz regularity is needed for the flow and barriers. -/
def radialCutoff {E : Type u158} [NormedAddCommGroup E] (R : ℝ) (x : E) : ℝ :=
  max 0 (min 1 (R+1-‖x‖))

end SharpLiebThirring.ODEProof
noncomputable section
open Matrix
open scoped Matrix.Norms.L2Operator
namespace SharpLiebThirring.MatrixFlow
open MatrixProof ScalarProof Matrix
open scoped Matrix.Norms.L2Operator Topology
variable {N : ℕ}

def sourceField (σ δ : ℝ) (hσ : σ < 1) (hδ : 0 < δ) (k : Fin N → ℝ) : Sym N → Sym N :=
  fun A ↦ ⟨matrixField σ δ k A.val,matrixField_isHermitian hσ hδ k A.prop⟩

end SharpLiebThirring.MatrixFlow
namespace SharpLiebThirring.MatrixFlow
open MatrixProof ScalarProof Matrix MeasureTheory Filter
open scoped Matrix.Norms.L2Operator Topology
variable {N : ℕ}

def complexUnitary (U : unitary (Matrix (Fin N) (Fin N) ℝ)) :
    unitary (Matrix (Fin N) (Fin N) ℂ) :=
  Unitary.map (StarMonoidHom.ofClass (complexify (n := Fin N))) U

def matrixEntry (i j : Fin N) : Matrix (Fin N) (Fin N) ℝ →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    {toFun := fun A ↦ A i j, map_add' := by intros; rfl, map_smul' := by intros; rfl}
@[simp] lemma matrixEntry_apply (i j : Fin N) (A : Matrix (Fin N) (Fin N) ℝ) : matrixEntry i j A = A i j := rfl

def scalarDiag : ℝ →L[ℝ] Sym N :=
  LinearMap.toContinuousLinearMap
    ({toFun := fun x : ℝ ↦ symDiag (fun _ ↦ x)
      map_add' := by
        intro x y
        apply Subtype.ext
        exact (diagonal_add (fun _ : Fin N ↦ x) (fun _ ↦ y)).symm
      map_smul' := by
        intro r x
        apply Subtype.ext
        exact diagonal_smul r (fun _ : Fin N ↦ x)} : ℝ →ₗ[ℝ] Sym N)

end SharpLiebThirring.MatrixFlow

end
end
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQW_LiebThirring.IntervalAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Finset
noncomputable section
open Finset
noncomputable section
open Finset
noncomputable section
open Set Metric MeasureTheory Filter
open scoped Topology NNReal
noncomputable section
open Matrix Set MeasureTheory WithLp
open scoped Matrix.Norms.L2Operator Topology
noncomputable section
open Set Metric
open scoped NNReal
noncomputable section
open Matrix
open scoped Matrix.Norms.L2Operator

namespace SharpLiebThirring.ActionProof
open Matrix MatrixProof MatrixFlow MeasureTheory Set
open scoped Matrix.Norms.L2Operator
variable {N : ℕ}

def actionDensity (σ : ℝ) (k a v : Fin N → ℝ) : ℝ :=
  (∑ i, v i^2) + (∑ i, k i^2*a i^2) - (∑ i, a i^2) ^ (1+1/σ)

end SharpLiebThirring.ActionProof

end

end

end

end

end

end

end

end OAI
end

section
-- module Solutions.OAIQW_LiebThirring.Gamma
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace SharpLiebThirring.ConstantProof
open MeasureTheory Set Filter
open scoped Topology

def betaAction (σ : ℝ) : ℝ := ∫ t in (-1 : ℝ)..1, (1-t^2)^σ

end SharpLiebThirring.ConstantProof

end

end OAI
end

section
-- module Solutions.OAIQW_LiebThirring.CutoffEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace SharpLiebThirring.SobolevProof
open MeasureTheory Set
open scoped Topology

/-- C¹ representatives of real H¹, with the L² inner product (not the H¹ norm). -/
def c1L2Submodule : Submodule ℝ ((ℝ → ℝ) × (ℝ → ℝ)) where
  carrier := {u | MemLp u.1 2 volume ∧ MemLp u.2 2 volume ∧ Continuous u.2 ∧
    ∀ x, HasDerivAt u.1 (u.2 x) x}
  zero_mem' := ⟨by simp,by simp,continuous_zero,fun x ↦ hasDerivAt_const x 0⟩
  add_mem' := by
    rintro u v ⟨hu,hu',hc,hd⟩ ⟨hv,hv',hvc,hvd⟩
    exact ⟨hu.add hv,hu'.add hv',hc.add hvc,fun x ↦ (hd x).add (hvd x)⟩
  smul_mem' := by
    rintro c u ⟨hu,hu',hc,hd⟩
    exact ⟨hu.const_smul c,hu'.const_smul c,continuous_const.smul hc,
      fun x ↦ (hd x).const_smul c⟩

def C1L2 : Type := ↥c1L2Submodule
instance instAddCommGroupC1L2 : AddCommGroup C1L2 := inferInstanceAs (AddCommGroup ↥c1L2Submodule)
instance instModuleRealC1L2 : Module ℝ C1L2 := inferInstanceAs (Module ℝ ↥c1L2Submodule)
namespace C1L2

def val (u : C1L2) : ℝ → ℝ := u.1.1
def grad (u : C1L2) : ℝ → ℝ := u.1.2
lemma val_memLp (u : C1L2) : MemLp u.val 2 volume := u.property.1
lemma grad_memLp (u : C1L2) : MemLp u.grad 2 volume := u.property.2.1
lemma grad_continuous (u : C1L2) : Continuous u.grad := u.property.2.2.1
lemma hasDerivAt (u : C1L2) (x : ℝ) : HasDerivAt u.val (u.grad x) x := u.property.2.2.2 x
lemma continuous (u : C1L2) : Continuous u.val := continuous_iff_continuousAt.mpr (fun x ↦ (u.hasDerivAt x).continuousAt)

def toLp : C1L2 →ₗ[ℝ] Lp ℝ 2 (volume : Measure ℝ) where
  toFun u := u.val_memLp.toLp u.val
  map_add' u v := u.val_memLp.toLp_add v.val_memLp
  map_smul' c u := u.val_memLp.toLp_const_smul c

lemma toLp_injective : Function.Injective toLp := by
  intro u v h
  have ha : u.val =ᵐ[volume] v.val := (MemLp.toLp_eq_toLp_iff u.val_memLp v.val_memLp).mp h
  have hv : u.val = v.val := MeasureTheory.Measure.eq_of_ae_eq ha u.continuous v.continuous
  apply Subtype.ext
  apply Prod.ext
  · exact hv
  · funext x
    exact ((hv ▸ u.hasDerivAt x) : HasDerivAt v.val (u.grad x) x).unique (v.hasDerivAt x)

instance instNormedAddCommGroup : NormedAddCommGroup C1L2 := NormedAddCommGroup.induced C1L2 (Lp ℝ 2 (volume : Measure ℝ)) toLp toLp_injective
instance instInnerProductSpaceReal : InnerProductSpace ℝ C1L2 := InnerProductSpace.induced toLp

@[simp] lemma val_zero (x : ℝ) : (0 : C1L2).val x = 0 := rfl
@[simp] lemma grad_zero (x : ℝ) : (0 : C1L2).grad x = 0 := rfl
@[simp] lemma val_add (u v : C1L2) (x : ℝ) : (u+v).val x = u.val x+v.val x := rfl
@[simp] lemma grad_add (u v : C1L2) (x : ℝ) : (u+v).grad x = u.grad x+v.grad x := rfl
@[simp] lemma val_smul (c : ℝ) (u : C1L2) (x : ℝ) : (c • u).val x = c*u.val x := rfl
@[simp] lemma grad_smul (c : ℝ) (u : C1L2) (x : ℝ) : (c • u).grad x = c*u.grad x := rfl

end C1L2
end SharpLiebThirring.SobolevProof
namespace SharpLiebThirring.SobolevProof
open MeasureTheory Set
lemma locallyIntegrable_intervalIntegrable {f : ℝ → ℝ} (hf : LocallyIntegrable f volume) (a b : ℝ) :
    IntervalIntegrable f volume a b :=
  (intervalIntegrable_iff').mpr (hf.integrableOn_isCompact isCompact_uIcc)
end SharpLiebThirring.SobolevProof
namespace SharpLiebThirring.SobolevProof
open MeasureTheory Set Filter Metric
open scoped Topology ContDiff
namespace C1L2

@[simp] lemma deriv_val (u : C1L2) : deriv u.val = u.grad := funext (fun x ↦ (u.hasDerivAt x).deriv)

/-- Exact integrated real eigen-equation; no regularity of W beyond local L¹. -/
def IsEigen (W : ℝ → ℝ) (k : ℝ) (u : C1L2) : Prop :=
  ∀ a b, u.grad b-u.grad a = ∫ x in a..b, (k^2-W x)*u.val x

lemma eigen_integrable {W : ℝ → ℝ} (hW : LocallyIntegrable W volume)
    (k : ℝ) (u : C1L2) : LocallyIntegrable (fun x ↦ (k^2-W x)*u.val x) volume :=
  ((locallyIntegrable_const (c := k^2)).sub hW).mul_continuous u.continuous

def eigenSubmodule {W : ℝ → ℝ} (hW : LocallyIntegrable W volume) (k : ℝ) : Submodule ℝ C1L2 where
  carrier := {u | u.IsEigen W k}
  zero_mem' := by intro a b; simp
  add_mem' := by
    intro u v hu hv a b
    simp only [val_add,grad_add,mul_add]
    rw [intervalIntegral.integral_add
      (locallyIntegrable_intervalIntegrable (eigen_integrable hW k u) a b)
      (locallyIntegrable_intervalIntegrable (eigen_integrable hW k v) a b),← hu a b,← hv a b]
    ring
  smul_mem' := by
    intro c u hu a b
    simp only [val_smul,grad_smul]
    simp_rw [mul_left_comm (k^2-_)]
    rw [intervalIntegral.integral_const_mul,← hu a b]
    ring

end C1L2
end SharpLiebThirring.SobolevProof
namespace SharpLiebThirring.SobolevProof
open MeasureTheory Set Filter
open scoped Topology ContDiff

lemma cutoffDerivative_compact (n : ℕ) : HasCompactSupport (cutoffDerivative n) := by
  have hh : cutoffDerivative n = deriv (cutoff n) := funext (fun x ↦ (cutoff_hasDerivAt n x).deriv.symm)
  rw [hh]
  exact (cutoff_compact n).deriv

namespace C1L2

def cut (n : ℕ) (u : C1L2) : C1L2 :=
  ⟨⟨fun x ↦ cutoff n x*u.val x,fun x ↦ cutoffDerivative n x*u.val x+cutoff n x*u.grad x⟩,
    ⟨(((cutoff_contDiff n).continuous).mul u.continuous).memLp_of_hasCompactSupport
      ((cutoff_compact n).mul_right),
    (((cutoffDerivative_continuous n).mul u.continuous).add
      (((cutoff_contDiff n).continuous).mul u.grad_continuous)).memLp_of_hasCompactSupport
      (((cutoffDerivative_compact n).mul_right).add ((cutoff_compact n).mul_right)),
    ((cutoffDerivative_continuous n).mul u.continuous).add
      (((cutoff_contDiff n).continuous).mul u.grad_continuous),
    fun x ↦ (cutoff_hasDerivAt n x).mul (u.hasDerivAt x)⟩⟩

@[simp] lemma cut_val (n : ℕ) (u : C1L2) (x : ℝ) : (u.cut n).val x = cutoff n x*u.val x := rfl
@[simp] lemma cut_grad (n : ℕ) (u : C1L2) (x : ℝ) :
    (u.cut n).grad x = cutoffDerivative n x*u.val x+cutoff n x*u.grad x := rfl

end C1L2
end SharpLiebThirring.SobolevProof
namespace SharpLiebThirring.SobolevProof.C1L2
open MeasureTheory Set Filter
open scoped Topology ContDiff

def energy (W : ℝ → ℝ) (u v : C1L2) : ℝ :=
  (∫ x, u.grad x*v.grad x)-(∫ x, W x*u.val x*v.val x)

end SharpLiebThirring.SobolevProof.C1L2

end

end OAI
end

section
-- module Solutions.OAIQW_LiebThirring.SobolevProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section
namespace SharpLiebThirring.SobolevProof
open MeasureTheory Set Filter
open scoped Topology ContDiff

/-- Classical representative of a real weak second-order eigenfunction. -/
structure RealEigenfunction (W : ℝ → ℝ) (k : ℝ) where
  val : ℝ → ℝ
  grad : ℝ → ℝ
  val_memLp : MemLp val 2 volume
  grad_memLp : MemLp grad 2 volume
  grad_continuous : Continuous grad
  hasDerivAt : ∀ x, HasDerivAt val (grad x) x
  grad_ac : ∀ a b, AbsolutelyContinuousOnInterval grad a b
  grad_deriv : ∀ᵐ x, deriv grad x = (k^2-W x)*val x

end SharpLiebThirring.SobolevProof
namespace SharpLiebThirring.SobolevProof
open MeasureTheory Set

def RealEigenfunction.toC1L2 {W : ℝ → ℝ} {k : ℝ} (u : RealEigenfunction W k) : C1L2 :=
  ⟨(u.val,u.grad),u.val_memLp,u.grad_memLp,u.grad_continuous,u.hasDerivAt⟩

end SharpLiebThirring.SobolevProof

end

end OAI
end


