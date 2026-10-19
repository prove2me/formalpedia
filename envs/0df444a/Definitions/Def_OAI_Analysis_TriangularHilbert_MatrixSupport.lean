-- Prove2me | Definitions.Def_OAI_Analysis_TriangularHilbert_MatrixSupport
-- name    : OAI_Analysis_TriangularHilbert_MatrixSupport
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T23:10:33.55539+00:00
-- url     : https://prove2.me/theorems/4dc500ed-c230-4fc7-9f55-59d49d91b3da
-- title:
--   Matrix energies, Sylvester operators and triangle block matrices
-- statement:
--   For complex square matrices, $\operatorname{tr}_{\mathbb R}(A)=\operatorname{Re}\operatorname{tr}A$ and $\langle X,Y\rangle=\operatorname{Re}\operatorname{tr}(X^*Y)$. The matrix energy of $P\ge0$ is $E(P)=\operatorname{Re}\operatorname{tr}(P\sqrt P)=\operatorname{tr}P^{3/2}$, and $\mathrm{sylv}_A(X)=AX+XA$.
--
--   1. **Costs.** $\mathrm{penalty}(A,X)=\langle X,\mathrm{sylv}_A X\rangle$, $\mathrm{variation}(A,K,X)=2\langle K,X\rangle-\mathrm{penalty}(A,X)$, and $\mathrm{rootCost}(A,K)=\frac32\sup_X\mathrm{variation}(A,K,X)$. The Hessian cost is $\mathrm{hessianCost}(P,K)=\mathrm{rootCost}(\sqrt P,K)$. For positive definite $A$, $\mathrm{sylv}_A$ is a linear homeomorphism, and for diagonal $A$ it acts entrywise by $q_i+q_j$.
--   2. **Energy and gradient.** $E(P)=\operatorname{Re}\operatorname{tr}(P\sqrt P)$ and $\nabla E(P)[K]=\frac32\operatorname{Re}\operatorname{tr}(\sqrt P\,K)$. The Hessian pairing is $\frac32\langle K,\mathrm{sylv}_{\sqrt P}^{-1}L\rangle$.
--   3. **Triangle blocks.** For $W_0,W_1,W_2$, the triangle matrix is the $3\times3$ block matrix with $W_0,W_1,W_2$ on the cyclic off-diagonal positions $(0,1),(1,2),(2,0)$ and their adjoints opposite. $\mathrm{rowStar}(W,v)$ keeps block row $v$, and
--   $$
--   \mathrm{starGram}(W,v)=\mathrm{rowStar}(W,v)^*\,\mathrm{rowStar}(W,v).
--   $$
--   Variants insert a block diagonal $D$, rescale an edge by a phase, form Gram rows $R_i^*R_j$, and regularize $P\mapsto P+\eta I$.
--   4. **Weights.** Spectral weights $\frac{|m_i|^2|m_j|^2}{|m_i|+|m_j|}|D_{ij}|^2$, cubic terms $m_im_jm_kD_{ij}D_{jk}D_{ki}$, and row and column norms.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/TriangularHilbert/MatrixSupport.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/TriangularHilbert/MatrixSupport.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the TriangularHilbert mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_TriangularHilbert
import Definitions.Def_OAI_Analysis_TriangularHilbert_Gaussian
import Definitions.Def_OAI_Analysis_TriangularHilbert_MeshMass
import Definitions.Def_OAI_Analysis_TriangularHilbert_GaussianMoments
import Definitions.Def_OAI_Analysis_TriangularHilbert_SignedWindowScalar

namespace OAI

universe uι uκ uX uμ

section
open scoped BigOperators
noncomputable section
namespace TriangularHilbert.MatrixEnergy

open scoped Matrix.Norms.L2Operator ComplexInnerProductSpace InnerProductSpace

def spectralWeight {ι : Type uι} (D : Matrix ι ι ℂ) (m : ι → ℝ) (i j : ι) : ℝ :=
  |m i|^2 * |m j|^2 / (|m i| + |m j|) * ‖D i j‖^2

def cubicTerm {ι : Type uι} (D : Matrix ι ι ℂ) (m : ι → ℝ) (i j k : ι) : ℂ :=
  (m i : ℂ) * (m j : ℂ) * (m k : ℂ) * D i j * D j k * D k i

end TriangularHilbert.MatrixEnergy

noncomputable section
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff
open Unitary
namespace TriangularHilbert.MatrixEnergy

variable {ι : Type uι} [Fintype ι]

def traceReal (A : Matrix ι ι ℂ) : ℝ := A.trace.re

@[simp] theorem traceReal_add (A B : Matrix ι ι ℂ) :
    traceReal (A + B) = traceReal A + traceReal B := by simp [traceReal]
@[simp] theorem traceReal_sub (A B : Matrix ι ι ℂ) :
    traceReal (A - B) = traceReal A - traceReal B := by simp [traceReal]
@[simp] theorem traceReal_smul (c : ℝ) (A : Matrix ι ι ℂ) :
    traceReal (c • A) = c * traceReal A := by simp [traceReal]
@[simp] theorem traceReal_zero : traceReal (0 : Matrix ι ι ℂ) = 0 := by simp [traceReal]
@[simp] theorem traceReal_star (A : Matrix ι ι ℂ) : traceReal Aᴴ = traceReal A := by
  simp [traceReal]
def hsReal (X Y : Matrix ι ι ℂ) : ℝ := traceReal (Xᴴ * Y)

@[simp] theorem hsReal_add_left (X Y Z : Matrix ι ι ℂ) :
    hsReal (X + Y) Z = hsReal X Z + hsReal Y Z := by
  simp [hsReal, add_mul]
@[simp] theorem hsReal_add_right (X Y Z : Matrix ι ι ℂ) :
    hsReal X (Y + Z) = hsReal X Y + hsReal X Z := by
  simp [hsReal, mul_add]
@[simp] theorem hsReal_sub_left (X Y Z : Matrix ι ι ℂ) :
    hsReal (X - Y) Z = hsReal X Z - hsReal Y Z := by
  simp [hsReal, sub_mul]
@[simp] theorem hsReal_sub_right (X Y Z : Matrix ι ι ℂ) :
    hsReal X (Y - Z) = hsReal X Y - hsReal X Z := by
  simp [hsReal, mul_sub]
@[simp] theorem hsReal_smul_left (c : ℝ) (X Y : Matrix ι ι ℂ) :
    hsReal (c • X) Y = c * hsReal X Y := by
  simp [hsReal, Matrix.smul_mul]
@[simp] theorem hsReal_smul_right (c : ℝ) (X Y : Matrix ι ι ℂ) :
    hsReal X (c • Y) = c * hsReal X Y := by
  simp [hsReal, Matrix.mul_smul]
@[simp] theorem hsReal_zero_right (X : Matrix ι ι ℂ) : hsReal X 0 = 0 := by simp [hsReal]

def sylv (A X : Matrix ι ι ℂ) : Matrix ι ι ℂ := A * X + X * A

@[simp] theorem sylv_add_right (A X Y : Matrix ι ι ℂ) :
    sylv A (X + Y) = sylv A X + sylv A Y := by unfold sylv; noncomm_ring
@[simp] theorem sylv_sub_right (A X Y : Matrix ι ι ℂ) :
    sylv A (X - Y) = sylv A X - sylv A Y := by unfold sylv; noncomm_ring
@[simp] theorem sylv_smul_right (c : ℝ) (A X : Matrix ι ι ℂ) :
    sylv A (c • X) = c • sylv A X := by simp [sylv, smul_add]
@[simp] theorem sylv_smul_left (c : ℝ) (A X : Matrix ι ι ℂ) :
    sylv (c • A) X = c • sylv A X := by simp [sylv, smul_add]
@[simp] theorem sylv_sub_left (A B X : Matrix ι ι ℂ) :
    sylv (A - B) X = sylv A X - sylv B X := by unfold sylv; noncomm_ring
@[simp] theorem sylv_zero_right (A : Matrix ι ι ℂ) : sylv A 0 = 0 := by simp [sylv]

def penalty (A X : Matrix ι ι ℂ) : ℝ := hsReal X (sylv A X)

def variation (A K X : Matrix ι ι ℂ) : ℝ := 2 * hsReal K X - penalty A X

def rootCost (A K : Matrix ι ι ℂ) : ℝ := (3 / 2 : ℝ) * sSup (Set.range (variation A K))

variable [DecidableEq ι]

theorem sylv_diagonal_apply (q : ι → ℝ) (X : Matrix ι ι ℂ) (i j : ι) :
    sylv (Matrix.diagonal (fun i => (q i : ℂ))) X i j =
      ((q i + q j : ℝ) : ℂ) * X i j := by
  simp only [sylv, Matrix.add_apply, Matrix.diagonal_mul, Matrix.mul_diagonal,
    Complex.ofReal_add]
  ring

def diagonalSolution (q : ι → ℝ) (K : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  fun i j => K i j / ((q i + q j : ℝ) : ℂ)

theorem diagonalSolution_solves (q : ι → ℝ) (K : Matrix ι ι ℂ)
    (hsupp : ∀ i j, q i + q j = 0 → K i j = 0) :
    sylv (Matrix.diagonal (fun i => (q i : ℂ))) (diagonalSolution q K) = K := by
  ext i j
  rw [sylv_diagonal_apply]
  by_cases h : q i + q j = 0
  · simp [diagonalSolution, h, hsupp i j h]
  · exact mul_div_cancel₀ _ (Complex.ofReal_ne_zero.mpr h)

theorem sylv_unitary_conj (U : unitary (Matrix ι ι ℂ)) (A X : Matrix ι ι ℂ) :
    sylv (conjStarAlgAut ℂ _ U A) (conjStarAlgAut ℂ _ U X) =
      conjStarAlgAut ℂ _ U (sylv A X) := by simp only [sylv, map_add, map_mul]

def hessianCost (P K : Matrix ι ι ℂ) : ℝ := rootCost (CFC.sqrt P) K

theorem exists_sylv_solution {A K : Matrix ι ι ℂ} (hA : A.IsHermitian)
    (hsupp : ∀ i j, hA.eigenvalues i + hA.eigenvalues j = 0 →
      conjStarAlgAut ℂ _ (star hA.eigenvectorUnitary) K i j = 0) :
    ∃ Y, sylv A Y = K := by
  let U := hA.eigenvectorUnitary
  let K' := conjStarAlgAut ℂ _ (star U) K
  let Y := diagonalSolution hA.eigenvalues K'
  refine ⟨conjStarAlgAut ℂ _ U Y, ?_⟩
  have hy : sylv (Matrix.diagonal (fun i => (hA.eigenvalues i : ℂ))) Y = K' :=
    diagonalSolution_solves _ _ hsupp
  have hh := congrArg (conjStarAlgAut ℂ _ U) hy
  rw [← sylv_unitary_conj] at hh
  have ha : conjStarAlgAut ℂ _ U
      (Matrix.diagonal (fun i => (hA.eigenvalues i : ℂ))) = A :=
    hA.spectral_theorem.symm
  rw [ha] at hh
  simpa only [K', ← conjStarAlgAut_mul_apply, Unitary.mul_star_self, map_one,
    StarAlgEquiv.one_apply] using hh

theorem exists_sylv_solution_posDef {A : Matrix ι ι ℂ} (hA : A.PosDef)
    (K : Matrix ι ι ℂ) : ∃ Y, sylv A Y = K := by
  apply exists_sylv_solution hA.isHermitian
  intro i j hij
  exact False.elim ((ne_of_gt (add_pos (hA.eigenvalues_pos i)
    (hA.eigenvalues_pos j))) hij)

def sylvLinear (A : Matrix ι ι ℂ) : Matrix ι ι ℂ →ₗ[ℝ] Matrix ι ι ℂ where
  toFun := sylv A
  map_add' := sylv_add_right A
  map_smul' c X := sylv_smul_right c A X

def sylvEquiv {A : Matrix ι ι ℂ} (hA : A.PosDef) :
    Matrix ι ι ℂ ≃L[ℝ] Matrix ι ι ℂ :=
  (LinearEquiv.ofBijective (sylvLinear A)
    (let hs : Function.Surjective (sylvLinear A) := exists_sylv_solution_posDef hA
     ⟨(LinearMap.injective_iff_surjective).mpr hs, hs⟩)).toContinuousLinearEquiv

def traceRealCLM : Matrix ι ι ℂ →L[ℝ] ℝ :=
  (show Matrix ι ι ℂ →ₗ[ℝ] ℝ from
    { toFun := traceReal
      map_add' := traceReal_add
      map_smul' := traceReal_smul }).toContinuousLinearMap

omit [DecidableEq ι] in
@[simp] theorem traceRealCLM_apply (X : Matrix ι ι ℂ) :
    traceRealCLM X = traceReal X := rfl

def energy (P : Matrix ι ι ℂ) : ℝ := traceReal (P * CFC.sqrt P)

def energyGradient (P : Matrix ι ι ℂ) : Matrix ι ι ℂ →L[ℝ] ℝ :=
  (3 / 2 : ℝ) • traceRealCLM.comp ((ContinuousLinearMap.mul ℝ _) (CFC.sqrt P))

@[simp] theorem energyGradient_apply (P K : Matrix ι ι ℂ) :
    energyGradient P K = (3 / 2 : ℝ) * traceReal (CFC.sqrt P * K) := rfl

end TriangularHilbert.MatrixEnergy

namespace TriangularHilbert.MatrixEnergy
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Unitary
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

end TriangularHilbert.MatrixEnergy

namespace TriangularHilbert.MatrixEnergy
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Unitary
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

abbrev Three := Fin 3
abbrev BlockSpace (ι : Type uι) := Three × ι
abbrev blocks (A : Matrix Three Three (Matrix ι ι ℂ)) :
    Matrix (BlockSpace ι) (BlockSpace ι) ℂ := Matrix.comp _ _ _ _ _ A

def triangleBlocks (W : Three → Matrix ι ι ℂ) : Matrix Three Three (Matrix ι ι ℂ) :=
  fun i j => if i = 0 then (if j = 0 then 0 else if j = 1 then W 0 else (W 2)ᴴ)
    else if i = 1 then (if j = 0 then (W 0)ᴴ else if j = 1 then 0 else W 1)
    else (if j = 0 then W 2 else if j = 1 then (W 1)ᴴ else 0)

def triangle (W : Three → Matrix ι ι ℂ) := blocks (triangleBlocks W)
def blockD (D : Three → Matrix ι ι ℂ) := blocks (Matrix.diagonal D)

def vertexProj (v : Three) : Matrix (BlockSpace ι) (BlockSpace ι) ℂ :=
  Matrix.diagonal (fun a => if a.1 = v then 1 else 0)

def rowStar (W : Three → Matrix ι ι ℂ) (v : Three) := vertexProj v * triangle W

def starGram (W : Three → Matrix ι ι ℂ) (v : Three) := (rowStar W v)ᴴ * rowStar W v

def starInsert (W D : Three → Matrix ι ι ℂ) (v : Three) :=
  (rowStar W v)ᴴ * blockD D * rowStar W v

end TriangularHilbert.MatrixEnergy

namespace TriangularHilbert.MatrixEnergy
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Unitary
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

end TriangularHilbert.MatrixEnergy

namespace TriangularHilbert.MatrixEnergy
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Unitary
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

def diagonalUnitary (c : ι → ℂ) (hc : ∀ i, ‖c i‖ = 1) : unitary (Matrix ι ι ℂ) :=
  ⟨Matrix.diagonal c, by
    apply Matrix.mem_unitaryGroup_iff'.mpr
    rw [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
      Matrix.diagonal_mul_diagonal]
    have hci (i : ι) : star (c i) * c i = 1 := by
      simpa only [RCLike.star_def, mul_comm, hc, one_pow, Complex.ofReal_one] using
        Complex.mul_conj' (c i)
    ext i j
    by_cases hij : i = j
    · subst j; simpa using hci i
    · simp [hij]⟩

def phaseEdge (z : ℂ) (W : Three → Matrix ι ι ℂ) : Three → Matrix ι ι ℂ :=
  fun v => if v = 0 then z • W 0 else W v

def rowPhase (z : ℂ) (v : Three) : BlockSpace ι → ℂ := fun a =>
  if v = 0 then (if a.1 = 1 then z else 1)
  else if v = 1 then (if a.1 = 0 then star z else 1) else 1

end TriangularHilbert.MatrixEnergy

namespace TriangularHilbert.MatrixEnergy
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator ContDiff
open Unitary MeasureTheory Filter
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

def regularize (P : Matrix ι ι ℂ) (η : ℝ) : Matrix ι ι ℂ := P + η • 1

end TriangularHilbert.MatrixEnergy

namespace TriangularHilbert.MatrixEnergy
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open MeasureTheory Filter Topology
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

end TriangularHilbert.MatrixEnergy

namespace TriangularHilbert.MatrixEnergy
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Unitary Filter Topology
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

end TriangularHilbert.MatrixEnergy

namespace TriangularHilbert.MatrixEnergy
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

end TriangularHilbert.MatrixEnergy

namespace TriangularHilbert.MatrixEnergy
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

def wideRow (R : Three → Matrix ι ι ℂ) : Matrix ι (BlockSpace ι) ℂ :=
  fun i a => R a.1 i a.2

def gramRow (R : Three → Matrix ι ι ℂ) := blocks (fun i j => (R i)ᴴ * R j)
def insertRow (R : Three → Matrix ι ι ℂ) (L : Matrix ι ι ℂ) :=
  blocks (fun i j => (R i)ᴴ * L * R j)
def pinchedRow (R : Three → Matrix ι ι ℂ) := blockD (fun v => (R v)ᴴ * R v)

def centerGram (W : Three → Matrix ι ι ℂ) (v : Three) : Matrix ι ι ℂ :=
  ∑ w, triangleBlocks W v w * (triangleBlocks W v w)ᴴ

end TriangularHilbert.MatrixEnergy

namespace TriangularHilbert.MatrixEnergy
open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open MeasureTheory Filter Topology
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

def sqrtInverse {P : Matrix ι ι ℂ} (hP : P.PosDef) :
    Matrix ι ι ℂ ≃L[ℝ] Matrix ι ι ℂ :=
  (sylvEquiv (Matrix.isStrictlyPositive_iff_posDef.mp
    (IsStrictlyPositive.sqrt P hP.isStrictlyPositive))).symm

def hessianPairPD {P : Matrix ι ι ℂ} (hP : P.PosDef) (K L : Matrix ι ι ℂ) : ℝ :=
  (3 / 2 : ℝ) * hsReal K (sqrtInverse hP L)

end TriangularHilbert.MatrixEnergy

open scoped BigOperators Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
noncomputable section
namespace TriangularHilbert.MatrixEnergy
variable {ι : Type uι} {κ : Type uκ} {μ : Type uμ} [Fintype ι] [Fintype κ] [Fintype μ]

def rowNorm (R : Matrix ι κ ℂ) (i : ι) : ℝ := Real.sqrt (∑ j, ‖R i j‖^2)
def colNorm (R : Matrix ι κ ℂ) (j : κ) : ℝ := Real.sqrt (∑ i, ‖R i j‖^2)

variable [DecidableEq κ]

end TriangularHilbert.MatrixEnergy
end
end
end
end

end OAI


