-- Prove2me | Definitions.Def_OAI_GroupTheory_Kervaire_IncidenceSpaces
-- name    : OAI_GroupTheory_Kervaire_IncidenceSpaces
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T15:51:42.70304+00:00
-- url     : https://prove2.me/theorems/9d753008-0265-48c0-98f6-1fe757b07075
-- title:
--   The incidence map on products of unitary groups
-- statement:
--   These notions belong to a formal proof of the Kervaire conjecture in its unimodular form. For a group $A$ and an element $w$ of the free product $A*\langle t\rangle$ whose exponent sum in $t$ is $\pm1$, the natural map from $A$ to $(A*\langle t\rangle)/\langle\!\langle w\rangle\!\rangle$ is injective, so adjoining one generator and one such relation never kills a nontrivial group. The proof writes $w$ with unit $t$-exponents and represents elements of the normal closure by planar ribbon diagrams. These are pairs of permutations of darts satisfying an Euler equation, whose disks read off copies of the relator. A capping induction removes cancelling pairs of darts. Its key rigidity step at relator corners is proved analytically, with the fractional spectral phase of unitary operators over the group von Neumann algebra of $A$, which is subadditive under a trace.
--
--   For finite index sets $K,R$, with $M_I$ the complex $I\times I$ matrices:
--
--   1. **Spaces.** The algebra $M_K\times M_{K\sqcup R}\times M_R$, and the horizontal space of triples $(A,B,Z)$, with $A,B$ skew-Hermitian and $Z$ an $R\times K$ matrix.
--   2. **Blocks.** The block embeddings, $\mathrm{diag}(A,B)$, and the skew off-diagonal block $\begin{pmatrix}0&-Z^*\\Z&0\end{pmatrix}$.
--   3. **Incidence map.** For a map $f$ from $\mathbb R\times M_K$ to $M_{K\sqcup R}$,
--   $$
--   \mathrm{inc}_f(t;X,P,Q)=f(t,X)\,P\,\mathrm{diag}(1,Q^*)\,P^* .
--   $$
--   4. **Brackets and directions.** The trace pairing $-\mathrm{Re}\,\mathrm{tr}(ab)$ on skew matrices, commutator brackets, the direction of a horizontal vector inside the algebra, compensated brackets $T^*VT-V$, and a horizontal basis.
--
--   The incidence map of the model $X\mapsto\mathrm{diag}(X,-1)$ has nonzero degree.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Kervaire/IncidenceSpaces.lean

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Kervaire/IncidenceSpaces.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the Kervaire mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_Kervaire
import Definitions.Def_OAI_GroupTheory_Kervaire_Reductions
import Definitions.Def_OAI_GroupTheory_Kervaire_PermutationCycles
import Definitions.Def_OAI_GroupTheory_Kervaire_Components
import Definitions.Def_OAI_GroupTheory_Kervaire_Suppression
import Definitions.Def_OAI_GroupTheory_Kervaire_ComponentFibers
import Definitions.Def_OAI_GroupTheory_Kervaire_StrongLimits
import Definitions.Def_OAI_GroupTheory_Kervaire_SpectralMeasures
import Definitions.Def_OAI_GroupTheory_Kervaire_SpectralLogarithm
import Definitions.Def_OAI_GroupTheory_Kervaire_ScalarPhase
import Definitions.Def_OAI_GroupTheory_Kervaire_TraceCalculus
import Definitions.Def_OAI_GroupTheory_Kervaire_SpectralApproximation
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseSubadditivity
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseNaturality
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseGrids
import Definitions.Def_OAI_GroupTheory_Kervaire_RegularOperators
import Definitions.Def_OAI_GroupTheory_Kervaire_MatrixTrace
import Definitions.Def_OAI_GroupTheory_Kervaire_MatrixShifts
import Definitions.Def_OAI_GroupTheory_Kervaire_WeightedCycles
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseFaithfulness
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseDimension
import Definitions.Def_OAI_GroupTheory_Kervaire_MixingOperators
import Definitions.Def_OAI_GroupTheory_Kervaire_HaarCurrents
import Definitions.Def_OAI_GroupTheory_Kervaire_CurrentPullback

namespace OAI

noncomputable section

open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology
open Filter
open scoped Topology
open scoped ComplexOrder
open scoped lp ComplexConjugate
open scoped ComplexOrder
open MeasureTheory Measure Set Filter
open scoped Topology
open MeasureTheory ContinuousAlternatingMap Set VectorField
open scoped Topology ContDiff
open ContinuousAlternatingMap
open scoped ContDiff
open MeasureTheory NormedSpace
open scoped ContDiff
open Module Set ContinuousAlternatingMap
open Matrix Module
open scoped ContDiff Matrix.Norms.L2Operator

namespace KervaireIncidenceCurrent

section
variable {K R : Type*} [Fintype K] [Fintype R] [DecidableEq K] [DecidableEq R]
abbrev Mat (I : Type*) := Matrix I I ℂ
abbrev Alg (K R : Type*) := Mat K × Mat (K ⊕ R) × Mat R
abbrev Horizontal (K R : Type*) [Fintype K] [Fintype R] :=
  skewAdjoint.submodule ℝ (Mat K) × skewAdjoint.submodule ℝ (Mat R) × Matrix R K ℂ

/-- Diagonal corner inclusions, as continuous real linear maps. -/
def in11 : Mat K →L[ℝ] Mat (K ⊕ R) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A ↦ fromBlocks A 0 0 0
      map_add' := by intros; ext i j; cases i <;> cases j <;> simp [fromBlocks]
      map_smul' := by intros; ext i j; cases i <;> cases j <;> simp [fromBlocks] }
def in22 : Mat R →L[ℝ] Mat (K ⊕ R) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun B ↦ fromBlocks 0 0 0 B
      map_add' := by intros; ext i j; cases i <;> cases j <;> simp [fromBlocks]
      map_smul' := by intros; ext i j; cases i <;> cases j <;> simp [fromBlocks] }

def diag (A : Mat K) (B : Mat R) : Mat (K ⊕ R) := fromBlocks A 0 0 B

def off (Z : Matrix R K ℂ) : Mat (K ⊕ R) := fromBlocks 0 (-Zᴴ) Z 0

omit [Fintype K] [Fintype R] [DecidableEq K] [DecidableEq R] in
lemma off_skew (Z : Matrix R K ℂ) : star (off Z) = -off Z := by
  ext i j
  cases i <;> cases j <;> simp [off, Matrix.star_apply, Matrix.conjTranspose_apply]

omit [Fintype K] [Fintype R] [DecidableEq K] [DecidableEq R] in
lemma diag_star (A : Mat K) (B : Mat R) : star (diag A B) = diag (star A) (star B) := by
  ext i j
  cases i <;> cases j <;> simp [diag, Matrix.star_apply]

omit [DecidableEq K] [DecidableEq R] in
lemma diag_mul (A C : Mat K) (B D : Mat R) : diag A B * diag C D = diag (A*C) (B*D) := by
  simp [diag, fromBlocks_multiply]

/-- The incidence map is polynomial in the redundant compact-group coordinates. -/
def incidence (f : ℝ × Mat K → Mat (K ⊕ R)) (p : ℝ × Alg K R) : Mat (K ⊕ R) :=
  f (p.1,p.2.1) * p.2.2.1 * diag 1 (star p.2.2.2) * star p.2.2.1

omit [DecidableEq K] [DecidableEq R] in
lemma diag_eq_corner (A : Mat K) (B : Mat R) : diag A B = in11 A + in22 B := by
  ext i j
  cases i <;> cases j <;> simp [diag, in11, in22, fromBlocks]

end
variable {K R : Type*} [Fintype K] [Fintype R] [DecidableEq K] [DecidableEq R]

omit [Fintype K] [Fintype R] in
lemma diag_one : diag (1 : Mat K) (1 : Mat R) = 1 := by
  ext i j
  cases i <;> cases j <;> simp [diag, fromBlocks, one_apply]

lemma diag_unitary {A : Mat K} {B : Mat R} (hA : A ∈ unitary (Mat K))
    (hB : B ∈ unitary (Mat R)) : diag A B ∈ unitary (Mat (K ⊕ R)) := by
  rw [Unitary.mem_iff] at hA hB ⊢
  simp only [diag_star, diag_mul, hA.1, hA.2, hB.1, hB.2, diag_one, and_self]

lemma unitary_alg_parts (p : unitary (Alg K R)) :
    (p.val.1 ∈ unitary (Mat K)) ∧ (p.val.2.1 ∈ unitary (Mat (K ⊕ R))) ∧
      (p.val.2.2 ∈ unitary (Mat R)) := by
  have h := Unitary.mem_iff.mp p.property
  exact ⟨⟨congrArg Prod.fst h.1, congrArg Prod.fst h.2⟩,
    ⟨congrArg (Prod.fst ∘ Prod.snd) h.1, congrArg (Prod.fst ∘ Prod.snd) h.2⟩,
    ⟨congrArg (Prod.snd ∘ Prod.snd) h.1, congrArg (Prod.snd ∘ Prod.snd) h.2⟩⟩

def compensated (T : unitary (Mat R)) (V : skewAdjoint.submodule ℝ (Mat R)) :
    skewAdjoint.submodule ℝ (Mat R) :=
  ⟨star (T : Mat R) * V * T - V, by
    change star (star (T : Mat R) * (V : Mat R) * T - V) = -_
    rw [star_sub, star_mul, star_mul, star_star, V.property]
    noncomm_ring⟩

end KervaireIncidenceCurrent

open scoped ComplexOrder
namespace KervaireSkewTrace
variable {I : Type*} [Fintype I] [DecidableEq I]
local notation "M" => Matrix I I ℂ
local notation "S" => skewAdjoint.submodule ℝ M

/-- The positive invariant trace pairing on skew-Hermitian matrices. -/
def pairing : LinearMap.BilinForm ℝ S where
  toFun a :=
    { toFun := fun b ↦ -(Matrix.trace ((a : M) * (b : M))).re
      map_add' b c := by
        change -(trace ((a : M) * ((b : M) + (c : M)))).re =
          -(trace ((a : M)*(b : M))).re + -(trace ((a : M)*(c : M))).re
        rw [mul_add, trace_add, Complex.add_re]
        ring
      map_smul' := by intros; simp }
  map_add' a b := by
    apply LinearMap.ext
    intro c
    change -(trace (((a : M)+(b : M))*(c : M))).re =
      -(trace ((a : M)*(c : M))).re + -(trace ((b : M)*(c : M))).re
    rw [add_mul, trace_add, Complex.add_re]
    ring
  map_smul' r a := by ext c; simp

def bracket (a b : S) : S :=
  ⟨(a : M)*(b : M)-(b : M)*(a : M), by
    change star ((a : M)*(b : M)-(b : M)*(a : M)) = -_
    rw [star_sub, star_mul, star_mul, a.property, b.property]
    simp only [neg_mul_neg]
    abel⟩

end KervaireSkewTrace
namespace KervaireIncidenceCurrent
variable {K R : Type*} [Fintype K] [Fintype R] [DecidableEq K] [DecidableEq R]

/-- The redundant compact group has a canonically chosen horizontal frame. -/
def direction : Horizontal K R →ₗ[ℝ] skewAdjoint.submodule ℝ (Alg K R) where
  toFun h := ⟨((h.1 : Mat K),off h.2.2,(h.2.1 : Mat R)), by
    change (star (h.1 : Mat K),star (off h.2.2),star (h.2.1 : Mat R)) = -_
    rw [h.1.property, h.2.1.property, off_skew]
    rfl⟩
  map_add' h g := by
    apply Subtype.ext
    refine Prod.ext rfl (Prod.ext ?_ rfl)
    change off (h.2.2+g.2.2) = off h.2.2+off g.2.2
    simp only [off, conjTranspose_add, neg_add_rev, fromBlocks_add]
    congr 1 <;> first | simp only [zero_add] | exact add_comm _ _
  map_smul' c h := by
    apply Subtype.ext
    refine Prod.ext rfl (Prod.ext ?_ rfl)
    ext i j
    cases i <;> cases j <;> simp [off, fromBlocks, conjTranspose_smul]

/-- Lower block of the bracket of two off-diagonal skew matrices. -/
def rectBracket (Z Y : Matrix R K ℂ) : skewAdjoint.submodule ℝ (Mat R) :=
  ⟨-Z*Yᴴ+Y*Zᴴ, by
    change (-Z*Yᴴ+Y*Zᴴ)ᴴ = -(-Z*Yᴴ+Y*Zᴴ)
    simp only [conjTranspose_add, conjTranspose_mul, conjTranspose_neg,
      conjTranspose_conjTranspose]
    simp only [Matrix.mul_neg, Matrix.neg_mul]
    abel⟩

omit [Fintype R] [DecidableEq K] [DecidableEq R] in
@[simp] lemma rectBracket_zero_left (Y : Matrix R K ℂ) : rectBracket 0 Y = 0 := by
  apply Subtype.ext
  simp [rectBracket]
omit [Fintype R] [DecidableEq K] [DecidableEq R] in
@[simp] lemma rectBracket_zero_right (Z : Matrix R K ℂ) : rectBracket Z 0 = 0 := by
  apply Subtype.ext
  simp [rectBracket]
@[simp] lemma compensated_zero (T : unitary (Mat R)) : compensated T 0 = 0 := by
  apply Subtype.ext
  simp [compensated]
@[simp] lemma skewBracket_zero_left (b : skewAdjoint.submodule ℝ (Mat K)) :
    KervaireSkewTrace.bracket 0 b = 0 := by
  apply Subtype.ext
  simp [KervaireSkewTrace.bracket]
@[simp] lemma skewBracket_zero_right (a : skewAdjoint.submodule ℝ (Mat K)) :
    KervaireSkewTrace.bracket a 0 = 0 := by
  apply Subtype.ext
  simp [KervaireSkewTrace.bracket]

/-- The defect of horizontal integrability is vertical and is absorbed by T. -/
def effectiveBracket (T : unitary (Mat R)) (h g : Horizontal K R) : Horizontal K R :=
  (KervaireSkewTrace.bracket h.1 g.1,
   KervaireSkewTrace.bracket h.2.1 g.2.1 + compensated T (rectBracket h.2.2 g.2.2),0)

variable {IK IR IZ : Type*} [Fintype IK] [Fintype IR] [Fintype IZ]
  (bK : Basis IK ℝ (skewAdjoint.submodule ℝ (Mat K)))
  (bR : Basis IR ℝ (skewAdjoint.submodule ℝ (Mat R)))
  (bZ : Basis IZ ℝ (Matrix R K ℂ))

def horizontalBasis : Basis (IK ⊕ IR ⊕ IZ) ℝ (Horizontal K R) := bK.prod (bR.prod bZ)

end KervaireIncidenceCurrent

end

end OAI


