-- Prove2me | Definitions.Def_OAI_Analysis_Unitarizability_KernelObstruction
-- name    : OAI_Analysis_Unitarizability_KernelObstruction
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T01:01:52.991319+00:00
-- url     : https://prove2.me/theorems/fa68c571-7db3-4d84-b917-f2992d27a858
-- title:
--   Blocks, translation commutant and kernel energy on $\ell^2(G;\mathbb{C}^K)$
-- statement:
--   Let $G$ be a group and $K$ a finite set. Write $\mathbb{C}^K$ for the Euclidean fibre,
--   $$\mathcal H=\ell^2(G;\mathbb{C}^K)=\Bigl\{\xi:G\to\mathbb{C}^K:\ \sum_{x\in G}\|\xi(x)\|^2<\infty\Bigr\},\qquad \|\xi\|^2=\sum_{x\in G}\|\xi(x)\|^2,$$
--   and $B(\mathcal H)$ for the bounded linear operators on $\mathcal H$.
--
--   1. **Coordinate maps.** For $x\in G$, the inclusion $\iota_x:\mathbb{C}^K\to\mathcal H$ places $v$ at the point $x$ (and $0$ elsewhere), and the evaluation $E_x:\mathcal H\to\mathbb{C}^K$ is $\xi\mapsto\xi(x)$. The file records $\|\iota_xv\|=\|v\|$, $\iota_x^*=E_x$ and $E_x\iota_x=\mathrm{id}$.
--   2. **Blocks, rows and columns.** For $F\in B(\mathcal H)$ and $x,y\in G$: the block $F_{xy}=E_xF\iota_y$ (an operator on $\mathbb{C}^K$), the row $E_xF:\mathcal H\to\mathbb{C}^K$ and the column $F\iota_y:\mathbb{C}^K\to\mathcal H$.
--   3. **Coefficient vectors.** For an operator $B$ on $\mathbb{C}^K$ with standard basis $(e_b)$, the entry vector $(B_{ab})_{(a,b)\in K\times K}$, $B_{ab}=(Be_b)_a$, in $\mathbb{C}^{K\times K}$; its Euclidean norm is the Hilbert–Schmidt norm $\|B\|_{HS}$. Blocks and coefficients respect differences: $(A-C)_{xy}=A_{xy}-C_{xy}$, and the coefficients of $A-C$ are those of $A$ minus those of $C$.
--   4. **Reindexing and translation.** For a bijection $e$ of $G$, $\xi\mapsto\xi\circ e$ is a linear isometry of $\mathcal H$. The left translation representation $\lambda:G\to B(\mathcal H)$,
--   $$(\lambda(g)\xi)(x)=\xi(g^{-1}x),$$
--   is a group homomorphism with $\lambda(g)\iota_y=\iota_{gy}$.
--   5. **Commutant.** $\mathcal C=\{F\in B(\mathcal H):\ F\lambda(g)=\lambda(g)F \text{ for all } g\in G\}$.
--   6. **Kernel energy.** For $A\in B(\mathcal H)$, with $1$ the identity of $G$,
--   $$\mathcal E(A)=\sum_{s\in G}\|A_{1,s}\|_{HS}^2 .$$
--
--   An operator in $\mathcal C$ is a convolution operator: its blocks satisfy $A_{xy}=A_{1,x^{-1}y}$, so $\mathcal E(A)$ is the squared $\ell^2$ norm of its matrix-valued kernel. The module proves the kernel obstruction: if $K$ is nonempty, $A\in\mathcal C$, $\kappa\ge 0$, $\|E_1T\|\le\kappa$ and $\|(A-T)\iota_1\|\le\kappa$, then the distance from $T$ to $\mathcal C$ is at least $\tfrac12\sqrt{\mathcal E(A)/|K|}-\kappa$. Splitting an invariant operator of large energy per fibre dimension into a row-sparse part $T$ and a column-sparse remainder therefore produces operators $T$ far from the commutant.
--
--   **Formalization Note** `Fibre K` is `EuclideanSpace ℂ K`, `Space G K` is `lp (fun _ : G => Fibre K) 2` and `Op G K` its continuous linear endomorphisms. The definitions are `inclusion`, `evaluation`, `block`, `row`, `col`, `coefficients`, `reindex`, `reindexIsometry`, `translation`, `Commutant` and `energy`; items 1 to 3 need no group structure on `G`. The listed identities are the simp lemmas of the file, together with `space_norm_sq` and `reindex_norm`. `energy` is a `tsum`, which Lean sets to $0$ for non-summable families; the module proves summability for every bounded operator.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Unitarizability/KernelObstruction.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Unitarizability/KernelObstruction.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the Dixmier mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Shrink
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Lp.lpHolder
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Combinatorics.Hall.Basic
import Mathlib.Data.Countable.Small
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Order.Filter.AtTopBot.Tendsto
import Mathlib.Order.Lattice.Nat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Topology.Instances.Discrete
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Definitions.Def_Dixmier
import Definitions.Def_OAI_Analysis_Unitarizability_SparseMask
import Definitions.Def_OAI_Analysis_Unitarizability_EndpointAssignment
import Definitions.Def_OAI_Analysis_Unitarizability_SparseSplitting
import Definitions.Def_OAI_Analysis_Unitarizability_Regular
import Definitions.Def_OAI_Analysis_Unitarizability_VectorMean
import Definitions.Def_OAI_Analysis_Unitarizability_FiniteSigns
import Definitions.Def_OAI_Analysis_Unitarizability_KernelEnergy
import Definitions.Def_OAI_Analysis_Unitarizability_FiniteSynthesis
import Definitions.Def_OAI_Analysis_Unitarizability_SignMatrix
import Definitions.Def_OAI_Analysis_Unitarizability_Parameters
import Definitions.Def_OAI_Analysis_Unitarizability_FrameParameters
import Definitions.Def_OAI_Analysis_Unitarizability_ComplexFrames
import Definitions.Def_OAI_Analysis_Unitarizability_Frames

namespace OAI

/-! Coordinate maps and the invariant-kernel obstruction.
The Hilbert space is the lp space with finite Euclidean fibres. -/
noncomputable section
namespace Dixmier
namespace KernelObstruction
open scoped ComplexConjugate
open Finset
variable {G K : Type*} [Fintype K]
local instance instDecidableEq_oAI_1 : DecidableEq K := Classical.decEq K

abbrev Fibre (K : Type*) [Fintype K] := EuclideanSpace ℂ K
abbrev Space (G K : Type*) [Fintype K] := lp (fun _ : G => Fibre K) 2
abbrev Op (G K : Type*) [Fintype K] := Space G K →L[ℂ] Space G K

def inclusion (x : G) : Fibre K →L[ℂ] Space G K :=
  lp.singleContinuousLinearMap ℂ (fun _ : G => Fibre K) 2 x

def evaluation (x : G) : Space G K →L[ℂ] Fibre K :=
  lp.evalCLM ℂ (fun _ : G => Fibre K) 2 x

@[simp] theorem inclusion_apply (x : G) (v : Fibre K) :
    inclusion x v = lp.single 2 x v := rfl
@[simp] theorem evaluation_apply (x : G) (ξ : Space G K) :
    evaluation x ξ = ξ x := rfl

@[simp] theorem inclusion_norm (x : G) (v : Fibre K) : ‖inclusion x v‖ = ‖v‖ :=
  lp.norm_single (p := 2) (E := fun _ : G => Fibre K) (by norm_num) x v

@[simp] theorem inclusion_adjoint (x : G) :
    (inclusion (K := K) x).adjoint = evaluation x := by
  apply ContinuousLinearMap.ext
  intro ξ
  apply ext_inner_left ℂ
  intro v
  rw [ContinuousLinearMap.adjoint_inner_right]
  change inner ℂ (lp.single 2 x v) ξ = inner ℂ v (ξ x)
  exact lp.inner_single_left (𝕜 := ℂ) (G := fun _ : G => Fibre K) x v ξ

@[simp] theorem evaluation_inclusion (x : G) :
    (evaluation (K := K) x).comp (inclusion x) = ContinuousLinearMap.id ℂ (Fibre K) := by
  ext v a
  simp

def block (F : Op G K) (x y : G) : Fibre K →L[ℂ] Fibre K :=
  (evaluation x).comp (F.comp (inclusion y))

def row (F : Op G K) (x : G) : Space G K →L[ℂ] Fibre K :=
  (evaluation x).comp F

def col (F : Op G K) (y : G) : Fibre K →L[ℂ] Space G K :=
  F.comp (inclusion y)

def coefficients (B : Fibre K →L[ℂ] Fibre K) : EuclideanSpace ℂ (K × K) :=
  WithLp.toLp 2 (fun ab => (B (EuclideanSpace.basisFun K ℂ ab.2)) ab.1)

@[simp] theorem coefficients_apply (B : Fibre K →L[ℂ] Fibre K) (a b : K) :
    coefficients B (a,b) = (B (EuclideanSpace.basisFun K ℂ b)) a := rfl

theorem space_norm_sq (ξ : Space G K) : ‖ξ‖^2 = ∑' x, ‖ξ x‖^2 := by
  simpa using lp.norm_rpow_eq_tsum (p := 2) (by norm_num) ξ

variable [Group G]

def reindex (e : G ≃ G) (ξ : Space G K) : Space G K :=
  ⟨fun x => ξ (e x), memℓp_gen (((lp.memℓp ξ).summable (by norm_num)).comp_injective e.injective)⟩

omit [Group G] in
theorem reindex_norm (e : G ≃ G) (ξ : Space G K) : ‖reindex e ξ‖ = ‖ξ‖ := by
  have h : ‖reindex e ξ‖^2 = ‖ξ‖^2 := by
    rw [space_norm_sq, space_norm_sq]
    exact e.tsum_eq (fun x => ‖ξ x‖^2)
  nlinarith [norm_nonneg (reindex e ξ), norm_nonneg ξ]

def reindexIsometry (e : G ≃ G) : Space G K →ₗᵢ[ℂ] Space G K where
  toFun := reindex e
  map_add' ξ η := by ext x a; rfl
  map_smul' z ξ := by ext x a; rfl
  norm_map' := reindex_norm e

/-- The fibre-valued left regular representation. -/
def translation : G →* Op G K where
  toFun g := (reindexIsometry (K := K) (Equiv.mulLeft g⁻¹)).toContinuousLinearMap
  map_one' := by ext ξ x a; simp [reindexIsometry, reindex]
  map_mul' g h := by ext ξ x a; simp [reindexIsometry, reindex]

@[simp] theorem translation_apply (g : G) (ξ : Space G K) (x : G) :
    translation g ξ x = ξ (g⁻¹ * x) := rfl

@[simp] theorem translation_inclusion (g y : G) (v : Fibre K) :
    translation g (inclusion y v) = inclusion (g*y) v := by
  ext x a
  simp only [translation_apply, inclusion_apply, lp.single_apply]
  by_cases h : x = g*y
  · subst x
    simp
  · have h' : g⁻¹*x ≠ y := by intro he; apply h; rw [← he]; simp
    simp [Pi.single_eq_of_ne h, Pi.single_eq_of_ne h']

def Commutant : Set (Op G K) := {F | ∀ g, Commute F (translation g)}

omit [Group G] in
@[simp] theorem block_sub (A C : Op G K) (x y : G) :
    block (A-C) x y = block A x y - block C x y := by
  ext v a
  rfl

@[simp] theorem coefficients_sub (A C : Fibre K →L[ℂ] Fibre K) :
    coefficients (A-C) = coefficients A - coefficients C := by ext ab; rfl

def energy (A : Op G K) : ℝ := ∑' s, ‖coefficients (block A 1 s)‖^2

end KernelObstruction
end Dixmier

end

end OAI


