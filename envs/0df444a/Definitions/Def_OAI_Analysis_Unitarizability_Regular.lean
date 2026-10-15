-- Prove2me | Definitions.Def_OAI_Analysis_Unitarizability_Regular
-- name    : OAI_Analysis_Unitarizability_Regular
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T00:52:48.201891+00:00
-- url     : https://prove2.me/theorems/2118d290-5c77-4aa7-bdc9-04ce34db508f
-- title:
--   Regular representations on $\ell^2(G)$, words and word products
-- statement:
--   Let $G$ be a type and $\ell^2(G)$ the complex Hilbert space of square-summable functions on $G$.
--
--   1. **Reindexing.** For a bijection $e:G\to G$, the map $\xi\mapsto\xi\circ e$ on $\ell^2(G)$. The file proves $\|\xi\|^2=\sum_{x}|\xi(x)|^2$ and $\|\xi\circ e\|=\|\xi\|$, and packages reindexing as a complex-linear isometry of $\ell^2(G)$.
--   2. **Right regular representation.** For a group $G$, the homomorphism $t\mapsto R_t$ from $G$ into the bounded operators on $\ell^2(G)$, where
--   $$(R_t\xi)(x)=\xi(xt).$$
--   3. **Left regular representation.** The homomorphism $g\mapsto U_g$ with
--   $$(U_g\xi)(x)=\xi(g^{-1}x).$$
--   Both are obtained by reindexing, so every $R_t$ and every $U_g$ is an isometry.
--   4. **Words.** For a type $I$ and $n\in\mathbb{N}$, the type of words of length $n$ is defined recursively by $\mathrm{Word}(I,0)=\{\ast\}$ (a single point) and $\mathrm{Word}(I,n+1)=I\times\mathrm{Word}(I,n)$, so a word is an $n$-tuple $w=(i_1,\dots,i_n)$. If $I$ is finite, so is $\mathrm{Word}(I,n)$.
--   5. **Word products.** For $s:I\to G$,
--   $$\pi_s(i_1,\dots,i_n)=s_{i_1}s_{i_2}\cdots s_{i_n},\qquad \pi_s(\ast)=1 .$$
--
--   The right regular operators measure non-amenability: the relevant finite sets $S$ are those for which $\bigl\|\sum_{t\in S}R_t\bigr\|$ is strictly smaller than $|S|$. Since $t\mapsto R_t$ is a homomorphism, the $n$-th power of $\sum_{i\in I}R_{s_i}$ equals $\sum_{w}R_{\pi_s(w)}$ over all $|I|^n$ words, so words index the terms of iterated averages with their full multiplicity; distinct words remain distinct labels even when their products in $G$ coincide. Left and right regular operators commute with each other.
--
--   **Formalization Note** `reindexL2`, `reindexIsometry` (a `LinearIsometry`), `rightRegular` and `leftRegular` (bundled monoid homomorphisms into `ScalarL2 G →L[ℂ] ScalarL2 G`) come with evaluation simp lemmas, `l2_norm_sq` and `reindexL2_norm`. `Word I n` is the nested product ending in `PUnit`, `wordFintype` is its `Fintype` instance, and `wordProduct s (n+1) w` is `s w.1 * wordProduct s n w.2`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Unitarizability/Regular.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Unitarizability/Regular.lean by skeleton subtraction
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

namespace OAI

/-! Regular convolution operators, product lists with multiplicity,
and sparse splitting from a contracting average. -/
noncomputable section
namespace Dixmier
universe u
open Finset
attribute [local instance] Classical.propDecidable

variable {G : Type*}

def reindexL2 (e : G ≃ G) (ξ : ScalarL2 G) : ScalarL2 G :=
  ⟨fun x => ξ (e x), memℓp_gen (((lp.memℓp ξ).summable (by norm_num)).comp_injective e.injective)⟩

@[simp] theorem reindexL2_apply (e : G ≃ G) (ξ : ScalarL2 G) (x : G) :
    reindexL2 e ξ x = ξ (e x) := rfl

theorem l2_norm_sq (ξ : ScalarL2 G) : ‖ξ‖ ^ 2 = ∑' x, ‖ξ x‖ ^ 2 := by
  simpa using lp.norm_rpow_eq_tsum (p := 2) (by norm_num) ξ

theorem reindexL2_norm (e : G ≃ G) (ξ : ScalarL2 G) : ‖reindexL2 e ξ‖ = ‖ξ‖ := by
  have hs : ‖reindexL2 e ξ‖ ^ 2 = ‖ξ‖ ^ 2 := by
    rw [l2_norm_sq, l2_norm_sq]
    exact e.tsum_eq (fun x => ‖ξ x‖ ^ 2)
  nlinarith [norm_nonneg (reindexL2 e ξ), norm_nonneg ξ]

def reindexIsometry (e : G ≃ G) : ScalarL2 G →ₗᵢ[ℂ] ScalarL2 G where
  toFun := reindexL2 e
  map_add' ξ η := by ext x; rfl
  map_smul' z ξ := by ext x; rfl
  norm_map' := reindexL2_norm e

variable [Group G]

/-- The right regular representation R_t ξ(x)=ξ(xt). -/
def rightRegular : G →* (ScalarL2 G →L[ℂ] ScalarL2 G) where
  toFun t := (reindexIsometry (Equiv.mulRight t)).toContinuousLinearMap
  map_one' := by ext ξ x; simp [reindexIsometry, reindexL2]
  map_mul' s t := by ext ξ x; simp [reindexIsometry, reindexL2, mul_assoc]

@[simp] theorem rightRegular_apply (t : G) (ξ : ScalarL2 G) (x : G) :
    rightRegular t ξ x = ξ (x * t) := rfl

/-- Left regular operators U_g commute with the right regular operators. -/
def leftRegular : G →* (ScalarL2 G →L[ℂ] ScalarL2 G) where
  toFun g := (reindexIsometry (Equiv.mulLeft g⁻¹)).toContinuousLinearMap
  map_one' := by ext ξ x; simp [reindexIsometry, reindexL2]
  map_mul' g h := by ext ξ x; simp [reindexIsometry, reindexL2]

@[simp] theorem leftRegular_apply (g : G) (ξ : ScalarL2 G) (x : G) :
    leftRegular g ξ x = ξ (g⁻¹ * x) := rfl

def Word (I : Type u) : ℕ → Type u
  | 0 => PUnit
  | n + 1 => I × Word I n

instance wordFintype {I : Type*} [Fintype I] : (n : ℕ) → Fintype (Word I n)
  | 0 => inferInstanceAs (Fintype PUnit)
  | n + 1 => by
    letI : Fintype (Word I n) := wordFintype n
    exact inferInstanceAs (Fintype (I × Word I n))

def wordProduct {I : Type*} (s : I → G) : (n : ℕ) → Word I n → G
  | 0, _ => 1
  | n + 1, w => s w.1 * wordProduct s n w.2

end Dixmier

end

end OAI


