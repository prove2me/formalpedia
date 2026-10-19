-- Prove2me | Definitions.Def_OAI_Combinatorics_EuclideanRamsey_FiniteEuclidean__EuclideanRamseySpherical
-- name    : OAI_Combinatorics_EuclideanRamsey_FiniteEuclidean__EuclideanRamseySpherical
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T06:07:26.920527+00:00
-- url     : https://prove2.me/theorems/ccf778aa-0aa7-4c4c-9c7e-921a70c055e4
-- title:
--   The Euclidean space of finitely supported sequences
-- statement:
--   A finite configuration $a=(a_0,\dots,a_{s-1})$ of points of $\mathbb R^d$ is Ramsey when, for every number of colours $r$, some dimension $D$ has the property that every $r$-colouring of $\mathbb R^D$ contains a monochromatic copy of $a$ congruent to it. This module is part of the proof that Ramsey configurations lie on a sphere.
--
--   Let $E$ be the real vector space of finitely supported real sequences $x=(x_0,x_1,\dots)$. This module makes $E$ an inner product space with
--   $$
--   \langle x,y\rangle=\sum_{n\ge0}x_ny_n,\qquad\|x\|^2=\sum_{n\ge0}x_n^2 .
--   $$
--   Coordinates are additive and homogeneous. For every $d$ there is a linear isometry $\mathbb R^d\to E$, placing a vector in the first $d$ coordinates. So $E$ contains a copy of every Euclidean space, and congruent copies of a configuration can be chosen in $E$ without fixing a dimension in advance.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/EuclideanRamsey/FiniteEuclidean.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/EuclideanRamsey/FiniteEuclidean.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the EuclideanRamseySpherical mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_EuclideanRamseySpherical
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorNecessity__EuclideanRamseySpherical
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Hessian__EuclideanRamseySpherical
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_DifferentialSplitting__EuclideanRamseySpherical
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_LatticeMoments__EuclideanRamseySpherical
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_AdicLifting__EuclideanRamseySpherical
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorPresentation__EuclideanRamseySpherical

-- Lean 4.34 name of Finsupp.mapDomain_apply (same arguments) in Mathlib 0df444a.
private abbrev Finsupp.mapDomain_apply_of_injective := @Finsupp.mapDomain_apply

namespace OAI

universe uValue

noncomputable section

open scoped TensorProduct RealInnerProductSpace
open scoped BigOperators
open Real Filter Topology MeasureTheory Polynomial
open Matrix MeasureTheory
open MeasureTheory
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator
open MeasureTheory Matrix
open scoped TensorProduct
open scoped BigOperators Pointwise Topology
open MeasureTheory Filter
open scoped BigOperators Pointwise
open scoped BigOperators Topology
open scoped TensorProduct BigOperators
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator

open scoped BigOperators RealInnerProductSpace
namespace EuclideanRamsey

def FiniteEuclidean := ℕ →₀ ℝ
namespace FiniteEuclidean
instance : AddCommGroup FiniteEuclidean := inferInstanceAs (AddCommGroup (ℕ →₀ ℝ))
instance : Module ℝ FiniteEuclidean := inferInstanceAs (Module ℝ (ℕ →₀ ℝ))
def coords (x : FiniteEuclidean) : ℕ →₀ ℝ := x

def product (x y : FiniteEuclidean) : ℝ :=
  (coords x).sum (fun n r => r*coords y n)
lemma product_eq_sum (x y : FiniteEuclidean) {s : Finset ℕ}
    (hx : (coords x).support ⊆ s) : product x y=∑ n∈s,coords x n*coords y n :=
  Finsupp.sum_of_support_subset _ hx _ (by simp)
instance core : InnerProductSpace.Core ℝ FiniteEuclidean where
  inner := product
  conj_inner_symm x y := by
    change product y x=product x y
    rw [product_eq_sum y x ((Finset.subset_union_right : (coords y).support ⊆ (coords x).support ∪ (coords y).support)),
      product_eq_sum x y ((Finset.subset_union_left : (coords x).support ⊆ (coords x).support ∪ (coords y).support))]
    apply Finset.sum_congr rfl
    intro n _; ring
  re_inner_nonneg x := by
    change 0 ≤ (coords x).sum (fun n r => r*coords x n)
    exact Finset.sum_nonneg (fun n _ => mul_self_nonneg _)
  add_left x y z := by
    change ((coords x)+(coords y)).sum _ = _
    exact Finsupp.sum_add_index (by simp) (by intro n _ r t; exact add_mul _ _ _)
  smul_left x y r := by
    change (r • coords x).sum (fun n t => t*coords y n)=r*product x y
    rw [Finsupp.sum_smul_index (by simp)]
    simp only [product,Finsupp.mul_sum,mul_assoc]
  definite x h := by
    change (coords x).sum (fun n r => r*coords x n)=0 at h
    have hs : ∀ n∈(coords x).support,coords x n*coords x n=0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun n _ => mul_self_nonneg _)).mp h
    apply Finsupp.ext
    intro n
    by_cases hn : n∈(coords x).support
    · exact mul_self_eq_zero.mp (hs n hn)
    · exact Finsupp.notMem_support_iff.mp hn
instance : NormedAddCommGroup FiniteEuclidean := InnerProductSpace.Core.toNormedAddCommGroup (𝕜:=ℝ)
instance : InnerProductSpace ℝ FiniteEuclidean := InnerProductSpace.ofCore core.toCore
lemma norm_sq (x : FiniteEuclidean) : ‖x‖^2=(coords x).sum (fun _ r => r^2) := by
  rw [← real_inner_self_eq_norm_sq]
  change product x x = _
  simp [product,Finsupp.sum,pow_two]
@[simp] lemma coords_add (x y : FiniteEuclidean) : coords (x+y)=coords x+coords y := rfl
@[simp] lemma coords_sub (x y : FiniteEuclidean) : coords (x-y)=coords x-coords y := rfl
@[simp] lemma coords_smul (c : ℝ) (x : FiniteEuclidean) : coords (c • x)=c • coords x := rfl

end FiniteEuclidean
end EuclideanRamsey
namespace EuclideanRamsey
namespace FiniteEuclidean
open scoped BigOperators RealInnerProductSpace

noncomputable def embed (d : ℕ) : EuclideanSpace ℝ (Fin d) →ₗᵢ[ℝ] FiniteEuclidean where
  toLinearMap :=
    { toFun := fun x => (Finsupp.equivFunOnFinite.symm (fun i => x i)).mapDomain Fin.val
      map_add' := by
        intro x y
        change Finsupp.mapDomain _ _ = _ + _
        rw [← Finsupp.mapDomain_add]
        congr 1
        ext i; simp
      map_smul' := by
        intro r x
        change Finsupp.mapDomain _ _ = r • (_ : ℕ →₀ ℝ)
        rw [← Finsupp.mapDomain_smul]
        congr 1
        ext i; simp }
  norm_map' x := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [norm_sq,EuclideanSpace.norm_sq_eq]
    change (Finsupp.mapDomain Fin.val _).sum _ = _
    rw [Finsupp.sum_mapDomain_index_inj Fin.val_injective]
    rw [Finsupp.sum_fintype]
    · simp [Real.norm_eq_abs,sq_abs]
    · intro _; simp

@[simp] lemma embed_apply (d : ℕ) (x : EuclideanSpace ℝ (Fin d)) (i : Fin d) :
    coords (embed d x) i.val=x i := by
  exact Finsupp.mapDomain_apply_of_injective Fin.val_injective _ i

end FiniteEuclidean
end EuclideanRamsey
namespace EuclideanRamsey
namespace FiniteEuclidean
open scoped BigOperators RealInnerProductSpace

end FiniteEuclidean
end EuclideanRamsey

end

end OAI


