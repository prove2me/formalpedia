-- Prove2me | Definitions.Def_OAI_Combinatorics_EuclideanRamsey_FiniteEuclidean
-- name    : OAI_Combinatorics_EuclideanRamsey_FiniteEuclidean
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T01:31:17.670998+00:00
-- url     : https://prove2.me/theorems/2a4d8025-d16c-4bda-a4dd-7b9b255e4a5e
-- title:
--   The Euclidean space of finitely supported real sequences, coordinate blocks and orthogonal concatenation
-- statement:
--   This file builds a countably infinite-dimensional Euclidean space that contains every $\mathbb{R}^d$ isometrically, together with isometric maps into it.
--
--   1. **The space.** $\mathbb{R}^{(\mathbb{N})}$ is the real vector space of sequences $x=(x_0,x_1,x_2,\dots)$ of real numbers with only finitely many nonzero terms, equipped with
--   $$\langle x,y\rangle=\sum_{n\ge0}x_ny_n,\qquad \|x\|^2=\sum_{n\ge0}x_n^2 .$$
--   It is a real inner product space (not complete). The file records that the inner product may be computed as a sum over any finite set containing the support of $x$, and that taking coordinates is additive and homogeneous.
--   2. **Reindexing.** For an injective map $f:\mathbb{N}\to\mathbb{N}$, $T_f$ is the linear isometry of $\mathbb{R}^{(\mathbb{N})}$ that moves the $n$-th coordinate to position $f(n)$: $(T_fx)_{f(n)}=x_n$, and $(T_fx)_m=0$ for $m$ outside the image of $f$.
--   3. **Blocks.** For $j\in\mathbb{N}$, $B_j=T_{f_j}$ with $f_j(n)=\mathrm{pair}(j,n)$, where $\mathrm{pair}:\mathbb{N}\times\mathbb{N}\to\mathbb{N}$ is the standard pairing bijection. Different blocks have disjoint coordinate supports, hence mutually orthogonal images.
--   4. **Embedding of $\mathbb{R}^d$.** For $d\in\mathbb{N}$, $\iota_d:\mathbb{R}^d\to\mathbb{R}^{(\mathbb{N})}$, $(x_0,\dots,x_{d-1})\mapsto(x_0,\dots,x_{d-1},0,0,\dots)$, is a linear isometry from Euclidean space $\mathbb{R}^d$; the $i$-th coordinate of $\iota_d(x)$ is $x_i$.
--   5. **Concatenation.** For a finite list $(y^{(0)},\dots,y^{(m-1)})$ of elements of $\mathbb{R}^{(\mathbb{N})}$,
--   $$\operatorname{flatten}\bigl(y^{(0)},\dots,y^{(m-1)}\bigr)=\sum_{i=0}^{m-1}B_i\bigl(y^{(i)}\bigr),$$
--   which places the $i$-th vector in the $i$-th block.
--   6. **Unit vectors.** $u_n\in\mathbb{R}^{(\mathbb{N})}$ is the sequence with $1$ in position $n$ and $0$ elsewhere.
--
--   This space serves as a universal ambient Euclidean space: congruent copies of a configuration can be placed in it regardless of dimension, colourings of it can be studied directly, and a compactness argument transfers monochromatic copies back to a finite-dimensional $\mathbb{R}^D$. Blocks and concatenation allow independent pieces of a construction to be combined orthogonally, so that squared distances add.
--
--   **Formalization Note** `FiniteEuclidean` is `ℕ →₀ ℝ`; its inner product `product` is installed through `InnerProductSpace.Core` (instance `core`), with lemmas `product_eq_sum`, `norm_sq`, `coords_add`, `coords_sub` and `coords_smul`, where `coords` is the identity view as a finitely supported function. The maps are `reindex f hf`, `block j` (using `Nat.pair`), `embed d` (with `embed_apply`), `flatten` on a `List FiniteEuclidean`, and `unit n`. The private abbreviation `Finsupp.mapDomain_apply_of_injective` is a compatibility alias for `Finsupp.mapDomain_apply`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/EuclideanRamsey/FiniteEuclidean.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/EuclideanRamsey/FiniteEuclidean.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the EuclideanRamsey mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_EuclideanRamsey
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorNecessity
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorDescent
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SmoothingKernel
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Hessian
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_DifferentialSplitting
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SmoothingMatrix
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_LatticeMoments
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Discretization
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_AdicLifting
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorPresentation
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SignedRows

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

def reindex (f : ℕ → ℕ) (hf : Function.Injective f) : FiniteEuclidean →ₗᵢ[ℝ] FiniteEuclidean where
  toLinearMap :=
    { toFun := fun x => (coords x).mapDomain f
      map_add' := fun x y => Finsupp.mapDomain_add
      map_smul' := fun c x => Finsupp.mapDomain_smul c (coords x) }
  norm_map' x := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [norm_sq,norm_sq]
    exact Finsupp.sum_mapDomain_index_inj hf

def block (j : ℕ) : FiniteEuclidean →ₗᵢ[ℝ] FiniteEuclidean :=
  reindex (Nat.pair j) (fun _m _n h => (Nat.pair_eq_pair.mp h).2)
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

noncomputable def flatten (l : List FiniteEuclidean) : FiniteEuclidean :=
  ∑ i : Fin l.length,block i (l.get i)

end FiniteEuclidean
end EuclideanRamsey
namespace EuclideanRamsey
namespace FiniteEuclidean
open scoped BigOperators RealInnerProductSpace

noncomputable def unit (n : ℕ) : FiniteEuclidean := Finsupp.single n 1
end FiniteEuclidean
end EuclideanRamsey

end

end OAI


