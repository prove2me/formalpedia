-- Prove2me | Definitions.Def_OAI_Combinatorics_EuclideanRamsey_CorrectionPaths
-- name    : OAI_Combinatorics_EuclideanRamsey_CorrectionPaths
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T01:52:35.52367+00:00
-- url     : https://prove2.me/theorems/ccb4b0eb-8517-44f8-8126-f4b6de350b33
-- title:
--   Maximal single-coordinate fraction cost as a normal cost, and coordinate permutations of $\mathbb{R}^\ell$
-- statement:
--   Let $G$ be a group and $\iota$ a finite index set, with tuples in $G^\iota$ multiplied coordinatewise. A *graded path system* $P$ is a relation $\mathrm{Holds}(u,n)$ between tuples $u\in G^\iota$ and degrees $n\in\mathbb{N}$ that contains every constant tuple in degree $0$ and is closed under products with degrees adding. For $i\in\iota$ and $g\in G$ let $e_i(g)\in G^\iota$ be the tuple with $g$ in coordinate $i$ and $1$ elsewhere. The elements $g$ for which $e_i(g)=uv^{-1}$ with $\mathrm{Holds}(u,m)$ and $\mathrm{Holds}(v,n)$ for some $m,n$ form a normal subgroup $\Phi_i\le G$ (the single-coordinate fractions), and the *single cost* $c_i(g)\in\mathbb{N}$ is the least $c$ admitting such a representation with $m+n\le c$.
--
--   1. **Maximal cost.** $c_{\max}(g)=\max_{i\in\iota}c_i(g)$; in particular $c_i(g)\le c_{\max}(g)$ for every $i$.
--   2. **Normal cost from the maximal cost.** Let $L\le G$ be a normal subgroup with $L\le\Phi_i$ for every $i\in\iota$. Then $g\mapsto c_{\max}(g)$, viewed as a real number, is a normal cost on $L$: it is nonnegative, vanishes at $1$, and for $g,h\in L$ and $k\in G$
--   $$c_{\max}(g^{-1})=c_{\max}(g),\qquad c_{\max}(kgk^{-1})=c_{\max}(g),\qquad c_{\max}(gh)\le c_{\max}(g)+c_{\max}(h).$$
--   3. **Coordinate permutations.** For a permutation $\sigma$ of $\{0,\dots,\ell-1\}$, $\pi_\sigma:\mathbb{R}^\ell\to\mathbb{R}^\ell$ is the linear isometry of Euclidean space given by $(\pi_\sigma x)_j=x_{\sigma^{-1}(j)}$; the identity permutation gives the identity map.
--
--   The maximal cost measures how many path letters are needed to correct one coordinate at a time. Combined with orbit averaging, it bounds the total degree of the correcting paths, so that a tuple of words can be made to carry two paths whose weights have a prescribed small ratio. Coordinate permutations describe point families in $\mathbb{R}^\ell$ that agree up to a permutation of coordinates.
--
--   **Formalization Note** `GradedPaths.maxCost` is `Finset.univ.sup` of `singleCost`, so it equals $0$ when $\iota$ is empty; `singleCost` is a natural-number `sInf`, which is $0$ when $g\notin\Phi_i$, but the cost axioms are only claimed on `L`. `normalCost L hL` is the resulting `NormalCost L`, with `hL : ∀ i, L ≤ singleFractions P.monoid P.diagonal i`. `permute σ` is `LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ σ`; `permute_apply` and `permute_one` are simp lemmas.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/EuclideanRamsey/CorrectionPaths.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/EuclideanRamsey/CorrectionPaths.lean by skeleton subtraction
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
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_FiniteEuclidean
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_PathFractions
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_DerivedFractions
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_PathWords
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_UltrafilterStrings
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_PathSynchronization
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_CornerGroup
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_ColoringCompactness
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_NormalCost
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_OrbitAveraging

namespace OAI

universe uGroup uIndex uAction uPoint

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
open Filter
open Set

namespace EuclideanRamsey
open scoped BigOperators
variable {G : Type uGroup} {ι : Type uIndex} [Group G] [Fintype ι] [DecidableEq ι]
namespace GradedPaths
variable (P : GradedPaths ι G) (L : Subgroup G) [L.Normal]
variable (hL : ∀ i,L ≤ singleFractions P.monoid P.diagonal i)

def maxCost (g : G) : ℕ := Finset.univ.sup (fun i => P.singleCost i g)
lemma single_le_maxCost (i : ι) (g : G) : P.singleCost i g ≤ P.maxCost g :=
  Finset.le_sup (f := fun j => P.singleCost j g) (Finset.mem_univ i)
noncomputable def normalCost : NormalCost L where
  cost g := P.maxCost g
  nonneg g := Nat.cast_nonneg _
  one := by simp [maxCost,P.singleCost_one]
  inv g hg := by
    congr 1
    apply Finset.sup_congr rfl
    intro i _
    exact P.singleCost_inv i (hL i hg)
  conj g hg k := by
    congr 1
    apply Finset.sup_congr rfl
    intro i _
    exact P.singleCost_conjugate i (hL i hg) k
  mul g hg h hh := by
    rw [← Nat.cast_add]
    apply Nat.cast_le.mpr
    apply Finset.sup_le
    intro i _
    exact (P.singleCost_mul i (hL i hg) (hL i hh)).trans
      (add_le_add (P.single_le_maxCost i g) (P.single_le_maxCost i h))

end GradedPaths
end EuclideanRamsey
namespace EuclideanRamsey
open scoped BigOperators
variable {ι : Type uIndex} {H : Type uAction} {X : Type uPoint} [Fintype ι] [DecidableEq ι]
variable [Group H] [MulAction H X] [Fintype H] [Fintype X]

end EuclideanRamsey
namespace EuclideanRamsey
open scoped BigOperators

noncomputable def permute {ℓ : ℕ} (σ : Equiv.Perm (Fin ℓ)) :
    EuclideanSpace ℝ (Fin ℓ) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin ℓ) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ σ
@[simp] lemma permute_apply {ℓ : ℕ} (σ : Equiv.Perm (Fin ℓ))
    (x : EuclideanSpace ℝ (Fin ℓ)) (j : Fin ℓ) : permute σ x j=x (σ.symm j) := rfl
@[simp] lemma permute_one {ℓ : ℕ} (x : EuclideanSpace ℝ (Fin ℓ)) :
    permute 1 x=x := by ext j; rfl

end EuclideanRamsey

end

end OAI


