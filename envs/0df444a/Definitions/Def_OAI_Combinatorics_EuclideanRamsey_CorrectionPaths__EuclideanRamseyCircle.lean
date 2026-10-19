-- Prove2me | Definitions.Def_OAI_Combinatorics_EuclideanRamsey_CorrectionPaths__EuclideanRamseyCircle
-- name    : OAI_Combinatorics_EuclideanRamsey_CorrectionPaths__EuclideanRamseyCircle
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T12:22:10.505634+00:00
-- url     : https://prove2.me/theorems/78ed1906-3f7c-48c4-898c-35f8869bb92c
-- title:
--   Maximal single-coordinate fraction cost as a normal cost, and coordinate permutations of $\mathbb{R}^\ell$
-- statement:
--   Let $G$ be a group and $\iota$ a finite index set. Tuples in $G^\iota$ are multiplied coordinatewise, and for $i\in\iota$ and $g\in G$ we write $e_i(g)\in G^\iota$ for the tuple with $g$ in coordinate $i$ and $1$ elsewhere. A *graded path system* $P$ is a relation "$u$ holds at grade $n$" between tuples $u\in G^\iota$ and natural numbers $n$ such that every constant tuple holds at grade $0$ and, if $u$ holds at grade $m$ and $v$ at grade $n$, then $uv$ holds at grade $m+n$. Let $M_P$ be the monoid of tuples holding at some grade, and for $i\in\iota$ let
--   $$N_i=\{\,g\in G:\ e_i(g)=uv^{-1}\text{ for some }u,v\in M_P\,\},$$
--   a normal subgroup of $G$. The *single cost* $\operatorname{cost}_i(g)\in\mathbb{N}$ is the least $c$ such that $e_i(g)=uv^{-1}$ with $u$ holding at grade $m$, $v$ holding at grade $n$ and $m+n\le c$ (and $0$ if there is no such representation).
--
--   1. **Maximal cost.** $c_{\max}(g)=\max_{i\in\iota}\operatorname{cost}_i(g)$ for $g\in G$ (equal to $0$ if $\iota$ is empty); in particular $\operatorname{cost}_i(g)\le c_{\max}(g)$ for every $i\in\iota$.
--   2. **Normal cost from the maximal cost.** Let $L\le G$ be a subgroup with $L\subseteq N_i$ for every $i\in\iota$. Then $g\mapsto c_{\max}(g)$, viewed as a real-valued function on $G$, is a normal cost on $L$: it is nonnegative, vanishes at $1$, and for all $g,h\in L$ and $k\in G$
--   $$c_{\max}(g^{-1})=c_{\max}(g),\qquad c_{\max}(kgk^{-1})=c_{\max}(g),\qquad c_{\max}(gh)\le c_{\max}(g)+c_{\max}(h).$$
--   3. **Coordinate permutations.** For $\ell\in\mathbb{N}$ and a permutation $\sigma$ of $\{0,1,\dots,\ell-1\}$, the map $\pi_\sigma:\mathbb{R}^\ell\to\mathbb{R}^\ell$ given by $(\pi_\sigma x)_j=x_{\sigma^{-1}(j)}$ is a linear isometry of Euclidean space onto itself, and $\pi_{\mathrm{id}}$ is the identity map.
--
--   In the construction of monochromatic congruent copies, $G$ is the free group whose generators are the points of an infinite-dimensional Euclidean space, $P$ is the system of unit words of an injective configuration (products of constant tuples and of letter tuples of congruent copies, graded by the number of copies), and $L$ is a term of the derived series of the augmentation kernel. The maximal cost then measures how many copies are needed to correct each coordinate of a tuple separately, and combined with orbit averaging it bounds the total grade of the correcting words; this yields one tuple of words carrying two weighted paths whose weights have a prescribed small ratio. Coordinate permutations describe the situation in which corresponding points of two families in $\mathbb{R}^\ell$ differ by a permutation of coordinates, which is how such pairs of paths are produced from an algebraic criterion.
--
--   **Formalization Note** `GradedPaths.maxCost` is `Finset.univ.sup` of `singleCost` (with `[Fintype ι] [DecidableEq ι]`), and `single_le_maxCost` is the inequality in item 1. `singleCost` is a natural-number `sInf`, which is $0$ for $g\notin N_i$, but the cost axioms are only asserted on `L`. `normalCost L hL` is the resulting `NormalCost L`, with `hL : ∀ i, L ≤ singleFractions P.monoid P.diagonal i`; the construction uses only these inclusions. `permute σ` is `LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ σ` on `EuclideanSpace ℝ (Fin ℓ)`, and `permute_apply`, `permute_one` are simp lemmas.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/EuclideanRamsey/CorrectionPaths.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/EuclideanRamsey/CorrectionPaths.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the EuclideanRamseyCircle mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_EuclideanRamseyCircle
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Model__EuclideanRamseyCircle
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_CircleInterpolation
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_CircleRows
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_CircleExtension
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorNecessity__EuclideanRamseyCircle
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorDescent__EuclideanRamseyCircle
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SmoothingKernel__EuclideanRamseyCircle
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Hessian__EuclideanRamseyCircle
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_DifferentialSplitting__EuclideanRamseyCircle
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SmoothingMatrix__EuclideanRamseyCircle
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_LatticeMoments__EuclideanRamseyCircle
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Discretization__EuclideanRamseyCircle
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_AdicLifting__EuclideanRamseyCircle
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorPresentation__EuclideanRamseyCircle
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SignedRows__EuclideanRamseyCircle
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_FiniteEuclidean__EuclideanRamseyCircle
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_PathFractions__EuclideanRamseyCircle
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_DerivedFractions__EuclideanRamseyCircle
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_PathWords__EuclideanRamseyCircle
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_UltrafilterStrings__EuclideanRamseyCircle
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_PathSynchronization__EuclideanRamseyCircle
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_CornerGroup__EuclideanRamseyCircle
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_ColoringCompactness__EuclideanRamseyCircle
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_NormalCost__EuclideanRamseyCircle
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_OrbitAveraging__EuclideanRamseyCircle

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


