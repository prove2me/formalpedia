-- Prove2me | Definitions.Def_OAI_Combinatorics_EuclideanRamsey_PathFractions__EuclideanRamseySpherical
-- name    : OAI_Combinatorics_EuclideanRamsey_PathFractions__EuclideanRamseySpherical
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T06:09:13.021004+00:00
-- url     : https://prove2.me/theorems/85e30750-8666-454c-8986-bbefa3ef0df8
-- title:
--   Right fractions of a submonoid of tuples and graded path systems
-- statement:
--   A finite configuration $a=(a_0,\dots,a_{s-1})$ of points of $\mathbb R^d$ is Ramsey when, for every number of colours $r$, some dimension $D$ has the property that every $r$-colouring of $\mathbb R^D$ contains a monochromatic copy of $a$ congruent to it. This module is part of the proof that Ramsey configurations lie on a sphere.
--
--   Let $G$ be a group and $\iota$ an index set. Tuples in $G^\iota$ are multiplied coordinatewise, and $e_i(g)$ denotes the tuple with $g$ in coordinate $i$ and $1$ elsewhere. Let $M\le G^\iota$ be a submonoid.
--
--   1. **Right fractions.** A tuple $z$ is a right fraction of $M$ when $z=uv^{-1}$ with $u,v\in M$. The identity is one, inverses of right fractions are right fractions, and if $M$ contains all constant tuples then conjugates by constants and products with single-coordinate right fractions are right fractions.
--   2. **Diagonal and pair inverses.** $M$ has the diagonal when it contains every constant tuple. It has pair inverses when, for all $i\ne j$ and $v\in M$, some $b\in M$ satisfies $v_ib_i=1=v_jb_j$.
--   3. **Single fractions.** If $M$ has the diagonal, $N_i=\{g:\ e_i(g)\text{ is a right fraction of }M\}$ is a normal subgroup of $G$.
--   4. **Graded path systems.** A relation "$u$ holds at grade $n$" that holds for constant tuples at grade $0$ and is closed under products with grades adding. The tuples holding at some grade form a submonoid with the diagonal.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/EuclideanRamsey/PathFractions.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/EuclideanRamsey/PathFractions.lean by skeleton subtraction
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
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_FiniteEuclidean__EuclideanRamseySpherical

namespace OAI

universe uGroup uIndex

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

open scoped BigOperators
namespace EuclideanRamsey
section Fractions
variable {G : Type uGroup} {ι : Type uIndex} [Group G] [DecidableEq ι]

def RightFraction (M : Submonoid (ι → G)) (z : ι → G) : Prop :=
  ∃ u ∈ M,∃ v ∈ M,z=u*v⁻¹

def HasDiagonal (M : Submonoid (ι → G)) : Prop := ∀ g : G,(fun _ => g)∈M

def PairInverse (M : Submonoid (ι → G)) : Prop :=
  ∀ i j : ι,i≠j → ∀ v∈M,∃ b∈M,v i*b i=1 ∧ v j*b j=1

omit [DecidableEq ι] in
lemma RightFraction.one (M : Submonoid (ι → G)) : RightFraction M 1 :=
  ⟨1,M.one_mem,1,M.one_mem,by simp⟩
omit [DecidableEq ι] in
lemma RightFraction.inv {M : Submonoid (ι → G)} {z : ι → G}
    (h : RightFraction M z) : RightFraction M z⁻¹ := by
  obtain ⟨u,hu,v,hv,rfl⟩ := h
  exact ⟨v,hv,u,hu,by group⟩
omit [DecidableEq ι] in
lemma RightFraction.conjugate {M : Submonoid (ι → G)} (hM : HasDiagonal M)
    {z : ι → G} (h : RightFraction M z) (g : G) :
    RightFraction M (fun i => g*z i*g⁻¹) := by
  obtain ⟨u,hu,v,hv,rfl⟩ := h
  refine ⟨(fun _ => g)*u,M.mul_mem (hM g) hu,(fun _ => g)*v,M.mul_mem (hM g) hv,?_⟩
  ext i
  simp only [Pi.mul_apply,Pi.inv_apply]
  group

lemma conjugate_single (i : ι) (g h : G) :
    (fun j => g*(Pi.mulSingle i h : ι → G) j*g⁻¹)=Pi.mulSingle i (g*h*g⁻¹) := by
  ext j
  by_cases hj : j=i <;> simp [hj]

lemma RightFraction.mul_single {M : Submonoid (ι → G)} (hM : HasDiagonal M)
    {z : ι → G} (hz : RightFraction M z) (i : ι) {g : G}
    (hg : RightFraction M (Pi.mulSingle i g)) : RightFraction M (z*Pi.mulSingle i g) := by
  obtain ⟨u,hu,v,hv,rfl⟩ := hz
  have hh := hg.conjugate hM (v i)⁻¹
  rw [conjugate_single,inv_inv] at hh
  obtain ⟨a,ha,b,hb,he⟩ := hh
  refine ⟨u*a,M.mul_mem hu ha,v*b,M.mul_mem hv hb,?_⟩
  have ht : v⁻¹*Pi.mulSingle i g = Pi.mulSingle i ((v i)⁻¹*g*v i)*v⁻¹ := by
    ext j
    by_cases hj : j=i
    · subst j; simp
    · simp [Pi.mulSingle_eq_of_ne hj]
  rw [mul_assoc,ht,he]
  group

def singleFractions (M : Submonoid (ι → G)) (hM : HasDiagonal M) (i : ι) : Subgroup G where
  carrier := {g | RightFraction M (Pi.mulSingle i g)}
  one_mem' := by simpa using RightFraction.one M
  mul_mem' {a b} ha hb := by
    change RightFraction M (Pi.mulSingle i (a*b))
    rw [Pi.mulSingle_mul]
    exact ha.mul_single hM i hb
  inv_mem' {a} ha := by
    change RightFraction M (Pi.mulSingle i a⁻¹)
    rw [Pi.mulSingle_inv]
    exact ha.inv

instance singleFractions_normal (M : Submonoid (ι → G)) (hM : HasDiagonal M) (i : ι) :
    (singleFractions M hM i).Normal where
  conj_mem g hg k := by
    change RightFraction M (Pi.mulSingle i (k*g*k⁻¹))
    rw [← conjugate_single]
    exact hg.conjugate hM k

end Fractions
end EuclideanRamsey
namespace EuclideanRamsey
open scoped BigOperators
variable {G : Type uGroup} {ι : Type uIndex} [Group G] [DecidableEq ι]

structure GradedPaths (ι : Type uIndex) (G : Type uGroup) [Group G] where
  Holds : (ι → G) → ℕ → Prop
  diag : ∀ g,Holds (fun _ => g) 0
  mul : ∀ {u v m n},Holds u m → Holds v n → Holds (u*v) (m+n)
namespace GradedPaths
variable (P : GradedPaths ι G)
def monoid : Submonoid (ι → G) where
  carrier := {u | ∃ n,P.Holds u n}
  one_mem' := ⟨0,P.diag 1⟩
  mul_mem' := by rintro u v ⟨m,hm⟩ ⟨n,hn⟩; exact ⟨m+n,P.mul hm hn⟩
omit [DecidableEq ι] in
lemma diagonal : HasDiagonal P.monoid := fun g => ⟨0,P.diag g⟩

end GradedPaths
end EuclideanRamsey

end

end OAI


