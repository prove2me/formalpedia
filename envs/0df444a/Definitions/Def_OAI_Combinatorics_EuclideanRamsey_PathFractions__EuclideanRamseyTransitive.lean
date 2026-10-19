-- Prove2me | Definitions.Def_OAI_Combinatorics_EuclideanRamsey_PathFractions__EuclideanRamseyTransitive
-- name    : OAI_Combinatorics_EuclideanRamsey_PathFractions__EuclideanRamseyTransitive
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T04:08:50.711924+00:00
-- url     : https://prove2.me/theorems/45d101c0-2823-49af-a65b-80b3184e432e
-- title:
--   Right fractions in tuple monoids, single-coordinate fraction subgroups and graded path costs
-- statement:
--   This file develops a calculus of fractions $uv^{-1}$ of tuples of group elements, together with a cost that measures how cheaply a single coordinate of a tuple can be changed.
--
--   Let $G$ be a group and $\iota$ an index set. The set $G^\iota$ of tuples $z=(z_i)_{i\in\iota}$ is a group under coordinatewise multiplication. For $i\in\iota$ and $g\in G$ let $e_i(g)\in G^\iota$ be the tuple with $g$ in coordinate $i$ and $1$ in every other coordinate. Let $M\subseteq G^\iota$ be a submonoid.
--
--   1. **Right fractions.** A tuple $z\in G^\iota$ is a *right fraction* of $M$ if $z=uv^{-1}$ for some $u,v\in M$.
--   2. **Diagonal.** $M$ *has the diagonal* if it contains every constant tuple $(g)_{i\in\iota}$ with $g\in G$.
--   3. **Pair inverses.** $M$ *has pair inverses* if for any two indices $i\neq j$ and every $v\in M$ there is $b\in M$ with $v_ib_i=1$ and $v_jb_j=1$.
--   4. **Single-coordinate fraction subgroup.** If $M$ has the diagonal, then for every $i\in\iota$ the set
--   $$N_i(M)=\{\,g\in G:\ e_i(g)\text{ is a right fraction of }M\,\}$$
--   is a subgroup of $G$, and this subgroup is normal.
--   5. **Graded path systems.** A *graded path system* $P$ on $G^\iota$ is a relation "$u$ holds at grade $n$" between tuples $u\in G^\iota$ and natural numbers $n$ such that every constant tuple holds at grade $0$, and whenever $u$ holds at grade $m$ and $v$ holds at grade $n$, the product $uv$ holds at grade $m+n$. The tuples that hold at some grade form a submonoid $M_P\subseteq G^\iota$, and $M_P$ has the diagonal.
--   6. **Bounded fractions.** For $c\in\mathbb{N}$, a tuple $z$ is a *$P$-fraction of cost at most $c$* if $z=uv^{-1}$ where $u$ holds at grade $m$, $v$ holds at grade $n$, and $m+n\le c$.
--   7. **Single cost.** For $i\in\iota$ and $g\in G$,
--   $$\operatorname{cost}_i(g)=\min\bigl\{c\in\mathbb{N}:\ e_i(g)\text{ is a }P\text{-fraction of cost at most }c\bigr\},$$
--   with the value $0$ when no such $c$ exists.
--
--   The file also records the elementary closure properties of these notions. For every submonoid $M$, the identity tuple is a right fraction and inverses of right fractions are right fractions. If $M$ has the diagonal, then conjugating a right fraction coordinatewise by a fixed $g\in G$ gives a right fraction (note that $(g\,e_i(h)_j\,g^{-1})_{j\in\iota}=e_i(ghg^{-1})$), and if $z$ and $e_i(g)$ are right fractions then so is $z\,e_i(g)$. For a graded path system $P$: every right fraction of $M_P$ is a $P$-fraction of some finite cost; the identity tuple has cost at most $0$; cost bounds are preserved by inversion and by coordinatewise conjugation with a constant; and if $z$ has cost at most $c$ and $e_i(g)$ has cost at most $c'$, then $z\,e_i(g)$ has cost at most $c+c'$. Consequently $\operatorname{cost}_i(g)\le c$ whenever $e_i(g)$ has cost at most $c$, the minimum is attained for every $g\in N_i(M_P)$, and for $g,h\in N_i(M_P)$ and $k\in G$
--   $$\operatorname{cost}_i(1)=0,\qquad \operatorname{cost}_i(g^{-1})=\operatorname{cost}_i(g),\qquad \operatorname{cost}_i(kgk^{-1})=\operatorname{cost}_i(g),\qquad \operatorname{cost}_i(gh)\le\operatorname{cost}_i(g)+\operatorname{cost}_i(h).$$
--
--   These notions isolate the group-theoretic core of a construction of monochromatic congruent copies in Euclidean Ramsey theory. There $G$ is the free group whose generators are the points of an infinite-dimensional Euclidean space, $\iota$ indexes the points of a configuration, a tuple holds at grade $n$ when it is a product of constant tuples and of $n$ tuples of letters read off congruent copies of the configuration, and $\operatorname{cost}_i$ is a conjugation-invariant, subadditive length on the normal subgroup $N_i(M_P)$ that bounds how many copies are needed to change one coordinate while keeping the others fixed.
--
--   **Formalization Note** The tuple $e_i(g)$ is `Pi.mulSingle i g`, which needs `[DecidableEq ι]`. The definitions are `RightFraction M z`, `HasDiagonal M`, `PairInverse M`, `singleFractions M hM i : Subgroup G` (taking a proof `hM : HasDiagonal M`, with normality given by the instance `singleFractions_normal`), the structure `GradedPaths ι G` with fields `Holds`, `diag`, `mul`, and `GradedPaths.monoid`, `GradedPaths.BoundedFraction` and `GradedPaths.singleCost`. The latter is an `sInf` of a set of natural numbers, hence $0$ when the set is empty. The lemmas `RightFraction.one`, `RightFraction.inv`, `RightFraction.conjugate`, `conjugate_single`, `RightFraction.mul_single`, `diagonal`, `bounded_exists`, `bounded_one`, `bounded_inv`, `bounded_conjugate`, `bounded_mul_single`, `singleCost_bounded`, `singleCost_le`, `singleCost_one`, `singleCost_inv`, `singleCost_conjugate` and `singleCost_mul` are the closure facts listed above.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/EuclideanRamsey/PathFractions.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/EuclideanRamsey/PathFractions.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the EuclideanRamseyTransitive mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Model
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorNecessity__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorDescent__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SmoothingKernel__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Hessian__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_DifferentialSplitting__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SmoothingMatrix__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_LatticeMoments__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Discretization__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_AdicLifting__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorPresentation__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SignedRows__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_FiniteEuclidean__EuclideanRamseyTransitive

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

def BoundedFraction (z : ι → G) (c : ℕ) : Prop :=
  ∃ (u v : ι → G) (m n : ℕ),P.Holds u m ∧ P.Holds v n ∧ z=u*v⁻¹ ∧ m+n≤c
omit [DecidableEq ι] in
lemma bounded_exists {z : ι → G} (h : RightFraction P.monoid z) :
    ∃ c,P.BoundedFraction z c := by
  obtain ⟨u,⟨m,hm⟩,v,⟨n,hn⟩,he⟩ := h
  exact ⟨m+n,u,v,m,n,hm,hn,he,le_rfl⟩
omit [DecidableEq ι] in
lemma bounded_one : P.BoundedFraction 1 0 :=
  ⟨1,1,0,0,P.diag 1,P.diag 1,by simp,le_rfl⟩
omit [DecidableEq ι] in
lemma bounded_inv {z : ι → G} {c : ℕ} (h : P.BoundedFraction z c) :
    P.BoundedFraction z⁻¹ c := by
  obtain ⟨u,v,m,n,hm,hn,rfl,hc⟩ := h
  exact ⟨v,u,n,m,hn,hm,by group,by omega⟩
omit [DecidableEq ι] in
lemma bounded_conjugate {z : ι → G} {c : ℕ} (h : P.BoundedFraction z c) (g : G) :
    P.BoundedFraction (fun i => g*z i*g⁻¹) c := by
  obtain ⟨u,v,m,n,hm,hn,rfl,hc⟩ := h
  refine ⟨(fun _ => g)*u,(fun _ => g)*v,m,n,?_,?_,?_,hc⟩
  · simpa using P.mul (P.diag g) hm
  · simpa using P.mul (P.diag g) hn
  · ext i; simp only [Pi.mul_apply,Pi.inv_apply]; group
lemma bounded_mul_single {z : ι → G} {c d : ℕ} (hz : P.BoundedFraction z c)
    (i : ι) {g : G} (hg : P.BoundedFraction (Pi.mulSingle i g) d) :
    P.BoundedFraction (z*Pi.mulSingle i g) (c+d) := by
  obtain ⟨u,v,m,n,hm,hn,rfl,hc⟩ := hz
  have hh := P.bounded_conjugate hg (v i)⁻¹
  rw [conjugate_single,inv_inv] at hh
  obtain ⟨a,b,k,l,hk,hl,he,hd⟩ := hh
  refine ⟨u*a,v*b,m+k,n+l,P.mul hm hk,P.mul hn hl,?_,by omega⟩
  have ht : v⁻¹*Pi.mulSingle i g = Pi.mulSingle i ((v i)⁻¹*g*v i)*v⁻¹ := by
    ext j
    by_cases hj : j=i
    · subst j; simp
    · simp [Pi.mulSingle_eq_of_ne hj]
  rw [mul_assoc,ht,he]
  group

def singleCost (i : ι) (g : G) : ℕ := sInf {c | P.BoundedFraction (Pi.mulSingle i g) c}
lemma singleCost_bounded (i : ι) {g : G} (hg : g∈singleFractions P.monoid P.diagonal i) :
    P.BoundedFraction (Pi.mulSingle i g) (P.singleCost i g) :=
  Nat.sInf_mem (P.bounded_exists hg)
lemma singleCost_le (i : ι) {g : G} {c : ℕ} (hc : P.BoundedFraction (Pi.mulSingle i g) c) :
    P.singleCost i g ≤ c := Nat.sInf_le hc
lemma singleCost_one (i : ι) : P.singleCost i 1=0 := by
  apply Nat.eq_zero_of_le_zero
  apply P.singleCost_le
  simpa using P.bounded_one
lemma singleCost_inv (i : ι) {g : G} (hg : g∈singleFractions P.monoid P.diagonal i) :
    P.singleCost i g⁻¹=P.singleCost i g := by
  apply Nat.le_antisymm
  · apply P.singleCost_le
    rw [Pi.mulSingle_inv]
    exact P.bounded_inv (P.singleCost_bounded i hg)
  · apply P.singleCost_le
    have he := P.bounded_inv (P.singleCost_bounded i ((singleFractions _ _ i).inv_mem hg))
    simpa only [Pi.mulSingle_inv,inv_inv] using he
lemma singleCost_conjugate (i : ι) {g : G} (hg : g∈singleFractions P.monoid P.diagonal i) (k : G) :
    P.singleCost i (k*g*k⁻¹)=P.singleCost i g := by
  have hle {g : G} (hg : g∈singleFractions P.monoid P.diagonal i) (k : G) :
      P.singleCost i (k*g*k⁻¹) ≤ P.singleCost i g := by
    apply P.singleCost_le
    rw [← conjugate_single]
    exact P.bounded_conjugate (P.singleCost_bounded i hg) k
  apply Nat.le_antisymm (hle hg k)
  have he := hle ((singleFractions_normal P.monoid P.diagonal i).conj_mem g hg k) k⁻¹
  simpa only [inv_inv,inv_mul_cancel_left,mul_assoc,mul_inv_cancel_right,inv_mul_cancel,mul_one] using he
lemma singleCost_mul (i : ι) {g h : G}
    (hg : g∈singleFractions P.monoid P.diagonal i) (hh : h∈singleFractions P.monoid P.diagonal i) :
    P.singleCost i (g*h)≤P.singleCost i g+P.singleCost i h := by
  apply P.singleCost_le
  rw [Pi.mulSingle_mul]
  exact P.bounded_mul_single (P.singleCost_bounded i hg) i (P.singleCost_bounded i hh)

end GradedPaths
end EuclideanRamsey

end

end OAI


