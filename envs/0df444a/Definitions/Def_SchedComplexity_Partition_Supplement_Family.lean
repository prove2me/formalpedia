-- Prove2me | Definitions.Def_SchedComplexity_Partition_Supplement_Family
-- name    : SchedComplexity_Partition_Supplement_Family
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T12:27:43.239804+00:00
-- url     : https://prove2.me/theorems/e962293a-8a2d-4a83-8855-ba1017c01037
-- title:
--   Sections 2–3 — the complete scheduling family and recognition languages
-- statement:
--   A scheduling problem fixes a machine-count regime $M$, a shop type $\ell$, a parameter set $\lambda$, and a criterion $k$. The five criteria are makespan $C_{\max}$, weighted completion time $\sum_jw_jC_j$, maximum lateness $L_{\max}$, weighted tardiness $\sum_jw_jT_j$, and weighted late-job count $\sum_jw_jU_j$. A recognition instance adds a bound $y$, and asks whether a feasible schedule has value at most $y$:
--
--   $$L(M,\ell,\lambda,k)=\{\operatorname{code}(I,y):I\text{ belongs to the class and admits a feasible schedule of value }\le y\}.$$
--
--   The nine kinds of parameters allow arbitrary release dates, a release date only for the last job, deadlines, arbitrary precedence (an acyclic arc set, since $J_j<J_k$ is a precedence relation), branching precedence (acyclic by definition), no waiting within a job, a fixed positive bound on operations per job, processing times between one and a fixed positive bound, and unit weights. Deadlines are allowed only with makespan and weighted completion time. Release and precedence features are levels: none $<$ last $<$ arbitrary releases, and none $<$ branching $<$ arbitrary precedence. Union takes the most general level present; every numerical or unit-weight restriction present must hold. Constants belong to the class, not the input.
--
--   Feasibility is exactly the published shop feasibility predicate, with common job order for permutation shops, $C_j=B_j+\sum_rp_{jr}$ for no wait, and $C_j\le d_j$ when deadlines are present. Identical-machine assignments are existential schedule data. Both maximum criteria are bounded pointwise for every job, so there is no maximum-of-empty-set default. Empty job sets are retained.
--
--   **Formalization Note** The bound is an integer for maximum lateness and a natural number otherwise. Binary codes use the published `BSym` and `encNats`: $n,m$; each job's release, operation count and machine/time pairs; the precedence matrix row by row; weight/due-date pairs; then $y$ (a sign bit and magnitude for lateness). The published shop code's terminal dummy bound is removed before adding the new fields. A fixed-machine class still carries $m$ in the code and checks equality. Invalid classes, non-codes and non-instances are outside the language. Zero-duration operations follow the shared processing-order feasibility convention. This interface makes polynomiality a genuine Cook-machine property, never a hypothesis of class membership.
-- source:
--   Brucker, Lenstra & Rinnooy Kan, Complexity of Machine Scheduling Problems, Mathematisch Centrum Report BW 43/75 (1975), Sections 2–3, pp. 4, 6–7

import Mathlib
import Definitions.Def_SchedComplexity_Partition_Supplement_Shops
import Definitions.Def_ProjSchedTW_Complexity_Encoding

namespace SchedComplexity.Partition.Supplement

open CookPvsNP ProjSchedTW.Complexity

/-- The five objective criteria of Section 3, p. 7. -/
inductive Criterion where
  | cmax | sumWC | lmax | sumWT | sumWU
  deriving DecidableEq

/-- Recognition thresholds: integers for maximum lateness, naturals for the other criteria.
Lateness can be negative, even though every input datum is nonnegative. -/
abbrev Bound : Criterion → Type
  | .lmax => ℤ
  | _ => ℕ

/-- The nine kinds of λ-elements (p. 7). Bounds are fixed class constants, never input data. -/
inductive Feature where
  | releaseAll | releaseLast | deadlines | precedence | tree | noWait
  | operations (bound : ℕ)
  | processing (bound : ℕ)
  | unitWeights
  deriving DecidableEq

/-- A parameter set is finite; repeated bound features impose all of their restrictions.
When both release features or both precedence features occur, the more general one wins,
as required by the special-case argument in the proof of Theorem 1(g). -/
abbrev Parameters := Finset Feature

/-- Admissible (λ,k): positive fixed bounds and the source's restriction on deadlines. -/
def Admissible (lam : Parameters) (k : Criterion) : Prop :=
  (∀ b, Feature.operations b ∈ lam → 0 < b) ∧
  (∀ b, Feature.processing b ∈ lam → 0 < b) ∧
  (Feature.deadlines ∈ lam → k = .cmax ∨ k = .sumWC)

/-- Features that may be added in Theorem 1(g). -/
def Generalizations (extra : Parameters) : Prop :=
  ∀ f ∈ extra, f = .releaseAll ∨ f = .releaseLast ∨ f = .deadlines ∨
    f = .precedence ∨ f = .tree

/-- Features that may be removed in Theorem 1(h). -/
def Restrictions (extra : Parameters) : Prop :=
  ∀ f ∈ extra, (∃ b, f = .operations b) ∨ (∃ b, f = .processing b) ∨ f = .unitWeights

/-- λ-data restrictions. Release levels are none < last < all and precedence levels
none < tree < arbitrary. An arbitrary precedence relation `J_j < J_k` (p. 7) is a strict
order, so its arc set must have no directed cycle (no loop); a branching is acyclic as well.
Deadlines and no-wait are constraints on schedules, not input data.
The branching predicate and the operation data are those of the published shop model. -/
def DataRestrictions {n m : ℕ} (lam : Parameters) (I : Instance n m) : Prop :=
  (if Feature.releaseAll ∈ lam then True
   else if Feature.releaseLast ∈ lam then ∀ j : Fin n, j.val + 1 < n → I.shop.release j = 0
   else ∀ j, I.shop.release j = 0) ∧
  (if Feature.precedence ∈ lam then
     ∀ j : Fin n, ¬ Relation.TransGen (fun a b => (a, b) ∈ I.shop.prec) j j
   else if Feature.tree ∈ lam then I.shop.IsBranching
   else I.shop.prec = ∅) ∧
  (∀ b, Feature.operations b ∈ lam → ∀ j, (I.shop.ops j).length ≤ b) ∧
  (∀ b, Feature.processing b ∈ lam → ∀ j, ∀ e ∈ I.shop.ops j, 1 ≤ e.2 ∧ e.2 ≤ b) ∧
  (Feature.unitWeights ∈ lam → ∀ j, I.weight j = 1)

/-- Criterion value at most y. Both maximum criteria are pointwise bounds, so there is
no default-valued supremum, including for n=0. The sums and lateness use signed integers. -/
def ValueLE {n m : ℕ} (I : Instance n m)
    (Q : SchedComplexity.Shops.ShopInstance n m) (S : Q.Op → ℕ) :
    (k : Criterion) → Bound k → Prop
  | .cmax, y => ∀ j, Q.completion S j ≤ y
  | .sumWC, y => (∑ j, (I.weight j : ℤ) * (Q.completion S j : ℤ)) ≤ (y : ℤ)
  | .lmax, y => ∀ j, lateness I Q S j ≤ y
  | .sumWT, y => (∑ j, (I.weight j : ℤ) * tardiness I Q S j) ≤ (y : ℤ)
  | .sumWU, y => (∑ j, I.weight j * lateIndicator I Q S j) ≤ y

/-- Feasibility uses the published release, job-chain, machine and precedence constraints,
with the common-order, no-wait and deadline restrictions required by the class. -/
def Meets {n m : ℕ} (ell : ShopKind) (lam : Parameters) (k : Criterion)
    (I : Instance n m) (y : Bound k) : Prop :=
  ∃ (a : Fin n → Fin m) (S : (realize ell I a).Op → ℕ),
    let Q := realize ell I a
    Q.IsFeasible S ∧
    (ell = .permutation → CommonOrder Q S) ∧
    (Feature.noWait ∈ lam → ∀ j, Q.completion S j = beginning Q S j +
      ∑ r : Fin (Q.ops j).length, Q.proc ⟨j, r⟩) ∧
    (Feature.deadlines ∈ lam → ∀ j, Q.completion S j ≤ I.due j) ∧
    ValueLE I Q S k y

/-- A scheduling problem fixes m (constant or variable), ℓ, λ including its constants, and k.
The number of jobs remains part of every input. -/
structure Problem where
  machines : MachineCount
  shopKind : ShopKind
  parameters : Parameters
  criterion : Criterion

/-- Precisely the admissible class parameters of Section 3. -/
def Problem.Valid (P : Problem) : Prop :=
  P.machines.Valid ∧ Admissible P.parameters P.criterion

/-- Threshold suffix: signed magnitude for L_max, a single natural for all other criteria.
A sign 0 represents nonnegative integers; sign 1 represents strictly negative integers. -/
def thresholdNumbers : (k : Criterion) → Bound k → List ℕ
  | .lmax, y => [if y < 0 then 1 else 0, y.natAbs]
  | .cmax, y => [y]
  | .sumWC, y => [y]
  | .sumWT, y => [y]
  | .sumWU, y => [y]

/-- The code determines the instance and y: n,m; for each job r_j,m_j followed by
(machine index,processing time) per operation; the n×n precedence matrix row by row;
then w_j,d_j per job; then the threshold suffix. Uses the published shop code with its
dummy terminal threshold removed. The machine count is present even in constant-m classes,
where it must equal the fixed value. Identical-machine inputs store canonical zero tags;
actual assignments are never encoded as input. Every number is subsequently encoded in binary. -/
def instanceNumbers {n m : ℕ} (I : Instance n m) (k : Criterion) (y : Bound k) : List ℕ :=
  (I.shop.code 0).dropLast ++
    (List.ofFn fun j : Fin n => [I.weight j, I.due j]).flatten ++ thresholdNumbers k y

/-- Section 2's recognition problem on explicit binary codes. Non-codes, inadmissible
classes, wrong machine counts and inputs outside the class are not in the language.
No optimum, supremum, feasibility oracle or polynomial-time property is assumed. -/
def Problem.language (P : Problem) : Lang BSym :=
  { x | P.Valid ∧ ∃ (n m : ℕ) (I : Instance n m) (y : Bound P.criterion),
      P.machines.Allows m ∧ HasShape P.shopKind I ∧ DataRestrictions P.parameters I ∧
      Meets P.shopKind P.parameters P.criterion I y ∧
      x = encNats (instanceNumbers I P.criterion y) }

/-- Convenient notation-free name for the family n|m|ℓ,λ|k. -/
def language (machines : MachineCount) (ell : ShopKind) (lam : Parameters) (k : Criterion) :
    Lang BSym :=
  (Problem.mk machines ell lam k).language

end SchedComplexity.Partition.Supplement


