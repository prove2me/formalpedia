-- Prove2me | Definitions.Def_PooledTestingAdaptivity_Gap_Policies
-- name    : PooledTestingAdaptivity_Gap_Policies
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T20:25:27.903892+00:00
-- url     : https://prove2.me/theorems/ee41bb51-80e3-447b-a3b3-5e8d45870ac0
-- title:
--   Ordered refinement, feasible policies, normalization and actual welfare optima
-- statement:
--   Fix an instance $J$, budget $B\ge0$ and a nonempty, health-independent family $\mathcal F$ of ordered allocations, each of length at most $B$ and with nonempty pools of size at most $G$. Write $S\preceq T$ when $S$ is obtained by shrinking each pool of $T$ and discarding empty replacements without reordering. Downward closure means $T\in\mathcal F$ and $S\preceq T$ imply $S\in\mathcal F$.
--
--   A policy is a finite binary query tree labelled by nonempty pools. It branches on the tested pool's outcome only. Write $P_\pi(x)$ for its recursively computed run. Feasibility and welfare are
--
--   $$\forall x,\ P_\pi(x)\in\mathcal F,\qquad W_J(\pi)=\sum_x\mu_J(x)w_J(P_\pi(x),x).$$
--
--   Normalization requires every selected pool to avoid the earlier cleared set on every realizable execution. Syntactic normalization additionally requires every descendant pool below a negative child to avoid its ancestor's pool, even on unreachable branches. Define the benchmarks from the actual feasible objects:
--
--   $$\operatorname{OPT}_{\rm stat}=\sup_{T\in\mathcal F}W_J(T),\qquad\operatorname{OPT}_{\rm dyn}=\sup_{\pi\text{ feasible}}W_J(\pi).$$
--
--   Both value sets are nonempty and bounded by $\sum_i u_i$; they have finitely many distinct values. A static list is also a tree, and each feasible run belongs to a finite family of bounded lists. Arbitrary finite trees retain inconsistent branches without imposing a global depth restriction; pruning those branches gives the usual depth-at-most-$B$ representation. A health-independent random seed can select a deterministic tree. Randomized policies average these same values and cannot improve either optimum.
-- source:
--   Edwin Lock, Nicholas Lopez, Francisco Marmolejo-Cossío, Jose Roberto Tello Ayala, David Parkes, STOC 2027 submission #1397 (October 2026), §2–2.1 and Definition 2.1, printed pp. 4–5, PDF pp. 5–6; Definition 4.1 and Lemma 4.2, printed p. 12, PDF p. 13; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1397.pdf

import Mathlib
import Definitions.Def_PooledTestingAdaptivity_Gap_DecisionTree
import Definitions.Def_PooledTestingAdaptivity_Gap_Instance

namespace PooledTestingAdaptivity.Gap

abbrev Policy (n : ℕ) := DecisionTree (Pool n)

/-- Policies branch only on the outcome of the pool at their current node. -/
def run {n : ℕ} (π : Policy n) (x : Profile n) : Allocation n :=
  (π.path fun t => negative t.val x).map Subtype.val

/-- Shrink each pool in place; deleting an empty replacement preserves order. -/
inductive Refines {n : ℕ} : Allocation n → Allocation n → Prop where
  | nil : Refines [] []
  | drop {S T : Allocation n} (t : Finset (Fin n)) :
      Refines S T → Refines S (t :: T)
  | keep {S T : Allocation n} {s t : Finset (Fin n)} :
      s.Nonempty → s ⊆ t → Refines S T → Refines (s :: S) (t :: T)

/-- §2.1: arbitrary health-independent constraints on ordered allocations. -/
structure FeasibleFamily {n : ℕ} (J : Instance n) (B : ℕ) where
  allocations : Set (Allocation n)
  nonempty : allocations.Nonempty
  admissible : ∀ T ∈ allocations, T.length ≤ B ∧ ∀ t ∈ T, t.Nonempty ∧ t.card ≤ J.cap

def DownwardClosed {n B : ℕ} {J : Instance n} (F : FeasibleFamily J B) : Prop :=
  ∀ T ∈ F.allocations, ∀ S, Refines S T → S ∈ F.allocations

/-- This includes profiles of prior mass zero. -/
def Feasible {n B : ℕ} {J : Instance n} (F : FeasibleFamily J B) (π : Policy n) : Prop :=
  ∀ x, run π x ∈ F.allocations

/-- Normalization along the execution on x, starting with the cleared set C. -/
def normalizedAt {n : ℕ} : Policy n → Profile n → Finset (Fin n) → Prop
  | .leaf _, _, _ => True
  | .query t k, x, C =>
      Disjoint t.val C ∧
        (if negative t.val x then normalizedAt (k true) x (C ∪ t.val) else normalizedAt (k false) x C)

def Normalized {n : ℕ} (π : Policy n) : Prop :=
  ∀ x, normalizedAt π x ∅

/-- Stronger syntactic condition on all descendants, even on inconsistent branches. -/
def SyntacticallyNormalized {n : ℕ} : Policy n → Prop
  | .leaf _ => True
  | .query t k =>
      DecisionTree.allLabels (fun s => Disjoint s.val t.val) (k true) ∧
      SyntacticallyNormalized (k true) ∧ SyntacticallyNormalized (k false)

noncomputable def dynamicWelfare {n : ℕ} (J : Instance n) (π : Policy n) : ℝ :=
  expectation J (fun x => reward J (run π x) x)

/-- Actual feasible welfare sets, bounded between zero and total utility. -/
noncomputable def optStatic {n B : ℕ} {J : Instance n} (F : FeasibleFamily J B) : ℝ :=
  sSup {v : ℝ | ∃ T ∈ F.allocations, staticWelfare J T = v}

noncomputable def optDynamic {n B : ℕ} {J : Instance n} (F : FeasibleFamily J B) : ℝ :=
  sSup {v : ℝ | ∃ π : Policy n, Feasible F π ∧ dynamicWelfare J π = v}

/-- A seed is chosen independently of health; each seed specifies a deterministic tree.
Any probability law on the seeds gives the randomized policies of §2. -/
abbrev SeededPolicy (Seed : Type) (n : ℕ) := Seed → Policy n

end PooledTestingAdaptivity.Gap


