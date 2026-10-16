-- Prove2me | Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_RoutingPath
-- name    : OAI_MeasureTheory_DyadicAvoidance_RoutingPath
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-16T03:02:08.721563+00:00
-- url     : https://prove2.me/theorems/4c0b0a4d-93fa-4662-b747-c451d99f94b8
-- title:
--   Routing down a tree by iterated local choices
-- statement:
--   This file defines the deterministic routing of a parameter down a tree by iterating a local choice rule, and proves its basic stability properties.
--
--   Let $\iota$ be an alphabet of children, let $\iota^{*}$ be the set of finite words over $\iota$ (the nodes of the infinite $\iota$-ary tree, the empty word $\varnothing$ being the root), and write $Pc$ for the word $P$ followed by the letter $c$. Let $X$ be a parameter set and $\operatorname{ch} : \iota^{*} \times X \to \iota$ a choice rule assigning to every node $P$ and parameter $x$ a child $\operatorname{ch}(P,x)$.
--
--   1. **Routing.** For $n \in \mathbb{N}$, a starting node $P \in \iota^{*}$ and $x \in X$, the node reached after $n$ steps is defined recursively by
--   $$
--   R_0(P,x) = P, \qquad R_{n+1}(P,x) = R_n(P,x)\,\operatorname{ch}\big(R_n(P,x), x\big).
--   $$
--   The two defining equations are recorded as simplification rules.
--
--   2. **Length.** $|R_n(P,x)| = |P| + n$.
--
--   3. **Agreement along the path.** For $x, y \in X$ and $n \in \mathbb{N}$: if $\operatorname{ch}(R_k(P,x), y) = \operatorname{ch}(R_k(P,x), x)$ for every $k < n$, then $R_n(P,y) = R_n(P,x)$. Only the choices at the nodes actually visited by $x$ are compared; nothing is assumed about the choices at other nodes.
--
--   4. **Periodicity.** If $X = \mathbb{R}$ and $\operatorname{ch}(P, x+1) = \operatorname{ch}(P, x)$ for all $P \in \iota^{*}$ and $x \in \mathbb{R}$, then $R_n(P, x+1) = R_n(P, x)$ for all $n$, $P$ and $x$.
--
--   In the dyadic avoidance construction the choice rule is the first-success selector rule read at a point $x \in \mathbb{R}$, and the leaf $R_d(\varnothing, x)$ determines which terminal label decides whether $x$ belongs to the random set. The agreement property is the mechanism by which a point and a slightly shifted point are shown to follow the same route.
--
--   **Formalization Note** Words are Lean lists `List ι`, and the step appends a single letter, `Q ++ [choose Q x]`; the routing function is `routeFrom choose n P x`, defined by recursion on `n`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/DyadicAvoidance/RoutingPath.lean

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/DyadicAvoidance/RoutingPath.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the DyadicAvoidance mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_DyadicAvoidance
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_PeriodicBasic
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_GridSeparation
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_FiniteTableModel
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_OrderedRouting

namespace OAI

universe u_ι u_X

noncomputable section

namespace Problem310.RoutingPath

variable {ι : Type u_ι} {X : Type u_X}

/-- Route from a node by appending the locally selected child at each step.
The choice rule is abstract: a first-success/default selector can be supplied. -/
def routeFrom (choose : List ι → X → ι) : ℕ → List ι → X → List ι
  | 0, P, _ => P
  | n + 1, P, x =>
      let Q := routeFrom choose n P x
      Q ++ [choose Q x]

@[simp] theorem routeFrom_zero (choose : List ι → X → ι) (P : List ι) (x : X) :
    routeFrom choose 0 P x = P := rfl

@[simp] theorem routeFrom_succ (choose : List ι → X → ι) (n : ℕ) (P : List ι) (x : X) :
    routeFrom choose (n + 1) P x =
      routeFrom choose n P x ++ [choose (routeFrom choose n P x) x] := rfl

@[simp] theorem length_routeFrom (choose : List ι → X → ι)
    (n : ℕ) (P : List ι) (x : X) :
    (routeFrom choose n P x).length = P.length + n := by
  induction n with
  | zero => simp
  | succ n ih => simp [ih, Nat.add_assoc]

/-- Earlier decisions along one path suffice to preserve the full common prefix.
No restriction is imposed on decisions off that path. -/
theorem routeFrom_eq_of_choices_eq (choose : List ι → X → ι)
    (n : ℕ) (P : List ι) (x y : X)
    (hchoice : ∀ k < n,
      choose (routeFrom choose k P x) y = choose (routeFrom choose k P x) x) :
    routeFrom choose n P y = routeFrom choose n P x := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have hp := ih (fun k hk => hchoice k (Nat.lt_trans hk (Nat.lt_succ_self n)))
      simp only [routeFrom_succ, hp, hchoice n (Nat.lt_succ_self n)]

/-- Periodic node choices give periodic routed leaves. -/
theorem routeFrom_periodic (choose : List ι → ℝ → ι)
    (hchoose : ∀ P x, choose P (x + 1) = choose P x)
    (n : ℕ) (P : List ι) (x : ℝ) :
    routeFrom choose n P (x + 1) = routeFrom choose n P x := by
  apply routeFrom_eq_of_choices_eq
  intro k hk
  exact hchoose _ x

end Problem310.RoutingPath

end

end OAI


