-- Prove2me | Definitions.Def_FewInnerTSP_MixedRepr
-- name    : FewInnerTSP_MixedRepr
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:34:08.315093+00:00
-- url     : https://prove2.me/theorems/f51a858e-8b78-458f-a373-d6cc2b39632f
-- title:
--   MixedRepr (Algorithm 2) with fuel, valid separator rules
-- statement:
--   A **separator rule** assigns to a state and a balancing set $Q$ a separator choice. It is **valid** if on every well-formed state and every $Q\subseteq V$ with $|Q|>17$ it returns a minimum balancing square of the points of $Q$, a parameter $t\in[1,3]$, and a separator with no vertex of $V$ on its boundary.
--
--   **MixedRepr** (Algorithm 2), for a base threshold $a_0$, a balance coefficient $\gamma$, a separator rule and a tie rule:
--   1. if $V=\emptyset$, return the family consisting of the empty cover;
--   2. if $B=\emptyset$ or $|B|$ is odd, return the empty family;
--   3. if $|A|\le a_0$, return the weighted rank reduction of all feasible covers;
--   4. otherwise let $Q=A$ if $|B|\le\gamma\sqrt{|A|}$ and $Q=B$ otherwise, take the separator of the rule, and for every crossing choice passing the residual test recurse on both child states; collect every union $\mathrm{Sel}\cup R_1\cup R_2$ that is a feasible cover of the parent, and return its weighted rank reduction.
--
--   The recursion carries a **fuel** counter that decreases at each call and returns the empty family at fuel $0$.
--
--   **Formalization Note** The page's recursion terminates because every split is balanced, so each child has fewer vertices; fuel $|V|+1$ therefore never runs out, and Lemma 5.4 is stated at that fuel. The page's $a_0$, $\gamma$, separator rule and tie rule are parameters.
-- source:
--   Li, Ma, Gong, Exact Euclidean TSP with Few Interior Points: A Square-Root Exponent, STOC 2027 submission (manuscript sha256 6541f631…), Algorithm 2, p.20 (PDF p.22); §5.5, p.11 (PDF p.13); Lemma 4.5, p.8 (PDF p.10)

import Mathlib
import Definitions.Def_FewInnerTSP_RankReduction
import Definitions.Def_FewInnerTSP_CrossingChoices

namespace FewInnerTSP

/-- A selection rule for the separator: for a state and a balancing set, one separator. -/
abbrev Selector (n m : ℕ) := State n m → Finset (Fin n) → SepChoice

/-- **A valid selection rule.** On a well-formed state and a set `Q ⊆ V` with `|Q| > 17` it returns a
minimum balancing square for `Q` and a parameter `t ∈ [1, 3]` whose square has no vertex of `V` on its
boundary.
Source: Li, Ma, Gong, STOC 2027 submission (manuscript sha256 6541f631…), Algorithm 1, lines 1–3, p.18
(PDF p.20); Lemma B.1, p.16; Lemma 4.5, p.8.

**Formalization Note** The page's rule, which takes a minimizing parameter with clearance (11), is one
such rule, by Lemma 4.5. -/
def IsValidSelector {n m : ℕ} (P : Fin n → Pt) (Γ : Skeleton n m) (sel : Selector n m) : Prop :=
  ∀ (S : State n m) (Q : Finset (Fin n)), IsState Γ S → Q ⊆ S.V → 17 < Q.card →
    IsMinBalancingSquare (Q.image P) (sel S Q).c (sel S Q).u ∧
    (sel S Q).t ∈ Set.Icc (1 : ℝ) 3 ∧
    ∀ v ∈ S.V, P v ∉ squareBoundary (sel S Q).c ((sel S Q).t * (sel S Q).u)

open Classical in
/-- All feasible covers of a state. Source: Li, Ma, Gong, p.11 (PDF p.13): "The base enumerates every
feasible cover before rank reduction". -/
noncomputable def allCovers {n m : ℕ} (Γ : Skeleton n m) (S : State n m) :
    Finset (Finset (Edge n m)) :=
  S.E.powerset.filter (IsFeasibleCover Γ S)

open Classical in
/-- **`MixedRepr` (Algorithm 2)**, with a fuel argument. Lines 1–3: the empty state returns the singleton
empty cover. Lines 4–6: `B = ∅` or odd `|B|` returns `∅`. Lines 7–9: `|A| ≤ a₀` returns the rank-reduced
family of all feasible covers. Otherwise line 10 takes `Q = A` if `|B| ≤ γ√|A|` and `Q = B` otherwise;
lines 12–20 join the two recursive families over all crossing choices that pass the residual test, keeping
feasible parent covers; line 21 returns the weighted rank reduction.
Source: Li, Ma, Gong, Algorithm 2, p.20 (PDF p.22).

**Formalization Note** The page's recursion terminates by balance: both sides of `σ` get at least one
point of `Q`, so each child has fewer vertices. The `fuel` argument avoids proving that inside the
definition; the milestone uses fuel `|V| + 1`, never an arbitrary one, because fuel `0` returns `∅` as a
junk value. The page's `a₀`, `γ`, selection rule and tie rule are parameters. -/
noncomputable def mixedRepr {n m : ℕ} (P : Fin n → Pt) (Γ : Skeleton n m) (a0 : ℕ) (γ : ℝ)
    (sel : Selector n m) (tie : Finset (Edge n m) → ℕ) :
    ℕ → State n m → Finset (Finset (Edge n m))
  | 0, _ => ∅
  | fuel + 1, S =>
    if S.V = ∅ then {∅}
    else if S.B = ∅ ∨ Odd S.B.card then ∅
    else if S.A.card ≤ a0 then rankReduce Γ S tie (allCovers Γ S)
    else
      let Q := if (S.B.card : ℝ) ≤ γ * Real.sqrt S.A.card then S.A else S.B
      let σ := sel S Q
      rankReduce Γ S tie
        (((crossingChoices P Γ S σ).filter (PassesResidual Γ S)).biUnion fun Sel =>
          (((mixedRepr P Γ a0 γ sel tie fuel (childState P Γ S σ Sel true)) ×ˢ
              (mixedRepr P Γ a0 γ sel tie fuel (childState P Γ S σ Sel false))).image
            fun R => Sel ∪ R.1 ∪ R.2).filter (IsFeasibleCover Γ S))

end FewInnerTSP


