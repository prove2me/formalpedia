-- Prove2me | Definitions.Def_SamplingLLL_Exploration
-- name    : SamplingLLL_Exploration
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T15:53:17.621336+00:00
-- url     : https://prove2.me/theorems/169f1fc5-28b7-4213-bd3f-a21abee7f3ad
-- title:
--   Membership explorations and the last-defect router
-- statement:
--   A membership exploration on a finite constraint set $C$ with distinguished element $c$ is a deterministic binary decision tree whose input is a set $B$ with $c\in B\subseteq C$, and whose queries ask whether an as-yet-unqueried member of $C\setminus\{c\}$ belongs to $B$. At a leaf $t$, $Y_t$ contains $c$ and the constraints answered yes, $N_t$ those answered no, and $L_t=C\setminus(Y_t\cup N_t)$ is the set never queried; $\epsilon_t=(-1)^{|Y_t|-1}$. A leaf is active for $B$ when $Y_t\subseteq B$ and $L_t\cap B=\emptyset$. The last-defect router takes the element $d$ of $B\setminus\{c\}$ queried last and returns the leaf reached on input $Y_t\triangle\{d\}$.
--
--   **Formalization Note** A node of the tree is identified by its pair $(Y,N)$, since two distinct nodes differ in that pair, so an exploration is a next-query rule on these pairs, which loses no decision tree.
-- source:
--   Achlioptas, Counting and Sampling by Local Repair: From the Lovász Local Lemma to Random k-SAT, STOC 2027 submission (manuscript sha256 7a943167…), Appendix A.2, pp.19–20

import Mathlib
import Definitions.Def_SamplingLLL_ProductCSP

set_option autoImplicit false

namespace SamplingLLL

/-- A node of a membership exploration, identified by the pair `(Y, N)` of constraints answered yes
(with the distinguished element `c`) and answered no. Distinct nodes of a binary decision tree
have distinct pairs, so every decision tree is a function of `(Y, N)`. -/
abbrev Leaf (m : ℕ) : Type := Finset (Fin m) × Finset (Fin m)

/-- A membership exploration, as its next-query rule (Appendix A.2, p.19); `none` stops. -/
abbrev NextQuery (m : ℕ) : Type := Finset (Fin m) → Finset (Fin m) → Option (Fin m)

variable {m : ℕ}

/-- Appendix A.2, p.19: the queries ask whether an as-yet-unqueried member of `C ∖ {c}` belongs to
the input. -/
def IsExploration (C : Finset (Fin m)) (c : Fin m) (next : NextQuery m) : Prop :=
  ∀ Y N d, next Y N = some d → d ∈ C ∧ d ≠ c ∧ d ∉ Y ∧ d ∉ N

/-- Running the rule on an input `B`, answering a query by membership in `B`; returns the node
reached and the list of queries in order. A valid exploration makes fewer than `m` queries, so the
fuel `m` of `run` never cuts a run short. -/
def runFrom (next : NextQuery m) (B : Finset (Fin m)) :
    ℕ → Leaf m → List (Fin m) → Leaf m × List (Fin m)
  | 0, t, tr => (t, tr)
  | k + 1, t, tr =>
    match next t.1 t.2 with
    | none => (t, tr)
    | some d =>
      if d ∈ B then runFrom next B k (insert d t.1, t.2) (tr ++ [d])
      else runFrom next B k (t.1, insert d t.2) (tr ++ [d])

/-- The run on input `B`, from the root `Y = {c}`, `N = ∅`. -/
def run (next : NextQuery m) (c : Fin m) (B : Finset (Fin m)) : Leaf m × List (Fin m) :=
  runFrom next B m ({c}, ∅) []

/-- The leaf reached on input `B`. -/
def leafOf (next : NextQuery m) (c : Fin m) (B : Finset (Fin m)) : Leaf m := (run next c B).1

/-- The leaves (terminal transcripts): those reached on some input `B` with `c ∈ B ⊆ C`. -/
def leaves (C : Finset (Fin m)) (c : Fin m) (next : NextQuery m) : Finset (Leaf m) :=
  (C.erase c).powerset.image fun B => leafOf next c (insert c B)

/-- `L_t = C ∖ (Y_t ∪ N_t)`, the set never queried on the route to `t`, p.19. -/
def unqueried (C : Finset (Fin m)) (t : Leaf m) : Finset (Fin m) := C \ (t.1 ∪ t.2)

/-- `ε_t = (-1)^{|Y_t|-1}`, p.20. `|Y_t| ≥ 1` on every leaf since `c ∈ Y_t`. -/
def sign (t : Leaf m) : ℤ := (-1) ^ (t.1.card - 1)

/-- Lemma A.3, p.20: `t` is active for the input `B`. -/
def Active (C : Finset (Fin m)) (t : Leaf m) (B : Finset (Fin m)) : Prop :=
  t.1 ⊆ B ∧ Disjoint (unqueried C t) B

instance (C : Finset (Fin m)) (t : Leaf m) (B : Finset (Fin m)) : Decidable (Active C t B) := by
  unfold Active; infer_instance

/-- The last-defect router of Lemma A.3, p.20: on the active leaf `t`, take the element `d` of
`B ∖ {c}` queried last on the input `Y_t`; the new leaf is the one reached on input `Y_t △ {d}`.
Returns `t` itself when `B ∖ {c}` has no queried member (no such `t` is active when `B ≠ {c}`). -/
def routerLeaf (next : NextQuery m) (c : Fin m) (B : Finset (Fin m)) (t : Leaf m) : Leaf m :=
  match ((run next c t.1).2.reverse.find? fun d => d ∈ B ∧ d ≠ c) with
  | some d => leafOf next c (symmDiff t.1 {d})
  | none => t

namespace ProductCSP

variable {n : ℕ} (P : ProductCSP n m)

/-- The active event of the leaf `t` of an exploration on `C` (Appendix A.3, p.20): every constraint
of `Y_t` is violated and every constraint of `L_t` is satisfied. -/
def active (C : Finset (Fin m)) (t : Leaf m) (x : P.Config) : Bool :=
  decide (Active C t (P.badSet C x))

/-- Mass of the active event. A leaf of mass zero is discarded (p.20). -/
def leafMass (C : Finset (Fin m)) (t : Leaf m) : ℚ := P.prob (P.active C t)

end ProductCSP

end SamplingLLL


