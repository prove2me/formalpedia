-- Prove2me | Definitions.Def_OneOfManyCC_LeafSets
-- name    : OneOfManyCC_LeafSets
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:53:04.860346+00:00
-- url     : https://prove2.me/theorems/44b41fe9-9c95-4439-9c28-63bb895e82dd
-- title:
--   Leaves of a protocol, the sets $\mathcal A_v,\mathcal B_v$, and the projections $S_w,T_w$
-- statement:
--   Let $P$ be a protocol tree. A node is named by the path from the root. For a node $v$, let $\mathcal A_v$ be the set of Alice inputs on which her messages agree with the edges leaving her nodes on the path to $v$, and define $\mathcal B_v$ in the same way for Bob.
--
--   If $P$ is a protocol for $\mathrm{OneOut}^{\neq}_k(R)$, so that its inputs are tuples, then each leaf $w$ has an output $(i_w,o_w)$. The **projections** of $\mathcal A_w$ and $\mathcal B_w$ onto coordinate $i_w$ are
--
--   $$S_w=\{x_{i_w} : (x_1,\dots,x_k)\in\mathcal A_w\},\qquad T_w=\{y_{i_w} : (y_1,\dots,y_k)\in\mathcal B_w\}.$$
--
--   These projections let a single input $x$ stand at the named position of a tuple reaching $w$, which is how players holding one input use a protocol built for tuples.
--
--   **Formalization Note** `leafOutput P w` is `some` of the label exactly when the path `w` ends at a leaf, so two leaves with equal labels are different. $S_w$ and $T_w$ are empty when `w` is not a leaf.
-- source:
--   Chukhin, Kulikov, Mihajlin, Smal, Solving One of Many Instances Is Almost as Hard as Solving One, STOC 2027 submission (manuscript sha256 5d4d41dd…), §5, p.10

import Mathlib
import Definitions.Def_OneOfManyCC_Protocol

namespace OneOfManyCC

namespace Protocol

variable {A B O : Type}

/-- The label of the leaf reached along the path `w` from the root (`false` = child `p₀`,
`true` = child `p₁`), and `none` when `w` is not the path of a leaf.

**Formalization Note.** A node of the tree is named by its path `List Bool`, so two leaves with the
same label are different leaves. -/
def leafOutput : Protocol A B O → List Bool → Option O
  | leaf o, [] => some o
  | leaf _, _ :: _ => none
  | alice _ _ _, [] => none
  | bob _ _ _, [] => none
  | alice _ p₀ _, false :: w => p₀.leafOutput w
  | alice _ _ p₁, true :: w => p₁.leafOutput w
  | bob _ p₀ _, false :: w => p₀.leafOutput w
  | bob _ _ p₁, true :: w => p₁.leafOutput w

/-- The set of leaves of `P`, as a set of paths. -/
def leaves (P : Protocol A B O) : Set (List Bool) :=
  {w | ∃ o, P.leafOutput w = some o}

/-- The set `A_v` of §5, p.10: "the set of tuples on which Alice's messages agree with the edges
leaving her nodes on the path from the root to v". Here for a protocol whose Alice inputs are of
type `A`; the paper applies it with inputs `Inj_k(A)`.

**Formalization Note.** At the root (`v = []`) every input agrees. A path that leaves the tree (past
a leaf) gets the empty set; such paths are not nodes and are never used. -/
def aliceSet : Protocol A B O → List Bool → Set A
  | _, [] => Set.univ
  | leaf _, _ :: _ => ∅
  | alice f p₀ _, false :: w => {x | f x = false ∧ x ∈ p₀.aliceSet w}
  | alice f _ p₁, true :: w => {x | f x = true ∧ x ∈ p₁.aliceSet w}
  | bob _ p₀ _, false :: w => p₀.aliceSet w
  | bob _ _ p₁, true :: w => p₁.aliceSet w

/-- The set `B_v` of §5, p.10, defined "in the same way for Bob". -/
def bobSet : Protocol A B O → List Bool → Set B
  | _, [] => Set.univ
  | leaf _, _ :: _ => ∅
  | alice _ p₀ _, false :: w => p₀.bobSet w
  | alice _ _ p₁, true :: w => p₁.bobSet w
  | bob g p₀ _, false :: w => {y | g y = false ∧ y ∈ p₀.bobSet w}
  | bob g _ p₁, true :: w => {y | g y = true ∧ y ∈ p₁.bobSet w}

variable {k : ℕ} {A₀ B₀ : Type}

/-- `w` is a leaf with index `i_w = i`, for a protocol whose outputs are pairs `(i, o)`. -/
def HasIndex (P : Protocol (Fin k ↪ A₀) (Fin k ↪ B₀) (Fin k × O)) (w : List Bool) (i : Fin k) :
    Prop :=
  ∃ o, P.leafOutput w = some (i, o)

/-- The projection `S_w` of §5, p.10.
Chukhin, Kulikov, Mihajlin, Smal, *Solving One of Many Instances Is Almost as Hard as Solving One*, STOC 2027 submission (manuscript sha256 5d4d41dd…), §5, p.10:
"For each leaf w with output (i_w, o_w), let S_w = {x_{i_w} : (x1, . . . , xk) ∈ A_w} and
T_w = {y_{i_w} : (y1, . . . , yk) ∈ B_w} be the projections of A_w and B_w onto coordinate i_w."

**Formalization Note.** It is the empty set when `w` is not a leaf. -/
def projS (P : Protocol (Fin k ↪ A₀) (Fin k ↪ B₀) (Fin k × O)) (w : List Bool) : Set A₀ :=
  {x | ∃ i, P.HasIndex w i ∧ ∃ X ∈ P.aliceSet w, X i = x}

/-- The projection `T_w` of §5, p.10; see `projS`. -/
def projT (P : Protocol (Fin k ↪ A₀) (Fin k ↪ B₀) (Fin k × O)) (w : List Bool) : Set B₀ :=
  {y | ∃ i, P.HasIndex w i ∧ ∃ Y ∈ P.bobSet w, Y i = y}

end Protocol

end OneOfManyCC


