-- Prove2me | Definitions.Def_OAI_Combinatorics_Sensitivity_RecursiveDefinitions
-- name    : OAI_Combinatorics_Sensitivity_RecursiveDefinitions
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T01:24:32.989549+00:00
-- url     : https://prove2.me/theorems/cee41389-fc7f-44a4-ac3d-cddf0b9bd2a8
-- title:
--   One level of the row-clause construction over a labeled tournament
-- statement:
--   Fix a tournament $T$ on $[k] = \{0, \dots, k-1\}$ with edge relation $i \to j$, a labeling $\lambda : [k] \times [k] \to [r]$, a set $I$, and a family $F = (F_0, \dots, F_h)$ of $h+1$ Boolean functions on $\{0,1\}^I$ (Boolean values identified with $\{0,1\}$). The next level lives on the coordinate set $([k] \times [r]) \times I$, that is, on $kr$ disjoint copies of $I$ arranged in $k$ rows and $r$ columns.
--
--   1. **Children.** For $x \in \{0,1\}^{([k] \times [r]) \times I}$, a row $j$ and a column $c$, the child $x[j,c] \in \{0,1\}^I$ is the part of $x$ on the copy indexed by $(j,c)$: $x[j,c](a) = x((j,c), a)$.
--
--   2. **Gate index.** For $q \in \{0, \dots, h-1\}$ the gate index is $h - 1 - q$, an index of $F$ different from the last index $h$.
--
--   3. **Row clauses.** For $q \in \{0, \dots, h-1\}$ and a row $i \in [k]$, the clause $C_{q,i}$ requires that all $r$ children of row $i$ (the targets) are accepted by the last member $F_h$, and that for every out-neighbour $j$ of $i$ the child of row $j$ in column $\lambda(i,j)$ (a gate) is rejected by $F_{h-1-q}$:
--   $$
--   C_{q,i}(x) = 1 \iff \Big( \forall\, c \in [r]:\ F_h(x[i,c]) = 1 \Big) \text{ and } \Big( \forall\, j \text{ with } i \to j:\ F_{h-1-q}\big(x[j, \lambda(i,j)]\big) = 0 \Big).
--   $$
--
--   4. **Recursive family.** The next-level family has $h$ members, the disjunctions of the row clauses:
--   $$
--   F'_q(x) = \bigvee_{i \in [k]} C_{q,i}(x), \qquad q = 0, \dots, h-1 .
--   $$
--
--   One level thus turns a family of $h+1$ predicates on $\{0,1\}^I$ into a family of $h$ predicates on $\{0,1\}^{([k] \times [r]) \times I}$. Iterating it is the core of a construction of Boolean functions whose block sensitivity is much larger than the square of their sensitivity: under the base conditions used there, the number of disjoint sensitive blocks at the all-zero input is multiplied by $k$ at each level, while the sensitivities obey controlled linear recurrences.
--
--   **Formalization Note** The definitions are `recursiveChild`, `gateIndex`, `rowClause` and `recursiveFamily`. The gate index is `(Fin.rev q).castSucc` as an element of `Fin (h + 1)`, and the last index $h$ is `Fin.last h`. Boolean values are produced with `decide`, and $I$ is an arbitrary type here.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Sensitivity/RecursiveDefinitions.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Sensitivity/RecursiveDefinitions.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the SensitivitySeparation mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_SensitivitySeparation
import Definitions.Def_OAI_Combinatorics_Sensitivity_HammingBase
import Definitions.Def_OAI_Combinatorics_Sensitivity_RecursiveProfiles
import Definitions.Def_OAI_Combinatorics_Sensitivity_Basic
import Definitions.Def_OAI_Combinatorics_Sensitivity_InitialPredicates
import Definitions.Def_OAI_Combinatorics_Sensitivity_Tournament

namespace OAI

/-! The literal target-row and labeled-gate construction. -/

noncomputable section
open scoped Classical

namespace Paper320

def recursiveChild {k r : ℕ} {I : Type}
    (x : ((Fin k × Fin r) × I) → Bool) (j : Fin k) (c : Fin r) : I → Bool :=
  fun a => x ((j, c), a)

def gateIndex {h : ℕ} (q : Fin h) : Fin (h + 1) := (Fin.rev q).castSucc

/-- A clause uses every target in its own row and one labeled gate per outgoing edge. -/
def rowClause {k r h : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin (h + 1) → (I → Bool) → Bool)
    (q : Fin h) (x : ((Fin k × Fin r) × I) → Bool) (i : Fin k) : Bool :=
  decide ((∀ c, F (Fin.last h) (recursiveChild x i c) = true) ∧
    ∀ j, T.Adj i j → F (gateIndex q) (recursiveChild x j (label i j)) = false)

/-- The next-level predicate is the disjunction of the literal row clauses. -/
def recursiveFamily {k r h : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin (h + 1) → (I → Bool) → Bool)
    (q : Fin h) (x : ((Fin k × Fin r) × I) → Bool) : Bool :=
  decide (∃ i, rowClause T label F q x i = true)

end Paper320

end

end OAI


