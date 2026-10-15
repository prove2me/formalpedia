-- Prove2me | Definitions.Def_OAI_Combinatorics_Sensitivity_RecursiveFailures
-- name    : OAI_Combinatorics_Sensitivity_RecursiveFailures
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T01:28:39.910894+00:00
-- url     : https://prove2.me/theorems/42129cfb-aad9-4329-84c4-bcec9002a25a
-- title:
--   Failed target and gate conditions of the row clauses
-- statement:
--   Use the setting of the row-clause construction: a tournament $T$ on $[k] = \{0, \dots, k-1\}$ with edges $i \to j$, a labeling $\lambda : [k] \times [k] \to [r]$, a family $F = (F_0, \dots, F_h)$ of Boolean functions on $\{0,1\}^I$, an index $q \in \{0, \dots, h-1\}$ with gate index $h-1-q$, and an input $x$ on $([k] \times [r]) \times I$ with children $x[j,c]$. Recall that the row clause $C_{q,i}$ asks all targets $x[i,c]$ to be accepted by $F_h$ and all gates $x[j, \lambda(i,j)]$ with $i \to j$ to be rejected by $F_{h-1-q}$.
--
--   1. **Failed targets** of row $i$: $\mathrm{TF}(i) = \{ c \in [r] : F_h(x[i,c]) = 0 \}$.
--
--   2. **Failed gates** of row $i$: $\mathrm{GF}_q(i) = \{ j \in [k] : i \to j,\ F_{h-1-q}(x[j, \lambda(i,j)]) = 1 \}$.
--
--   Thus $C_{q,i}(x) = 1$ exactly when both sets are empty.
--
--   3. **Target candidates**, the rows whose only failed condition is a single target:
--   $$
--   \mathcal{T}_q(x) = \{ i \in [k] : |\mathrm{TF}(i)| = 1,\ \mathrm{GF}_q(i) = \emptyset \}.
--   $$
--
--   4. **Gate candidates**, the rows whose only failed condition is a single gate:
--   $$
--   \mathcal{G}_q(x) = \{ i \in [k] : \mathrm{TF}(i) = \emptyset,\ |\mathrm{GF}_q(i)| = 1 \}.
--   $$
--
--   5. **Witnesses.** For $r > 0$, the target witness of row $i$ is an element of $\mathrm{TF}(i)$ when this set is nonempty, and column $0$ otherwise; the gate witness of row $i$ is an element of $\mathrm{GF}_q(i)$ when this set is nonempty, and $i$ itself otherwise.
--
--   A single bit flip changes a single child, and a child enters at most one condition of any given row (as a target if it lies in that row, otherwise as at most one gate). Hence on an input rejected by the next-level predicate a flip can only satisfy the clause of a row that fails exactly one condition, and it must act on the child named by that row's witness. The good-labeling property bounds the number of target candidates by fewer than $16$, which is where the factor $16$ in the recurrence for sensitivity on rejected inputs comes from.
--
--   **Formalization Note** The definitions are `targetFailures`, `gateFailures`, `targetCandidates`, `gateCandidates`, `targetWitness` (which takes the hypothesis `0 < r` to name column $0$) and `gateWitness`. Witnesses are chosen with classical choice; the default values only make the functions total.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Sensitivity/RecursiveFailures.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Sensitivity/RecursiveFailures.lean by skeleton subtraction
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
import Definitions.Def_OAI_Combinatorics_Sensitivity_RecursiveDefinitions
import Definitions.Def_OAI_Combinatorics_Sensitivity_RecursiveBlocks
import Definitions.Def_OAI_Combinatorics_Sensitivity_RecursiveSets
import Definitions.Def_OAI_Combinatorics_Sensitivity_TournamentCounts

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-! Fixed initial-input lists of clauses with exactly one failed condition. -/

noncomputable section
open scoped Classical

namespace Paper320

def targetFailures {k r h : ℕ} {I : Type}
    (F : Fin (h + 1) → (I → Bool) → Bool)
    (x : ((Fin k × Fin r) × I) → Bool) (i : Fin k) : Finset (Fin r) :=
  Finset.univ.filter fun c => F (Fin.last h) (recursiveChild x i c) = false

def gateFailures {k r h : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin (h + 1) → (I → Bool) → Bool)
    (q : Fin h) (x : ((Fin k × Fin r) × I) → Bool) (i : Fin k) : Finset (Fin k) :=
  Finset.univ.filter fun j => T.Adj i j ∧
    F (gateIndex q) (recursiveChild x j (label i j)) = true

def targetCandidates {k r h : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin (h + 1) → (I → Bool) → Bool)
    (q : Fin h) (x : ((Fin k × Fin r) × I) → Bool) : Finset (Fin k) :=
  Finset.univ.filter fun i => (targetFailures F x i).card = 1 ∧ gateFailures T label F q x i = ∅

def gateCandidates {k r h : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin (h + 1) → (I → Bool) → Bool)
    (q : Fin h) (x : ((Fin k × Fin r) × I) → Bool) : Finset (Fin k) :=
  Finset.univ.filter fun i => targetFailures F x i = ∅ ∧ (gateFailures T label F q x i).card = 1

def targetWitness {k r h : ℕ} {I : Type}
    (F : Fin (h + 1) → (I → Bool) → Bool)
    (x : ((Fin k × Fin r) × I) → Bool) (hr : 0 < r) (i : Fin k) : Fin r :=
  if hi : (targetFailures F x i).Nonempty then hi.choose else ⟨0, hr⟩

def gateWitness {k r h : ℕ} {I : Type} (T : Tournament k)
    (label : Fin k → Fin k → Fin r) (F : Fin (h + 1) → (I → Bool) → Bool)
    (q : Fin h) (x : ((Fin k × Fin r) × I) → Bool) (i : Fin k) : Fin k :=
  if hi : (gateFailures T label F q x i).Nonempty then hi.choose else i

end Paper320

end

end OAI


