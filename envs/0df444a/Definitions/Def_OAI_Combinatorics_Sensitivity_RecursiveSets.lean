-- Prove2me | Definitions.Def_OAI_Combinatorics_Sensitivity_RecursiveSets
-- name    : OAI_Combinatorics_Sensitivity_RecursiveSets
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T01:26:55.977644+00:00
-- url     : https://prove2.me/theorems/158866c5-bef1-4fd8-8a5e-11b832ed2eeb
-- title:
--   Coordinates through which a single child changes a member of the family
-- statement:
--   Work on the coordinate set $([k] \times [r]) \times I$ of the recursive construction, with $I$ finite and $[n] = \{0, \dots, n-1\}$. The children of an input $x$ are $x[j,c] \in \{0,1\}^I$, $x[j,c](a) = x((j,c), a)$; let $F = (F_0, \dots, F_{h-1})$ be a family of Boolean functions on $\{0,1\}^I$, and write $y^{\{a\}}$ for $y$ with coordinate $a$ flipped.
--
--   1. **Embedding into one copy.** For an element $j$ of a set $J$ and a finite set $A \subseteq I$, the set $\{j\} \times A = \{ (j,a) : a \in A \} \subseteq J \times I$. A pair $(j',a)$ belongs to it exactly when $j' = j$ and $a \in A$, and it has exactly $|A|$ elements.
--
--   2. **Sensitive coordinates of a child.** For an index $q$, a row $j$ and a column $c$,
--   $$
--   \mathrm{Ch}_q(x; j, c) = \{ ((j,c), a) : a \in I,\ F_q(x[j,c]^{\{a\}}) \ne F_q(x[j,c]) \},
--   $$
--   whose size is the sensitivity $s(F_q, x[j,c])$.
--
--   3. **Jointly sensitive coordinates of a child.** For two indices $q, q'$,
--   $$
--   \mathrm{Ch}_{q,q'}(x; j, c) = \{ ((j,c), a) : F_q(x[j,c]^{\{a\}}) \ne F_q(x[j,c]) \text{ and } F_{q'}(x[j,c]^{\{a\}}) \ne F_{q'}(x[j,c]) \},
--   $$
--   whose size is the joint sensitivity $s(F_q, F_{q'}; x[j,c])$.
--
--   These sets locate, among the raw coordinates of the next level, the coordinates through which a single child changes its value; the sensitivity of a row-clause predicate is bounded by covering its sensitive coordinates with a few such sets.
--
--   **Formalization Note** The definitions are `childLift`, `childChanges` and `childJointChanges`; the simp lemmas `mem_childLift`, `childLift_card`, `childChanges_card` and `childJointChanges_card` give the membership rule and the three cardinality identities.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Sensitivity/RecursiveSets.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Sensitivity/RecursiveSets.lean by skeleton subtraction
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

namespace OAI

/-! Finite sets of changing raw coordinates inside an individual child. -/

noncomputable section
open scoped Classical

namespace Paper320

def childLift {J I : Type} (j : J) (A : Finset I) : Finset (J × I) :=
  A.map ⟨fun a => (j, a), fun _ _ h => congrArg (fun p : J × I => p.2) h⟩

@[simp] theorem mem_childLift {J I : Type} (j : J) (A : Finset I) (p : J × I) :
    p ∈ childLift j A ↔ p.1 = j ∧ p.2 ∈ A := by
  rcases p with ⟨k, a⟩
  unfold childLift
  rw [Finset.mem_map]
  constructor
  · rintro ⟨b, hb, hp⟩
    change (j, b) = (k, a) at hp
    cases hp
    exact ⟨rfl, hb⟩
  · rintro ⟨rfl, ha⟩
    exact ⟨a, ha, rfl⟩

@[simp] theorem childLift_card {J I : Type} (j : J) (A : Finset I) :
    (childLift j A).card = A.card := Finset.card_map _

def childChanges {k r h : ℕ} {I : Type} [Fintype I]
    (F : Fin h → (I → Bool) → Bool) (q : Fin h)
    (x : ((Fin k × Fin r) × I) → Bool) (j : Fin k) (c : Fin r) :
    Finset ((Fin k × Fin r) × I) :=
  childLift (j, c) (Finset.univ.filter fun a =>
    F q (flip (recursiveChild x j c) {a}) ≠ F q (recursiveChild x j c))

def childJointChanges {k r h : ℕ} {I : Type} [Fintype I]
    (F : Fin h → (I → Bool) → Bool) (q q' : Fin h)
    (x : ((Fin k × Fin r) × I) → Bool) (j : Fin k) (c : Fin r) :
    Finset ((Fin k × Fin r) × I) :=
  childLift (j, c) (Finset.univ.filter fun a =>
    F q (flip (recursiveChild x j c) {a}) ≠ F q (recursiveChild x j c) ∧
    F q' (flip (recursiveChild x j c) {a}) ≠ F q' (recursiveChild x j c))

@[simp] theorem childChanges_card {k r h : ℕ} {I : Type} [Fintype I]
    (F : Fin h → (I → Bool) → Bool) (q : Fin h)
    (x : ((Fin k × Fin r) × I) → Bool) (j : Fin k) (c : Fin r) :
    (childChanges F q x j c).card = sensitivityAt (F q) (recursiveChild x j c) := by
  simp [childChanges, sensitivityAt]

@[simp] theorem childJointChanges_card {k r h : ℕ} {I : Type} [Fintype I]
    (F : Fin h → (I → Bool) → Bool) (q q' : Fin h)
    (x : ((Fin k × Fin r) × I) → Bool) (j : Fin k) (c : Fin r) :
    (childJointChanges F q q' x j c).card =
      jointSensitivityAt (F q) (F q') (recursiveChild x j c) := by
  simp [childJointChanges, jointSensitivityAt]

end Paper320

end

end OAI


