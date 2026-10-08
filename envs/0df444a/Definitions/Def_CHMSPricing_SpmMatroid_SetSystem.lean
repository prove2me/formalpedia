-- Prove2me | Definitions.Def_CHMSPricing_SpmMatroid_SetSystem
-- name    : CHMSPricing_SpmMatroid_SetSystem
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T10:56:30.588006+00:00
-- url     : https://prove2.me/theorems/cc2773f6-13f3-43da-92b0-4150405a6837
-- title:
--   Downward-closed set systems, the matroid augmentation axiom, and the rank of a set
-- statement:
--   A **feasibility constraint** on a finite set of agents is a set system $\mathcal J$ of subsets (the feasible sets) that is **downward closed**: $\emptyset \in \mathcal J$, and $B \in \mathcal J$, $A \subseteq B$ imply $A \in \mathcal J$ (§2.1).
--
--   The set system is a **matroid** (§4.1) if, in addition, it satisfies the augmentation axiom: for every $A, B \in \mathcal J$ with $|A| > |B|$ there is $e \in A \setminus B$ with $B \cup \{e\} \in \mathcal J$. (Heredity, the first matroid axiom, is downward closure.)
--
--   The **rank** of a set $S$ of agents (§4) is the size of a largest feasible subset of $S$:
--
--   $$\operatorname{rank}(S) = \max_{S' \subseteq S,\ S' \in \mathcal J} |S'|.$$
--
--   These are the combinatorial objects of the mission: Theorem 5 is stated for matroid constraints, and the rank bounds the service probabilities of any feasible mechanism.
--
--   **Formalization Note** The maximum is a genuine maximum over a finite nonempty family (the empty set is a feasible subset of every $S$). The paper's own matroid axioms are used rather than Mathlib's `Matroid`.
-- source:
--   Chawla, Hartline, Malec and Sivan, Multi-parameter Mechanism Design and Sequential Posted Pricing, arXiv:0907.2435v2, p. 4, §2.1; p. 6, §4 (rank) and §4.1 (matroid axioms)

import Mathlib

namespace CHMSPricing.SpmMatroid

/-- A downward-closed set system `𝒥 ⊆ 2^α` (the feasibility constraint of §2.1, p. 4):
the empty set is feasible and every subset of a feasible set is feasible. -/
structure SetSystem (α : Type*) [Fintype α] [DecidableEq α] where
  Feasible : Finset α → Prop
  feasible_empty : Feasible ∅
  feasible_mono : ∀ ⦃A B : Finset α⦄, A ⊆ B → Feasible B → Feasible A

namespace SetSystem

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- §4.1, p. 6: the set system is a matroid. Heredity is `feasible_mono`; this is the
augmentation axiom: for feasible `A, B` with `|A| > |B|` some `e ∈ A \ B` has `B ∪ {e}`
feasible. -/
def IsMatroid (J : SetSystem α) : Prop :=
  ∀ A B : Finset α, J.Feasible A → J.Feasible B → B.card < A.card →
    ∃ e ∈ A \ B, J.Feasible (insert e B)

open Classical in
/-- §4, p. 6: `rank(S) = max_{S' ⊆ S, S' ∈ 𝒥} |S'|`, the size of a largest feasible subset of `S`
(a genuine maximum: `∅` is a feasible subset of every `S`). -/
noncomputable def rank (J : SetSystem α) (S : Finset α) : ℕ :=
  (S.powerset.filter J.Feasible).sup Finset.card

end SetSystem

end CHMSPricing.SpmMatroid


