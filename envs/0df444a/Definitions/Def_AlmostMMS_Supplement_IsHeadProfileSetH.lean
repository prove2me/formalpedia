-- Prove2me | Definitions.Def_AlmostMMS_Supplement_IsHeadProfileSetH
-- name    : AlmostMMS_Supplement_IsHeadProfileSetH
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:28:17.18331+00:00
-- url     : https://prove2.me/theorems/57668d27-eb30-4f1f-84d9-e37aea7f151f
-- title:
--   Shared set $\Pi$ of head profiles for head size $h$
-- statement:
--   Fix $n$ agents, items $e_1,\dots,e_m$ with values $v_i(e)$, and a head size $h$. A **demand** is a positive value $\alpha$; a **demand profile** is a finite multiset of demands. A profile $\pi$ is a **head profile** for agent $i$ if every $\alpha\in\pi$ equals $v_i(e)$ for some head item $e\le h$.
--
--   A **shared set of head profiles** is a finite collection $\Pi$ that contains the empty profile $\varnothing$ and the no-profile $\bot$, and in which every other member $\pi$ is a head profile for some agent: all demands of $\pi$ are positive, and there is one agent $i$ such that
--   $$
--   \text{every } \alpha\in\pi \text{ equals } v_i(e)\ \text{for some head item } e\le h .
--   $$
--
--   All agents choose their (fractional) head profiles from the same set $\Pi$; in the proof of Theorem 2.1 it consists of $\varnothing$, $\bot$ and the head parts of every agent's MMS bundles.
--
--   **Formalization Note** $\bot$ is `none` and $\varnothing$ is `some 0`; item $e_j$ is position $j-1$, so a head item is a position below $h$. The empty profile is a head profile for every agent and need not name one.
-- source:
--   Feige, Grinberg, Almost-MMS allocations with small agent redundancy, STOC 2027 submission, arXiv:2611.05360 (manuscript sha256 3925c4ab…), Definition 2.1, p.12; Definition 2.7, p.14; Definition 2.13, p.16

import Mathlib

namespace AlmostMMS.Supplement

/-- **Shared set of head profiles with head size `h`** (Definitions 2.1, 2.7, 2.13, pp.12, 14, 16).
Feige, Grinberg, *Almost-MMS allocations with small agent redundancy*, STOC 2027 submission,
arXiv:2611.05360 (manuscript sha256 3925c4ab…): a finite collection `Π` of demand profiles that
contains the empty profile `∅` and the no-profile `⊥`, in which every profile is a head profile for
some agent: its demands `α` are positive (demands, Definition 2.1), and there is one agent `i` such
that every demand `α` equals `v_i(e)` for some head item `e ≤ h` (Definition 2.7).

**Formalization Note.** `⊥` is `none` and `∅` is `some 0`. Item `e_j` is the position
`⟨j - 1, _⟩ : Fin m`, so the head item `e ≤ h` is a position with `e.val < h`. The empty profile is a
head profile for every agent, so it is exempt from naming one (this keeps `Π = {⊥, ∅}` admissible
when there are no agents). -/
def IsHeadProfileSetH {n m : ℕ} (v : Fin n → Fin m → ℝ) (h : ℕ)
    (Ps : Finset (Option (Multiset ℝ))) : Prop :=
  none ∈ Ps ∧ some 0 ∈ Ps ∧
    ∀ p, some p ∈ Ps → (∀ α ∈ p, 0 < α) ∧
      (p = 0 ∨ ∃ i : Fin n, ∀ α ∈ p, ∃ e : Fin m, e.val < h ∧ v i e = α)

end AlmostMMS.Supplement


