-- Prove2me | Definitions.Def_BalancedKneser_IsBalancedEF
-- name    : BalancedKneser_IsBalancedEF
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:44:42.689396+00:00
-- url     : https://prove2.me/theorems/0212733f-186d-480b-b8d9-3bbc80c227f4
-- title:
--   Balanced allocations and balanced EF$c$ allocations for two groups
-- statement:
--   Goods $M$ (a finite set) are divided between two prescribed nonempty groups of agents: the first group, with $q_1$ agents and valuations $u^{(1)}_1,\dots,u^{(1)}_{q_1}$, and the second group, with $q_2$ agents and valuations $u^{(2)}_1,\dots,u^{(2)}_{q_2}$. Every member of a group receives the same bundle. An allocation is specified by the bundle $A\subseteq M$ of the first group; the second group receives $A^c=M\setminus A$.
--
--   1. The allocation is **balanced** if the two bundle sizes differ by at most one: $\big||A|-|A^c|\big|\le 1$. For $|M|=2n$ this means $|A|=n$.
--   2. It is a **balanced EF$c$ allocation** if it is balanced, every first-group agent accepts $A$ as EF$c$ against $A^c$, and every second-group agent accepts $A^c$ as EF$c$ against $A$ (see the EF$c$ acceptance definition).
--
--   **Formalization Note** The groups are indexed by $\mathrm{Fin}\,q_1$ and $\mathrm{Fin}\,q_2$; the allocation is the first group's bundle $A$. When $|M|$ is odd, either group may receive the larger bundle.
-- source:
--   Alipour, Jafari, Balanced Fair Division and Generalized Kneser Graphs, arXiv:2611.04486v1, §1, p.1 (PDF p.3) and §2, p.3 (PDF p.5): balanced allocation, balanced EFc

import Mathlib
import Definitions.Def_BalancedKneser_AcceptsEF

namespace BalancedKneser

/-- **Balanced allocation** (Alipour–Jafari, arXiv:2611.04486v1, §1, p.1 (PDF p.3)). Goods
`M` are divided between two groups; the first group receives `A`, the second its complement
`Aᶜ = M ∖ A`. The allocation is balanced when the two bundle sizes differ by at most one.

Formalization Note: an allocation is encoded by the first group's bundle `A`. For an even
number `2n` of goods this says `|A| = n` (the source's "n-set A", §2, p.3); for an odd number
either group may receive the larger bundle. -/
def IsBalanced {M : Type*} [Fintype M] [DecidableEq M] (A : Finset M) : Prop :=
  A.card ≤ (Finset.univ \ A).card + 1 ∧ (Finset.univ \ A).card ≤ A.card + 1

/-- **Balanced EFc allocation** (Alipour–Jafari, arXiv:2611.04486v1, §1, p.1 and §2, p.3
(PDF pp.3, 5)). The first group has `q₁` agents with valuations `u₁ i`, the second `q₂` agents
with valuations `u₂ j`. Every member of a group receives the same bundle: the first group gets
`A`, the second `Aᶜ`. The allocation `A` is a balanced EFc allocation when it is balanced and
every agent of each group accepts it as EFc (`AcceptsEF`) against the other group's bundle.

Formalization Note: the groups are prescribed by the index types `Fin q₁` and `Fin q₂`; agents
in the same group share one bundle. -/
def IsBalancedEF {M : Type*} [Fintype M] [DecidableEq M] {q₁ q₂ : ℕ} (c : ℕ)
    (u₁ : Fin q₁ → Finset M → ℝ) (u₂ : Fin q₂ → Finset M → ℝ) (A : Finset M) : Prop :=
  IsBalanced A ∧ (∀ i, AcceptsEF c (u₁ i) A (Finset.univ \ A)) ∧
    (∀ j, AcceptsEF c (u₂ j) (Finset.univ \ A) A)

end BalancedKneser


