-- Prove2me | Definitions.Def_MeanBudgetXC_IsLocalSystem
-- name    : MeanBudgetXC_IsLocalSystem
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:38:34.591344+00:00
-- url     : https://prove2.me/theorems/134ab2d8-3370-444f-9a8c-a0ad8701603a
-- title:
--   Consistent system of local laws of context size $d$ and activity $a$
-- statement:
--   A **consistent system of local laws of context size $d$ and activity $a$** on a vertex set $V$ assigns to every context $S\subseteq V$ with $|S|\le d$ a function $\mu_S$ on assignments $x\in\{0,1\}^S$ such that:
--
--   1. $\mu_S$ is a probability law: $\mu_S(x)\ge0$ and $\sum_x\mu_S(x)=1$;
--   2. $\mu_S$ is supported on assignments with at most $a$ ones;
--   3. the laws are consistent: for every $T\subseteq S$, the marginal of $\mu_S$ on $\{0,1\}^T$ is $\mu_T$.
--
--   No joint law on all of $V$ is assumed. At $a=2$ this is the paper's "activity two" system $L_{N,d}$.
--
--   **Formalization Note** An assignment is a function `S → Bool`, with `true` for one. The family $\mu$ is a function on every finite set of vertices; its values on sets with more than $d$ elements are unconstrained and never read. Consistency is required for every nested pair of contexts, including $T=\emptyset$.
-- source:
--   Chao–Gao–Qi–Wang, A Sharp Mean-Budget Transition for Local Pair Marginals, STOC 2027 submission (manuscript sha256 882d9c71…), Section 1.1, p.3, and Section 4, p.17

import Mathlib

namespace MeanBudgetXC

variable {V : Type*} [DecidableEq V]

/-- A **consistent system of local laws of context size `d` and activity `a`**
(Chao–Gao–Qi–Wang, *A Sharp Mean-Budget Transition for Local Pair Marginals*, STOC 2027
submission, manuscript sha256 882d9c71…9e76, Section 1.1, p.3, and Section 4, p.17). For every
context `S ⊆ V` with `|S| ≤ d`, `μ S` is a probability law on `{0,1}^S` (nonnegative, total mass
one), supported on assignments with at most `a` ones, and the laws are consistent: whenever
`T ⊆ S`, the marginal of `μ_S` on `T` is `μ_T`. No joint law on all of `V` is assumed.

**Formalization Note** An assignment on `S` is a function `S → Bool` (`true` = 1). `μ` is given
on every finite set; its values on sets with more than `d` elements are unconstrained and never
used. Consistency is required for every nested pair of contexts, including `T = ∅`. -/
def IsLocalSystem (d a : ℕ) (μ : (S : Finset V) → (S → Bool) → ℝ) : Prop :=
  ∀ S : Finset V, S.card ≤ d →
    (∀ x, 0 ≤ μ S x) ∧ (∑ x, μ S x = 1) ∧
    (∀ x : S → Bool, a < (Finset.univ.filter fun s => x s = true).card → μ S x = 0) ∧
    (∀ (T : Finset V) (hTS : T ⊆ S) (y : T → Bool),
      ∑ x ∈ Finset.univ.filter (fun x : S → Bool => ∀ t : T, x ⟨t.1, hTS t.2⟩ = y t), μ S x
        = μ T y)

end MeanBudgetXC


