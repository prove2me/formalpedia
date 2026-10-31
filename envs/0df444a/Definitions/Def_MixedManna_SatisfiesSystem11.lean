-- Prove2me | Definitions.Def_MixedManna_SatisfiesSystem11
-- name    : MixedManna_SatisfiesSystem11
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:13:35.55998+00:00
-- url     : https://prove2.me/theorems/f92ad6ed-858f-4588-99dc-965fc0395ae7
-- title:
--   The market-clearing system (11a)–(11c)
-- statement:
--   Nonnegative prices $p$ and spendings $f$ **satisfy (11a)–(11c)** when
--   $$
--   \begin{aligned}
--   &\forall i\in N: && \textstyle\sum_{k,j\in M^+}f_{ijk}-\sum_{k,j\in M^-}f_{ijk}\le\sum_{j\in M^+}W_{ij}p_j-\sum_{j\in M^-}W_{ij}p_j &(11a)\\
--   &\forall j\in M^-: && \textstyle\sum_{i,k}f_{ijk}\le p_j &(11b)\\
--   &\forall j\in M^+: && \textstyle p_j\le\sum_{i,k}f_{ijk} &(11c)
--   \end{aligned}
--   $$
--   Here $p_j$ is the price of a good and $-p_j$ that of a bad; $f_{ijk}$ is spending on a good and $-f_{ijk}$ earning on a bad. The system expresses that each agent spends at most her budget and every item is paid for.
--
--   **Formalization Note** The complementarity conditions (11a′)–(11c′) are not included.
-- source:
--   Chaudhury, Garg, McGlaughlin, Mehta, Competitive Allocation of a Mixed Manna, arXiv:2008.02753v1, §4.2.1, (11a)–(11c), p.19

import Mathlib
import Definitions.Def_MixedManna_Seg

namespace MixedManna

variable {N M : Type*} [Fintype N] [Fintype M]

open Classical

/-- **The market-clearing system (11a)–(11c)** (Chaudhury, Garg, McGlaughlin, Mehta, *Competitive
Allocation of a Mixed Manna*, arXiv:2008.02753v1, p.19): nonnegative prices `p` and spendings `f`
with

* `(11a)` `∀ i ∈ N`: `Σ_{k,j∈M⁺} f_ijk − Σ_{k,j∈M⁻} f_ijk ≤ Σ_{j∈M⁺} W_ij p_j − Σ_{j∈M⁻} W_ij p_j`;
* `(11b)` `∀ j ∈ M⁻`: `Σ_{i,k} f_ijk ≤ p_j`;
* `(11c)` `∀ j ∈ M⁺`: `p_j ≤ Σ_{i,k} f_ijk`.

`p_j` is the price of a good and `−p_j` that of a bad; `f_ijk` is spending on a good and `−f_ijk`
earning on a bad.

**Formalization Note** The complementarity conditions (11a′)–(11c′) are not part of "(p, f)
satisfies (11a), (11b), (11c)"; the variables are nonnegative as everywhere in the LCP. -/
def SatisfiesSystem11 (I : Instance N M) (p : M → ℝ) (f : Seg I → ℝ) : Prop :=
  (∀ j, 0 ≤ p j) ∧ (∀ σ, 0 ≤ f σ) ∧
  (∀ i, ∑ σ : Seg I, (if segAgent σ = i then itemSign I (segItem σ) * f σ else 0) ≤
      ∑ j, itemSign I j * I.W i j * p j) ∧
  (∀ j, ¬ IsGood I j → (∑ σ : Seg I, if segItem σ = j then f σ else 0) ≤ p j) ∧
  (∀ j, IsGood I j → p j ≤ ∑ σ : Seg I, if segItem σ = j then f σ else 0)

end MixedManna


