-- Prove2me | Definitions.Def_SplayDynOpt_IsNormalSchedule
-- name    : SplayDynOpt_IsNormalSchedule
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T15:59:22.321817+00:00
-- url     : https://prove2.me/theorems/c1b0c123-cad1-434f-bce0-941ce73b7d12
-- title:
--   Normal-form schedules $T^*$ with parameters $k,C$
-- statement:
--   A **normal-form schedule** with parameters $k,C$ for an access sequence $X$ on $[n]$ is an execution $T_0,\dots,T_\ell;\ t_1\le\dots\le t_m$ in the root BST model such that:
--
--   1. every $T_i$ with $0\le i\le\ell$ is $k$-ribless and has height at most $C\log_2 n$;
--   2. every $T_i$ with $1\le i\le\ell$ is obtained from $T_{i-1}$ by one rotation of a key of depth at most $k$ in $T_{i-1}$.
--
--   Its cost is $\operatorname{cost}(T^*)=m+\ell$. These are the three properties of the paper's nearly optimal tree $T^*$, which hold simultaneously at all times: riblessness, rotations at constant depth and logarithmic depth.
--
--   The later milestones are stated for every such schedule, with constants depending only on $k$ and $C$.
--
--   **Formalization Note** Mathlib's `BinaryTree.height` counts the nodes on a longest root-to-leaf path, which is the largest key depth plus one. Since the bound is $O(\log n)$ this does not matter for $n\ge2$. At $n=1$ no schedule exists under this definition, since a tree of height $1$ does not fit under $C\log_2 1=0$; the statements using it are trivial there.
-- source:
--   Chmel et al., Splay trees are almost dynamically optimal, arXiv:2607.18498 (version of 2026-11-02, sha256 6881e83c…), §5.1, p.14; Theorem 2, pp.14–15; §5.5, p.37 (T* pays 1 per access)

import Mathlib
import Definitions.Def_SplayDynOpt_OPT
import Definitions.Def_SplayDynOpt_kRibless

set_option autoImplicit false

namespace SplayDynOpt

/-- A **normal-form schedule** `T*` with parameters `k, C` for the access sequence `X` on `[n]`:
an execution in the root BST model (`IsExecution`) such that
1. every tree `Tᵢ`, `0 ≤ i ≤ ℓ`, is `k`-ribless and has height at most `C · log₂ n`;
2. every rotation `Tᵢ₋₁ → Tᵢ`, `1 ≤ i ≤ ℓ`, rotates a key of depth at most `k` in `Tᵢ₋₁`.
Its cost is `cost(T*) = m + ℓ` ("the nearly optimal tree T∗ pays 1 for each access", p.37).

Chmel et al., *Splay trees are almost dynamically optimal*, arXiv:2607.18498 (version of
2026-11-02, sha256 6881e83c…), §5.1, p.14: "a nearly optimal tree T∗ […] which has the following
properties simultaneously at all times. 1. T∗ is ribless […] 2. All rotations in T∗ happen within
constant depth of the root. 3. The depth of T∗ is O(log n)."

**Formalization Note.** `BinaryTree.height` counts the nodes on a longest root-to-leaf path (the
maximum key depth plus one). The constants `k, C` are parameters: statements about `T*` are made
for every `k, C`, with constants depending on them. Access times are non-decreasing. -/
def IsNormalSchedule (k C : ℕ) (n : ℕ) (X : List ℕ) (E : Execution) : Prop :=
  IsExecution n X E ∧
  (∀ i ≤ E.len, kRibless k (E.tree i) ∧ ((E.tree i).height : ℝ) ≤ C * Real.logb 2 n) ∧
  (∀ i, 1 ≤ i → i ≤ E.len → IsRotationWithin k (E.tree (i - 1)) (E.tree i))

end SplayDynOpt


