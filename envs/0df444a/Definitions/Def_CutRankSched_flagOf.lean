-- Prove2me | Definitions.Def_CutRankSched_flagOf
-- name    : CutRankSched_flagOf
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T13:34:21.829596+00:00
-- url     : https://prove2.me/theorems/788010d1-f0d4-4eab-a55d-40a64c0903fd
-- title:
--   Descending flag $U^k_s$ of a partial assignment (9)
-- statement:
--   For a partial assignment $\lambda_1, \dots, \lambda_k$ of the first $k$ events, the **descending weak flag** at cut $k$ is
--   $$
--   U^k_s = \operatorname{span}\{\, a^{(k)}_j : j \le k,\ \lambda_j \ge s \,\} \le R_k, \qquad s \in [L],
--   $$
--   so that $U^k_1 \supseteq \cdots \supseteq U^k_L$. It records, for every threshold $s$, which future anticommutations the events placed in layers $\ge s$ impose.
--
--   **Formalization Note** 0-based layers: threshold `s : Fin L` is the paper's $s+1$, and $\lambda_j \ge s$ is `s ≤ lam j`. Only the values of the assignment on the first $k$ events enter.
-- source:
--   Zhao, Chen, Li, Kong, Peng, Yu and Yue, Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling, STOC 2027 submission (manuscript sha256 20eb83d2…), Section 5.3, Eq. (9), p.9

import Mathlib
import Definitions.Def_CutRankSched_Instance
import Definitions.Def_CutRankSched_signature

set_option autoImplicit false

namespace CutRankSched

/-- The descending flag (9) of a partial assignment at cut `k` (Zhao–Chen–Li–Kong–Peng–Yu–Yue, *Cut-Rank Dynamic Programming for Fixed-Event Hardware-Constrained Pauli-Rotation Scheduling*, STOC 2027 submission manuscript (sha256 20eb83d2…49473878), §5.3, Eq. (9), p.9):
`U^k_s = span{a^{(k)}_j : j ≤ k, λ_j ≥ s}`, `s ∈ [L]`; `U^k_1 ⊇ ⋯ ⊇ U^k_L`.

**Formalization Note** 0-based layers: `s : Fin L` is the paper's `s + 1`, and `λ_j ≥ s` is
`s ≤ lam j`. Signatures are zero-padded (`signature`). Only the values of `lam` on events
`j.val < k` matter. -/
def flagOf (I : Instance) (L k : ℕ) (lam : Fin I.n → Fin L) :
    Fin L → Submodule (ZMod 2) (Fin I.n → ZMod 2) :=
  fun s => Submodule.span (ZMod 2) {v | ∃ j : Fin I.n, j.val < k ∧ s ≤ lam j ∧ v = signature I k j}

end CutRankSched


