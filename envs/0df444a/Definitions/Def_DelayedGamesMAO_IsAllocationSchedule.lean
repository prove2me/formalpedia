-- Prove2me | Definitions.Def_DelayedGamesMAO_IsAllocationSchedule
-- name    : DelayedGamesMAO_IsAllocationSchedule
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:25:33.927057+00:00
-- url     : https://prove2.me/theorems/46fdc336-c6c9-41d2-8042-b844a9e57a0a
-- title:
--   Definition 1 — allocation schedule
-- statement:
--   Let $(d_t)$ be a delay sequence and $T$ a horizon. A nonnegative array $(\alpha^{(t)}_k)_{1\le k\le t\le T+1}$ is an **allocation schedule** if for every $t\in[T]$:
--
--   1. (S1, monotonicity) $\alpha^{(k)}_t\ge\alpha^{(k+1)}_t$ for all $k=t,\dots,T$;
--   2. (S2, zero tail) $\alpha^{(k)}_t=0$ for all $k\ge t+d_t+1$;
--   3. (S3, capacity) $\sum_{k=1}^t\alpha^{(t)}_k=\sum_{k\in A_t}\alpha^{(t)}_k\le1$.
--
--   $\alpha^{(t)}_k$ is the fraction of regularization weight that the iterate $w_k$ still holds at time $t$.
--
--   **Formalization Note** The array is a function of two naturals, $\alpha\,t\,k=\alpha^{(t)}_k$; only the entries with $1\le k\le t\le T+1$ are constrained, and (S2) is required for $t+d_t+1\le k\le T+1$.
-- source:
--   Esposito–Jacobsen–Qiu–Ryabchenko–Zhang, Optimal Learning in Games with Arbitrary Delays: Best-of-Both-Worlds for Self-Play and Adversarial Opponents, STOC 2027 submission (manuscript sha256 d17ba8b0…1247), §5.1, Definition 1, p.10

import Mathlib
import Definitions.Def_DelayedGamesMAO_active

set_option autoImplicit false

namespace DelayedGamesMAO

/-- **Allocation schedule** (Definition 1).
Esposito–Jacobsen–Qiu–Ryabchenko–Zhang, *Optimal Learning in Games with Arbitrary Delays:
Best-of-Both-Worlds for Self-Play and Adversarial Opponents*, STOC 2027 submission manuscript
(sha256 d17ba8b0…1247), §5.1, Definition 1, p.10: "A nonnegative array `(α_k^{(t)})_{1≤k≤t≤T+1}` is an allocation
schedule if it satisfies the following three properties for all `t ∈ [T]`: (S1) monotonicity:
`α_t^{(k)} ≥ α_t^{(k+1)}` for all `k = t, …, T`, (S2) zero tail: `α_t^{(k)} = 0` for all
`k ≥ t + d_t + 1`, (S3) capacity: `∑_{k=1}^t α_k^{(t)} = ∑_{k∈A_t} α_k^{(t)} ≤ 1`."

`α t k` is `α_k^{(t)}` (superscript first).

**Formalization Note.** Only the entries `1 ≤ k ≤ t ≤ T + 1` are constrained; (S2) ranges over
the array, i.e. `t + d_t + 1 ≤ k ≤ T + 1`. -/
def IsAllocationSchedule (d : ℕ → ℕ) (T : ℕ) (α : ℕ → ℕ → ℝ) : Prop :=
  (∀ t ∈ Finset.Icc 1 (T + 1), ∀ k ∈ Finset.Icc 1 t, 0 ≤ α t k) ∧
  ∀ t ∈ Finset.Icc 1 T,
    (∀ k ∈ Finset.Icc t T, α (k + 1) t ≤ α k t) ∧
    (∀ k ∈ Finset.Icc (t + d t + 1) (T + 1), α k t = 0) ∧
    (∑ k ∈ Finset.Icc 1 t, α t k = ∑ k ∈ active d t, α t k) ∧
    ∑ k ∈ active d t, α t k ≤ 1

end DelayedGamesMAO


