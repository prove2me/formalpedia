-- Prove2me | Definitions.Def_KServerConj_IsWFATraj
-- name    : KServerConj_IsWFATraj
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:50:04.172192+00:00
-- url     : https://prove2.me/theorems/d2ce4b9a-980a-406f-b89d-0f2714bc094c
-- title:
--   Trajectories of the Work Function Algorithm, and their cost
-- statement:
--   Given $k$, $C_0$ and requests $r_1,\dots,r_T$, a sequence of configurations $C_0,C_1,\dots,C_T$ is a **WFA trajectory** if $C_0$ is the initial configuration and, for every $1\le t\le T$, the configuration $C_t$ has $k$ points, contains $r_t$, and minimizes
--
--   $$w_t(Y)+D(C_{t-1},Y)$$
--
--   over all configurations $Y$ of $k$ points with $r_t\in Y$. The cost of the trajectory is $\mathrm{WFA}_{C_0}(r_1,\dots,r_T)=\sum_{t=1}^T D(C_{t-1},C_t)$.
--
--   The **Work Function Algorithm** (WFA) moves in this way: at each request it balances the offline cost of the new configuration against the cost of moving there. The paper fixes a lazy tie-break ($C_t\subseteq C_{t-1}\cup\{r_t\}$) "for simplicity", noting that the result extends to any other tie-breaking rule.
--
--   **Formalization Note** Every tie-break is allowed: any minimizer over all configurations containing $r_t$ is a valid move, and the lazy trajectory is one of the trajectories. Values $C_t$ for $t>T$ are unconstrained.
-- source:
--   Coester, Koutsoupias, Zbysiński, The k-server conjecture is true, arXiv:2609.15979 (version of 2026-11-03, sha256 7ca0380a…), §1.1, p.2 (pdf p.3)

import Mathlib
import Definitions.Def_KServerConj_workFn

namespace KServerConj

/-- **A trajectory of the Work Function Algorithm**, Coester, Koutsoupias, Zbysiński, *The k-server
conjecture is true*, arXiv:2609.15979 (version of 2026-11-03, sha256 7ca0380a…), §1.1, printed p.2
(PDF p.3):

"To serve the request at time t, the work function algorithm (WFA) moves to a configuration
C_t ∋ r_t minimizing w_t(C_t) + D(C_{t−1}, C_t). For simplicity, we assume here a lazy
implementation with C_t ⊆ C_{t−1} ∪ {r_t}, although our result extends to any other tie-breaking
rule."

`IsWFATraj k C₀ r T C` says: `C 0 = C₀`, and for every `1 ≤ t ≤ T` the configuration `C t` has `k`
points, contains `r t`, and minimizes `w_t(Y) + D(C (t-1), Y)` over **all** configurations `Y` of
`k` points containing `r t`.

**Formalization Note.** Every tie-break is allowed: the lazy minimizer of the paper is one such
trajectory, and Lemma 1.1 is stated for "any WFA trajectory". Requests are `r 1, …, r T`; values of
`C t` for `t > T` are unconstrained. -/
def IsWFATraj {M : Type*} [PseudoMetricSpace M] (k : ℕ) (C₀ : Finset M) (r : ℕ → M) (T : ℕ)
    (C : ℕ → Finset M) : Prop :=
  C 0 = C₀ ∧ ∀ t, 1 ≤ t → t ≤ T → (C t).card = k ∧ r t ∈ C t ∧
    ∀ Y : Finset M, Y.card = k → r t ∈ Y →
      workFn k C₀ r t (C t) + confDist (C (t - 1)) (C t) ≤ workFn k C₀ r t Y + confDist (C (t - 1)) Y

/-- **The cost of a trajectory**, `WFA_{C₀}(r₁, …, r_T) = ∑_{t=1}^T D(C_{t−1}, C_t)` for a WFA
trajectory `C` (§1.1, printed p.2, PDF p.3: "paying movement cost D(C_{t−1}, C_t)"). -/
noncomputable def wfaCost {M : Type*} [PseudoMetricSpace M] (C : ℕ → Finset M) (T : ℕ) : ℝ :=
  ∑ t ∈ Finset.Icc 1 T, confDist (C (t - 1)) (C t)

end KServerConj


