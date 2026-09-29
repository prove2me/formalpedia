-- Prove2me | Definitions.Def_CompetitivePaging_Combining_punishCount
-- name    : CompetitivePaging_Combining_punishCount
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T13:22:28.616958+00:00
-- url     : https://prove2.me/theorems/4c0c625d-d30e-4082-b4da-51458a1d3bb5
-- title:
--   $v$-intervals and the number of times one paging algorithm punishes another
-- statement:
--   Let $A$ and $B$ be deterministic on-line algorithms with $k$ labelled servers on a vertex set $M$, and let $\sigma=\sigma(1)\sigma(2)\cdots\sigma(N)$ be a request sequence. Time $t\in\{1,\dots,N\}$ is the step at which $\sigma(t)$ is processed; the configuration just after step $t$ is the one after the first $t$ requests, and the configuration "after step $0$" is the initial one.
--
--   1. A pair $(t_1,t_2)$ with $1\le t_1<t_2\le N$ is a **$v$-interval for $A$** if some server of $A$ is moved to the vertex $v$ at step $t_1$ (it is not on $v$ before step $t_1$ and is on $v$ after it), stays on $v$ after every step $s$ with $t_1\le s<t_2$, and is moved away from $v$ at step $t_2$.
--   2. $A$ **punishes** $B$ at time $t_2$ if for some vertex $v$ and some $t_1$ the pair $(t_1,t_2)$ is a $v$-interval for $A$, and for some $(t_1',t_2')$ with
--   $$t_1'\le t_1<t_2'\le t_2$$
--   the pair $(t_1',t_2')$ is a $v$-interval for $B$.
--   3. $\mathrm{PUN}(A,B,s,\sigma)$ is the number of time steps $t\in\{1,\dots,s\}$ at which $A$ punishes $B$.
--
--   Punishments are the accounting device of the sufficiency half of Theorem 6: every punishment is matched with a distinct server move of $B$.
--
--   **Formalization Note** Servers are labelled (`KServer.Config k M = Fin k → M`), and "the server" of a $v$-interval is one label. Following the paper literally, a $v$-interval begins with a move ($t_1\ge1$); a server that sits on $v$ from the start does not open a $v$-interval.
-- source:
--   Fiat, Karp, Luby, McGeoch, Sleator, Young, Competitive Paging Algorithms, arXiv:cs/0205038v1, p. 9 (PDF p. 10), §6, proof of Theorem 6 (sufficiency): definitions of v-interval, punish, PUN(i, s, σ)

import Mathlib
import Definitions.Def_KServer_model

namespace CompetitivePaging.Combining

/-- **`v`-interval** (Fiat et al. 1991, §6, proof of Theorem 6, p. 9). Time `t` (for
`1 ≤ t ≤ |σ|`) is the step at which the `t`-th request of `σ` is processed; the configuration of
`A` just after step `t` is `A.conf (σ.take t)`, and `A.conf (σ.take 0) = A.conf []` is its initial
configuration. The pair `(t₁, t₂)` is a `v`-interval for `A` on `σ` if some server `j` of `A`
is moved to the vertex `v` at step `t₁` (it is not on `v` before step `t₁` and is on `v` after
it), stays on `v` after every step `s` with `t₁ ≤ s < t₂`, and is moved away from `v` at step
`t₂`, where `1 ≤ t₁ < t₂ ≤ |σ|`. -/
def IsVInterval {k : ℕ} {M : Type} [MetricSpace M] (A : KServer.OnlineAlgorithm k M)
    (σ : List M) (v : M) (t₁ t₂ : ℕ) : Prop :=
  1 ≤ t₁ ∧ t₁ < t₂ ∧ t₂ ≤ σ.length ∧
    ∃ j : Fin k, A.conf (σ.take (t₁ - 1)) j ≠ v ∧
      (∀ s : ℕ, t₁ ≤ s → s < t₂ → A.conf (σ.take s) j = v) ∧
      A.conf (σ.take t₂) j ≠ v

/-- **`A` punishes `B` at time `t₂`** (Fiat et al. 1991, §6, proof of Theorem 6, p. 9): for some
vertex `v` and some `t₁`, `(t₁, t₂)` is a `v`-interval for `A`, and for some `(t₁', t₂')` with
`t₁' ≤ t₁ < t₂' ≤ t₂`, `(t₁', t₂')` is a `v`-interval for `B`. -/
def Punishes {k : ℕ} {M : Type} [MetricSpace M] (A B : KServer.OnlineAlgorithm k M)
    (σ : List M) (t₂ : ℕ) : Prop :=
  ∃ (v : M) (t₁ : ℕ), IsVInterval A σ v t₁ t₂ ∧
    ∃ t₁' t₂' : ℕ, t₁' ≤ t₁ ∧ t₁ < t₂' ∧ t₂' ≤ t₂ ∧ IsVInterval B σ v t₁' t₂'

open Classical in
/-- `PUN(A, B, s, σ)`: the number of time steps `t ∈ {1, …, s}` at which `A` punishes `B` while
processing `σ` (Fiat et al. 1991, §6, proof of Theorem 6, p. 9). -/
noncomputable def punishCount {k : ℕ} {M : Type} [MetricSpace M]
    (A B : KServer.OnlineAlgorithm k M) (σ : List M) (s : ℕ) : ℕ :=
  ((Finset.Icc 1 s).filter (fun t => Punishes A B σ t)).card

end CompetitivePaging.Combining


