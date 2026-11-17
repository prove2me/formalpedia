-- Prove2me | Definitions.Def_MCPoise_Supplement_latency
-- name    : MCPoise_Supplement_latency
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:14:19.447863+00:00
-- url     : https://prove2.me/theorems/e8d5496c-6d69-4366-ad3f-690846e992e0
-- title:
--   Views $\varphi^\tau_v(u)$ and information latency $l^\tau_v(u)$ of an infinite schedule
-- statement:
--   Fix an infinite schedule $M$ (a matching $M_\tau$ for each round $\tau \ge 1$). The **view** $\varphi^\tau_v(u)$ of vertex $v$ on vertex $u$ at time $\tau$ is the largest $t' \le \tau$ such that the information $u$ held at time $t'$ reaches $v$ by time $\tau$, through calls of rounds $t'+1, \dots, \tau$ taken in increasing order; it is $0$ if there is no such $t'$. The **information latency** is
--   $$l^\tau_v(u) = \tau - \varphi^\tau_v(u).$$
--
--   In particular $\varphi^\tau_v(v) = \tau$, so $l^\tau_v(v) = 0$, and $\varphi^0_v(u) = 0$.
--
--   The multicommodity vector-clock problems minimize $\max_{i}\max_{\tau \ge 0} l^\tau_{t_i}(s_i)$ (MCMVC) and $\max_{\tau \ge 0}\sum_i l^\tau_{t_i}(s_i)$ (MCAVC).
--
--   **Formalization Note** The value $0$ when no time-respecting path exists is the source's convention that all nodes start with the freshest information. The round-index reading (information of time $t'$ travels in rounds $t'+1, \dots, \tau$) is the same for every schedule compared.
-- source:
--   R. Jain, A. Niaparast, R. Ravi, Polylog Pairwise Poise: Approximating Multicommodity Multicast, STOC 2027 submission (manuscript sha256 2c6a7cc5…), §4.1.1, p.25 (views, latency, MCMVC, MCAVC)

import Mathlib
import Definitions.Def_MCPoise_Supplement_TempReach

namespace MCPoise.Supplement

/-- **The view `ϕ^τ_v(u)`** that `v` has of `u` at time `τ`.
Jain, Niaparast, Ravi, *Polylog Pairwise Poise: Approximating Multicommodity Multicast*, STOC 2027 submission (manuscript sha256 2c6a7cc5…), §4.1.1, p.25: "`ϕ^t_v(u)` is the largest `t′ ≤ t` for which the information of `u` at time `t′` could be
transmitted through the sequence of communications in our fixed schedule `M` and arrive at `v` by time `t`. We
assume that all nodes starts off with the freshest information, and thus `ϕ^0_v(u) = 0` for all pairs of nodes `v` and
`u`. Since every node constantly generates new information, `ϕ^t_v(v) = t` for all `v ∈ V`."

`view M v u τ` is the largest `t′ ≤ τ` with `TempReach M u t′ v τ`, and `0` if there is none.

**Formalization Note.** The set is bounded by `τ`, so `sSup` on `ℕ` is its maximum; on the empty set it is `0`,
which is the source's convention that every node starts with the freshest information (`ϕ ≥ 0`). Since `u` holds
its own information at every time, `view M u u τ = τ`. Reading of the round index: round `τ` is `M τ`, and the
information of time `t′` can travel in rounds `t′ + 1, …, τ`; the same definition serves the output and the
comparator. -/
noncomputable def view (M : ℕ → List (ℕ × ℕ)) (v u τ : ℕ) : ℕ :=
  sSup {t' : ℕ | t' ≤ τ ∧ TempReach M u t' v τ}

/-- **Information latency** `l^τ_v(u) = τ − ϕ^τ_v(u)`.
Jain, Niaparast, Ravi, *Polylog Pairwise Poise: Approximating Multicommodity Multicast*, STOC 2027 submission (manuscript sha256 2c6a7cc5…), §4.1.1, p.25: "The information latency of `v` with respect to `u` at time `t`, denoted by `l^t_v(u)` is given
by `t − ϕ^t_v(u)`".

**Formalization Note.** `view M v u τ ≤ τ`, so the natural-number subtraction is exact. -/
noncomputable def latency (M : ℕ → List (ℕ × ℕ)) (v u τ : ℕ) : ℕ :=
  τ - view M v u τ

end MCPoise.Supplement


