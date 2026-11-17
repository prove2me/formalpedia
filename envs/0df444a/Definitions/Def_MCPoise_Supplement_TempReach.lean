-- Prove2me | Definitions.Def_MCPoise_Supplement_TempReach
-- name    : MCPoise_Supplement_TempReach
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:12:44.939928+00:00
-- url     : https://prove2.me/theorems/3c4c0a05-29ba-4c97-b83d-1716228bde90
-- title:
--   Propagation of information in the telephone model (time-respecting paths)
-- statement:
--   In the **telephone model** a schedule is a sequence of rounds; in round $r$ a set $M_r$ of calls (edges) is active, and the two endpoints of a call exchange all the information they hold.
--
--   For a sequence of rounds $M_1, M_2, \dots$, a vertex $u$, and times $a \le r$, we say that $v$ **holds at time $r$ the information $u$ held at time $a$** when this follows from the rules
--
--   1. at time $a$, $u$ holds it;
--   2. whoever holds it at time $r$ still holds it at time $r+1$;
--   3. if $v$ holds it at time $r$ and $\{v, w\} \in M_{r+1}$, then $w$ holds it at time $r+1$.
--
--   Equivalently, there are vertices $u = w_0, w_1, \dots, w_m = v$ and rounds $a < \tau_1 < \dots < \tau_m \le r$ with $\{w_{j-1}, w_j\} \in M_{\tau_j}$ for every $j$ (a time-respecting path).
--
--   This single relation gives both the delivery of messages in a finite multicast schedule and the views of the vector-clock problems.
--
--   **Formalization Note** A call of round $r+1$ acts on what its endpoints held at time $r$, so both endpoints exchange everything simultaneously and information crosses at most one call per round. Vertices are natural numbers; that the calls are edges forming a matching is checked separately.
-- source:
--   R. Jain, A. Niaparast, R. Ravi, Polylog Pairwise Poise: Approximating Multicommodity Multicast, STOC 2027 submission (manuscript sha256 2c6a7cc5…), §1, p.2 (Telephone Model); §4.1.1, p.25 (definition of the view)

import Mathlib

namespace MCPoise.Supplement

/-- **Propagation of information in the telephone model.**
Jain, Niaparast, Ravi, *Polylog Pairwise Poise: Approximating Multicommodity Multicast*, STOC 2027 submission (manuscript sha256 2c6a7cc5…), §1, p.2: "each round allows endpoints to exchange all the information they hold"; §4.1.1, p.25: "`ϕ^t_v(u)` is
the largest `t′ ≤ t` for which the information of `u` at time `t′` could be transmitted through the sequence of
communications in our fixed schedule `M` and arrive at `v` by time `t`".

For a sequence of rounds `M` (round `r ≥ 1` is the list of calls `M r`), `TempReach M u a v r` says that vertex
`v` holds, at time `r`, the information that vertex `u` held at time `a`:
* at time `a`, `u` holds it;
* whoever holds it at time `r` still holds it at time `r + 1`;
* if `v` holds it at time `r` and `{v, w}` is a call of round `r + 1`, then `w` holds it at time `r + 1`.

Equivalently, there are vertices `u = w₀, …, w_m = v` and rounds `a < τ₁ < ⋯ < τ_m ≤ r` with `{w_{j−1}, w_j}` a call
of round `τ_j`.

**Formalization Note.** A call of round `r + 1` acts on the holders at time `r`, so both endpoints exchange
everything they held before the round, simultaneously, and information crosses at most one call per round. Vertices
are numbers (`ℕ`); a schedule's calls are checked to be edges separately (`IsMatchingRound`). -/
inductive TempReach (M : ℕ → List (ℕ × ℕ)) (u a : ℕ) : ℕ → ℕ → Prop
  | start : TempReach M u a u a
  | wait {v r : ℕ} : TempReach M u a v r → TempReach M u a v (r + 1)
  | call {v w r : ℕ} : TempReach M u a v r → ((v, w) ∈ M (r + 1) ∨ (w, v) ∈ M (r + 1)) →
      TempReach M u a w (r + 1)

end MCPoise.Supplement


