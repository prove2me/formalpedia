-- Prove2me | Definitions.Def_KumarSeidman_Reentrant_System
-- name    : KumarSeidman_Reentrant_System
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T11:38:31.64526+00:00
-- url     : https://prove2.me/theorems/7e223c81-b3c1-4ca2-924f-58bc29574663
-- title:
--   §I, items 1)–4), p. 289 — a manufacturing system: routes μ, input rates d, processing times τ, set-up times δ
-- statement:
--   A **manufacturing system** in the sense of Kumar and Seidman has part types $p = 1, \dots, P$ and machines $m = 1, \dots, M$.
--
--   1. Parts of type $p$ follow a fixed route of length $n_p \ge 1$: their $i$-th operation is performed at machine $\mu_{p,i}$, and while they wait for it they are stored in a **buffer** $b_{p,i}$. A route may visit the same machine more than once.
--   2. Parts of type $p$ arrive at the constant rate $d_p > 0$.
--   3. Each part in buffer $b_{p,i}$ needs processing time $\tau_{p,i} > 0$ (so $\tau_{p,i}^{-1}$ is the processing rate).
--   4. The buffers served by machine $m$ form $B_m = \{b_{p,i} : \mu_{p,i} = m\}$. When machine $m$ switches from processing buffer $b \in B_m$ to processing buffer $b' \in B_m$ it incurs a **set-up time** $\delta_{b,b'} \ge 0$.
--
--   The **cumulative input** $u_b(t)$ of a buffer over $[0,t]$ is determined by the cumulative outputs $y$ of all buffers: the first buffer of route $p$ receives the external arrivals, $u_{p,1}(t) = d_p t$, and every later buffer receives exactly the output of its predecessor on the route,
--   $$u_{p,i+1}(t) = y_{p,i}(t).$$
--   The output of the last buffer of a route leaves the system.
--
--   These are the data of every result of the paper; Example 1 instantiates them for a single re-entrant part type on two machines.
--
--   **Formalization Note** Part types are `Fin P`, machines `Fin M`, and a buffer is a pair `⟨p, i⟩` with `i : Fin (n p)`; the paper's index $i$ (from 1) is the Lean index $i-1$. The route is a function `route` of the buffer, so $B_m$ is the set of buffers with `route b = m`. Set-up times are a function of an ordered pair of buffers; only pairs at the same machine are ever used, and a run that continues on the same buffer pays nothing (`δ b b = 0`), as the paper charges $\delta_{b,b'}$ only when the machine switches. Transport delays and assembly, which the paper omits "purely for notational convenience", are not modelled.
-- source:
--   Kumar & Seidman, Dynamic Instabilities and Stabilization Methods in Distributed Real-Time Scheduling of Manufacturing Systems, IEEE Trans. Automat. Control 35(3), 1990, p. 289, §I items 1)–4); p. 290, §II (u_{p,i}, y_{p,i})

import Mathlib

namespace KumarSeidman.Reentrant

/-- The buffers `b_{p,i}` of a manufacturing system with part types `Fin P` and route lengths
`n p`: a buffer is a pair `⟨p, i⟩` with `i : Fin (n p)`. The paper's index `i` (from `1`) is the
Lean index `i - 1` (from `0`). -/
abbrev Buffer (P : ℕ) (n : Fin P → ℕ) : Type := Σ p : Fin P, Fin (n p)

/-- A manufacturing system (Kumar–Seidman 1990, §I, items 1)–4), p. 289), with part types
`Fin P`, machines `Fin M` and route lengths `n p > 0`.

* `route ⟨p, i⟩ = μ_{p,i}` is the machine at which parts of type `p` receive their `i`-th
  operation; they wait for it in buffer `b_{p,i}`.
* `d p > 0` is the (constant) input rate of parts of type `p`.
* `τ ⟨p, i⟩ > 0` is the processing time per part at buffer `b_{p,i}`.
* `δ b b' ≥ 0` is the set-up time incurred when the machine serving `b` and `b'` switches from
  processing `b` to processing `b'`; only pairs at the same machine are ever used. A run that
  continues on the same buffer pays nothing, recorded as `δ b b = 0`. -/
structure System (P M : ℕ) (n : Fin P → ℕ) where
  n_pos : ∀ p, 0 < n p
  route : Buffer P n → Fin M
  d : Fin P → ℝ
  d_pos : ∀ p, 0 < d p
  τ : Buffer P n → ℝ
  τ_pos : ∀ b, 0 < τ b
  δ : Buffer P n → Buffer P n → ℝ
  δ_nonneg : ∀ b b', 0 ≤ δ b b'
  δ_self : ∀ b, δ b b = 0

/-- The cumulative input `u_b(t)` of buffer `b` over `[0, t]`, given the cumulative outputs `y`
of all buffers (§II, p. 290): the first buffer of route `p` receives the external arrivals
`d_p t`; buffer `b_{p,i+1}` receives exactly the output of `b_{p,i}` (no transport delay). The
output of the last buffer of a route leaves the system. -/
def System.input {P M : ℕ} {n : Fin P → ℕ} (S : System P M n) (y : Buffer P n → ℝ → ℝ)
    (b : Buffer P n) (t : ℝ) : ℝ :=
  if h : (b.2 : ℕ) = 0 then S.d b.1 * t
  else y ⟨b.1, ⟨(b.2 : ℕ) - 1, by have := b.2.isLt; omega⟩⟩ t

end KumarSeidman.Reentrant


