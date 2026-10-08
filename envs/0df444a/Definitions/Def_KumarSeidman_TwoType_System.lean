-- Prove2me | Definitions.Def_KumarSeidman_TwoType_System
-- name    : KumarSeidman_TwoType_System
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:17:19.630991+00:00
-- url     : https://prove2.me/theorems/1aabd73e-0304-4b50-82dd-2d9c2555e35f
-- title:
--   §I, p. 289 — manufacturing system data: part types, routes, input rates, processing and set-up times
-- statement:
--   This module fixes the data of a manufacturing system in the sense of Kumar and Seidman (§I, items 1–4).
--
--   There are $P$ part types and $M$ machines. Parts of type $p$ arrive at rate $d_p$ and follow a fixed route of $n_p$ stages; at stage $i$ they wait in buffer $b_{p,i}$, located at machine $\mu_{p,i}$. The set of buffers located at machine $m$ is
--   $$
--   B_m=\{\,b_{p,i} : \mu_{p,i}=m\,\}.
--   $$
--   Processing one part at buffer $b_{p,i}$ takes $\tau_{p,i}$ time units, so machine $\mu_{p,i}$ works on $b_{p,i}$ at rate at most $1/\tau_{p,i}$. When a machine switches from buffer $b$ to buffer $b'$ it must first spend the set-up time $\delta_{b,b'}$, during which it processes nothing.
--
--   The module also defines the machine $\mu_b$ and the processing time $\tau_b$ of a buffer $b$. These data are the vocabulary of every statement in the mission.
--
--   **Formalization Note** Part types are `Fin P` and machines `Fin M`; a buffer is a pair $(p,i)$ with $i\in\{0,\dots,n_p-1\}$, so the paper's stage $i$ is Lean index $i-1$. The structure holds data only: the sign conditions $0<d_p$, $0<\tau_{p,i}$, $0\le\delta_{b,b'}$ are hypotheses of the theorems. As in the paper, there is no assembly and no transport delay.
-- source:
--   Kumar & Seidman, Dynamic Instabilities and Stabilization Methods in Distributed Real-Time Scheduling of Manufacturing Systems, IEEE Trans. Automat. Control 35(3), 1990, p. 289, §I items 1–4

import Mathlib

namespace KumarSeidman.TwoType

/-- The data of a manufacturing system in the sense of Kumar–Seidman (1990), §I, items 1–4
(p. 289), without assembly and without transport delays (as in the paper).

* `P` part types `Fin P` and `M` machines `Fin M`;
* part type `p` follows a route of length `n p`, visiting machine `μ p i` at its stage `i`
  (Lean index `i` is the paper's index `i + 1`); its parts wait in buffer `b_{p,i}`;
* `d p` is the input rate of part type `p`;
* `τ p i` is the processing time of one part at buffer `b_{p,i}` (so machine `μ p i` works on
  that buffer at rate at most `1 / τ p i`);
* `δ b b'` is the set-up time a machine needs to switch from buffer `b` to buffer `b'`.

The structure carries data only; the sign conditions of the paper (`0 < n p`, `0 < d p`,
`0 < τ p i`, `0 ≤ δ b b'`) are hypotheses of the theorems that use a system. -/
structure System where
  P : ℕ
  M : ℕ
  n : Fin P → ℕ
  μ : (p : Fin P) → Fin (n p) → Fin M
  d : Fin P → ℝ
  τ : (p : Fin P) → Fin (n p) → ℝ
  δ : (Σ p : Fin P, Fin (n p)) → (Σ p : Fin P, Fin (n p)) → ℝ

namespace System

variable (S : System)

/-- A buffer `b_{p,i}`: a part type `p` together with a stage `i` of its route. -/
abbrev Buffer : Type := Σ p : Fin S.P, Fin (S.n p)

/-- The machine `μ_{p,i}` at which buffer `b_{p,i}` is located. -/
def mach (b : S.Buffer) : Fin S.M := S.μ b.1 b.2

/-- The processing time `τ_{p,i}` of buffer `b_{p,i}`. -/
def procTime (b : S.Buffer) : ℝ := S.τ b.1 b.2

end System

end KumarSeidman.TwoType


