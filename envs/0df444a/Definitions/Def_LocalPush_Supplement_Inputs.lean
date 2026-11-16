-- Prove2me | Definitions.Def_LocalPush_Supplement_Inputs
-- name    : LocalPush_Supplement_Inputs
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:17:57.401656+00:00
-- url     : https://prove2.me/theorems/1048034a-2928-4963-9919-0d11ddbde3c4
-- title:
--   Input and output layouts of Theorems 5.11, 6.1 and 6.3
-- statement:
--   The memory layouts through which the supplement's programs receive their parameters, in the style of the base mission's input of Theorem 1.2. All cells, registers and pointers not listed are $0$, and no program is given the number of nodes $n$, the number of edges $m$ or the adjacency lists: the graph is reachable only through the degree and neighbour oracle instructions.
--
--   1. Theorem 5.11: integer cell $0$ holds the seed $s$; real cells $0,1,2,3$ hold $\alpha,\rho,\xi,\delta$. The output vector $\tilde x$ is read from real memory, entry $v$ at address $-1-v$ (the base mission's output convention).
--   2. Theorem 6.1: integer cells $0,1$ hold $s,t$; real cells $0,1,2$ hold $\alpha,\epsilon,\theta$.
--   3. Theorem 6.3: integer cells $0,1$ hold $s,t$; real cells $0,1$ hold $\gamma,\epsilon$.
--
--   The scalar estimate returned in Theorems 6.1 and 6.3 is real memory at address $-1$.
--
--   **Formalization Note** The paper names no input format; these layouts are a reading, like the base mission's.
-- source:
--   Cui, Wei, Yang, Revisiting Local Push, STOC 2027 submission (manuscript sha256 4c36279a…), Theorem 5.11, p.27; Theorem 6.1, p.30; Theorem 6.3, p.32

import Mathlib
import Definitions.Def_LocalPush_Machine

namespace LocalPush

namespace Supplement

/-!
# Input and output layouts of Theorems 5.11, 6.1 and 6.3

Cui, Wei, Yang, *Revisiting Local Push: Faster Algorithms and Optimal Query Complexity for PageRank and
Effective Resistance*, STOC 2027 submission (manuscript sha256 4c36279a…), Theorem 5.11, p.27 (PDF p.27),
Theorem 6.1, p.30 (PDF p.30), Theorem 6.3, p.32 (PDF p.32).

**Formalization Note.** In the style of the base `LocalPush.pushInput` (built with the published
`initState`; every other cell, register and pointer is `0`). The program is never given `n`, `m` or the lists.
* Theorem 5.11 (`l1Input`): integer cell `0` holds the seed `s`; real cells `0, 1, 2, 3` hold `α, ρ, ξ, δ`.
  The output vector `x̃` is the base `outVec n` (real memory at `−1 − v`).
* Theorem 6.1 (`pairInput`): integer cells `0, 1` hold `s, t`; real cells `0, 1, 2` hold `α, ϵ, θ`.
* Theorem 6.3 (`erInput`): integer cells `0, 1` hold `s, t`; real cells `0, 1` hold `γ, ϵ`.
* The scalar output of Theorems 6.1 and 6.3 (`outReal`) is real memory at `−1`.
-/

/-- The input of Theorem 5.11: seed `s` in integer cell `0`; `α, ρ, ξ, δ` in real cells `0, …, 3`. -/
noncomputable def l1Input {n : ℕ} (s : Fin n) (α ρ ξ δ : ℝ) : State :=
  initState [((s : ℕ) : ℤ)] [α, ρ, ξ, δ]

/-- The input of Theorem 6.1: `s, t` in integer cells `0, 1`; `α, ϵ, θ` in real cells `0, 1, 2`. -/
noncomputable def pairInput {n : ℕ} (s t : Fin n) (α ϵ θ : ℝ) : State :=
  initState [((s : ℕ) : ℤ), ((t : ℕ) : ℤ)] [α, ϵ, θ]

/-- The input of Theorem 6.3: `s, t` in integer cells `0, 1`; `γ, ϵ` in real cells `0, 1`. -/
noncomputable def erInput {n : ℕ} (s t : Fin n) (γ ϵ : ℝ) : State :=
  initState [((s : ℕ) : ℤ), ((t : ℕ) : ℤ)] [γ, ϵ]

/-- The scalar output of a state: real memory at address `−1`. -/
def outReal (st : State) : ℝ :=
  st.core.mem (-1)

end Supplement

end LocalPush


