-- Prove2me | Definitions.Def_BeatingGV42_IsAsympOptimal
-- name    : BeatingGV42_IsAsympOptimal
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:33:08.44749+00:00
-- url     : https://prove2.me/theorems/3a42c468-8342-4995-b514-7a7da5b3dacb
-- title:
--   Asymptotically optimal sequence of function fields
-- statement:
--   Let $(F_i/\mathbb F_Q)_{i\ge 1}$ be a sequence of function fields with genera $g_i\to\infty$, and let $N_i=B_1(F_i)$ be the number of rational places of $F_i$. The sequence is **asymptotically optimal** if
--   $$
--   \lim_{i\to\infty}\frac{N_i}{g_i}=\sqrt Q-1 .
--   $$
--   By the Drinfeld–Vlăduţ bound this is the largest possible ratio. Asymptotically optimal sequences exist when $Q$ is a square (Garcia–Stichtenoth), and they supply the mother codes of Proposition 4.9.
--
--   **Formalization Note** `Fs : ℕ → FunctionFieldOver k`, indexed from $0$, with $Q$ = `Nat.card k`. The §4.3 standing assumption $g_i\to\infty$ (`AlgebraicCurve.genusFF`) is the first conjunct; the ratio is a real division (junk at $g_i=0$ affects finitely many terms).
-- source:
--   Cohen, Manket, Beating the Gilbert–Varshamov Bound at Alphabet Size 42, manuscript of October 24, 2026 (STOC 2027 submission; held version sha256 da05fc8e…eb595), §4.3 and Definition 4.6, p.17 (PDF p.19)

import Mathlib
import Definitions.Def_BeatingGV42_FunctionFieldOver
import Definitions.Def_BeatingGV42_numPlaces

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Filter Topology

universe u

namespace BeatingGV42

/-- **Asymptotically optimal sequence of function fields** (Cohen, Manket, *Beating the Gilbert–Varshamov Bound at Alphabet Size 42*, manuscript of October 24, 2026 (held version sha256 da05fc8e…), §4.3 and Definition 4.6, p.17
(PDF p.19)): "Let (F_i/F_Q)^∞_{i=1} be a sequence of function fields with genera g_i → ∞ … The
sequence (F_i/F_Q)^∞_{i=1} is asymptotically optimal if lim_{i→∞} N_i/g_i = √Q − 1", where
`N_i = B_1(F_i)` is the number of rational places.

**Formalization Note** The sequence is indexed by `i : ℕ` (from `0`). The §4.3 standing assumption
`g_i → ∞` is the first conjunct; `g_i` is the platform's `AlgebraicCurve.genusFF`. `Q = Nat.card k`.
The ratio `N_i/g_i` is a real division; its junk value at `g_i = 0` occurs for finitely many `i` at
most and does not affect the limit. -/
def IsAsympOptimal {k : Type u} [Field k] (Fs : ℕ → FunctionFieldOver k) : Prop :=
  Tendsto (fun i => AlgebraicCurve.genusFF k (Fs i).carrier) atTop atTop ∧
    Tendsto (fun i => (numPlaces k (Fs i).carrier 1 : ℝ) / (AlgebraicCurve.genusFF k (Fs i).carrier : ℝ))
      atTop (𝓝 (Real.sqrt (Nat.card k) - 1))

end BeatingGV42


