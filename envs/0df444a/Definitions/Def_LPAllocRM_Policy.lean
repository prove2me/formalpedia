-- Prove2me | Definitions.Def_LPAllocRM_Policy
-- name    : LPAllocRM_Policy
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:05:05.662677+00:00
-- url     : https://prove2.me/theorems/564d72a5-fec2-4c7a-b992-35d99972c080
-- title:
--   History-dependent acceptance policy $\pi\in\Pi$
-- statement:
--   A **policy** for $n$ product classes is a rule $\pi$ that, at each time $t$, maps the history of the arrival process up to $t$ to a vector in $\{0,1\}^n$: a one in position $j$ means that a class-$j$ request arriving at $t$ is accepted, a zero that it is rejected. The set $\Pi$ of allowable policies consists of **all** such rules; in particular the rule may depend on the entire history up to $t$, not just on the current counts.
--
--   **Formalization Note** The history up to $t$ is the arrival path restricted to $(-\infty,t]$, closed at $t$, so it includes an arrival at time $t$ ("Recall that $D_j(t)$ includes any class $j$ arrival at time $t$", p.723). A decision at $t$ can only read this restriction, so every policy is nonanticipating by its type. $\{0,1\}$ is `Bool`.
-- source:
--   Cooper, Asymptotic Behavior of an Allocation Policy for Revenue Management, Operations Research 50(4) (2002), doi:10.1287/opre.50.4.720.2855, §2, p.722 (definition of Π after (1))

import Mathlib

namespace LPAllocRM

/-- A history-dependent acceptance policy `π ∈ Π` for `n` product classes. `π t h j = true` means
a class-`j` request arriving at time `t` is accepted when the history of the arrival process up to
and including `t` is `h`; `false` means it is rejected.
Cooper, *Asymptotic Behavior of an Allocation Policy for Revenue Management*, Operations Research 50(4) (2002), doi:10.1287/opre.50.4.720.2855,
§2, p.722 (PDF p.3): "An element π of Π maps (for each t) the history up to t to {0, 1}^n, where a
one in the jth position means a class j arrival will be accepted if it arrives at time t".

**Formalization Note** The history up to `t` is the arrival path restricted to `(−∞, t]`, a function
`Set.Iic t → Fin n → ℕ`. It is closed at `t`, so it includes any arrival at time `t` ("Recall that
D_j(t) includes any class j arrival at time t", p.723). Since a decision at `t` can only read this
restriction, every policy is nonanticipating by its type. `Π` is the set of **all** such maps: no
Markov, allocation or measurability restriction is built into the type (measurability of the
resulting counts is required in `Admissible`). `{0, 1}` is `Bool`. -/
abbrev Policy (n : ℕ) : Type := (t : ℝ) → (Set.Iic t → Fin n → ℕ) → Fin n → Bool

end LPAllocRM


