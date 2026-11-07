-- Prove2me | Definitions.Def_BeatingGV42_MinDistAtLeast
-- name    : BeatingGV42_MinDistAtLeast
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:31:18.946799+00:00
-- url     : https://prove2.me/theorems/55746b7a-de19-4dd1-8498-727dcc9f2b38
-- title:
--   Minimum distance at least $d$ of a $q$-ary code
-- statement:
--   Let $q,n\ge 0$ be integers and let $C\subseteq[q]^n$ be a **$q$-ary code of length $n$**, where $[q]=\{0,\dots,q-1\}$. For a real number $d$, the code $C$ has **minimum distance at least $d$** if every two distinct codewords differ in at least $d$ coordinates:
--   $$
--   \forall x,y\in C,\quad x\ne y\ \Longrightarrow\ \Delta(x,y)\ge d,
--   $$
--   where $\Delta(x,y)=|\{i : x_i\ne y_i\}|$ is the Hamming distance. A code with relative distance at least $\delta$ is one with minimum distance at least $\delta n$.
--
--   The paper measures codes by their rate and relative minimum distance, "the smallest fraction of coordinates on which two distinct codewords differ"; this predicate is the distance half of that measurement and is used by every code-existence statement of the mission.
--
--   **Formalization Note** A code is a `Finset (Fin n → Fin q)` and $\Delta$ is Mathlib's `hammingDist`. The bound $d$ is real. A code with at most one word satisfies the predicate for every $d$.
-- source:
--   Cohen, Manket, Beating the Gilbert–Varshamov Bound at Alphabet Size 42, manuscript of October 24, 2026 (STOC 2027 submission; held version sha256 da05fc8e…eb595), §1, p.1 (PDF p.3)

import Mathlib

set_option autoImplicit false

namespace BeatingGV42

/-- **Minimum distance at least `d`** (Cohen, Manket, *Beating the Gilbert–Varshamov Bound at Alphabet Size 42*, manuscript of October 24, 2026 (held version sha256 da05fc8e…), §1, p.1 (PDF p.3)): a code
`C ⊆ [q]ⁿ` has minimum distance at least `d` when every two *distinct* codewords differ in at
least `d` coordinates. "Its relative minimum distance, δ, is the smallest fraction of coordinates
on which two distinct codewords differ."

**Formalization Note** A `q`-ary code of length `n` is a `Finset (Fin n → Fin q)`, the alphabet
being `Fin q = {0, …, q − 1}`; distance is Mathlib's `hammingDist`. The bound `d` is real so that
a relative distance `δ` is expressed as `MinDistAtLeast C (δ * n)`. A code with at most one word
satisfies the predicate for every `d` (there are no pairs of distinct codewords). -/
def MinDistAtLeast {n q : ℕ} (C : Finset (Fin n → Fin q)) (d : ℝ) : Prop :=
  ∀ x ∈ C, ∀ y ∈ C, x ≠ y → d ≤ (hammingDist x y : ℝ)

end BeatingGV42


