-- Prove2me | Definitions.Def_ProcessingNetworks_MArP_jumpCount
-- name    : ProcessingNetworks_MArP_jumpCount
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:28:28.87571+00:00
-- url     : https://prove2.me/theorems/817be46c-53a5-4504-9f9c-1dc41f100485
-- title:
--   The number $J(i,j,t)$ of jumps from $i$ to $j$ up to time $t$
-- statement:
--   Given a jump chain $Y$ with jump times $\sigma_n$, the $(n+1)$-st jump, at time $\sigma_{n+1}$, goes from $Y_n$ to $Y_{n+1}$. For $i\ne j$,
--   $$
--   J(i,j,t)=\#\{n\ge 0:\ \sigma_{n+1}\le t,\ Y_n=i,\ Y_{n+1}=j\},
--   $$
--   and by convention $J(i,i,t)=0$.
--
--   **Formalization Note** The cardinality is `Set.ncard`, which is $0$ on an infinite set. The set is finite whenever $\sigma_n\to\infty$, which holds almost surely for a non-explosive chain. The book counts jumps in $[0,t]$ on p.305 and in $(0,t]$ in Theorem D.26; these agree because no jump occurs at time $0$.
-- source:
--   Dai & Harrison, Processing Networks (pre-publication draft 2020-4-2, spnbook.org), Section E.1, p.305 (PDF p.321); Theorem D.26, p.297 (PDF p.313)

import Mathlib

open Classical

namespace ProcessingNetworks.MArP

/-- The number `J(i, j, t)` of jumps from state `i` to state `j` during `[0, t]`, with the convention
`J(i, i, t) = 0` (Dai & Harrison, Processing Networks, pre-publication draft 2020-4-2, Section E.1,
p.305, PDF p.321; Theorem D.26, p.297, PDF p.313, writes `(0, t]`; there is no jump at time `0`).
The `(n+1)`-st jump, at time `σ_{n+1}`, goes from `Y_n` to `Y_{n+1}`.

**Formalization Note.** `Set.ncard` is `0` on an infinite set. The set is finite on every path with
`σ_n → ∞`, which is almost every path of a non-explosive chain, so the junk value does not arise
there. -/
noncomputable def jumpCount {S Ω : Type*} (Y : ℕ → Ω → S) (σ : ℕ → Ω → ℝ) (i j : S) (t : ℝ)
    (ω : Ω) : ℕ :=
  if i = j then 0 else {n : ℕ | σ (n + 1) ω ≤ t ∧ Y n ω = i ∧ Y (n + 1) ω = j}.ncard

end ProcessingNetworks.MArP


