-- Prove2me | Definitions.Def_GenSort_passOutcome
-- name    : GenSort_passOutcome
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:29:41.677208+00:00
-- url     : https://prove2.me/theorems/d2bbf853-2878-495b-8168-9c20719596c9
-- title:
--   One error isolation pass, given its sample
-- statement:
--   A single pass on the current edge set $E$, with parameters $s, t$ of §3.5:
--   1. Query the $M' = 16d(s + \lceil 2^{10}s\log n\rceil)$ sampled edges. If fewer than $s + \lceil 2^{10}s\log n\rceil$ of them are bad, terminate this pass with nothing removed. Otherwise the first $s$ bad edges are the training edges and the next $\lceil 2^{10}s\log n\rceil$ are the validation edges.
--   2. Let $S$ be the multiset of right endpoints of the training edges; query all edges of $E$ at the vertices of $S$ and mark every left vertex incident to a queried bad edge; for every ordering $\tau$ of $S$ form $C_\tau$.
--   3. Remove $C_{\tau'}$, where $\tau'$ is the ordering whose candidate set misses the fewest validation edges.
--
--   The result is the new edge set and the number of queries made.
--
--   **Formalization Note** The pass queries all $M'$ sampled edges (the page's budget "within $16d \cdot (s + 2^{10}s\log n)$ many samples and queries"). "We terminate prematurely" ends this pass only. $\log = \log_2$.
-- source:
--   Khanna, Putterman, Song, A Near-Optimal Generalized Sorting Algorithm, STOC 2027 submission (preprint of November 3, 2026, sha256 f1b5a9aa…), §3.5 "A Single Error Isolation Pass", steps 1–3, pp.9–10 (PDF pp.11–12)

import Mathlib
import Definitions.Def_GenSort_sPar
import Definitions.Def_GenSort_mPar
import Definitions.Def_GenSort_passSamples
import Definitions.Def_GenSort_TieRules
import Definitions.Def_GenSort_removalSet

namespace GenSort

/-- **One error isolation pass, given its sample**, Khanna–Putterman–Song, *A Near-Optimal Generalized Sorting Algorithm*, STOC 2027 submission (preprint of November 3, 2026, sha256 f1b5a9aa…), §3.5 "A Single Error Isolation Pass",
steps 1–3, pp.9–10 (PDF pp.11–12), with `s = sPar n d`, `t` inside `ρ.Q`, `m = mPar n d`
validation edges and budget `M' = passSamples n d = 16d(s + m)`.

The `M'` sampled edges `y` of the current edge set `E` are queried. If fewer than `s + m` of
them are bad, the pass ends with nothing removed. Otherwise the first `s` bad ones are the
training edges, with right endpoints `S`, and the next `m` are the validation edges; all edges of
`E` at the vertices of `S` are queried; the ordering `τ' = ρ.τsel E S val` is chosen and
`C_τ'` is removed. The result is the new edge set and the number of queries made.

**Formalization Note.** The pass queries all `M'` sampled edges (the page's budget, "within
`16d · (s + 2^10 s log n)` many samples and queries"). "We terminate prematurely" ends this pass
only, with no edge removed. -/
noncomputable def passOutcome {n : ℕ} {L R : Type*} [DecidableEq L] [DecidableEq R]
    (E : Finset (L × R)) (ℓ : L → Fin n) (r : R → Fin n) (π : Equiv.Perm (Fin n)) (d : ℕ)
    (ρ : TieRules L R (sPar n d)) (y : Fin (passSamples n d) → E) : Finset (L × R) × ℕ :=
  open Classical in
  let bl : List (L × R) := (List.ofFn fun i => (y i : L × R)).filter fun p =>
    decide (π.symm (r p.2) < π.symm (ℓ p.1))
  if h : sPar n d + mPar n d ≤ bl.length then
    let S : Fin (sPar n d) → R := fun i => (bl.get ⟨i, by have := i.isLt; omega⟩).2
    let val := (bl.drop (sPar n d)).take (mPar n d)
    (E \ removalSet E ℓ r π S (ρ.Q E S (ρ.τsel E S val)),
      passSamples n d + (E.filter fun p => ∃ i, p.2 = S i).card)
  else (E, passSamples n d)

end GenSort


