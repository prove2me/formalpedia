-- Prove2me | Definitions.Def_EnvelopeMSLP_lpValue
-- name    : EnvelopeMSLP_lpValue
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:24:49.610312+00:00
-- url     : https://prove2.me/theorems/f82a31d4-77fc-49ba-8c5b-f4fb1ee26444
-- title:
--   Extended optimal value of a linear objective
-- statement:
--   For a set $S\subseteq\mathbb R^\iota$ and an objective $c$, the value is
--   $$V=\sup\{\langle c,x\rangle : x\in S\}\in[-\infty,+\infty].$$
--   It equals $-\infty$ on an empty set and $+\infty$ when the objective is unbounded above. All three linear programs of the paper read their optimal value off this one definition.
--
--   **Formalization Note** The supremum is computed in `EReal`, so no junk real value arises.
-- source:
--   Terça and Wozabal, Envelope Theorems for Multi-Stage Linear Stochastic Optimization, preprint (PDF of 2018-06-18), displays (1), (4), (6), pp.5, 8, 10

import Mathlib
open Matrix

namespace EnvelopeMSLP

/-- **Extended optimal value of a linear objective over a set.**
Terça and Wozabal, *Envelope Theorems for Multi-Stage Linear Stochastic Optimization*, preprint (PDF of 2018-06-18), displays (1), (4), (6), pp.5, 8, 10:
`sup {⟨c, x⟩ : x ∈ S}` computed in `EReal`.

**Formalization Note.** The value lies in `EReal`, so it is `⊥` on an empty feasible set and `⊤`
on an objective that is unbounded above; no junk real value arises. -/
noncomputable def lpValue {ι : Type*} [Fintype ι] (S : Set (ι → ℝ)) (c : ι → ℝ) : EReal :=
  sSup ((fun x => ((c ⬝ᵥ x : ℝ) : EReal)) '' S)

end EnvelopeMSLP


