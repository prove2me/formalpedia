-- Prove2me | Definitions.Def_FoundationsML_Stability_IsMinimizer
-- name    : FoundationsML_Stability_IsMinimizer
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-20T04:23:21.192285+00:00
-- url     : https://prove2.me/theorems/c33a7f0b-a507-447e-8c4d-1c511f6c153a
-- title:
--   Minimizer of a function
-- statement:
--   **Formalization scaffolding for `argmin_{h∈H} F_S(h)` ((14.6), p. 336, PDF p. 353), not
--   itself a book-numbered definition.** `h` minimizes `F` over its whole domain: `F h ≤ F h'`
--   for every `h'`.
--
--   **Formalization Note.** Restated locally in `Stability`, byte-identical to chunk
--   `06-kernels`'s own copy.
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, (14.6), p. 336 (PDF p. 353)

import Mathlib

namespace FoundationsML.Stability

/-- `h` minimizes `F` over its whole domain: `F h ≤ F h'` for every `h'`. Formalization
scaffolding for the kernel-based regularization algorithm's `h_S = argmin_{h∈H} F_S(h)`
(Mohri, Rostamizadeh & Talwalkar, *Foundations of Machine Learning*, 2nd ed., MIT Press 2018,
(14.6), p. 336, PDF p. 353), not itself a book-numbered definition.

**Formalization Note.** Restated locally in `Stability`, byte-identical to chunk `06-kernels`'s
own copy (drafts cannot import another chunk's draft module). -/
def IsMinimizer {H α : Type*} [Preorder α] (F : H → α) (h : H) : Prop :=
  ∀ h' : H, F h ≤ F h'

end FoundationsML.Stability


