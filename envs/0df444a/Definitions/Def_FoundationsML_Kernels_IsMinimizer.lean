-- Prove2me | Definitions.Def_FoundationsML_Kernels_IsMinimizer
-- name    : FoundationsML_Kernels_IsMinimizer
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T22:59:11.172982+00:00
-- url     : https://prove2.me/theorems/879313d4-beb4-4267-874d-d78bc7b3a36f
-- title:
--   Minimizer of a function (formalization scaffolding)
-- statement:
--   `IsMinimizer F h` says `h` minimizes `F` over its whole domain: `F h ≤ F h'` for every `h'`.
--   Formalization scaffolding for Theorem 6.11's `argmin_{h∈H} F(h)` (p. 117, PDF p. 134), not
--   itself a book-numbered definition.
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, p. 117, Theorem 6.11 (PDF p. 134)

import Mathlib

namespace FoundationsML.Kernels

/-- `h` minimizes `F` over its whole domain: `F h ≤ F h'` for every `h'`. Formalization
scaffolding for Theorem 6.11 (Representer theorem)'s `argmin_{h∈H} F(h)`, not itself a
book-numbered definition. -/
def IsMinimizer {H α : Type*} [Preorder α] (F : H → α) (h : H) : Prop :=
  ∀ h' : H, F h ≤ F h'

end FoundationsML.Kernels


