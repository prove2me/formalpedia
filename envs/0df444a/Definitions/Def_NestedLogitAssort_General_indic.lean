-- Prove2me | Definitions.Def_NestedLogitAssort_General_indic
-- name    : NestedLogitAssort_General_indic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:47:37.934905+00:00
-- url     : https://prove2.me/theorems/65c0ee40-caaa-45f1-a8ec-abd5d475fcd1
-- title:
--   0–1 vector of an assortment
-- statement:
--   An assortment $S\subseteq N$ corresponds to the vector $z\in\{0,1\}^n$ with $z_j=1$ if $j\in S$ and $z_j=0$ otherwise.
-- source:
--   Davis, Gallego & Topaloglu, Assortment Optimization under Variants of the Nested Logit Model, revised manuscript of June 18, 2013, Section 1

import Mathlib

namespace NestedLogitAssort.General

/-- **The 0–1 vector of an assortment.**
Davis, Gallego & Topaloglu, *Assortment Optimization under Variants of the Nested Logit Model*,
revised manuscript of June 18, 2013, Section 1 (unnumbered): an assortment `S ⊂ N` corresponds to the vector `z ∈ {0,1}^n`
with `z_j = 1` exactly when `j ∈ S`. -/
noncomputable def indic {n : ℕ} (S : Finset (Fin n)) : Fin n → ℝ :=
  fun j => if j ∈ S then (1 : ℝ) else 0

end NestedLogitAssort.General


