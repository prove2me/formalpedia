-- Prove2me | Definitions.Def_d9ExtendFinitePrefix
-- name    : d9ExtendFinitePrefix
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-08T08:07:25.434989+00:00
-- url     : https://prove2.me/theorems/5744626e-c1f6-4e52-9c78-0988030f14ec
-- title:
--   d9ExtendFinitePrefix
-- statement:
--   Automatically extracted helper definition d9ExtendFinitePrefix from oversized parent candidate 029f41399a9b5b2cc3817d3867fba60227809162ca9c89b493c85daffb84e989.
-- source:
--   candidate-decomposition:304a5ba4-c3fe-4878-9ae0-c209084c89c1:029f41399a9b5b2cc3817d3867fba60227809162ca9c89b493c85daffb84e989

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
open NestedSeatAlloc.IntPolicy

/-- Extend a finite coordinate tuple by zero outside its support. -/
def d9ExtendFinitePrefix (S : Finset ℕ) (z : S → ℝ) (i : ℕ) : ℝ :=
  if hi : i ∈ S then z ⟨i, hi⟩ else 0


