-- Prove2me | Definitions.Def_GrothendieckLB_IsSignFn
-- name    : GrothendieckLB_IsSignFn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:46:27.638411+00:00
-- url     : https://prove2.me/theorems/327ff025-1007-46fc-9924-a9872de5ed9f
-- title:
--   Measurable sign function
-- statement:
--   A function $F$ on a measurable space is a **sign function** if it is measurable and takes values in $\{-1,+1\}$. The sign pairs $(f,g)$ of Part II of the paper are pairs of such functions on $\mathbb R^d$.
--
--   **Formalization Note** No oddness is included, because Definition 10.1 of the paper has none.
-- source:
--   Saha et al., New Lower and Upper Bounds for the Grothendieck Constant, arXiv:2608.11158 (held version, sha256 e7eb5d65…), Section 7, p.31; Definition 10.1, p.42

import Mathlib

namespace GrothendieckLB

/-- A measurable sign function `F : α → {±1}` (Saha et al., *New Lower and Upper Bounds for the Grothendieck Constant*, arXiv:2608.11158 (held version, sha256 e7eb5d65…), Section 7, p.31; Definition 10.1, p.42).

**Formalization Note** No oddness: Definition 10.1 has none. -/
def IsSignFn {α : Type*} [MeasurableSpace α] (F : α → ℝ) : Prop :=
  Measurable F ∧ ∀ x, F x = 1 ∨ F x = -1

end GrothendieckLB


