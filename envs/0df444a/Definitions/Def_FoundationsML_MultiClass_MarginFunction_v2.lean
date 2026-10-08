-- Prove2me | Definitions.Def_FoundationsML_MultiClass_MarginFunction_v2
-- name    : FoundationsML_MultiClass_MarginFunction_v2
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-10-06T05:16:04.546878+00:00
-- url     : https://prove2.me/theorems/5be55c43-74df-4e96-abb9-3d2c9a161488
-- title:
--   Multi-class margin $\rho_h(x,y)$ (p. 215) — corrected
-- statement:
--   **Margin of a multi-class scoring function (p. 215, PDF p. 232).** For a scoring function $h : X\times Y\to\mathbb R$ and a labeled example $(x,y)$, $\rho_h(x,y) = h(x,y) - \max_{y'\neq y} h(x,y')$; $h$ misclassifies $(x,y)$ iff $\rho_h(x,y)\le0$.
--
--   **Formalization Note.** Corrected re-issue of the retired module of the same name. The retired module wrote the maximum as `⨆ y' ∈ {y' | y' ≠ y}, h (x, y')`, which on $\mathbb R$ equals $\max(\max_{y'\ne y}h(x,y'),0)$ (the inner supremum over the empty index $y'=y$ is `sSup ∅ = 0`), not the book's margin when all competing scores are negative. The maximum is now `sSup` of the image of exactly the set $\{y'\mid y'\neq y\}$, which for a finite label set with at least two labels is the book's $\max_{y'\neq y}$; consuming theorems assume $k\ge2$.
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, p. 215 (PDF p. 232)

import Mathlib

namespace FoundationsML.MultiClass

/-- The margin `ρ_h(x,y)` of a multi-class scoring function `h : X × Y → ℝ` at a labeled
example `(x,y)` (Mohri, Rostamizadeh & Talwalkar, *Foundations of Machine Learning*, 2nd ed.,
MIT Press 2018, p. 215, PDF p. 232): `ρ_h(x,y) = h(x,y) − max_{y'≠y} h(x,y')`. The hypothesis
`h` misclassifies `(x,y)` iff `ρ_h(x,y) ≤ 0`.

**Formalization Note.** The maximum over the labels `y' ≠ y` is the real supremum `sSup` of
the image of the set `{y' | y' ≠ y}` under `y' ↦ h(x,y')`, i.e. a supremum over exactly that
set; for a finite label set `Y` with at least two elements it is the book's `max_{y'≠y}`.
(The retired module wrote `⨆ y' ∈ {y' | y' ≠ y}, h (x, y')`, which on `ℝ` unfolds to
`⨆ y', ⨆ (_ : y' ≠ y), h (x, y')` and equals `max(max_{y'≠y} h(x,y'), 0)` because the inner
supremum over the empty index `y' = y` is `sSup ∅ = 0`; this is not the book's margin when all
competing scores are negative.) When `Y = {y}` is a singleton the set is empty and the value
is `h(x,y) − 0`, outside the book's multi-class setting (`k ≥ 2`), which every consuming
theorem assumes explicitly. -/
noncomputable def MarginFunction {X Y : Type*} (h : X × Y → ℝ) (x : X) (y : Y) : ℝ :=
  h (x, y) - sSup ((fun y' : Y => h (x, y')) '' {y' : Y | y' ≠ y})

end FoundationsML.MultiClass


