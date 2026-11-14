-- Prove2me | Definitions.Def_MOLS
-- name    : MOLS
-- status  : Definition
-- author  : @parclytaxel
-- created : 2026-11-13T11:05:11.478078+00:00
-- url     : https://prove2.me/theorems/f70dde20-9524-48ee-9598-d3918488bf7d
-- title:
--   Definition of mutually orthogonal Latin squares
-- statement:
--   A pair of Latin squares over the same symbol set are **mutually orthogonal** if, when superimposed, the pairs of symbols in each cell are distinct.

import Mathlib.Data.Fintype.Prod

/-- Structure holding a pair of mutually orthogonal Latin squares. -/
@[ext]
structure MOLS (n : ℕ) where
  /-- The pair of Latin squares as a function from coordinates to symbol pairs -/
  f : Fin n × Fin n → Fin n × Fin n
  /-- No two symbol pairs repeat -/
  f_inj : f.Injective
  /-- No two symbols repeat in a row for the first square -/
  r₁_inj (r) : (fun c ↦ (f (r, c)).1).Injective
  /-- No two symbols repeat in a row for the second square -/
  r₂_inj (r) : (fun c ↦ (f (r, c)).2).Injective
  /-- No two symbols repeat in a column for the first square -/
  c₁_inj (c) : (fun r ↦ (f (r, c)).1).Injective
  /-- No two symbols repeat in a column for the second square -/
  c₂_inj (c) : (fun r ↦ (f (r, c)).2).Injective
deriving DecidableEq


