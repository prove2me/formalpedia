-- Prove2me | Definitions.Def_PrivLittlestone_gammaTerm
-- name    : PrivLittlestone_gammaTerm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:23:04.175521+00:00
-- url     : https://prove2.me/theorems/6d86bfb7-d82f-46cc-97a8-f67293d9d212
-- title:
--   Insertion mass factor $\gamma = e^\eta\sum_{j=1}^D B^j e^{-aj}$
-- statement:
--   For a ranked candidate system of height $D$ and branching $B$, and scales $\eta, a$,
--   $$
--   \gamma = e^{\eta} \sum_{j=1}^{D} B^j e^{-aj}.
--   $$
--   It bounds the relative weight introduced by one retained record (Lemma 3.1).
-- source:
--   He–He, Private Online Learning of Littlestone Classes and Matroid Flats, STOC 2027 submission (manuscript sha256 21480556…c562), Lemma 3.1, p.5

import Mathlib

namespace PrivLittlestone

/-- The insertion mass factor `γ = e^η ∑_{j=1}^D B^j e^{−aj}` (He–He, *Private Online Learning of
Littlestone Classes and Matroid Flats*, STOC 2027 submission manuscript (sha256 21480556…c562),
Lemma 3.1, p.5). -/
noncomputable def gammaTerm (η a B : ℝ) (D : ℕ) : ℝ :=
  Real.exp η * ∑ j ∈ Finset.Icc 1 D, B ^ j * Real.exp (-a * (j : ℝ))

end PrivLittlestone


