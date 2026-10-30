-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartI_ch05_ch05Continuants
-- name    : RamanujanLostNotebook_PartI_ch05_ch05Continuants
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-11T06:50:46.351325+00:00
-- url     : https://prove2.me/theorems/48c9322f-5499-46af-bb98-c6df77930664
-- title:
--   Ramanujan's Lost Notebook Part I, Ch. 5: ch05Continuants
-- statement:
--   Canonical continuants of b₀+K(aⱼ/bⱼ), with indices starting at 1. The state is ((Pₙ₋₁,Pₙ),(Qₙ₋₁,Qₙ)); P₋₁=1, P₀=b₀, Q₋₁=0, Q₀=1. The recurrence is (5.1.3), p.125, with general denominators for Section 5.5. No division occurs, so zero partial denominators remain polynomial data.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part I, Springer 2005, Chapter 5.

import Mathlib

noncomputable section

namespace RamanujanLostNotebook.PartI

/-- Canonical continuants of b₀+K(aⱼ/bⱼ), with indices starting at 1. The state is ((Pₙ₋₁,Pₙ),(Qₙ₋₁,Qₙ)); P₋₁=1, P₀=b₀, Q₋₁=0, Q₀=1. The recurrence is (5.1.3), p.125, with general denominators for Section 5.5. No division occurs, so zero partial denominators remain polynomial data. -/
def ch05Continuants (b0 : ℂ) (a b : ℕ → ℂ) : ℕ → (ℂ × ℂ) × (ℂ × ℂ)
  | 0 => ((1, b0), (0, 1))
  | n + 1 =>
    let t := ch05Continuants b0 a b n
    ((t.1.2, b (n + 1) * t.1.2 + a (n + 1) * t.1.1),
      (t.2.2, b (n + 1) * t.2.2 + a (n + 1) * t.2.1))

end RamanujanLostNotebook.PartI

end


