-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartI_ch06_ch6Continuants
-- name    : RamanujanLostNotebook_PartI_ch06_ch6Continuants
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-11T10:50:08.914563+00:00
-- url     : https://prove2.me/theorems/fa45b1be-1bdf-4a37-a2ac-de2f8c835d0d
-- title:
--   Ramanujan's Lost Notebook Part I, Ch. 6: ch6Continuants
-- statement:
--   Continuants for d₀+u₁/d₁+⋯+uₙ/dₙ. State ((Aₙ₋₁,Aₙ),(Bₙ₋₁,Bₙ)) starts at ((1,d₀),(0,1)); both sequences satisfy Xₙ=dₙXₙ₋₁+uₙXₙ₋₂. The finite fraction is Aₙ/Bₙ, its reciprocal Bₙ/Aₙ. Polynomial recurrence avoids assigning values to intermediate divisions by zero.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part I, Springer 2005, Chapter 6.

import Mathlib

noncomputable section

namespace RamanujanLostNotebook.PartI

/-- Continuants for d₀+u₁/d₁+⋯+uₙ/dₙ. State ((Aₙ₋₁,Aₙ),(Bₙ₋₁,Bₙ)) starts at ((1,d₀),(0,1)); both sequences satisfy Xₙ=dₙXₙ₋₁+uₙXₙ₋₂. The finite fraction is Aₙ/Bₙ, its reciprocal Bₙ/Aₙ. Polynomial recurrence avoids assigning values to intermediate divisions by zero. -/
def ch6Continuants (u d : ℕ → ℂ) : ℕ → (ℂ × ℂ) × (ℂ × ℂ)
  | 0 => ((1, d 0), (0, 1))
  | n + 1 =>
    let s := ch6Continuants u d n
    ((s.1.2, d (n + 1) * s.1.2 + u (n + 1) * s.1.1),
     (s.2.2, d (n + 1) * s.2.2 + u (n + 1) * s.2.1))

end RamanujanLostNotebook.PartI

end


