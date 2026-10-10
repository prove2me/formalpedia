-- Prove2me | Definitions.Def_TitiusBode_Defs
-- name    : TitiusBode_Defs
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-09T21:26:14.926242+00:00
-- url     : https://prove2.me/theorems/8f5c852b-a841-4b42-a1a5-d0d1ffac3367
-- title:
--   Titius–Bode and Dermott laws: basic definitions
-- statement:
--   Basic objects of the Titius–Bode and Dermott laws.
--
--   1. The extended power of two $2^n$ for $n \in \{-\infty, 0, 1, 2, \dots\}$, with $2^{-\infty} = 0$.
--   2. The sequence $x_0 = 0$, $x_1 = 3$, $x_{i+2} = 2x_{i+1}$, i.e. $x = 0, 3, 6, 12, 24, \dots$, and the original formulation $a = 4 + x_i$ (Earth $= 10$).
--   3. The form $a(n) = 4 + 3\cdot 2^n$ (Earth $= 10$) and the form in astronomical units $a(n) = 0.4 + 0.3 \cdot 2^n$, both for $n \in \{-\infty, 0, 1, 2, \dots\}$.
--   4. The canonical form $a_n = 0.4 + 0.3\cdot 2^n$ for $n \in \mathbb N$.
--   5. The recursive form as printed in the source: $a_0 = 0.55$, $a_{n+1} = 2a_n - 0.4$.
--   6. The relative deviation $(d - p)/p$ of an observed value $d$ from a prediction $p$.
--   7. Dermott's law $T(n) = T(0)\,C^n$.
--
--   These are the shared definitions for every statement of the mission.
--
--   **Formalization Note** The exponent $-\infty$ is the bottom element of the natural numbers with a bottom adjoined. The deviation is the plain real quotient (Lean returns $0$ when $p = 0$); statements only use it at positive $p$. Dermott's period is defined for every $n \in \mathbb N$; the source uses $n \ge 1$.
-- source:
--   Wikipedia, "Titius–Bode law", revision oldid=1372822920, https://en.wikipedia.org/w/index.php?title=Titius%E2%80%93Bode_law&oldid=1372822920, sections "Original formulation" and "Data"; Wikipedia, "Dermott's law", revision oldid=1315813288, https://en.wikipedia.org/w/index.php?title=Dermott%27s_law&oldid=1315813288

import Mathlib

namespace TitiusBode

/-- The extended power of two used by the Titius–Bode law: `2 ^ n` for a natural
number `n`, and `2 ^ (-∞) = 0` for the formal exponent `n = -∞` (encoded as `⊥`). -/
noncomputable def twoPowExt : WithBot ℕ → ℝ
  | ⊥ => 0
  | (n : ℕ) => 2 ^ n

/-- The sequence `x = 0, 3, 6, 12, 24, 48, 96, 192, 384, 768, …` of the original
Titius–Bode formulation: `x₀ = 0`, `x₁ = 3`, and from then on each value is twice the
previous one. -/
def tbX : ℕ → ℕ
  | 0 => 0
  | 1 => 3
  | (i + 2) => 2 * tbX (i + 1)

/-- The original Titius–Bode formulation `a = 4 + x`, in units in which the Earth's
semi-major axis equals `10`; `i = 0, 1, 2, …` indexes the terms of `x`. -/
def tbOriginal (i : ℕ) : ℕ := 4 + tbX i

/-- The second representation `a = 4 + 3 × 2 ^ n`, `n = -∞, 0, 1, 2, …`, in units in
which the Earth's semi-major axis equals `10`. -/
noncomputable def tbTenths (n : WithBot ℕ) : ℝ := 4 + 3 * twoPowExt n

/-- The Titius–Bode distance in astronomical units, `a = 0.4 + 0.3 × 2 ^ n`,
`n = -∞, 0, 1, 2, …`. These are the predicted positions of the law. -/
noncomputable def tbAU (n : WithBot ℕ) : ℝ := 0.4 + 0.3 * twoPowExt n

/-- The "classical" (canonical) form `aₙ = 0.4 + 0.3 × 2 ^ n`, `n = 0, 1, 2, …`. -/
noncomputable def tbCanonical (n : ℕ) : ℝ := 0.4 + 0.3 * 2 ^ n

/-- The "recursive" form as printed in the source: `a₀ = 0.55` and
`aₙ₊₁ = 2 × aₙ - 0.4`. -/
noncomputable def tbRecursive : ℕ → ℝ
  | 0 => 0.55
  | (n + 1) => 2 * tbRecursive n - 0.4

/-- Relative deviation of an observed value from a predicted value,
`(observed - predicted) / predicted` (multiply by `100` for a percentage). -/
noncomputable def deviation (observed predicted : ℝ) : ℝ :=
  (observed - predicted) / predicted

/-- Dermott's law: the orbital period of the `n`-th satellite is `T(n) = T(0) · C ^ n`
(the source uses `n = 1, 2, 3, …`). -/
noncomputable def dermottPeriod (T₀ C : ℝ) (n : ℕ) : ℝ := T₀ * C ^ n

end TitiusBode


