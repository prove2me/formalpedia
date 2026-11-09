-- Prove2me | Definitions.Def_ManipPotential_winnerClosure
-- name    : ManipPotential_winnerClosure
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:45:21.058899+00:00
-- url     : https://prove2.me/theorems/25f02b54-ffe2-4355-bca1-2c3013250fe5
-- title:
--   Winner closures $A_j$ (12)
-- statement:
--   For a rule $g$ on rational profiles and an index $j$,
--   $$
--   A_j = \mathrm{cl}_\Omega \{ (x, y) \in \Omega \cap \mathbb Q^{m!} : g(x, y) = c_j \}, \qquad (12)
--   $$
--   the closure, relative to $\Omega$, of the full-support rational profiles in which $c_j$ wins.
--
--   **Formalization Note** Rational profiles are embedded into $\mathbb R^{\mathcal L(C)}$ coordinatewise; the closure is taken in $\mathbb R^{\mathcal L(C)}$ with its product topology and intersected with $\Omega$, which is the closure relative to $\Omega$.
-- source:
--   Berker, Conitzer, Hartman, Liu, Oesterheld, How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Eq. (12), p.30

import Mathlib
import Definitions.Def_ManipPotential_Omega

namespace ManipPotential

/-- `A_j = cl_Ω {(x, y) ∈ Ω ∩ ℚ^{m!} : g(x, y) = c_j}` (Berker–Conitzer–Hartman–Liu–Oesterheld, *How Many Votes Is a Lie Worth? Measuring Strategyproofness through Resource Augmentation*, arXiv:2602.22838 (version of November 3, 2026, sha256 5a383ac5…), Eq. (12), p.30).

**Formalization Note** Rational profiles enter through the cast `ℚ → ℝ`; the closure is taken in
`ℝ^{L(C)}` (product topology) and intersected with `Ω`, which is the closure relative to `Ω`. -/
def winnerClosure {m : ℕ} (g : (Ranking m → ℚ) → Fin m) (j : Fin m) : Set (Ranking m → ℝ) :=
  Omega m ∩ closure {P | P ∈ Omega m ∧ ∃ q : Ranking m → ℚ, (fun r => (q r : ℝ)) = P ∧ g q = j}

end ManipPotential


