-- Prove2me | Definitions.Def_Freiman_rootConvergentData
-- name    : Freiman_rootConvergentData
-- status  : Definition
-- author  : @tp
-- created : 2026-09-09T10:45:57.88588+00:00
-- url     : https://prove2.me/theorems/4b8c38f5-d340-4ad8-a112-b463156f2adf
-- title:
--   The convergent matrix data used to reduce an irrational pair of roots
-- statement:
--   This is precisely the convergent data used in the proof of found:reduce-roots, with the first few indices discarded to ensure positive denominators. It records the determinant, complete quotient, vanishing signed errors, and diverging successive denominator increments. Existence of this data remains an open theorem. The secondRootCoordinate is the inverse fractional-linear image of the other root.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, foundations.tex, §§1.1–1.3

import Definitions.Def_Freiman_reducedForms

namespace Freiman

structure RootConvergentData (r : ℝ) where
  p : ℕ → ℤ
  q : ℕ → ℕ
  complete : ℕ → ℝ
  q_pos : ∀ n, 0 < q n
  det : ∀ n, formUnimodular (p (n+1)) (p n) (q (n+1)) (q n)
  complete_gt : ∀ n, 1 < complete n
  complete_irr : ∀ n, Irrational (complete n)
  root_identity : ∀ n, r = ((p (n+1):ℝ)*complete n+(p n:ℝ))/
    ((q (n+1):ℝ)*complete n+(q n:ℝ))
  error_zero : ∀ ε : ℝ, 0<ε → ∃ N : ℕ, ∀ n : ℕ, N≤n → |(p n:ℝ)-r*(q n:ℝ)|<ε
  denominator_difference_escape : ∀ R : ℝ, ∃ N : ℕ, ∀ n : ℕ, N≤n → R≤(q (n+1):ℝ)-(q n:ℝ)
noncomputable def secondRootCoordinate {r : ℝ} (D : RootConvergentData r) (s : ℝ) (n : ℕ) : ℝ :=
  ((D.p n:ℝ)-s*(D.q n:ℝ))/(s*(D.q (n+1):ℝ)-(D.p (n+1):ℝ))

end Freiman


