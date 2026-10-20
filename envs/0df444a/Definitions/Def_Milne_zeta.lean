-- Prove2me | Definitions.Def_Milne_zeta
-- name    : Milne_zeta
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-20T02:09:24.829985+00:00
-- url     : https://prove2.me/theorems/6361dcfc-11ba-4810-a927-ee1a8ebd221c
-- title:
--   Zeta functions of varieties over finite fields as Taylor coefficient sequences
-- statement:
--   The zeta function of a variety over a finite field, in the form fixed by the relation log Z(X, t) = Σ N_m t^m / m of Section 7 of the source, where N_m is the number of points of the variety over the field with p^m elements. The zeta function is rendered through its Taylor coefficients: c₀ = 1 and (n+1) c_{n+1} = Σ_{m=1}^{n+1} N_m c_{n+1−m}, the standard recurrence extracted from the logarithmic derivative. The course-of-values recursion is realized through a prefix function zetaSeq, and zetaCoeff returns the k-th Taylor coefficient of the zeta function attached to a point-count sequence.
-- source:
--   J. S. Milne, Motives — Grothendieck's Dream, v2.04, April 2012, Section 7 (pp. 10-11).

import Mathlib

/-!
# Motives — Grothendieck's dream: zeta functions

The zeta function of a variety over a finite field is determined by the
numbers of points over the extension fields through the relation
log Z(X, t) = Σ N_m t^m / m of section 7 of the paper. The Taylor
coefficients are defined by the standard recurrence extracted from the
logarithmic derivative: c₀ = 1 and
(n+1) c_{n+1} = Σ_{m=1}^{n+1} N_m c_{n+1−m}. The course-of-values
recursion is realized through a prefix function.
-/

namespace Milne

/-- The prefix function of the coefficient sequence of the zeta function
attached to a point count sequence N — N m is the number of points of
the variety over the field with p^m elements. zetaSeq N n k is the
coefficient of t^k for k ≤ n; the coefficient of t⁰ is 1, and the
recurrence (n+1) c_{n+1} = Σ_{m=1}^{n+1} N_m c_{n+1−m} is the standard
relation between the logarithmic derivative of Z and the counts. -/
def zetaSeq (N : ℕ → ℚ) : ℕ → (ℕ → ℚ)
  | 0 => fun _ => 1
  | n + 1 => fun k => if k ≤ n
      then zetaSeq N n k
      else (∑ j ∈ Finset.range (n + 1), N (n + 1 - j) * zetaSeq N n j) / (n + 1 : ℚ)

/-- The k-th Taylor coefficient of the zeta function attached to the
point count sequence N. -/
def zetaCoeff (N : ℕ → ℚ) (k : ℕ) : ℚ := zetaSeq N (k + 1) k

end Milne


