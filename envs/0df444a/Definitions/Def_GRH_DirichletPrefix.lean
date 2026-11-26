-- Prove2me | Definitions.Def_GRH_DirichletPrefix
-- name    : GRH_DirichletPrefix
-- status  : Definition
-- author  : @scuba8684
-- created : 2026-11-26T16:15:24.473859+00:00
-- url     : https://prove2.me/theorems/25a8c374-9484-4771-a047-019e21e423fa
-- title:
--   Arithmetic tests for Dirichlet rectangles using weighted character prefixes
-- statement:
--   For a nonprincipal character at witness modulus $Q$, let $B(n)$ count the maximum distance of its prefix from one using the unit residues in the prefix and its complement. At residue zero set $B(n)=1$. At other residues use the smaller of the number of units after the first in the prefix and one plus the number of units left in the period. The error is the sum of $B(n)(n^{-x}-(n+1)^{-x})$ through $M$, plus $R(M+1)^{-x}$, where $R$ bounds each $B(n)$. A rectangle at a divisor of $Q$ passes if a positive $x$ at most its left edge and a real $K$ bounding $|s|/x$ make $K$ times this error less than one. The integer mass and power-bracket definitions give the rational version of this check.
-- source:
--   Developed for the centered Möbius theorem at https://prove2.me/theorems/5000f709-1ce6-4ce6-a1ad-637c5b963006 and its open primitive grid condition at https://prove2.me/theorems/59bf325f-868f-5552-94bb-1b5f67435396. Uses the centered Abel estimate at https://prove2.me/theorems/3b5a3db7-3b41-46b5-a41d-4a78754ad8d2 and the power variation estimate at https://prove2.me/theorems/189b3afb-17f1-43b4-9047-0e36a164d965.

import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.Data.Nat.Totient

namespace GRH.DirichletPrefix

/-- Number of unit residues among the integers from one through r. -/
def count (Q r : ℕ) : ℕ :=
  ∑ k ∈ Finset.range r, if (k+1).Coprime Q then 1 else 0

/-- Upper bound for the distance of a nonprincipal character prefix from one. -/
def weightAt (Q r : ℕ) : ℕ :=
  if r=0 then 1 else min (count Q r - 1) (Q.totient + 1 - count Q r)

def weight (Q n : ℕ) : ℕ := weightAt Q (n % Q)

/-- Abel variation of the individually bounded prefixes, with a uniform final tail. -/
noncomputable def error (Q M R : ℕ) (a : ℝ) : ℝ :=
  (∑ k ∈ Finset.range M, (weight Q (k+1):ℝ) *
    (((k:ℝ)+1)^(-a)-((k:ℝ)+2)^(-a))) + (R:ℝ)*((M:ℝ)+1)^(-a)

/-- A sufficient arithmetic test for a closed rectangle at a divisor of Q. -/
def Covers (d : ℕ) (a b H : ℝ) : Prop :=
  ∃ Q M R : ℕ, ∃ x K : ℝ, 2 < Q ∧ d ∣ Q ∧ 0 < x ∧ x ≤ a ∧
    0 ≤ K ∧ b^2+H^2 ≤ (K*x)^2 ∧ (∀ r : Fin Q, weightAt Q r.val ≤ R) ∧
    K * error Q M R x < 1

/-- Integer upper bound for the scaled Abel error from upper rounding of the powers. -/
def mass (Q M R : ℕ) (u : ℕ → ℕ) : ℕ :=
  (∑ k ∈ Finset.range M, weight Q (k+1)*(u (k+1)-(u (k+2)-1))) + R*u (M+1)

/-- Each positive entry u(n) brackets D times n to the power -p/t to one integer. -/
def Table (M D p t : ℕ) (u : ℕ → ℕ) : Prop :=
  ∀ k : Fin (M+1), let n := k.val+1
    0 < u n ∧ (u n-1)^t*n^p ≤ D^t ∧ D^t ≤ (u n)^t*n^p ∧ u (n+1) ≤ u n

end GRH.DirichletPrefix


