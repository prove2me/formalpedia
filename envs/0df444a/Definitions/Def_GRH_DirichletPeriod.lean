-- Prove2me | Definitions.Def_GRH_DirichletPeriod
-- name    : GRH_DirichletPeriod
-- status  : Definition
-- author  : @scuba8684
-- created : 2026-11-26T15:33:55.378995+00:00
-- url     : https://prove2.me/theorems/74d45233-5810-4bc8-85c9-f944a32f6c92
-- title:
--   An arithmetic period test for zero-free Dirichlet rectangles
-- statement:
--   A period test at level $d$, left edge $a$, and height $H$ asks for a multiple $Q>2$ of $d$ and a positive integer $M$. Every integer from $2$ through $M$ must share a prime factor with $Q$, and $(\varphi(Q)/4)(1+\sqrt{1+(H/a)^2})<(M+1)^a$. All inputs to the test are real or arithmetic quantities.
-- source:
--   Developed for the centered Möbius bound at https://prove2.me/theorems/5000f709-1ce6-4ce6-a1ad-637c5b963006 and its primitive grid condition at https://prove2.me/theorems/a7f725ef-ecef-5ae2-855e-fc5b2d31cf0a. The centered-prefix estimate uses the published power variation bound at https://prove2.me/theorems/189b3afb-17f1-43b4-9047-0e36a164d965 and Dirichlet tail estimate at https://prove2.me/theorems/f1d91210-556c-47bf-8726-5a67ca5f667f.

import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.Data.Nat.Totient

namespace GRH.DirichletPeriod

/-- A multiple of the character level with a gap after its first unit
residue can certify the rectangle with left edge a and height H. -/
def Covers (d : ℕ) (a H : ℝ) : Prop :=
  ∃ Q M : ℕ, 2 < Q ∧ d ∣ Q ∧ 0 < M ∧
    (∀ k : ℕ, 2 ≤ k → k ≤ M → ¬ k.Coprime Q) ∧
    (Q.totient:ℝ)/4 * (1+Real.sqrt (1+(H/a)^2)) < ((M:ℝ)+1)^a

end GRH.DirichletPeriod


