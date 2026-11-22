-- Prove2me | Definitions.Def_Erdos462Balanced
-- name    : Erdos462Balanced
-- status  : Definition
-- author  : @adamhenr
-- created : 2026-11-21T09:05:49.447936+00:00
-- url     : https://prove2.me/theorems/a2b40072-76fb-4286-8068-64a98c55b110
-- title:
--   Balanced products in the strict interval
-- statement:
--   Count distinct integers $n=pq$, where $p$ and $q$ are primes and $\sqrt{x}/2<q<\sqrt{x}<p<3\sqrt{x}$. The set used in the explicit theorem imposes both $x<n$ and $n<x+H_{384}(x)$. The assertion called ExplicitBounds puts simultaneous lower bounds on the cardinality and on the total weight of this set for real $x\ge 9.6\cdot10^{37}$.
-- source:
--   Adam Henriksson, Balanced semiprimes in short intervals under the Riemann hypothesis. Theorem 1.1 and Section 2.

import Definitions.Def_Erdos462Window

namespace Erdos462RH
open scoped BigOperators
def Balanced (x : ℝ) (n : ℕ) : Prop :=
  x < (n : ℝ) ∧ ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ n = p*q ∧
    Real.sqrt x / 2 < q ∧ (q : ℝ) < Real.sqrt x ∧ Real.sqrt x < p ∧
    (p : ℝ) < 3 * Real.sqrt x
noncomputable def products (x : ℝ) : Finset ℕ := by
  classical exact (window 384 x).filter (Balanced x)
noncomputable def interiorProducts (x : ℝ) : Finset ℕ := by
  classical exact (products x).filter (fun n => (n:ℝ) < x + width 384 x)
def ExplicitBounds : Prop := ∀ x : ℝ, 96*10^36 ≤ x →
  (14/3)*Real.sqrt x ≤ ((interiorProducts x).card:ℝ) ∧
  14/9 ≤ ∑ n ∈ interiorProducts x, weight n
end Erdos462RH


