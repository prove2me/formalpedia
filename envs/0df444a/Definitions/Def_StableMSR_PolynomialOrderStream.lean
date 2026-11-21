-- Prove2me | Definitions.Def_StableMSR_PolynomialOrderStream
-- name    : StableMSR_PolynomialOrderStream
-- status  : Definition
-- author  : @lreyzin
-- created : 2026-11-20T18:00:12.111172+00:00
-- url     : https://prove2.me/theorems/c92c68cb-f4de-4a28-b721-a3d3006dd32a
-- title:
--   Explicit serialized polynomial hash orders
-- statement:
--   Choose the first prime above the quadratic threshold, enumerate fixed-length coefficient vectors by base-q digits, rank hash keys with deterministic ties, and serialize the resulting multiset of permutations in the public RAM output format.
-- source:
--   Shyam Ravichandran and Lev Reyzin, Exact Sum-of-Radii Clustering under Any Constant Stability, arXiv:2611.03547, Appendix B, Theorem B.2. Charged deterministic RAM implementation.

import Definitions.Def_StableMSR_Recovery_Supplement_RandomExecution
import Definitions.Def_StableMSR_BoundedSumRAM
import Mathlib.NumberTheory.Bertrand
set_option autoImplicit false
namespace StableMSR.Recovery.Supplement.OrderStream
open Compiler.BoundedSum
def lower (m : ℕ) := 8193+4*m^2
def fieldSize (m : ℕ) :=
  ∑ j ∈ Finset.range (2*lower m+1),
    if Nat.Prime j ∧ lower m≤j ∧ (∀k<j,lower m≤k → ¬Nat.Prime k) then j else 0
def degreeCount := 8193
def count (m : ℕ) := (fieldSize m)^degreeCount
def hash (q l c x : ℕ) :=
  (∑ i ∈ Finset.range l, (c/q^i%q)*x^i)%q
def score (m c x : ℕ) := hash (fieldSize m) degreeCount c x*m+x
def rank (m c x : ℕ) := ((Finset.range m).filter (fun y=>score m c y<score m c x)).card
def atRank (m c j : ℕ) :=
  ∑ x ∈ Finset.range m, if rank m c x=j then x else 0
def row (m c : ℕ) : List ℤ := (List.range m).map (fun j=>(atRank m c j:ℤ))
def family (m : ℕ) := (List.range (count m)).map (row m)
def span (m : ℕ) := 1+count m*(m+1)
def word (m i : ℕ) := if i=0 then count m else
  let r := (i-1)%(m+1)
  if r=0 then m else atRank m ((i-1)/(m+1)) (r-1)
end StableMSR.Recovery.Supplement.OrderStream


