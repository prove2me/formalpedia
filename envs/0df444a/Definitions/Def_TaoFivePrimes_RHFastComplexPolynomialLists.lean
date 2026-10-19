-- Prove2me | Definitions.Def_TaoFivePrimes_RHFastComplexPolynomialLists
-- name    : TaoFivePrimes_RHFastComplexPolynomialLists
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-16T10:17:52.695173+00:00
-- url     : https://prove2.me/theorems/5a343748-e0a1-45a4-9d86-8be0f89985dd
-- title:
--   Complex polynomial-list semantics
-- statement:
--   Exact complex list coefficient operations and their interpretation as a polynomial. Their correspondence to polynomial ring operations and rounded integer balls requires separate ordinary proofs.
-- source:
--   Coefficient arithmetic for the center Gaussian/Hermite method, Platt DOI10.1090/mcom/3198. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Polynomial.BigOperators
open scoped BigOperators
namespace RHFastComplexPoly
noncomputable def entry (xs:List ℂ) (i:Nat) : ℂ := (xs[i]?).getD 0
noncomputable def addList (xs ys:List ℂ) : List ℂ :=
 (List.range (max xs.length ys.length)).map (fun i=>entry xs i+entry ys i)
noncomputable def mulCoeff (xs ys:List ℂ) (k:Nat) : ℂ :=
 ∑i∈Finset.range (k+1),if i<xs.length ∧ i≤k ∧ k-i<ys.length then entry xs i*entry ys (k-i) else 0
noncomputable def mulList (xs ys:List ℂ) : List ℂ :=
 (List.range (xs.length+ys.length-1)).map (mulCoeff xs ys)
noncomputable def divideList (xs:List ℂ) (n:Nat) : List ℂ :=xs.map (fun a=>a/(n:ℂ))
noncomputable def polynomial (xs:List ℂ) : Polynomial ℂ :=
 ∑i∈Finset.range xs.length,Polynomial.C (entry xs i)*Polynomial.X^i
end RHFastComplexPoly
noncomputable def TaoFivePrimes_RHFastComplexPolynomialLists : Nat := 28


