-- Prove2me | Definitions.Def_HGASUndecidable_Main_SphereCodes
-- name    : HGASUndecidable_Main_SphereCodes
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T20:18:11.842823+00:00
-- url     : https://prove2.me/theorems/2fee26d6-2baa-4ae5-b9de-ed6453265dc4
-- title:
--   Products of spheres, tangency, and computable input serialization
-- statement:
--   A finite list of positive block dimensions specifies the product of unit spheres in a flattened Euclidean space. Tangency requires the inner product of each state block with the corresponding vector-field block to vanish at every point of that product, with no restriction off the product. Rational polynomial supports are serialized as exponent lists and coefficients; encodePolys uses the same RawFieldCode format as HGAS. The input for Theorem 10.1 contains the dimension list, D, vector-field coefficient data and reward polynomial. A total computable map on these natural-number codes must return an HGAS-format field of the asserted dimension and declared degree.
-- source:
--   Shevchenko, Liu, Liu (2026), arXiv:2610.12434 (SHA-256 72e185f4750fe9bb72a2f146b2802fa13a97dcdd4f66e0e762b703dc7ddd77a8), §10.1, printed pp. 67–69 (PDF 69–71)

import Definitions.Def_HGASUndecidable_Main_Compactification

noncomputable section
open scoped BigOperators

namespace HGASUndecidable.Main

def polynomialTerms {n : ℕ} (p : QPoly n) : List (List ℕ × ℚ) :=
  p.support.toList.map (fun m => (List.ofFn (fun i : Fin n => m i), p.coeff m))

def encodePolys {n : ℕ} (d : ℕ) (p : Fin n → QPoly n) : ℕ :=
  Encodable.encode ((n,d,(List.ofFn (fun i : Fin n =>
    (polynomialTerms (p i)).map (fun t => (i.val,t)))).flatten) : RawFieldCode)

def blockOffset {k : ℕ} (dims : Fin k → ℕ) (i : Fin k) : ℕ :=
  ∑ j ∈ Finset.univ.filter (fun j => j.val < i.val), dims j

def sphereProduct {k : ℕ} (dims : Fin k → ℕ) : Set (State (∑ i, dims i)) :=
  {x | ∀ i, (∑ j : Fin (dims i), coordinate x (blockOffset dims i+j.val)^2) = 1}

def tangentProduct {k : ℕ} (dims : Fin k → ℕ)
    (X : Fin (∑ i, dims i) → QPoly (∑ i, dims i)) : Prop :=
  ∀ x ∈ sphereProduct dims, ∀ i,
    (∑ j : Fin (dims i), coordinate x (blockOffset dims i+j.val) *
      coordinate (evalQField X x) (blockOffset dims i+j.val)) = 0

def sphereInputCode {k : ℕ} (dims : Fin k → ℕ) (D : ℕ)
    (X : Fin (∑ i, dims i) → QPoly (∑ i, dims i)) (a : QPoly (∑ i, dims i)) : ℕ :=
  Encodable.encode (List.ofFn dims, D, encodePolys 0 X, polynomialTerms a)

end HGASUndecidable.Main


