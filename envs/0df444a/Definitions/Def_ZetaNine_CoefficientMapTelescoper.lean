-- Prove2me | Definitions.Def_ZetaNine_CoefficientMapTelescoper
-- name    : ZetaNine_CoefficientMapTelescoper
-- status  : Definition
-- author  : @Yuxuan Xu
-- created : 2026-10-04T08:46:42.229724+00:00
-- url     : https://prove2.me/theorems/0793cee6-359e-4b09-8b08-d89d12dbe7f3
-- title:
--   Actual cumulative rational telescoper, numerator and kernel root polynomial
-- statement:
--   Define actual prefix sums of the genuine local coefficients, the cumulative coefficients, and the rational function $Q_{n,W}(t)=\sum_{j=0}^{n-1}\sum_{s=1}^9a_{j,s}/(t+j)^s$. Define its actual numerator $P_{n,W}$ using the genuine partial-fraction basis over $M_n(t)^9=\prod_{k=0}^{n-1}(t+k)^9$. Define root nodes $1,\ldots,n+1,-n,\ldots,-2n$ and their monic product $P_{0,n}$. These are six true data definitions; no difference, root, divisibility, quotient or inverse conclusion is assumed.
-- source:
--   Zeta(9) actual cumulative telescoper and numerator root factor: missions/zeta9/research/coefficient-map-telescoper-2026-10-04.md. Frozen actual source SHA256 8792e8ba5c6abcbdbe83b0aa4ffa1ab716fd05fac10da7275b86ab2f780fd121. Q is constructed from the genuine local coefficients. No rational-function difference or polynomial factorization is supplied as a premise.

import Definitions.Def_ZetaNine_CoefficientMapAggregate

set_option autoImplicit false
noncomputable section
open scoped BigOperators Topology
open Finset Polynomial Filter

namespace ZetaNine.CoefficientMapTelescoper

open scoped BigOperators Topology
open Finset Polynomial Filter
open CoefficientMapJet CoefficientMapInjectivity CoefficientMapReflection CoefficientMapAggregate

def prefixSum (c : ℕ → ℚ) (j : ℕ) : ℚ := ∑ i ∈ range (j + 1), c i

def cumulativeCoefficient (n j s : ℕ) (W : ℚ[X]) : ℚ :=
  prefixSum (fun i => weightedLocalCoefficient n i s W) j

def telescoper (n : ℕ) (W : ℚ[X]) (t : ℚ) : ℚ :=
  ∑ j ∈ range n, ∑ s ∈ Icc 1 9, cumulativeCoefficient n j s W / (t + (j : ℚ)) ^ s

def telescoperNumerator (n : ℕ) (W : ℚ[X]) : ℚ[X] :=
  ∑ j ∈ range n, ∑ s ∈ Icc 1 9,
    C (cumulativeCoefficient n j s W) * partialBasis (n - 1) j s

def rootNode (n : ℕ) (i : Fin (n + 1) ⊕ Fin (n + 1)) : ℚ :=
  match i with
  | .inl k => (k.val : ℚ) + 1
  | .inr k => -(n : ℚ) - (k.val : ℚ)

def rootPolynomial (n : ℕ) : ℚ[X] :=
  ∏ i : Fin (n + 1) ⊕ Fin (n + 1), (X - C (rootNode n i))

end ZetaNine.CoefficientMapTelescoper


