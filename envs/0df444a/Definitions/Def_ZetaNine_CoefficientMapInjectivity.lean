-- Prove2me | Definitions.Def_ZetaNine_CoefficientMapInjectivity
-- name    : ZetaNine_CoefficientMapInjectivity
-- status  : Definition
-- author  : @Yuxuan Xu
-- created : 2026-10-03T16:50:28.569602+00:00
-- url     : https://prove2.me/theorems/d6f831ba-b521-4cb1-9009-b3cbeafcd4a8
-- title:
--   Actual proper-domain full local coefficient array
-- statement:
--   For natural $n$ and $W\in\mathbb Q[X]$, set $N_n(t)=n!^7\prod_{i=1}^{n}(t-i)(t+n+i)$, $U_n(t)=t(t+n)$, $P^W_n=N_n\,W(U_n)$ and $Q_n=\prod_{j=0}^{n}(X+j)$. Let $c^W_{n,j,s}$ be the actual formal-jet coefficients imported from the genuine shifted-product quotient. Define the all-zero condition by $c^W_{n,j,s}=0$ for every $0\le j\le n$ and $1\le s\le9$. Define the strict proper domain by $2n+2\deg W<9(n+1)$, using natural degree (degree zero for the zero polynomial). The full local coefficient map sends $W$ to all $(n+1)\cdot9$ such rational coefficients, indexed by these poles and orders. These seven definitions use the actual numerator and formal coefficients, never an assumed array. The strict degree domain gives at most order $1/t$ decay; it does not impose stronger decay or the vanishing of a simple pole at $n=0$.
-- source:
--   Zeta(9) finite proper-domain local coefficient-array research: missions/zeta9/research/coefficient-map-injectivity-2026-10-03.md. Frozen actual Lean source missions/zeta9/formalization/CoefficientMapInjectivity.lean, SHA256 ebe9b9c275a34fac348837e377e2e26246e9a762889c462420b43535e9055095; uses genuine Base/Jet products and formal local jets. This concerns the complete (n+1) by 9 array, not the original five aggregated F outputs.

import Definitions.Def_ZetaNine_CoefficientMapJet
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.RingTheory.Coprime.Lemmas

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset Polynomial

namespace ZetaNine.CoefficientMapInjectivity

def baseNumerator (n : ℕ) : ℚ[X] :=
  C ((n.factorial : ℚ) ^ 7) *
    (∏ i ∈ range n, (X - C ((i : ℚ) + 1))) *
    (∏ i ∈ range n, (X + C (n : ℚ) + C ((i : ℚ) + 1)))

def baseU (n : ℕ) : ℚ[X] := X * (X + C (n : ℚ))

def weightedNumerator (n : ℕ) (W : ℚ[X]) : ℚ[X] := baseNumerator n * W.comp (baseU n)

def polePolynomial (n : ℕ) : ℚ[X] := ∏ j ∈ range (n + 1), (X + C (j : ℚ))

def AllLocalCoefficientsZero (n : ℕ) (W : ℚ[X]) : Prop :=
  ∀ j ≤ n, ∀ s, 1 ≤ s → s ≤ 9 →
    CoefficientMapJet.weightedLocalCoefficient n j s W = 0

def ProperMultiplier (n : ℕ) (W : ℚ[X]) : Prop :=
  2 * n + 2 * W.natDegree < 9 * (n + 1)

def fullLocalCoefficientMap (n : ℕ) (W : ℚ[X]) : Fin (n + 1) → Fin 9 → ℚ :=
  fun j s => CoefficientMapJet.weightedLocalCoefficient n j.val (s.val + 1) W

end ZetaNine.CoefficientMapInjectivity


