-- Prove2me | Definitions.Def_OnlineMaxWeightMatch_Approx_Supplement_EncodedRideHail
-- name    : OnlineMaxWeightMatch_Approx_Supplement_EncodedRideHail
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T08:23:07.620397+00:00
-- url     : https://prove2.me/theorems/bb7ad4e4-8bcd-4045-8bcf-29657b00293e
-- title:
--   Finitely presented RideHail instances, their binary size, and the polynomially bounded class (Theorem 1.1)
-- statement:
--   Theorem 1.1 is a statement about an algorithmic problem, so its inputs are finite objects. A **presented RideHail instance** $J$ consists of numbers $m$ (bins) and $n$ (balls), rational weights $w_{i,t}\ge0$, and rational arrival probabilities $p_t\in[0,1]$. It describes the RideHail instance with these data, and $OPT_{on}(J)$ is the expected profit of the optimal online algorithm on it.
--
--   The **size** of $J$ is the length of its binary encoding: $m$, $n$, the weight table row by row, and the probabilities, each number written in binary (a rational as numerator and denominator).
--
--   For a polynomial $q$, the **polynomially bounded class** consists of the instances in which every arrival probability is positive and
--   $$w_{i,t}\le q(|J|)\quad\text{and}\quad 1/p_t\le q(|J|)\qquad\text{for all } i,t,$$
--   where $|J|$ is the size of $J$. This is the restricted class of the second sentence of Theorem 1.1.
--
--   **Formalization Note** $OPT_{on}(J)$ is the published `optOn` of the base mission: the supremum of the expected profits of all deterministic non-anticipating online policies.
-- source:
--   Papadimitriou, Pollner, Saberi & Wajc, Online Stochastic Max-Weight Bipartite Matching: Beyond Prophet Inequalities, arXiv:2102.10261v3, p. 1, §1 (RideHail problem) and Theorem 1.1

import Mathlib
import Definitions.Def_OnlineMaxWeightMatch_Approx_RideHail
import Definitions.Def_OptimalQueuingComplexity_Restless_encNat

namespace OnlineMaxWeightMatch.Approx.Supplement

open OnlineMaxWeightMatch.Approx OptimalQueuingComplexity.Restless

/-- A **finitely presented RideHail instance**, the input of the computational problem of
Theorem 1.1: `m` bins, `n` balls, rational weights `w i t ≥ 0` and rational arrival
probabilities `p t ∈ [0, 1]`. -/
structure RatRideHail where
  m : ℕ
  n : ℕ
  w : Fin m → Fin n → ℚ
  p : Fin n → ℚ
  w_nonneg : ∀ i t, 0 ≤ w i t
  p_nonneg : ∀ t, 0 ≤ p t
  p_le_one : ∀ t, p t ≤ 1

/-- The RideHail instance (bins `Fin m`, balls `Fin n`) that a presented instance describes. -/
def RatRideHail.toInstance (J : RatRideHail) : RideHailInstance (Fin J.m) J.n where
  w i t := (J.w i t : ℝ)
  p t := (J.p t : ℝ)
  w_nonneg i t := by exact_mod_cast J.w_nonneg i t
  p_nonneg t := by exact_mod_cast J.p_nonneg t
  p_le_one t := by exact_mod_cast J.p_le_one t

/-- Binary code of a presented instance: `m`, `n`, the weight table row by row (bin `i`, then
the weights `w i 0, …, w i (n-1)`), then the arrival probabilities; numbers in binary. -/
def encRideHail (J : RatRideHail) : List Bool :=
  encNat J.m ++ encNat J.n ++ encTable (fun row : Fin J.n → ℚ => encTable encRat row) J.w ++ encTable encRat J.p

/-- `OPT_on` of a presented instance: the published `optOn` of the instance it describes. -/
noncomputable def ratOptOn (J : RatRideHail) : ℝ :=
  optOn J.toInstance

/-- The instances of the second clause of Theorem 1.1 for the polynomial `q`: every arrival
probability is positive and every weight and every inverse arrival probability is at most
`q(|enc J|)`, the polynomial evaluated at the input length. -/
def RatRideHail.PolyBounded (q : Polynomial ℕ) (J : RatRideHail) : Prop :=
  ∀ t, 0 < J.p t ∧ (J.p t)⁻¹ ≤ ((q.eval (encRideHail J).length : ℕ) : ℚ) ∧
    ∀ i, J.w i t ≤ ((q.eval (encRideHail J).length : ℕ) : ℚ)

end OnlineMaxWeightMatch.Approx.Supplement


