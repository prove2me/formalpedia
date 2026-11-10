-- Prove2me | Definitions.Def_AdaptiveRLDC_LowerBound_SetOperations
-- name    : AdaptiveRLDC_LowerBound_SetOperations
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T14:56:05.930495+00:00
-- url     : https://prove2.me/theorems/8cbde203-c4ce-4a3b-a3c9-ead1c5f7390c
-- title:
--   Weighted set restrictions, conditioning, puncturing and spreadness
-- statement:
--   Let $\mu$ assign nonnegative weights of total mass at most one to subsets of a finite universe. A restriction keeps the original weights in a family $D$; conditioning divides those weights by $\mu(D)>0$. Puncturing is the pushforward $S\mapsto S\setminus H$, with weights from all preimages added. It is represented on the whole power set with zero mass outside subsets disjoint from $H$.
--
--   For $m>0$ and $r>1$, spreadness means
--   $$\mu(\{S:T\subseteq S\})\le m/r^{|T|}\quad(T\ne\varnothing).$$
--   Support, total mass, family mass and a bound on supported set sizes are defined separately. The empty set is allowed to have positive mass. These distinctions are necessary for weighted extraction; restriction and conditioning are different operations.
-- source:
--   Guy Goldberg, Tom Gur, Sidhant Saraogi, Lower Bounds for Adaptive Relaxed Locally Decodable Codes via the Capped Horvitz–Thompson Estimator, STOC 2027 submission #1071 (October 2026), §3.1; Definitions 3.8–3.9, printed p.13, PDF p.14; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1071.pdf; sha256 fc1b12e269801cef0033faea9f18d9873b62d5b18dbd21242a4daefc43048a5b. Title-page date November 3, 2026; submission status does not assert acceptance. Exact per-concept locations: §3.1 printed p.13/PDF p.14; Definitions 3.8–3.9 printed p.14/PDF p.15.

import Mathlib
import Definitions.Def_AdaptiveRLDC_LowerBound_FiniteWeights

open scoped BigOperators
noncomputable section

namespace AdaptiveRLDC.LowerBound

open Classical

/-- Total mass, and the unnormalised restriction and normalised conditioning of §3.1. -/
def totalMass {n : ℕ} (μ : Sets n → ℝ) : ℝ := ∑ S, μ S

def restrictWeights {n : ℕ} (μ : Sets n → ℝ) (D : Finset (Sets n)) : Sets n → ℝ :=
  fun S => if S ∈ D then μ S else 0

def familyMass {n : ℕ} (μ : Sets n → ℝ) (D : Finset (Sets n)) : ℝ := ∑ S ∈ D, μ S

def conditionWeights {n : ℕ} (μ : Sets n → ℝ) (D : Finset (Sets n)) : Sets n → ℝ :=
  fun S => restrictWeights μ D S / familyMass μ D

/-- Definition 3.9: pushforward by set difference, zero-extended to the whole power set. -/
def puncture {n : ℕ} (μ : Sets n → ℝ) (H : Sets n) : Sets n → ℝ :=
  fun A => ∑ S, if S \ H = A then μ S else 0

/-- Support of positive weights, and support on sets of cardinality at most q. -/
def weightSupport {n : ℕ} (μ : Sets n → ℝ) : Finset (Sets n) :=
  Finset.univ.filter (fun S => 0 < μ S)

def SupportedAtMost {n : ℕ} (μ : Sets n → ℝ) (q : ℕ) : Prop :=
  ∀ S, 0 < μ S → S.card ≤ q

/-- Definition 3.8: the multiplier m is free; the empty star is excluded. -/
def IsSpread {n : ℕ} (μ : Sets n → ℝ) (m r : ℝ) : Prop :=
  IsSubdistribution μ ∧ 0 < m ∧ 1 < r ∧
    ∀ T : Sets n, T.Nonempty → eventMass μ (fun S => T ⊆ S) ≤ m / r ^ T.card

end AdaptiveRLDC.LowerBound


