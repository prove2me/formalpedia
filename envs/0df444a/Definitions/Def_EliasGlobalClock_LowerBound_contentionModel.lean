-- Prove2me | Definitions.Def_EliasGlobalClock_LowerBound_contentionModel
-- name    : EliasGlobalClock_LowerBound_contentionModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:04:40.56378+00:00
-- url     : https://prove2.me/theorems/038425ff-68fa-400d-b588-6d8fedc6955e
-- title:
--   Conditional contention, batch schedules and scale weights
-- statement:
--   For wake-up time $w$ and slot $t$, let $p(w,t\mid y)$ be the probability of a masked attempt, computed from the protocol's conditional stream kernel. It is zero for $w<0$ and $t\le w$. Define
--
--   $$s_{t\mid y}(j)=\sum_{k=1}^j p(t-k,t\mid y),\qquad
--   K(\sigma)=\begin{cases}\min\{\sqrt\sigma,1/\sqrt\sigma\},&\sigma>0,\\0,&\sigma=0.\end{cases}$$
--
--   A batch schedule wakes exactly $m$ players at each of $t_0,\ldots,t_0+\ell-1$. Its diagonal weight is $\sum_{j=1}^{\ell}K(m s_{t_0+j\mid y}(j))$, and the column weight at $t$ is $\sum_{j=1}^{\ell}K(m s_{t\mid y}(j))$. These are different quantities and include both endpoints of the source sums.
--
--   For positive scale index $i$, set $n_i=2^i$ and $m_i=2\lceil n_i^{\eta/2}\rceil$. The normalized packing summand for windows $\ell_i$ and profile $s$ is $\ell_i^{-1}\sum_{j=1}^{\ell_i}K(m_i s(j))$. The explicit geometric bound recorded from the proof is
--
--   $$C_\eta=\frac{2\sqrt2}{1-2^{-\eta/4}},\qquad 0<\eta<1.$$
--
--   All definitions have mathematical bodies. They assert no failure, averaging or packing inequality. The piecewise weight is extended by zero to negative inputs, which never occur for a protocol's contention.
-- source:
--   Kuowen Chen, Shengquan Du, Tsvi Kopelowitz, Seth Pettie, Ben Plosk, STOC 2027 submission #1311 (October 2026), printed pp.9, 11–12, PDF pp.10, 12–13, §4.1–4.2; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1311.pdf

import Definitions.Def_EliasGlobalClock_LowerBound_latencyModel

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace EliasGlobalClock.LowerBound

/-- Negative wake-ups and slots at/before wake-up contribute zero. Probabilities
are obtained from the protocol's conditional stream kernel. -/
noncomputable def transmissionProbability {Ω : Type*} [MeasurableSpace Ω]
    (P : StreamProtocol Ω) (w : ℤ) (t : ℕ) (y : Ω) : ℝ :=
  if 0 ≤ w ∧ w < (t : ℤ) then
    (P.attempts w.toNat y {a | a t = true}).toReal else 0

noncomputable def contention {Ω : Type*} [MeasurableSpace Ω]
    (P : StreamProtocol Ω) (t : ℕ) (y : Ω) (j : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 j, transmissionProbability P ((t : ℤ) - k) t y

/-- Source K; the zero case is explicit. Only nonnegative contention is used. -/
noncomputable def contentionWeight (σ : ℝ) : ℝ :=
  if 0 < σ then min (Real.sqrt σ) (1 / Real.sqrt σ) else 0

/-- Exactly m players in each of ℓ successive batches. The m=0 value is unused. -/
def batchWake (t₀ ℓ m : ℕ) : Fin (ℓ * m) → ℕ :=
  fun u => t₀ + u.val / m

noncomputable def diagonalWeight {Ω : Type*} [MeasurableSpace Ω]
    (P : StreamProtocol Ω) (t₀ ℓ m : ℕ) (y : Ω) : ℝ :=
  ∑ j ∈ Finset.Icc 1 ℓ, contentionWeight ((m : ℝ) * contention P (t₀ + j) y j)

noncomputable def columnWeight {Ω : Type*} [MeasurableSpace Ω]
    (P : StreamProtocol Ω) (t ℓ m : ℕ) (y : Ω) : ℝ :=
  ∑ j ∈ Finset.Icc 1 ℓ, contentionWeight ((m : ℝ) * contention P t y j)

/-- n_i=2^i and m_i=2 ceil(n_i^(η/2)), with i indexed here by positive integers. -/
noncomputable def scaleMultiplicity (η : ℝ) (i : ℕ+) : ℕ :=
  2 * Nat.ceil (((2 ^ (i : ℕ) : ℕ) : ℝ) ^ (η / 2))

noncomputable def packingTerm (η : ℝ) (s : ℕ → ℝ) (ℓ : ℕ+ → ℕ)
    (i : ℕ+) : ℝ :=
  (∑ j ∈ Finset.Icc 1 (ℓ i), contentionWeight ((scaleMultiplicity η i : ℝ) * s j)) /
    (ℓ i : ℝ)

/-- The two geometric tails and the rounding factor in the proof of Lemma 4.4. -/
noncomputable def packingConstant (η : ℝ) : ℝ :=
  2 * Real.sqrt 2 / (1 - (2 : ℝ) ^ (-η / 4))

end EliasGlobalClock.LowerBound


