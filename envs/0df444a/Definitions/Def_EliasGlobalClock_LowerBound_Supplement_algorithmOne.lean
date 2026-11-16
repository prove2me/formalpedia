-- Prove2me | Definitions.Def_EliasGlobalClock_LowerBound_Supplement_algorithmOne
-- name    : EliasGlobalClock_LowerBound_Supplement_algorithmOne
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T07:33:39.593307+00:00
-- url     : https://prove2.me/theorems/9cc659b2-1911-4cb3-8ee7-3b9aecf9c505
-- title:
--   Algorithm 1 (LeaderElection) as an anonymous GlobalClock stream protocol
-- statement:
--   Fix a code and its sequence $\mathrm{Int}(t)$. In Algorithm 1 every awake player $u$, woken at slot $t_u$, transmits in each slot $t>t_u$ independently with probability
--   $$2^{-\mathrm{Int}(t)},$$
--   and the protocol halts at the first slot in which exactly one player transmits.
--
--   This definition realizes Algorithm 1 in the published stream-protocol interface of the mission: the attempt stream of a player woken at $w$ is the product over slots $t$ of a Bernoulli law with success probability $2^{-\mathrm{Int}(t)}$ for $t>w$ (silent for $t\le w$), the shared random input is trivial, and the published first-singleton coupling stops the execution at the first success. The rule depends only on the code and the global clock, never on the population, the error profile or the wake-up pattern.
--
--   **Formalization Note** The shared input space is `Unit` with the Dirac measure; the stream law is `Measure.infinitePi` of Bernoulli measures on `Bool`.
-- source:
--   Kuowen Chen, Shengquan Du, Tsvi Kopelowitz, Seth Pettie, Ben Plosk, STOC 2027 submission #1311 (October 2026), The Necessity of Elias Codes in the Global Clock Model, printed p.7 / PDF p.8, §3, Algorithm 1 (LeaderElection(u, t_u)) and the latency definition; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1311.pdf

import Definitions.Def_EliasGlobalClock_LowerBound_latencyModel
import Definitions.Def_EliasGlobalClock_LowerBound_Supplement_codes

open MeasureTheory ProbabilityTheory

namespace EliasGlobalClock.LowerBound.Supplement

/-- Transmission probability `2^{−Int(t)}` of Algorithm 1 in slot `t`, as an element of
the unit interval. -/
noncomputable def attemptProbability (c : ℕ+ → List Bool) (t : ℕ) : unitInterval :=
  ⟨(2⁻¹ : ℝ) ^ decode c t, by positivity, pow_le_one₀ (by norm_num) (by norm_num)⟩

/-- Law of one player's attempt stream in Algorithm 1 (`LeaderElection(u, t_u)`, printed p.7):
independent fresh choices in different slots, transmitting (`true`) in slot `t > t_u` with
probability `2^{−Int(t)}`; slots `t ≤ t_u` are silent. -/
noncomputable def algorithmOneLaw (c : ℕ+ → List Bool) (w : ℕ) : Measure AttemptStream :=
  Measure.infinitePi (fun t : ℕ =>
    if w < t then bernoulliMeasure true false (attemptProbability c t)
    else Measure.dirac false)

instance (c : ℕ+ → List Bool) (w : ℕ) : IsProbabilityMeasure (algorithmOneLaw c w) := by
  have : ∀ t : ℕ, IsProbabilityMeasure (if w < t then
      bernoulliMeasure true false (attemptProbability c t) else Measure.dirac false) := by
    intro t; split_ifs <;> infer_instance
  unfold algorithmOneLaw
  infer_instance

/-- Algorithm 1 with code `c` as an anonymous GlobalClock stream protocol with a trivial
(singleton) shared input. The rule depends only on the code and the global clock, never on
`n`, the error profile, the wake-up pattern or the first wake-up time. -/
noncomputable def algorithmOne (c : ℕ+ → List Bool) : StreamProtocol Unit where
  attempts w := Kernel.const Unit (algorithmOneLaw c w)
  probability _ := inferInstance

end EliasGlobalClock.LowerBound.Supplement


