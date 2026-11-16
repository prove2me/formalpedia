-- Prove2me | Definitions.Def_EntAssistOneWay_Separation_Supplement_RandomizedSMP
-- name    : EntAssistOneWay_Separation_Supplement_RandomizedSMP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T16:49:52.295201+00:00
-- url     : https://prove2.me/theorems/ae2ff18b-753b-4ab4-9c37-b81ce89d5988
-- title:
--   Classical SMP protocols with player-only shared randomness and a randomized referee
-- statement:
--   A **classical simultaneous-message-passing (SMP) protocol with shared randomness between the players only** consists of a probability space $(\Omega,P)$ of shared seeds; message maps $a(\omega,x)\in\{0,1\}^{c_A}$ for Alice and $b(\omega,y)\in\{0,1\}^{c_B}$ for Bob, measurable in $\omega$ for every input; and a referee that sees only the two messages and accepts with probability $q(a,b)\in[0,1]$, using its own private coin. The cost is $c_A+c_B$ and the acceptance probability is
--
--   $$\Pr[\text{accept}\mid x,y]=\int_\Omega q\big(a(\omega,x),b(\omega,y)\big)\,dP(\omega).$$
--
--   The referee never sees the seed. This is the target model $C^{\parallel,\mathrm{pub}}$ of Theorem 3.4.
--
--   **Formalization Note** Private coins of Alice and Bob are part of $\omega$. The integrand is measurable and $[0,1]$-valued, so the Bochner integral is the true expectation.
-- source:
--   Ryan Anselm, Srijita Kundu, Olivier Lalonde, Ashwin Nayak, STOC 2027 submission #228 (October 2026), p. 15, §3.1 (SMP model with randomness shared between Alice and Bob only); p. 18, proof of Theorem 3.4 (randomized referee output)

import Mathlib

open scoped BigOperators
open Classical
set_option autoImplicit false

namespace EntAssistOneWay.Separation.Supplement

noncomputable section

/-- §3.1, p. 15: a classical SMP protocol in which only Alice and Bob share randomness.
The shared seed `ω` lives on an arbitrary probability space (private coins of the players
are part of it). Alice sends `cA` bits depending on `(ω, x)`, Bob sends `cB` bits depending
on `(ω, y)`; the referee sees only the two messages and accepts with probability
`referee a b ∈ [0, 1]` (its own private coin). Cost: `cA + cB`. -/
structure RandomizedSMPProtocol (X Y Ω : Type) [MeasurableSpace Ω] (cA cB : ℕ) where
  seedLaw : MeasureTheory.Measure Ω
  probability : MeasureTheory.IsProbabilityMeasure seedLaw
  alice : Ω → X → Fin (2 ^ cA)
  bob : Ω → Y → Fin (2 ^ cB)
  measurable_alice : ∀ x, Measurable (fun ω => alice ω x)
  measurable_bob : ∀ y, Measurable (fun ω => bob ω y)
  referee : Fin (2 ^ cA) → Fin (2 ^ cB) → ℝ
  referee_nonneg : ∀ a b, 0 ≤ referee a b
  referee_le_one : ∀ a b, referee a b ≤ 1

/-- Acceptance probability `∫ q(a(ω,x), b(ω,y)) dP(ω)`; the integrand is measurable and
takes values in `[0, 1]`, so the integral is the true expectation. -/
def randomizedSMPAccept {X Y Ω : Type} [MeasurableSpace Ω] {cA cB : ℕ}
    (P : RandomizedSMPProtocol X Y Ω cA cB) (x : X) (y : Y) : ℝ :=
  ∫ ω, P.referee (P.alice ω x) (P.bob ω y) ∂P.seedLaw

end

end EntAssistOneWay.Separation.Supplement


