-- Prove2me | Definitions.Def_ShiMatchmaking_Communication_Matchmaking
-- name    : ShiMatchmaking_Communication_Matchmaking
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T15:47:56.982219+00:00
-- url     : https://prove2.me/theorems/f6443c71-3c4a-481d-a439-01128030a959
-- title:
--   Matchmaking runs, supported worst-case cost, and pair information
-- statement:
--   A matchmaking protocol in $M(n,d^I,d^J)$ is a blackboard protocol on the tagged $2n$ agents, with their private row/column inputs and transaction outputs, that terminates on every positive-mass profile. Output and concatenated transcript are computed from its actual run. Its per-agent cost is the maximum total bit count over supported profiles, divided by $2n$. Success probability is the probability that the output is $\epsilon$-stable. It is not part of protocol admissibility.
--
--   For a fixed pair let $x_{ij}$ indicate whether the run matches it and put
--   $$N_{ij}=P_{ij}(1-x_{ij})+(1-G_{ij})x_{ij}.$$
--   The pair is low-error if its unconditional expectation is at most $.04/n$. Its information is the mutual information in bits between its two private flags and the concatenated transcript. The four laws $\pi_{ab}$ are the actual transcript distributions conditional on these flags being $a,b$, respectively. In particular, $\pi_{11}$ conditions on benefit $.99$ and cost $.01$, and $\pi_{00}$ on benefit zero and cost one.
--
--   A one-round matchmaking protocol instantiates the independent one-round communication object with the same agents, observations, and transaction outputs. Its success probability and cost use the same product law and supported worst-case normalization. Neither entropy lower bounds nor rectangle factorization nor stability is assumed in any structure field. Finite support and termination give finite attained maximum bit counts; off-domain empty support is totalized with maximum zero, and no theorem has empty support or $n=0$.
-- source:
--   Peng Shi (2023), Optimal Matchmaking Strategy in Two-Sided Marketplaces, Management Science, DOI 10.1287/mnsc.2022.4444, supplied published 65-page artifact; Definitions 3–5, pp. 23–25; Appendix D.5, pp. 40–43, equations (D.27)–(D.30), low-error definition p. 41, conditional laws pp. 42–43.

import Definitions.Def_ShiMatchmaking_Communication_Blackboard
import Definitions.Def_ShiMatchmaking_Communication_BinaryMarket

noncomputable section

namespace ShiMatchmaking.Communication

/-- Definition 4 on the binary market: termination only on its support. -/
structure MatchmakingProtocol (n : ℕ) (dI dJ : ℝ) where
  protocol : Blackboard (Agents n) (fun _ => Fin n → Bool) (Outcome n)
  terminates : ∀ ω : Profile n, 0 < marketMass n dI dJ ω →
    protocol.Terminates (privateInput ω)

def MatchmakingProtocol.outcome {n : ℕ} {dI dJ : ℝ}
    (P : MatchmakingProtocol n dI dJ) (ω : Profile n) : Outcome n :=
  P.protocol.result (privateInput ω)

def MatchmakingProtocol.transcript {n : ℕ} {dI dJ : ℝ}
    (P : MatchmakingProtocol n dI dJ) (ω : Profile n) : Message :=
  P.protocol.transcript (privateInput ω)

/-- Worst-case total bits over supported inputs, divided by all 2n agents. -/
def MatchmakingProtocol.cost {n : ℕ} {dI dJ : ℝ}
    (P : MatchmakingProtocol n dI dJ) : ℝ :=
  (((marketSupport n dI dJ).sup (fun ω => P.protocol.bits (privateInput ω)) : ℕ) : ℝ) /
    (2 * (n : ℝ))

def MatchmakingProtocol.success {n : ℕ} {dI dJ : ℝ}
    (P : MatchmakingProtocol n dI dJ) (ε : ℝ) : ℝ :=
  probability (marketMass n dI dJ) (fun ω => Stable (binaryGame ω) ε (P.outcome ω))

/-- Equation (D.30); the matching is obtained from the run, not decoded from flattened bits. -/
def MatchmakingProtocol.pairError {n : ℕ} {dI dJ : ℝ}
    (P : MatchmakingProtocol n dI dJ) (i j : Fin n) (ω : Profile n) : ℝ := by
  classical
  let x : ℝ := if (P.outcome ω).matched i j then 1 else 0
  exact (if Perfect ω i j then 1 else 0) * (1 - x) +
    (1 - if Good ω i j then 1 else 0) * x

/-- Fixed unconditional low-error predicate defining S on p. 41. -/
def MatchmakingProtocol.LowError {n : ℕ} {dI dJ : ℝ}
    (P : MatchmakingProtocol n dI dJ) (i j : Fin n) : Prop :=
  expectation (marketMass n dI dJ) (P.pairError i j) ≤ (4 / 100 : ℝ) / n

def MatchmakingProtocol.pairInformation {n : ℕ} {dI dJ : ℝ}
    (P : MatchmakingProtocol n dI dJ) (i j : Fin n) : ℝ :=
  mutualInformationBits (marketMass n dI dJ) (fun ω => (ω.1 i j, ω.2 i j)) P.transcript

/-- The four conditional transcript laws of pp. 42--43. -/
def MatchmakingProtocol.pairLaw {n : ℕ} {dI dJ : ℝ}
    (P : MatchmakingProtocol n dI dJ) (i j : Fin n) (a b : Bool) : Message → ℝ :=
  conditionalMass (marketMass n dI dJ) P.transcript (fun ω => ω.1 i j = a ∧ ω.2 i j = b)

abbrev OneRoundProtocol (n : ℕ) :=
  Simultaneous (Agents n) (fun _ => Fin n → Bool) (Outcome n)

def oneRoundCost {n : ℕ} (P : OneRoundProtocol n) (dI dJ : ℝ) : ℝ :=
  (((marketSupport n dI dJ).sup (fun ω => P.bits (privateInput ω)) : ℕ) : ℝ) / (2 * (n : ℝ))

def oneRoundSuccess {n : ℕ} (P : OneRoundProtocol n) (dI dJ ε : ℝ) : ℝ :=
  probability (marketMass n dI dJ)
    (fun ω => Stable (binaryGame ω) ε (P.result (privateInput ω)))

end ShiMatchmaking.Communication


