-- Prove2me | Definitions.Def_DecDynMatch_Supplement_Protocol
-- name    : DecDynMatch_Supplement_Protocol
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:23:44.920224+00:00
-- url     : https://prove2.me/theorems/23014b1e-4a3e-4f51-93ae-d886bd46dec6
-- title:
--   Randomized decentralized matching protocol (known preferences)
-- statement:
--   A **randomized decentralized matching protocol** on $K$ arms is a single player rule. Given the player's own utility vector $\mu_i=(\mu_{i,k})_{k}$ and its **local history** — the list, oldest first, of its own proposals since entry together with the outcome of each (rejection, or acceptance with the realized utility) — the rule returns a probability distribution over the $K$ arms, the law of the player's proposal in the current round.
--
--   The local clock $a_i=t-b_i$ is the length of the history. The rule sees nothing else: no global clock, no active set $P_t$, no other player's identity, actions or outcomes, no population-event signal. Arms are not part of a protocol: in the known-preference setting every arm accepts its most preferred current proposer. The protocol is fixed before the instance and the horizon.
--
--   **Formalization Note** Private state and private randomness are represented behaviourally, as one distribution per local history; because a player recalls its whole local history, this is the same class of protocols (Kuhn's theorem). `History K` is `List (Fin K × Option ℝ)`, `none` meaning a rejection.
-- source:
--   J. Chen, M. Gao, Z. Zhang, Decentralized Dynamic Stable Matching, arXiv:2610.41912 (held version, sha256 6a27277e…), §2.2, p.4; §2.3, p.5; App. B, p.23

import Mathlib

namespace DecDynMatch.Supplement

/-- A player's local history: one entry per round since its entry, oldest first, holding the arm
it proposed to and the outcome, `none` for a rejection (R) and `some r` for an acceptance (A) with
realized utility `r` (§2.2, p.4: "Each player observes the outcome on whether its proposal is
accepted or rejected (A/R) and, when accepted, its realized utility"). Its length is the player's
local clock `aᵢ = t − bᵢ`. -/
abbrev History (K : ℕ) := List (Fin K × Option ℝ)

/-- **Randomized decentralized matching protocol (known preferences).** J. Chen, M. Gao, Z. Zhang, *Decentralized Dynamic Stable Matching*, arXiv:2610.41912
(held version, sha256 6a27277e…), §2.2, p.4: "A
decentralized matching protocol specifies how players make proposals to arms … using only a
player's … locally available information. In each round t, every active player proposes to exactly
one arm. … Upon entry at round bᵢ, player i initializes its local state according to the protocol,
and sets its local clock to 0. … Neither players nor arms have access to a global clock for t.
Players cannot observe the active player set Pₜ or other players' actions or outcomes. No direct
communication, population-event notification, or public coordination signal is available. In the
known-preference setting, each player i knows its true utilities {μ_{i,k}}_k … Each arm accepts its
most preferred current proposer"; §2.3, p.5: "the protocol is specified first, before the instance
and the time horizon are chosen"; App. B, p.23: "The lower bounds allow private state, private
randomness, adaptive proposals, and accepted utilities."

A protocol on `K` arms is a single player rule: given the player's own utility vector
`μᵢ : Fin K → ℝ` and its local history, it returns the probability distribution of the arm it
proposes to in the current round. Arms are not part of the protocol: in the known-preference setting
each arm accepts its most preferred current proposer.

**Formalization Note.**
* Private state plus private randomness is represented behaviourally, as one distribution per local
  history. Since a player recalls its whole local history, every protocol with private state and
  private random bits induces such a rule with the same law of all proposals (Kuhn's theorem), and
  conversely; the class of protocols is the paper's.
* The rule sees `K` (through the type), `μᵢ`, its local clock (the history length) and its own
  proposals, outcomes and accepted utilities, and nothing else: no global round, no `Pₜ`, no other
  player's identity or actions. -/
structure Protocol (K : ℕ) where
  /-- the law of the next proposal, given the own utilities and the local history -/
  rule : (Fin K → ℝ) → History K → PMF (Fin K)

end DecDynMatch.Supplement


