-- Prove2me | Definitions.Def_PopRAM_RegInit
-- name    : PopRAM_RegInit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:22:16.42701+00:00
-- url     : https://prove2.me/theorems/83caae9c-2a76-4ddd-a115-fc39e8c4c6a0
-- title:
--   Register initialisation (Protocol 3) as a mini-protocol
-- statement:
--   Protocol 3 allocates the $M=\rho' w$ register bits one by one: "The leader assigns the $i$-th bit of register $r$ to the first free agent it encounters: $L + \phi \to L + (R; r, i, 0)$." Number the bits $m = r w + i$, $0\le m<M$, in the order of the double loop. The states are $L_m$ (the leader after allocating $m$ bits), $\phi$ (free), $R_m$ (the agent holding bit $m$, value $0$) and $X$ (any other agent, inert). The rule is
--   $$L_m + \phi \to L_{m+1} + R_m,\qquad \phi + L_m \to R_m + L_{m+1}\qquad (m<M),$$
--   and every other pair is unchanged. Allocation is complete when the leader is in $L_M$.
--
--   **Formalization Note** The rule applies in both orientations because the proof of Lemma 2 counts the probability $2p/n$ per interaction (the leader as initiator or as responder).
-- source:
--   Gąsieniec, Grodzicki, Stachowiak, Efficient Stable Word-RAM Simulation by Population Protocols, arXiv:2611.06178 (preprint, held version, sha256 f13223b33593e77d2342fbfab2d49c58efd6035c06f316456f76030e0dca9acd), Protocol 3, p.14 (PDF p.15); Lemma 2 and its proof, pp.7–8 (PDF pp.8–9)

import Mathlib

set_option autoImplicit false

namespace PopRAM

/-! # RegInit as a mini-protocol (Protocol 3)

Gąsieniec, Grodzicki, Stachowiak, *Efficient Stable Word-RAM Simulation by Population Protocols*,
arXiv:2611.06178 (held version, sha256 f13223b3…), Protocol 3, p.14 (PDF p.15), and Lemma 2 with its
proof, pp.7–8 (PDF pp.8–9): "The leader assigns the i-th bit of register r to the first free agent
it encounters: L + φ → L + (R; r, i, 0)."

**Formalization Note** The `M = ρ′w` register bits are numbered `m = r·w + i < M`, in the order of
Protocol 3's double loop. `L m` is the leader that has allocated `m` bits, `φ` (`free`) a free
agent, `R m` the agent holding bit `m` (value `0`), and `X` any other agent (inert). The allocation
rule applies in **both** orientations: the proof of Lemma 2 counts the probability `2p/n` per
interaction ("each interaction assigns the next bit with probability at least 2p/n"), i.e. the leader
as initiator or as responder. Every other pair of states is unchanged. -/

/-- States of RegInit. -/
inductive RIState where
  | L (m : ℕ)
  | free
  | R (m : ℕ)
  | X
  deriving DecidableEq

/-- The transition function of RegInit with `M` bits to allocate. -/
def regInitδ (M : ℕ) : RIState → RIState → RIState × RIState
  | .L m, .free => if m < M then (.L (m + 1), .R m) else (.L m, .free)
  | .free, .L m => if m < M then (.R m, .L (m + 1)) else (.free, .L m)
  | a, b => (a, b)

/-- Allocation is complete: the leader has allocated all `M` bits. -/
def regInitDone {n : ℕ} (M : ℕ) : Set (Fin n → RIState) := {c | ∃ b, c b = .L M}

end PopRAM


