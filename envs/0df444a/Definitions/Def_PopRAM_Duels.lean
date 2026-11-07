-- Prove2me | Definitions.Def_PopRAM_Duels
-- name    : PopRAM_Duels
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:22:19.043028+00:00
-- url     : https://prove2.me/theorems/bd2f656d-b86e-4d39-b03d-6145ccddfcbe
-- title:
--   Leader election by ranked duels (backup, §C.1)
-- statement:
--   In the backup's election stage every agent is a leader $(L,i)$ or a non-input follower $(F,i)$ of rank $i$, or an input agent. The rules are
--   $$(L,i)+(L|F,j)\to(L,i)+(F,i)\ \text{ if } i>j,\qquad (L,i)+(L,i)\to(L,i+1)+(F,i+1),$$
--   and, as "rules involving the leader apply in both interaction orientations", each applies with the leader as initiator or as responder; in an equal-rank duel the initiator wins. Input agents are unchanged in this stage, and so are interactions between two non-leaders. `uniqueLeader` is the set of configurations with exactly one leader.
-- source:
--   Gąsieniec, Grodzicki, Stachowiak, Efficient Stable Word-RAM Simulation by Population Protocols, arXiv:2611.06178 (preprint, held version, sha256 f13223b33593e77d2342fbfab2d49c58efd6035c06f316456f76030e0dca9acd), §C.1, p.31 (PDF p.32); p.30 (PDF p.31)

import Mathlib

set_option autoImplicit false

namespace PopRAM

/-! # Leader election by ranked duels (backup, §C.1)

Gąsieniec, Grodzicki, Stachowiak, *Efficient Stable Word-RAM Simulation by Population Protocols*,
arXiv:2611.06178 (held version, sha256 f13223b3…), §C.1, p.31 (PDF p.32):

    (L, i) + (L|F, j) → (L, i) + (F, i)  if i > j,
    (L, i) + (L, i) → (L, i + 1) + (F, i + 1),

and p.30 (PDF p.31): "Rules involving the leader apply in both interaction orientations."

**Formalization Note** `ldr i` is a leader of rank `i`, `fol i` a non-input follower of rank `i`,
`inp` an input agent (inert in this stage: "In this stage, the transition function concerns only the
role and rank component", and input agents receive a rank only in input conversion). Both rules
apply in both orientations; in an equal-rank duel the initiator wins. All other pairs (including
two non-leaders) are unchanged. -/

/-- States of the duel stage. -/
inductive DState where
  | ldr (i : ℕ)
  | fol (i : ℕ)
  | inp
  deriving DecidableEq

/-- The transition function of the duel stage. -/
def duelδ : DState → DState → DState × DState
  | .ldr i, .ldr j =>
      if j < i then (.ldr i, .fol i)
      else if i < j then (.fol j, .ldr j)
      else (.ldr (i + 1), .fol (i + 1))
  | .ldr i, .fol j => if j < i then (.ldr i, .fol i) else (.ldr i, .fol j)
  | .fol j, .ldr i => if j < i then (.fol i, .ldr i) else (.fol j, .ldr i)
  | a, b => (a, b)

/-- Whether a state is a leader. -/
def isLdr : DState → Bool
  | .ldr _ => true
  | _ => false

/-- Configurations with exactly one leader. -/
def uniqueLeader {n : ℕ} : Set (Fin n → DState) :=
  {c | (Finset.univ.filter (fun b => isLdr (c b) = true)).card = 1}

end PopRAM


