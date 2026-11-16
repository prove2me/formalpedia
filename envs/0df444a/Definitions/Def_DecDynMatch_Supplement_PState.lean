-- Prove2me | Definitions.Def_DecDynMatch_Supplement_PState
-- name    : DecDynMatch_Supplement_PState
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:25:48.499369+00:00
-- url     : https://prove2.me/theorems/e600f9d4-05e1-425f-ab33-39bf3e8fad19
-- title:
--   Local state of an SC-PC player (modes Seek/Root/Work/Replay, stages Clear/Scan/Commit)
-- statement:
--   The local state of an SC-PC player consists of: per-arm sample counts $N_v$, utility sums $U_v$ and last acceptance ages $\mathrm{lastA}[v]$ (initially $-\infty$); the local clock $a$; the replay scale $P$; the last output age $\ell$ (initially $\bot$); the scheduled change $\nu$; the mode $m\in\{\textsc{Seek},\textsc{Root},\textsc{Work},\textsc{Replay}\}$; the signed BUS counter $x\in\mathbb Z$; the qualification flag armed; the local deadline $c$; the age $b$ from which BUS outcomes count; the Root stage $s\in\{\textsc{Clear},\textsc{Scan},\textsc{Commit}\}$, the scanned arm $j$ and the flag busNext; the Commit entry age $v_C$; the Work round index $h$, the remaining arm set $S_i$, the held arm, the target and the rejection counter $z$; and the output arm $y$ and replay deadline $q$. The module also declares the StateUpdate arguments ($\textsc{Seek}_{\rm fresh}$, $\textsc{Seek}_{\rm armed}$, Root, Scan, Commit, Work, Replay) and the WorkAction proposal types (park, hold, probe, filler).
--
--   **Formalization Note** $-\infty$ and $\bot$ are `none`. The Lean fields `l`, `bq`, `vC`, `S` are $\ell$, $b$, $v_C$, $S_i$. The extra proposal tag `other` marks proposals made outside Work and is never read.
-- source:
--   J. Chen, M. Gao, Z. Zhang, Decentralized Dynamic Stable Matching, arXiv:2610.41912 (held version, sha256 6a27277e…), App. C.1, Algorithms 2, 4–7, pp.29–35

import Mathlib

namespace DecDynMatch.Supplement

/-- Player modes of SC-PC: Seek, Root, Work, Replay (App. C.1, Figure 2, p.29). -/
inductive PMode
  | seek
  | root
  | work
  | replay
  deriving DecidableEq, Repr

/-- Root stages of SC-PC: Clear, Scan, Commit (Algorithm 4, p.32). -/
inductive Stage
  | clear
  | scan
  | commit
  deriving DecidableEq, Repr

/-- The arguments of StateUpdate (Algorithm 4, p.32): Seek_fresh, Seek_armed, Root, Scan, Commit,
Work, Replay. A scheduled change `ν` is one of them. -/
inductive Upd
  | seekFresh
  | seekArmed
  | root
  | scan
  | commit
  | work
  | replay
  deriving DecidableEq, Repr

/-- Proposal types returned by WorkAction (Algorithm 6, p.34): park, hold, probe, filler; `other`
tags a proposal made outside Work (it is never read). -/
inductive PType
  | park
  | hold
  | probe
  | filler
  | other
  deriving DecidableEq, Repr

/-- **Local state of an SC-PC player.** J. Chen, M. Gao, Z. Zhang, *Decentralized Dynamic Stable Matching*, arXiv:2610.41912
(held version, sha256 6a27277e…), App. C.1, Algorithms 2 and 4–7, pp.29–35: per-arm
sample counts `N v`, utility sums `U v` and last acceptance ages `lastA v`; the local clock `a`;
the replay scale `P`; the last output age `ℓ` (field `l`); the scheduled change `ν`; the mode
`m`; the signed BUS counter `x`; the qualification flag `armed`; the local deadline `c`; the age
`b` from which BUS outcomes count (field `bq`); the Root stage `s`; the scanned arm `j`; the flag
`busNext`; the Commit entry age `v_C` (field `vC`); the Work round index `h`; the remaining arms
`Sᵢ` (field `S`); the held arm, the target and the rejection counter `z`; the output arm `y` and
the replay deadline `q`.

**Formalization Note.** `lastA v = none` encodes `−∞`, `l = none` encodes `ℓ = ⊥`, `held = none`
and `target = none` encode `⊥`, `ν = none` encodes "none". The scanned arm `j` is a natural
number in `{1, …, K − 1}`. -/
structure PState (K : ℕ) where
  N : Fin K → ℕ
  U : Fin K → ℝ
  lastA : Fin K → Option ℕ
  a : ℕ
  P : ℕ
  l : Option ℕ
  ν : Option Upd
  m : PMode
  x : ℤ
  armed : Bool
  c : ℕ
  bq : ℕ
  s : Stage
  j : ℕ
  busNext : Bool
  vC : ℕ
  h : ℕ
  S : Finset (Fin K)
  held : Option (Fin K)
  target : Option (Fin K)
  z : ℕ
  y : Fin K
  q : ℕ

end DecDynMatch.Supplement


