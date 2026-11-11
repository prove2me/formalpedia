-- Prove2me | Definitions.Def_DecDynMatch_LState
-- name    : DecDynMatch_LState
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T09:56:25.225015+00:00
-- url     : https://prove2.me/theorems/e0796223-445f-47b9-b2f2-07f24a4d1874
-- title:
--   Local state of an SC-DA player
-- statement:
--   Each SC-DA player keeps a purely local state: the local clock $a$; the previous Work completion time $\ell$; the counter $\rho$ of consecutive BUS acceptances (capped at $J$); the Work round index $h$; the saved arm $y$; the replay deadline $q$ (in local time); the Sweep position $s\in\{1,\dots,2K\}$; the deferred-acceptance index $k\in\{1,\dots,K\}$; the mode $m\in\{\textsf{Seek},\textsf{Sweep},\textsf{Work},\textsf{Replay}\}$; a pending mode $\nu$ (or none); the BUS-rejection flag $\textsf{seenR}$; and the flag $\textsf{blockOK}$ of the current Sweep block.
--
--   On arrival a player starts with $a=\ell=\rho=h=0$, $y=0$, $s=k=1$, $m=\textsf{Seek}$, $\nu=$ none, $\textsf{seenR}=$ false. The Sweep proposal sequence is
--   $$
--   \sigma=(0,1,0,2,\dots,0,K-1,0,0),
--   $$
--   indexed by $1,\dots,2K$.
--
--   **Formalization Note** The field `l` is $\ell$. Algorithm 1 does not initialize $q$ and $\textsf{blockOK}$; both are written before they are read, so the chosen initial values $q=0$, $\textsf{blockOK}=$ true are never observed. The Sweep index is 1-based as in the paper.
-- source:
--   J. Chen, M. Gao, Z. Zhang, Decentralized Dynamic Stable Matching, arXiv:2610.41912 (held version, sha256 6a27277e…), Algorithm 1, lines 2–3, p.6; eq. (3), p.7; p.14

import Mathlib
import Definitions.Def_DecDynMatch_Instance

namespace DecDynMatch

/-- The four local modes Seek, Sweep, Work, Replay of SC-DA (§3.1, p.5). -/
inductive Mode
  | seek
  | sweep
  | work
  | replay
  deriving DecidableEq, Repr

/-- **Local state of an SC-DA player.** J. Chen, M. Gao, Z. Zhang, *Decentralized Dynamic Stable
Matching*, arXiv:2610.41912 (held version, sha256 6a27277e…), Algorithm 1, p.6: the variables
`a` (local clock), `ℓ` (previous Work completion time, here `l`), `ρ` (consecutive BUS acceptances),
`h` (Work round index), `y` (saved arm), `q` (replay deadline, local time), `s` (Sweep position),
`k` (DA application index), `m` (mode), `ν` (pending mode, `none` = no change), `seenR`
(BUS-rejection flag) and `blockOK` (current Sweep block all accepted).

**Formalization Note.** The field `l` is the paper's `ℓ`. `ν : Option Mode` with `none` for the
paper's "none". -/
structure LState (K : ℕ) where
  a : ℕ
  l : ℕ
  ρ : ℕ
  h : ℕ
  y : Fin K
  q : ℕ
  s : ℕ
  k : ℕ
  m : Mode
  ν : Option Mode
  seenR : Bool
  blockOK : Bool

variable {K : ℕ} {ι : Type*} [Fintype ι]

/-- Initial state on arrival (Algorithm 1, line 3, p.6; p.14): "a, ℓ, ρ, h, y ← 0; s, k ← 1;
m ← Seek; ν ← none; seenR ← false".

**Formalization Note.** Algorithm 1 does not initialize `q` and `blockOK`; both are written before
they are read (`q` at every Work output, `blockOK` on every Sweep entry), so the values `q = 0`,
`blockOK = true` chosen here are never observed. `y = 0` is arm `0`. -/
def init (I : Instance K ι) : LState K :=
  { a := 0, l := 0, ρ := 0, h := 0, y := bus I, q := 0, s := 1, k := 1, m := .seek, ν := none,
    seenR := false, blockOK := true }

/-- The Sweep proposal sequence `σ = (0, 1, 0, 2, …, 0, K − 1, 0, 0)` (eq. (3), p.7), "indexed by
1, 2, …, 2K": `σ_s = s / 2` for even `s < 2K`, and `σ_s = 0` (BUS) for odd `s` and for `s = 2K`.
The index `s` is 1-based as in the paper. -/
def sigma (I : Instance K ι) (s : ℕ) : Fin K :=
  if hs : s % 2 = 0 ∧ s < 2 * K then ⟨s / 2, by omega⟩ else bus I

end DecDynMatch


