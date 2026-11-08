-- Prove2me | Definitions.Def_QWildMatch_J
-- name    : QWildMatch_J
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T10:15:21.8062+00:00
-- url     : https://prove2.me/theorems/17c65668-07f9-4b03-af78-367731d0be64
-- title:
--   The blocks $I_b$ of starts, their number $N_B$, and the text intervals $J_b$
-- statement:
--   The $n+1$ possible starts $0,\dots,n$ are partitioned into $N_B=\lceil(n+1)/L\rceil$ consecutive blocks $I_b$ of at most $L$ starts, and
--
--   $$J_b=\bigcup_{s\in I_b}[s,\min(n,s+\ell))$$
--
--   is the set of text positions that a fixed-start verifier of block $b$ can read.
--
--   **Formalization Note** The page does not fix which partition is meant. Here $I_b=\{s\le n: bL\le s<(b+1)L\}$, the canonical one, and $N_B$ is written `(n + L) / L` in natural-number division, which equals the ceiling for $L\ge1$ (see `block_partition`). Positions are `Fin n`, which builds in the $\min(n,\cdot)$.
-- source:
--   Zhao, Chen, Li, Kong, Peng, Yu, Yue, Quantum Approximate Pattern Matching with Wildcards and Weighted Edits, STOC 2027 submission (file sha256 9e87a9dd…), §6.1, p.8

import Mathlib

namespace QWildMatch

/-- The number of blocks `N_B = ⌈(n + 1)/L⌉` (Zhao et al., STOC 2027 submission (file sha256
9e87a9dd…), §6.1, p.8), written `(n + L) / L` in natural-number division, which is the ceiling for
`L ≥ 1` (see `block_partition`). -/
def NB (n L : ℕ) : ℕ := (n + L) / L

/-- The block `I_b` of consecutive starts among `0, …, n`: the starts `s` with `bL ≤ s < (b+1)L`
(Zhao et al., STOC 2027 submission, §6.1, p.8). -/
def I (n L b : ℕ) : Finset ℕ :=
  (Finset.range (n + 1)).filter (fun s => b * L ≤ s ∧ s < (b + 1) * L)

/-- `J_b = ⋃_{s ∈ I_b} [s, min(n, s + ℓ))`, the text positions any fixed-start verifier of block `b`
can read (Zhao et al., STOC 2027 submission, §6.1, p.8).

**Formalization Note** Positions are `Fin n`, which builds in the `min(n, ·)`. -/
def J (n L l b : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun x : Fin n => ∃ s ∈ I n L b, s ≤ (x : ℕ) ∧ (x : ℕ) < s + l)

end QWildMatch


