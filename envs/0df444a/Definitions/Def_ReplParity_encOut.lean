-- Prove2me | Definitions.Def_ReplParity_encOut
-- name    : ReplParity_encOut
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:37:24.934244+00:00
-- url     : https://prove2.me/theorems/38610002-1b99-4fec-bef8-26e13a69f9c6
-- title:
--   Output encoding: a parity or $\bot$
-- statement:
--   A learner for parities outputs either $\bot$ or a parity $f_z$, which is named by its vector $z\in\mathbb F_2^d$. The machine output is $\bot$ or a bit string $z_1\dots z_d$; over the alphabet $\{0,1,\#\}$, $\bot$ is written as the single symbol $\#$ and a bit string as its bits. A bit string is read back as the vector $z$ with $z_i=1$ exactly when its $i$-th bit is $1$.
-- source:
--   Shen, Zhong, Replicable Parity Learning: Cubic Sample Complexity and a Geometric Characterization, STOC 2027 submission (manuscript sha256 40424491d00eef39c790dd41b7557e0ffdf9de2d14d95ddcd611aeacb0f77a50), §2.1, p.10 (PDF p.12); Theorem 3.6, p.19 (PDF p.21)

import Mathlib
import Definitions.Def_ReplParity_Vec

namespace ReplParity

/-- **Output encoding.** Shen, Zhong, *Replicable Parity Learning: Cubic Sample Complexity and a
Geometric Characterization*, STOC 2027 submission (manuscript sha256 40424491…), §2.1, p.10 and
Theorem 3.6, p.19 (PDF p.21): the learner "outputs a hypothesis or the symbol ⊥"; "Its outputs are
parities or ⊥".

The machine's output is `none` (for `⊥`) or `some l`, a bit list (the vector `z` of the output
parity `f_z`). It is written over `Option Bool` as `[none]` for `⊥` and as the bits of `l`. -/
def encOut : Option (List Bool) → List (Option Bool)
  | none => [none]
  | some l => l.map some

/-- Reading a machine output as `⊥` or as a vector `z ∈ 𝔽ᵈ₂` (`true ↦ 1`, `false ↦ 0`). -/
def decodeOut (d : ℕ) : Option (List Bool) → Option (Vec d) :=
  Option.map (fun l i => if l.getD i false then 1 else 0)

end ReplParity


