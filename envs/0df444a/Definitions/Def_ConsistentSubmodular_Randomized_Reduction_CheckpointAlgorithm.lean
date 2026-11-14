-- Prove2me | Definitions.Def_ConsistentSubmodular_Randomized_Reduction_CheckpointAlgorithm
-- name    : ConsistentSubmodular_Randomized_Reduction_CheckpointAlgorithm
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:08:57.473496+00:00
-- url     : https://prove2.me/theorems/8d83101e-4d05-4eaf-93f0-14afdcea60bd
-- title:
--   Algorithm 1 (checkpoint algorithm): parameters, blocks, states and run
-- statement:
--   Elements are $0,\dots,n-1$ (element $e$ is the paper's $x_{e+1}$), and $X_t$ denotes the arrived prefix after $t$ arrivals.
--
--   - `Params` has four natural-number fields: block length $\ell=\lfloor\gamma k\rfloor$, core budget $\kappa=k-2\ell$, number of subblocks $h=\lceil1/\gamma\rceil$, and number $s$ of transition operations per update.
--   - `Params.Valid P k` asserts, for the budget $k$: $\ell>0$, $h>0$, $\kappa+2\ell\le k$, and $k\le s\cdot\lfloor \ell/h\rfloor$ (so that $s$ operations per update finish every transition inside the shortest subblock).
--   - `block n ℓ i` is the block $B_{i+1}$ of the paper: the arrivals $x_{i\ell+1},\dots,x_{(i+1)\ell}$.
--   - `oldCore n ℓ A i` is the old core of block $i$, $A_{i-1}\cup B_i$ (with $A_{i-1}$ the checkpoint sample of the preceding block), and $\emptyset$ for $i=0$.
--   - `state P A σ i r` is the maintained set after $r$ updates of block $i$, given samples $A_i$ and selected subblocks $\sigma_i$:
--   $$\mathrm{path}\bigl(C_i,\,A_i,\ \mathrm{done}(\ell,h,s,\ \mathrm{operations}(C_i,A_i),\ \sigma_i,\ r)\bigr)\ \cup\ \bigl(B_{i+1}\cap X_{i\ell+r}\bigr),$$
--   where $C_i$ is the old core: the transition performed so far, plus the arrivals of the current block.
--   - `phase ℓ t` $=\lfloor (t-1)/\ell\rfloor$ is the block of the update at time $t\ge1$, and `pos ℓ t` $=t-\mathrm{phase}\cdot\ell$ its position inside the block, between $1$ and $\ell$.
--   - `run P A σ t` is the set $\mathrm{ALG}_t$ maintained by Algorithm 1: `state` at block `phase` and position `pos`.
--   - `Good P A σ` is the property of the random choices that for all blocks $i$: $\sigma_i<h$, $A_i\subseteq X_{i\ell}$ and $|A_i|\le\kappa$ (the choices of positive probability).
--
--   These definitions give the explicit trajectory of Algorithm 1 in the randomized reduction (Lemma 1, Appendix A.3) from clairvoyant addition robustness to consistency.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Randomized/Reduction/CheckpointAlgorithm.lean (definitions and supporting lemmas of this module, ported from Lean v4.30.0-rc1 to Lean v4.33.1)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Randomized_Reduction_CheckpointSchedule
import Definitions.Def_ConsistentSubmodular_Randomized_Reduction_CheckpointWindow

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular.Checkpoints

variable {n : ℕ}

/-- The parameters of Algorithm 1: the block length `ℓ = ⌊γk⌋`, the core budget
`κ = k - 2ℓ`, the number `h = ⌈1/γ⌉` of subblocks per block, and the number `s`
of transition operations per update. -/
structure Params where
  ℓ : ℕ
  κ : ℕ
  h : ℕ
  s : ℕ

/-- The conditions on the parameters that the analysis uses for the budget `k`:
both cores and the current block fit into the budget, and `s` operations per
update finish every transition inside the shortest subblock, which has
`⌊ℓ/h⌋` updates. -/
structure Params.Valid (P : Params) (k : ℕ) : Prop where
  block_pos : 0 < P.ℓ
  subblocks_pos : 0 < P.h
  budget : P.κ + 2 * P.ℓ ≤ k
  complete : k ≤ P.s * (P.ℓ / P.h)

/-- Block `i`, the block `B_{i+1}` of the paper: the arrivals
`x_{iℓ+1}, ..., x_{(i+1)ℓ}`. -/
def block (n ℓ i : ℕ) : Finset (Fin n) := future n (i * ℓ) ℓ

/-- The old core of block `i`: `A_{i-1} ∪ B_i` in the paper's notation, and
`∅` for the first block, whose arrivals are all retained. -/
def oldCore (n ℓ : ℕ) (A : ℕ → Finset (Fin n)) (i : ℕ) : Finset (Fin n) :=
  if i = 0 then ∅ else A (i - 1) ∪ block n ℓ (i - 1)

/-- The maintained set after `r` updates of block `i`: the core after the
transition operations performed so far, together with the arrivals of the
current block. -/
def state (P : Params) (A : ℕ → Finset (Fin n)) (σ : ℕ → ℕ) (i r : ℕ) : Finset (Fin n) :=
  path (oldCore n P.ℓ A i) (A i)
      (done P.ℓ P.h P.s (operations (oldCore n P.ℓ A i) (A i)) (σ i) r) ∪
    (block n P.ℓ i ∩ arrivedPrefix n (i * P.ℓ + r))

/-- The block `⌊(t - 1)/ℓ⌋` of the update at time `t ≥ 1`. -/
def phase (ℓ t : ℕ) : ℕ := (t - 1) / ℓ

/-- The position of time `t` inside its block, between `1` and `ℓ` for `t ≥ 1`. -/
def pos (ℓ t : ℕ) : ℕ := t - phase ℓ t * ℓ

/-- The set `ALG_t` maintained by Algorithm 1. -/
def run (P : Params) (A : ℕ → Finset (Fin n)) (σ : ℕ → ℕ) (t : ℕ) : Finset (Fin n) :=
  state P A σ (phase P.ℓ t) (pos P.ℓ t)

/-- Random choices with positive probability: the subblock indices are in
range, and the sample of the checkpoint after block `i` is a set of at most `κ`
elements arrived by then. -/
def Good (P : Params) (A : ℕ → Finset (Fin n)) (σ : ℕ → ℕ) : Prop :=
  ∀ i, σ i < P.h ∧ A i ⊆ arrivedPrefix n (i * P.ℓ) ∧ (A i).card ≤ P.κ

end ConsistentSubmodular.Checkpoints

end


