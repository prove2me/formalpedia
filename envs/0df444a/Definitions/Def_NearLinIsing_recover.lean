-- Prove2me | Definitions.Def_NearLinIsing_recover
-- name    : NearLinIsing_recover
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:42:18.705347+00:00
-- url     : https://prove2.me/theorems/42612ede-0475-4623-aa6b-6a2054d7eb6d
-- title:
--   Charged spin recovery
-- statement:
--   Given an edge set $F$ of $G$ as $m$ flags and weights $t_e$, recovery adds each missing edge $e$ independently with probability $t_e$, then gives each connected component of the resulting graph on all $n$ vertices, isolated ones included, an independent fair sign, using a depth-first search over the incidence lists. It outputs the $n$ spins.
-- source:
--   Miao, Near-linear-Time Sampling of the Ferromagnetic Ising Model at the Tree Uniqueness Threshold, arXiv:2611.04786, Lemma 4.5 and its proof, p. 21

import Mathlib
import Definitions.Def_NearLinIsing_Prog

namespace NearLinIsing

/-- **Spin recovery** of Lemma 4.5 (p. 21), charged. Input: an edge set `F` of `G` as an array of
`m` flags (`inF`), and the edge weights `t_e` through the charged accessor `tw` (one read per
edge). Add each missing edge `e` independently with probability `t_e` (giving `A ⊇ F`), then give
each connected component of `(V, A)` (isolated vertices included) an independent fair sign, by a
depth-first search over the incidence lists. Output: the `n` spins as an array of flags.

Miao, *Near-linear-Time Sampling of the Ferromagnetic Ising Model at the Tree Uniqueness
Threshold*, arXiv:2611.04786, Lemma 4.5 and its proof, p. 21.

**Formalization Note.** A spin `true`/`false` stands for `+1`/`−1`; a fair sign is a Bernoulli(½)
draw (reading R3). The search pushes every vertex at most once, so the per-component loop bound
`n` is never reached. -/
noncomputable def recoverSpins (G : IncGraph) (tw : ℕ → ℝ) (inF : Array Bool) : Prog (Array Bool) := do
  let n ← qN G
  let m ← qM G
  let mut A ← alloc m false
  for e in List.range m do
    tick 3 -- dispatch, read input flag, branch
    if inF[e]! then
      tick 1 -- write
      A := A.set! e true
    else
      let te ← op 1 (tw e) -- read the weight
      let b ← bernoulli te
      tick 2 -- branch, write
      if b then A := A.set! e true
  let mut seen ← alloc n false
  let mut spin ← alloc n false
  for s in List.range n do
    tick 3 -- dispatch, read flag, branch
    if !seen[s]! then
      let sg ← bernoulli (1 / 2)
      tick 3 -- two writes, cons
      seen := seen.set! s true
      spin := spin.set! s sg
      let mut stack : List ℕ := [s]
      for _ in List.range n do
        tick 2 -- dispatch, emptiness test
        match stack with
        | [] => break
        | x :: rest =>
          tick 1 -- pop
          stack := rest
          let d ← qDeg G x
          for i in List.range d do
            tick 1 -- dispatch
            let e ← qInc G x i
            tick 2 -- read edge flag, branch
            if A[e]! then
              let ab ← qEnd G e
              tick 4 -- comparison, select, read flag, branch
              let y := if ab.1 = x then ab.2 else ab.1
              if !seen[y]! then
                tick 3 -- two writes, cons
                seen := seen.set! y true
                spin := spin.set! y sg
                stack := y :: stack
  return spin

/-- The spins named by an output array: `σ_v` is entry `v` (default `false`). -/
def spinsOf (G : IncGraph) (a : Array Bool) : Fin G.n → Bool := fun v => a.getD v.val false

/-- An edge set of `G` as the array of its `m` flags (the input format of `recoverSpins`). -/
noncomputable def encF (G : IncGraph) (F : Finset (Fin G.m)) : Array Bool :=
  Array.ofFn fun e : Fin G.m => decide (e ∈ F)

end NearLinIsing


