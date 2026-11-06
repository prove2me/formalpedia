-- Prove2me | Definitions.Def_NearLinIsing_cycleTrial
-- name    : NearLinIsing_cycleTrial
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:41:59.424387+00:00
-- url     : https://prove2.me/theorems/bdfbb2b5-441a-406e-83dc-571f2fecd80a
-- title:
--   The exact cycle trial and the insertion proposal
-- statement:
--   The **cycle trial** starts at a uniform directed edge $a_0$ of $H$ and walks with the transition probabilities (13), stopping with the leftover probability $1-\sum_bP_H(a,b)$ of the current row. After querying transition $\ell$ it continues to transition $\ell+1$ with probability $\ell/(\ell+1)$, so transition $\ell$ is reached with probability $1/\ell$. The exploration ends at the first repeated directed edge, and the result is retained only if that edge is $a_0$ and the closed walk is a simple cycle; the trial then outputs the cycle's edge list, and otherwise no candidate.
--
--   The **insertion proposal** runs one trial with probability $|E(H)|/(4N)$ and proposes nothing otherwise. Scratch arrays are cleared along the path, so a trial costs what it explores.
-- source:
--   Miao, Near-linear-Time Sampling of the Ferromagnetic Ising Model at the Tree Uniqueness Threshold, arXiv:2611.04786, §4.2, Eq. (13), p. 19; Lemma 4.4 and its proof, p. 21; proof of Proposition 4.6, pp. 21–22

import Mathlib
import Definitions.Def_NearLinIsing_Prog
import Definitions.Def_NearLinIsing_PortGraph

namespace NearLinIsing

/-!
The exact cycle proposal of Lemma 4.4 (p. 21) and the insertion proposal it implements.

Miao, *Near-linear-Time Sampling of the Ferromagnetic Ising Model at the Tree Uniqueness
Threshold*, arXiv:2611.04786, §4.2 (Eq. (13), p. 19), proof of Lemma 4.3 (last paragraph, p. 21),
Lemma 4.4 and its proof (p. 21), proof of Proposition 4.6 (pp. 21–22).
-/

/-- Scratch arrays of the trial: `vis` (per directed edge: visited in the current exploration) and
`mark` (per port: used by the simplicity test). Both are all `false` between trials; the trial
clears what it touched along its own path ("touched-vertex lists", proof of Proposition 4.6). -/
structure Scratch where
  vis : Array Bool
  mark : Array Bool

/-- The clean scratch arrays of `H` (their allocation is charged by the caller, `initState`). -/
def Scratch.init (H : PortGraph) : Scratch :=
  ⟨Array.replicate (2 * H.ne) false, Array.replicate H.np false⟩

/-- One transition of the exploration from a row of `P_H`: with the uniform `u`, scan the row with
cumulative sums and return the first successor `b` with `u < ∑_{b' ≤ b} P_H(a,b')`; return `none`
(stop) with the leftover probability `1 − ∑_b P_H(a,b)`. -/
noncomputable def scanRow (row : List (ℕ × ℝ)) (u : ℝ) : Prog (Option ℕ) := do
  let mut cum : ℝ := 0
  let mut res : Option ℕ := none
  for bp in row do
    tick 3 -- dispatch, addition, comparison
    cum := cum + bp.2
    if u < cum then
      res := some bp.1
      break
  return res

/-- **The cycle trial** of Lemma 4.4 (proof, p. 21). Start at a uniform directed edge `a₀` of `H`.
Repeatedly query one transition of (13) from the current directed edge (stop with the row's
leftover probability). If the new directed edge was already visited, the exploration ends: the
result is retained only when that first repeated directed edge is `a₀` and the closed walk is a
simple cycle (its head ports are distinct), and then the trial outputs the list of its physical
edges. Otherwise, after querying transition `ℓ`, continue to transition `ℓ + 1` with probability
`ℓ/(ℓ+1)` (the horizon with survival probability `1/ℓ` at transition `ℓ`). In every other case the
output is `none` (no candidate). The scratch arrays are cleared along the path before returning.

**Formalization Note.** At most `2 ne` directed edges are distinct, so the loop bound `2 ne + 1` is
never reached before a repetition or a stop. -/
noncomputable def cycleTrial (H : PortGraph) (sc : Scratch) : Prog (Option (List ℕ) × Scratch) := do
  let D ← op 1 (2 * H.ne)
  let a0 ← uniformIdx D
  tick 2 -- write flag, cons
  let mut vis := sc.vis.set! a0 true
  let mut mark := sc.mark
  let mut path : List ℕ := [a0]
  let mut cur := a0
  let mut len : ℕ := 0
  let mut res : Option (List ℕ) := none
  for _ in List.range (D + 1) do
    tick 2 -- dispatch, row read
    let u ← drawU
    let nb ← scanRow (H.rowP[cur]!) u
    tick 1 -- increment
    len := len + 1
    match nb with
    | none => break
    | some b =>
      tick 2 -- flag read, branch
      if vis[b]! then
        tick 1 -- comparison
        if b = a0 then
          let mut simple := true
          for a in path do
            tick 7 -- dispatch, division, parity, endpoint read, flag read, branch, write
            let q := if a % 2 = 0 then H.eV[a / 2]! else H.eU[a / 2]!
            if mark[q]! then simple := false
            mark := mark.set! q true
          for a in path do
            tick 5 -- dispatch, division, parity, endpoint read, write
            let q := if a % 2 = 0 then H.eV[a / 2]! else H.eU[a / 2]!
            mark := mark.set! q false
          tick 1 -- branch
          if simple then
            tick (2 * path.length) -- one division and one cons per edge of the output list
            res := some (path.map (· / 2))
        break
      else
        tick 3 -- write flag, cons, assignment
        vis := vis.set! b true
        path := b :: path
        cur := b
        let v ← drawU
        tick 4 -- cast, increment, division, comparison
        if (len : ℝ) / (len + 1) ≤ v then break
  for a in path do
    tick 2 -- dispatch, write
    vis := vis.set! a false
  return (res, { vis := vis, mark := mark })

/-- **The insertion proposal** (Lemma 4.4, last sentence; §3.1, p. 10): with probability
`|E(H)|/(4N)` run one cycle trial, otherwise propose nothing. -/
noncomputable def insertProposal (H : PortGraph) (N : ℕ) (sc : Scratch) :
    Prog (Option (List ℕ) × Scratch) := do
  let u ← drawU
  tick 5 -- two casts, multiplication, division, comparison
  if u < (H.ne : ℝ) / (4 * N) then cycleTrial H sc else pure (none, sc)

end NearLinIsing


