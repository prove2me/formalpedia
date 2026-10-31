-- Prove2me | Definitions.Def_TractableComposite_liftProg
-- name    : TractableComposite_liftProg
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:51:53.126996+00:00
-- url     : https://prove2.me/theorems/d5ef6620-efe7-4ef1-99ea-6ce3cc98d091
-- title:
--   The lifting program $\bar u\mapsto\bar s$ (monotone-chain upper hull)
-- statement:
--   A program in the real-RAM tick model that computes the lifting $\bar s$ of $\bar u\in P$. For each row $i$ it
--
--   1. builds the upper hull of the points $(a_{ik},u_{ik})$, $k=0,\dots,n$ (abscissas already sorted) by a monotone-chain stack scan, popping the top while it is not strictly above the segment from the point below it to the new point;
--   2. reverses the stack into the ascending list of hull indices;
--   3. walks $j=0,\dots,n$, setting $\bar s_{ij}=u_{ij}$ at hull indices and interpolating linearly between neighbouring hull indices elsewhere.
--
--   Each index is pushed once and popped at most once, so the program takes $O(n)$ ticks per row. Every real operation, comparison and loop iteration costs one tick.
-- source:
--   He & Tawarmalani, Tractable relaxations of composite functions (manuscript, sha256 8c6bca18…), pp.4–6 ("a two-dimensional convex hull algorithm, such as Graham scan [14]", "in O(n) time")

import Mathlib
import Definitions.Def_LNTopology_Hermetization_tick
import Definitions.Def_LNTopology_Hermetization_rle
import Definitions.Def_LNTopology_Hermetization_rmul
import Definitions.Def_LNTopology_Hermetization_rdiv
import Definitions.Def_TractableComposite_radd
import Definitions.Def_TractableComposite_rsub

namespace TractableComposite

/-- **The lifting program ū ↦ s̄**, Proposition 2, p.6 ("the unique point (ū, s̄) ∈ PQ' can be found in
O(dn) time") and pp.4–5 ("a two-dimensional convex hull algorithm, such as Graham scan [14], that, for
each of the d discrete univariate functions ξᵢ(a; uᵢ) finds its envelope in O(n) time").
He & Tawarmalani, *Tractable relaxations of composite functions* (manuscript, sha256 8c6bca18…), pp.4–6.

For each `i`, the program
1. builds the upper hull of the points `(aᵢₖ, uᵢₖ)`, `k = 0,…,n` (abscissas already sorted), by a
   monotone-chain stack scan: before pushing `k` it pops the top `t₁` (above `t₂`) while `t₁` is not
   strictly above the segment `t₂ k`, tested by the ticked orientation test
   `(u_{t₁} − u_{t₂})(a_k − a_{t₂}) ≤ (a_{t₁} − a_{t₂})(u_k − u_{t₂})`; each index is pushed once and popped at
   most once;
2. reverses the stack (a ticked loop) into the ascending list of hull indices;
3. walks `j = 0,…,n` along the hull: at a hull index it sets `s̄ᵢⱼ = ūᵢⱼ`, otherwise it interpolates
   linearly between the neighbouring hull indices.

**Cost model** (reading R3; the published discipline of `LNTopology.Hermetization.tick`): every real
arithmetic operation (`radd`, `rsub`, `rmul`, `rdiv`), every real comparison (`rle`, `req`) and every
query of `φ` (`phiAt`) costs one tick; every iteration of every loop and every recursive call ticks at
least once, and the unticked work inside one iteration is a bounded number of reads and updates of
array-like state (`Fin d → Fin (n+1) → ℝ`, `Fin d → Fin (n+1)`, `Fin d → Fin (n+1) → Bool`, the head of
a list, index arithmetic on `ℕ`/`Fin`); the only decisions on real data are the ticked primitives; the
program never reads the counter. The running time of a run started at `0` is the final counter. -/
noncomputable def liftProg {d n : ℕ} (a u : Fin d → Fin (n + 1) → ℝ) : StateM ℕ (Fin d → Fin (n + 1) → ℝ) := do
  let mut s : Fin d → Fin (n + 1) → ℝ := fun _ _ => 0
  for i in List.finRange d do
    LNTopology.Hermetization.tick 1
    -- step 1: monotone-chain upper hull; `st` is the stack, top first
    let mut st : List (Fin (n + 1)) := []
    for k in List.finRange (n + 1) do
      LNTopology.Hermetization.tick 1
      -- pop loop: at most `k` iterations (the stack holds at most `k` indices)
      for _ in List.range k.val do
        LNTopology.Hermetization.tick 1
        match st with
        | t₁ :: t₂ :: rest =>
          let dx₁ ← rsub (a i t₁) (a i t₂)
          let dyk ← rsub (u i k) (u i t₂)
          let dy₁ ← rsub (u i t₁) (u i t₂)
          let dxk ← rsub (a i k) (a i t₂)
          let p₁ ← LNTopology.Hermetization.rmul dx₁ dyk
          let p₂ ← LNTopology.Hermetization.rmul dy₁ dxk
          let notAbove ← LNTopology.Hermetization.rle p₂ p₁
          if notAbove then st := t₂ :: rest else break
        | _ => break
      st := k :: st
    -- step 2: reverse the stack into the ascending list of hull indices
    let mut hull : List (Fin (n + 1)) := []
    for _ in List.range (n + 1) do
      LNTopology.Hermetization.tick 1
      match st with
      | t :: rest =>
        hull := t :: hull
        st := rest
      | [] => break
    -- step 3: evaluate the envelope at every abscissa
    let mut lft : Fin (n + 1) := 0
    for j in List.finRange (n + 1) do
      LNTopology.Hermetization.tick 1
      match hull with
      | h :: tl =>
        if h = j then
          s := Function.update s i (Function.update (s i) j (u i j))
          lft := j
          hull := tl
        else
          let num ← rsub (a i j) (a i lft)
          let den ← rsub (a i h) (a i lft)
          let t ← LNTopology.Hermetization.rdiv num den
          let dy ← rsub (u i h) (u i lft)
          let inc ← LNTopology.Hermetization.rmul t dy
          let v ← radd (u i lft) inc
          s := Function.update s i (Function.update (s i) j v)
      | [] => pure ()
  return s

end TractableComposite


