-- Prove2me | Definitions.Def_CanadaCTP_PathExplorer
-- name    : CanadaCTP_PathExplorer
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:19:25.425292+00:00
-- url     : https://prove2.me/theorems/e5c11a42-4bb9-423f-8d9c-81b44cc07b83
-- title:
--   Algorithm 2 — PathExplorer, implemented with the $O(d)$ iteration of Lemma 8 and its trace
-- statement:
--   **PathExplorer** (Algorithm 2) computes a coin vector for a path $X$ and budget $b$. It starts from $\mathrm{coin}\equiv1$. While $\mathrm{expCost}(\mathrm{coin})>b$, it chooses among the pairs $(j,x)$ with $\mathrm{coin}(j,x)=1$ and $\beta(j,x,\mathrm{coin})>0$ one minimizing $\alpha/\beta$, ties broken by the lexicographic order on (edge, support index), and sets $\mathrm{coin}(j^*,x^*)=0$; if the expected cost is now below $b$, it raises $\mathrm{coin}(j^*,x^*)$ to $(b-b_{i+1})/(b_i-b_{i+1})$, so that the cost is exactly $b$, and stops.
--
--   Each iteration computes, as in the proof of Lemma 8, $q_j=\sum_x P[X_j=x]\mathrm{coin}(j,x)$, $r_j=\sum_x P[X_j=x]\mathrm{coin}(j,x)\,x$, the reach probabilities $\prod_{\ell<j}q_\ell$, $\mathrm{restProb}(j)=\prod_{\ell>j}q_\ell$ and $z_j$ with $\mathrm{restCost}(j,x)=x+z_j$, in $O(d)$ operations, $d=\sum_j|\operatorname{supp}X_j|$.
--
--   The program also returns its **trace**: before each iteration, the current coin vector, the chosen pair, its ratio $\alpha/\beta$ and its $\beta$. Lemma 4 and SumMaximizer read the linear pieces of $\mathrm{prob}_X$ from it.
--
--   **Formalization Note** The program runs in the published operation counter `CapacitatedAssort.General.Work`; every arithmetic operation, comparison, read, write and loop dispatch is charged. The while loop has structural fuel $d+1$; since every iteration sets an entry equal to $1$ to $0$, it ends within $d$ iterations for $b\ge0$ (p.39), so the fuel is never exhausted. Snapshotting the coin vector for the trace is charged $d+2$.
-- source:
--   Abels–Pitschmann–Schewior–Schmand, Canada Retravelled (manuscript, STOC 2027 submission, sha256 8117348eb78ba082edf376778214fa414f31cb0cd8a8d06c12a1dfba627e3a33), Algorithm 2, p.9; proof of Lemma 8, pp.38–39; proof of Lemma 4, pp.10–11

import Mathlib
import Definitions.Def_CanadaCTP_PathOpt
import Definitions.Def_CapacitatedAssort_General_Work

namespace CanadaCTP

open CapacitatedAssort.General

/-! # PathExplorer, Algorithm 2

Abels–Pitschmann–Schewior–Schmand, *Canada Retravelled* (manuscript, sha256 8117348e…3a33),
Algorithm 2, p.9, implemented as in the proof of Lemma 8, pp.38–39, in the unit-cost operation
counter `CapacitatedAssort.General.Work`.

**Formalization Note.**
* Each iteration computes, in `O(d)` counted operations, `q_j = Σ_x P[X_j = x]·coin(j, x)`,
  `r_j = Σ_x P[X_j = x]·coin(j, x)·x`, the reach probabilities `pass_j = Π_{ℓ<j} q_ℓ`,
  `restProb(j) = Π_{ℓ>j} q_ℓ`, `z_j` with `restCost(j, x) = x + z_j`, and
  `expCost(coin) = Σ_j pass_j·r_j`. Then `α(j, x) = pass_j·P[X_j = x]·restProb(j)` and
  `β(j, x) = pass_j·P[X_j = x]·(x + z_j)`, the coefficients of Lemma 2.
* The arg min runs over the pairs with `coin(j, x) = 1` and `β > 0`; ties are broken by the
  lexicographic order on (edge index, support index): the scan keeps the first minimizer.
* The while loop has structural fuel `d + 1`: each iteration sets one entry equal to `1` to `0`,
  so for `b ≥ 0` the loop ends within `d` iterations (proof of Lemma 8, p.39) and the fuel is
  never exhausted.
* The final adjustment is `coin(j*, x*) = (b − b_{i+1})/(b_i − b_{i+1})` (p.39), after which the
  loop condition fails and the coin vector is returned.
* The output records, as ghost data, the trace of the run: before each iteration the current
  coin vector together with the chosen pair and its ratio `α/β` and `β` (used by Lemma 4 and by
  SumMaximizer). Snapshotting the vector is charged `d + 2`. -/

/-- A pair `(j, x)` of an edge and a support index. -/
abbrev PEPair {m : ℕ} (X : Fin m → EdgeDist) := Σ j : Fin m, Fin (X j).pts.length

/-- One trace entry: the strategy `coin_i` before iteration `i`, the pair `(j_i, x_i)` set to
`0` in that iteration, its ratio `α/β` and its `β`. -/
structure PEStep {m : ℕ} (X : Fin m → EdgeDist) where
  coin : Coin X
  pair : PEPair X
  ratio : ℝ
  beta : ℝ

/-- The output of PathExplorer: the coin vector and the trace of the run. -/
structure PEOut {m : ℕ} (X : Fin m → EdgeDist) where
  coin : Coin X
  trace : List (PEStep X)

/-- The per-edge statistics of a coin vector (indices are edge indices `0 … m−1`). -/
structure PathStats where
  q : ℕ → ℝ
  r : ℕ → ℝ
  pass : ℕ → ℝ
  rest : ℕ → ℝ
  z : ℕ → ℝ
  cost : ℝ

/-- The statistics of the proof of Lemma 8, in `O(d)` counted operations. -/
noncomputable def pathStats {m : ℕ} (X : Fin m → EdgeDist) (c : Coin X) : Work PathStats := do
  charge 1
  let mut q : ℕ → ℝ := fun _ => 0
  let mut r : ℕ → ℝ := fun _ => 0
  for j in List.finRange m do
    charge 3 -- dispatch, two initializations
    let mut qj : ℝ := 0
    let mut rj : ℝ := 0
    for x in List.finRange (X j).pts.length do
      charge 9 -- dispatch, three reads, three multiplications, two additions
      qj := qj + prb X j x * c j x
      rj := rj + prb X j x * c j x * val X j x
    charge 2 -- two writes
    q := Function.update q j.val qj
    r := Function.update r j.val rj
  let mut pass : ℕ → ℝ := fun _ => 0
  let mut acc : ℝ := 1
  let mut cost : ℝ := 0
  for j in List.range m do
    charge 7 -- dispatch, write, two reads, two multiplications, addition
    pass := Function.update pass j acc
    cost := cost + acc * r j
    acc := acc * q j
  let mut rest : ℕ → ℝ := fun _ => 0
  let mut z : ℕ → ℝ := fun _ => 0
  let mut rp : ℝ := 1
  let mut zz : ℝ := 0
  for j in (List.range m).reverse do
    charge 8 -- dispatch, two writes, two reads, two multiplications, addition
    rest := Function.update rest j rp
    z := Function.update z j zz
    zz := r j + q j * zz
    rp := q j * rp
  return ⟨q, r, pass, rest, z, cost⟩

/-- The arg min of Algorithm 2 over pairs with `coin(j, x) = 1` and `β(j, x, coin) > 0` of
`α/β`, ties to the lexicographically least pair. Returns `(α/β, β, (j, x))`. -/
noncomputable def argminPair {m : ℕ} (X : Fin m → EdgeDist) (c : Coin X) (st : PathStats) :
    Work (Option (ℝ × ℝ × PEPair X)) := do
  charge 1
  let mut best : Option (ℝ × ℝ × PEPair X) := none
  for j in List.finRange m do
    charge 1
    for x in List.finRange (X j).pts.length do
      charge 14 -- dispatch, reads, comparisons, six multiplications/additions, division, write
      if c j x = 1 then
        let a := st.pass j.val * prb X j x * st.rest j.val
        let be := st.pass j.val * prb X j x * (val X j x + st.z j.val)
        if 0 < be then
          match best with
          | none => best := some (a / be, be, ⟨j, x⟩)
          | some (r0, _, _) => if a / be < r0 then best := some (a / be, be, ⟨j, x⟩)
  return best

/-- The while loop of Algorithm 2 with fuel; `tr` is the trace so far, most recent first. -/
noncomputable def peLoop {m : ℕ} (X : Fin m → EdgeDist) (b : ℝ) :
    ℕ → Coin X → List (PEStep X) → Work (PEOut X)
  | 0, c, tr => do
      charge (tr.length + 1)
      return ⟨c, tr.reverse⟩
  | fuel + 1, c, tr => do
      let st ← pathStats X c
      charge 1 -- loop test `expCost(coin) > b`
      if st.cost ≤ b then
        charge (tr.length + 1)
        return ⟨c, tr.reverse⟩
      else
        let best ← argminPair X c st
        match best with
        | none =>
            charge (tr.length + 1)
            return ⟨c, tr.reverse⟩
        | some (ratio, be, p) =>
            charge (dX X + 2) -- snapshot of `coin` for the trace, cons
            let tr' := (⟨c, p, ratio, be⟩ : PEStep X) :: tr
            charge 1 -- `coin(j*, x*) = 0`
            let c0 := updC c p.1 p.2 0
            let st0 ← pathStats X c0
            charge 1 -- test `expCost(coin) < b`
            if st0.cost < b then
              charge (4 + tr'.length + 1) -- adjustment (three arithmetic operations, write)
              return ⟨updC c p.1 p.2 ((b - st0.cost) / (st.cost - st0.cost)), tr'.reverse⟩
            else peLoop X b fuel c0 tr'

/-- PathExplorer (Algorithm 2) on input `(X, b)`: initialize `coin ≡ 1`, then run the while
loop. -/
noncomputable def pathExplorer {m : ℕ} (X : Fin m → EdgeDist) (b : ℝ) : Work (PEOut X) := do
  charge (dX X + m + 1) -- initialization of every entry to `1`
  peLoop X b (dX X + 1) (fun _ _ => 1) []

/-- The coin vector `coin_X(b)` computed by PathExplorer. -/
noncomputable def peOut {m : ℕ} (X : Fin m → EdgeDist) (b : ℝ) : Coin X :=
  ((pathExplorer X b).run 0).1.coin

/-- The trace of PathExplorer's run on `(X, b)`. -/
noncomputable def peTrace {m : ℕ} (X : Fin m → EdgeDist) (b : ℝ) : List (PEStep X) :=
  ((pathExplorer X b).run 0).1.trace

/-- The number of counted operations of PathExplorer on `(X, b)`. -/
noncomputable def peOps {m : ℕ} (X : Fin m → EdgeDist) (b : ℝ) : ℕ :=
  ((pathExplorer X b).run 0).2

end CanadaCTP


