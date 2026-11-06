-- Prove2me | Definitions.Def_CanadaCTP_ParallelTraveller
-- name    : CanadaCTP_ParallelTraveller
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:21:33.821032+00:00
-- url     : https://prove2.me/theorems/c9f1f6b9-6925-45a8-a717-23606621d062
-- title:
--   Algorithm 1 — the ParallelTraveller policy, with its operation counter
-- statement:
--   **ParallelTraveller** (Algorithm 1) is a randomized adaptive policy for a CTP instance.
--
--   1. *Preprocessing.* For each path in turn, walk towards $t$ while the next edge has weight $0$. If $t$ is reached, the run ends; otherwise walk back to $s$ at cost $0$.
--   2. *Phase $\ell=0,1,2,\dots$.* At $s$, form the updated weights $X^{i,\ell}$ (Definition 4: every revealed edge becomes the point mass at its observed weight, every other edge keeps its distribution). Run SumMaximizer with budget $2^\ell\mu$ to get budgets $b_i$, and PathExplorer on $(X^{i,\ell},b_i)$ for every path. Then, for $i=1,\dots,k$: run the coin strategy of path $i$; if it reaches $t$, the run ends; otherwise walk back to $s$ and take the next path.
--
--   The policy's memory holds its control state, the plan of the current phase, and a counter `ops` of the operations it has performed: every step adds its own counted operations. Its **phase** is $-1$ during the preprocessing and $\ell$ during phase $\ell$.
--
--   This is the algorithm of Theorem 1 and Theorem 3.
--
--   **Formalization Note** The paper rescales all weights by $1/\mu$ and uses budget $2^\ell$. Here the weights are kept and the budget is $2^\ell\mu$. PathExplorer and SumMaximizer commute with a common positive rescaling of values and budget, so the moves are identical. The plan of a phase is computed once, at its first step. Bookkeeping transitions are steps with the move "wait" (cost $0$).
-- source:
--   Abels–Pitschmann–Schewior–Schmand, Canada Retravelled (manuscript, STOC 2027 submission, sha256 8117348eb78ba082edf376778214fa414f31cb0cd8a8d06c12a1dfba627e3a33), Algorithm 1, p.7; Definition 4, p.6; proof of Theorem 3, pp.15–16

import Mathlib
import Definitions.Def_CanadaCTP_SumMaximizer

namespace CanadaCTP

open CapacitatedAssort.General

/-! # ParallelTraveller, Algorithm 1

Abels–Pitschmann–Schewior–Schmand, *Canada Retravelled* (manuscript, sha256 8117348e…3a33),
Algorithm 1, p.7, with Definition 4 (p.6) and the rescaling of the preprocessing.

**Formalization Note.**
* The algorithm is a policy in the sense of `CanadaCTP.Policy`: its memory is a control state
  (`PTCore`) plus the operation counter `ops`. Each step performs at most one move; a step's own
  counted operations (`Work`) are added to `ops`, and nothing else touches `ops`.
* Rescaling. The paper divides every weight by `μ` (the least non-zero realization) and uses
  budget `2^ℓ` in phase `ℓ`; here the weights are kept and phase `ℓ` uses budget `2^ℓ·μ`. Both
  PathExplorer and SumMaximizer commute with a common positive rescaling of all values and the
  budget (all costs scale by `μ`, all ratios by `1/μ`, the order of ratios and every tie is
  unchanged), so the moves are the same. `2^ℓ·μ` is computed by doubling.
* Preprocessing. For `i = 0, …, k−1` in order: walk forward on path `i` while the next edge has
  revealed weight `0`; on reaching `t` the run ends; otherwise walk back to `s` (cost `0`) and
  take the next path.
* Phase `ℓ`. At `s`, in one step, build `X^{i,ℓ}` (Definition 4: every revealed edge becomes the
  point mass at its observed weight, every other edge keeps its distribution), run SumMaximizer
  with budget `2^ℓ·μ` and PathExplorer on `(X^{i,ℓ}, bᵢ)` for every path, and store the coins.
  Then for `i = 0, …, k−1`: at vertex `j` of path `i`, with edge `j` revealed as `w`, traverse
  edge `j` with probability `coinᵢ(j, index of w)`; on failure walk back to `s` and take path
  `i + 1`; after path `k − 1` start phase `ℓ + 1`. Reaching `t` ends the run.
* Bookkeeping transitions (next path, next phase) are steps with the move `wait` (cost `0`).
* `phase` is `−1` during the preprocessing and `ℓ` during phase `ℓ`. -/

/-- The control state of ParallelTraveller. -/
inductive PTMode where
  | start
  | pre (i : ℕ) (back : Bool)
  | plan (ℓ : ℕ)
  | go (ℓ : ℕ) (i : ℕ)
  | back (ℓ : ℕ) (i : ℕ)

/-- The core memory: control state, `μ`, the current phase budget `2^ℓ·μ`, and the plan of the
current phase (the updated distributions `X^{i,ℓ}` and the coins, support indices as `ℕ`). -/
structure PTCore (I : Inst) where
  mode : PTMode
  mu : ℝ
  budget : ℝ
  pd : (i : Fin I.k) → Fin (I.m i) → EdgeDist
  pc : (i : Fin I.k) → Fin (I.m i) → ℕ → ℝ

/-- The phase of a control state: `−1` before phase `0`. -/
def PTCore.phase {I : Inst} (c : PTCore I) : ℤ :=
  match c.mode with
  | PTMode.start => -1
  | PTMode.pre _ _ => -1
  | PTMode.plan ℓ => ℓ
  | PTMode.go ℓ _ => ℓ
  | PTMode.back ℓ _ => ℓ

/-- The memory of ParallelTraveller: control state and counted operations so far. -/
structure PTMem (I : Inst) where
  core : PTCore I
  ops : ℕ

/-- The point mass at `max v 0` (revealed weights are `≥ 0`, so this is the point mass at the
observed weight). -/
def pointDist (v : ℝ) : EdgeDist where
  pts := [(max v 0, 1)]
  nodup := by simp
  val_nonneg := by simp
  prob_pos := by simp
  sum_one := by simp

/-- `X^{i,ℓ}` of Definition 4: the distributions updated with respect to the observations. -/
def updated (I : Inst) (o : Obs I) (i : Fin I.k) (j : Fin (I.m i)) : EdgeDist :=
  match o.rev i j with
  | none => I.X i j
  | some v => pointDist v

/-- The vertex index of the traveller on path `i` (`0` at `s`), if it is on path `i`. -/
def curV (I : Inst) (i : Fin I.k) : Pos I → Option ℕ
  | Pos.s => some 0
  | Pos.mid i' v => if i' = i then some v else none
  | Pos.t => none

/-- The rescaling factor `μ`, computed by one scan of all supports. -/
noncomputable def computeMu (I : Inst) : Work ℝ := do
  charge 1
  let mut best : Option ℝ := none
  for i in List.finRange I.k do
    charge 1
    for j in List.finRange (I.m i) do
      charge 1
      for p in (I.X i j).pts do
        charge 4 -- dispatch, read, two comparisons
        if p.1 ≠ 0 then
          match best with
          | none => best := some p.1
          | some b0 => if p.1 < b0 then best := some p.1
  return best.getD 1

/-- Linear search of a value in a support. -/
noncomputable def findIdx (D : EdgeDist) (v : ℝ) : Work (Option (Fin D.pts.length)) := do
  charge (2 * D.pts.length + 1)
  return idxOf D v

/-- A coin vector with support indices read as natural numbers (`0` out of range). -/
def coinNat {m : ℕ} {X : Fin m → EdgeDist} (c : Coin X) : Fin m → ℕ → ℝ :=
  fun j n => if h : n < (X j).pts.length then c j ⟨n, h⟩ else 0

/-- The plan of phase `ℓ` (computed once, at its first step): `X^{i,ℓ}`, SumMaximizer with the
phase budget, PathExplorer on every path with its share. -/
noncomputable def ptPlan (I : Inst) (o : Obs I) (budget : ℝ) :
    Work (((i : Fin I.k) → Fin (I.m i) → EdgeDist) × ((i : Fin I.k) → Fin (I.m i) → ℕ → ℝ)) := do
  charge (∑ i, dsz I i + nE I + I.k + 1) -- build `X^{i,ℓ}`
  let Y := updated I o
  let bud ← sumMaximizer (fun i => (⟨I.m i, Y i⟩ : Σ m : ℕ, (Fin m → EdgeDist))) budget
  let mut pc : (i : Fin I.k) → Fin (I.m i) → ℕ → ℝ := fun _ _ _ => 0
  for i in List.finRange I.k do
    charge 2
    let out ← pathExplorer (Y i) (bud i)
    charge (dX (Y i) + 1) -- store the coins
    pc := Function.update pc i (coinNat out.coin)
  return (Y, pc)

/-- One step of ParallelTraveller from control state `c` and observation `o`: the distribution
of (move, next control state), computed in `Work`. -/
noncomputable def ptStep (I : Inst) (c : PTCore I) (o : Obs I) :
    Work (PMF (Move I × PTCore I)) :=
  match c.mode with
  | PTMode.start => do
      let μ ← computeMu I
      charge 1
      return PMF.pure (Move.wait, { c with mode := PTMode.pre 0 false, mu := μ })
  | PTMode.pre i false => do
      charge 6
      if h : i < I.k then
        match curV I ⟨i, h⟩ o.pos with
        | none => return PMF.pure (Move.wait, c)
        | some v =>
            let r : Option ℝ := if hv : v < I.m ⟨i, h⟩ then o.rev ⟨i, h⟩ ⟨v, hv⟩ else none
            if r = some 0 then return PMF.pure (Move.fwd ⟨i, h⟩, c)
            else if v = 0 then
              return PMF.pure (Move.wait, { c with mode := PTMode.pre (i + 1) false })
            else return PMF.pure (Move.bwd, { c with mode := PTMode.pre i true })
      else
        return PMF.pure (Move.wait, { c with mode := PTMode.plan 0, budget := c.mu })
  | PTMode.pre i true => do
      charge 2
      if o.pos = Pos.s then
        return PMF.pure (Move.wait, { c with mode := PTMode.pre (i + 1) false })
      else return PMF.pure (Move.bwd, c)
  | PTMode.plan ℓ => do
      let p ← ptPlan I o c.budget
      charge 2
      return PMF.pure (Move.wait, { c with mode := PTMode.go ℓ 0, pd := p.1, pc := p.2 })
  | PTMode.go ℓ i => do
      charge 4
      if h : i < I.k then
        match curV I ⟨i, h⟩ o.pos with
        | none => return PMF.pure (Move.wait, c)
        | some v =>
            if hv : v < I.m ⟨i, h⟩ then
              match o.rev ⟨i, h⟩ ⟨v, hv⟩ with
              | none => return PMF.pure (Move.wait, c)
              | some w => do
                  let x ← findIdx (c.pd ⟨i, h⟩ ⟨v, hv⟩) w
                  let p : ℝ := match x with
                    | some x => c.pc ⟨i, h⟩ ⟨v, hv⟩ x.val
                    | none => 0
                  charge 4 -- read the coin, flip, branch
                  return (coinFlip p).map fun b =>
                    if b then (Move.fwd ⟨i, h⟩, c)
                    else if v = 0 then (Move.wait, { c with mode := PTMode.go ℓ (i + 1) })
                    else (Move.bwd, { c with mode := PTMode.back ℓ i })
            else return PMF.pure (Move.wait, c)
      else
        charge 2 -- double the budget
        return PMF.pure (Move.wait,
          { c with mode := PTMode.plan (ℓ + 1), budget := 2 * c.budget })
  | PTMode.back ℓ i => do
      charge 2
      if o.pos = Pos.s then
        return PMF.pure (Move.wait, { c with mode := PTMode.go ℓ (i + 1) })
      else return PMF.pure (Move.bwd, c)

/-- The initial control state. -/
def ptInit (I : Inst) : PTCore I :=
  { mode := PTMode.start, mu := 1, budget := 1, pd := I.X, pc := fun _ _ _ => 0 }

/-- The ParallelTraveller policy (Algorithm 1). The step's counted operations are added to
`ops`. -/
noncomputable def ptPolicy (I : Inst) : Policy I (PTMem I) where
  init := ⟨ptInit I, 0⟩
  step := fun mem o =>
    let r := (ptStep I mem.core o).run 0
    r.1.map fun mc => (mc.1, (⟨mc.2, mem.ops + r.2⟩ : PTMem I))

end CanadaCTP


