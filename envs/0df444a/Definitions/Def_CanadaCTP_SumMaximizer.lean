-- Prove2me | Definitions.Def_CanadaCTP_SumMaximizer
-- name    : CanadaCTP_SumMaximizer
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:20:45.247809+00:00
-- url     : https://prove2.me/theorems/254f421d-10d5-47bf-af09-d53b22f47379
-- title:
--   Algorithm 3 — SumMaximizer: steepest ascent over the linear segments of the $\mathrm{prob}_{X^i}$
-- statement:
--   **SumMaximizer** (Algorithm 3) splits a budget $b\ge0$ among $k$ paths $X^1,\dots,X^k$. For each path it runs PathExplorer on $(X^i,0)$ and reads off the linear segments of $\mathrm{prob}_{X^i}$ from the trace (Lemma 4): iteration $i$ gives the segment $[b_{i+1},b_i]$ of length $\beta(j_i,x_i,\mathrm{coin}_i)$ and slope $\alpha/\beta$; the last segment is the constant $1$, of infinite length and slope $0$. Starting from $b_i=0$, it repeatedly gives budget to the path whose current segment is steepest (ties to the least path index): a whole segment if it fits into the remaining budget, otherwise the remaining budget.
--
--   The order of the paths is a binary heap keyed by the slope of the current segment, so each update costs $O(\log k)$ operations.
--
--   This is the MaxSum solver used in every phase of ParallelTraveller.
--
--   **Formalization Note** The program runs in `CapacitatedAssort.General.Work`. The heap is built by bottom-up sift-downs. The sift-down has fuel $\lfloor\log_2k\rfloor+1$ (the heap depth), and the main loop has fuel equal to the number of finite segments plus one, since each pass removes a finite segment or ends the loop. Neither fuel is ever exhausted.
-- source:
--   Abels–Pitschmann–Schewior–Schmand, Canada Retravelled (manuscript, STOC 2027 submission, sha256 8117348eb78ba082edf376778214fa414f31cb0cd8a8d06c12a1dfba627e3a33), Definition 3, p.6; Algorithm 3, p.15; proof of Lemma 9, pp.39–40

import Mathlib
import Definitions.Def_CanadaCTP_PathExplorer

namespace CanadaCTP

open CapacitatedAssort.General

/-! # SumMaximizer, Algorithm 3, and the MaxSum problem

Abels–Pitschmann–Schewior–Schmand, *Canada Retravelled* (manuscript, sha256 8117348e…3a33),
Definition 3 (p.6), Algorithm 3 (p.15), the running-time argument of Lemma 9 (pp.39–40).

**Formalization Note.**
* The linear segments of `prob_{Xⁱ}` come from the trace of PathExplorer on `(Xⁱ, 0)`
  (Lemma 4, proof of Lemma 9): iteration `i` gives the segment `[b_{i+1}, b_i]` of length
  `β(j_i, x_i, coin_i) = b_i − b_{i+1}` and slope `α/β`; listed from budget `0` upwards. After the
  last finite segment comes the constant-`1` segment of infinite length and slope `0`, which is
  represented by the empty list.
* The order `π` of the lists is a binary max-heap of the path indices keyed by the slope of the
  current first segment, ties to the least path index; "update `π`" is one sift-down from the
  root, `O(log k)` counted operations. The heap is built by bottom-up sift-downs.
* Loops have structural fuel: the sift-down `⌊log₂ k⌋ + 1` (the heap depth), the while loop the
  total number of finite segments `+ 1` (each pass either removes a finite segment or ends the
  loop). Neither fuel is ever exhausted. -/

/-- The slope of the current first segment of path `i` (`0` for the final constant segment). -/
def headSlope (segs : ℕ → List (ℝ × ℝ)) (i : ℕ) : ℝ :=
  match segs i with
  | [] => 0
  | s :: _ => s.2

/-- `i` comes before `i'` in the order `π`: steeper first segment, ties to the smaller index. -/
abbrev precedes (segs : ℕ → List (ℝ × ℝ)) (i i' : ℕ) : Prop :=
  headSlope segs i' < headSlope segs i ∨ (headSlope segs i = headSlope segs i' ∧ i < i')

/-- Sift-down in a binary heap `h` (positions `0 … k−1`) from position `p`. -/
noncomputable def siftDown (k : ℕ) (segs : ℕ → List (ℝ × ℝ)) :
    ℕ → (ℕ → ℕ) → ℕ → Work (ℕ → ℕ)
  | 0, h, _ => return h
  | fuel + 1, h, p => do
      charge 14 -- index arithmetic, four reads, two comparisons of keys, swap
      let l := 2 * p + 1
      let r := 2 * p + 2
      let b1 := if l < k ∧ precedes segs (h l) (h p) then l else p
      let b2 := if r < k ∧ precedes segs (h r) (h b1) then r else b1
      if b2 = p then return h
      else
        let h' : ℕ → ℕ := fun q => if q = p then h b2 else if q = b2 then h p else h q
        siftDown k segs fuel h' b2

/-- The while loop of Algorithm 3: `bud` are the budgets `b_i`, `b` the remaining budget. -/
noncomputable def smLoop (k : ℕ) :
    ℕ → (ℕ → List (ℝ × ℝ)) → (ℕ → ℕ) → (ℕ → ℝ) → ℝ → Work (ℕ → ℝ)
  | 0, _, _, bud, _ => return bud
  | fuel + 1, segs, h, bud, b => do
      charge 2 -- loop test `b > 0`
      if b ≤ 0 ∨ k = 0 then return bud
      else
        charge 3 -- read `π(1)`, read its first segment
        let i := h 0
        match segs i with
        | [] =>
            charge 3 -- `length = ∞ > b`: `b_{π(1)} += b`, loop ends
            return Function.update bud i (bud i + b)
        | (len, _) :: rest =>
            charge 1 -- `length ≤ b`
            if len ≤ b then
              charge 4 -- `b_{π(1)} += length`, remove the segment, `b -= length`
              let segs' := Function.update segs i rest
              let h' ← siftDown k segs' (Nat.log 2 k + 1) h 0
              smLoop k fuel segs' h' (Function.update bud i (bud i + len)) (b - len)
            else
              charge 3
              return Function.update bud i (bud i + b)

/-- SumMaximizer (Algorithm 3) on paths `Xs i = ⟨m_i, Xⁱ⟩` and budget `b`. -/
noncomputable def sumMaximizer {k : ℕ} (Xs : Fin k → Σ m : ℕ, (Fin m → EdgeDist)) (b : ℝ) :
    Work (Fin k → ℝ) := do
  charge (k + 1) -- `b_i = 0`
  let mut segs : ℕ → List (ℝ × ℝ) := fun _ => []
  let mut total : ℕ := 0
  for i in List.finRange k do
    charge 3
    let out ← pathExplorer (Xs i).2 0
    charge (2 * out.trace.length + 2) -- read off the segments, reverse
    let sg := (out.trace.map fun s => (s.beta, s.ratio)).reverse
    segs := Function.update segs i.val sg
    total := total + sg.length
  charge (k + 1) -- the heap array
  let mut h : ℕ → ℕ := id
  for p in (List.range (k / 2)).reverse do
    charge 1
    h ← siftDown k segs (Nat.log 2 k + 1) h p
  let bud ← smLoop k (total + 1) segs h (fun _ => 0) b
  charge (k + 1) -- output
  return fun i => bud i.val

end CanadaCTP


