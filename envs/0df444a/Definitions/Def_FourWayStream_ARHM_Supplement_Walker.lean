-- Prove2me | Definitions.Def_FourWayStream_ARHM_Supplement_Walker
-- name    : FourWayStream_ARHM_Supplement_Walker
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T08:00:44.435624+00:00
-- url     : https://prove2.me/theorems/836f7278-3f41-4cca-ae93-df6b2d95f13b
-- title:
--   §7.4, Appendix E.2 — path-following walkers, the walker algorithm of Theorem 7.11, the Poisson tail
-- statement:
--   **Walker.** A walker stores a start vertex $s$, a current vertex $c$, a previous vertex $p\in[n]\cup\{\bot\}$, a step counter $\ell$ and a flag. It starts with $c=s$, $p=\bot$, $\ell=0$, and processes each arriving edge $\{x,y\}$:
--   - if $c=x$ and $y\ne p$, it sets $p\leftarrow x$, $c\leftarrow y$, $\ell\leftarrow\ell+1$, and symmetrically if $c=y$ and $x\ne p$;
--   - if it has just moved and now $c=s$, it closes with length $\ell$ and ignores the rest of the stream.
--
--   **Graph shapes.** A graph has maximum degree two if it has no loops and every vertex lies in at most two edges. A cycle of length $L\ge3$ is an injective labeling $c_0,\dots,c_{L-1}$ (indices mod $L$) with every $\{c_i,c_{i+1}\}$ an edge; a path component is an injective labeling with consecutive pairs as edges and no other edge at its vertices.
--
--   **Walker algorithm.** For $h\ge0$, run $h$ walkers from independent uniform starts, with counters stopped at $2k$, and answer "$k$-cycles" iff some walker has closed after exactly $k$ steps; otherwise answer "$2k$-cycles". For $h=0$ it always answers "$2k$-cycles" and stores nothing.
--
--   **Poisson tail.** For $R>0$, $\mathbb P[\mathrm{Pois}(R)<k]=e^{-R}\sum_{j<k}R^j/j!$.
--
--   These objects state Lemmas E.2, E.3 and Theorem 7.11.
--
--   **Formalization Note** The walker of Lemmas E.2–E.3 has an unbounded counter. The algorithm's state is the tuple of $h$ capped walkers (start, current, previous, counter in $\{0,\dots,2k\}$, flag); its transitions are deterministic and do not depend on the stage.
-- source:
--   Nadezhda Voronova, STOC 2027 submission #1371 (October 2026), §7.4, p.37; Theorem 7.11, p.37; Appendix E.2, p.49

import Mathlib
import Definitions.Def_FourWayStream_ARHM_Supplement_NGC

set_option autoImplicit false

/-!
# Path-following walkers, the walker algorithm for repeated NGC, the Poisson tail

Nadezhda Voronova, *Four Ways to Stream*, STOC 2027 submission #1371 (October 2026): §7.4 (p.37),
Theorem 7.11 (p.37), Appendix E.2 (p.49).

A walker stores a start `s`, a current vertex `c`, a previous vertex `p ∈ [n] ∪ {⊥}`, a step counter
`ℓ` and a flag. It starts with `c = s`, `p = ⊥`, `ℓ = 0`; on an arriving edge `{x, y}` it moves
(`p ← x`, `c ← y`, `ℓ ← ℓ + 1`) if `c = x` and `y ≠ p`, symmetrically if `c = y` and `x ≠ p`; if it has
just moved and now `c = s`, it closes with length `ℓ` and ignores the rest of the stream.

`Walker n` is this walker with an unbounded counter (used in Lemmas E.2, E.3). The algorithm of
Theorem 7.11 runs `h` walkers whose counters stop at `2k` ("for NGC, `ℓ` is bounded by `2k` and
counters may stop there"): its state set is `Fin h → BState n k`, its initial distribution draws the
`h` starts independently and uniformly, its transitions are deterministic and stage-independent, and
it answers "`k`-cycles" (output `false`) iff some walker has closed with `ℓ = k`; otherwise it
answers "`2k`-cycles" (output `true`). With `h = 0` there are no walkers and it always answers
`2k`-cycles.
-/

noncomputable section
open Classical

namespace FourWayStream.ARHM.Supplement

/-! ### The walker -/

/-- A walker on the vertex set `Fin n`: start, current, previous (`none` = `⊥`), steps, closed. -/
structure Walker (n : ℕ) where
  start : Fin n
  cur : Fin n
  prev : Option (Fin n)
  steps : ℕ
  closed : Bool

namespace Walker

variable {n : ℕ}

/-- The walker started at `s`: `c = s`, `p = ⊥`, `ℓ = 0`, not closed. -/
def init (s : Fin n) : Walker n := ⟨s, s, none, 0, false⟩

/-- Move from `x` (the current vertex) to `y`, closing if `y` is the start. -/
def moveTo (W : Walker n) (x y : Fin n) : Walker n :=
  ⟨W.start, y, some x, W.steps + 1, decide (y = W.start)⟩

/-- Process the edge `{x, y}` given as an ordered pair. -/
def stepXY (W : Walker n) (x y : Fin n) : Walker n :=
  if W.closed = true then W
  else if W.cur = x ∧ W.prev ≠ some y then W.moveTo x y
  else if W.cur = y ∧ W.prev ≠ some x then W.moveTo y x
  else W

theorem stepXY_comm (W : Walker n) (x y : Fin n) : W.stepXY x y = W.stepXY y x := by
  unfold stepXY
  by_cases h1 : W.closed = true
  · simp [h1]
  · by_cases hxy : x = y
    · subst hxy; rfl
    · by_cases hx : W.cur = x
      · have hy : W.cur ≠ y := fun h => hxy (hx.symm.trans h)
        simp [h1, hy]
      · simp [h1, hx]

/-- Process the (undirected) edge `e`. -/
def step (W : Walker n) (e : Sym2 (Fin n)) : Walker n :=
  Sym2.lift ⟨fun x y => W.stepXY x y, fun x y => W.stepXY_comm x y⟩ e

end Walker

/-- The walker started at `s` after the edge sequence `str`. -/
def walk {n : ℕ} (s : Fin n) (str : List (Sym2 (Fin n))) : Walker n :=
  str.foldl Walker.step (Walker.init s)

/-! ### Graph shapes for Lemma E.2 -/

/-- A graph of maximum degree two: no loops, every vertex in at most two edges. -/
def MaxDegTwo {n : ℕ} (E : Finset (Sym2 (Fin n))) : Prop :=
  (∀ e ∈ E, ¬ e.IsDiag) ∧ ∀ v : Fin n, (E.filter (fun e => v ∈ e)).card ≤ 2

/-- `cyc : ZMod L → Fin n` is a cycle of length `L ≥ 3` of `E`: injective, with every edge
`{cyc i, cyc (i + 1)}` in `E`. -/
def IsCycleOf {n : ℕ} (E : Finset (Sym2 (Fin n))) (L : ℕ) (cyc : ZMod L → Fin n) : Prop :=
  3 ≤ L ∧ Function.Injective cyc ∧ ∀ i : ZMod L, s(cyc i, cyc (i + 1)) ∈ E

/-- `pth : Fin P → Fin n` is a path component of `E`: injective, its consecutive pairs are edges of
`E`, and every edge of `E` at a vertex of `pth` is one of these pairs. -/
def IsPathComponentOf {n : ℕ} (E : Finset (Sym2 (Fin n))) (P : ℕ) (pth : Fin P → Fin n) : Prop :=
  Function.Injective pth ∧
    (∀ i j : Fin P, j.val = i.val + 1 → s(pth i, pth j) ∈ E) ∧
    ∀ e ∈ E, ∀ i : Fin P, pth i ∈ e → ∃ a b : Fin P, b.val = a.val + 1 ∧ e = s(pth a, pth b)

/-- The vertex of the cycle `cyc` reached after `j` moves from `cyc 0` in direction `dir` (`true`:
increasing index). -/
def cycPos {n L : ℕ} (cyc : ZMod L → Fin n) (dir : Bool) (j : ℕ) : Fin n :=
  cyc (if dir then (j : ZMod L) else -(j : ZMod L))

/-! ### The Poisson tail -/

/-- `P[Pois(R) < k] = e^{−R} Σ_{j < k} R^j / j!`, for a Poisson variable of mean `R`. -/
def poissonLT (R : ℝ) (k : ℕ) : ℝ :=
  Real.exp (-R) * ∑ j ∈ Finset.range k, R ^ j / (j.factorial : ℝ)

/-! ### The walker algorithm of Theorem 7.11 -/

/-- A walker with counter capped at `2k`: `(start, cur, prev, steps, closed)`. -/
abbrev BState (n k : ℕ) := Fin n × Fin n × Option (Fin n) × Fin (2 * k + 1) × Bool

/-- Forget the cap. -/
def BState.toWalker {n k : ℕ} (b : BState n k) : Walker n :=
  ⟨b.1, b.2.1, b.2.2.1, b.2.2.2.1.val, b.2.2.2.2⟩

/-- Store a walker, its counter stopped at `2k`. -/
def BState.ofWalker {n k : ℕ} (W : Walker n) : BState n k :=
  (W.start, W.cur, W.prev, ⟨min W.steps (2 * k), by omega⟩, W.closed)

/-- One step of a capped walker. -/
def BState.step {n k : ℕ} (b : BState n k) (e : Sym2 (Fin n)) : BState n k :=
  BState.ofWalker (b.toWalker.step e)

/-- Theorem 7.11, part 1: the algorithm running `h` walkers from independent uniform starts, with
counters stopped at `2k`, answering "`k`-cycles" (`false`) iff some walker closed after exactly `k`
steps. -/
def walkerAlg (n k h : ℕ) : CEdgeAlg (Fin n) (Fin h → BState n k) where
  init := fun st => if ∀ i, st i = BState.ofWalker (Walker.init (st i).1) then ((n : ℝ) ^ h)⁻¹
    else 0
  trans := fun _ e a b => if b = (fun i => (a i).step e) then 1 else 0
  dec := fun a b => if b = decide (¬ ∃ i, (a i).2.2.2.2 = true ∧ (a i).2.2.2.1.val = k) then 1
    else 0

end FourWayStream.ARHM.Supplement


