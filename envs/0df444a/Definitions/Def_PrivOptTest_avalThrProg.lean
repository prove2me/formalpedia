-- Prove2me | Definitions.Def_PrivOptTest_avalThrProg
-- name    : PrivOptTest_avalThrProg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:59:07.724204+00:00
-- url     : https://prove2.me/theorems/cdb0c85a-5f5a-4b43-bba9-24e99eee78b9
-- title:
--   The charged program of Algorithm 2 (the time clause of Theorem 1.3)
-- statement:
--   An explicit program in the state monad over a tick counter. One tick is charged per real arithmetic operation, comparison, logarithm, ceiling, bit operation, array read or write and coin read; a shift by $s$ bits costs $s+1$. The domain is a sorted random-access array of reals, the datasets are arrays of reals, and the coins are random-access read-only tapes (the noise of every pass, the two final Laplace samples, and the public hash of every pass, which is never written out). The program computes $b$ and $T$ by doubling, ranks records by binary search, lifts and sorts them, runs the binary search through Algorithm 1 on the prefix datasets, and computes the final statistics by maxima over occupied nodes only.
--
--   `avalThrResult` is the trace and output of the protocol of Theorem 3.12 on given coins, and `tapeOf` reads the protocol's own coins as tapes.
--
--   **Formalization Note** The program uses only the listed charged primitives and a constant number of uncharged helpers of constant size; it does not call the protocol. Maxima over occupied nodes equal the maxima over all of $\{0,1\}^L$ or $\{0,1\}^H$ (an empty node never exceeds an occupied neighbour), which is what makes a bound in $\log m$ possible.
-- source:
--   M. Haghifam, K. K. Patel, A. Blum, G. Fanti, J. Ziani, Should We Combine Our Data? Algorithms and Limits for Privately Assessing Data Sharing, arXiv:2611.03599 (manuscript sha256 4ac94dcf…), Theorem 1.3, p.4; Algorithm 2, p.20; §1.4.2, p.9

import Mathlib
import Definitions.Def_PrivOptTest_algo2

namespace PrivOptTest

/-- The charged machine of the time clause of Theorem 1.3 (arXiv:2611.03599, manuscript sha256
4ac94dcf…, p.4): programs carry a tick counter. -/
abbrev Prog := StateM ℕ

/-- Charge `c` ticks. One tick per real operation, comparison, `ln`, `⌈·⌉`, bit, memory read or write
and coin read. A shift of a record by `s` bits costs `s + 1`. -/
def tick (c : ℕ := 1) : Prog Unit := modify (· + c)

/-- Random-access read-only coin tapes: the noise of each pass, the two `Lap(28/ε)` samples, and the
hash of each pass, read at one tick per entry. The hash table is not written out. -/
structure CoinTape (K : Type) where
  noiseA : ℕ → ℕ → K
  noiseB : ℕ → ℕ → K
  lapA : K
  lapB : K
  hash : ℕ → ℕ → ℕ

/-- What the program returns: the messages in order, each as a scalar and the released entries of a
vector, and the common output. -/
structure ProgResult (K : Type) where
  msgs : List (K × List K)
  out : Outcome

section Prog

variable {K : Type} [Field K] [LinearOrder K] [FloorRing K]

/-- `⌈log₂ m⌉` by repeated doubling, starting from `c = 0`, `p = 1`. The first argument is fuel and is
not charged. -/
def clogProg (m : ℕ) : ℕ → ℕ → ℕ → Prog ℕ
  | 0, c, _ => pure c
  | f + 1, c, p => do
    tick 2
    if m ≤ p then pure c else clogProg m f (c + 1) (2 * p)

/-- Binary search for the rank of `x` in the sorted domain array. The first argument is fuel. -/
def rankProg (dom : Array K) (x : K) : ℕ → ℕ → ℕ → Prog ℕ
  | 0, lo, _ => pure lo
  | f + 1, lo, hi => do
    tick 4
    if hi - lo ≤ 1 then pure lo
    else
      let mid := (lo + hi) / 2
      if dom.getD mid 0 ≤ x then rankProg dom x f mid hi else rankProg dom x f lo mid

/-- Insert `x` in a sorted list, one tick per element passed. -/
def insertProg (x : ℕ) : List ℕ → Prog (List ℕ)
  | [] => do tick; pure [x]
  | y :: ys => do
    tick
    if x ≤ y then pure (x :: y :: ys)
    else do
      let zs ← insertProg x ys
      pure (y :: zs)

/-- Insertion sort, charged per comparison. -/
def sortProg : List ℕ → Prog (List ℕ)
  | [] => pure []
  | x :: xs => do
    let ys ← sortProg xs
    insertProg x ys

/-- `prefix_ℓ(x)`: a shift by `b − ℓ` bits. -/
def prefixProg (b ℓ x : ℕ) : Prog ℕ := do
  tick (b - ℓ + 1)
  pure (prefixOf b ℓ x)

/-- The number of elements of `l` with `f x`, one tick per element, `f` a single comparison. -/
def countProg (f : ℕ → Bool) : List ℕ → Prog ℕ
  | [] => pure 0
  | x :: xs => do
    tick
    let c ← countProg f xs
    pure (if f x then c + 1 else c)

/-- A party's rank-and-lift step, then its block: `bit = 1` and the `k` largest for Alice, `bit = 0` and
the `k` smallest for Bob. -/
def encodeProg (dom : Array K) (S : List K) (bit k : ℕ) (up : Bool) : Prog (List ℕ) := do
  let lifted ← S.mapM fun x => do
    let r ← rankProg dom x (dom.size + 1) 0 dom.size
    tick 2
    pure (2 * r + bit)
  let sorted ← sortProg lifted
  tick (S.length + 1)
  pure (if up then sorted.drop (S.length - k) else sorted.take k)

/-- One party's release in a pass at depth `ℓ` (Algorithm 1, lines 1–7, on the prefix dataset). -/
def releaseProg (P : Params K) (ℓ : ℕ) (recs : List ℕ) (g : ℕ → ℕ) (noise : ℕ → K) :
    Prog (List K) := do
  tick (ℓ + 2)
  let u := 2 ^ ℓ
  let pre ← recs.mapM (prefixProg P.b ℓ)
  let hs ← pre.mapM fun x => do
    tick 2
    pure (pcfHash u P.Rbar g x)
  (List.range (pcfBuckets u P.Rbar)).mapM fun z => do
    let c ← countProg (fun y => y == z) hs
    tick 3
    pure ((c : K) + noise z)

/-- Running maximum of the `min` of two release lists (Algorithm 1, line 8). -/
def maxMinProg : K → List K → List K → Prog K
  | cur, x :: xs, y :: ys => do
    tick 3
    maxMinProg (max cur (min x y)) xs ys
  | cur, _, _ => pure cur

/-- Algorithm 1, line 8, on two release lists. -/
def estimateProg (a b : List K) : Prog K :=
  match a, b with
  | x :: xs, y :: ys => do
    tick
    maxMinProg (min x y) xs ys
  | _, _ => pure 0

/-- The binary search (Algorithm 2, lines 4–11). The first argument is fuel. Messages accumulate in
reverse. -/
def searchProg (P : Params K) (A B : List ℕ) (c : CoinTape K) :
    ℕ → ℕ → SearchState K → List (K × List K) → Prog (SearchState K × List (K × List K))
  | 0, _, s, ms => pure (s, ms)
  | f + 1, i, s, ms => do
    tick 3
    if 1 < s.H - s.L then
      let ℓ := (s.L + s.H) / 2
      tick 2
      let a ← releaseProg P ℓ A (c.hash i) (c.noiseA i)
      let b ← releaseProg P ℓ B (c.hash i) (c.noiseB i)
      let e ← estimateProg a b
      tick 4
      let F := (P.k : K) - e
      let s' : SearchState K :=
        if F < P.α then { s with L := ℓ, FL := F } else { s with H := ℓ, FH := F }
      searchProg P A B c f (i + 1) s' ((0, b) :: (0, a) :: ms)
    else pure (s, ms)

/-- The maximum over occupied nodes of `6|A^L_p| + |A^{L+1}_{pj}|`. Empty nodes have value 0, so with
data present the maximum over all of `{0,1}^L` is attained at an occupied node. -/
def jumpMaxProg (j : ℕ) (pL pH : List ℕ) : Prog ℕ :=
  pL.foldlM (fun best p => do
    let c ← countProg (fun y => y == p) pL
    let d ← countProg (fun y => y == 2 * p + j) pH
    tick 4
    pure (max best (6 * c + d))) 0

/-- The maximum over occupied nodes `p` of `6|A^H_p| + Σ_{q<p} |A^H_q|` (`left = true`) or
`6|A^H_p| + Σ_{q>p} |A^H_q|` (`left = false`). An empty node has the value of the occupied node next to
it with its own count dropped, so the maximum over all of `{0,1}^H` is attained at an occupied node. -/
def cumMaxProg (left : Bool) (pH : List ℕ) : Prog ℕ :=
  pH.foldlM (fun best p => do
    let c ← countProg (fun y => y == p) pH
    let d ← countProg (fun y => if left then decide (y < p) else decide (p < y)) pH
    tick 4
    pure (max best (6 * c + d))) 0

/-- The unnoised statistic of Algorithm 2, lines 13–18, on a party's records. -/
def statProg (P : Params K) (s : SearchState K) (recs : List ℕ) : Prog K := do
  tick 3
  if P.α / 2 ≤ s.FH - s.FL then do
    let pL ← recs.mapM (prefixProg P.b s.L)
    let pH ← recs.mapM (prefixProg P.b (s.L + 1))
    let u ← jumpMaxProg 0 pL pH
    let v ← jumpMaxProg 1 pL pH
    tick 2
    pure (((u : ℤ) - (v : ℤ) : ℤ) : K)
  else do
    let pH ← recs.mapM (prefixProg P.b s.H)
    let u ← cumMaxProg true pH
    let v ← cumMaxProg false pH
    tick 2
    pure (((u : ℤ) - (v : ℤ) : ℤ) : K)

/-- **The charged program of Algorithm 2** over a scalar field `K` with logarithm `ln`, on the sorted
domain array and the two datasets. It uses only charged primitives. Coins come from a tape. -/
def avalProg (ln : K → K) (dom : Array K) (SA SB : List K) (t : ℕ) (ε β : K) (c : CoinTape K) :
    Prog (ProgResult K) := do
  let b₀ ← clogProg dom.size (dom.size + 1) 0 1
  let b := b₀ + 1
  let T ← clogProg b (b + 1) 0 1
  tick 40
  let P := paramsOf ln b (t / 2) T ε β
  let A ← encodeProg dom SA 1 P.k true
  let B ← encodeProg dom SB 0 P.k false
  let (s, ms) ← searchProg P A B c b 0 (searchInit P) []
  let u ← statProg P s A
  let v ← statProg P s B
  tick (ms.length + 6)
  let va := u + c.lapA
  let vb := v + c.lapB
  pure { msgs := ((vb, []) :: (va, []) :: ms).reverse
         out := if vb ≤ va then Outcome.matched else Outcome.far }

end Prog

/-- A returned message as a protocol message: entries beyond the released ones are the zero padding. -/
def padMsg {K : Type} [Zero K] (x : K × List K) : K × (ℕ → K) :=
  (x.1, fun z => x.2.getD z 0)

/-- The trace and output described by a returned result. -/
def ProgResult.toResult {K : Type} [Zero K] (r : ProgResult K) :
    (ℕ → (K × (ℕ → K)) ⊕ Unit) × (Outcome ⊕ Unit) :=
  (fun j => if h : j < r.msgs.length then Sum.inl (padMsg r.msgs[j]) else Sum.inr (),
    Sum.inl r.out)

/-- The coin tapes given by the coins of the protocol `avalThr`. -/
noncomputable def tapeOf {P : Params ℝ} (ω : Algo2Noise P × Algo2Noise P × Algo2Hash P) : CoinTape ℝ where
  noiseA := noiseAt ω.1
  noiseB := noiseAt ω.2.1
  lapA := ω.1.2
  lapB := ω.2.1.2
  hash := hashAt ω.2.2

/-- **`avalThrProg`: the charged program on a domain `X ⊂ ℝ`.** The domain is available as a sorted
random-access array of reals, the datasets are arrays of reals, the scalar field is `ℝ` and `ln` is
`Real.log`. -/
noncomputable def avalThrProg (X : Finset ℝ) {n : ℕ} (t : ℕ) (ε β : ℝ) (SA SB : Fin n → ↥X)
    (c : CoinTape ℝ) : Prog (ProgResult ℝ) :=
  avalProg Real.log (X.sort (· ≤ ·)).toArray (List.ofFn fun i => (SA i : ℝ))
    (List.ofFn fun i => (SB i : ℝ)) t ε β c

/-- **`avalThrResult`: the trace and the output of the printed Algorithm 2 on given coins**, that is,
of the protocol `avalThr`. -/
noncomputable def avalThrResult (X : Finset ℝ) {n : ℕ} (t : ℕ) (ε β : ℝ) (SA SB : Fin n → ↥X)
    (ω : (avalThr X n t ε β).Coins) :
    (ℕ → (avalThr X n t ε β).Msg ⊕ Unit) × (Outcome ⊕ Unit) :=
  ((avalThr X n t ε β).trace SA SB ω, (avalThr X n t ε β).output SA SB ω)

end PrivOptTest


