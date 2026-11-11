-- Prove2me | Definitions.Def_SemiStreamReach_Main_StreamModel
-- name    : SemiStreamReach_Main_StreamModel
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T21:52:44.498725+00:00
-- url     : https://prove2.me/theorems/96d2dc31-bcde-4659-9c1e-9524316bbc7d
-- title:
--   The randomized multi-pass streaming model on the word RAM, input/output layouts, exact SSSP output, and the approximate-oracle hypothesis of Lemma 18
-- statement:
--   **Model.** A streaming algorithm makes passes over a stream in which the edges of the input graph arrive one at a time in an arbitrary order (the same order in every pass), and its space is measured in bits, with words of $\Theta(\log n)$ bits. A program is a finite instruction list of the word RAM with unit-cost random words (the published `DynBrooks_Machine`), fixed before the word size $w$. A run starts with the words of the first pass pending and pass count $1$; whenever the machine waits at a `read` with nothing pending, the same words are delivered again and the pass count increases. The **space** at a step is $w$ times the number of memory cells written so far; the output is write-only and not charged. The randomness is the coin tape $\omega$, a sequence of independent uniform $w$-bit words.
--
--   **Inputs.** A directed graph on $\{0,\dots,n-1\}$ with edge set $E$ (at most one edge per ordered pair) and natural weights is streamed as: a header, then for each edge $(u,v)$, in an arbitrary order listing every edge exactly once, the three words $u+1,v+1,w(u,v)$, then the end marker $0$. For exact SSSP the header is $n,\ s+1$.
--
--   **Single-source shortest paths.** Given a source $s$, SSSP asks for $\mathrm{dist}_G(s,v)$ for all $v$ and a **shortest-path tree** rooted at $s$. The output is $2n$ words: for each $v$, the distance word ($\mathrm{dist}_G(s,v)+1$, or $0$ for $\infty$) and the parent word ($u+1$, or $0$ for none). It is correct when every distance is exact, $s$ and the unreachable vertices have no parent, and every reachable $v\ne s$ has a parent $u$ with $(u,v)\in E$ and $\mathrm{dist}_G(s,u)+w(u,v)=\mathrm{dist}_G(s,v)$ such that following parents from $v$ reaches $s$. Approximate distances are output as $2n$ words, a pair $p,q$ per vertex meaning $p/q$ ($\infty$ when $q=0$); an implicit hopset as the list of its weighted edges $(u+1,v+1,p,q)$ (weight $p/q$) and its blocks.
--
--   `ExactSSSPSpec P a c_w A T δ` says: on every $n$-vertex input with weights in $\{0,\dots,n^a\}$ and every edge order, with word size $c_w\,\ell(n)$, on every coin tape the run uses at most $A\,n\,(\log_2(n+2))^A$ bits at every step and halts within $T(n)$ passes, and the coin tapes with a wrong output have probability at most $\delta(n)$. `ApproxOracleSpec` is the analogous property of an approximate algorithm (the hypothesis of Lemma 18).
--
--   **Formalization Note.** $\ell(m)=\max\{1,\lceil\log_2(m+1)\rceil\}$. `passRun P w ω inp t` is the (configuration, pass count) after $t$ steps; `RunsWithin` states the space and pass bounds on every coin tape; `failSet` is the set of coin tapes on which the run does not halt with a correct output, measured with `DynBrooks.coinMeasure w`. This is the multi-pass pattern of the published `SemiStreamMWM_StreamModel`, with the coin tape $\omega$ in place of the all-zero tape.
-- source:
--   Hoppenworth, Li, Mahabadi, Tarnawski, Semi-Streaming Reachability and Shortest Paths in n^{1/3+o(1)} Passes, arXiv:2611.05061 (PDF sha256 c1b64474…), p. 1 (PDF 3) and p. 13 (PDF 15), the streaming model and SSSP; p. 56-57 (PDF 58-59), shortest-path trees with zero weights; p. 16 (PDF 18), Lemma 18

import Mathlib
import Definitions.Def_DynBrooks_Machine
import Definitions.Def_SemiStreamReach_Main_Distances
import Definitions.Def_SemiStreamReach_Main_ImplicitHopset

open scoped ENNReal
open Classical

namespace SemiStreamReach.Main

/-! # The randomized multi-pass streaming model, input and output layouts, and exact SSSP

Hoppenworth, Li, Mahabadi, Tarnawski, arXiv:2611.05061 (PDF sha256 c1b64474…), §3 p. 13 (PDF 15):
"In the streaming model, the algorithm can make multiple passes over a stream in which the edges of
the input graph arrive one at a time in an arbitrary order. We measure space in words of O(log n)
bits." "Given a source s ∈ V, the single-source shortest paths problem (SSSP) asks for dist_G(s, v)
for all v ∈ V and a shortest-path tree rooted at s." "The notation Õ(·) hides polylog n factors. We
say that a guarantee holds with high probability if it can be made to hold with probability at
least 1 − n^{−c} for any fixed constant c > 0."

**Formalization Note.** The paper names no instruction set. A program is a `DynBrooks.Program` (the
published `DynBrooks_Machine`): a finite instruction list fixed before the word size `w`, memory
`ℕ → BitVec w`, unit-cost random words from the coin tape `ω : ℕ → BitVec w` (law
`DynBrooks.coinMeasure w`: independent uniform words), a `read` that takes the next pending input
word and blocks when none is pending, a write-only output, and the set `written` of every cell ever
assigned. **Passes** (the pattern of the published `SemiStreamMWM_StreamModel`, here with the coin
tape `ω`): a run starts with the words of the first pass pending and pass count `1`; whenever the
machine is blocked at a `read` with nothing pending, the same words are delivered again and the
count increases, so the stream order is the same in every pass and a pass ends only after all of it
has been read. **Space** in bits is `w · |written|` (every cell ever written is charged); the output
is not charged. A run **halts** at a `halt` instruction; its output is the output list then (it
never changes afterwards). `RunsWithin P w inp S T` says that on **every** coin tape the space is at
most `S` at every step and the run halts having made at most `T` passes; `failSet` is the set of
coin tapes on which the run does not halt with an output satisfying a given correctness predicate.

**Input layout** of a directed graph with edge set `E ⊆ Fin n × Fin n` (at most one edge per
ordered pair) and natural weights `wt`: an edge list `σ` contains every edge of `E` exactly once in
an arbitrary order (`IsEdgeStream`); each edge `(u, v)` is the three words `u + 1, v + 1, wt(u, v)`
(`edgeWords`); a pass is a header, the edge words and the end marker `0`. For exact SSSP the header
is `n, s + 1` (`ssspWords`).

**Output layouts.** Exact SSSP: `2n` words, for `v = 0, …, n − 1` the distance word
(`dist + 1`, or `0` for `∞`) and the parent word (`u + 1`, or `0` for none). `IsSSSPOutput` says the
decoded distances equal `dist_G(s, ·)` in `ℝ≥0∞`, `s` and the unreachable vertices have no parent,
and every reachable `v ≠ s` has a parent `u` with `(u, v) ∈ E` and
`dist_G(s, u) + w(u, v) = dist_G(s, v)` from which following parents reaches `s` (with zero weights
tight parent edges alone could form a cycle, p. 57). Approximate distances: `2n` words, for each `v`
a pair `p, q` meaning the estimate `p/q`, or `∞` when `q = 0`. Implicit hopsets: the number `k` of
listed `H0` edges, then `k` quadruples `u + 1, v + 1, p, q` (an edge `(u, v)` of weight `p/q`,
`q ≥ 1`; an edge listed twice keeps its lightest weight), then the number of blocks, then each block
as its size followed by its vertex labels. `ℓ(m) = max{1, ⌈log₂(m + 1)⌉}` is the number of bits of
`m`. -/

/-- `ℓ(m) = max{1, ⌈log₂(m + 1)⌉}`: the bits needed to hold the number `m`. -/
def ell (m : ℕ) : ℕ := max 1 (Nat.clog 2 (m + 1))

/-- `σ` lists every edge of `E` exactly once, in an arbitrary order. -/
def IsEdgeStream {n : ℕ} (E : Finset (Fin n × Fin n)) (σ : List (Fin n × Fin n)) : Prop :=
  σ.Nodup ∧ ∀ e, e ∈ σ ↔ e ∈ E

/-- The words of the edges: `u + 1, v + 1, wt(u, v)` for each edge `(u, v)` of `σ`, in order. -/
def edgeWords {n : ℕ} (wt : Fin n × Fin n → ℕ) (σ : List (Fin n × Fin n)) : List ℕ :=
  σ.flatMap (fun e => [e.1.val + 1, e.2.val + 1, wt e])

/-- One pass of the exact SSSP input: `n`, `s + 1`, the edge words, `0`. -/
def ssspWords {n : ℕ} (s : Fin n) (wt : Fin n × Fin n → ℕ) (σ : List (Fin n × Fin n)) :
    List ℕ :=
  [n, s.val + 1] ++ edgeWords wt σ ++ [0]

/-- The start of a run: program counter `0`, all cells zero, nothing written, nothing output. -/
def initConfig (w : ℕ) (inp : List ℕ) : DynBrooks.Config w where
  pc := 0
  mem := fun _ => 0
  input := inp
  coinPos := 0
  output := []
  written := ∅

/-- One step of a multi-pass run on coin tape `ω`, on states (configuration, passes started so
far): a completed state receives the words of the next pass; otherwise the machine makes one
step. -/
noncomputable def passStep {w : ℕ} (P : DynBrooks.Program) (ω : ℕ → BitVec w) (inp : List ℕ)
    (st : DynBrooks.Config w × ℕ) : DynBrooks.Config w × ℕ :=
  if DynBrooks.IsCompleted P st.1 then (DynBrooks.feed st.1 inp, st.2 + 1)
  else (DynBrooks.step P ω st.1, st.2)

/-- The state after `t` steps of the multi-pass run of `P` with word size `w` on coin tape `ω`. -/
noncomputable def passRun (P : DynBrooks.Program) (w : ℕ) (ω : ℕ → BitVec w) (inp : List ℕ)
    (t : ℕ) : DynBrooks.Config w × ℕ :=
  (passStep P ω inp)^[t] (initConfig w inp, 1)

/-- The machine is at a `halt` instruction. -/
def IsHalted {w : ℕ} (P : DynBrooks.Program) (c : DynBrooks.Config w) : Prop :=
  P[c.pc]? = some DynBrooks.Instr.halt

/-- Space in bits: the word size times the number of cells ever written. -/
def spaceBits (w : ℕ) (c : DynBrooks.Config w) : ℕ := w * c.written.card

/-- On every coin tape: space at most `S` at every step, and the run halts having made at most `T`
passes. -/
def RunsWithin (P : DynBrooks.Program) (w : ℕ) (inp : List ℕ) (S T : ℝ) : Prop :=
  ∀ ω : ℕ → BitVec w,
    (∀ t, (spaceBits w (passRun P w ω inp t).1 : ℝ) ≤ S) ∧
    ∃ t, IsHalted P (passRun P w ω inp t).1 ∧ ((passRun P w ω inp t).2 : ℝ) ≤ T

/-- The coin tapes on which the run does not halt with an output satisfying `Good`. -/
def failSet (P : DynBrooks.Program) (w : ℕ) (inp : List ℕ) (Good : List ℕ → Prop) :
    Set (ℕ → BitVec w) :=
  {ω | ¬ ∃ t, IsHalted P (passRun P w ω inp t).1 ∧ Good (passRun P w ω inp t).1.output}

/-- The parent of `v` in an exact SSSP output: the label in the parent word, if it is in `1..n`. -/
def parentOf {n : ℕ} (out : List ℕ) (v : Fin n) : Option (Fin n) :=
  let p := out.getD (2 * v.val + 1) 0
  if h : 1 ≤ p ∧ p ≤ n then some ⟨p - 1, by omega⟩ else none

/-- The output is the exact distance vector from `s` together with a shortest-path tree rooted at
`s`. -/
def IsSSSPOutput {n : ℕ} (E : Finset (Fin n × Fin n)) (wt : Fin n × Fin n → ℕ) (s : Fin n)
    (out : List ℕ) : Prop :=
  out.length = 2 * n ∧
  ∀ v : Fin n,
    (out.getD (2 * v.val) 0 = 0 ↔ dist (ofEdges E wt) s v = ⊤) ∧
    (1 ≤ out.getD (2 * v.val) 0 →
      dist (ofEdges E wt) s v = ((out.getD (2 * v.val) 0 - 1 : ℕ) : ℝ≥0∞)) ∧
    ((v = s ∨ dist (ofEdges E wt) s v = ⊤) → out.getD (2 * v.val + 1) 0 = 0) ∧
    (v ≠ s → dist (ofEdges E wt) s v ≠ ⊤ →
      ∃ u, parentOf out v = some u ∧ (u, v) ∈ E ∧
        dist (ofEdges E wt) s u + ((wt (u, v) : ℕ) : ℝ≥0∞) = dist (ofEdges E wt) s v ∧
        ∃ k : ℕ, (fun o : Option (Fin n) => o.bind (parentOf out))^[k] (some v) = some s)

/-- The estimate encoded by the pair of words `p, q`: `p/q`, or `∞` when `q = 0`. -/
noncomputable def decodeEst (p q : ℕ) : ℝ≥0∞ :=
  if q = 0 then ⊤ else ENNReal.ofReal ((p : ℝ) / (q : ℝ))

/-- The estimate of `v` in an approximate-distance output. -/
noncomputable def estOf {n : ℕ} (out : List ℕ) (v : Fin n) : ℝ≥0∞ :=
  decodeEst (out.getD (2 * v.val) 0) (out.getD (2 * v.val + 1) 0)

/-- The output is a vector of `(1 + ε)`-approximate distances from `s`. -/
def IsApproxOutput {n : ℕ} (E : Finset (Fin n × Fin n)) (wt : Fin n × Fin n → ℕ) (s : Fin n)
    (ε : ℝ) (out : List ℕ) : Prop :=
  out.length = 2 * n ∧ IsApproxDist (ofEdges E wt) s ε (estOf out)

/-- The output words of an implicit hopset given by a list of weighted edges `(u, v, p, q)`
(weight `p/q`) and a list of blocks. -/
def ihWords {n : ℕ} (L : List (Fin n × Fin n × ℕ × ℕ)) (Bs : List (List (Fin n))) : List ℕ :=
  [L.length] ++ L.flatMap (fun e => [e.1.val + 1, e.2.1.val + 1, e.2.2.1, e.2.2.2]) ++
    [Bs.length] ++ Bs.flatMap (fun B => B.length :: B.map (fun v => v.val + 1))

/-- The weighted edge set `H0` of a list of weighted edges (lightest weight per pair). -/
noncomputable def edgesOfList {n : ℕ} (L : List (Fin n × Fin n × ℕ × ℕ)) : WGraph (Fin n) :=
  fun u v => ⨅ e ∈ L, ⨅ (_ : e.1 = u ∧ e.2.1 = v),
    ENNReal.ofReal ((e.2.2.1 : ℝ) / (e.2.2.2 : ℝ))

/-- The output encodes an `(h, ε, x)`-implicit hopset of the input graph, with constant `A` in
Definition 7 (1). -/
def IsImplicitHopsetOutput {n : ℕ} (E : Finset (Fin n × Fin n)) (wt : Fin n × Fin n → ℕ)
    (h : ℕ) (ε : ℝ) (x : ℕ) (A : ℝ) (out : List ℕ) : Prop :=
  ∃ (L : List (Fin n × Fin n × ℕ × ℕ)) (Bs : List (List (Fin n))),
    out = ihWords L Bs ∧ (∀ e ∈ L, 1 ≤ e.2.2.2) ∧
    IsImplicitHopset (ofEdges E wt) h ε x A (edgesOfList L) (Bs.map List.toFinset)

/-- `P` computes exact SSSP (distances and a shortest-path tree) on `n`-vertex directed graphs with
integer weights in `{0, …, n^a}`, with word size `cw · ℓ(n)`: on every coin tape it uses at most
`A · n · (log₂(n + 2))^A` bits at every step and halts within `T n` passes, and the coin tapes on
which its output is wrong have probability at most `δ n`. -/
def ExactSSSPSpec (P : DynBrooks.Program) (a cw : ℕ) (A : ℝ) (T : ℕ → ℝ) (δ : ℕ → ℝ≥0∞) :
    Prop :=
  ∀ (n : ℕ) (s : Fin n) (E : Finset (Fin n × Fin n)) (wt : Fin n × Fin n → ℕ)
    (σ : List (Fin n × Fin n)),
    1 ≤ n → (∀ e ∈ E, wt e ≤ n ^ a) → IsEdgeStream E σ →
    RunsWithin P (cw * ell n) (ssspWords s wt σ)
        (A * (n : ℝ) * Real.logb 2 ((n : ℝ) + 2) ^ A) (T n) ∧
      DynBrooks.coinMeasure (cw * ell n)
        (failSet P (cw * ell n) (ssspWords s wt σ) (IsSSSPOutput E wt s)) ≤ δ n

/-- The hypothesis of Lemma 18 on an approximate algorithm `P`, for a size parameter `N`: on every
directed graph with `n' ≤ K0 · N` vertices and positive integer weights at most `(N + 1)^b`, read
from the stream with header `N, n', s + 1`, with word size `cw · ℓ(N + n')`, on every coin tape it
uses at most `A · N · (log₂(N + 2))^A` bits at every step and halts within `T N` passes, and the coin
tapes on which its output is not a vector of `(1 + c/log₂(N + 2))`-approximate distances from `s`
have probability at most `δ N`. -/
def ApproxOracleSpec (P : DynBrooks.Program) (cw : ℕ) (A : ℝ) (T : ℕ → ℝ) (K0 b : ℕ) (c : ℝ)
    (δ : ℕ → ℝ≥0∞) : Prop :=
  ∀ (N n' : ℕ) (s : Fin n') (E : Finset (Fin n' × Fin n')) (wt : Fin n' × Fin n' → ℕ)
    (σ : List (Fin n' × Fin n')),
    1 ≤ N → n' ≤ K0 * N → (∀ e ∈ E, 1 ≤ wt e ∧ wt e ≤ (N + 1) ^ b) → IsEdgeStream E σ →
    RunsWithin P (cw * ell (N + n')) ([N, n', s.val + 1] ++ edgeWords wt σ ++ [0])
        (A * (N : ℝ) * Real.logb 2 ((N : ℝ) + 2) ^ A) (T N) ∧
      DynBrooks.coinMeasure (cw * ell (N + n'))
        (failSet P (cw * ell (N + n')) ([N, n', s.val + 1] ++ edgeWords wt σ ++ [0])
          (IsApproxOutput E wt s (c / Real.logb 2 ((N : ℝ) + 2)))) ≤ δ N

end SemiStreamReach.Main


