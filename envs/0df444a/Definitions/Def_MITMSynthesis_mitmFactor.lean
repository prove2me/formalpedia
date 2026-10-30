-- Prove2me | Definitions.Def_MITMSynthesis_mitmFactor
-- name    : MITMSynthesis_mitmFactor
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:04:39.090711+00:00
-- url     : https://prove2.me/theorems/f4cf829b-b379-47b0-897b-c5143becf0b6
-- title:
--   The algorithm MITM-factor (corrected), in the cost monad
-- statement:
--   The meet-in-the-middle algorithm MITM-factor of the paper, with two corrections, run in the cost monad. Input: a list `vs` of pairs (layer, unitary) enumerating $V_{n,\mathcal G}$, a target $U$, a depth bound $l$, and a linear order on unitaries.
--
--   1. **Depth 0.** Compare $U$ with $I$ (one step); if equal, return the empty circuit.
--   2. **Loop** for $i = 1, \dots, \lceil l/2 \rceil$, keeping $S_{i-1}$ as a list of pairs (unitary $W$, circuit $c$ with product $W$), starting from $S_0 = [(I, [\,])]$:
--      1. build $S_i = V_{n,\mathcal G} S_{i-1}$: each $(W, c)$ and each layer $(a, v)$ give $(vW, a :: c)$, one multiplication each;
--      2. sort $S_i$ by the unitary and copy it into an array;
--      3. (depth $2i-1$) for every $(V, c) \in S_{i-1}$ compute $V^\dagger U$ and binary-search it in $S_i$; on a hit $(W, d)$ with $W = V^\dagger U$ return the circuit $c$ followed by $d$, whose product is $VW = U$;
--      4. (depth $2i$, **only if $2i \le l$**) the same for every $(V, c) \in S_i$.
--   3. Return no circuit.
--
--   Every multiplication, adjoint, comparison and list or array step is charged. The returned circuit is a list of layers $L_1, \dots, L_m$ whose unitaries satisfy $U_1 U_2 \cdots U_m = U$.
--
--   **Formalization Note** The pieces are `extendOneC`, `extendC`, `buildS` (the list $S_i$), `queriesC` (the list $S^\dagger U$), `iterC` (iteration $i$, returning `inl` of a circuit or `inr` of $S_i$), `loopC` and `mitmFactor`. The linear order is the instance argument `ord`. $\lceil l/2\rceil$ is `(l + 1) / 2`. The printed pseudocode tests depth $2\lceil l/2\rceil = l+1$ when $l$ is odd and never tests depth $0$; both are corrected here (see the main theorem).
-- source:
--   Amy, Maslov, Mosca, Roetteler, A meet-in-the-middle algorithm for fast synthesis of depth-optimal quantum circuits, arXiv:1206.0758v3, §3, p. 6, function MITM-factor(G, U, l) and the paragraph following it

import Mathlib
import Definitions.Def_MITMSynthesis_Timed
import Definitions.Def_MITMSynthesis_sortC
import Definitions.Def_MITMSynthesis_searchC

namespace MITMSynthesis


variable {α : Type} {M : Type}

/-- Extend one depth-`(i-1)` entry `(W, c)` by every layer `(a, v)` of `vs`, producing
`(v * W, a :: c)` (the new layer is applied last, i.e. written first). One multiplication and one
list step per new entry. -/
def extendOneC [Mul M] (W : M) (c : List α) : List (α × M) → Timed (List (M × List α))
  | [] => pure []
  | (a, v) :: rest => do
      let x ← mulC v W
      let r ← extendOneC W c rest
      tick
      pure ((x, a :: c) :: r)

/-- `S_i := V_{n,G} S_{i-1}` on lists: extend every entry of `prev` by every layer of `vs`.
Concatenation charges one step per element moved. -/
def extendC [Mul M] (vs : List (α × M)) : List (M × List α) → Timed (List (M × List α))
  | [] => pure []
  | (W, c) :: rest => do
      let xs ← extendOneC W c vs
      let ys ← extendC vs rest
      ticks (xs.length + 1)
      pure (xs ++ ys)

/-- The list `S_i` of pairs (unitary, circuit): `S_0 = [(I, [])]`, `S_{i+1} = V S_i`. -/
def buildS [Monoid M] (vs : List (α × M)) : ℕ → Timed (List (M × List α))
  | 0 => do tick; pure [(1, [])]
  | i + 1 => do
      let p ← buildS vs i
      extendC vs p

/-- The queries `V† U` (with payload the circuit of `V`) for every entry `(V, c)`; one adjoint,
one multiplication and one list step each. -/
def queriesC [Mul M] [Star M] (U : M) : List (M × List α) → Timed (List (M × List α))
  | [] => pure []
  | (V, c) :: rest => do
      let s ← starC V
      let q ← mulC s U
      let r ← queriesC U rest
      tick
      pure ((q, c) :: r)

variable [Monoid M] [Star M] [ord : LinearOrder M]

/-- **Iteration `i` of MITM-factor** (arXiv:1206.0758v3, p. 6, corrected), given `prev = S_{i-1}`.
Build `S_i = V S_{i-1}`, sort it by the unitary and copy it into an array. Search every element
of `S_{i-1}† U` in `S_i` (depth `2i-1`); on a hit `V† U = W` return the circuit `V W`. Otherwise,
**only if `2 i ≤ l`**, search every element of `S_i† U` in `S_i` (depth `2i`). Returns `inl` of a
circuit (list of layer labels) on a hit and `inr S_i` otherwise. -/
def iterC (vs : List (α × M)) (U : M) (l i : ℕ) (prev : List (M × List α)) :
    Timed (List α ⊕ List (M × List α)) := do
  tick
  let cur ← extendC vs prev
  let sorted ← sortC Prod.fst cur
  ticks (sorted.length + 1)
  let arr := sorted.toArray
  let q1 ← queriesC U prev
  let h1 ← searchAllC Prod.fst arr q1
  match h1 with
  | some (c, (_, d)) => do
      ticks (c.length + 1)
      pure (.inl (c ++ d))
  | none =>
      if 2 * i ≤ l then do
        let q2 ← queriesC U cur
        let h2 ← searchAllC Prod.fst arr q2
        match h2 with
        | some (c, (_, d)) => do
            ticks (c.length + 1)
            pure (.inl (c ++ d))
        | none => pure (.inr cur)
      else pure (.inr cur)

/-- Run iterations `i, i+1, …` for at most `k` more iterations, starting from `prev = S_{i-1}`. -/
def loopC (vs : List (α × M)) (U : M) (l : ℕ) : ℕ → ℕ → List (M × List α) → Timed (Option (List α))
  | 0, _, _ => do tick; pure none
  | k + 1, i, prev => do
      tick
      let r ← iterC vs U l i prev
      match r with
      | .inl c => pure (some c)
      | .inr cur => loopC vs U l k (i + 1) cur

/-- **MITM-factor** (arXiv:1206.0758v3, §3, p. 6), with two corrections: depth `0` is tested
first (`U = I` returns the empty circuit), and the depth-`2i` test runs only when `2 i ≤ l`.
Input: the list `vs` of pairs (layer, unitary) enumerating `V_{n,G}`, the target `U`, the depth
bound `l`; the comparison order on unitaries is the instance `[LinearOrder M]`. The loop runs
`i = 1, …, ⌈l/2⌉ = (l + 1) / 2`. Output: `some c`, a circuit as a list of layer labels whose
unitaries multiply (left to right, `U₁ U₂ ⋯ U_m`) to `U`, or `none`. -/
def mitmFactor (vs : List (α × M)) (U : M) (l : ℕ) : Timed (Option (List α)) := do
  let o ← cmpC U 1
  if o = Ordering.eq then pure (some [])
  else loopC vs U l ((l + 1) / 2) 1 [(1, [])]

end MITMSynthesis


