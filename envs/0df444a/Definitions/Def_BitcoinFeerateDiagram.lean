-- Prove2me | Definitions.Def_BitcoinFeerateDiagram
-- name    : BitcoinFeerateDiagram
-- status  : Definition
-- author  : @pitimespi
-- created : 2026-10-29T23:50:33.654197+00:00
-- url     : https://prove2.me/theorems/963c1c8f-f0d9-4bf8-b2ec-de780eddbc19
-- title:
--   FeeFrac arithmetic, Core's chunk-diagram comparison, and the cluster-mempool replacement check
-- statement:
--   A transcription of the cluster mempool's replacement check over the replace-by-fee mission's `BitcoinReplacement`, at Bitcoin Core revision `a773e1e`, where it replaced BIP125 rule 3.
--
--   **`FeeFrac`** — a fee and a size (integers). **`IsEmpty`**, **`mul`**, **`mulFallback`** (the 32-bit split multiplication), **`div`** (round down or up), **`divFallback`**, **`ceilDiv`**, **`evaluateFee`**, **`evaluateFeeDown`**, **`evaluateFeeUp`** — Core's arithmetic, with both code paths. **`byRatioCmp a b`** — `compare (a.fee · b.size) (b.fee · a.size)`, the `ByRatio` ordering; **`ratio a`** — `fee / size` in $\mathbb{Q}$.
--
--   **`PartialOrdering`** — `less`, `equivalent`, `greater`, `unordered`; **`boolCompare`**. **`sweep`** — the loop of `CompareChunks`, one equation per iteration over the two chunk lists with the accumulated (fee, size) of each and the two "better somewhere" flags; **`compareChunks c0 c1`** — Core's `CompareChunks`. **`ImprovesFeerateDiagram old new`** — `compareChunks new old = greater` (`policy/rbf.cpp`).
--
--   **`diagram cs x`** — the feerate diagram as a function: the cumulative fee at cumulative size $x$, linear within each chunk and constant after the last; **`diagramFee`**, **`diagramSize`** — totals. **`SizesPos`** — every chunk has positive size; **`FeeratesNonIncreasing`** — chunk feerates in non-increasing order. **`Dominates c0 c1`** — `diagram c0 ≥ diagram c1` on $[0, \infty)$; **`BetterSomewhere c0 c1`** — strictly greater at some $x \ge 0$; **`StrictlyBetter`** — both.
--
--   **Formalization Note.** Imports Mathlib and the replacement mission. The chunk lists (the linearization of the affected clusters, `txmempool.cpp`/`txgraph.cpp`) are taken as input; fees and sizes are unbounded integers, so overflow is not modelled.
-- source:
--   Bitcoin Core a773e1e33b349dc819b5a0edc1c7a4839dc73b48: util/feefrac.h (FeeFrac :20, MulFallback :25-30, DivFallback :40-59, Mul/Div :64-82, operator+/- :120-131, EvaluateFee :147-175, ByRatio :217-240), util/overflow.h (CeilDiv :70-74), util/feefrac.cpp (CompareChunks :12-75), policy/rbf.cpp (ImprovesFeerateDiagram :127-140, PaysForRBF :100-125): https://github.com/bitcoin/bitcoin/blob/a773e1e33b349dc819b5a0edc1c7a4839dc73b48/src/util/feefrac.cpp; test vectors from src/test/rbf_tests.cpp (feerate_chunks_utilities) and src/test/feefrac_tests.cpp

import Mathlib
import Definitions.Def_BitcoinReplacement

/-!
# Bitcoin Core's feerate-diagram replacement check (`ImprovesFeerateDiagram`)

At bitcoin/bitcoin revision `a773e1e33b349dc819b5a0edc1c7a4839dc73b48` BIP125 rule 3
("the replacement pays a higher feerate than each directly conflicting transaction") is gone from
`policy/rbf.cpp`; it has been replaced by the cluster-mempool check

```cpp
std::optional<std::pair<DiagramCheckError, std::string>> ImprovesFeerateDiagram(CTxMemPool::ChangeSet& changeset)
{
    const auto chunk_results{changeset.CalculateChunksForRBF()};
    if (!chunk_results.has_value()) { return {DiagramCheckError::UNCALCULABLE, ...}; }
    if (!std::is_gt(CompareChunks(chunk_results.value().second, chunk_results.value().first))) {
        return {DiagramCheckError::FAILURE, "insufficient feerate: does not improve feerate diagram"};
    }
    return std::nullopt;
}
```
(`policy/rbf.cpp`, lines 127–140).  `CalculateChunksForRBF` (`txmempool.cpp` 1042–1051) returns
`TxGraph::GetMainStagingDiagrams()` (`txgraph.cpp` 2810–2834): `first` is the list of chunk
feerates (`FeeFrac`s) of every *main* cluster that the replacement touches, `second` the list of
chunk feerates of every *staging* cluster (the same transactions with the conflicts removed and the
replacement added), each list sorted by decreasing feerate (`ByRatioNegSize`).  The replacement is
accepted iff `CompareChunks(new, old)` is `std::partial_ordering::greater`.

This file transcribes

* `FeeFrac` (`util/feefrac.h`): a (fee, size) pair with `int64_t` fee and `int32_t` size, its `+`
  and `-`, the `ByRatio` feerate comparison by cross-multiplication, and the fee evaluation
  `EvaluateFee<RoundDown>` together with the `Mul`/`Div` and `MulFallback`/`DivFallback` helpers;
* `CompareChunks` (`util/feefrac.cpp`, lines 12–75): the sweep over the breakpoints of the two
  piecewise-linear diagrams, as a function on `List FeeFrac`;
* `ImprovesFeerateDiagram` as the predicate `CompareChunks new old = greater`;
* the mathematical object the sweep compares: the *diagram function* `diagram cs : ℚ → ℚ` of a chunk
  list, the piecewise-linear function through the cumulative (size, fee) points, extended
  horizontally to the right ("The implied diagram for each starts at (0, 0), then contains for each
  chunk the cumulative fee and size up to that chunk, and then extends infinitely to the right with
  a horizontal line", `util/feefrac.h`).

The chunk lists themselves (the output of cluster linearisation and chunking,
`ChunkLinearization` in `cluster_linearize.h`) are taken as *input*: nothing here models
clusters, dependencies or linearisations.  Machine-integer overflow is not modelled: all arithmetic
is in `ℤ`/`ℚ`, which is what the C++ computes under the documented preconditions
("the sum of the FeeFracs in either of the chunks' data set do not overflow").
-/

namespace BitcoinFeerateDiagram

/-- `struct FeeFrac { int64_t fee; int32_t size; }` (`util/feefrac.h`).  A fee and a size; "the size
of a FeeFrac cannot be zero unless the fee is also zero".  Modelled with unbounded integers. -/
structure FeeFrac where
  /-- `int64_t fee` (satoshi; may be negative, e.g. after `prioritisetransaction`). -/
  fee : ℤ
  /-- `int32_t size` (vbytes or weight units, depending on the tag). -/
  size : ℤ
  deriving DecidableEq, Repr

namespace FeeFrac

/-- `FeeFrac()` : the empty `FeeFrac` (fee 0, size 0), the initial value of `accum` in
`CompareChunks`. -/
instance : Zero FeeFrac := ⟨⟨0, 0⟩⟩

/-- `operator+(a, b) = {a.fee + b.fee, a.size + b.size}`. -/
instance : Add FeeFrac := ⟨fun a b => ⟨a.fee + b.fee, a.size + b.size⟩⟩

/-- `operator-(a, b) = {a.fee - b.fee, a.size - b.size}`. -/
instance : Sub FeeFrac := ⟨fun a b => ⟨a.fee - b.fee, a.size - b.size⟩⟩

/-- `IsEmpty()`: `size == 0`. -/
def IsEmpty (a : FeeFrac) : Prop := a.size = 0

/-- `FeeFrac::Mul(int64_t a, int32_t b)` (the `__int128` version): the exact product. -/
def mul (a b : ℤ) : ℤ := a * b

/-- `FeeFrac::MulFallback(int64_t a, int32_t b)`: the 32×64 signed product returned as a pair
`(high, low32)` whose value is `high * 2^32 + low32`:
```cpp
int64_t low = int64_t{static_cast<uint32_t>(a)} * b;
int64_t high = (a >> 32) * b;
return {high + (low >> 32), static_cast<uint32_t>(low)};
```
`static_cast<uint32_t>(x)` is `x mod 2^32` and the arithmetic shift `x >> 32` is
`⌊x / 2^32⌋`; in ℤ, `/` and `%` are floor division and nonnegative remainder, which is exactly this. -/
def mulFallback (a b : ℤ) : ℤ × ℤ :=
  let low := (a % 2 ^ 32) * b
  let high := (a / 2 ^ 32) * b
  (high + low / 2 ^ 32, low % 2 ^ 32)

/-- `FeeFrac::Div(__int128 n, int32_t d, bool round_down)`: C++ `/` and `%` truncate towards zero
(`Int.tdiv`, `Int.tmod`), then the quotient is corrected so that the result rounds towards
`-∞` (if `round_down`) or `+∞` (otherwise):
```cpp
int64_t quot = n / d;
int32_t mod = n % d;
return quot + ((mod > 0) - (mod && round_down));
```
Requires `d > 0`. -/
def div (n d : ℤ) (roundDown : Bool) : ℤ :=
  n.tdiv d + ((if 0 < n.tmod d then 1 else 0) - (if n.tmod d ≠ 0 ∧ roundDown then 1 else 0))

/-- `FeeFrac::DivFallback(std::pair<int64_t, uint32_t> n, int32_t d, bool round_down)`, the 96/32
division of the value `n.first * 2^32 + n.second` (as produced by `mulFallback`):
```cpp
int64_t quot_high = n.first / d;
int64_t n_low = ((n.first % d) << 32) + n.second;
int64_t quot_low = n_low / d;
int32_t mod_low = n_low % d;
quot_low += (mod_low > 0) - (mod_low && round_down);
return (quot_high << 32) + quot_low;
```
C++ `/`, `%` truncate towards zero; `<< 32` on a signed value is multiplication by `2^32`. -/
def divFallback (n : ℤ × ℤ) (d : ℤ) (roundDown : Bool) : ℤ :=
  let quotHigh := n.1.tdiv d
  let nLow := (n.1.tmod d) * 2 ^ 32 + n.2
  let quotLow := nLow.tdiv d
  let modLow := nLow.tmod d
  let quotLow' := quotLow + ((if 0 < modLow then 1 else 0) - (if modLow ≠ 0 ∧ roundDown then 1 else 0))
  quotHigh * 2 ^ 32 + quotLow'

/-- `CeilDiv(dividend, divisor)` (`util/overflow.h`, unsigned): `dividend / divisor + (dividend %
divisor != 0)`.  Stated on `ℤ` for nonnegative operands, where `/` and `%` agree with the unsigned
operations. -/
def ceilDiv (n d : ℤ) : ℤ := n / d + (if n % d ≠ 0 then 1 else 0)

/-- `FeeFrac::EvaluateFee<RoundDown>(int32_t at_size)` (`util/feefrac.h`): the fee for `at_size`
units at this object's feerate, `(fee * at_size) / size` rounded towards `-∞` (`RoundDown`) or
`+∞`.  Requires `size > 0` and `at_size ≥ 0`.
```cpp
if (fee >= 0 && fee < 0x200000000) [[likely]] {
    if constexpr (RoundDown) { return (uint64_t(fee) * at_size) / uint32_t(size); }
    else                     { return CeilDiv(uint64_t(fee) * at_size, uint32_t(size)); }
} else {
    return Div(Mul(fee, at_size), size, RoundDown);
}
```
In the first branch all operands are nonnegative, so the unsigned `uint64_t` operations are the
integer operations on `ℤ` (no overflow by the stated precondition). -/
def evaluateFee (f : FeeFrac) (atSize : ℤ) (roundDown : Bool) : ℤ :=
  if 0 ≤ f.fee ∧ f.fee < 2 ^ 33 then
    if roundDown then (f.fee * atSize) / f.size else ceilDiv (f.fee * atSize) f.size
  else div (mul f.fee atSize) f.size roundDown

/-- `EvaluateFeeDown(at_size) = EvaluateFee<true>(at_size)`. -/
def evaluateFeeDown (f : FeeFrac) (atSize : ℤ) : ℤ := evaluateFee f atSize true

/-- `EvaluateFeeUp(at_size) = EvaluateFee<false>(at_size)`. -/
def evaluateFeeUp (f : FeeFrac) (atSize : ℤ) : ℤ := evaluateFee f atSize false

/-- `ByRatio` comparison `operator<=>(ByRatio a, ByRatio b)`:
```cpp
auto cross_a = T::Mul(a.m_feefrac.fee, b.m_feefrac.size);
auto cross_b = T::Mul(b.m_feefrac.fee, a.m_feefrac.size);
return cross_a <=> cross_b;
```
i.e. the feerates `a.fee / a.size` and `b.fee / b.size` compared by cross-multiplication, with no
rounding (`std::strong_ordering`, mapped to `Ordering`). -/
def byRatioCmp (a b : FeeFrac) : Ordering := compare (mul a.fee b.size) (mul b.fee a.size)

/-- The feerate of a `FeeFrac` as an exact rational number (`fee / size`). -/
def ratio (a : FeeFrac) : ℚ := (a.fee : ℚ) / (a.size : ℚ)

end FeeFrac

/-- `std::partial_ordering`, the result type of `CompareChunks`. -/
inductive PartialOrdering
  | less
  | equivalent
  | greater
  | unordered
  deriving DecidableEq, Repr

/-- `better_somewhere[0] <=> better_somewhere[1]` on `bool` (`false < true`), the final `return` of
`CompareChunks` (reached only when at most one of the two flags is set). -/
def boolCompare (b0 b1 : Bool) : PartialOrdering :=
  match b0, b1 with
  | false, false => .equivalent
  | false, true => .less
  | true, false => .greater
  | true, true => .equivalent

/-- The `do { … } while(true)` loop of `CompareChunks` (`util/feefrac.cpp`, lines 29–71), as a
function of its state: `rem0`, `rem1` are the unprocessed chunks of the two inputs
(`chunk[i][next_index[i]..]`), `acc0`, `acc1` the accumulated points `accum[i]`, and `b0`, `b1` the
flags `better_somewhere[i]`.  Each arm is one iteration:

* `done_0 && done_1` → `break`, then `return better_somewhere[0] <=> better_somewhere[1]`;
* exactly one side done → `unproc_side` is the other side, `P = next_point(unproc_side)`,
  `A = prev_point(!unproc_side)`, and `cmp = ByRatio{P - A} <=> ByRatio{FeeFrac(0, 1)}`
  ("act as if AB has slope tail_feerate(of 0)");
* both sides have points left → `unproc_side = next_point(0).size > next_point(1).size`,
  `B = next_point(!unproc_side)`, `cmp = ByRatio{P - A} <=> ByRatio{B - A}`, and if
  `B.size == P.size` the other side is advanced as well;

then `if (is_gt(cmp)) better_somewhere[unproc_side] = true; if (is_lt(cmp))
better_somewhere[!unproc_side] = true; advance(unproc_side); if (both flags) return unordered;`. -/
def sweep : List FeeFrac → List FeeFrac → FeeFrac → FeeFrac → Bool → Bool → PartialOrdering
  | [], [], _, _, b0, b1 => boolCompare b0 b1
  | c0 :: r0, [], acc0, acc1, b0, b1 =>
      -- done_1: unproc_side = 0, P = chunk[0][next] + accum[0], A = accum[1]
      let p := c0 + acc0
      let cmp := FeeFrac.byRatioCmp (p - acc1) ⟨0, 1⟩
      let b0' := b0 || (cmp == .gt)
      let b1' := b1 || (cmp == .lt)
      if b0' && b1' then .unordered else sweep r0 [] p acc1 b0' b1'
  | [], c1 :: r1, acc0, acc1, b0, b1 =>
      -- done_0: unproc_side = 1, P = chunk[1][next] + accum[1], A = accum[0]
      let p := c1 + acc1
      let cmp := FeeFrac.byRatioCmp (p - acc0) ⟨0, 1⟩
      let b1' := b1 || (cmp == .gt)
      let b0' := b0 || (cmp == .lt)
      if b0' && b1' then .unordered else sweep [] r1 acc0 p b0' b1'
  | c0 :: r0, c1 :: r1, acc0, acc1, b0, b1 =>
      let p0 := c0 + acc0
      let p1 := c1 + acc1
      if p0.size > p1.size then
        -- unproc_side = 1: P = p1, A = accum[0], B = p0 (B.size ≠ P.size here)
        let cmp := FeeFrac.byRatioCmp (p1 - acc0) (p0 - acc0)
        let b1' := b1 || (cmp == .gt)
        let b0' := b0 || (cmp == .lt)
        if b0' && b1' then .unordered else sweep (c0 :: r0) r1 acc0 p1 b0' b1'
      else
        -- unproc_side = 0: P = p0, A = accum[1], B = p1
        let cmp := FeeFrac.byRatioCmp (p0 - acc1) (p1 - acc1)
        let b0' := b0 || (cmp == .gt)
        let b1' := b1 || (cmp == .lt)
        if b0' && b1' then .unordered
        else if p1.size = p0.size then sweep r0 r1 p0 p1 b0' b1'   -- advance(!unproc_side) too
        else sweep r0 (c1 :: r1) p0 acc1 b0' b1'
  termination_by r0 r1 => r0.length + r1.length

/-- `CompareChunks(chunks0, chunks1)` (`util/feefrac.cpp`): compare the feerate diagrams implied by
two sorted chunk lists; `next_index = {0, 0}`, `accum = {FeeFrac(), FeeFrac()}`,
`better_somewhere = {false, false}`. -/
def compareChunks (chunks0 chunks1 : List FeeFrac) : PartialOrdering :=
  sweep chunks0 chunks1 0 0 false false

/-- `ImprovesFeerateDiagram` (`policy/rbf.cpp`): with `old` the main-mempool diagram
(`chunk_results.first`) and `new` the staging diagram (`chunk_results.second`), the replacement
passes iff `std::is_gt(CompareChunks(new, old))`, i.e. the new diagram is strictly greater. -/
def ImprovesFeerateDiagram (old new : List FeeFrac) : Prop :=
  compareChunks new old = .greater

/-- The feerate diagram of a chunk list as a function of cumulative size: it starts at `(0, 0)`,
is linear with slope `c.fee / c.size` across each chunk `c` in order, and is constant (the total
fee) beyond the total size.  (For the chunk lists produced by Core every chunk has positive size;
`diagram` is only meaningful under `SizesPos`.) -/
def diagram : List FeeFrac → ℚ → ℚ
  | [], _ => 0
  | c :: cs, x => if x ≤ c.size then (c.fee : ℚ) * x / c.size else c.fee + diagram cs (x - c.size)

/-- Total fee of a chunk list (the final height of its diagram). -/
def diagramFee (cs : List FeeFrac) : ℤ := (cs.map FeeFrac.fee).sum

/-- Total size of a chunk list (the last breakpoint of its diagram). -/
def diagramSize (cs : List FeeFrac) : ℤ := (cs.map FeeFrac.size).sum

/-- Every chunk has positive size (`Assume(slope_ap.size > 0)` in `CompareChunks`; true of every
chunk of a linearisation, since a chunk is a nonempty set of transactions of positive weight). -/
def SizesPos (cs : List FeeFrac) : Prop := ∀ c ∈ cs, 0 < c.size

/-- The chunks are listed in non-increasing feerate order (`ByRatio` comparison), as
`GetMainStagingDiagrams` sorts them. -/
def FeeratesNonIncreasing (cs : List FeeFrac) : Prop :=
  cs.IsChain fun a b => b.fee * a.size ≤ a.fee * b.size

/-- `Dominates c0 c1`: the diagram of `c0` lies (weakly) above the diagram of `c1` at every
nonnegative size. -/
def Dominates (c0 c1 : List FeeFrac) : Prop :=
  ∀ x : ℚ, 0 ≤ x → diagram c1 x ≤ diagram c0 x

/-- `BetterSomewhere c0 c1`: the diagram of `c0` lies strictly above that of `c1` at some
nonnegative size. -/
def BetterSomewhere (c0 c1 : List FeeFrac) : Prop :=
  ∃ x : ℚ, 0 ≤ x ∧ diagram c1 x < diagram c0 x

/-- `StrictlyBetter c0 c1`: `c0` dominates `c1` and is strictly better somewhere — the intended
meaning of `CompareChunks(c0, c1) == greater`. -/
def StrictlyBetter (c0 c1 : List FeeFrac) : Prop :=
  Dominates c0 c1 ∧ BetterSomewhere c0 c1

end BitcoinFeerateDiagram


