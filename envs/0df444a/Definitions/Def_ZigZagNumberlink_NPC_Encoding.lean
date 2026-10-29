-- Prove2me | Definitions.Def_ZigZagNumberlink_NPC_Encoding
-- name    : ZigZagNumberlink_NPC_Encoding
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T04:15:46.281983+00:00
-- url     : https://prove2.me/theorems/62587105-db51-492c-a181-e78915b769f2
-- title:
--   Explicit square-board binary encoding and the solvability language
-- statement:
--   Encode a raw puzzle by the unary headers $1^n0$ and $1^k0$, followed by all $n^2$ cell labels in row-major order, scanning columns from left to right within each row. Each label occupies $b=\max(1,\lfloor\log_2 k\rfloor+1)$ bits, least significant first; in particular $b=1$ when $k=0$. Equivalently $b$ is the least positive integer with $k<2^b$.
--
--   The language $L\subseteq\{0,1\}^*$ consists exactly of encodings of valid solvable puzzles. Membership is defined by existence of puzzle data whose code equals the entire input word and which satisfy the concrete solvability predicate. This is a specification of a language, not an assumption of a decoding or verification algorithm. All malformed words reject: missing header terminators, wrong payload size, labels exceeding $k$, wrong terminal multiplicities, and zero-sized boards. Valid but unsolvable boards also reject.
--
--   The code has $n+k+2+n^2b$ bits and includes each board cell. The source specifies displayed boards rather than a bit order; these conventions retain every positive square board and every valid terminal pairing, with polynomial encoding overhead. They do not encode a solution or impose a puzzle promise.
-- source:
--   Encoding convention for Adcock et al., Zig-Zag Numberlink is NP-Complete, Journal of Information Processing 23(3) (2015), https://doi.org/10.2197/ipsjjip.23.239, Definitions 1–4, printed p. 240 / PDF p. 2, and Theorem 1, printed p. 241 / PDF p. 3. PDF SHA-256: 7686eee342d84716ae6a65b1b061d92002874689610ad4478f5aeed7406b5daf.

import Definitions.Def_ZigZagNumberlink_NPC_Puzzle

namespace ZigZagNumberlink.NPC

/-- The least positive width that can hold labels zero through k. -/
def labelWidth (k : ℕ) : ℕ := Nat.log2 k + 1

/-- Unary headers terminated by false. -/
def unaryHeader (v : ℕ) : List Bool := List.replicate v true ++ [false]

/-- Fixed-width bits, least significant bit first. -/
def labelBits (width value : ℕ) : List Bool :=
  (List.range width).map (fun j => value.testBit j)

/-- Explicit row-major board: n and k headers, then all n² cell labels. -/
def Puzzle.encode (F : Puzzle) : List Bool :=
  unaryHeader F.n ++ unaryHeader F.k ++
    (List.ofFn fun y : Fin F.n =>
      (List.ofFn fun x : Fin F.n =>
        labelBits (labelWidth F.k) (F.label (x, y)).val).flatten).flatten

/-- Only exact encodings of valid solvable boards are accepted. -/
def language : List Bool → Prop :=
  fun word => ∃ F : Puzzle, F.encode = word ∧ F.Solvable

end ZigZagNumberlink.NPC


