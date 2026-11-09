-- Prove2me | Definitions.Def_AMRangeAvoid_Characterization_Encoding
-- name    : AMRangeAvoid_Characterization_Encoding
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:57:29.512588+00:00
-- url     : https://prove2.me/theorems/7b1554ca-cdb9-4255-90c9-312a11782b26
-- title:
--   Binary words and self-delimiting encodings
-- statement:
--   Finite binary strings are lists of bits; a word of width $n$ is a function from $\{0,\ldots,n-1\}$ to $\{0,1\}$. There is one word of width zero. Conversion lists coordinates in increasing order. Natural values use canonical little-endian binary, framed by a unary payload-length prefix and a zero delimiter. Tuple codes concatenate framed components; parsers return failure on incomplete or noncanonical codes.
--
--   The integer logarithms are exact:
--   $$\operatorname{floorLog2}(n)=\lfloor\log_2 n\rfloor,\qquad \operatorname{ceilLog2}(n)=\lceil\log_2 n\rceil\quad(n>0).$$
--   In particular, both logarithms of 1 are zero. Values at zero follow Mathlib's natural logarithm conventions and never specify the positive SSLB threshold's logarithm. These codecs fix a uniform binary input convention for every subsequent computational definition.
-- source:
--   Zeyong Li, STOC 2027 submission #502 (October 2026), §2 preamble, printed p.9 (PDF p.11), §2.2, printed pp.10–11 (PDF pp.12–13), and Definition 3.1, printed p.14 (PDF p.16); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/502.pdf

import Mathlib

/-! Binary encodings for Li, STOC 2027 submission #502, §§2–3 (printed pp.9–18).
Lengths are framed in unary; natural values themselves are canonical binary.
The framing costs twice the payload length plus one, not the value of the natural.
-/
namespace AMRangeAvoid.Characterization

abbrev Bits := List Bool
abbrev Word (n : ℕ) := Fin n → Bool

def wordBits {n : ℕ} (w : Word n) : Bits := List.ofFn w

def bitsWord (n : ℕ) (b : Bits) : Word n := fun i => b.getD i false

/-- Little-endian evaluation, including the empty word representing zero. -/
def bitsNat : Bits → ℕ
  | [] => 0
  | b :: bs => b.toNat + 2 * bitsNat bs

/-- A self-delimiting block: one 1 per payload bit, then 0, then the payload. -/
def frame (b : Bits) : Bits := List.replicate b.length true ++ [false] ++ b

def readUnary : Bits → Option (ℕ × Bits)
  | [] => none
  | false :: bs => some (0, bs)
  | true :: bs => do
    let (n, rest) ← readUnary bs
    pure (n + 1, rest)

def readFrame (b : Bits) : Option (Bits × Bits) := do
  let (n, rest) ← readUnary b
  if n ≤ rest.length then pure (rest.take n, rest.drop n) else none

def natCode (n : ℕ) : Bits := frame n.bits

def readNat (b : Bits) : Option (ℕ × Bits) := do
  let (payload, rest) ← readFrame b
  let n := bitsNat payload
  if n.bits = payload then pure (n, rest) else none

/-- A tuple is encoded by concatenating its framed components. -/
def tupleCode (bs : List Bits) : Bits := (bs.map frame).flatten

/-- Read a fixed number of components; failure stops immediately. -/
def readFrames : ℕ → Bits → Option (List Bits × Bits)
  | 0, b => some ([], b)
  | n + 1, b => do
    let (a, rest) ← readFrame b
    let (as, tail) ← readFrames n rest
    pure (a :: as, tail)

/-- Exact integer logs. In particular ceilLog2 1 = 0. -/
def floorLog2 (n : ℕ) : ℕ := Nat.log 2 n

def ceilLog2 (n : ℕ) : ℕ := Nat.clog 2 n

end AMRangeAvoid.Characterization


