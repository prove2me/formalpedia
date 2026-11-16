-- Prove2me | Definitions.Def_QAdvFew_PoQOracle_Supplement_Layout
-- name    : QAdvFew_PoQOracle_Supplement_Layout
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:11:16.314993+00:00
-- url     : https://prove2.me/theorems/57df5a11-f34d-4e33-af1c-2342bb04e4c7
-- title:
--   Register layout helpers
-- statement:
--   Registers are tensor products $\mathcal H(\{0,1\}^a)\otimes\mathcal H(\{0,1\}^b)$; a computational-basis string of $a+b$ qubits is the concatenation of its first $a$ and last $b$ bits. This module fixes the bookkeeping: splitting a basis string into its two parts, the tensor product $|\psi\rangle\otimes|\varphi\rangle$ of amplitude vectors, padding with zeros, a self-delimiting binary code $\mathrm{bnat}(k)$ of a natural number (each binary digit $b$ written as $1b$, then a $0$), the number $\sum_i x_i2^i$ with binary digits $x$, the low $k$ binary digits of a number, and reading a block of $\ell$ bits at a given offset.
--
--   These conventions are used by every later definition of the supplement; in particular, circuit sizes are description lengths written with $\mathrm{bnat}$.
-- source:
--   Goldin, Lombardi, Morimae, Quantum Advantage has Few Complexity Implications, arXiv:2611.05303v1, §3.2.1, p. 12 (PDF p. 14); §3.3, p. 16 (PDF p. 18); §5.1–5.2, pp. 32–34 (PDF pp. 34–36)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Complexity

open QAlgorithms.Complexity

namespace QAdvFew.PoQOracle.Supplement

/-- Bit-string layout helpers for registers (Goldin, Lombardi, Morimae, *Quantum Advantage has Few
Complexity Implications*, arXiv:2611.05303v1, §3.2.1, p. 12 (PDF p. 14); §3.3 and §5.1,
pp. 16, 32–34 (PDF pp. 18, 34–36), where registers are written as tensor products
`H({0,1}^a) ⊗ H({0,1}^b)`). A basis string of `a + b` qubits is the concatenation `Fin.append` of
its first `a` and last `b` bits; `lft` and `rgt` read the two parts back. -/
def lft {a b : ℕ} (z : Bits (a + b)) : Bits a := fun i => z (Fin.castAdd b i)

/-- The last `b` bits of a basis string of `a + b` qubits. -/
def rgt {a b : ℕ} (z : Bits (a + b)) : Bits b := fun j => z (Fin.natAdd a j)

/-- The tensor product `|ψ⟩ ⊗ |φ⟩` of amplitude vectors on `a` and `b` qubits. -/
def tensorState {a b : ℕ} (ψ : QState a) (φ : QState b) : QState (a + b) :=
  fun z => ψ (lft z) * φ (rgt z)

/-- The bits of `x` followed by `k` zeros. -/
def padZeros {a : ℕ} (k : ℕ) (x : Bits a) : Bits (a + k) := Fin.append x (fun _ => false)

/-- A self-delimiting binary code of a natural number, used in circuit descriptions: each binary
digit `b` of `k` (least significant first, `Nat.bits`) is written as `1b`, and the code ends with
`0`. Its length is `2⌈log₂(k+1)⌉ + 1`. -/
def bnat (k : ℕ) : Str := (Nat.bits k).flatMap (fun b => [true, b]) ++ [false]

/-- A self-delimiting code of a bit string: each bit `b` written as `1b`, then `0`. -/
def bstr (s : Str) : Str := s.flatMap (fun b => [true, b]) ++ [false]

/-- The number with binary digits `x` (bit `i` has weight `2^i`). -/
def bitsToNat {k : ℕ} (x : Bits k) : ℕ := ∑ i : Fin k, if x i then 2 ^ (i : ℕ) else 0

/-- The `k` low binary digits of `a`. -/
def natToBits (k a : ℕ) : Bits k := fun i => a.testBit i

/-- The `len` bits of `z` starting at position `off` (positions at or beyond the end read `0`). -/
def rd {N : ℕ} (z : Bits N) (off len : ℕ) : Bits len :=
  fun j => if h : off + j < N then z ⟨off + j, h⟩ else false

/-- The bits of `z` as a string. -/
def toStr {k : ℕ} (z : Bits k) : Str := List.ofFn z

end QAdvFew.PoQOracle.Supplement


