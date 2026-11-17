-- Prove2me | Definitions.Def_ArgmaxDeFinetti_Supplement_BitMachine
-- name    : ArgmaxDeFinetti_Supplement_BitMachine
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:41:50.172026+00:00
-- url     : https://prove2.me/theorems/c3b44d22-b165-40a7-883e-94509dd16472
-- title:
--   Bit-model Turing machines, binary input encodings and the running-time bound $\exp(O((\sqrt d/\varepsilon)\log(2+\varepsilon\sqrt d)))$
-- statement:
--   The algorithmic statements of the paper (Theorems 5.2 and 5.4) are read in the standard **bit model**. An algorithm is a deterministic Turing machine (a finite multi-stack machine) whose input and output alphabets are $\{0,1\}$; it computes an output $y$ from an input $x$ within $T$ steps if, started with $x$ on its input stack, it halts after at most $T$ steps with $y$ on its output stack.
--
--   Numbers are encoded in binary: a natural number by its binary digits, each preceded by a flag bit, and a terminator; an integer by a sign bit and its absolute value; a rational number by its numerator and denominator in lowest terms; a complex rational $x+iy$ by $x$ and $y$; an explicitly given operator on $\mathbb C^d\otimes\mathbb C^d$ by its $d^4$ entries row by row.
--
--   The running-time bound is
--
--   $$
--   (B+2)^k\cdot\exp\!\Big(C\,\frac{\sqrt d}{\varepsilon}\log\big(2+\varepsilon\sqrt d\big)\Big),
--   $$
--
--   a polynomial in the input bit length $B$ times the subexponential factor of (5.10) and (5.16), with absolute constants $C,k$.
--
--   **Formalization Note** The paper names no machine model; this is a reading. The machine is Mathlib's `Turing.FinTM2`; every symbol it writes is determined by its finite state, so it works over a finite alphabet. The logarithm is natural.
-- source:
--   Jeronimo, Wu, Xu, Optimal Quantum de Finetti Theorems via Argmax Rounding, arXiv:2608.02590 (held version, sha256 fb339472…), Theorems 5.2 and 5.4, pp.38–40; Theorems 1.7–1.8, pp.9–10 ("polynomial in the input bit complexity")

import Mathlib

open Matrix

namespace ArgmaxDeFinetti

namespace Supplement

/-- A deterministic Turing machine with binary input and output alphabets: a Mathlib finite multi-stack machine
`Turing.FinTM2` together with identifications of its input and output stack alphabets with `Bool`.
Model of computation for the running-time statements of Jeronimo, Wu, Xu, *Optimal Quantum de Finetti Theorems via Argmax Rounding*, arXiv:2608.02590 (held version, sha256 fb339472…), Theorems 5.2 and 5.4, pp.38–40 (and
Theorems 1.7–1.8, pp.9–10: "polynomial in the input bit complexity").

**Formalization Note** The paper names no machine model; a deterministic Turing machine over a finite alphabet with
binary input and output is the standard bit model. Every symbol the machine can write is determined by its finite
state, so it computes over a finite alphabet. -/
structure BitMachine where
  /-- the underlying finite multi-stack Turing machine -/
  tm : Turing.FinTM2
  /-- the input alphabet is `{0, 1}` -/
  inAlph : tm.Γ tm.k₀ ≃ Bool
  /-- the output alphabet is `{0, 1}` -/
  outAlph : tm.Γ tm.k₁ ≃ Bool

/-- The machine, started on the binary input `x`, halts with the binary output `y` within `T` steps
(Mathlib's `Turing.TM2OutputsInTime`: from the initial configuration with `x` on the input stack it reaches, after
at most `T` steps, the halting configuration with `y` on the output stack and every other stack empty). -/
def BitMachine.OutputsWithin (A : BitMachine) (x y : List Bool) (T : ℕ) : Prop :=
  Nonempty (Turing.TM2OutputsInTime A.tm (x.map A.inAlph.symm) (some (y.map A.outAlph.symm)) T)

/-- Self-delimiting binary encoding of a natural number: its binary digits (least significant first, as
`Nat.bits`), each preceded by the flag `1`, followed by the terminator `0`. Its length is `2⌈log₂(n+1)⌉ + 1`. -/
def encNat (n : ℕ) : List Bool :=
  (Nat.bits n).flatMap (fun b => [true, b]) ++ [false]

/-- Binary encoding of an integer: a sign bit, then the encoding of its absolute value. -/
def encInt (z : ℤ) : List Bool :=
  decide (z < 0) :: encNat z.natAbs

/-- Binary encoding of a rational number: its signed numerator and its positive denominator (in lowest terms). -/
def encRat (q : ℚ) : List Bool :=
  encInt q.num ++ encNat q.den

/-- The complex number `x + iy` with rational real and imaginary parts `z = (x, y)`. -/
def ratC (z : ℚ × ℚ) : ℂ :=
  ⟨(z.1 : ℝ), (z.2 : ℝ)⟩

/-- The list of indices `(i, j) ∈ [d] × [d]` in lexicographic order. -/
def pairList (d : ℕ) : List (Fin d × Fin d) :=
  (List.finRange d).flatMap (fun i => (List.finRange d).map (fun j => (i, j)))

/-- Binary encoding of an explicitly given operator on `ℂ^d ⊗ ℂ^d` with complex-rational entries: the entries row by
row in lexicographic order of the index pairs, each as its real part and then its imaginary part (`encRat`). -/
def encMat {d : ℕ} (M : Matrix (Fin d × Fin d) (Fin d × Fin d) (ℚ × ℚ)) : List Bool :=
  (pairList d).flatMap (fun p => (pairList d).flatMap (fun q => encRat (M p q).1 ++ encRat (M p q).2))

/-- The running-time bound `(B + 2)^k · exp(C · (√d/ε) · log(2 + ε√d))`: a polynomial of degree `k` in the input
bit length `B` times `exp(O((√d/ε) log(2 + ε√d)))`, Jeronimo, Wu, Xu, *Optimal Quantum de Finetti Theorems via Argmax Rounding*, arXiv:2608.02590 (held version, sha256 fb339472…), eqs. (5.10) and (5.16), pp.38, 40.

**Formalization Note** `log` is the natural logarithm (another base changes only `C`). `C` and `k` are
quantified in each theorem before `d`, `ε` and the input. -/
noncomputable def subexpBound (C : ℝ) (k : ℕ) (B d : ℕ) (ε : ℝ) : ℝ :=
  ((B : ℝ) + 2) ^ k * Real.exp (C * (Real.sqrt d / ε) * Real.log (2 + ε * Real.sqrt d))

end Supplement

end ArgmaxDeFinetti


