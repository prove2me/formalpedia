-- Prove2me | Definitions.Def_BipHamCount_Deterministic_Arithmetic
-- name    : BipHamCount_Deterministic_Arithmetic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T13:47:15.740202+00:00
-- url     : https://prove2.me/theorems/673d0e16-bb37-4bb9-a29f-cf71e74c110a
-- title:
--   Bit-charged integer arithmetic, coefficient arrays and Berkowitz
-- statement:
--   Instrumented computations return a value and a natural-number cost. Integer addition, subtraction and multiplication on $a,b$ cost $(\operatorname{size}|a|+\operatorname{size}|b|+1)^2$, while comparison with zero costs $\operatorname{size}|a|+1$. Coefficient arrays, with the constant coefficient first and missing coefficients zero, implement $\mathbb Z[x]$ addition, negation and convolution through these integer primitives.
--
--   The division-free Berkowitz routine recursively computes characteristic coefficients using lower triangular Toeplitz factors and returns the signed constant coefficient, hence a determinant. It has actual program bodies over integers and coefficient arrays; its operation interface contains no correctness or cost assumptions. Buffer reads, writes and loops are charged. The empty determinant returns one.
--
--   Only the generic counter from the published Work module is used. That module's real-RAM docstring is not the cost convention of this development. Correctness and polynomial bit-cost of these implementations remain proof obligations of the program milestones.
-- source:
--   Koana, Kumabe, Counting Hamiltonian Cycles in Bipartite Digraphs Deterministically in O(1.9526^n) Time, STOC 2027 submission #814 (October 2026), §4.1 p.7; Lemma 4.4 pp.8–9; Berkowitz 1984, DOI 10.1016/0020-0190(84)90018-8. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/814.pdf

import Mathlib
import Definitions.Def_CapacitatedAssort_General_Work

open CapacitatedAssort.General

namespace BipHamCount.Deterministic

/-! Bit-charged arithmetic for §4, pp.6–9. Only the generic Work counter is reused.
The imported module's unit-cost real-RAM convention is NOT adopted. Integer arithmetic
uses (size |a| + size |b| + 1)²; a sign/zero test costs size |a|+1.
Arrays use charged reads, writes and loop dispatch; all coefficient arithmetic is explicit. -/

/-- Integer addition with the BRIEF bit charge (§4, pp.6–9). -/
def zadd (a b : ℤ) : Work ℤ := do
  charge ((Nat.size a.natAbs + Nat.size b.natAbs + 1)^2)
  return a + b

/-- Integer subtraction with the same bit charge (§4). -/
def zsub (a b : ℤ) : Work ℤ := do
  charge ((Nat.size a.natAbs + Nat.size b.natAbs + 1)^2)
  return a - b

/-- Integer multiplication with the same conservative bit charge (§4). -/
def zmul (a b : ℤ) : Work ℤ := do
  charge ((Nat.size a.natAbs + Nat.size b.natAbs + 1)^2)
  return a * b

/-- Sign/zero comparison charge (§4); returns the exact ordering against zero. -/
def zcmp (a : ℤ) : Work Ordering := do
  charge (Nat.size a.natAbs + 1)
  return compare a 0

/-- Sign of a natural exponent; includes the parity computation (§4, p.9). -/
def paritySign (e : ℕ) : Work ℤ := do
  charge ((Nat.size e + 1)^2)
  return if e % 2 = 0 then 1 else -1

/-- Coefficient arrays for ℤ[x], constant coefficient first, p.9. Trailing zeros are allowed. -/
abbrev ZPoly := Array ℤ

/-- Coefficient-array addition, p.9. Missing coefficients are zero. -/
def padd (a b : ZPoly) : Work ZPoly := do
  let d := max a.size b.size
  charge (4*d+1)
  let mut out := #[]
  for i in List.range d do
    charge 4
    let c ← zadd (a[i]?.getD 0) (b[i]?.getD 0)
    out := out.push c
  return out

/-- Coefficient-array negation through bit-charged integer subtraction, p.9. -/
def pneg (a : ZPoly) : Work ZPoly := do
  charge (4*a.size+1)
  let mut out := #[]
  for x in a do
    charge 2
    let c ← zsub 0 x
    out := out.push c
  return out

/-- Schoolbook coefficient convolution, p.9. No uncharged polynomial multiplication. -/
def pmul (a b : ZPoly) : Work ZPoly := do
  charge (4*(a.size+b.size+1))
  let mut out := Array.replicate (a.size+b.size) (0 : ℤ)
  for i in List.range a.size do
    charge (4*b.size+1)
    for j in List.range b.size do
      charge 6
      let c ← zmul (a[i]?.getD 0) (b[j]?.getD 0)
      let s ← zadd (out[i+j]?.getD 0) c
      out := out.set! (i+j) s
  return out

/-- Ring operation implementations, with no correctness or cost theorem hidden in fields.
Used to run the same division-free routine over ℤ and coefficient arrays, p.9. -/
structure RingOps (R : Type) where
  zero : R
  one : R
  add : R → R → Work R
  mul : R → R → Work R
  neg : R → Work R

/-- Bit arithmetic for integer determinants in §4.1, p.7. -/
def intOps : RingOps ℤ := ⟨0, 1, zadd, zmul, zsub 0⟩

/-- Coefficient arithmetic for Q(x) in Lemma 4.4, p.9. -/
def polyOps : RingOps ZPoly := ⟨#[], #[1], padd, pmul, pneg⟩

/-- Charged dense matrix read; a malformed buffer returns the supplied zero. -/
def matRead {R : Type} (O : RingOps R) (M : Array (Array R)) (i j : ℕ) : Work R := do
  charge 2
  return ((M[i]?.getD #[])[j]?).getD O.zero

/-- Berkowitz characteristic coefficients, leading coefficient first, p.9 [Ber84].
For a block [a R; C M], the lower triangular Toeplitz column is
(1, −a, −RC, −RMC, …); multiply it by the characteristic vector of M.
`off` selects the trailing principal block, so recursive calls do not copy matrices. -/
def berkCoeffs {R : Type} (O : RingOps R) (M : Array (Array R)) :
    ℕ → ℕ → Work (Array R)
  | 0, _ => do
      charge 1
      return #[O.one]
  | n+1, off => do
      charge 4
      let p ← berkCoeffs O M n (off+1)
      let a ← matRead O M off off
      let na ← O.neg a
      let mut t := #[O.one, na]
      let mut vec := #[]
      charge (4*n+1)
      for j in List.range n do
        charge 2
        let x ← matRead O M (off+1+j) off
        vec := vec.push x
      charge (4*n+1)
      for l in List.range n do
        charge (4*n+1)
        let mut s := O.zero
        for j in List.range n do
          charge 3
          let r ← matRead O M off (off+1+j)
          let z ← O.mul r (vec[j]?.getD O.zero)
          s ← O.add s z
        let ns ← O.neg s
        charge 1
        t := t.push ns
        if l+1 < n then
          let mut next := #[]
          charge (4*n+1)
          for i in List.range n do
            charge (4*n+1)
            let mut u := O.zero
            for j in List.range n do
              charge 3
              let b ← matRead O M (off+1+i) (off+1+j)
              let z ← O.mul b (vec[j]?.getD O.zero)
              u ← O.add u z
            charge 1
            next := next.push u
          vec := next
      let mut out := #[]
      charge (4*(n+2)+1)
      for i in List.range (n+2) do
        let mut s := O.zero
        charge (4*(min i n+1)+1)
        for j in List.range (min i n+1) do
          charge 4
          let z ← O.mul (t[i-j]?.getD O.zero) (p[j]?.getD O.zero)
          s ← O.add s z
        charge 1
        out := out.push s
      return out

/-- Division-free determinant by Berkowitz, §4.1 p.7 and Lemma 4.4 p.9.
No Matrix.det or permanent is evaluated by this program. -/
def berkowitz {R : Type} (O : RingOps R) (n : ℕ) (M : Array (Array R)) : Work R := do
  let p ← berkCoeffs O M n 0
  charge (Nat.size n + 3)
  let x := p[n]?.getD O.zero
  if n % 2 = 0 then return x else O.neg x

end BipHamCount.Deterministic


