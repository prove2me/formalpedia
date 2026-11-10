-- Prove2me | Definitions.Def_FineGrainedEF_Main_IntCircuits
-- name    : FineGrainedEF_Main_IntCircuits
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T01:09:36.440638+00:00
-- url     : https://prove2.me/theorems/e99d9243-6f84-44dc-9c97-51ecfda1673b
-- title:
--   Integer circuit primitives of A.1: ADD, AddInt, Neg, SubInt, Abs, MulInt, shifts, literals and carry resolution
-- statement:
--   Words are bit strings, least significant bit first; signed words use two's complement (p. 43).
--
--   - **ADD** (ripple-carry adder): for unsigned strings of lengths $r,s$, output length $\max(r,s)+1$, missing bits zero, $\gamma_0:=0$, $d_j:=(a_j\oplus b_j)\oplus\gamma_j$, $\gamma_{j+1}:=((a_jb_j)\vee(a_j\gamma_j))\vee(b_j\gamma_j)$, last output bit the last carry.
--   - **Zero/sign extension**: wiring to a fresh constant zero / copies of the sign bit.
--   - **AddInt**: sign-extend both inputs to $\max(r,s)+1$ bits and apply the ripple gates; $\max(r,s)+1$ output bits.
--   - **Neg**: extend by one sign bit, complement, add the constant one with the ripple gates; $r+1$ bits.
--   - **SubInt**: $\mathrm{AddInt}$-style ripple sum of the first input and $\mathrm{Neg}$ of the second, both sign-extended to $\max(r,s)+1$ bits.
--   - **Abs**: $\mathrm{Mux}(\text{sign},\mathrm{Neg}(x),x\text{ sign-extended to }r+1)$; $r+1$ bits.
--   - **MulInt**: unsigned partial products of $|x|$ ($r+1$ bits) and $|y|$ ($s+1$ bits), row $i$ shifted left by $i$, summed by a balanced tree of ADD ripple adders (split at $\lceil k/2\rceil$ rows); the low $r+s$ bits $P$ of the sum are kept (the product of the magnitudes is at most $2^{r+s-2}$) and the sign restored by $\mathrm{Mux}(\mathrm{sign}\,x\oplus\mathrm{sign}\,y,\ \mathrm{Neg}(P)\text{ low }r+s\text{ bits},\ P)$; $r+s$ output bits.
--   - **Shifts**: $2^kx$ appends $k$ hardwired low zeros; $\lfloor x/2^k\rfloor$ is the right shift with sign extension; $x\bmod 2^k$ the low $k$ bits (a single zero for $k=0$).
--   - **Literals** (p. 47): an integer literal has the least sufficient two's-complement width, at least two bits.
--   - **Carry** (pp. 44–45): with $w$ the common (largest) coefficient width after sign extension, $\kappa_0:=0$, $h_j:=\mathrm{AddInt}(a_j,\kappa_j)$ ($w+1$ bits), $b_j:=h_j\bmod 2$, $\kappa_{j+1}:=\lfloor h_j/2\rfloor$ kept at $w$ bits (bits $h_1,\dots,h_w$). The output is $b=\mathrm{Carry}(a)=(b_0,\dots,b_{m-1})$; the carries $\kappa_0,\dots,\kappa_m$ are auxiliary outputs, and $\sum_j a_j2^j=\sum_j b_j2^j+2^m\kappa_m$.
--
--   **Formalization Note.** `ripple`, `ADD`, `addInt`, `negInt`, `subInt`, `signBit`, `absInt`, `shl`, `addTreeAux`, `mulInt`, `floorPow2`, `modPow2`, `litWidth`, `intConst`, `intLit`, `carryChain`, `carry` (returning the output bits and the list $\kappa_0,\dots,\kappa_m$). The paper leaves the bracketing of MulInt's balanced adder tree, the truncation to $r+s$ bits and the exact form of "add one" in Neg implicit; these are pinned as described.
-- source:
--   Krapivin, Li, Shi, Fine-Grained Proof Complexity for Elementary Arithmetic in Extended Frege, STOC 2027 submission (manuscript sha256 704dfb8a…), pp. 43-45, §A.1 (ADD p. 43; AddInt, Neg, SubInt, Abs, MulInt, shifts p. 44; Carry pp. 44-45), literals p. 47

import Mathlib
import Definitions.Def_FineGrainedEF_Main_EF
import Definitions.Def_FineGrainedEF_Main_BoolCircuits

namespace FineGrainedEF.Main

/-- The ripple-carry gates (p. 43) on two equal-length words `a, b` with incoming carry `γ`:
`d_j := (a_j ⊕ b_j) ⊕ γ_j`, `γ_{j+1} := ((a_j ∧ b_j) ∨ (a_j ∧ γ_j)) ∨ (b_j ∧ γ_j)`. Returns the
sum bits and the last carry. -/
def ripple : List ℕ → List ℕ → ℕ → Build (List ℕ × ℕ)
  | a :: as, b :: bs, γ => do
      let t ← xorG a b
      let d ← xorG t γ
      let ab ← andG a b
      let ag ← andG a γ
      let bg ← andG b γ
      let o ← orG ab ag
      let γ' ← orG o bg
      let r ← ripple as bs γ'
      pure (d :: r.1, r.2)
  | _, _, γ => pure ([], γ)

/-- `ADD` (p. 43), the unsigned schoolbook ripple-carry adder: for unsigned strings of lengths
`r, s`, output length `max(r, s) + 1`; missing input bits and `γ_0` are wired to one fresh
constant zero; the last output bit is the last carry. -/
def ADD (a b : List ℕ) : Build (List ℕ) := do
  let w := max a.length b.length
  let z ← zeroG
  let a' := a ++ List.replicate (w - a.length) z
  let b' := b ++ List.replicate (w - b.length) z
  let r ← ripple a' b' z
  pure (r.1 ++ [r.2])

/-- `AddInt` (p. 44): sign-extend both signed inputs to width `max(r, s) + 1` and apply the
ripple-carry gates (incoming carry a fresh constant zero); the signed output keeps the
`max(r, s) + 1` sum bits. -/
def addInt (x y : List ℕ) : Build (List ℕ) := do
  let w := max x.length y.length + 1
  let x' ← signExt w x
  let y' ← signExt w y
  let z ← zeroG
  let r ← ripple x' y' z
  pure r.1

/-- `Neg` (p. 44): extend the signed `r`-bit input by one sign bit, complement the bits, and add
one with the ripple-carry gates (the constant one as an `(r+1)`-bit word); the signed output keeps
`r + 1` bits. -/
def negInt (x : List ℕ) : Build (List ℕ) := do
  let w := x.length + 1
  let x' ← signExt w x
  let c ← x'.mapM notG
  let one ← constWord 1 w
  let z ← zeroG
  let r ← ripple c one z
  pure r.1

/-- `SubInt` (p. 44): negate the second input, sign-extend the first input and the negated second
input to `max(r, s) + 1`, add with the ripple-carry gates; output `max(r, s) + 1` bits. -/
def subInt (x y : List ℕ) : Build (List ℕ) := do
  let ny ← negInt y
  let w := max x.length y.length + 1
  let x' ← signExt w x
  let ny' ← signExt w ny
  let z ← zeroG
  let r ← ripple x' ny' z
  pure r.1

/-- The sign bit (highest bit) of a signed word. -/
def signBit (x : List ℕ) : ℕ := x.getLastD 0

/-- `Abs` (p. 44): the original sign bit selects (by `Mux`) the negated input or the input
sign-extended to `r + 1` bits; output `r + 1` signed bits. -/
def absInt (x : List ℕ) : Build (List ℕ) := do
  let nx ← negInt x
  let x' ← signExt (x.length + 1) x
  mux (signBit x) nx x'

/-- `2^k x` (p. 44): left shift; `k` low bits hardwired to one fresh constant zero (no gate when
`k = 0`); `w + k` output bits. -/
def shl (k : ℕ) (x : List ℕ) : Build (List ℕ) :=
  if k = 0 then pure x
  else do
    let z ← zeroG
    pure (List.replicate k z ++ x)

/-- Balanced tree of `ADD` ripple adders over the unsigned rows (`fuel ≥ rows.length`), split at
`⌈|rows|/2⌉` as for Boolean trees; the empty sum is the one-bit constant zero. -/
def addTreeAux : ℕ → List (List ℕ) → Build (List ℕ)
  | 0, _ => do
      let z ← zeroG
      pure [z]
  | fuel + 1, rows =>
      match rows with
      | [] => do
          let z ← zeroG
          pure [z]
      | [r] => pure r
      | rows => do
          let k := (rows.length + 1) / 2
          let x ← addTreeAux fuel (rows.take k)
          let y ← addTreeAux fuel (rows.drop k)
          ADD x y

/-- `MulInt` (p. 44): for signed inputs of widths `r, s`, form the unsigned partial products of
the absolute values `|x|` (`r + 1` bits) and `|y|` (`s + 1` bits): row `i` is
`(|x|_i ∧ |y|_j)_j` shifted left by `i`; sum the rows with a balanced tree of ripple adders
(`addTreeAux`); keep the low `r + s` bits `P` of the unsigned sum (the product of the magnitudes
is at most `2^{r+s-2}`); restore the sign by conditional negation
`Mux(sign x ⊕ sign y, low_{r+s}(Neg P), P)`. Signed output of `r + s` bits. -/
def mulInt (x y : List ℕ) : Build (List ℕ) := do
  let ax ← absInt x
  let ay ← absInt y
  let rows ← (List.range ax.length).mapM fun i => do
    let row ← ay.mapM fun b => andG (ax.getD i 0) b
    shl i row
  let P ← addTreeAux rows.length rows
  let w := x.length + y.length
  let P' ← zeroExt w P
  let Pw := P'.take w
  let sg ← xorG (signBit x) (signBit y)
  let nP ← negInt Pw
  mux sg (nP.take w) Pw

/-- `⌊x / 2^k⌋` for a signed word (p. 44): right shift with sign extension, `max(w, k)` output
bits (the input is first sign-extended to width `k` if `k > w`). Wiring only. -/
def floorPow2 (k : ℕ) (x : List ℕ) : Build (List ℕ) := do
  let x' ← signExt (max x.length k) x
  pure ((List.range x'.length).map fun j => x'.getD (j + k) (signBit x'))

/-- `x mod 2^k` (p. 44): the low bits `x_0, …, x_{k-1}`, unsigned; for `k = 0` a single
hardwired zero. -/
def modPow2 (k : ℕ) (x : List ℕ) : Build (List ℕ) :=
  if k = 0 then do
    let z ← zeroG
    pure [z]
  else do
    let x' ← signExt (max x.length k) x
    pure (x'.take k)

/-- Least sufficient two's-complement width of an integer literal, at least two bits (p. 47). -/
def litWidth (v : ℤ) : ℕ :=
  max 2 (if 0 ≤ v then Nat.size v.toNat + 1 else Nat.size (-v - 1).toNat + 1)

/-- A hardwired signed constant: the two's-complement bits of `v` at width `w`. -/
def intConst (v : ℤ) (w : ℕ) : Build (List ℕ) :=
  constWord (Int.toNat (v % (2 ^ w : ℤ))) w

/-- An integer literal (p. 47): scale zero, least sufficient signed width, at least two bits. -/
def intLit (v : ℤ) : Build (List ℕ) := intConst v (litWidth v)

/-- Carry-resolution chain of `Carry` from carry `κ`. -/
def carryChain : List (List ℕ) → List ℕ → Build (List ℕ × List (List ℕ))
  | [], κ => pure ([], [κ])
  | a :: as, κ => do
      let h ← addInt a κ
      let b := h.getD 0 0
      let κ' := (h.drop 1).take a.length
      let r ← carryChain as κ'
      pure (b :: r.1, κ :: r.2)

/-- Binary carry resolution `Carry(a)` (pp. 44–45): sign-extend the coefficients to their common
width `w` (the largest entry width), `κ_0 := 0` (`w` hardwired zero bits),
`h_j := AddInt(a_j, κ_j)` (`w + 1` bits), `b_j := h_j mod 2` (the low bit of `h_j`),
`κ_{j+1} := ⌊h_j / 2⌋` kept at `w` bits by omitting the repeated high sign bit (bits
`h_1, …, h_w`). Returns the output bits `(b_0, …, b_{m-1})` and the carries
`(κ_0, …, κ_m)` (the terminal carry `κ_m` is an auxiliary output). -/
def carry (a : List (List ℕ)) : Build (List ℕ × List (List ℕ)) := do
  let w := (a.map List.length).foldl max 0
  let a' ← a.mapM (signExt w)
  let z ← zeroG
  carryChain a' (List.replicate w z)

end FineGrainedEF.Main


