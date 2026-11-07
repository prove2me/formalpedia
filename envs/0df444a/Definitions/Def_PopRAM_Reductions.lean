-- Prove2me | Definitions.Def_PopRAM_Reductions
-- name    : PopRAM_Reductions
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:22:23.570295+00:00
-- url     : https://prove2.me/theorems/0081a2b3-cfa1-493b-b00e-545de7c12d82
-- title:
--   Reduction of RAM instructions to GET and PUT (Table 3, Protocols 1, 2, 4–9)
-- statement:
--   The register file is a map from register indices to $w$-bit words. The two **atomic subroutines** are $\mathrm{PUT}(r,i,b)$, which sets bit $i$ of register $r$ to $b$, and $\mathrm{GET}(r,i)$, which returns it (Table 2). Every RAM instruction is emulated by a sequence of such calls:
--
--   1. $\mathrm{SET}(r,r_p)$ (Protocol 1): $r\leftarrow0$; for $i=0,\dots,w-1$: $b\leftarrow\mathrm{GET}(r_p,i)$; if $b=1$ and $r+2^i\ge a_{\max}$ return InvalidAddress; $r\leftarrow r+2^ib$;
--   2. direct $\mathrm{COPY}(r_s,r_d)$ (Protocol 2): bitwise GET then PUT;
--   3. $\mathrm{JGE}(r,I_z)$ (Protocol 4): one GET of the sign bit $w-1$;
--   4. $\mathrm{LOAD}(C,r_d)$ (Protocol 5): PUT of the $w$ bits of $C$;
--   5. the indirect COPYs (Protocols 6, 7): SET, then a direct copy;
--   6. $\mathrm{ADD}$, $\mathrm{SUB}$ (Protocols 8, 9): bitwise with a carry, SUB via $a-b=a+\neg b+1$;
--   7. $\mathrm{INC}(r)$, $\mathrm{DEC}(r)$: ADD and SUB with the constant $1$ as second operand.
--
--   The emulation counts the calls of GET and PUT. `ramSpec` is the word-level meaning of the same instruction: arithmetic modulo $2^w$, JGE on the signed value, and an indirect address valid iff its signed value lies in $\{0,\dots,a_{\max}-1\}$.
-- source:
--   Gąsieniec, Grodzicki, Stachowiak, Efficient Stable Word-RAM Simulation by Population Protocols, arXiv:2611.06178 (preprint, held version, sha256 f13223b33593e77d2342fbfab2d49c58efd6035c06f316456f76030e0dca9acd), §2.2, pp.8–9 (PDF pp.9–10), Tables 2–3, Protocols 1–2; App. A.5, pp.15–17 (PDF pp.16–18), Protocols 4–9

import Mathlib

set_option autoImplicit false

namespace PopRAM

/-! # Reduction of RAM instructions to the atomic subroutines GET and PUT (§2.2, App. A.5)

Gąsieniec, Grodzicki, Stachowiak, *Efficient Stable Word-RAM Simulation by Population Protocols*,
arXiv:2611.06178 (held version, sha256 f13223b3…), §2.2, pp.8–9 (PDF pp.9–10): Table 2 (`PUT(r, i, b)`
sets the i-th bit of register r to b; `GET(r, i)` returns it), Protocols 1 (SET) and 2 (direct
COPY), Table 3; App. A.5, pp.15–17 (PDF pp.16–18): Protocols 4 (JGE), 5 (LOAD), 6–7 (indirect
COPYs), 8 (ADD), 9 (SUB); INC and DEC are "emulated as ADD and SUB with the second operand replaced
by the constant 1, encoded in the transition function" (p.9).

**Formalization Note**
- The register file is `regs : ℕ → BitVec w`; bit `i` is `getLsbD i` (bit `0` least significant,
  bit `w − 1` the U2 sign bit). Each reduction runs in a state monad that also counts the calls of
  `GET` and `PUT` (`calls`).
- `SET amax rp` follows Protocol 1 literally: `r ← 0`; for `i = 0, …, w − 1`: `b ← GET(rp, i)`; if
  `b = 1` and `r + 2^i ≥ amax` return `InvalidAddress` (`none`); `r ← r + 2^i b`.
- ADD and SUB follow Protocols 8 and 9 bit by bit with a carry (SUB starts with carry 1 and uses
  `1 − b₂`); INC/DEC replace the second operand by the constant `1` and so use `2w` calls.
- `reduce amax ip I` emulates instruction `I` at instruction pointer `ip` and returns the next `ip`,
  or `none` for `InvalidAddress`.
- `ramSpec amax ip F I` is the reference semantics of the same instruction on whole words: `BitVec`
  arithmetic mod `2^w`, `LOAD` writes `BitVec.ofInt w C`, `JGE` tests `toInt ≥ 0`, an indirect
  address is valid iff its signed value lies in `[0, amax)`. -/

/-- The RAM instructions of Table 3 (including INC and DEC). -/
inductive RamInstr where
  | load (c : ℤ) (rd : ℕ)
  | add (rs1 rs2 rd : ℕ)
  | sub (rs1 rs2 rd : ℕ)
  | copyInd (rp rd : ℕ)
  | storeInd (rs rp : ℕ)
  | jge (r z : ℕ)
  | inc (r : ℕ)
  | dec (r : ℕ)
  deriving DecidableEq

/-- The register file together with the number of atomic subroutine calls so far. -/
structure RF (w : ℕ) where
  regs : ℕ → BitVec w
  calls : ℕ

/-- Computations on the register file. -/
abbrev RM (w : ℕ) := StateM (RF w)

/-- `x` with bit `i` set to `b`. -/
def setBit {w : ℕ} (x : BitVec w) (i : ℕ) (b : Bool) : BitVec w :=
  if b then x ||| BitVec.twoPow w i else x &&& ~~~(BitVec.twoPow w i)

/-- `GET(r, i)`: the `i`-th bit of register `r` (one call). -/
def GET {w : ℕ} (r i : ℕ) : RM w Bool :=
  modifyGet fun s => ((s.regs r).getLsbD i, { s with calls := s.calls + 1 })

/-- `PUT(r, i, b)`: set the `i`-th bit of register `r` to `b` (one call). -/
def PUT {w : ℕ} (r i : ℕ) (b : Bool) : RM w Unit :=
  modify fun s =>
    { regs := Function.update s.regs r (setBit (s.regs r) i b), calls := s.calls + 1 }

/-- Protocol 1, `SET(r, rp)`: the index stored in `rp`, or `InvalidAddress` (`none`). -/
def SET {w : ℕ} (amax rp : ℕ) : RM w (Option ℕ) := do
  let mut r := 0
  for i in List.range w do
    let b ← GET rp i
    if b && decide (amax ≤ r + 2 ^ i) then return none
    r := r + (if b then 2 ^ i else 0)
  return some r

/-- Protocol 2, direct `COPY(rs, rd)`. -/
def COPYd {w : ℕ} (rs rd : ℕ) : RM w Unit := do
  for i in List.range w do
    let b ← GET rs i
    PUT rd i b

/-- Protocol 5, `LOAD(C, rd)`. -/
def LOADr {w : ℕ} (c : ℤ) (rd : ℕ) : RM w Unit := do
  for i in List.range w do
    PUT rd i ((BitVec.ofInt w c).getLsbD i)

/-- Protocol 8, `ADD(rs1, rs2, rd)`. -/
def ADDr {w : ℕ} (rs1 rs2 rd : ℕ) : RM w Unit := do
  let mut carry := 0
  for i in List.range w do
    let b1 ← GET rs1 i
    let b2 ← GET rs2 i
    let s := b1.toNat + b2.toNat + carry
    carry := s / 2
    PUT rd i (decide (s % 2 = 1))

/-- Protocol 9, `SUB(rs1, rs2, rd)`, via `a − b = a + ¬b + 1`. -/
def SUBr {w : ℕ} (rs1 rs2 rd : ℕ) : RM w Unit := do
  let mut carry := 1
  for i in List.range w do
    let b1 ← GET rs1 i
    let b2 ← GET rs2 i
    let s := b1.toNat + (1 - b2.toNat) + carry
    carry := s / 2
    PUT rd i (decide (s % 2 = 1))

/-- `INC(r)`: ADD with the second operand the constant `1` (bit `i` of `1` is `[i = 0]`). -/
def INCr {w : ℕ} (r : ℕ) : RM w Unit := do
  let mut carry := 0
  for i in List.range w do
    let b1 ← GET r i
    let s := b1.toNat + (if i = 0 then 1 else 0) + carry
    carry := s / 2
    PUT r i (decide (s % 2 = 1))

/-- `DEC(r)`: SUB with the second operand the constant `1`. -/
def DECr {w : ℕ} (r : ℕ) : RM w Unit := do
  let mut carry := 1
  for i in List.range w do
    let b1 ← GET r i
    let s := b1.toNat + (1 - (if i = 0 then 1 else 0)) + carry
    carry := s / 2
    PUT r i (decide (s % 2 = 1))

/-- Protocol 4, `JGE(r, z)`: the next instruction pointer. -/
def JGEr {w : ℕ} (r z ip : ℕ) : RM w ℕ := do
  let b ← GET r (w - 1)
  return if b then ip + 1 else z

/-- The reduction of a RAM instruction (Table 3): the next `ip`, or `none` for `InvalidAddress`. -/
def reduce {w : ℕ} (amax ip : ℕ) : RamInstr → RM w (Option ℕ)
  | .load c rd => do LOADr c rd; return some (ip + 1)
  | .add rs1 rs2 rd => do ADDr rs1 rs2 rd; return some (ip + 1)
  | .sub rs1 rs2 rd => do SUBr rs1 rs2 rd; return some (ip + 1)
  | .copyInd rp rd => do
      match ← SET amax rp with
      | none => return none
      | some r => do COPYd r rd; return some (ip + 1)
  | .storeInd rs rp => do
      match ← SET amax rp with
      | none => return none
      | some r => do COPYd rs r; return some (ip + 1)
  | .jge r z => do let ip' ← JGEr r z ip; return some ip'
  | .inc r => do INCr r; return some (ip + 1)
  | .dec r => do DECr r; return some (ip + 1)

/-- The register index denoted by a word, if its signed value lies in `[0, amax)`. -/
def validAddr {w : ℕ} (amax : ℕ) (x : BitVec w) : Option ℕ :=
  if 0 ≤ x.toInt ∧ x.toInt < amax then some x.toInt.toNat else none

/-- Reference semantics of a RAM instruction on whole words: the new register file and `ip`, or
`none` for an invalid indirect address. -/
def ramSpec {w : ℕ} (amax ip : ℕ) (F : ℕ → BitVec w) : RamInstr → Option ((ℕ → BitVec w) × ℕ)
  | .load c rd => some (Function.update F rd (BitVec.ofInt w c), ip + 1)
  | .add rs1 rs2 rd => some (Function.update F rd (F rs1 + F rs2), ip + 1)
  | .sub rs1 rs2 rd => some (Function.update F rd (F rs1 - F rs2), ip + 1)
  | .copyInd rp rd =>
      (validAddr amax (F rp)).map fun a => (Function.update F rd (F a), ip + 1)
  | .storeInd rs rp =>
      (validAddr amax (F rp)).map fun a => (Function.update F a (F rs), ip + 1)
  | .jge r z => some (F, if 0 ≤ (F r).toInt then z else ip + 1)
  | .inc r => some (Function.update F r (F r + 1), ip + 1)
  | .dec r => some (Function.update F r (F r - 1), ip + 1)

end PopRAM


