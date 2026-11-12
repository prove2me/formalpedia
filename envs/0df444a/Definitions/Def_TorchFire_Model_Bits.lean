-- Prove2me | Definitions.Def_TorchFire_Model_Bits
-- name    : TorchFire_Model_Bits
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T08:26:58.884188+00:00
-- url     : https://prove2.me/theorems/1a0fa544-bfcb-44bb-9b22-2fd018ed55dd
-- title:
--   Bit strings $\{0,1\}^n$, the ⊥-flag encoding, and padded concatenations
-- statement:
--   Bit strings $\{0,1\}^n$ are functions $\mathrm{Fin}\,n\to\mathbb Z_2$; bitwise XOR $\oplus$ is addition in $\mathbb Z_2$, and the $\mathbb Z_2$-linear algebra of Construction 4.2 (the matrices $A_y$, the vectors $b_y$, $v^{\mathsf T}A_y$) is matrix–vector multiplication over $\mathbb Z_2$.
--
--   A partial value — an oracle answer that may be $\perp$ — is written in the **⊥-flag encoding**: a value $v$ becomes $(0,v)$ and $\perp$ becomes $(1,0)$, a fixed-width string with one flag bit, so no value is ever confused with $\perp$. The module also provides zero-padded writing of a bit list into a register of fixed width, concatenation $x\,\Vert\,y$, and the $w$-digit binary representation $[c]_w$ of a number with leading zeros.
--
--   These are the encodings behind the oracle interfaces of the paper: $P^{-1}$, $O_b$, $O_2$, $N$, $\Gamma$ and $T$ return $\perp$ on bad inputs, and the encodings $\mathrm{enc}$ (21) and $\mathrm{code}$ (44) are zero-padded concatenations.
--
--   **Formalization Note** $\mathbb Z_2$ is used instead of booleans so that XOR is the group law; the choice changes no instance. The flag encoding is the pinned-down convention of the mission (paper.md decision 3).
-- source:
--   Chatterjee, Mukherjee, Pathak, Podder, Quantum Fire with Delegated Cloning, arXiv:2610.03593 (held version, sha256 4e43d2f2…afd593), §3 Basic Notations p.16, Classical Oracles Queried in Superposition p.17; (21) p.26; (43)–(44) pp.50–51

import Mathlib

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 2048

namespace TorchFire.Model

/-- **Bit strings** `{0,1}^n` (Chatterjee–Mukherjee–Pathak–Podder, *Quantum Fire with Delegated
Cloning*, arXiv:2610.03593, held version sha256 4e43d2f2…afd593, §3 "Basic Notations", p.16, and
"Classical Oracles Queried in Superposition", p.17).

A string is a function `Fin n → ZMod 2`. Bitwise XOR `⊕` is pointwise addition in `ZMod 2`, and
`ℤ₂`-linear algebra (the matrices `A_y`, vectors `b_y`, `vᵀA_y` of Construction 4.2) is
`Matrix.mulVec` / `Matrix.vecMul` over `ZMod 2`.

**Formalization Note** `ZMod 2` is used instead of `Bool` so that `⊕` is the additive group law;
both are two-element types and the choice changes no instance. -/
abbrev Bits (n : ℕ) : Type := Fin n → ZMod 2

/-- **The ⊥-flag encoding** of a partial value (paper.md decision 3). A value `v` is encoded as
`(0, v)` and `⊥` as `(1, 0)`: a fixed-width bit vector with one flag bit. An oracle answer that may
be `⊥` (the paper's `P⁻¹`, `O_b`, `O₂`, `N`, `Γ`, `T`) is XOR-written in this encoding, so a value is
never confused with `⊥`. -/
def encBot {α : Type} [Zero α] : Option α → ZMod 2 × α
  | none => (1, 0)
  | some v => (0, v)

/-- Decoding of the ⊥-flag encoding: flag `0` is a value, flag `1` is `⊥` (a malformed or rejected
answer). -/
def decBot {α : Type} (x : ZMod 2 × α) : Option α :=
  if x.1 = 0 then some x.2 else none

/-- A list of bits written into a fixed-width register, padded with zeros (positions beyond the list
are `0`). Used for the zero-padded encodings `enc` (21) and `code` (44). -/
def listToBits (w : ℕ) (l : List (ZMod 2)) : Bits w := fun i => l.getD i.val 0

/-- The bits of a string, as a list (for concatenations `x ∥ y` of (24), (43), (44)). -/
def bitsToList {n : ℕ} (x : Bits n) : List (ZMod 2) := List.ofFn x

/-- Concatenation `x ∥ y` of bit strings. -/
def bappend {a b : ℕ} (x : Bits a) (y : Bits b) : Bits (a + b) := Fin.append x y

/-- The binary representation `[c]_w` of a natural number with `w` digits (least significant bit
last, leading zeros), as in "`[c]_λ` denote the binary representation of `c` with leading zeros",
p.50. -/
def natToBits (w : ℕ) (c : ℕ) : Bits w := fun i => ((c / 2 ^ (w - 1 - i.val)) % 2 : ℕ)

end TorchFire.Model


