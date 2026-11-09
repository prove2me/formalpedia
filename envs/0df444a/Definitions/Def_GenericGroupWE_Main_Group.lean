-- Prove2me | Definitions.Def_GenericGroupWE_Main_Group
-- name    : GenericGroupWE_Main_Group
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:52:58.563458+00:00
-- url     : https://prove2.me/theorems/86a67a54-7a02-45b4-9c2a-8966ced9192b
-- title:
--   Fresh prime-order generic groups and exposed strings
-- statement:
--   For a prime $p$, let $\ell=2\lceil\log_2p\rceil$. An encoding is an injection from the $p$ residues into the $2^\ell$ strings of exactly $\ell$ bits. A fresh group context samples this injection uniformly. Its public generator is the encoding of $1$; its addition/subtraction oracle returns the encoding of the corresponding sum/difference, or a single failure symbol if either operand is invalid.
--
--   Labels use little-endian fixed-width bits. Arbitrary strings are accepted as query operands, including malformed lengths. The context's table is interpreter data; public metadata contains only $p$ and the generator. Packet encoding preserves length up to a constant factor. This interface is shared by honest algorithms and adversaries.
-- source:
--   Hair and Sahai, Witness Encryption via Prime-Order Generic Groups, STOC 2027 submission #47 (PDF built 2026-11-02; SHA-256 0b7f14e2db9bb3e199883ab907f854b7b5884c7c9f3d1e4c306bb71e89b659cb), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/47.pdf, §2, A Fresh Generic Cyclic Group, PDF pp. 7–8 (printed pp. 6–7); length-additive packet convention for the oracle interface.

import Mathlib

namespace GenericGroupWE.Main

abbrev Bits := List Bool

/-- Hair--Sahai, STOC 2027 submission 47, §2, PDF 7: fixed-width exposed labels. -/
def labelLength (p : ℕ) : ℕ := 2 * Nat.clog 2 p

abbrev Encoding (p : ℕ) := Fin p ↪ Fin (2 ^ labelLength p)

/-- The encoding space is nonempty even before a primality check. -/
instance encodingNonempty (p : ℕ) : Nonempty (Encoding p) := by
  have h : p ≤ 2 ^ labelLength p :=
    (Nat.le_pow_clog (by decide : 1 < 2) p).trans
      (Nat.pow_le_pow_right (by decide) (by unfold labelLength; omega))
  exact ⟨⟨fun a => ⟨a.val, a.isLt.trans_le h⟩, fun a b hab =>
    Fin.ext (congrArg (fun z : Fin (2 ^ labelLength p) => z.val) hab)⟩⟩

/-- Little-endian bit strings of exactly the specified width. -/
def fixedBits (width n : ℕ) : Bits := List.ofFn fun i : Fin width => n.testBit i.val

def label {p : ℕ} (σ : Encoding p) (a : Fin p) : Bits :=
  fixedBits (labelLength p) (σ a).val

/-- A context carries the table only for the interpreter, never as algorithm input. -/
structure GroupContext where
  p : ℕ
  prime : p.Prime
  σ : Encoding p

noncomputable def freshContext (p : ℕ) (hp : p.Prime) : PMF GroupContext :=
  (PMF.uniformOfFintype (Encoding p)).map fun σ => ⟨p, hp, σ⟩

def GroupContext.generator (Γ : GroupContext) : Bits :=
  label Γ.σ ⟨1, Γ.prime.one_lt⟩

/-- Exact decoding: guessed strings of any length are permitted as operands. -/
def GroupContext.decode (Γ : GroupContext) (x : Bits) : Option (Fin Γ.p) :=
  (List.finRange Γ.p).find? fun a => label Γ.σ a == x

/-- `subtract = false` means addition. All invalid operands receive the same reply. -/
def GroupContext.query (Γ : GroupContext) (subtract : Bool) (x y : Bits) : Option Bits := do
  let a ← Γ.decode x
  let b ← Γ.decode y
  let z := if subtract then a.val + Γ.p - b.val else a.val + b.val
  pure (label Γ.σ ⟨z % Γ.p, Nat.mod_lt _ Γ.prime.pos⟩)

/-- Length-additive packet encoding; each data bit is prefixed by `true`, then `false` ends it. -/
def packet : Bits → Bits
  | [] => [false]
  | b :: bs => true :: b :: packet bs

def unpacket : Bits → Option (Bits × Bits)
  | [] => none
  | false :: rest => some ([], rest)
  | true :: [] => none
  | true :: b :: rest => do
      let (bs, tail) ← unpacket rest
      pure (b :: bs, tail)

def pack (xs : List Bits) : Bits := (xs.map packet).flatten

def bitsNat (bs : Bits) : ℕ := bs.foldr Nat.bit 0

def replyBits : Option Bits → Bits
  | none => [false]
  | some x => true :: packet x

/-- Only the order and generator, not the table, are exposed in this public metadata. -/
def publicContext : Option GroupContext → Bits
  | none => [false]
  | some Γ => true :: pack [Γ.p.bits, Γ.generator]

end GenericGroupWE.Main


