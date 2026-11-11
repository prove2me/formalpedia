-- Prove2me | Definitions.Def_QuantumAdviceAmplification_Separation_codes
-- name    : QuantumAdviceAmplification_Separation_codes
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T06:02:14.333049+00:00
-- url     : https://prove2.me/theorems/15df9c4c-e63f-45b0-9c10-962b980d5ca4
-- title:
--   Finite-seed random access codes and the operational shared-header protocol
-- statement:
--   A classical code has a finite seed probability space, an unrestricted encoder, and a deterministic decoder, with separate worst-message, worst-query correctness. A quantum code uses arbitrary mixed density matrices and one two-outcome POVM per query.
--
--   For positive $d,q$ let $\ell=d+q$. The published systematic Toeplitz matrix is reused over $\mathbb F_2$, with codewords $(u,Tu)$. Nearest systematic messages are computed by exhaustive search in lexicographic order, retaining the first minimizer. Hamming distance and normalized uniform distance averages are computed from these actual words.
--
--   Protocol 1 draws a single uniform seed, shift and mask shared by every block. The encoder serializes their header and every rounded systematic block. The decoder parses the shift, locates the queried block, reads its systematic coordinates and the required Toeplitz segment, and removes the mask.
--   $$h=2\ell-1+\lceil\log_2\ell\rceil,\qquad m'=h+Bd.$$
--   The file also defines the trivial code, restriction and zero padding, and implementation predicates that count actual tape steps in both hard-wired and parameter-input modes. No error or time theorem is included as a code field.
-- source:
--   Shih-Han Hung, Han-Hsuan Lin, STOC 2027 submission #1297 (October 2026), p.5, Definition 2.3; pp.7–10, Eqs. (9)–(21), Protocol 1

import Definitions.Def_QuantumAdviceAmplification_Separation_machine
import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P23
set_option autoImplicit false
noncomputable section

namespace QuantumAdviceAmplification.Separation

/-- General finite-seed classical RAC data; correctness and time are not fields. -/
structure ClassicalCode (k m : ℕ) where
  Seed : Type
  [seedFintype : Fintype Seed]
  law : PMF Seed
  encode : Bits k → Seed → Bits m
  decode : Fin k → Bits m → Bool

attribute [instance] ClassicalCode.seedFintype

def codeError {k m : ℕ} (C : ClassicalCode k m) (z : Bits k) (i : Fin k) : ℝ :=
  ∑ s : C.Seed, (C.law s).toReal * if C.decode i (C.encode z s) ≠ z i then 1 else 0

def IsRAC {k m : ℕ} (C : ClassicalCode k m) (ε : ℝ) : Prop :=
  ∀ (z : Bits k) (i : Fin k), codeError C z i ≤ ε

/-- Definition 2.3, with arbitrary mixed states and a two-outcome POVM per query. -/
structure QuantumCode (k m : ℕ) where
  encode : Bits k → Matrix (Bits m) (Bits m) ℂ
  density : ∀ z, QAlgorithms.IsDensityMatrix (encode z)
  effect : Fin k → Matrix (Bits m) (Bits m) ℂ
  validEffect : ∀ i, QAlgorithms.IsEffect (effect i)

def IsQRAC {k m : ℕ} (C : QuantumCode k m) (ε : ℝ) : Prop :=
  ∀ (z : Bits k) (i : Fin k),
    1 - ε ≤ if z i then QAlgorithms.effectProb (C.effect i) (C.encode z)
      else 1 - QAlgorithms.effectProb (C.effect i) (C.encode z)

def getBit {n : ℕ} (x : Bits n) (i : ℕ) : Bool := (vectorList x).getD i false

def ofNumber (n v : ℕ) : Bits n := fun i => v.testBit (n - 1 - i.val)

def weight {n : ℕ} (w : Bits n) : ℕ := (Finset.univ.filter fun i => w i = true).card

def distance {n : ℕ} (x y : Bits n) : ℕ := weight (fun i => xor (x i) (y i))

def volume (ℓ r : ℕ) : ℕ := ∑ j ∈ Finset.range (r + 1), Nat.choose ℓ j

def b2f (b : Bool) : ZMod 2 := if b then 1 else 0

/-- ell=q+d, with d systematic coordinates followed by q parity coordinates. -/
structure BlockShape where
  d : ℕ
  q : ℕ
  d_pos : 0 < d
  q_pos : 0 < q

def BlockShape.ell (S : BlockShape) : ℕ := S.q + S.d

def toeplitz (S : BlockShape) (t : Bits (S.ell - 1)) : Matrix (Fin S.q) (Fin S.d) (ZMod 2) :=
  QAlgorithms.Papers.Independent.Advance50.P23.toeplitz S.q S.d (fun i => b2f (t i))

def codeword (S : BlockShape) (t : Bits (S.ell - 1)) (u : Bits S.d) : Bits S.ell :=
  fun p => if h : p.val < S.d then u ⟨p.val, h⟩ else
    decide ((∑ j : Fin S.d, toeplitz S t ⟨p.val - S.d, by have := p.isLt; unfold BlockShape.ell at *; omega⟩ j * b2f (u j)) = 1)

def toeplitzCode (S : BlockShape) (t : Bits (S.ell - 1)) : Set (Bits S.ell) :=
  Set.range (codeword S t)

def syndrome (S : BlockShape) (t : Bits (S.ell - 1)) (w : Bits S.ell) : Fin S.q → ZMod 2 :=
  fun i => (∑ j : Fin S.d, toeplitz S t i j * b2f (getBit w j.val)) +
    b2f (getBit w (S.d + i.val))

/-- Exhaustive search in increasing binary rank. Strict improvement retains the first
minimizer on ties; no rounding oracle or promised covering estimate is supplied. -/
def nearest (S : BlockShape) (t : Bits (S.ell - 1)) (y : Bits S.ell) : Bits S.d :=
  ofNumber S.d ((List.range (2 ^ S.d)).foldl (fun best v =>
    if distance y (codeword S t (ofNumber S.d v)) <
      distance y (codeword S t (ofNumber S.d best)) then v else best) 0)

def codeDistance (S : BlockShape) (t : Bits (S.ell - 1)) (y : Bits S.ell) : ℕ :=
  distance y (codeword S t (nearest S t y))

def uniformMean {α : Type} [Fintype α] (f : α → ℝ) : ℝ :=
  (∑ a, f a) / Fintype.card α

def averageDistance (S : BlockShape) (t : Bits (S.ell - 1)) : ℝ :=
  uniformMean fun y : Bits S.ell => (codeDistance S t y : ℝ) / S.ell

def epsilonStar (S : BlockShape) : ℝ :=
  uniformMean (averageDistance S)

def headerLength (ℓ : ℕ) : ℕ := 2 * ℓ - 1 + ⌈log₂ ℓ⌉₊

def payloadLength (S : BlockShape) (B : ℕ) : ℕ := headerLength S.ell + B * S.d

abbrev ProtocolSeed (S : BlockShape) := Bits (S.ell - 1) × Fin S.ell × Bits S.ell

instance protocolSeedNonempty (S : BlockShape) : Nonempty (ProtocolSeed S) :=
  ⟨(fun _ => false, ⟨0, by have := S.d_pos; unfold BlockShape.ell; omega⟩, fun _ => false)⟩

/-- One shared t, shift and mask for every block. -/
def protocolEncode (S : BlockShape) (B : ℕ) (z : Bits (B * S.ell))
    (seed : ProtocolSeed S) : Bits (payloadLength S B) :=
  let t := seed.1
  let τ := seed.2.1
  let σ := seed.2.2
  let shiftWidth := ⌈log₂ S.ell⌉₊
  fun p =>
    if p.val < S.ell - 1 then getBit t p.val
    else if p.val < S.ell - 1 + shiftWidth then
      τ.val.testBit (shiftWidth - 1 - (p.val - (S.ell - 1)))
    else if p.val < headerLength S.ell then getBit σ (p.val - (S.ell - 1 + shiftWidth))
    else
      let j := (p.val - headerLength S.ell) / S.d
      let i := (p.val - headerLength S.ell) % S.d
      let y : Bits S.ell := fun a =>
        xor (getBit z (j * S.ell + (a.val + τ.val) % S.ell)) (σ a)
      getBit (nearest S t y) i

/-- Protocol 1 D1-D4 on the serialized advice, including unused shift encodings. -/
def protocolDecode (S : BlockShape) (B : ℕ) (a : Fin (B * S.ell))
    (c : Bits (payloadLength S B)) : Bool :=
  let j := a.val / S.ell
  let i := a.val % S.ell
  let width := ⌈log₂ S.ell⌉₊
  let τ := value ((List.range width).map fun b => getBit c (S.ell - 1 + b)) % S.ell
  let p := (i + S.ell - τ) % S.ell
  let σ := getBit c (S.ell - 1 + width + p)
  let u : Bits S.d := fun b => getBit c (headerLength S.ell + j * S.d + b.val)
  xor (if p < S.d then getBit u p else
    decide ((∑ b : Fin S.d, b2f (getBit c (p - 1 - b.val)) * b2f (u b)) = 1)) σ

def protocolCode (S : BlockShape) (B : ℕ) : ClassicalCode (B * S.ell) (payloadLength S B) where
  Seed := ProtocolSeed S
  law := PMF.uniformOfFintype _
  encode := protocolEncode S B
  decode := protocolDecode S B

/-- The source trivial code stores a uniformly random m-bit word. -/
def trivialCode (k m : ℕ) : ClassicalCode k m where
  Seed := Bits m
  law := PMF.uniformOfFintype _
  encode := fun _ s => s
  decode := fun _ c => getBit c 0

/-- Restrict to the first k message bits, fill the remainder with zeros, and pad advice
with zeros to m bits. The decoder ignores trailing padding. -/
def restrictPad (S : BlockShape) (B k m : ℕ) : ClassicalCode k m where
  Seed := ProtocolSeed S
  law := PMF.uniformOfFintype _
  encode := fun z s i => getBit (protocolEncode S B (fun j => getBit z j.val) s) i.val
  decode := fun a c =>
    if h : a.val < B * S.ell then
      protocolDecode S B ⟨a.val, h⟩ (fun i => getBit c i.val)
    else false

/-- Exact time for an implementation, rather than an assigned cost function. -/
def CodeRunsWithin {k m : ℕ} (C : ClassicalCode k m) (T : ℝ) : Prop :=
  ∃ M : Machine, ∀ (a : Fin k) (c : Bits m),
    ComputesWithin M (bin (a.val + 1)) (vectorList c) (C.decode a c) T

/-- Both the hard-wired and parameter-input forms of Lemma 3.7(b).
Fixed-width fields let a single machine recover the field width from the input length. -/
def ProtocolImplementations (cdec : ℝ) : Prop :=
  (∃ U : Machine, ∀ (S : BlockShape) (B w : ℕ) (a : Fin (B * S.ell))
      (c : Bits (payloadLength S B)),
    0 < B → B * S.ell ≤ 2 ^ w → S.ell < 2 ^ w → S.d < 2 ^ w → a.val + 1 < 2 ^ w →
    payloadLength S B < 2 ^ w →
    ComputesWithin U (bits w S.ell ++ bits w S.d ++ bits w (a.val + 1))
      (vectorList c) (protocolDecode S B a c) (cdec * (S.d + w ^ 2))) ∧
  (∀ S : BlockShape, ∃ M : Machine, ∀ (B w : ℕ) (a : Fin (B * S.ell))
      (c : Bits (payloadLength S B)),
    0 < B → B * S.ell ≤ 2 ^ w → S.ell < 2 ^ w → S.d < 2 ^ w → a.val + 1 < 2 ^ w →
    payloadLength S B < 2 ^ w →
    ComputesWithin M (bits w (a.val + 1)) (vectorList c)
      (protocolDecode S B a c) (cdec * (S.d + w ^ 2)))

end QuantumAdviceAmplification.Separation


