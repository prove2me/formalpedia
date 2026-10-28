-- Prove2me | Definitions.Def_BitDFT_Encoding
-- name    : BitDFT_Encoding
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-24T12:00:06.714436+00:00
-- url     : https://prove2.me/theorems/ec43533b-b354-445d-afc6-a4727b09a921
-- title:
--   Binary encodings and actual machine computation
-- statement:
--   Self-delimiting natural headers, fixed-width signed integer and Gaussian-pair encodings, vector/list encodings, a predicate measuring real multitape transition counts and exact output tapes, and the arbitrary binary multiplier interface. Integer encodings truncate outside their documented range; theorem hypotheses must supply the range.
-- source:
--   Harvey and van der Hoeven, Integer multiplication is at least as hard as matrix transposition (2025), https://arxiv.org/abs/2503.22848, Sections 2–3.4; BitDFT transfer specification (24 October 2026) for explicit binary conventions and derived end-to-end formulations.

import Definitions.Def_IntMul_MultitapeModel

set_option autoImplicit false
namespace BitDFT

/-- Self-delimiting binary natural: unary bit-length, a zero, then MSB-first bits. -/
def encNat (n : ℕ) : List Bool :=
  List.replicate n.size true ++ [false] ++ IntMul.bin n.size n

/-- Fixed-width sign-magnitude; positive sign for zero. Valid when |z| < 2^w. -/
def encInt (w : ℕ) (z : ℤ) : List Bool :=
  [decide (z < 0)] ++ IntMul.bin w z.natAbs

def encComplex (w : ℕ) (z : ℤ × ℤ) : List Bool :=
  encInt w z.1 ++ encInt w z.2

def encVector {n : ℕ} (w : ℕ) (U : Fin n → ℤ × ℤ) : List Bool :=
  (List.finRange n).flatMap (fun i => encComplex w (U i))

def encList (w : ℕ) (a : List ℤ) : List Bool := a.flatMap (encInt w)

/-- Actual multitape transitions, with the entire encoded input on the first
binary argument and an empty second argument. Output tape must be exact, including blank tail. -/
def Computes (A : IntMul.MultitapeTM) (input output : List Bool) (bound : ℝ) : Prop :=
  ∃ t : ℕ, (t : ℝ) ≤ bound ∧ A.HaltsWithOutput input [] t output

/-- A single machine with a pointwise bound at every positive operand width.
No monotonicity, smoothness or computability assumption on the bounding function. -/
def Multiplier (A : IntMul.MultitapeTM) (T : ℕ → ℝ) : Prop :=
  ∀ n : ℕ, 1 ≤ n → IntMul.MultipliesAt A n (T n)

end BitDFT


