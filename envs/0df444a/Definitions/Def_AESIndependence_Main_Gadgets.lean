-- Prove2me | Definitions.Def_AESIndependence_Main_Gadgets
-- name    : AESIndependence_Main_Gadgets
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T04:10:56.307586+00:00
-- url     : https://prove2.me/theorems/25c48475-b256-49f8-b8aa-dc64c90a414e
-- title:
--   Integer-depth words and classical reversible gates
-- statement:
--   For the generalized cipher, let $b$ be the byte length, $d$ its array width, and $n=bd^2$. A byte lies in a field $F$ of size $2^b$ with any fixed binary basis. The map $A$ is invertible and binary-linear; the column map $C$ is invertible over $F$, and every entry of $C$ and $C^{-1}$ is nonzero. Write $M$ for SubBytes, ShiftRows and MixColumns in that order, and $T_v(x)=x+v$ for key addition. For $j\in\mathbb Z$ put $h_v^{(j)}=M^{-j}T_vM^j$.
--
--   NOT, CNOT and Toffoli operate on the binary coordinates: NOT adds one at its target, CNOT adds its control bit, and Toffoli adds the product of its two control bits. Constructors require distinct controls and targets. The binary coordinate equivalence transports these exact functions to states. Every other bit is unchanged.
--   A gadget word is a list of fixed depths and full-state keys. Its cost counts occurrences, and its evaluation applies the first entry first. A word implements a desired map only when they agree for every input. The allowed gate depths are $\{-2,-1,0,1\}$; balanced gadget depths are $\{0,1,2,3\}$. Empty words implement the identity.
--   The byte update maps explicitly give
--   $$x_i\gets x_i+\alpha x_j,\quad x_k\gets x_k+x_i^2x_j,\quad x_k\gets x_k+x_i^2,\quad x_i\gets x_i+u\operatorname{Tr}(vx_j),$$
--   and leave every unmentioned byte equal to its input. Affine byte operations update all bytes simultaneously. These are operational targets for synthesis, not assumptions that words already exist. Full-state equality also requires every helper to be restored for arbitrary initial contents.
-- source:
--   Angelos Pelecanos, Stefano Tessaro, Vinod Vaikuntanathan, STOC 2027 submission #1279 (October 2026), Definition 4.1 and §5, pp.16–29 (PDF pp.16–29)

import Mathlib
import Definitions.Def_AESIndependence_Main_CipherModel

namespace AESIndependence.Main
noncomputable section
open scoped BigOperators Classical

/-- Gates carry the source's distinct-wire requirements in their constructors. -/
inductive Gate (ι : Type) where
  | not (target : ι)
  | cnot (control target : ι) (distinct : control ≠ target)
  | toffoli (control₁ control₂ target : ι)
      (h₁₂ : control₁ ≠ control₂) (h₁t : control₁ ≠ target) (h₂t : control₂ ≠ target)

/-- Every unmentioned wire is fixed. No ancillary wires occur. -/
def gateAction {ι : Type} (G : Gate ι) (x : BinaryState ι) : BinaryState ι :=
  match G with
  | .not t => Function.update x t (x t + 1)
  | .cnot c t _ => Function.update x t (x t + x c)
  | .toffoli c₁ c₂ t _ _ _ => Function.update x t (x t + x c₁ * x c₂)

variable {b d : ℕ} {F : Type} [Field F] [Algebra (ZMod 2) F]

def stateGate (D : Cipher b d F) (G : Gate (BitIndex b d)) : State d F → State d F :=
  fun x => (stateCoordinates D).symm (gateAction G (stateCoordinates D x))

def conjugatedGate (D : Cipher b d F) (G : Gate (BitIndex b d)) : State d F → State d F :=
  fun x => ((roundPermutation D)^(-2 : ℤ))
    (stateGate D G (((roundPermutation D)^(2 : ℤ)) x))

def bitMask (D : Cipher b d F) (p : BitIndex b d) : State d F :=
  fun q => if q = p.1 then D.basis p.2 else 0

/-- Integer depths, including all negative depths used by the source's symbolic words. -/
def gadget (D : Cipher b d F) (j : ℤ) (v : State d F) : Equiv.Perm (State d F) :=
  (roundPermutation D)^(-j) * translation v * (roundPermutation D)^j

abbrev GadgetWord (d : ℕ) (F : Type) := List (ℤ × State d F)

def gadgetWordAction (D : Cipher b d F) (w : GadgetWord d F) : State d F → State d F :=
  runWord (w.map (fun p => (gadget D p.1 p.2 : State d F → State d F)))

def HasGadgetWord (D : Cipher b d F) (depths : Set ℤ) (bound : ℝ)
    (f : State d F → State d F) : Prop :=
  ∃ w : GadgetWord d F, (w.length : ℝ) ≤ bound ∧
    (∀ p ∈ w, p.1 ∈ depths) ∧ gadgetWordAction D w = f

def gateDepths : Set ℤ := {-2, -1, 0, 1}
def balancedDepths : Set ℤ := {0, 1, 2, 3}

/-- Exactly the stated update; all other bytes remain at their input values. -/
def affineBytes (α c : ByteIndex d → F) (x : State d F) : State d F :=
  fun q => α q * x q + c q

def byteAddition (i j : ByteIndex d) (α : F) (x : State d F) : State d F :=
  Function.update x i (x i + α * x j)

def byteProduct (i j k : ByteIndex d) (x : State d F) : State d F :=
  Function.update x k (x k + (x i)^2 * x j)

def squareAddition (i k : ByteIndex d) (x : State d F) : State d F :=
  Function.update x k (x k + (x i)^2)

def selectedBitAddition (i j : ByteIndex d) (u v : F) (x : State d F) : State d F :=
  Function.update x i (x i + u * traceByte b (v * x j))

end
end AESIndependence.Main


