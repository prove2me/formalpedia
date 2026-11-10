-- Prove2me | Definitions.Def_AESIndependence_Main_ReferenceChain
-- name    : AESIndependence_Main_ReferenceChain
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T04:11:53.700509+00:00
-- url     : https://prove2.me/theorems/2c78d161-bfce-4f19-afac-78dea026a7b4
-- title:
--   Ancilla-free circuits and the conjugated alternating-group reference chain
-- statement:
--   For a finite wire set $I$, binary assignments are $\mathbb F_2^I$, and even permutations form $\operatorname{Alt}(\mathbb F_2^I)$. A circuit is a list of NOT, CNOT and Toffoli gates on exactly $I$. It implements $g$ when its evaluation equals $g$ on every assignment, without additional wires or clean-input promises.
--   Given $c$ distinct even generators, their Cayley walk on the alternating group uses the matrix
--   $$K=\frac12I+\frac1{4c}\sum_{i=1}^c(L_{g_i}+L_{g_i^{-1}}),$$
--   where $L_g$ is left group multiplication. An expander witness records a lower gap bound $\gamma$ and circuits of length at most $a|I|$ for each generator and its inverse. This predicate is proved existentially by Theorem 2.19; no cipher theorem assumes its existence.
--   The fixed basis transports generators from binary assignments to field-valued states. For an AES deterministic round $M$, the reference tuple matrix is
--   $$K_{\rm ref}=\frac12I+\frac1{4c}\sum_i(M^{-2}g_iM^2+M^{-2}g_i^{-1}M^2).$$
--   Each term acts simultaneously on every tuple entry. The group walk and the tuple walk have different state spaces. This interface keeps both explicit so the transitive quotient and conjugation step can be formalized rather than assumed.
-- source:
--   Angelos Pelecanos, Stefano Tessaro, Vinod Vaikuntanathan, STOC 2027 submission #1279 (October 2026), Theorem 2.19 and Definition 2.20, p.14 (PDF p.14)

import Mathlib
import Definitions.Def_AESIndependence_Main_Gadgets

namespace AESIndependence.Main
noncomputable section
open scoped BigOperators Classical

abbrev EvenPerm (ι : Type) [Fintype ι] := alternatingGroup (BinaryState ι)

/-- Left Cayley multiplication by an actual element of the alternating group. -/
def cayleyAction {ι : Type} [Fintype ι] (g : EvenPerm ι) : Equiv.Perm (EvenPerm ι) where
  toFun h := g * h
  invFun h := g⁻¹ * h
  left_inv h := by simp
  right_inv h := by simp

def cayleyMatrix {ι : Type} [Fintype ι] {c : ℕ} (g : Fin c → EvenPerm ι) :
    Matrix (EvenPerm ι) (EvenPerm ι) ℝ := lazyGeneratorMatrix (fun i => cayleyAction (g i))

/-- A circuit is just gates on the same wire type; equality is on every assignment. -/
def CircuitImplements {ι : Type} (w : List (Gate ι)) (g : BinaryState ι → BinaryState ι) : Prop :=
  runWord (w.map gateAction) = g

/-- Quantitative witness, not a hypothesis of the AES goal. -/
def ExpanderWitness {ι : Type} [Fintype ι] {c : ℕ} (g : Fin c → EvenPerm ι)
    (γ a : ℝ) : Prop :=
  Function.Injective g ∧ γ ≤ spectralGap (cayleyMatrix g) ∧
  ∀ i : Fin c,
    (∃ w : List (Gate ι), (w.length : ℝ) ≤ a * Fintype.card ι ∧
      CircuitImplements w (g i).val) ∧
    (∃ w : List (Gate ι), (w.length : ℝ) ≤ a * Fintype.card ι ∧
      CircuitImplements w ((g i).val)⁻¹)

variable {b d : ℕ} {F : Type} [Field F] [Algebra (ZMod 2) F]

def liftBinaryPermutation (D : Cipher b d F) (g : Equiv.Perm (BinaryState (BitIndex b d))) :
    Equiv.Perm (State d F) :=
  (stateCoordinates D).trans (g.trans (stateCoordinates D).symm)

/-- Conjugate all generators by M², then act simultaneously on tuple entries. -/
def referenceMatrix [Fintype F] {c : ℕ} (D : Cipher b d F)
    (g : Fin c → EvenPerm (BitIndex b d)) (t : ℕ) :
    Matrix (DistinctTuple (State d F) t) (DistinctTuple (State d F) t) ℝ :=
  lazyGeneratorMatrix (fun i => tuplePerm
    ((roundPermutation D)^(-2 : ℤ) * liftBinaryPermutation D (g i).val *
      (roundPermutation D)^(2 : ℤ)))

end
end AESIndependence.Main


