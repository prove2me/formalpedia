-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_DiffDefs
-- name    : Development_AutomorphicArithmetic_FrobeniusLocalisation_DiffDefs
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T15:10:47.813793+00:00
-- url     : https://prove2.me/theorems/bd4b87e9-c895-45a6-8703-92c71e73630d
-- title:
--   Diff Defs
-- statement:
--   Definitions and structural lemmas for Diff Defs, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/FrobeniusLocalisation/DiffDefs.lean

import Definitions.Def_Development_AutomorphicArithmetic_PrimeDiscriminants_SlopeTestRemainingChoices
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace UpperTheory.HF.Formalism.HC.HostRaw
open UpperTheory.HF _root_.Formalism _root_.Formalism.HC _root_.Formalism.HC.HostRaw
variable {φ : Frame} (H : HostRaw φ)
def unitsOne (f : ℕ) : Subgroup (ZMod H.condN)ˣ := (ZMod.unitsMap (Nat.gcd_dvd_right f H.condN)).ker
def imgOne (f : ℕ) : Subgroup φ.GG := (H.unitsOne f).map H.art
def condE : ℕ := sInf {f : ℕ | f ∣ H.condN ∧ H.imgOne f = ⊥}
def sl (l : ℕ) : ℕ := max 1 (H.condE.factorization l)
def inertG (l : ℕ) : Subgroup φ.GG := H.imgOne (ordCompl[l] H.condN)
def el (l : ℕ) : ℕ := Nat.card (H.inertG l)
open Classical in

def artL (l : ℕ) : φ.GG :=
  if h : ∃ u : (ZMod H.condN)ˣ, (u : ZMod H.condN).val ≡ l [MOD ordCompl[l] H.condN] ∧
      (u : ZMod H.condN).val ≡ 1 [MOD ordProj[l] H.condN] then H.art h.choose else 1
def decG (l : ℕ) : Subgroup φ.GG := H.inertG l ⊔ Subgroup.zpowers (H.artL l)
def nw (l : ℕ) : ℕ := (H.inertG l).relIndex (H.decG l)
def ram : Finset ℕ := (NumberField.discr H.E).natAbs.primeFactors
def ramI : Finset ℕ := H.ram.erase H.d
def smallR : Finset ℕ := H.small ∩ H.ram
def rad : ℕ := ∏ l ∈ H.ram, l
def QSc : ℕ := ∏ l ∈ H.smallR, l ^ H.sl l
def eL : ℕ := sInf {m : ℕ | 0 < m ∧ (m : NumberField.RingOfIntegers H.E) ∈ differentIdeal ℤ (NumberField.RingOfIntegers H.E)}
end UpperTheory.HF.Formalism.HC.HostRaw
end


