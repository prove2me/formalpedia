-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_FrobeniusLocalisation_SizeDefs
-- name    : Development_AutomorphicArithmetic_FrobeniusLocalisation_SizeDefs
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T15:10:30.683703+00:00
-- url     : https://prove2.me/theorems/63887688-d636-4ec1-a5c6-0991ad00e51d
-- title:
--   Size Defs
-- statement:
--   Definitions and structural lemmas for Size Defs, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/FrobeniusLocalisation/SizeDefs.lean

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_PrimePairSizeCondition
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
namespace UpperTheory.HF.Formalism.HC
open UpperTheory.HF _root_.Formalism _root_.Formalism.HC
namespace Frame
open _root_.Formalism.HC.Frame
variable (φ : Frame)
def oh : ℕ := Nat.card φ.hH.ker
def Thick (T : Finset ℕ) (u : φ.A) (π : φ.GG) : Prop := ∃ s ∈ T, π = φ.tau2 (φ.dig s + u)
def letter {φ : Frame} (g τ : φ.GG) (i : ℤ) : φ.GG := placeOf (g ^ i * τ)
end Frame
namespace HostRaw
open _root_.Formalism.HC.HostRaw
variable {φ : Frame} (H : HostRaw φ)
def frobG (p : ℕ) : φ.GG :=
  if h : Nat.Coprime p H.condN then H.art (ZMod.unitOfCoprime p h) else 1
def Inert (p : ℕ) : Prop := p.Prime ∧ jacobiSym (-(H.d : ℤ)) p = -1
def DRC (B : ℝ) : Set ℕ :=
  {p | H.Inert p ∧ (p : ℝ) ≤ B ∧ φ.cc ∈ Subgroup.zpowers (H.frobG p) ∧ H.frobG p ≠ φ.cc}
def DRh (B : ℝ) : Set ℕ := {p | H.Inert p ∧ (p : ℝ) ≤ B ∧ φ.hH (H.frobG p).2 = 1}
end HostRaw
end UpperTheory.HF.Formalism.HC
end


