-- Prove2me | Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_PrimePairSizeCondition
-- name    : Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_PrimePairSizeCondition
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:30:40.036058+00:00
-- url     : https://prove2.me/theorems/4a01620b-26ab-4e05-92a7-53bf5dbeec6b
-- title:
--   Prime Pair Size Condition
-- statement:
--   Definitions and structural lemmas for Prime Pair Size Condition, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/PrimePairSizeCondition.lean

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ConjEMemHostFIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.HC
structure PChar where
  N : ℕ
  [ne : NeZero N]
  χ : DirichletCharacter ℂ N
  prim : χ.IsPrimitive
attribute [instance] PChar.ne
namespace PChar
def val (ψ : PChar) (a : ℕ) : ℂ := ψ.χ (a : ZMod ψ.N)
def one : PChar := ⟨1, 1, DirichletCharacter.isPrimitive_one_level_one⟩
def inv (ψ : PChar) : PChar :=
  ⟨ψ.N, ψ.χ⁻¹, by
    have h : ψ.χ.conductor = ψ.N := ψ.prim
    exact (DirichletCharacter.conductor_inv ψ.χ).trans h⟩
def of {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) : PChar :=
  @PChar.mk χ.conductor ⟨χ.conductor_ne_zero⟩ χ.primitiveCharacter χ.primitiveCharacter_isPrimitive
def IsReal (ψ : PChar) : Prop := ∀ a : ZMod ψ.N, (ψ.χ a).im = 0
end PChar
structure KSet where
  KEPT : Finset PChar
  one_mem : PChar.one ∈ KEPT
  inv_mem : ∀ ψ ∈ KEPT, ψ.inv ∈ KEPT

  psK : Option PChar
  psK_spec : ∀ ψ, psK = some ψ → ψ ∈ KEPT ∧ ψ.χ.Odd ∧ ψ.IsReal
structure HType extends KSet where
  eps : ℝ
  eps_pos : 0 < eps
  eps_lt : eps < 1 / 52
  J : ℕ
  one_le_J : 1 ≤ J
  P0 : ℕ
  P0_pos : 0 < P0

  t : ℝ → ℕ
  Ct : ℝ
  t_le : ∀ x : ℝ, 1 ≤ x → (t x : ℝ) ≤ x ^ Ct
namespace HType
variable (T : HType)
def SM : Finset ℕ := (2 * T.P0 * ∏ ψ ∈ T.KEPT, ψ.N).primeFactors
def P : ℕ := ∏ p ∈ (∏ l ∈ T.SM, l * (l - 1)).primeFactors.erase 2, p
def z (X : ℝ) : ℝ := X ^ (T.eps / (5 * (T.J : ℝ)))
def z' (X : ℝ) : ℝ := T.z X * Real.log (X ^ ((1 : ℝ) / T.J)) ^ 2
def L (x : ℝ) : ℝ := x ^ T.eps
def b (x : ℝ) : ℝ := Real.exp (T.L x)
def X' (x : ℝ) : ℝ := Real.exp (x ^ (T.eps / 3))
def InRange (X x : ℝ) (e : ℕ) : Prop :=
  1 ≤ X ∧ X ^ ((1 : ℝ) / T.J) ≤ x ∧ x ≤ X ∧
    x ^ (2 + 8 * T.eps) / 2 ≤ (2 : ℝ) ^ e ∧ (2 : ℝ) ^ e ≤ 2 * x ^ (2 + 8 * T.eps)
end HType
structure HConst where

  oB : ℕ

  rB : ℕ

  c : ℝ
  c_pos : 0 < c

  C : ℝ
def Frame.TorsionIndexBounded (φ : Frame) (oB : ℕ) : Prop := φ.o ≤ oB
namespace HostRaw
variable {φ : Frame} (H : HostRaw φ)
theorem condN_pos : 0 < H.condN :=
  Nat.mul_pos (Nat.mul_pos H.QS_pos H.hyp.1.pos) H.hyp.2.1.pos
instance condN_neZero : NeZero H.condN := ⟨H.condN_pos.ne'⟩
def OddPrimesSplitBelow (z : ℝ) : Prop :=
  11 ≤ z ∧ ∀ p : ℕ, p.Prime → p ≠ 2 → (p : ℝ) ≤ z → jacobiSym (-(H.d : ℤ)) p = 1
def SmallPrimeSizeBounds (SM : Finset ℕ) (z : ℝ) : Prop := ∀ l ∈ H.small, l ∈ SM ∧ (l : ℝ) ≤ z / 4
def DiscriminantConductorSizes (z' : ℝ) : Prop :=
  z' / 2 < Real.log H.d ∧ Real.log H.d ≤ z' ∧ Real.log (H.condN : ℝ) ≤ 3 * z'
def ModulusSizeBounds (z : ℝ) : Prop := z / 2 < Real.log H.q ∧ Real.log H.q ≤ z
def PrimePairSizeCondition (z : ℝ) (rB rr rr' : ℕ) : Prop :=
  rr.Prime ∧ rr'.Prime ∧ rr ≠ 2 ∧ rr < rr' ∧ rr' < 2 * rr ∧ Nat.Coprime (rr * rr') H.condN ∧ (rr' : ℝ) ≤ z ∧ rr' ≤ rB
end HostRaw
structure PreHost (T : HType) (κ : HConst) (X x : ℝ) {φ : Frame} (H : HostAx φ) (rr rr' : ℕ) : Prop where
  range : T.InRange X x φ.e
  ha5 : φ.TorsionIndexBounded κ.oB
  ha6 : H.OddPrimesSplitBelow (T.z X)
  ha7 : H.SmallPrimeSizeBounds T.SM (T.z X)
  ha8 : H.DiscriminantConductorSizes (T.z' X)
  ha9 : H.ModulusSizeBounds (T.z X)
  ha12 : H.PrimePairSizeCondition (T.z X) κ.rB rr rr'
end Formalism.HC
end


