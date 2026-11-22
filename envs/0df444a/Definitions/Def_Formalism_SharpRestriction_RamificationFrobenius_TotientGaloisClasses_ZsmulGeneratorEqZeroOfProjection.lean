-- Prove2me | Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ZsmulGeneratorEqZeroOfProjection
-- name    : Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ZsmulGeneratorEqZeroOfProjection
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T16:53:29.985192+00:00
-- url     : https://prove2.me/theorems/b6d75ff9-4538-49d7-9d0c-da00af2d81f3
-- title:
--   Zsmul Generator Eq Zero Of Projection
-- statement:
--   Definitions and structural lemmas for Zsmul Generator Eq Zero Of Projection, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/ZsmulGeneratorEqZeroOfProjection.lean

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_Statement
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
open Formalism.FrobeniusOrbits
def Idx (n : ℕ) : Type := Fin n
instance (n : ℕ) : Fintype (Idx n) := inferInstanceAs (Fintype (Fin n))
instance (n : ℕ) : DecidableEq (Idx n) := inferInstanceAs (DecidableEq (Fin n))
structure Frame where
  e : ℕ

  ord : ℕ
  grp : AddCommGroup (Idx ord)
  h0 : letI := grp; Idx ord →+ Additive (HGrp e)
  projection_surjective_field : Function.Surjective h0
  gen0 : Idx ord
  zsmul_generator_eq_zero_of_projection : letI := grp; ∀ k : ℤ, h0 (k • gen0) = 0 → k • gen0 = 0
namespace Frame
variable (φ : Frame)
def A : Type := Idx φ.ord
instance : AddCommGroup φ.A := φ.grp
instance : Fintype φ.A := inferInstanceAs (Fintype (Idx φ.ord))
instance : DecidableEq φ.A := inferInstanceAs (DecidableEq (Idx φ.ord))
def A.val {φ : Frame} (t : φ.A) : ℕ := Fin.val (n := φ.ord) t
theorem A.val_lt {φ : Frame} (t : φ.A) : t.val < φ.ord := by
  exact Fin.is_lt (n := φ.ord) t
theorem A.val_injective (φ : Frame) : Function.Injective (A.val : φ.A → ℕ) := by
  exact fun s t h => Fin.ext h
def A.ofVal {φ : Frame} (u : ℕ) (hu : u < φ.ord) : φ.A := (⟨u, hu⟩ : Fin φ.ord)
@[simp] theorem A.val_ofVal {φ : Frame} (u : ℕ) (hu : u < φ.ord) : (A.ofVal u hu : φ.A).val = u := rfl
theorem ord_pos : 0 < φ.ord := by
  exact Fin.pos (n := φ.ord) (0 : φ.A)
def h : φ.A →+ Additive (HGrp φ.e) := φ.h0
def a0 : φ.A := φ.gen0
def A0 : AddSubgroup φ.A := AddSubgroup.zmultiples φ.a0
def n0 : ℕ := addOrderOf φ.a0
def o : ℕ := φ.ord / φ.n0
def dig (s : ℕ) : φ.A := s • φ.a0
def ofNat (u : ℕ) : φ.A := A.ofVal (u % φ.ord) (Nat.mod_lt _ φ.ord_pos)
theorem val_ofNat (u : ℕ) : (φ.ofNat u).val = u % φ.ord := rfl
@[simp] theorem ofNat_val (t : φ.A) : φ.ofNat t.val = t := by
  apply A.val_injective φ
  rw [φ.val_ofNat, Nat.mod_eq_of_lt (A.val_lt t)]
abbrev MA : Type := Multiplicative φ.A
abbrev GG : Type := G0 × φ.MA
def hH : φ.MA →* HGrp φ.e where
  toFun a := (φ.h a.toAdd).toMul
  map_one' := by simp
  map_mul' a b := by simp
def iota (t : φ.A) : φ.MA := Multiplicative.ofAdd t
def iotaInv (a : φ.MA) : φ.A := a.toAdd
def sg : φ.GG := ((-1, 1), 1)
def cc : φ.GG := (c0, 1)
def iod : φ.GG := ((1, -1), 1)
def chD : φ.GG →* ℤˣ := (MonoidHom.snd ℤˣ ℤˣ).comp (MonoidHom.fst G0 φ.MA)
def chQ : φ.GG →* ℤˣ := (MonoidHom.fst ℤˣ ℤˣ).comp (MonoidHom.fst G0 φ.MA)
def chC : φ.GG →* ℂˣ := (Units.map (Int.castRingHom ℂ).toMonoidHom).comp φ.chD
def Psi : Subgroup φ.GG := φ.chD.ker
def placeOf {φ : Frame} (g : φ.GG) : φ.GG := if g.1.2 = 1 then g else φ.cc * g
def tau1 (t : φ.A) : φ.GG := ((1, 1), φ.iota t)
def tau2 (t : φ.A) : φ.GG := ((-1, 1), φ.iota t)
def TwoGroup : Prop := ∃ j : ℕ, φ.ord = 2 ^ j
end Frame
end Formalism.HC
end


