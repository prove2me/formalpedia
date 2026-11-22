-- Prove2me | Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_ExistsPowSmulMemBall
-- name    : Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_ExistsPowSmulMemBall
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:35:48.963609+00:00
-- url     : https://prove2.me/theorems/430bef21-c5ce-4a19-8ce6-b1006a82dde4
-- title:
--   Exists Pow Smul Mem Ball
-- statement:
--   Definitions and structural lemmas for Exists Pow Smul Mem Ball, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GenusPolyhedralBounds/RelativeIndexClassSets/ExistsPowSmulMemBall.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open IsLocalRing
namespace Formalism.MainNotions.Gaps.EtaleWeightGaps
variable (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable (A : Type*) [CommRing A] [Algebra O A]
abbrev As : Subalgebra O A := integralClosure O A
abbrev Pts : Type _ := MaximalSpectrum ↥(As O A)
variable {O A}
abbrev Loc (ζ : Pts O A) : Type _ := Localization.AtPrime ζ.asIdeal
class IsDVRAt (ζ : Pts O A) : Prop where

  isDomain : IsDomain (Loc ζ)

  isDVR : IsDiscreteValuationRing (Loc ζ)
attribute [instance] IsDVRAt.isDomain IsDVRAt.isDVR
theorem comap_eq_maximalIdeal (ζ : Pts O A) :
    ζ.asIdeal.comap (algebraMap O ↥(As O A)) = maximalIdeal O :=
  IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal ζ.asIdeal)
instance isLocalHom_algebraMap (ζ : Pts O A) : IsLocalHom (algebraMap O (Loc ζ)) := by
  constructor
  intro a ha
  by_contra hna
  have h1 : a ∈ maximalIdeal O := (IsLocalRing.mem_maximalIdeal a).2 hna
  rw [← comap_eq_maximalIdeal ζ, Ideal.mem_comap] at h1
  rw [IsScalarTower.algebraMap_apply O ↥(As O A) (Loc ζ),
    IsLocalization.AtPrime.isUnit_to_map_iff (Loc ζ) ζ.asIdeal] at ha
  exact ha h1
def vL (ζ : Pts O A) (a : ↥(As O A)) : ℕ∞ := Ring.ord (Loc ζ) (algebraMap ↥(As O A) (Loc ζ) a)
def ep (ϖ : O) (ζ : Pts O A) : ℕ := (vL ζ (algebraMap O ↥(As O A) ϖ)).toNat
def fdeg (ζ : Pts O A) : ℕ := Module.finrank (ResidueField O) (ResidueField (Loc ζ))
def ordAt (ϖ : O) (ζ : Pts O A) (n : ℕ) (a : ↥(As O A)) : WithTop ℤ :=
  (vL ζ a).map (Nat.cast : ℕ → ℤ) + ((-((n : ℤ) * (ep ϖ ζ : ℤ)) : ℤ) : WithTop ℤ)
open Classical in

def ord (ϖ : O) (ζ : Pts O A) (x : A) : WithTop ℤ :=
  if h : ∃ n : ℕ, ϖ ^ n • x ∈ As O A then ordAt ϖ ζ h.choose ⟨ϖ ^ h.choose • x, h.choose_spec⟩ else ⊤
variable (A) in

structure IsUnif (ϖ : O) : Prop where

  irreducible : Irreducible ϖ

  isUnit : IsUnit (algebraMap O A ϖ)

  denom : ∀ x : A, ∃ n : ℕ, ϖ ^ n • x ∈ As O A
section Val
variable (ζ : Pts O A) [IsDVRAt ζ]
end Val
section Ord
variable {ϖ : O}
variable (ζ : Pts O A) [IsDVRAt ζ]
end Ord
section Ord2
variable {ϖ : O}
end Ord2
section Ball
variable {V : Type*} [AddCommGroup V] [Module A V]
variable (A) in

def IsGen (e : V) : Prop := Function.Bijective (fun a : A => a • e)
def coord (e v : V) : A := Function.invFun (fun a : A => a • e) v
def ordV (ϖ : O) (ζ : Pts O A) (e : V) (c : Pts O A → ℤ) (v : V) : WithTop ℤ :=
  ord ϖ ζ (coord e v) + ((c ζ : ℤ) : WithTop ℤ)
def ballSet (ϖ : O) (e : V) (c : Pts O A → ℤ) : Set V := {v | ∀ ζ : Pts O A, 0 ≤ ordV ϖ ζ e c v}
def ball (ϖ : O) (e : V) (c : Pts O A → ℤ) : Submodule ↥(As O A) V :=
  Submodule.span ↥(As O A) (ballSet ϖ e c)
def ballO [Module O V] [IsScalarTower O A V] (ϖ : O) (e : V) (c : Pts O A → ℤ) : Submodule O V :=
  (ball ϖ e c).restrictScalars O
variable {ϖ : O} {e : V} (c : Pts O A → ℤ)
end Ball
section Compare
end Compare
section OrdZ
variable {ϖ : O} (ζ : Pts O A) [IsDVRAt ζ]
def ordZ (ϖ : O) (ζ : Pts O A) (x : A) : ℤ := (ord ϖ ζ x).untopD 0
end OrdZ
section Ball2
variable {V : Type*} [AddCommGroup V] [Module A V] {ϖ : O} {e : V} (c : Pts O A → ℤ)
def coordEquiv (he : IsGen A e) : V ≃ₗ[A] A :=
  (LinearEquiv.ofBijective (LinearMap.toSpanSingleton A V e) he).symm
end Ball2
section FieldCase
end FieldCase
end Formalism.MainNotions.Gaps.EtaleWeightGaps


