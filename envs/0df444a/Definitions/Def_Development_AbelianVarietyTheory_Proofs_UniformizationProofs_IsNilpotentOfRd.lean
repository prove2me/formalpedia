-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsNilpotentOfRd
-- name    : Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsNilpotentOfRd
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:47:36.635926+00:00
-- url     : https://prove2.me/theorems/60807c81-1794-4dbd-a1be-1b9482b3c865
-- title:
--   Is Nilpotent Of Rd
-- statement:
--   Definitions and structural lemmas for Is Nilpotent Of Rd, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/IsNilpotentOfRd.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open AddMonoidAlgebra
namespace GlobalTheory.CubeLift
variable {A : Type} [CommRing A] {X Y W : Type} [AddCommGroup X] [AddCommGroup Y] [AddCommGroup W]
abbrev mv (f : X →+ Y) : A[X] →+* A[Y] := mapDomainRingHom A f
def avg : A[X × Y] →+ A[Y] :=
  comapDomainAddMonoidHom (fun y : Y => ((0 : X), y)) fun _ _ h => congrArg Prod.snd h
abbrev tri (a b c : X →+ Y) : X × X × X →+ Y := a.coprod (b.coprod c)
abbrev rd (I : Ideal A) : A[X] →+* (A ⧸ I)[X] := mapRingHom X (Ideal.Quotient.mk I)
abbrev um (f : X →+ Y) : (A[X])ˣ →* (A[Y])ˣ := Units.map (mv f).toMonoidHom
def cong (I : Ideal A) : Subgroup (A[X])ˣ := (Units.map (rd I).toMonoidHom).ker
def lin (I : Ideal A) (u : (A[X])ˣ) : (A ⧸ I * I)[X] := rd (I * I) (u.val - 1)
def del (g : (A[X])ˣ) (a b c : X →+ Y) : (A[Y])ˣ :=
  um (a + b + c) g * um a g * um b g * um c g / um (a + b) g / um (a + c) g / um (b + c) g
abbrev p₁ : X →+ X × X × X := .inl X (X × X)
abbrev p₂ : X →+ X × X × X := (AddMonoidHom.inr X (X × X)).comp (.inl X X)
abbrev p₃ : X →+ X × X × X := (AddMonoidHom.inr X (X × X)).comp (.inr X X)
structure Cub (e : (A[X × X × X])ˣ) : Prop where
  s₁ : ∀ (Y : Type) [AddCommGroup Y] (a b c : X →+ Y), um (tri a b c) e = um (tri b a c) e
  s₂ : ∀ (Y : Type) [AddCommGroup Y] (a b c : X →+ Y), um (tri a b c) e = um (tri a c b) e
  co : ∀ (Y : Type) [AddCommGroup Y] (a b c d : X →+ Y),
    um (tri (a + b) c d) e * um (tri a b d) e = um (tri a (b + c) d) e * um (tri b c d) e
end GlobalTheory.CubeLift


