-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_UnitaryThreeGroups_BaseRepGL3NormalisedOfPsiEqOne
-- name    : Development_AutomorphicArithmetic_AutomorphicVarieties_UnitaryThreeGroups_BaseRepGL3NormalisedOfPsiEqOne
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:41:31.401804+00:00
-- url     : https://prove2.me/theorems/dd49c886-3b22-49b5-aeed-b286c497a8c3
-- title:
--   Base Rep GL3 Normalised Of Psi Eq One
-- statement:
--   Definitions and structural lemmas for Base Rep GL3 Normalised Of Psi Eq One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/AutomorphicVarieties/UnitaryThreeGroups/BaseRepGL3NormalisedOfPsiEqOne.lean

import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_UnitaryThreeGroups_UnitaryThreeReflectionRight
import Theorems.Thm_UpperTheory_V_U3_unitaryThreeReflection_left
import Theorems.Thm_UpperTheory_V_U3_unitaryThreeReflection_right
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] UpperTheory.V.U3.unitaryThreeReflection_left
attribute [local simp] UpperTheory.V.U3.unitaryThreeReflection_right


set_option autoImplicit false
namespace UpperTheory.V.U3
open Matrix
section Shape
variable {G : Type*} [Group G] {R : Type*} [CommRing R]
def HasMult {m : ℕ} (η : G →* ℤˣ) (r : G →* GG m R) : Prop := ∀ g, (r g).right = η g
def zeta (c g₁ : G) (r : G →* GG 3 R) : R := zmat c g₁ r 0 0
def MatIrr {m : ℕ} (H : Subgroup G) (a : G → Matrix (Fin m) (Fin m) R) : Prop :=
  ∀ W : Submodule R (Fin m → R), (∀ g ∈ H, ∀ v ∈ W, a g *ᵥ v ∈ W) → W = ⊥ ∨ W = ⊤
def mats {m : ℕ} (r : G →* GG m R) (g : G) : Matrix (Fin m) (Fin m) R := (r g).mat
def TypeI (η : G →* ℤˣ) (r : G →* GG 3 R) : Prop := MatIrr η.ker (mats r)
def Upper (η : G →* ℤˣ) (r : G →* GG 3 R) : Prop := ∀ g ∈ η.ker, ∀ a b, wt a b < 0 → (r g).mat a b = 0
def Lower (η : G →* ℤˣ) (r : G →* GG 3 R) : Prop := ∀ g ∈ η.ker, ∀ a b, 0 < wt a b → (r g).mat a b = 0
def Block (η : G →* ℤˣ) (r : G →* GG 3 R) : Prop := ∀ g ∈ η.ker, ∀ a b, Odd (wt a b) → (r g).mat a b = 0
def corner (X : Matrix (Fin 3) (Fin 3) R) : Matrix (Fin 2) (Fin 2) R := X.submatrix ![0, 2] ![0, 2]
def TypeII (η : G →* ℤˣ) (r : G →* GG 3 R) : Prop :=
  Block η r ∧ MatIrr η.ker fun g => corner (r g).mat
def Wfun (r : G →* GG 3 R) (g : G) : Matrix (Fin 2) (Fin 2) R :=
  if (r g).right = 1 then corner (r g).mat else corner (r g).mat * Matrix.diagonal ![-1, 1]
def MatIso {m : ℕ} (H : Subgroup G) (a a' : G → Matrix (Fin m) (Fin m) R) : Prop :=
  ∃ M : GL (Fin m) R, ∀ g ∈ H, (M : Matrix (Fin m) (Fin m) R) * a g = a' g * M
end Shape
section Deform
variable {G : Type*} [Group G] {C : Type*} [CommRing C] {m : ℕ}
def IsCoc (r : G →* GG m C) (γ : G → Matrix (Fin m) (Fin m) C) : Prop :=
  ∀ g h, γ (g * h) = γ g + adRep r g (γ h)
def EntIn (I : Ideal C) (X : Matrix (Fin m) (Fin m) C) : Prop := ∀ a b, X a b ∈ I
def IsDeform (r : G →* GG m C) (γ : G → Matrix (Fin m) (Fin m) C) (r' : G →* GG m C) : Prop :=
  ∀ g, (r' g).right = (r g).right ∧ (r' g).mat = (1 + γ g) * (r g).mat
def zvar (c g₁ : G) (r : G →* GG 3 C) (γ : G → Matrix (Fin 3) (Fin 3) C) : Matrix (Fin 3) (Fin 3) C :=
  γ g₁ * (r g₁).mat - γ (gstar c g₁) * (r (gstar c g₁)).mat
structure NormCoc (c g₁ : G) (r : G →* GG 3 C) (γ : G → Matrix (Fin 3) (Fin 3) C) : Prop where
  atc : γ c = 0
  z12 : zvar c g₁ r γ 0 1 = 0
  z21 : zvar c g₁ r γ 1 0 = 0
def cob (r : G →* GG m C) (X : Matrix (Fin m) (Fin m) C) (g : G) : Matrix (Fin m) (Fin m) C :=
  X - adRep r g X
def CongOne (I : Ideal C) (h : GL (Fin m) C) : Prop := EntIn I ((h : Matrix (Fin m) (Fin m) C) - 1)
end Deform
structure Marks {G : Type*} [Group G] {k : Type*} [CommRing k] (η : G →* ℤˣ) (Ψ : G →* kˣ) (c g₁ : G) : Prop where
  csq : c * c = 1
  ηc : η c = -1
  Ψc : Ψ c = 1
  ηg : η g₁ = 1
  Ψg : IsUnit (((Ψ g₁ : kˣ) : k) ^ 2 - 1)
example : Marks (G := ℤˣ × ℚˣ) (k := ℚ) (MonoidHom.fst _ _) (MonoidHom.snd _ _) (-1, 1)
    (1, Units.mk0 2 two_ne_zero) :=
  ⟨by simp, rfl, rfl, rfl, by norm_num⟩
end UpperTheory.V.U3


