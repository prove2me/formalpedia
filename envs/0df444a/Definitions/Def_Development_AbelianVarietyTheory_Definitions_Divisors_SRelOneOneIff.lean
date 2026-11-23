-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_SRelOneOneIff
-- name    : Development_AbelianVarietyTheory_Definitions_Divisors_SRelOneOneIff
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:35:17.090476+00:00
-- url     : https://prove2.me/theorems/3fa14e52-60e7-4c53-a485-601ad478f7f5
-- title:
--   SRel One One Iff
-- statement:
--   Definitions and structural lemmas for SRel One One Iff, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/SRelOneOneIff.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSeparatedOfIsQProjOver
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZM
open scoped CategoryTheory.Obj
noncomputable section
namespace GlobalTheory.SiegLev
def SRelBy {h n' n : ℕ} {B' B : Type} [CommRing B'] [CommRing B] {ζ' : B'} {ζ : B} {S' S : Scheme.{0}} {s' : S' ⟶ Sp B'}
    {s : S ⟶ Sp B} (c' : SiegPre h n' ζ' s') (c : SiegPre h n ζ s) (d' d : ℕ) (f : S' ⟶ S) (φ : c'.A.left ⟶ c.A.left) :
    Prop :=
  IsGrpPullback c'.A c.A f φ ∧ (∃ φ₂ : (G2 c'.A).left ⟶ (G2 c.A).left, IsSquare φ φ₂ ∧ LBIso c'.P (c.P.pull φ₂)) ∧
    ∀ a, (c'.lev a ^ d').left ≫ φ = f ≫ (c.lev a ^ d).left
def SRel {h n' n : ℕ} {B' B : Type} [CommRing B'] [CommRing B] {ζ' : B'} {ζ : B} {S' S : Scheme.{0}} {s' : S' ⟶ Sp B'}
    {s : S ⟶ Sp B} (c' : SiegPre h n' ζ' s') (c : SiegPre h n ζ s) (d' d : ℕ) (f : S' ⟶ S) : Prop :=
  ∃ φ, SRelBy c' c d' d f φ
theorem sRel_one_one_iff {h n : ℕ} {B' B : Type} [CommRing B'] [CommRing B] {ζ' : B'} {ζ : B} {S' S : Scheme.{0}}
    {s' : S' ⟶ Sp B'} {s : S ⟶ Sp B} (c' : SiegPre h n ζ' s') (c : SiegPre h n ζ s) (f : S' ⟶ S) :
    SRel c' c 1 1 f ↔ SiegPB c' c f := by
  unfold SRel SRelBy SiegPB
  simp only [pow_one]
  constructor
  · rintro ⟨φ, hpb, ⟨φ₂, hsq, hiso⟩, hlev⟩
    exact ⟨φ, φ₂, hpb, hsq, hiso, hlev⟩
  · rintro ⟨φ, φ₂, hpb, hsq, hiso, hlev⟩
    exact ⟨φ, hpb, ⟨φ₂, hsq, hiso⟩, hlev⟩
structure SQuot {h N : ℕ} {o' : Type} [CommRing o'] {ζ' : o'} (F : SFam h N ζ') (n : ℕ) {o : Type} [CommRing o] (ζ : o)
    (j : o →+* o') where

  X : Scheme.{0}

  s : X ⟶ Sp o

  smooth : SmoothOfRelativeDimension (h * (h + 1) / 2) s

  qproj : IsQProjOver s

  univ : SiegPre h n ζ s

  princ : univ.Principal

  π : F.X ⟶ X

  base : π ≫ s = F.s ≫ spMap j

  fin : IsFinite π

  etale : Etale π

  onto : Surjective π

  low : SRel F.univ univ (N / n) 1 π

  fibre : ∀ (R : Type) [CommRing R] [IsLocalRing R] (y y' : Sp R ⟶ F.X) (s' : Sp R ⟶ Sp o) (c : SiegPre h n ζ s'),
    y ≫ F.s ≫ spMap j = y' ≫ F.s ≫ spMap j → SRel c F.univ 1 (N / n) y → SRel c F.univ 1 (N / n) y' → y ≫ π = y' ≫ π
def SQuot.self {h N : ℕ} {o : Type} [CommRing o] {ζ : o} (F : SFam h N ζ) (hN : 0 < N)
    (hid : SiegPB F.univ F.univ (𝟙 _)) : SQuot F N ζ (RingHom.id o) where
  X := F.X
  s := F.s
  smooth := F.smooth
  qproj := F.qproj
  univ := F.univ
  princ := F.princ
  π := 𝟙 _
  base := by rw [show spMap (RingHom.id o) = 𝟙 _ from Spec.map_id _]; simp
  fin := inferInstance
  etale := inferInstance
  onto := inferInstance
  low := by rw [Nat.div_self hN, sRel_one_one_iff]; exact hid
  fibre R _ _ y y' s' c h₁ h₂ h₃ := by
    rw [Nat.div_self hN, sRel_one_one_iff] at h₂ h₃
    rw [show spMap (RingHom.id o) = 𝟙 _ from Spec.map_id _] at h₁
    simpa using F.inj R y y' s' c (by simpa using h₁) h₂ h₃
end GlobalTheory.SiegLev


