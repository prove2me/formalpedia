-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSeparatedOfIsQProjOver
-- name    : Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSeparatedOfIsQProjOver
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:08:58.33012+00:00
-- url     : https://prove2.me/theorems/e3b4da86-b9e3-4e56-8af9-68f2d2a5ef82
-- title:
--   Is Separated Of Is QProj Over
-- statement:
--   Definitions and structural lemmas for Is Separated Of Is QProj Over, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ModuliSpaces/IsSeparatedOfIsQProjOver.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsGaloisCover
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_AuxiliaryInertOddPrime
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
noncomputable section
namespace GlobalTheory.ZM
variable {o : Type} [CommRing o] {S : Scheme.{0}} {g k : ℕ} {J : Type} {b : TBase o k} {s : S ⟶ Sp o}
structure SFam (h k : ℕ) {o : Type} [CommRing o] (ζ : o) where

  X : Scheme.{0}

  s : X ⟶ Sp o

  smooth : SmoothOfRelativeDimension (h * (h + 1) / 2) s

  qproj : IsQProjOver s

  univ : SiegPre h k ζ s

  princ : univ.Principal

  rep : ∀ (S : Scheme.{0}) (s' : S ⟶ Sp o) (c : SiegPre h k ζ s'), IsReduced S → Dense {x : S | (s' x).asIdeal = ⊥} →
    c.Principal → ∃ f : S ⟶ X, f ≫ s = s' ∧ SiegPB c univ f

  inj : ∀ (R : Type) [CommRing R] [IsLocalRing R] (x y : Sp R ⟶ X) (s' : Sp R ⟶ Sp o) (c : SiegPre h k ζ s'),
    x ≫ s = y ≫ s → SiegPB c univ x → SiegPB c univ y → x = y
def SRep {h p M : ℕ} (Ag : SiegelFamily h p M) : Prop :=
  IsSeparated Ag.s ∧ ∀ (S : Scheme.{0}) (s' : S ⟶ Sp (ZP p M)) (c : SiegPre h M (zetaZP p M) s'), IsReduced S →
    Dense {x : S | (s' x).asIdeal = ⊥} → c.Principal → ∃ f : S ⟶ Ag.X, f ≫ Ag.s = s' ∧ SiegPB c Ag.univ f
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
def LevUnder (D : Datum H) (a : J → 𝓞 E) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La) (t : TObj g k J b s) (τ : SAB H S)
    (lev : D.La → (𝟙_ (Over S) ⟶ τ.G)) : Prop :=
  ∃ φ : τ.G ≅ t.A, IsMonHom φ.hom ∧ LBIso τ.PP.L (t.L.pull φ.hom.left) ∧
    (∀ j, τ.act.act (a j) ≫ φ.hom = φ.hom ≫ t.act j) ∧ (∀ x y, lev (x + y) = lev x * lev y) ∧
    ∀ i, (lev (bas (Pi.single i 1)) ≫ φ.hom).left = (t.pt i).left
def TSieg {La : Type} [AddCommGroup La] (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] La) (bas' : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] La)
    (t : TObj g k J b s) {B : Type} [CommRing B] {ζ : B} {s' : S ⟶ Sp B} (c : SiegPre g k ζ s') : Prop :=
  letI := t.ab.comm
  ∃ φ : c.A ≅ t.A, IsMonHom φ.hom ∧ LBIso c.P ((abelian₂ t.A t.L).pull (φ.hom ⊗ₘ φ.hom).left) ∧
    ∀ i, (c.lev (bas'.symm (bas (Pi.single i 1))) ≫ φ.hom).left = (t.pt i).left
structure PELRep (D : Datum H) (a : J → 𝓞 E) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La) (ρ : o) (t : TObj g k J b s) :
    Prop where

  qproj : IsQProjOver s

  flat : Flat s

  red : IsReduced S

  rep : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (β : o →+* V) (t' : TObj g k J b (spMap β))
    (τ' : SAB H (Sp V)), Function.Injective β → IsPEL D a bas ρ t' τ' → ∃ f : Sp V ⟶ S, f ≫ s = spMap β ∧ TMap t' t f

  inj : ∀ (R : Type) [CommRing R] [IsLocalRing R] (x y : Sp R ⟶ S) (s' : Sp R ⟶ Sp o) (t' : TObj g k J b s'),
    x ≫ s = y ≫ s → TMap t' t x → TMap t' t y → x = y
end GlobalTheory.ZM
end


