-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_SpecialFibreUnits
-- name    : Development_AbelianVarietyTheory_BlockTheory_DivisorBase_SpecialFibreUnits
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:15:51.32036+00:00
-- url     : https://prove2.me/theorems/9f6e67c3-8f42-4b4a-9039-40a22f30f720
-- title:
--   Special Fibre Units
-- statement:
--   Definitions and structural lemmas for Special Fibre Units, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/SpecialFibreUnits.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_CubicalStructures_CubeSymmetricSwapFirst
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits
noncomputable section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Semi
def lbPow {Z : Scheme.{0}} (D : LB Z) (M : ℕ) : LB Z where
  ι := D.ι
  U := D.U
  g := fun i j => D.g i j ^ M
def constUnit {A : Type} [CommRing A] {T : Scheme.{0}} (p : T ⟶ Spec (.of A)) (a : Aˣ) :
    Γ(T, ⊤)ˣ :=
  Units.map p.appTop.hom.toMonoidHom
    (Units.map (Scheme.ΓSpecIso (.of A)).inv.hom.toMonoidHom a)
section Fibres
variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {Z : Scheme.{0}} (f : Z ⟶ Spec (.of O))
def specialFibre : Scheme.{0} :=
  pullback f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue O)))
def specialι : specialFibre f ⟶ Z := pullback.fst _ _
def reducedSpecialFibre : Scheme.{0} := (specialFibre f).nilradical.subscheme
def reducedSpecialι : reducedSpecialFibre f ⟶ Z :=
  (specialFibre f).nilradical.subschemeι ≫ specialι f
def genericFibre : Scheme.{0} :=
  pullback f (Spec.map (CommRingCat.ofHom (algebraMap O (FractionRing O))))
def genericι : genericFibre f ⟶ Z := pullback.fst _ _
def genericStr : genericFibre f ⟶ Spec (.of (FractionRing O)) := pullback.snd _ _
def unifUnit (ϖ : O) (hϖ : Irreducible ϖ) : (FractionRing O)ˣ :=
  Units.mk0 (algebraMap O (FractionRing O) ϖ)
    ((map_ne_zero_iff _ (IsFractionRing.injective O (FractionRing O))).2 hϖ.ne_zero)
def Hyp (D : LB Z) : Prop :=
  IsIntegral Z ∧ (∀ z : Z, IsIntegrallyClosed (Z.presheaf.stalk z)) ∧ IsProper f ∧ Flat f ∧
    ConnectedSpace (specialFibre f) ∧ D.IsLB ∧
    ∃ t : (D.pull (reducedSpecialι f)).Gen, t.IsGen
def PowEq (ϖ : O) (hϖ : Irreducible ϖ) (D : LB Z) (sig : (D.pull (genericι f)).Gen)
    (M : ℕ) (n : ℤ) (gen : (lbPow D M).Gen) : Prop :=
  ∀ j : PUnit → D.ι,
    sig.s j ^ M =
      res le_top (constUnit (genericStr f) (unifUnit ϖ hϖ)) ^ n *
        res (LB.wchart_le D (fun _ : PUnit => genericι f) j PUnit.unit)
          (pullU (genericι f) (D.U (j PUnit.unit)) (gen.s (j PUnit.unit)))
def IsCoord {R C : Type} [CommRing R] [Field C] [Algebra R C] (D : LB Z)
    (sig : (D.pull (genericι f)).Gen) (ybar : Spec (.of R) ⟶ Z)
    (y : Spec (.of C) ⟶ genericFibre f) (e : (D.pull ybar).Gen) (c : Cˣ) : Prop :=
  ∀ (j : PUnit → D.ι) (W : (Spec (.of C)).Opens)
    (h₁ : W ≤ y ⁻¹ᵁ (D.pull (genericι f)).U j)
    (h₂ : W ≤ Spec.map (CommRingCat.ofHom (algebraMap R C)) ⁻¹ᵁ (D.pull ybar).U j),
    res h₁ (pullU y _ (sig.s j)) =
      res le_top (constUnit (𝟙 (Spec (.of C))) c) *
        res h₂ (pullU (Spec.map (CommRingCat.ofHom (algebraMap R C))) _ (e.s j))
def ValConst (ϖ : O) (D : LB Z) (sig : (D.pull (genericι f)).Gen) (M : ℕ) (n : ℤ) : Prop :=
  ∀ (R C Γ₀ : Type) [CommRing R] [Field C] [Algebra R C] [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation C Γ₀), v.Integers R →
    ∀ (φ : O →+* R), Function.Injective φ → IsLocalHom φ →
    ∀ (ybar : Spec (.of R) ⟶ Z), ybar ≫ f = Spec.map (CommRingCat.ofHom φ) →
    ∀ (y : Spec (.of C) ⟶ genericFibre f),
      y ≫ genericι f = Spec.map (CommRingCat.ofHom (algebraMap R C)) ≫ ybar →
      (∃ (e : (D.pull ybar).Gen) (c : Cˣ), e.IsGen ∧ IsCoord f D sig ybar y e c) ∧
      ∀ (e : (D.pull ybar).Gen) (c : Cˣ), e.IsGen → IsCoord f D sig ybar y e c →
        v (c : C) ^ M = v (algebraMap R C (φ ϖ)) ^ n
end Fibres
def PropZ : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O) (hϖ : Irreducible ϖ)
    (Z : Scheme.{0}) (f : Z ⟶ Spec (.of O)) (D : LB Z), Hyp f D →
    ∀ sig : (D.pull (genericι f)).Gen, sig.IsGen →
      ∃ (M : ℕ) (n : ℤ), 1 ≤ M ∧
        (∃ gen : (lbPow D M).Gen, gen.IsGen ∧ PowEq f ϖ hϖ D sig M n gen) ∧
        ValConst f ϖ D sig M n
def PropZSlope : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O) (hϖ : Irreducible ϖ)
    (Z : Scheme.{0}) (f : Z ⟶ Spec (.of O)) (D : LB Z), Hyp f D →
    ∀ sig : (D.pull (genericι f)).Gen, sig.IsGen →
      ∃ ρ : ℚ, ∀ (M : ℕ) (n : ℤ), 1 ≤ M → (n : ℚ) = M * ρ →
        (∃ gen : (lbPow D M).Gen, gen.IsGen ∧ PowEq f ϖ hϖ D sig M n gen) ∧
        ValConst f ϖ D sig M n
def trivLB (Z : Scheme.{0}) : LB Z where
  ι := PUnit
  U := fun _ => ⊤
  g := fun _ _ => 1
end
end GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits


