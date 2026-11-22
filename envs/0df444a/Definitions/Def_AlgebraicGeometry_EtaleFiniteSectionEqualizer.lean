-- Prove2me | Definitions.Def_AlgebraicGeometry_EtaleFiniteSectionEqualizer
-- name    : AlgebraicGeometry_EtaleFiniteSectionEqualizer
-- status  : Definition
-- author  : @tomasz
-- created : 2026-11-22T01:32:02.901812+00:00
-- url     : https://prove2.me/theorems/5dfe2bf5-1239-4ff3-9c4f-7065fd66a398
-- title:
--   Étale section equalizers for finite surjective covers
-- statement:
--   The sheaf and global section equalizers of a finite surjective cover.

import Definitions.Def_AlgebraicGeometry_EtaleFiniteStalkEqualizer

noncomputable section

section

section

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PhilipponEtaleAcyclicCohomology (globalSections)
open PhilipponEtaleClosedPushforward (pushforward)
open PhilipponEtaleGeometricStalks
  (algebraicallyClosedGeometricMap algebraicallyClosedGeometricPoints_conservative)
open PhilipponEtalePullbackComposition (restrictDirectImage unit_restrictDirectImage)
open PhilipponEtaleSmallSite (pullbackAdjunction pullbackSheaves)
open PhilipponEtaleStrictHenselization (toBase)


namespace PhilipponFiniteEtaleDescent

universe u

private abbrev Ab (X : Scheme.{u}) := Sheaf X.smallEtaleTopology AddCommGrpCat.{u}

/-- A scheme is a coproduct of strictly henselian local spectra with
closed inclusions. -/
def HasClosedStrictLocalComponents (W : Scheme.{u}) : Prop :=
  ∃ (I : Type u) (B : I → Type u) (_ : ∀ i, CommRing (B i))
    (h : ∀ i, HenselianLocalRing (B i)),
    (∀ i, let _ := h i; IsSepClosed (IsLocalRing.ResidueField (B i))) ∧
      ∃ c : (∐ fun i ↦ Spec (.of (B i))) ≅ W,
        ∀ i, IsClosedImmersion (Sigma.ι (fun j ↦ Spec (.of (B j))) i ≫ c.hom)

variable {X Y Z : Scheme.{u}} (p : Y ⟶ X) (d₁ d₂ : Z ⟶ Y) (ρ : Z ⟶ X)
  (h₁ : d₁ ≫ p = ρ) (h₂ : d₂ ≫ p = ρ)

/-- The unit induces a map to the equalizer of the restrictions to the double overlap. -/
def unitToEqualizer (F : Ab X) :
    F ⟶ equalizer (restrictDirectImage p d₁ ρ h₁ F) (restrictDirectImage p d₂ ρ h₂ F) :=
  equalizer.lift ((pullbackAdjunction p).unit.app F)
    ((unit_restrictDirectImage p d₁ ρ h₁ F).trans (unit_restrictDirectImage p d₂ ρ h₂ F).symm)

set_option maxRecDepth 4096 in
/-- For a finite surjection, the unit identifies an étale sheaf with the
equalizer of its two restrictions on the overlap, using the decomposition
of the strict-local pullbacks. -/
theorem isIso_unitToEqualizer [IsFinite p] [Surjective p] (hsq : IsPullback d₁ d₂ p p)
    (hSplit : ∀ x : X, HasClosedStrictLocalComponents (pullback (toBase (algebraicallyClosedGeometricMap x)) p))
    (F : Ab X) : IsIso (unitToEqualizer p d₁ d₂ ρ h₁ h₂ F) := by
  let Φ (x : X) := Scheme.pointSmallEtale (algebraicallyClosedGeometricMap x)
  let P := ObjectProperty.ofObj Φ
  have hP : P.IsConservativeFamilyOfPoints := algebraicallyClosedGeometricPoints_conservative X
  let δ₁ := restrictDirectImage p d₁ ρ h₁ F
  let δ₂ := restrictDirectImage p d₂ ρ h₂ F
  let κ := unitToEqualizer p d₁ d₂ ρ h₁ h₂ F
  let k := equalizer.ι δ₁ δ₂
  let η := (pullbackAdjunction p).unit.app F
  have hκ : κ ≫ k = η := equalizer.lift_ι _ _
  apply ((hP.jointlyReflectIsomorphisms AddCommGrpCat.{u}).isIso_iff κ).mpr
  intro Ψ
  obtain ⟨x, hx⟩ := (ObjectProperty.ofObj_iff Φ Ψ.obj).mp Ψ.property
  rw [← hx]
  obtain ⟨I, B, hB, hH, hSep, c, hc⟩ := hSplit x
  let _ : ∀ i, CommRing (B i) := hB
  let _ : ∀ i, HenselianLocalRing (B i) := hH
  let _ : ∀ i, IsSepClosed (IsLocalRing.ResidueField (B i)) := hSep
  let S := (Φ x).sheafFiber (A := AddCommGrpCat.{u})
  obtain ⟨hη, hImage⟩ := PhilipponFiniteStalkDescent.unit_exact_on_stalk
    p (algebraicallyClosedGeometricMap x) B d₁ d₂ ρ hsq h₁ h₂ c hc F
  have hα : S.map κ ≫ S.map k = S.map η := by rw [← S.map_comp, hκ]
  have hEqual : S.map k ≫ S.map δ₁ = S.map k ≫ S.map δ₂ := by
    rw [← S.map_comp, ← S.map_comp]
    exact congrArg S.map (equalizer.condition δ₁ δ₂)
  have hk : Function.Injective (S.map k) := (AddCommGrpCat.mono_iff_injective _).1 inferInstance
  change IsIso (S.map κ)
  apply (ConcreteCategory.isIso_iff_bijective _).2
  constructor
  · intro a b hab
    apply hη
    exact (ConcreteCategory.congr_hom hα a).symm.trans
      ((congrArg (S.map k) hab).trans (ConcreteCategory.congr_hom hα b))
  · intro b
    obtain ⟨a, ha⟩ := hImage (S.map k b) (ConcreteCategory.congr_hom hEqual b)
    exact ⟨a, hk ((ConcreteCategory.congr_hom hα a).trans ha)⟩

private theorem preimage_of_equalizer {C : Type*} [Category C] (U : C ⥤ Type u)
    {D E T : C} (f g : E ⟶ T) [HasEqualizer f g] [PreservesLimit (parallelPair f g) U]
    (κ : D ⟶ equalizer f g) [IsIso κ]
    (b : U.obj E) (hb : U.map f b = U.map g b) :
    ∃ a : U.obj D, U.map (κ ≫ equalizer.ι f g) a = b := by
  let v := U.map κ ≫ equalizerComparison f g U ≫ (Types.equalizerIso (U.map f) (U.map g)).hom
  have h : v ≫ ↾Subtype.val = U.map (κ ≫ equalizer.ι f g) := by
    dsimp only [v]
    simp only [Category.assoc, Types.equalizerIso_hom_comp_subtype,
      equalizerComparison_comp_π, U.map_comp]
  let t : {x : U.obj E // U.map f x = U.map g x} := ⟨b, hb⟩
  refine ⟨inv v t, ?_⟩
  exact (ConcreteCategory.congr_hom h (inv v t)).symm.trans
    (congrArg Subtype.val (ConcreteCategory.congr_hom (IsIso.inv_hom_id v) t))

set_option maxRecDepth 4096 in
/-- In any limit-preserving evaluation of the descent equalizer, an
element agreeing on the overlap comes from the base. -/
theorem exists_preimage_of_agreement [IsFinite p] [Surjective p] (hsq : IsPullback d₁ d₂ p p)
    (hSplit : ∀ x : X, HasClosedStrictLocalComponents (pullback (toBase (algebraicallyClosedGeometricMap x)) p))
    (U : Ab X ⥤ Type u) [PreservesLimitsOfShape WalkingParallelPair U]
    (F : Ab X) (b : U.obj ((pushforward p).obj ((pullbackSheaves p).obj F)))
    (hb : U.map (restrictDirectImage p d₁ ρ h₁ F) b =
      U.map (restrictDirectImage p d₂ ρ h₂ F) b) :
    ∃ a : U.obj F, U.map ((pullbackAdjunction p).unit.app F) a = b := by
  let δ₁ := restrictDirectImage p d₁ ρ h₁ F
  let δ₂ := restrictDirectImage p d₂ ρ h₂ F
  let κ := unitToEqualizer p d₁ d₂ ρ h₁ h₂ F
  let k := equalizer.ι δ₁ δ₂
  have hκ : κ ≫ k = (pullbackAdjunction p).unit.app F := equalizer.lift_ι _ _
  let : IsIso κ := isIso_unitToEqualizer p d₁ d₂ ρ h₁ h₂ hsq hSplit F
  obtain ⟨a, ha⟩ := preimage_of_equalizer U δ₁ δ₂ κ b hb
  exact ⟨a, (ConcreteCategory.congr_hom (congrArg U.map hκ) a).symm.trans ha⟩

private theorem globalSectionsForget_preservesEqualizers (X : Scheme.{u}) :
    PreservesLimitsOfShape WalkingParallelPair (globalSections X ⋙ forget AddCommGrpCat.{u}) := by
  change PreservesLimitsOfShape WalkingParallelPair
    (sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u} ⋙
      (CategoryTheory.evaluation _ _).obj (Opposite.op (Scheme.Etale.mk (𝟙 X))) ⋙
      forget AddCommGrpCat.{u})
  infer_instance

/-- A global section of the direct image with equal restrictions on the
overlap is the image of a section of the base sheaf. -/
theorem exists_section_of_agreement [IsFinite p] [Surjective p] (hsq : IsPullback d₁ d₂ p p)
    (hSplit : ∀ x : X, HasClosedStrictLocalComponents (pullback (toBase (algebraicallyClosedGeometricMap x)) p))
    (F : Ab X) (b : (globalSections X).obj ((pushforward p).obj ((pullbackSheaves p).obj F)))
    (hb : (globalSections X).map (restrictDirectImage p d₁ ρ h₁ F) b =
      (globalSections X).map (restrictDirectImage p d₂ ρ h₂ F) b) :
    ∃ a : (globalSections X).obj F, (globalSections X).map ((pullbackAdjunction p).unit.app F) a = b := by
  let U := globalSections X ⋙ forget AddCommGrpCat.{u}
  let : PreservesLimitsOfShape WalkingParallelPair U := globalSectionsForget_preservesEqualizers X
  exact exists_preimage_of_agreement p d₁ d₂ ρ h₁ h₂ hsq hSplit U F b hb

end PhilipponFiniteEtaleDescent

end

end


