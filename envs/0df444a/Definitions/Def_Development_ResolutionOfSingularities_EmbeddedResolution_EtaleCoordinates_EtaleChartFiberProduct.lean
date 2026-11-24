-- Prove2me | Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleChartFiberProduct
-- name    : Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_EtaleChartFiberProduct
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:02:21.081821+00:00
-- url     : https://prove2.me/theorems/f1c047d0-1e94-4fbc-b10c-9605a9d6fd23
-- title:
--   Etale Chart Fiber Product
-- statement:
--   Definitions and structural lemmas for Etale Chart Fiber Product, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/EtaleCoordinates/EtaleChartFiberProduct.lean

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_EtaleCoordinates_StrictNormalCrossings
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace
noncomputable section
namespace FunctorialResolution.EmbeddedResolution
abbrev affineSpaceCoord (k : Type u) [Field k] (m : ℕ) (j : Fin m) :=
  AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up j : ULift.{u} (Fin m))
section
variable {X : Scheme.{u}} {k : Type u} [Field k] {q : X ⟶ Spec (CommRingCat.of k)}
  {U : X.Opens} {m : ℕ}
@[reducible] def EtaleChart.coordTop (c : EtaleChart q U m) (j : Fin m) :
    U.toScheme.presheaf.obj (op ⊤) :=
  c.map.appTop.hom (affineSpaceCoord k m j)
end
def pointOfMem {P : Scheme.{u}} (V : P.Opens) (p : ↥P) (hp : p ∈ V) : ↥(V.toScheme) :=
  ⟨p, hp⟩
def specResidueFieldPoint {X : Scheme.{u}} (x : ↥X) : ↥(Spec (X.residueField x)) :=
  (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (X.residueField x))
section
variable {P : Scheme.{u}} {k : Type u} [Field k] {q : P ⟶ Spec (CommRingCat.of k)}
  {V : P.Opens} {n : ℕ}
abbrev chartPullback (c₁ c₂ : EtaleChart q V n) : Scheme.{u} := pullback c₁.map c₂.map
abbrev chartPullbackFst (c₁ c₂ : EtaleChart q V n) : chartPullback c₁ c₂ ⟶ P :=
  pullback.fst c₁.map c₂.map ≫ V.ι
abbrev chartPullbackSnd (c₁ c₂ : EtaleChart q V n) : chartPullback c₁ c₂ ⟶ P :=
  pullback.snd c₁.map c₂.map ≫ V.ι
theorem etale_pullback_fst_map (c₁ c₂ : EtaleChart q V n) :
    AlgebraicGeometry.Etale (pullback.fst c₁.map c₂.map) := by
  have : AlgebraicGeometry.Etale c₂.map := c₂.isEtale
  infer_instance
instance instEtalePullbackFstChart (c₁ c₂ : EtaleChart q V n) :
    AlgebraicGeometry.Etale (pullback.fst c₁.map c₂.map) :=
  etale_pullback_fst_map c₁ c₂
theorem etale_pullback_snd_map (c₁ c₂ : EtaleChart q V n) :
    AlgebraicGeometry.Etale (pullback.snd c₁.map c₂.map) := by
  have h1 : AlgebraicGeometry.Etale c₁.map := c₁.isEtale
  have h2 : AlgebraicGeometry.Etale c₂.map := c₂.isEtale
  exact inferInstance
instance instEtalePullbackSndChart (c₁ c₂ : EtaleChart q V n) :
    AlgebraicGeometry.Etale (pullback.snd c₁.map c₂.map) :=
  etale_pullback_snd_map c₁ c₂
theorem etale_comp {A B C : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C)
    (hf : AlgebraicGeometry.Etale f) (hg : AlgebraicGeometry.Etale g) :
    AlgebraicGeometry.Etale (f ≫ g) := by
  have := hf
  have := hg
  infer_instance
theorem etale_chartPullbackFst (c₁ c₂ : EtaleChart q V n) :
    AlgebraicGeometry.Etale (chartPullbackFst c₁ c₂) := by
  have h₁ : AlgebraicGeometry.Etale (pullback.fst c₁.map c₂.map) :=
    etale_pullback_fst_map c₁ c₂
  have h₂ : AlgebraicGeometry.Etale V.ι := inferInstance
  show AlgebraicGeometry.Etale (pullback.fst c₁.map c₂.map ≫ V.ι)
  exact etale_comp _ _ h₁ h₂
instance instEtaleChartPairFst (c₁ c₂ : EtaleChart q V n) :
    AlgebraicGeometry.Etale (chartPullbackFst c₁ c₂) :=
  etale_chartPullbackFst c₁ c₂
theorem etale_chartPullbackSnd (c₁ c₂ : EtaleChart q V n) :
    AlgebraicGeometry.Etale (chartPullbackSnd c₁ c₂) := by
  have h₁ : AlgebraicGeometry.Etale (pullback.snd c₁.map c₂.map) :=
    etale_pullback_snd_map c₁ c₂
  have h₂ : AlgebraicGeometry.Etale V.ι := inferInstance
  show AlgebraicGeometry.Etale (pullback.snd c₁.map c₂.map ≫ V.ι)
  exact etale_comp _ _ h₁ h₂
instance instEtaleChartPairSnd (c₁ c₂ : EtaleChart q V n) :
    AlgebraicGeometry.Etale (chartPullbackSnd c₁ c₂) :=
  etale_chartPullbackSnd c₁ c₂
abbrev ChartsAgreeAt (c₁ c₂ : EtaleChart q V n) (p : ↥P) (hp : p ∈ V) : Prop :=
  V.toScheme.fromSpecResidueField (pointOfMem V p hp) ≫ c₁.map =
    V.toScheme.fromSpecResidueField (pointOfMem V p hp) ≫ c₂.map
def chartPullbackLift (c₁ c₂ : EtaleChart q V n) (p : ↥P) (hp : p ∈ V)
    (h : ChartsAgreeAt c₁ c₂ p hp) :
    Spec (V.toScheme.residueField (pointOfMem V p hp)) ⟶ chartPullback c₁ c₂ :=
  pullback.lift (V.toScheme.fromSpecResidueField (pointOfMem V p hp))
    (V.toScheme.fromSpecResidueField (pointOfMem V p hp)) h
@[simp] theorem chartPullbackLift_fst (c₁ c₂ : EtaleChart q V n) (p : ↥P) (hp : p ∈ V)
    (h : ChartsAgreeAt c₁ c₂ p hp) :
    chartPullbackLift c₁ c₂ p hp h ≫ pullback.fst c₁.map c₂.map =
      V.toScheme.fromSpecResidueField (pointOfMem V p hp) :=
  pullback.lift_fst _ _ _
@[simp] theorem chartPullbackLift_snd (c₁ c₂ : EtaleChart q V n) (p : ↥P) (hp : p ∈ V)
    (h : ChartsAgreeAt c₁ c₂ p hp) :
    chartPullbackLift c₁ c₂ p hp h ≫ pullback.snd c₁.map c₂.map =
      V.toScheme.fromSpecResidueField (pointOfMem V p hp) :=
  pullback.lift_snd _ _ _
@[simp] theorem chartPullbackLift_fst_assoc {W : Scheme.{u}} (c₁ c₂ : EtaleChart q V n) (p : ↥P)
    (hp : p ∈ V) (h : ChartsAgreeAt c₁ c₂ p hp) (g : V.toScheme ⟶ W) :
    chartPullbackLift c₁ c₂ p hp h ≫ pullback.fst c₁.map c₂.map ≫ g =
      V.toScheme.fromSpecResidueField (pointOfMem V p hp) ≫ g := by
  rw [← Category.assoc, chartPullbackLift_fst]
@[simp] theorem chartPullbackLift_snd_assoc {W : Scheme.{u}} (c₁ c₂ : EtaleChart q V n) (p : ↥P)
    (hp : p ∈ V) (h : ChartsAgreeAt c₁ c₂ p hp) (g : V.toScheme ⟶ W) :
    chartPullbackLift c₁ c₂ p hp h ≫ pullback.snd c₁.map c₂.map ≫ g =
      V.toScheme.fromSpecResidueField (pointOfMem V p hp) ≫ g := by
  rw [← Category.assoc, chartPullbackLift_snd]
def chartPullbackPoint (c₁ c₂ : EtaleChart q V n) (p : ↥P) (hp : p ∈ V)
    (h : ChartsAgreeAt c₁ c₂ p hp) : ↥(chartPullback c₁ c₂) :=
  (chartPullbackLift c₁ c₂ p hp h).base (specResidueFieldPoint (pointOfMem V p hp))
theorem chartPullbackFst_base_chartPullbackPoint (c₁ c₂ : EtaleChart q V n) (p : ↥P) (hp : p ∈ V)
    (h : ChartsAgreeAt c₁ c₂ p hp) :
    (chartPullbackFst c₁ c₂).base (chartPullbackPoint c₁ c₂ p hp h) = p := by
  have hfs : (V.toScheme.fromSpecResidueField (pointOfMem V p hp)).base
      (specResidueFieldPoint (pointOfMem V p hp)) = pointOfMem V p hp := by
    simp
  have e : (chartPullbackLift c₁ c₂ p hp h ≫ pullback.fst c₁.map c₂.map).base
      (specResidueFieldPoint (pointOfMem V p hp)) = pointOfMem V p hp := by
    rw [chartPullbackLift_fst]
    exact hfs
  have key : (pullback.fst c₁.map c₂.map).base (chartPullbackPoint c₁ c₂ p hp h)
      = pointOfMem V p hp := e
  have key2 : V.ι.base ((pullback.fst c₁.map c₂.map).base (chartPullbackPoint c₁ c₂ p hp h))
      = V.ι.base (pointOfMem V p hp) := by rw [key]
  exact key2
theorem comp_base_apply {A B C : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C)
    (x : ↥A) : (f ≫ g).base x = g.base (f.base x) := rfl
theorem chartPullbackSnd_base_chartPullbackPoint (c₁ c₂ : EtaleChart q V n) (p : ↥P) (hp : p ∈ V)
    (h : ChartsAgreeAt c₁ c₂ p hp) :
    (chartPullbackSnd c₁ c₂).base (chartPullbackPoint c₁ c₂ p hp h) = p := by
  have key := chartPullbackLift_snd_assoc c₁ c₂ p hp h V.ι
  have e1 : (V.toScheme.fromSpecResidueField (pointOfMem V p hp)).base
      (specResidueFieldPoint (pointOfMem V p hp)) = pointOfMem V p hp := by
    simp
  have e2 : V.ι.base (pointOfMem V p hp) = p := rfl
  have hA := comp_base_apply (chartPullbackLift c₁ c₂ p hp h)
      (pullback.snd c₁.map c₂.map ≫ V.ι) (specResidueFieldPoint (pointOfMem V p hp))
  have hB := comp_base_apply
      (V.toScheme.fromSpecResidueField (pointOfMem V p hp)) V.ι
      (specResidueFieldPoint (pointOfMem V p hp))
  have h3 : (chartPullbackLift c₁ c₂ p hp h ≫ pullback.snd c₁.map c₂.map ≫ V.ι).base
        (specResidueFieldPoint (pointOfMem V p hp))
      = (V.toScheme.fromSpecResidueField (pointOfMem V p hp) ≫ V.ι).base
        (specResidueFieldPoint (pointOfMem V p hp)) := by
    rw [key]
  exact hA.symm.trans (h3.trans (hB.trans ((congrArg (fun z => V.ι.base z) e1).trans e2)))
end
section
variable {P : Scheme.{u}} {k : Type u} [Field k] {q : P ⟶ Spec (CommRingCat.of k)}
  {V : P.Opens} {n : ℕ}
def chartPullbackFstStalkMap (c₁ c₂ : EtaleChart q V n) (p : ↥P) (hp : p ∈ V)
    (h : ChartsAgreeAt c₁ c₂ p hp) :
    P.presheaf.stalk p ⟶ (chartPullback c₁ c₂).presheaf.stalk (chartPullbackPoint c₁ c₂ p hp h) :=
  eqToHom (congrArg (fun y : ↥P => P.presheaf.stalk y)
      (chartPullbackFst_base_chartPullbackPoint c₁ c₂ p hp h).symm) ≫
    (chartPullbackFst c₁ c₂).stalkMap (chartPullbackPoint c₁ c₂ p hp h)
def chartPullbackSndStalkMap (c₁ c₂ : EtaleChart q V n) (p : ↥P) (hp : p ∈ V)
    (h : ChartsAgreeAt c₁ c₂ p hp) :
    P.presheaf.stalk p ⟶ (chartPullback c₁ c₂).presheaf.stalk (chartPullbackPoint c₁ c₂ p hp h) :=
  eqToHom (congrArg (fun y : ↥P => P.presheaf.stalk y)
      (chartPullbackSnd_base_chartPullbackPoint c₁ c₂ p hp h).symm) ≫
    (chartPullbackSnd c₁ c₂).stalkMap (chartPullbackPoint c₁ c₂ p hp h)
end
end FunctorialResolution.EmbeddedResolution


