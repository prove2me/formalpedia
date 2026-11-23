-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_GeomIntSelf
-- name    : Development_AbelianVarietyTheory_Definitions_KeyFormula_GeomIntSelf
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:33:15.299374+00:00
-- url     : https://prove2.me/theorems/2f39d44e-5ba1-401c-bc69-a06e1b80e8d3
-- title:
--   Geom Int Self
-- statement:
--   Definitions and structural lemmas for Geom Int Self, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/KeyFormula/GeomIntSelf.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_KeyRuleOneOfKeyFormula
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSeparatedOfIsQProjOver
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_LinCombTrivG
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.KeyFam
open GlobalTheory.KeyPow
def per {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (a : Fin g ⊕ Fin g → ℤ) : Fin g → ℂ :=
  τ.mulVec (fun i => (a (.inl i) : ℂ)) + fun i => (a (.inr i) : ℂ)
def PerLev (P : Out.PolAV (Sp ℂ)) {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (k : ℕ)
    (lev : (Fin g ⊕ Fin g → ℤ) → (𝟙_ (Over (Sp ℂ)) ⟶ P.A)) : Prop :=
  P.g = g ∧ τ.IsSymm ∧ (τ.map Complex.im).PosDef ∧ ∃ u : HolUnif P.A P.L g,
    (∀ z, z ∈ u.Λ ↔ ∃ a, z = per τ a) ∧
    (∀ (n : ℕ) (a b : Fin g ⊕ Fin g → ℤ) (c : ℂˣ), 0 < n →
      (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (omegaStd a b : ℂ) / n) →
      Out.WeilIs P.A P.L n (u.ex ((n : ℂ)⁻¹ • per τ a)) (u.ex ((n : ℂ)⁻¹ • per τ b)) (unitOn c)) ∧
    ∀ a, lev a = u.ex ((k : ℂ)⁻¹ • per τ a)
def PolPB {S S' : Scheme.{0}} (P' : Out.PolAV S') (P : Out.PolAV S) (f : S' ⟶ S) (φ : P'.A.left ⟶ P.A.left) : Prop :=
  IsGrpPullback P'.A P.A f φ ∧ P'.g = P.g ∧ LBIso P'.L (P.L.pull φ)
def LamIs {S S' : Scheme.{0}} (A : Over S') [GrpObj A] (L : LB A.left) (B : Over S) (Pb : LB (B ⊗ B).left)
    (φ : A.left ⟶ B.left) : Prop :=
  ∃ φ₂ : (A ⊗ A).left ⟶ (B ⊗ B).left, IsSquare φ φ₂ ∧ LBIso (abelian₂ A L) (Pb.pull φ₂)
variable {h k : ℕ} {o : Type} [CommRing o] {ζ : o} {S S' : Scheme.{0}} {s : S ⟶ Sp o}
def SqOf (P : Out.PolAV S') (c : SiegPre h k ζ s) (f : S' ⟶ S) (φ : P.A.left ⟶ c.A.left) : Prop :=
  IsGrpPullback P.A c.A f φ ∧ P.g = h ∧ LamIs P.A P.L c.A c.P φ
def PtAt (c : SiegPre h k ζ s) (p : Sp ℂ ⟶ S) (τ : Matrix (Fin h) (Fin h) ℂ) : Prop :=
  ∃ (P : Out.PolAV (Sp ℂ)) (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over (Sp ℂ)) ⟶ P.A)) (φ : P.A.left ⟶ c.A.left),
    PerLev P τ k lev ∧ SqOf P c p φ ∧ ∀ a, (lev a).left ≫ φ = p ≫ (c.lev a).left
def SameComp (s : S ⟶ Sp o) (σ : o →+* ℂ) (p q : Sp ℂ ⟶ S) : Prop :=
  ∃ (hp : p ≫ s = 𝟙 _ ≫ spMap σ) (hq : q ≫ s = 𝟙 _ ≫ spMap σ), ∀ z : Sp ℂ,
    pullback.lift p (𝟙 _) hp z ∈ connectedComponent (pullback.lift q (𝟙 _) hq z)
def TorsConst (A : Over S) [GrpObj A] (n : ℕ) : Prop :=
  ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S) (y : Over.mk x ⟶ A), y ^ n = 1 →
    ∃ t : 𝟙_ (Over S) ⟶ A, t ^ n = 1 ∧ y = toUnit _ ≫ t
def Val (x : KeyIn ℂ) (t : ℂ) : Prop :=
  ∃ (τ M : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (a b : Fin x.P.g → ℂ) (c : ℂ),
    charHalf _ a b ∧ c ≠ 0 ∧ NormalAt x τ M a b c ∧ t = M.det ^ 4 / c ^ 8
def Known (K : Type) [Field K] (y : KeyIn K) : Prop :=
  ∃ t₀ : K, ∀ (e : K →+* ℂ) (x : KeyIn ℂ), KeyPB x y e → Val x (e t₀)
def PotKnown (K : Type) [Field K] (P : Out.PolAV (Sp K)) : Prop :=
  ∃ (K' : Type) (_ : Field K') (_ : NumberField K') (j : K →+* K'),
    ∀ (K'' : Type) [Field K''] (j' : K' →+* K'') (y : KeyIn K'') (φ : y.P.A.left ⟶ P.A.left),
      PolPB y.P P (spMap (j'.comp j)) φ → Known K'' y
def GeomInt (K R : Type) [Field K] [CommRing R] [Algebra K R] : Prop :=
  Algebra.Smooth K R ∧ ∀ (K' : Type) [Field K'] [Algebra K K'], IsDomain (K' ⊗[K] R)
def PolFam : Prop :=
  ∀ P : Out.PolAV (Sp ℂ), 1 ≤ P.g →
    ∃ (K : Type) (_ : Field K) (_ : NumberField K) (R : Type) (_ : CommRing R) (_ : Algebra K R)
      (Q : Out.PolAV (Sp R)) (s : R →+* ℂ) (s₀ : R →ₐ[K] K) (φ : P.A.left ⟶ Q.A.left),
      GeomInt K R ∧ PolPB P Q (spMap s) φ ∧
      ∀ (P₀ : Out.PolAV (Sp K)) (φ₀ : P₀.A.left ⟶ Q.A.left), PolPB P₀ Q (spMap s₀.toRingHom) φ₀ → PotKnown K P₀
end GlobalTheory.KeyFam
end


