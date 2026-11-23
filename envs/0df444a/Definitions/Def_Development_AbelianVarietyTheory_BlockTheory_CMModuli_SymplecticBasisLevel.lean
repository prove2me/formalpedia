-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_SymplecticBasisLevel
-- name    : Development_AbelianVarietyTheory_BlockTheory_CMModuli_SymplecticBasisLevel
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:25:27.806905+00:00
-- url     : https://prove2.me/theorems/48c244ea-3d90-4dde-ab3f-1dd14864f467
-- title:
--   Symplectic Basis Level
-- statement:
--   Definitions and structural lemmas for Symplectic Basis Level, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/CMModuli/SymplecticBasisLevel.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_PeriodMapPresentation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.SymplecticBasisLevel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke.PeriodMapPresentation
open scoped Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
section Lattice
def weilVal (k : ℕ) (n : ℤ) : ℂ := Complex.exp (-(2 * Real.pi * Complex.I) * (n : ℂ) / k)
def IsMarking (D D' : Datum H) (l : Level H) (ζ : ℂ) (mk : D.La →ₗ[𝓞 E] D'.La) : Prop :=
  (∀ a : D.La, (∃ y : D'.La, mk a = l.M' • y) ↔ ∃ b : D.La, a = l.M' • b) ∧
  (∀ x : D'.La, ∃ (a : D.La) (y : D'.La), x = mk a + l.M' • y) ∧
  ∃ ζ' : ℂ, IsPrimitiveRoot ζ' l.M' ∧ ζ' ^ (l.M' / l.A) = ζ ∧
    ∀ a b : D.La, weilVal l.M' (D'.EF (mk a) (mk b)) = ζ' ^ D.EF a b
def FixesLevel (D' : Datum H) (l : Level H) (ψ : D'.La ≃ₗ[𝓞 E] D'.La) : Prop :=
  (∀ x y, D'.EF (ψ x) (ψ y) = D'.EF x y) ∧
  (∀ x, ψ x - x ∈ l.Mb • (⊤ : Submodule (𝓞 E) D'.La)) ∧
  ∀ x, ∃ y : D'.La, ψ x - x = l.A • y
def SamePoint (D' : Datum H) (l : Level H) {g : ℕ} (P P' : D'.La →+ (Fin g → ℂ)) : Prop :=
  ∃ (ψ : D'.La ≃ₗ[𝓞 E] D'.La) (T : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)), FixesLevel D' l ψ ∧ ∀ x, P' (ψ x) = T (P x)
def IsSympBasis (D' : Datum H) {g : ℕ} (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] D'.La) : Prop :=
  ∀ u v, D'.EF (bas u) (bas v) = omegaStd u v
def perE {D' : Datum H} {g : ℕ} (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] D'.La) (P : D'.La →+ (Fin g → ℂ)) :
    Matrix (Fin g) (Fin g) ℂ := Matrix.of fun i j => P (bas (Pi.single (Sum.inl j) 1)) i
def perF {D' : Datum H} {g : ℕ} (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] D'.La) (P : D'.La →+ (Fin g → ℂ)) :
    Matrix (Fin g) (Fin g) ℂ := Matrix.of fun i j => P (bas (Pi.single (Sum.inr j) 1)) i
def perTau {D' : Datum H} {g : ℕ} (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] D'.La) (P : D'.La →+ (Fin g → ℂ)) :
    Matrix (Fin g) (Fin g) ℂ := (perF bas P)⁻¹ * perE bas P
def IsHalf {g : ℕ} (a : Fin g → ℂ) : Prop := ∀ i, a i = 0 ∨ a i = 1 / 2
end Lattice
section Fibre
variable {D : Datum H} {l : Level H} (Xo : Moduli D l) {g : ℕ} (ty : Fin g → (E →+* ℂ))
abbrev univG : Over Xo.X := Xo.univ.t.G
def IsFibre (D' : Datum H) (mk : D.La →ₗ[𝓞 E] D'.La) (P : D'.La →+ (Fin g → ℂ)) (y : Sp ℂ ⟶ Xo.X)
    (ex : (Fin g → ℂ) → (Over.mk y ⟶ univG Xo)) : Prop :=
  (∀ z w, ex (z + w) = ex z * ex w) ∧
  Function.Surjective ex ∧
  (∀ z, ex z = 1 ↔ ∃ x : D'.La, z = P x) ∧
  (∀ (a : 𝓞 E) z, ex (tyAct ty a z) = ex z ≫ Xo.univ.t.act.act a) ∧
  (∀ (k : ℕ) (a b : D'.La) (c : ℂˣ), 0 < k → (c : ℂ) = weilVal k (D'.EF a b) →
    Out.WeilIs (univG Xo) Xo.univ.t.PP.L k (ex ((k : ℂ)⁻¹ • P a)) (ex ((k : ℂ)⁻¹ • P b)) (unitOn c)) ∧
  (∀ a : D.La, toUnit (Over.mk y) ≫ Xo.univ.etaA a = ex ((l.A : ℂ)⁻¹ • P (mk a))) ∧
  ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La),
    toUnit (Over.mk y) ≫ Xo.univ.eta a = ex ((l.M : ℂ)⁻¹ • P (mk a))
def IsExpDeriv (y : Sp ℂ ⟶ Xo.X) (ex : (Fin g → ℂ) → (Over.mk y ⟶ univG Xo)) : Prop :=
  ∃ d : (Fin g → ℂ) → (epsPt y ⟶ univG Xo),
    (∀ w, IsDerivAlong (X := (univG Xo).left) (fun z => (ex z).left) w (d w).left) ∧
    (∀ w w', d (w + w') = d w * d w') ∧
    (∀ (c : ℂ) w, (d (c • w)).left = spMap (epsScale c) ≫ (d w).left) ∧
    ∀ v : epsPt y ⟶ univG Xo,
      spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (1 : Over.mk y ⟶ univG Xo).left → ∃! w, d w = v
end Fibre
section Component
variable {D : Datum H} {l : Level H} (Xo : Moduli D l) (σ : KA l →+* ℂ) {g : ℕ} (ty : Fin g → (E →+* ℂ))
  (D' : Datum H) (u : (D'.La →+ (Fin g → ℂ)) → (Sp ℂ ⟶ Xo.X))
  (ex : ∀ P : D'.La →+ (Fin g → ℂ), (Fin g → ℂ) → (Over.mk (u P) ⟶ univG Xo))
def HolInFamilies : Prop :=
  ∀ (m : ℕ) (B : Set (Fin m → ℂ)) (Pf : (Fin m → ℂ) → (D'.La →+ (Fin g → ℂ))), IsOpen B →
    IsHolFamily D' ty B Pf →
      HolOn B (fun b => u (Pf b)) ∧
      HolOn (X := (univG Xo).left) (B ×ˢ (Set.univ : Set (Fin g → ℂ))) (fun p => (ex (Pf p.1) p.2).left)
def LiftsLocally : Prop :=
  ∀ (m : ℕ) (B : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ Xo.X)), IsOpen B → HolOnOver Xo.s σ B y →
    ∀ b₀ ∈ B, ∀ P₀ : D'.La →+ (Fin g → ℂ), IsPeriodMap D' ty P₀ → u P₀ = y b₀ →
      ∃ (B' : Set (Fin m → ℂ)) (Pf : (Fin m → ℂ) → (D'.La →+ (Fin g → ℂ))),
        IsOpen B' ∧ b₀ ∈ B' ∧ B' ⊆ B ∧ IsHolFamily D' ty B' Pf ∧ Pf b₀ = P₀ ∧ ∀ b ∈ B', u (Pf b) = y b
def ThetaInFamilies : Prop :=
  ∀ bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] D'.La, IsSympBasis D' bas →
    (∀ P, IsPeriodMap D' ty P →
      IsUnit (perF bas P).det ∧ (perTau bas P).IsSymm ∧ ((perTau bas P).map Complex.im).PosDef) ∧
    ∀ (m : ℕ) (B : Set (Fin m → ℂ)) (Pf : (Fin m → ℂ) → (D'.La →+ (Fin g → ℂ))), IsOpen B → IsPreconnected B →
      IsHolFamily D' ty B Pf →
        ∃ a c : Fin g → ℂ, IsHalf a ∧ IsHalf c ∧
          IsThetaFamily Xo.univ.t.PP B (fun b => u (Pf b)) (fun b => ex (Pf b))
            (fun b z => thetaChar (perTau bas (Pf b)) a c ((perF bas (Pf b))⁻¹ *ᵥ z))
def IsPiece (mk : D.La →ₗ[𝓞 E] D'.La) : Prop :=
  D'.p = D.p ∧ D'.q = D.q ∧
  IsMarking D D' l (σ (baseKA l).ζ) mk ∧
  (∀ P, IsPeriodMap D' ty P →
    u P ≫ Xo.s = spMap σ ∧ IsFibre Xo ty D' mk P (u P) (ex P) ∧ IsExpDeriv Xo (u P) (ex P)) ∧
  (∀ P P', IsPeriodMap D' ty P → IsPeriodMap D' ty P' → (u P = u P' ↔ SamePoint D' l P P')) ∧
  HolInFamilies Xo ty D' u ex ∧
  LiftsLocally Xo σ ty D' u ∧
  ThetaInFamilies Xo ty D' u ex
end Component
def UnifAt {D : Datum H} {l : Level H} (Xo : Moduli D l) (σ : KA l →+* ℂ) {g : ℕ} (ty : Fin g → (E →+* ℂ)) : Prop :=
  ∃ (n : ℕ) (Di : Fin n → Datum H) (mk : ∀ i, D.La →ₗ[𝓞 E] (Di i).La)
    (u : ∀ i, ((Di i).La →+ (Fin g → ℂ)) → (Sp ℂ ⟶ Xo.X))
    (ex : ∀ (i) (P : (Di i).La →+ (Fin g → ℂ)), (Fin g → ℂ) → (Over.mk (u i P) ⟶ univG Xo)),
    (∀ i, IsPiece Xo σ ty (Di i) (u i) (ex i) (mk i)) ∧
    (∀ i j P P', IsPeriodMap (Di i) ty P → IsPeriodMap (Di j) ty P' → u i P = u j P' → i = j) ∧
    ∀ y : Sp ℂ ⟶ Xo.X, y ≫ Xo.s = spMap σ → ∃ i P, IsPeriodMap (Di i) ty P ∧ u i P = y
def ComplexUnif {D : Datum H} {l : Level H} (Xo : Moduli D l) : Prop :=
  ∀ σ : KA l →+* ℂ, σ (baseKA l).ρ = H.rt0 →
    ∀ (g : ℕ) (ty : Fin g → (E →+* ℂ)), IsTypeFn D ty → UnifAt Xo σ ty
end GlobalTheory.IndefiniteRowSideFullHecke.SymplecticBasisLevel


