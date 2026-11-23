-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_IsFlatAnIffIsConstMul
-- name    : Development_AutomorphicSpectrum_Definitions_GlobalGeometry_IsFlatAnIffIsConstMul
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:58:12.83483+00:00
-- url     : https://prove2.me/theorems/9a396453-592f-4465-bad0-75f04baf6527
-- title:
--   Is Flat An Iff Is Const Mul
-- statement:
--   Definitions and structural lemmas for Is Flat An Iff Is Const Mul, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/GlobalGeometry/IsFlatAnIffIsConstMul.lean

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_IsConstMul
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_EigLat
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_IsLineGenOn
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Flat
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
abbrev CFn (Xo : Moduli D l) (c : Coeff l) : Type := ∀ y : Sp ℂ ⟶ Xo.XF c, Vecs y D.p → Vecs y D.q → ℂ
variable {Xo : Moduli D l} {c : Coeff l}
def IsFlatAn (U : Set (Xo.XF c)) (τ τ' : E →+* ℂ) (σ : c.F →+* ℂ) (Φ : CFn Xo c) {σK : KA l →+* ℂ} {g : ℕ}
    {ty : Fin g → (E →+* ℂ)} (FU : FamilyUnif Xo σK ty) (i : Fin FU.n)
    (e : Fin D.p ⊕ Fin D.q → (FU.Di i).La) (ρ : ℂ) : Prop :=
  ∀ (P : (FU.Di i).La →+ (Fin g → ℂ)) (y : Sp ℂ ⟶ Xo.XF c) (v : Vecs y D.p) (w : Vecs y D.q)
    (V : Fin D.p → Fin g → ℂ) (W : Fin D.q → Fin g → ℂ) (C : Matrix (Fin D.p) (Fin D.p ⊕ Fin D.q) ℂ)
    (Fm B : Matrix (Fin D.q) (Fin D.p ⊕ Fin D.q) ℂ),
    IsPeriod (FU.Di i) ty P → under y = FU.u i P → IsFramed U τ σ y v w →
    (∀ a, IsDerivAt0 (fun z => (FU.ex i P z).left) (V a) (v a).left) →
    (∀ j, IsDerivAt0 (fun z => (FU.ex i P z).left) (W j) (w j).left) →
    (∀ a, tyPart ty τ' (∑ m, C a m • P (e m)) = V a) →
    (∀ n, tyPart ty (ComplexEmbedding.conjugate τ') (P (e n)) = ∑ j, B j n • W j) →
    (∀ j n, ∑ m, Fm j m * τ' (sesq (FU.Di i) (e m) (e n)) = B j n) →
    Φ y v w * (Matrix.fromRows C Fm).det = ρ
structure IsUnitAn (τ : E →+* ℂ) (σ : c.F →+* ℂ) (Φ : CFn Xo c) : Prop where

  ne : ∀ y v w, IsFramed Set.univ τ σ y v w → Φ y v w ≠ 0

  chg : ∀ y v w v' w' (A : Matrix (Fin D.p) (Fin D.p) ℂ) (B : Matrix (Fin D.q) (Fin D.q) ℂ),
    IsFramed Set.univ τ σ y v w → IsFramed Set.univ τ σ y v' w' →
    (∀ i, IsComb (A i) v (v' i)) → (∀ j, IsComb (B j) w (w' j)) → Φ y v' w' * A.det = Φ y v w * B.det

  norm : ∀ y v w (Γ : Matrix (Fin D.p) (Fin D.p) ℂ) (Δ : Matrix (Fin D.q) (Fin D.q) ℂ),
    IsFramed Set.univ τ σ y v w → IsHodgeGram Xo.univ.t.G Xo.univ.t.PP.L (under y) v Γ →
    IsHodgeGram Xo.univ.t.G Xo.univ.t.PP.L (under y) w Δ → ‖Φ y v w‖ ^ 2 * ‖Γ.det‖ = ‖Δ.det‖

  hol : ∀ (R : Type) [CommRing R] (x : Sp R ⟶ Xo.XF c) (vR : Fin D.p → (epsAt (under x) ⟶ Xo.univ.t.G))
    (wR : Fin D.q → (epsAt (under x) ⟶ Xo.univ.t.G)) (m : ℕ) (B : Set (Fin m → ℂ)) (ψ : (Fin m → ℂ) → (R →+* ℂ))
    (v : ∀ b, Vecs (spMap (ψ b) ≫ x) D.p) (w : ∀ b, Vecs (spMap (ψ b) ≫ x) D.q), IsOpen B →
    (∀ r, DifferentiableOn ℂ (fun b => ψ b r) B) →
    (∀ b ∈ B, IsFramed Set.univ τ σ (spMap (ψ b) ≫ x) (v b) (w b) ∧
      (∀ a, (v b a).left = spMap (dualMap (ψ b)) ≫ (vR a).left) ∧
      ∀ j, (w b j).left = spMap (dualMap (ψ b)) ≫ (wR j).left) →
    DifferentiableOn ℂ (fun b => Φ (spMap (ψ b) ≫ x) (v b) (w b)) B
def ExtendsUnitAt {K Ω : Type} [Field K] [Field Ω] {X : Scheme.{0}} (s : X ⟶ Sp K) (σ : K →+* ℂ) (ξ : Sp Ω ⟶ X)
    (W : X.Opens) (F : (Sp ℂ ⟶ X) → ℂ) (t : Ω) (x : Sp ℂ ⟶ X) : Prop :=
  ∀ (m : ℕ) (B : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ X)), IsOpen B → IsHolTo B y →
    (∀ b ∈ B, y b ≫ s = spMap σ) → ∀ b₀ ∈ B, y b₀ = x →
    ∃ (ε : ℝ) (h : (Fin m → ℂ) → ℂ), 0 < ε ∧ DifferentiableOn ℂ h (Metric.ball b₀ ε) ∧ h b₀ ≠ 0 ∧
      ∀ b ∈ B ∩ Metric.ball b₀ ε, ⊤ ≤ y b ⁻¹ᵁ W → ∀ r : ℂ, ValAt ξ (y b) t r → F (y b) = h b * r
variable {O : Type} [CommRing O] {β : O →+* c.F}
def SameVec (Y : Model Xo c β) {F : Type} [Field F] (y : Sp F ⟶ Xo.XF c) (v : epsAt (under y) ⟶ Xo.univ.t.G)
    (v' : epsAt (y ≫ Y.j) ⟶ Y.t.G) : Prop :=
  ∃ u : Sp (DualNumber F) ⟶ Y.oF.t.G.left, u ≫ Y.oF.t.G.hom = spMap (algebraMap F (DualNumber F)) ≫ y ∧
    u ≫ Y.m0.toSABMap.φ = v.left ∧ u ≫ Y.m.φ = v'.left
def Represents (Y : Model Xo c β) (U : Set (Xo.XF c)) (τ : E →+* ℂ) {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ Y.X}
    {V : Type} [AddCommGroup V] [Module Ω V] (M : LieModel Y.t.G ξ V) (a : ⋀[Ω]^D.p V) (b : ⋀[Ω]^D.q V)
    (φ : FrameFn Xo c) : Prop :=
  ∀ (F : Type) [Field F] (βF : c.F →+* F) (y : Sp F ⟶ Xo.XF c) (v : Vecs y D.p) (w : Vecs y D.q)
    (b₁ : Fin D.p → V) (b₂ : Fin D.q → V) (α κ : Ω), IsFramed U τ βF y v w →
    a = α • exteriorPower.ιMulti Ω D.p b₁ → b = κ • exteriorPower.ιMulti Ω D.q b₂ →
    (∀ i, ∃ v', M.ValAt (y ≫ Y.j) (b₁ i) v' ∧ SameVec Y y (v i) v') →
    (∀ j, ∃ w', M.ValAt (y ≫ Y.j) (b₂ j) w' ∧ SameVec Y y (w j) w') →
    ValAt ξ (y ≫ Y.j) (α / κ) (φ F y v w)
structure CptOver (Y : Model Xo c β) (U : Set (Xo.XF c)) where

  Ω : Type
  [field : Field Ω]

  ξ₀ : Sp Ω ⟶ Xo.XF c

  inc : c.F →+* Ω

  over_inc : ξ₀ ≫ pullback.snd _ _ = spMap inc

  gen : IsCptGen (ξ₀ ≫ Y.j)

  closure : ∀ u : Xo.XF c, u ∈ U ↔ genPt ξ₀ ⤳ u

  V : Type
  [acg : AddCommGroup V]
  [mod : Module Ω V]

  M : LieModel Y.t.G (ξ₀ ≫ Y.j) V

  ρ : 𝓞 E →+* Module.End Ω V

  act : M.IsActOf Y.t.act.act ρ
attribute [instance] CptOver.field CptOver.acg CptOver.mod
def CptOver.eig {Y : Model Xo c β} {U : Set (Xo.XF c)} (Z : CptOver Y U) (τ : E →+* ℂ) : Lat (Z.ξ₀ ≫ Y.j) Z.V :=
  Z.M.eigLat Z.ρ (Z.inc.comp (tauIn c τ))
def CptOver.genFib {Y : Model Xo c β} {U : Set (Xo.XF c)} (Z : CptOver Y U) : Set (Cpt (Z.ξ₀ ≫ Y.j)) :=
  {x | x.1 ∈ Set.range (pullback.fst Y.s (spMap β))}
def FlatOnModel {Y : Model Xo c β} {U : Set (Xo.XF c)} (Z : CptOver Y U) (τ : E →+* ℂ) (φ : FrameFn Xo c) : Prop :=
  IsLineFn U τ φ ∧ ∃ (a : ⋀[Z.Ω]^D.p Z.V) (b : ⋀[Z.Ω]^D.q Z.V),
    IsLineGenOn (Z.eig τ) (Z.eig (ComplexEmbedding.conjugate τ)) D.p D.q a b Z.genFib ∧ Represents Y U τ Z.M a b φ
theorem FlatOnModel.isLineFn {Y : Model Xo c β} {U : Set (Xo.XF c)} {Z : CptOver Y U} {τ : E →+* ℂ}
    {φ : FrameFn Xo c} (h : FlatOnModel Z τ φ) : IsLineFn U τ φ := h.1
def CptOver.IsGeom {Y : Model Xo c β} {U : Set (Xo.XF c)} (Z : CptOver Y U) : Prop :=
  ∀ x : Z.Ω, (∃ f : Polynomial c.F, f ≠ 0 ∧ f.eval₂ Z.inc x = 0) → x ∈ Set.range Z.inc
example {Y : Model Xo c β} {U : Set (Xo.XF c)} (Z : CptOver Y U) (τ : E →+* ℂ) {F : Type} [Field F]
    (βF : c.F →+* F) (y : Sp F ⟶ Xo.XF c) (v : Vecs y D.p) (w : Vecs y D.q) (hf : IsFramed U τ βF y v w) :
    ¬ FlatOnModel Z τ (fun _ _ _ _ _ => 0) := fun h => h.isLineFn.ne F βF y v w hf rfl
end GlobalTheory.CompanionTheory.Ar.Flat


