-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_ArcDictExpZeroSection
-- name    : Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_ArcDictExpZeroSection
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T13:21:31.090008+00:00
-- url     : https://prove2.me/theorems/97ec5a8c-ed6c-4ee6-8ff8-50e33e61ed10
-- title:
--   Arc Dict Exp Zero Section
-- statement:
--   Definitions and structural lemmas for Arc Dict Exp Zero Section, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ArchimedeanThetaValues/ArcDictExpZeroSection.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HasArcDataIff
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_DegeneratingToriPeriodMapEqBaseOfYEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ConstOfNormPeriodic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.ArcPts
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj LaurentSeries PowerSeries
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} [StarRing (𝓞 E)]
variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
structure GtAn [Algebra (FractionRing ℂ) ℂ] {b : O →+* ℂ} (a : ArcIn D l β ℂ b) where
  star_eq : (inferInstance : StarRing (𝓞 E)) = H.starRing
  A : AnArc (𝓞 E)
  ε : A.X ≃ₗ[𝓞 E] a.D₀.X
  be_eq : ∀ x y, A.be x y = a.be (ε x) (ε y)
  gB_eq : A.gB = a.D₀.P.g
  u : HolUnif a.D₀.P.A a.D₀.P.L A.gB
  lam : u.Λ = A.abelian₂
  ah : u.IsAH A.Hm (fun m => A.chi ⟨m.1, lam ▸ m.2⟩)
  rig : u.IsRig a.D₀.rig
  tan : (∀ v, IsTangent v → ∃! w, u.IsDiff w v) ∧ ∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v
  pow : ∀ n : ℕ, (∀ s, ∃! θ, u.IsThetaFn A.Hm (fun m => A.chi ⟨m.1, lam ▸ m.2⟩) n θ ∧ u.IsFnPow n s θ) ∧
    ∀ θ, u.IsThetaFn A.Hm (fun m => A.chi ⟨m.1, lam ▸ m.2⟩) n θ → ∃! s, u.IsFnPow n s θ
  act : ∀ x z, u.ex (A.F x z) = u.ex z ≫ (letI := H.starRing; a.oa.onB.act x)
  ct : ∀ x, u.ex (A.ct x) = a.D₀.c (ε x)
  psi : ∀ x, FrameValue.genVal u a.D₀.P.isLB (a.D₀.psi (ε x)) (Out.jFK (R := ℂ) ℂ) (fun _ => A.ct x) = A.psi x
  ex0 : A.V → Out.GtPtF a.D₀ ℂ
  ex0_b : ∀ v, (show Sp ℂ ⟶ _ from (ex0 v).b.left) = (u.ex v.2).left
  arcDict_expZero_section : ∀ v x, FrameValue.genVal u a.D₀.P.isLB ((ex0 v).s (ε x)) (show Sp ℂ ⟶ _ from 𝟙 (Sp ℂ))
    ![A.ct x + v.2, A.ct x, v.2, 0] = eTwoPi (v.1 x)
def GtAn.fn [Algebra (FractionRing ℂ) ℂ] {b : O →+* ℂ} {a : ArcIn D l β ℂ b} (Λ : GtAn a) (j : ℕ) (α : Λ.A.X)
    (s : a.D₀.SecB j (Λ.ε α)) (z : Fin Λ.A.gB → ℂ) : ℂ :=
  FrameValue.secVal Λ.u a.D₀.P.isLB s (Λ.u.ex z).left ![z, z + Λ.A.ct α, Λ.A.ct α, 0]
def GtAn.Rep [Algebra (FractionRing ℂ) ℂ] {b : O →+* ℂ} {a : ArcIn D l β ℂ b} (Λ : GtAn a) (k : ℕ)
    (p : Out.QkPt a.D₀ (FractionRing ℂ) k) (la : Λ.A.La) : Prop :=
  ∀ q : Out.QkPt a.D₀ ℂ k, QkExt (algebraMap _ ℂ) p q → q.y = Λ.ε la.y ∧ q.g = Λ.ex0 ((k : ℂ)⁻¹ • Λ.A.P0 la)
end GlobalTheory.ArcPts


