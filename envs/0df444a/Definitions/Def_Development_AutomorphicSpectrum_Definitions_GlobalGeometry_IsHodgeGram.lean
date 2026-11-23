-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_IsHodgeGram
-- name    : Development_AutomorphicSpectrum_Definitions_GlobalGeometry_IsHodgeGram
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:53:59.216964+00:00
-- url     : https://prove2.me/theorems/20722a35-9c9a-4d00-8da4-e24bfc83b2ec
-- title:
--   Is Hodge Gram
-- statement:
--   Definitions and structural lemmas for Is Hodge Gram, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/GlobalGeometry/IsHodgeGram.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_LieModel
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_CommutativeAlgebra_LatNormGrLatNeZeroOfSpan
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Fl
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
section Frames
variable {S : Scheme.{0}} {R : Type} [CommRing R]
def IsComb {G : Over S} [GrpObj G] {x : Sp R ⟶ S} {n : ℕ} (c : Fin n → R) (v : Fin n → (epsAt x ⟶ G))
    (w : epsAt x ⟶ G) : Prop :=
  ∃ u : Fin n → (epsAt x ⟶ G), (∀ i, (u i).left = spMap (epsMul (c i)) ≫ (v i).left) ∧ w = (List.ofFn u).prod
def IsEigVec {O : Type} [CommRing O] {G : Over S} [GrpObj G] (act : OAct O G) (x : Sp R ⟶ S) (τ : O →+* R)
    (v : epsAt x ⟶ G) : Prop :=
  IsTanAt G x v ∧ ∀ a, (v ≫ act.act a).left = spMap (epsMul (τ a)) ≫ v.left
def IsEigFrame {O : Type} [CommRing O] {G : Over S} [GrpObj G] (act : OAct O G) (x : Sp R ⟶ S) (τ : O →+* R)
    {n : ℕ} (v : Fin n → (epsAt x ⟶ G)) : Prop :=
  (∀ i, IsEigVec act x τ (v i)) ∧ ∀ w, IsEigVec act x τ w → ∃! c : Fin n → R, IsComb c v w
def IsHodgeGram (G : Over S) [GrpObj G] (L : LB G.left) (x : Sp ℂ ⟶ S) {n : ℕ} (v : Fin n → (epsAt x ⟶ G))
    (Γ : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∃ (Q : Out.PolAV (Sp ℂ)) (ψ : Q.A.left ⟶ G.left) (v' : Fin n → (epsR ℂ ⟶ Q.A)) (u : HolUnif Q.A Q.L Q.g)
    (Hm : Matrix (Fin Q.g) (Fin Q.g) ℂ) (χ : u.Λ → ℂ) (W : Fin n → Fin Q.g → ℂ),
    IsGrpPullback Q.A G x ψ ∧ LBIso (L.pull ψ) Q.L ∧ u.IsAH Hm χ ∧
      (∀ i, (v' i).left ≫ ψ = (v i).left ∧ u.IsDiff (W i) (v' i)) ∧ ∀ i j, Γ i j = Real.pi * hermForm Hm (W i) (W j)
end Frames
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
def tauIn {l : Level H} (c : Coeff l) (τ : E →+* ℂ) : 𝓞 E →+* c.F :=
  ((τ.codRestrict c.F.toSubfield (c.conj τ)).comp (algebraMap (𝓞 E) E) :)
def sesq (D : Datum H) (x y : D.La) : E :=
  ∑ k, (D.EF (RingOfIntegers.basis E k • x) y : E) * HT.dualInt E k
def tyPart {g : ℕ} (ty : Fin g → (E →+* ℂ)) (τ : E →+* ℂ) (z : Fin g → ℂ) : Fin g → ℂ :=
  open Classical in fun k => if ty k = τ then z k else 0
end GlobalTheory.CompanionTheory.Ar.Fl


