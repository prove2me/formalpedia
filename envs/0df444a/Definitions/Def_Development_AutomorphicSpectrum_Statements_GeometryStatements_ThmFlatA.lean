-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Statements_GeometryStatements_ThmFlatA
-- name    : Development_AutomorphicSpectrum_Statements_GeometryStatements_ThmFlatA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:04:05.705485+00:00
-- url     : https://prove2.me/theorems/a6f890de-af25-4285-84ec-ba3706ef0757
-- title:
--   Thm Flat A
-- statement:
--   Definitions and structural lemmas for Thm Flat A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Statements/GeometryStatements/ThmFlatA.lean

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_IsFlatAnIffIsConstMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
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
def ThmFlatA : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l)
    (l : Level H) (c : Coeff l) [NumberField c.F] (U : Set ((Xo l).XF c)) (τ : E →+* ℂ) (g : ℕ)
    (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif (Xo l) (algebraMap (KA l) ℂ) ty) (i : Fin FU.n),
    1 ≤ D.p + D.q → τ (H.rt : E) = H.rt0 → (∀ p : ℕ, p.Prime → l.GoodAt p) → IsTypeFn H D.p D.q ty →
    IsClopen U → IsIrreducible U →
    (∀ y : Sp ℂ ⟶ (Xo l).XF c, y ≫ pullback.snd _ _ = spMap (algebraMap c.F ℂ) →
      (Set.range y ⊆ U ↔ ∃ P, IsPeriod (FU.Di i) ty P ∧ under y = FU.u i P)) →
    ∃ (φ : FrameFn (Xo l) c) (N : LogNorms c.F), IsFlatGen U τ φ FU i ∧ HasNorms U τ φ N ∧ N.IsAdelic
end GlobalTheory.CompanionTheory.Ar.Flat


