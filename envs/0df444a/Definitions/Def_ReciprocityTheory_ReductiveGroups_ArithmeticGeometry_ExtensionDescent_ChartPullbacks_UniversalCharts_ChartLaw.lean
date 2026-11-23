-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_ChartLaw
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_ChartLaw
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:40:41.691832+00:00
-- url     : https://prove2.me/theorems/5c4cd0bd-25f7-4bd4-83bd-0abb0410a0d2
-- title:
--   Chart Law
-- statement:
--   Definitions and structural lemmas for Chart Law, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/UniversalCharts/ChartLaw.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_DualLiftCompJetSub
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_UnivChartLoc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp epsR epsScaleR IsTangent IsLieComb IsLieBasis)
namespace ReciprocityTheory.ChartRestriction.G.Chart
attribute [local instance] Over.cartesianMonoidalCategory
abbrev algOver (R : Type) [CommRing R] (A : Type) [CommRing A] [Algebra R A] : Over (Sp R) :=
  Over.mk (ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap R A))
def algOverHom {R : Type} [CommRing R] {A B : Type} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]
    (ψ : A →ₐ[R] B) : algOver R B ⟶ algOver R A :=
  Over.homMk (ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (ψ : A →+* B)) (by
    dsimp
    simp only [ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact ψ.comp_algebraMap)
def ChartLawLocSt : Prop :=
  ∀ (R : Type) [CommRing R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], Smooth G.hom →
    ∀ (d : ℕ) (v : Fin d → (epsR R ⟶ G)), IsLieBasis v →
    ∃ x : ∀ m : ℕ, algOver R (JetR R (Fin d) m) ⟶ G,
      (∀ m, algOverHom (jetTruncR R (Fin d) m) ≫ x (m + 1) = x m) ∧
      (∀ m, algOverHom (jetZeroR R (Fin d) m) ≫ x m = toUnit _ ≫ η[G]) ∧
      (∀ j : Fin d, ∃ ψ : JetR R (Fin d) 1 →ₐ[R] DualNumber R,
        ψ (zR 1 j) = TrivSqZeroExt.inr 1 ∧ (∀ i, i ≠ j → ψ (zR 1 i) = 0) ∧ algOverHom ψ ≫ x 1 = v j) ∧
      ∀ (κ : Type) (m : ℕ) (y : algOver R (JetR R κ m) ⟶ G),
        algOverHom (jetZeroR R κ m) ≫ y = toUnit _ ≫ η[G] →
        ∃! ψ : JetR R (Fin d) m →ₐ[R] JetR R κ m,
          (∀ j, jetZeroR R κ m (ψ (zR m j)) = 0) ∧ y = algOverHom ψ ≫ x m
variable {R : Type} [CommRing R]
variable {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
def prodPts {d : ℕ} (c : Fin d → R) (v : Fin d → (sp (R₀ := R) (DualNumber R) ⟶ G)) :
    sp (R₀ := R) (DualNumber R) ⟶ G :=
  (List.ofFn fun i => spMap (scaleD (c i)) ≫ v i).prod
variable {n : ℕ} {x : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin n) m) ⟶ G} (hx : IsUnivChart G n x)
end ReciprocityTheory.ChartRestriction.G.Chart


