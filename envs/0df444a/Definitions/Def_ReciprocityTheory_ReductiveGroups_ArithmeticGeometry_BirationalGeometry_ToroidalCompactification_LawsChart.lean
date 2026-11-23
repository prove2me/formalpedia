-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_LawsChart
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_LawsChart
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:42:13.721431+00:00
-- url     : https://prove2.me/theorems/b2b7e164-604e-4bcf-8cdb-d5e8bc72ab48
-- title:
--   Laws Chart
-- statement:
--   Definitions and structural lemmas for Laws Chart, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/LawsChart.lean

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
namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
abbrev JetR (R : Type) [CommRing R] (κ : Type) (m : ℕ) : Type :=
  MvPolynomial κ R ⧸ (Ideal.span (Set.range (MvPolynomial.X : κ → MvPolynomial κ R))) ^ (m + 1)
abbrev algOver (R : Type) [CommRing R] (A : Type) [CommRing A] [Algebra R A] : Over (Sp R) :=
  Over.mk (spMap (algebraMap R A))
def algOverHom {R : Type} [CommRing R] {A B : Type} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]
    (ψ : A →ₐ[R] B) : algOver R B ⟶ algOver R A :=
  Over.homMk (spMap (ψ : A →+* B)) (by
    dsimp
    simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact ψ.comp_algebraMap)
def jetTruncR (R : Type) [CommRing R] (κ : Type) (m : ℕ) : JetR R κ (m + 1) →ₐ[R] JetR R κ m :=
  Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right (by omega))
def jetZeroR (R : Type) [CommRing R] (κ : Type) (m : ℕ) : JetR R κ m →ₐ[R] JetR R κ 0 :=
  Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right (by omega))
abbrev zR {R : Type} [CommRing R] {κ : Type} (m : ℕ) (j : κ) : JetR R κ m := Ideal.Quotient.mk _ (MvPolynomial.X j)
def ChartLawSt : Prop :=
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
end ReciprocityTheory.ChartRestriction.G.Geo.Tor


