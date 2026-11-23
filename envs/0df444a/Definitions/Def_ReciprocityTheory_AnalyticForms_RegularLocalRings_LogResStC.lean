-- Prove2me | Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_LogResStC
-- name    : ReciprocityTheory_AnalyticForms_RegularLocalRings_LogResStC
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T03:47:06.417491+00:00
-- url     : https://prove2.me/theorems/730ec8ea-1343-461b-b7dd-d84fc081ce3c
-- title:
--   Log Res St C
-- statement:
--   Definitions and structural lemmas for Log Res St C, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/LogResStC.lean

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_FinalTheorems
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory
universe u
namespace ReciprocityTheory.AnForm.R.FinalTheorems
noncomputable abbrev reesChart {R : Type u} [CommRing R] {m : ℕ} (g : Fin m → R) (i : Fin m) :
    Subalgebra R (Localization.Away (g i)) :=
  Algebra.adjoin R (Set.range fun k => IsLocalization.mk' (Localization.Away (g i)) (g k)
    (⟨g i, Submonoid.mem_powers _⟩ : Submonoid.powers (g i)))
def ReesCharts {X W : Scheme.{u}} (π : W ⟶ X) (J : X.IdealSheafData) : Prop :=
  ∀ U : X.affineOpens, ∃ (m : ℕ) (g : Fin m → Γ(X, U.1)),
    Ideal.span (Set.range g) = J.ideal U ∧
    ∃ V : Fin m → W.Opens, (⨆ i, V i) = π ⁻¹ᵁ U.1 ∧
      ∀ i, ∃ e : (V i).toScheme ≅ Spec (CommRingCat.of (reesChart g i)),
        e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U.1) (reesChart g i))) ≫ U.2.fromSpec =
          (V i).ι ≫ π
def LogResStC (X : Scheme.{u}) (B : TopologicalSpace.Closeds X) : Prop :=
  ∃ (J : X.IdealSheafData) (W : Scheme.{u}) (π : W ⟶ X), (J.support : Set X) ⊆ B ∧ Blowup π J ∧
    (∀ w : W, IsRegularLocalRing (W.presheaf.stalk w)) ∧
    Snc (Scheme.IdealSheafData.vanishingIdeal
      ⟨π.base ⁻¹' (B : Set X), IsClosed.preimage π.base.hom.continuous B.2⟩) ∧
    (∀ x : X, SncAt (Scheme.IdealSheafData.vanishingIdeal B) x →
      ∃ f ∈ nonZeroDivisors (X.presheaf.stalk x), stalkId J x = Ideal.span {f}) ∧
    (∃ U : X.Opens, (U : Set X) = {x : X | SncAt (Scheme.IdealSheafData.vanishingIdeal B) x} ∧
      IsIso (π ∣_ U)) ∧
    IsSeparated π ∧ LocallyOfFiniteType π ∧ ReesCharts π J
def GFLogStCR : Prop :=
  ∀ (X : Scheme.{u}) [IsNoetherian X], QE X → IsReduced X → FFinRes X →
    ∀ B : TopologicalSpace.Closeds X, Sing X ⊆ B → interior (B : Set X) = ∅ → LogResStC X B
end ReciprocityTheory.AnForm.R.FinalTheorems


