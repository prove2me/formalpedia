-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsUnivRingBc
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsUnivRingBc
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T13:32:43.519806+00:00
-- url     : https://prove2.me/theorems/151638b3-ad37-5478-a78c-0bea999176d7
-- title:
--   Is Univ Ring Bc
-- statement:
--   Definitions and structural lemmas for Is Univ Ring Bc, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/IsUnivRingBc.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_EigLatBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_AlgChart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_ker_jetAug_pow
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_zR_mem_ker
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isGrpPullback_pullback

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
open scoped CategoryTheory.Obj
namespace ReciprocityTheory.ChartRestriction.G.Chart
attribute [local instance] Over.cartesianMonoidalCategory
section Ring
variable {R : Type} [CommRing R] {B : Type} [CommRing B] [Algebra R B] (eps : B →ₐ[R] R) {n : ℕ}
def IsUnivRing (m : ℕ) (π : B →ₐ[R] JetR R (Fin n) m) : Prop :=
  ∀ (A : Type) [CommRing A] [Algebra R A] (aug : A →ₐ[R] R), (RingHom.ker aug) ^ (m + 1) = ⊥ →
    ∀ h : B →ₐ[R] A, aug.comp h = eps → ∃! ψ : JetR R (Fin n) m →ₐ[R] A, aug.comp ψ = jetAug R (Fin n) m ∧ h = ψ.comp π
variable {R' : Type} [CommRing R'] [Algebra R R']
def jetMapA (n m : ℕ) : JetR R (Fin n) m →ₐ[R] JetR R' (Fin n) m :=
  jetLift R (RingHom.ker (jetAug R' (Fin n) m)) (ker_jetAug_pow (Fin n) m) (fun j => zR m j) (fun j => zR_mem_ker m j)
end Ring
section Geo
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] (G : Over (Spec (CommRingCat.of R))) [GrpObj G]
abbrev fB (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] :
    Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R R'))
variable {P : Type} [CommRing P] [Algebra R' P] [Algebra R P] [IsScalarTower R R' P]
theorem sp_hom_fB : (sp (R₀ := R') P).hom ≫ fB R R' = (sp (R₀ := R) P).hom := by
  simp only [sp, Over.mk_hom, fB]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
def iotaB : sp (R₀ := R) P ⟶ Over.mk ((sp (R₀ := R') P).hom ≫ fB R R') :=
  Over.homMk (𝟙 _) (by rw [Category.id_comp]; exact sp_hom_fB (R := R) (R' := R') (P := P))
def pushR (y : sp (R₀ := R') P ⟶ (Over.pullback (fB R R')).obj G) : sp (R₀ := R) P ⟶ G :=
  iotaB ≫ pushPt (isGrpPullback_pullback G (fB R R')).1.w y
def pullR (q : sp (R₀ := R) P ⟶ G) : sp (R₀ := R') P ⟶ (Over.pullback (fB R R')).obj G :=
  Over.homMk ((isGrpPullback_pullback G (fB R R')).1.lift q.left (sp (R₀ := R') P).hom
    ((Over.w q).trans (sp_hom_fB (R := R) (R' := R') (P := P)).symm)) ((isGrpPullback_pullback G (fB R R')).1.lift_snd _ _ _)
variable (R R') in

def dualMapA : DualNumber R →ₐ[R] DualNumber R' :=
  { dualMapR (algebraMap R R') with
    commutes' := fun r => by ext <;> simp [dualMapR, TrivSqZeroExt.algebraMap_eq_inl'] }
end Geo
end ReciprocityTheory.ChartRestriction.G.Chart


