-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_GermEvalOneStandardPointSelf
-- name    : Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_GermEvalOneStandardPointSelf
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:49:41.403753+00:00
-- url     : https://prove2.me/theorems/6e639706-f812-44bb-9617-4835cbc3eab1
-- title:
--   Germ Eval One Standard Point Self
-- statement:
--   Definitions and structural lemmas for Germ Eval One Standard Point Self, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/GermEvalOneStandardPointSelf.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_ker_jetAug_pow
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_zR_mem_ker
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_Tri_prod

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj MvPowerSeries
open ReciprocityTheory.ChartRestriction.G.Chart ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (IsGrpPullback pushHom)
open GlobalTheory.JetSer ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.ChartBaseChange
section Values
variable {A B : Type} [CommRing A] [CommRing B] {X Y : Scheme.{0}}
end Values
variable {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R']
section Push
variable {G : Over (Spec (CommRingCat.of R))} [GrpObj G] {G' : Over (Spec (CommRingCat.of R'))} [GrpObj G']
  {π : G'.left ⟶ G.left} (hπ : IsGrpPullback G' G (Spec.map (CommRingCat.ofHom (algebraMap R R'))) π)
  {A : Type} [CommRing A] [Algebra R A] [Algebra R' A] [IsScalarTower R R' A]
theorem sp_tower : (sp (R₀ := R') A).hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')) = (sp (R₀ := R) A).hom := by
  simp only [sp, Over.mk_hom]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
def push (y : sp (R₀ := R') A ⟶ G') : sp (R₀ := R) A ⟶ G :=
  Over.homMk (y.left ≫ π) (by
    rw [Category.assoc, hπ.1.w, ← Category.assoc, Over.w y]
    exact sp_tower)
end Push
section Coeff
variable (R R') in

def jetCoeff (κ : Type) (m : ℕ) : JetR R κ m →ₐ[R] JetR R' κ m :=
  jetLift R (RingHom.ker (jetAug R' κ m)) (ker_jetAug_pow κ m) (zR m) (zR_mem_ker m)
end Coeff
section Univ
variable {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
def fib {A : Type} [CommRing A] [Algebra R A] (q : A →ₐ[R] R') : Subalgebra R (R × A) :=
  AlgHom.equalizer ((Algebra.ofId R R').comp (AlgHom.fst R R A)) (q.comp (AlgHom.snd R R A))
def fibLift {A B : Type} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B] (q : A →ₐ[R] R')
    (u : B →ₐ[R] R) (v : B →ₐ[R] A) (h : q.comp v = (Algebra.ofId R R').comp u) : B →ₐ[R] fib q :=
  (u.prod v).codRestrict _ fun b => (AlgHom.congr_fun h b).symm
def fibFst {A : Type} [CommRing A] [Algebra R A] (q : A →ₐ[R] R') : fib q →ₐ[R] R :=
  (AlgHom.fst R R A).comp (fib q).val
def fibSnd {A : Type} [CommRing A] [Algebra R A] (q : A →ₐ[R] R') : fib q →ₐ[R] A :=
  (AlgHom.snd R R A).comp (fib q).val
variable {G' : Over (Spec (CommRingCat.of R'))} [GrpObj G']
  {π : G'.left ⟶ G.left} (hπ : IsGrpPullback G' G (Spec.map (CommRingCat.ofHom (algebraMap R R'))) π)
end Univ
section Test
variable {d n N : ℕ}
def IsMove (a : Fin N → Pt R' n d)
    (Θ : ∀ m, JetR R (Fin N × Fin d) m →ₐ[R] JetR R' (Fin n × Fin d) m) : Prop :=
  ∀ m g, Θ m (toJet m g) = toJet m (ev a (MvPowerSeries.map (algebraMap R R') g))
variable {G : Over (Spec (CommRingCat.of R))} [GrpObj G] {G' : Over (Spec (CommRingCat.of R'))} [GrpObj G']
  {π : G'.left ⟶ G.left} (hπ : IsGrpPullback G' G (Spec.map (CommRingCat.ofHom (algebraMap R R'))) π)
end Test
end GlobalTheory.ChartBaseChange


