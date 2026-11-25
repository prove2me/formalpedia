-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_FormalGroupLawJacobianExtensionChangeCoeff
-- name    : Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_FormalGroupLawJacobianExtensionChangeCoeff
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T17:37:38.759506+00:00
-- url     : https://prove2.me/theorems/968b98ac-caf0-5894-8273-fc79013e73b6
-- title:
--   Formal Group Law Jacobian Extension Change Coeff
-- statement:
--   Definitions and structural lemmas for Formal Group Law Jacobian Extension Change Coeff, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/FormalGroupLawJacobianExtensionChangeCoeff.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartFH
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_LengthDegreeAbelianVariety
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_IsEigBasisIff
import Theorems.Thm_ReciprocityTheory_PGsh_Up_MulStable_const
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_succ_succ_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_succ_zero_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_zero_succ_alt
import Theorems.Thm_ReciprocityTheory_PGsh_Up_Smith_blockOne_zero_zero_alt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_succ_succ_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_succ_zero_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_zero_succ_alt
attribute [local simp] ReciprocityTheory.PGsh.Up.Smith.blockOne_zero_zero_alt


set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.ChF
lemma map_sub' {R S : Type} [CommRing R] [CommRing S] (β : R →+* S) {m n d e : ℕ}
    (a : Fin m → Fin d → PS R n e) (ha : ∀ i j, MvPowerSeries.constantCoeff (a i j) = 0) (f : PS R m d)
    (a' : Fin m → Fin d → PS S n e) (h : ∀ i j, MvPowerSeries.map β (a i j) = a' i j) :
    MvPowerSeries.map β (sub a f) = sub a' (MvPowerSeries.map β f) := by
  unfold sub
  rw [MvPowerSeries.map_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero (a := fun q : Fin m × Fin d => a q.1 q.2) (fun q => ha q.1 q.2))]
  simp only [h]
lemma cc_sub {R : Type} [CommRing R] {m n d e : ℕ}
    (a : Fin m → Fin d → PS R n e) (ha : ∀ i j, MvPowerSeries.constantCoeff (a i j) = 0) (f : PS R m d)
    (hf : MvPowerSeries.constantCoeff f = 0) : MvPowerSeries.constantCoeff (sub a f) = 0 := by
  unfold sub
  exact MvPowerSeries.constantCoeff_subst_eq_zero
    (MvPowerSeries.hasSubst_of_constantCoeff_zero (a := fun q : Fin m × Fin d => a q.1 q.2)
      (fun q => ha q.1 q.2)) (fun q => ha q.1 q.2) hf
lemma ev_eq {R : Type} [CommRing R] {m n d : ℕ} (a : Fin m → Fin d → PS R n d) (f : PS R m d) :
    ev a f = sub a f := rfl
lemma map_pt {R S : Type} [CommRing R] [CommRing S] (β : R →+* S) {n d : ℕ} (j : Fin n) (i : Fin d) :
    MvPowerSeries.map β (pt R d j i) = pt S d j i := by simp [pt]
lemma cc_pt {R : Type} [CommRing R] {n d : ℕ} (j : Fin n) (i : Fin d) :
    MvPowerSeries.constantCoeff (pt R d j i) = 0 := by simp [pt]
lemma map_sub_pair_eq_sub_map_of_constantCoeff_eq_zero {R S : Type} [CommRing R] [CommRing S] (β : R →+* S) {n d e : ℕ}
    (x y : Fin d → PS R n e) (hx : ∀ j, MvPowerSeries.constantCoeff (x j) = 0)
    (hy : ∀ j, MvPowerSeries.constantCoeff (y j) = 0) (f : PS R 2 d) :
    MvPowerSeries.map β (sub ![x, y] f) =
      sub ![fun j => MvPowerSeries.map β (x j), fun j => MvPowerSeries.map β (y j)] (MvPowerSeries.map β f) :=
  map_sub' β _ (fun i j => by
    fin_cases i
    · exact hx j
    · exact hy j) f _ (fun i j => by fin_cases i <;> rfl)
lemma constantCoeff_sub2_eq_zero {R : Type} [CommRing R] {n d e : ℕ}
    (x y : Fin d → PS R n e) (hx : ∀ j, MvPowerSeries.constantCoeff (x j) = 0)
    (hy : ∀ j, MvPowerSeries.constantCoeff (y j) = 0) (f : PS R 2 d)
    (hf : MvPowerSeries.constantCoeff f = 0) : MvPowerSeries.constantCoeff (sub ![x, y] f) = 0 :=
  cc_sub _ (fun i j => by
    fin_cases i
    · exact hx j
    · exact hy j) f hf
noncomputable def mapLaw {R S : Type} [CommRing R] [CommRing S] (β : R →+* S) {d : ℕ} (F : FGLaw R d) :
    FGLaw S d where
  F := F.mapF β
  const i := by simp [FGLaw.mapF, MvPowerSeries.constantCoeff_map, F.const]
  unit i := by
    have := congrArg (MvPowerSeries.map β) (F.unit i)
    simp only [ev_eq] at this ⊢
    rw [map_sub_pair_eq_sub_map_of_constantCoeff_eq_zero β _ _ (fun _ => by simp) (cc_pt _)] at this
    simp only [map_pt, Pi.zero_apply, map_zero, MvPowerSeries.map_X] at this
    exact this
  comm i := by
    have := congrArg (MvPowerSeries.map β) (F.comm i)
    simp only [ev_eq] at this ⊢
    rw [map_sub_pair_eq_sub_map_of_constantCoeff_eq_zero β _ _ (cc_pt _) (cc_pt _)] at this
    simp only [map_pt] at this
    exact this
  assoc i := by
    have := congrArg (MvPowerSeries.map β) (F.assoc i)
    simp only [ev_eq] at this ⊢
    rw [map_sub_pair_eq_sub_map_of_constantCoeff_eq_zero β _ _ (fun l => constantCoeff_sub2_eq_zero _ _ (cc_pt _) (cc_pt _) _ (F.const l)) (cc_pt _),
      map_sub_pair_eq_sub_map_of_constantCoeff_eq_zero β _ _ (cc_pt _) (fun l => constantCoeff_sub2_eq_zero _ _ (cc_pt _) (cc_pt _) _ (F.const l))] at this
    simp only [map_sub_pair_eq_sub_map_of_constantCoeff_eq_zero β _ _ (cc_pt _) (cc_pt _), map_pt] at this
    exact this
end GlobalTheory.ChF


