-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_GmLawCharsMul
-- name    : Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_GmLawCharsMul
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T17:37:52.45242+00:00
-- url     : https://prove2.me/theorems/8251d8e8-d8ef-4894-99f8-7bfccc9647a8
-- title:
--   Gm Law Chars Mul
-- statement:
--   Definitions and structural lemmas for Gm Law Chars Mul, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/GmLawCharsMul.lean

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
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.ChF
open MvPowerSeries
lemma gm_hs {R : Type} [CommRing R] {m n d : ℕ} (a : Fin m → Pt R n d)
    (h : ∀ j i, constantCoeff (a j i) = 0) :
    HasSubst (fun p : Fin m × Fin d => a p.1 p.2) :=
  hasSubst_of_constantCoeff_zero (fun p => h p.1 p.2)
lemma ev_gm {R : Type} [CommRing R] {n r : ℕ} (a b : Pt R n r)
    (ha : ∀ i, constantCoeff (a i) = 0) (hb : ∀ i, constantCoeff (b i) = 0) (i : Fin r) :
    ev ![a, b] (gmF R r i) = a i + b i + a i * b i := by
  have h := gm_hs (m := 2) ![a, b] (by
    intro j i
    fin_cases j
    · exact ha i
    · exact hb i)
  unfold ev gmF
  rw [subst_add h, subst_add h, subst_mul h, subst_X h, subst_X h]
  rfl
lemma gm_const {R : Type} [CommRing R] {r : ℕ} (i : Fin r) :
    constantCoeff (gmF R r i) = 0 := by
  simp [gmF]
lemma pt_const {R : Type} [CommRing R] {n r : ℕ} (j : Fin n) (i : Fin r) :
    constantCoeff (pt R r j i) = 0 := by
  simp [pt]
def gmLaw (R : Type) [CommRing R] (r : ℕ) : FGLaw R r where
  F := gmF R r
  const := gm_const
  unit i := by
    rw [ev_gm _ _ (by simp) (pt_const _)]
    simp [pt]
  comm i := by
    rw [ev_gm _ _ (pt_const _) (pt_const _)]
    simp only [pt, gmF]
    ring
  assoc i := by
    have h : ∀ (j k : Fin 3) (l : Fin r), constantCoeff (ev (n := 3) ![pt R r j, pt R r k] (gmF R r l)) = 0 := by
      intro j k l
      rw [ev_gm _ _ (pt_const _) (pt_const _)]
      simp [pt]
    rw [ev_gm _ _ (h _ _) (pt_const _), ev_gm _ _ (pt_const _) (h _ _),
      ev_gm _ _ (pt_const _) (pt_const _), ev_gm _ _ (pt_const _) (pt_const _)]
    ring
end GlobalTheory.ChF


