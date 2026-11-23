-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_FormalGroupLawPointMaps
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_FormalGroupLawPointMaps
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:43:05.659075+00:00
-- url     : https://prove2.me/theorems/27b4e174-f48a-4bbd-ab81-250a162648e9
-- title:
--   Formal Group Law Point Maps
-- statement:
--   Definitions and structural lemmas for Formal Group Law Point Maps, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/FormalGroupLawPointMaps.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_DofComm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_ActLin
import Theorems.Thm_Formalism_FG_InjVAux_HasOrd_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_CZ_cons
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_CZ_nil
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_CZ_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_cc_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_cc_pt

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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB.LogPf ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
namespace ReciprocityTheory.ChartRestriction.G.TB.PointMapComposition
variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
variable (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k]
def mapPt {n : ℕ} (p : Pt R n d) : Pt k n d := fun i => MvPowerSeries.map (algebraMap R k) (p i)
theorem mapPt_pt {n : ℕ} (j : Fin n) : mapPt k (pt R d j) = pt k d j := by
  funext i
  simp [mapPt, pt, MvPowerSeries.map_X]
theorem mapPt_comp1 {n : ℕ} (φ : Pt R 1 d) (a : Pt R n d) (ha : ∀ i, constantCoeff (a i) = 0) :
    mapPt k (comp1 φ a) = comp1 (mapPt k φ) (mapPt k a) := by
  funext i
  have hs : MvPowerSeries.HasSubst (fun p : Fin 1 × Fin d => ![a] p.1 p.2) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun p => by
      rcases p with ⟨j, l⟩; fin_cases j; exact ha l)
  simp only [mapPt, comp1, ev]
  rw [MvPowerSeries.map_subst hs]
  congr 1
  funext p
  rcases p with ⟨j, l⟩
  fin_cases j
  rfl
theorem mapPt_addOf {n : ℕ} (F : Fin d → PS R 2 d) (u v : Pt R n d) (hu : ∀ i, constantCoeff (u i) = 0)
    (hv : ∀ i, constantCoeff (v i) = 0) :
    mapPt k (addOf F u v) = addOf (fun i => MvPowerSeries.map (algebraMap R k) (F i)) (mapPt k u) (mapPt k v) := by
  funext i
  have hs : MvPowerSeries.HasSubst (fun p : Fin 2 × Fin d => ![u, v] p.1 p.2) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun p => by
      rcases p with ⟨j, l⟩; fin_cases j
      · exact hu l
      · exact hv l)
  simp only [mapPt, addOf, ev]
  rw [MvPowerSeries.map_subst hs]
  congr 1
  funext p
  rcases p with ⟨j, l⟩
  fin_cases j <;> rfl
def actKO (B : FB R d O) : OAct O (Nab.lawK k B) where
  act a := B.actK k a
  const a i := by simp [FB.actK, B.A.const a i]
  hom a := by
    have h := congrArg (mapPt k) (B.A.hom a)
    have hp0 : ∀ i, constantCoeff (pt R (n := 2) d 0 i) = 0 := LogPf.cc_pt 0
    have hp1 : ∀ i, constantCoeff (pt R (n := 2) d 1 i) = 0 := LogPf.cc_pt 1
    have hadd : ∀ i, constantCoeff (B.G.add (pt R (n := 2) d 0) (pt R (n := 2) d 1) i) = 0 := fun i =>
      constantCoeff_ev (CZ.cons hp0 (CZ.cons hp1 CZ.nil)) (B.G.const i)
    have hc : ∀ (j : Fin 2) i, constantCoeff (comp1 (B.A.act a) (pt R (n := 2) d j) i) = 0 := fun j i =>
      constantCoeff_ev (CZ.cons (LogPf.cc_pt j) CZ.nil) (B.A.const a i)
    rw [mapPt_comp1 k _ _ hadd, mapPt_addOf k _ _ _ hp0 hp1, mapPt_addOf k _ _ _ (hc 0) (hc 1),
      mapPt_comp1 k _ _ hp0, mapPt_comp1 k _ _ hp1, mapPt_pt, mapPt_pt] at h
    exact h
  add_act a b := by
    have h := congrArg (mapPt k) (B.A.add_act a b)
    rw [mapPt_addOf k _ _ _ (B.A.const a) (B.A.const b)] at h
    exact h
  mul_act a b := by
    have h := congrArg (mapPt k) (B.A.mul_act a b)
    rw [mapPt_comp1 k _ _ (B.A.const b)] at h
    exact h
  one_act := by
    have h := congrArg (mapPt k) B.A.one_act
    rw [mapPt_pt] at h
    exact h
end ReciprocityTheory.ChartRestriction.G.TB.PointMapComposition


