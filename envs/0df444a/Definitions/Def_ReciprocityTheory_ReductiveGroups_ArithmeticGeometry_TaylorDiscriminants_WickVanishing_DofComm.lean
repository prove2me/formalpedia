-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_DofComm
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_DofComm
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:06:34.181793+00:00
-- url     : https://prove2.me/theorems/9429aa90-11ff-439d-917e-4505c6427974
-- title:
--   Dof Comm
-- statement:
--   Definitions and structural lemmas for Dof Comm, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/DofComm.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_ConnectionKillsSeries
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeBilinearTermEqNegDoubleSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LogInv
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeExp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_CZ_cons
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_CZ_nil
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_CZ_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_cc_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_cc_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_cz01
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_cz12
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_pt_apply

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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB.LogPf
namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab
section VF
variable {k : Type} [CommRing k] {τ : Type} [Fintype τ]
end VF
section Law
variable {k : Type} [CommRing k] {d : ℕ} (G : FGLaw k d)
def co (v : Fin d → k) : Fin 1 × Fin d → PS k 1 d := fun p => ∑ i, C (v i) * Jac G p.2 i
end Law
section Transfer
theorem map_ev {R k : Type} [CommRing R] [CommRing k] (φ : R →+* k) {d m n : ℕ} {a : Fin m → Pt R n d} (ha : CZ a)
    (f : PS R m d) : MvPowerSeries.map φ (ev a f) = ev (fun j i => MvPowerSeries.map φ (a j i)) (MvPowerSeries.map φ f) := by
  exact MvPowerSeries.map_subst ha.hasSubst f
variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
variable (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k]
def lawK (B : FB R d O) : FGLaw k d where
  F := B.FK k
  const i := by
    simp [FB.FK, FGLaw.mapF, B.G.const i]
  unit i := by
    have h := congrArg (MvPowerSeries.map (algebraMap R k)) (B.G.unit i)
    rw [map_ev _ (CZ.cons cc_zero (CZ.cons (cc_pt 0) CZ.nil)), map_X] at h
    have e : (fun j c => MvPowerSeries.map (algebraMap R k) ((![0, pt R d 0] : Fin 2 → Pt R 1 d) j c)) =
        (![0, pt k d 0] : Fin 2 → Pt k 1 d) := by
      funext j c
      fin_cases j <;> simp [pt_apply]
    rw [e] at h
    exact h
  comm i := by
    have h := congrArg (MvPowerSeries.map (algebraMap R k)) (B.G.comm i)
    rw [map_ev _ (CZ.cons (cc_pt 1) (CZ.cons (cc_pt 0) CZ.nil))] at h
    have e : (fun j c => MvPowerSeries.map (algebraMap R k) ((![pt R d 1, pt R d 0] : Fin 2 → Pt R 2 d) j c)) =
        (![pt k d 1, pt k d 0] : Fin 2 → Pt k 2 d) := by
      funext j c
      fin_cases j <;> simp [pt_apply]
    rw [e] at h
    exact h
  assoc i := by
    have hL : CZ (![fun l => ev (n := 3) ![pt R d 0, pt R d 1] (B.G.F l), pt R d 2] : Fin 2 → Pt R 3 d) :=
      CZ.cons (fun l => constantCoeff_ev cz01 (B.G.const l)) (CZ.cons (cc_pt 2) CZ.nil)
    have hR : CZ (![pt R d 0, fun l => ev (n := 3) ![pt R d 1, pt R d 2] (B.G.F l)] : Fin 2 → Pt R 3 d) :=
      CZ.cons (cc_pt 0) (CZ.cons (fun l => constantCoeff_ev cz12 (B.G.const l)) CZ.nil)
    have h := congrArg (MvPowerSeries.map (algebraMap R k)) (B.G.assoc i)
    rw [map_ev _ hL, map_ev _ hR] at h
    have eL : (fun j c => MvPowerSeries.map (algebraMap R k)
        ((![fun l => ev (n := 3) ![pt R d 0, pt R d 1] (B.G.F l), pt R d 2] : Fin 2 → Pt R 3 d) j c)) =
        (![fun l => ev (n := 3) ![pt k d 0, pt k d 1] (B.FK k l), pt k d 2] : Fin 2 → Pt k 3 d) := by
      funext j c
      fin_cases j
      · show MvPowerSeries.map (algebraMap R k) (ev (n := 3) ![pt R d 0, pt R d 1] (B.G.F c)) =
          ev (n := 3) ![pt k d 0, pt k d 1] (B.FK k c)
        rw [map_ev _ cz01]
        congr 1
        funext j' c'
        fin_cases j' <;> simp [pt_apply]
      · simp [pt_apply]
    have eR : (fun j c => MvPowerSeries.map (algebraMap R k)
        ((![pt R d 0, fun l => ev (n := 3) ![pt R d 1, pt R d 2] (B.G.F l)] : Fin 2 → Pt R 3 d) j c)) =
        (![pt k d 0, fun l => ev (n := 3) ![pt k d 1, pt k d 2] (B.FK k l)] : Fin 2 → Pt k 3 d) := by
      funext j c
      fin_cases j
      · simp [pt_apply]
      · show MvPowerSeries.map (algebraMap R k) (ev (n := 3) ![pt R d 1, pt R d 2] (B.G.F c)) =
          ev (n := 3) ![pt k d 1, pt k d 2] (B.FK k c)
        rw [map_ev _ cz12]
        congr 1
        funext j' c'
        fin_cases j' <;> simp [pt_apply]
    rw [eL, eR] at h
    exact h
end Transfer
end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab


