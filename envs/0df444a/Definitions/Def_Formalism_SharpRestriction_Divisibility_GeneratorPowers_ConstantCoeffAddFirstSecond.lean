-- Prove2me | Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ConstantCoeffAddFirstSecond
-- name    : Formalism_SharpRestriction_Divisibility_GeneratorPowers_ConstantCoeffAddFirstSecond
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T14:33:40.495815+00:00
-- url     : https://prove2.me/theorems/c408a193-31d8-5b7d-af61-cb1358eceb22
-- title:
--   Constant Coeff Add First Second
-- statement:
--   Definitions and structural lemmas for Constant Coeff Add First Second, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/Divisibility/GeneratorPowers/ConstantCoeffAddFirstSecond.lean

import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ConstantCoeffAddSecondThird
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_MulGenScaleRight
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_JetSubstPSTrunc
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_FBIdJet_psJet_mul
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_FBIdJet_psJet_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_inv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_CZ_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_cc_ev
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_ev_X
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_ev_ev
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_cc_ev
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_ev_X
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_ev_ev
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_exp_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_exp_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_hasSubst_pts
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_subst_exp

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
namespace Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix2c
open MvPolynomial Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix ReciprocityTheory.ChartRestriction.G.TB Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix2b
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw FB)
open ReciprocityTheory.ChartRestriction.G.TB.WickVanishing (ev_ev ev_X hasSubst_pts exp_add subst_exp exp_zero)
section Series
variable {S : Type} [CommRing S] [Algebra ℚ S] {d : ℕ}
lemma cc_pt_lemma {n : ℕ} (j : Fin n) (i : Fin d) :
    MvPowerSeries.constantCoeff (pt S d j i) = 0 := by
  simp [ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.pt]
lemma cc_logOf_lemma_2 (G : FGLaw S d) (i : Fin d) :
    MvPowerSeries.constantCoeff (ReciprocityTheory.ChartRestriction.G.TB.LogPf.logOf G i) = 0 := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
  show ReciprocityTheory.ChartRestriction.G.TB.LogPf.prim _ 0 = 0
  simp [ReciprocityTheory.ChartRestriction.G.TB.LogPf.prim]
lemma cc_lg_lemma_7 {n : ℕ} (G : FGLaw S d) (j : Fin n) (i : Fin d) :
    MvPowerSeries.constantCoeff (Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix.lg G j i) = 0 :=
  ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.cc_ev (a := ![pt S d j])
    (fun j' i' => by fin_cases j'; exact cc_pt_lemma j i') (cc_logOf_lemma_2 G i)
lemma cc_bilL_lemma_8 (G : FGLaw S d) (c : Fin d → Fin d → S) :
    MvPowerSeries.constantCoeff (bilL G c) = 0 := by
  simp [Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix.bilL, MvPowerSeries.smul_eq_C_mul, cc_lg_lemma_7]
theorem bilL_add (G : FGLaw S d) (c c' : Fin d → Fin d → S) : bilL G (c + c') = bilL G c + bilL G c' := by
  simp only [Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix.bilL, Pi.add_apply, add_smul, Finset.sum_add_distrib]
theorem bilL_zero (G : FGLaw S d) : bilL G 0 = 0 := by
  simp [Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix.bilL]
theorem twist_add (G : FGLaw S d) (c c' : Fin d → Fin d → S) :
    expP (-bilL G (c + c')) = expP (-bilL G c) * expP (-bilL G c') := by
  rw [bilL_add, neg_add]
  exact exp_add (by rw [map_neg, cc_bilL_lemma_8, neg_zero]) (by rw [map_neg, cc_bilL_lemma_8, neg_zero])
theorem twist_zero (G : FGLaw S d) : expP (-bilL G 0) = 1 := by
  rw [bilL_zero, neg_zero]
  exact exp_zero
end Series
section Jet
variable {S : Type} [CommRing S] [Algebra ℚ S] {d : ℕ}
def twU (G : FGLaw S d) (c : Fin d → Fin d → S) (m : ℕ) : (Jet S (Fin 2 × Fin d) m)ˣ where
  val := psJet m (expP (-bilL G c))
  inv := psJet m (expP (-bilL G (-c)))
  val_inv := by rw [← FBIdJet.psJet_mul, ← twist_add, add_neg_cancel, twist_zero, FBIdJet.psJet_one]
  inv_val := by rw [← FBIdJet.psJet_mul, ← twist_add, neg_add_cancel, twist_zero, FBIdJet.psJet_one]
end Jet
section Chart
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix2
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} {S : Type} [CommRing S] [Algebra c.F S] [Algebra ℚ S] (y : FrPt Xo c S)
end Chart
end Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix2c


