-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_BiextCoeffSecondLinear
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_BiextCoeffSecondLinear
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T00:57:45.126664+00:00
-- url     : https://prove2.me/theorems/0f317109-eb1f-4996-9c2b-00e76b23abb3
-- title:
--   Biext Coeff Second Linear
-- statement:
--   Definitions and structural lemmas for Biext Coeff Second Linear, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/BiextCoeffSecondLinear.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_FormalGroupCoeffSecondLinear
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_Pf_EigA_coeff_lin_ev
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_Pf_EigA_formal_group_coeff_first_linear
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_Pf_EigA_formal_group_coeff_second_linear
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_LogPf_CZ_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_dLin_comp1
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_dLin_pt

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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigA
section Act
variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
variable (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k]
theorem dLin_addOf (F : Fin d → PS k 2 d)
    (hF0 : ∀ i l, coeff (Finsupp.single ((0 : Fin 2), l) 1) (F i) = if l = i then 1 else 0)
    (hF1 : ∀ i l, coeff (Finsupp.single ((1 : Fin 2), l) 1) (F i) = if l = i then 1 else 0)
    (u v : Pt k 1 d) (hu : ∀ i, constantCoeff (u i) = 0) (hv : ∀ i, constantCoeff (v i) = 0) :
    dLin (addOf F u v) = dLin u + dLin v := by
  classical
  ext i j
  show coeff (Finsupp.single ((0 : Fin 1), j) 1) (ev ![u, v] (F i)) = dLin u i j + dLin v i j
  rw [coeff_lin_ev _ (by
      intro a i'
      fin_cases a
      · exact hu i'
      · exact hv i')]
  rw [Fintype.sum_prod_type, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, hF0, hF1, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rfl
theorem const_actK' (B : FB R d O) (a : O) (l : Fin d) : constantCoeff (B.actK k a l) = 0 := by
  simp [FB.actK, B.A.const]
theorem actK_add (B : FB R d O) (a b : O) :
    B.actK k (a + b) = addOf (B.FK k) (B.actK k a) (B.actK k b) := by
  funext i
  show MvPowerSeries.map (algebraMap R k) (B.A.act (a + b) i) = ev ![B.actK k a, B.actK k b] (B.FK k i)
  rw [B.A.add_act]
  show MvPowerSeries.map (algebraMap R k) (ev ![B.A.act a, B.A.act b] (B.G.F i)) = _
  rw [Nab.map_ev (algebraMap R k) (by
      intro j l
      fin_cases j
      · exact B.A.const a l
      · exact B.A.const b l)]
  congr 1
  funext j l
  fin_cases j <;> rfl
theorem actK_mul (B : FB R d O) (a b : O) : B.actK k (a * b) = comp1 (B.actK k a) (B.actK k b) := by
  funext i
  show MvPowerSeries.map (algebraMap R k) (B.A.act (a * b) i) = ev ![B.actK k b] (B.actK k a i)
  rw [B.A.mul_act]
  show MvPowerSeries.map (algebraMap R k) (ev ![B.A.act b] (B.A.act a i)) = _
  rw [Nab.map_ev (algebraMap R k) (by
      intro j l
      fin_cases j
      exact B.A.const b l)]
  congr 1
  funext j l
  fin_cases j
  rfl
theorem actK_one (B : FB R d O) : B.actK k 1 = pt k d 0 := by
  funext i
  show MvPowerSeries.map (algebraMap R k) (B.A.act 1 i) = X ((0 : Fin 1), i)
  rw [B.A.one_act]
  simp [pt]
theorem biext_coeff_first_linear (B : FB R d O) (i l : Fin d) :
    coeff (Finsupp.single ((0 : Fin 2), l) 1) (B.FK k i) = if l = i then 1 else 0 := by
  show coeff _ (MvPowerSeries.map (algebraMap R k) (B.G.F i)) = _
  rw [coeff_map, formal_group_coeff_first_linear]
  split_ifs <;> simp
theorem biext_coeff_second_linear (B : FB R d O) (i l : Fin d) :
    coeff (Finsupp.single ((1 : Fin 2), l) 1) (B.FK k i) = if l = i then 1 else 0 := by
  show coeff _ (MvPowerSeries.map (algebraMap R k) (B.G.F i)) = _
  rw [coeff_map, formal_group_coeff_second_linear]
  split_ifs <;> simp
theorem dAct_add (B : FB R d O) (a b : O) : dAct k B (a + b) = dAct k B a + dAct k B b := by
  show dLin (B.actK k (a + b)) = dLin (B.actK k a) + dLin (B.actK k b)
  rw [actK_add, dLin_addOf k _ (biext_coeff_first_linear k B) (biext_coeff_second_linear k B) _ _ (const_actK' k B a) (const_actK' k B b)]
theorem dAct_mul (B : FB R d O) (a b : O) : dAct k B (a * b) = dAct k B a * dAct k B b := by
  show dLin (B.actK k (a * b)) = dLin (B.actK k a) * dLin (B.actK k b)
  rw [actK_mul, dLin_comp1 _ _ (const_actK' k B b)]
theorem dAct_one (B : FB R d O) : dAct k B 1 = 1 := by
  show dLin (B.actK k 1) = 1
  rw [actK_one, dLin_pt]
def dActH (B : FB R d O) : O →+* Matrix (Fin d) (Fin d) k where
  toFun a := dAct k B a
  map_one' := dAct_one k B
  map_mul' a b := dAct_mul k B a b
  map_zero' := by
    have h0 := dAct_add k B 0 0
    rw [add_zero] at h0
    simpa using h0
  map_add' a b := dAct_add k B a b
def dActS (B : FB R d O) : O →+* Matrix (Fin d) (Fin d) k where
  toFun a := (dActH k B (star a)).transpose
  map_one' := by rw [star_one, map_one, Matrix.transpose_one]
  map_mul' a b := by rw [star_mul, map_mul, Matrix.transpose_mul]
  map_zero' := by rw [star_zero, map_zero, Matrix.transpose_zero]
  map_add' a b := by rw [star_add, map_add, Matrix.transpose_add]
end Act
section H
variable {R : Type} [CommRing R] {d : ℕ} (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] (h : PS k 2 d)
end H
end ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigA


