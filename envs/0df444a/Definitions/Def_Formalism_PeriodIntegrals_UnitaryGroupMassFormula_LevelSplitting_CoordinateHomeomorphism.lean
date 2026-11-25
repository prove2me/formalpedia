-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_CoordinateHomeomorphism
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_CoordinateHomeomorphism
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T12:21:24.363272+00:00
-- url     : https://prove2.me/theorems/1d9df2ee-88ec-5c4b-b528-49a30b38dfd2
-- title:
--   Coordinate Homeomorphism
-- statement:
--   Definitions and structural lemmas for Coordinate Homeomorphism, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/CoordinateHomeomorphism.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_NCIface
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_UnitaryGroupSecondCountableT2
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.LevelKSplit.W.NC
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.LevelKSplit
open scoped TensorProduct
section Gen
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {Q : Type} [AddCommGroup Q] [TopologicalSpace Q] [ContinuousAdd Q]
structure CoordHyp (N A N1 Z : Subgroup G) (Lev : G → G) (sH : Q → G) (yQ : N1 → Q) : Prop where
  hAN : A ≤ N
  coordinate_level_le : N1 ≤ N
  hZN1 : Z ≤ N1
  cLev : Continuous Lev
  csH : Continuous sH
  cyQ : Continuous yQ
  lev_mem : ∀ n ∈ N, Lev n ∈ A
  lev_rest : ∀ n ∈ N, (Lev n)⁻¹ * n ∈ N1
  triv : ∀ u ∈ A, u ∈ N1 → u = 1
  norm1 : ∀ n ∈ N, ∀ m ∈ N1, n * m * n⁻¹ ∈ N1
  sH_mem : ∀ y, sH y ∈ N1
  dec : ∀ m : N1, (sH (yQ m))⁻¹ * (m : G) ∈ Z
  yQ_sH : ∀ y z (hz : z ∈ Z), yQ ⟨sH y * z, N1.mul_mem (sH_mem y) (hZN1 hz)⟩ = y
  cent : ∀ z ∈ Z, ∀ m ∈ N1, z * m = m * z
  mul : ∀ y y', sH y * sH y' * (sH (y + y'))⁻¹ ∈ Z
variable {N A N1 Z : Subgroup G} {Lev : G → G} {sH : Q → G} {yQ : N1 → Q}
theorem lev_eq (H : CoordHyp N A N1 Z Lev sH yQ) (u : A) (w : G) (hw : w ∈ N1) :
    Lev ((u : G) * w) = u := by
  have hg : (u : G) * w ∈ N := N.mul_mem (H.hAN u.2) (H.coordinate_level_le hw)
  set v := Lev ((u : G) * w) with hv
  have h1 : v⁻¹ * (u : G) ∈ N1 := by
    have : v⁻¹ * (u : G) = (v⁻¹ * ((u : G) * w)) * w⁻¹ := by group
    rw [this]
    exact N1.mul_mem (H.lev_rest _ hg) (N1.inv_mem hw)
  have h2 : v⁻¹ * (u : G) ∈ A := A.mul_mem (A.inv_mem (H.lev_mem _ hg)) u.2
  have h3 := H.triv _ h2 h1
  have : (u : G) = v := by
    calc (u : G) = v * (v⁻¹ * u) := by group
      _ = v := by rw [h3, mul_one]
  exact this.symm
def cfun (H : CoordHyp N A N1 Z Lev sH yQ) (p : A × (Q × Z)) : N :=
  ⟨(p.1 : G) * sH p.2.1 * (p.2.2 : G),
    N.mul_mem (N.mul_mem (H.hAN p.1.2) (H.coordinate_level_le (H.sH_mem _))) (H.coordinate_level_le (H.hZN1 p.2.2.2))⟩
def cm (H : CoordHyp N A N1 Z Lev sH yQ) (n : N) : N1 :=
  ⟨(Lev n)⁻¹ * (n : G), H.lev_rest n n.2⟩
def cinv (H : CoordHyp N A N1 Z Lev sH yQ) (n : N) : A × (Q × Z) :=
  (⟨Lev n, H.lev_mem n n.2⟩, yQ (cm H n), ⟨(sH (yQ (cm H n)))⁻¹ * (cm H n : G), H.dec _⟩)
theorem cinv_cfun (H : CoordHyp N A N1 Z Lev sH yQ) (p : A × (Q × Z)) :
    cinv H (cfun H p) = p := by
  obtain ⟨u, y, z⟩ := p
  have hw : sH y * (z : G) ∈ N1 := N1.mul_mem (H.sH_mem y) (H.hZN1 z.2)
  have hL : Lev ((u : G) * sH y * (z : G)) = u := by
    rw [mul_assoc]; exact lev_eq H u _ hw
  have hm : cm H (cfun H (u, y, z)) = ⟨sH y * (z : G), hw⟩ := by
    apply Subtype.ext
    simp only [cm, cfun]
    rw [hL]; group
  have hy : yQ (cm H (cfun H (u, y, z))) = y := by
    rw [hm]; exact H.yQ_sH y z z.2
  refine Prod.ext (Subtype.ext ?_) (Prod.ext hy (Subtype.ext ?_))
  · simp only [cinv, cfun]; exact hL
  · simp only [cinv]
    rw [hy, hm]
    group
theorem cfun_cinv (H : CoordHyp N A N1 Z Lev sH yQ) (n : N) : cfun H (cinv H n) = n := by
  apply Subtype.ext
  simp only [cfun, cinv, cm]
  group
theorem continuous_cm (H : CoordHyp N A N1 Z Lev sH yQ) : Continuous (cm H) :=
  Continuous.subtype_mk ((H.cLev.comp continuous_subtype_val).inv.mul continuous_subtype_val) _
def cHomeo (H : CoordHyp N A N1 Z Lev sH yQ) : (A × (Q × Z)) ≃ₜ N where
  toFun := cfun H
  invFun := cinv H
  left_inv := cinv_cfun H
  right_inv := cfun_cinv H
  continuous_toFun := Continuous.subtype_mk
    (((continuous_subtype_val.comp continuous_fst).mul
      (H.csH.comp (continuous_fst.comp continuous_snd))).mul
      (continuous_subtype_val.comp (continuous_snd.comp continuous_snd))) _
  continuous_invFun := by
    have h1 := continuous_cm H
    refine Continuous.prodMk (Continuous.subtype_mk (H.cLev.comp continuous_subtype_val) _)
      (Continuous.prodMk (H.cyQ.comp h1) (Continuous.subtype_mk ?_ _))
    exact (H.csH.comp (H.cyQ.comp h1)).inv.mul (continuous_subtype_val.comp h1)
end Gen
end PI.LevelKSplit.W.NC


