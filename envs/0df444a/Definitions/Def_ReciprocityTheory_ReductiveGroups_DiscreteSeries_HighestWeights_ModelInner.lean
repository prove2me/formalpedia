-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ModelInner
-- name    : ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ModelInner
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T13:43:34.100886+00:00
-- url     : https://prove2.me/theorems/52d27d36-326b-5b6d-a8b5-037d9f3b5e94
-- title:
--   Model Inner
-- statement:
--   Definitions and structural lemmas for Model Inner, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/HighestWeights/ModelInner.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_ModelSpace
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_continuous_of_mem_Vsp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_finiteDimensional_Vsp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_compactSpace_KG

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory
namespace ReciprocityTheory.ChartRestriction.DS.HW
open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
variable {n : ℕ}
def MV (ε : Fin n → Bool) (m : Fin n → ℤ) : Type := ↥(Vsp ε m)
instance (ε : Fin n → Bool) (m : Fin n → ℤ) : AddCommGroup (MV ε m) := inferInstanceAs (AddCommGroup ↥(Vsp ε m))
instance (ε : Fin n → Bool) (m : Fin n → ℤ) : Module ℂ (MV ε m) := inferInstanceAs (Module ℂ ↥(Vsp ε m))
def MV.fn {ε : Fin n → Bool} {m : Fin n → ℤ} (f : MV ε m) : KG ε → ℂ := ((show ↥(Vsp ε m) from f) : KG ε → ℂ)
def MV.mk {ε : Fin n → Bool} {m : Fin n → ℤ} (f : KG ε → ℂ) (hf : f ∈ Vsp ε m) : MV ε m :=
  (⟨f, hf⟩ : ↥(Vsp ε m))
theorem MV.mem {ε : Fin n → Bool} {m : Fin n → ℤ} (f : MV ε m) : f.fn ∈ Vsp ε m := by
  exact (show ↥(Vsp ε m) from f).2
@[simp] theorem MV.fn_mk {ε : Fin n → Bool} {m : Fin n → ℤ} (f : KG ε → ℂ) (hf : f ∈ Vsp ε m) :
    (MV.mk f hf).fn = f := rfl
theorem MV.ext {ε : Fin n → Bool} {m : Fin n → ℤ} {f g : MV ε m} (h : f.fn = g.fn) : f = g := by
  exact Subtype.ext h
@[simp] theorem MV.fn_add {ε : Fin n → Bool} {m : Fin n → ℤ} (f g : MV ε m) : (f + g).fn = f.fn + g.fn := rfl
@[simp] theorem MV.fn_smul {ε : Fin n → Bool} {m : Fin n → ℤ} (c : ℂ) (f : MV ε m) : (c • f).fn = c • f.fn := rfl
@[simp] theorem MV.fn_zero {ε : Fin n → Bool} {m : Fin n → ℤ} : (0 : MV ε m).fn = 0 := rfl
def mvInner {ε : Fin n → Bool} {m : Fin n → ℤ} (f g : MV ε m) : ℂ :=
  ∫ x, starRingEnd ℂ (f.fn x) * g.fn x ∂(muK ε)
theorem MV.continuous_fn {ε : Fin n → Bool} {m : Fin n → ℤ} (f : MV ε m) : Continuous f.fn := by
  exact continuous_of_mem_Vsp ε m f.mem
theorem integrable_of_continuous_KG {ε : Fin n → Bool} {F : KG ε → ℂ} (hF : Continuous F) :
    MeasureTheory.Integrable F (muK ε) := by

  have := compactSpace_KG ε
  exact hF.integrable_of_hasCompactSupport (isClosed_tsupport F).isCompact
theorem mvInner_integrable {ε : Fin n → Bool} {m : Fin n → ℤ} (f g : MV ε m) :
    MeasureTheory.Integrable (fun x => starRingEnd ℂ (f.fn x) * g.fn x) (muK ε) := by
  exact integrable_of_continuous_KG
    ((Complex.continuous_conj.comp f.continuous_fn).mul g.continuous_fn)
theorem mvInner_self_eq {ε : Fin n → Bool} {m : Fin n → ℤ} (f : MV ε m) :
    mvInner f f = ((∫ x, Complex.normSq (f.fn x) ∂(muK ε) : ℝ) : ℂ) := by
  unfold mvInner
  simp_rw [← Complex.normSq_eq_conj_mul_self]
  exact integral_ofReal
theorem mvInner_conj {ε : Fin n → Bool} {m : Fin n → ℤ} (f g : MV ε m) :
    starRingEnd ℂ (mvInner g f) = mvInner f g := by
  unfold mvInner
  rw [← integral_conj]
  congr 1
  funext x
  simp only [map_mul, Complex.conj_conj]
  exact mul_comm _ _
theorem mvInner_re_nonneg {ε : Fin n → Bool} {m : Fin n → ℤ} (f : MV ε m) : 0 ≤ (mvInner f f).re := by
  rw [mvInner_self_eq, Complex.ofReal_re]
  exact integral_nonneg fun x => Complex.normSq_nonneg _
theorem mvInner_add_left {ε : Fin n → Bool} {m : Fin n → ℤ} (f g h : MV ε m) :
    mvInner (f + g) h = mvInner f h + mvInner g h := by
  simp only [mvInner, MV.fn_add, Pi.add_apply, map_add, add_mul]
  exact integral_add (mvInner_integrable f h) (mvInner_integrable g h)
theorem mvInner_smul_left {ε : Fin n → Bool} {m : Fin n → ℤ} (f g : MV ε m) (c : ℂ) :
    mvInner (c • f) g = starRingEnd ℂ c * mvInner f g := by
  simp only [mvInner, MV.fn_smul, Pi.smul_apply, smul_eq_mul, map_mul, mul_assoc]
  exact integral_const_mul _ _
theorem mvInner_definite {ε : Fin n → Bool} {m : Fin n → ℤ} (f : MV ε m) (h : mvInner f f = 0) : f = 0 := by

  have hc : Continuous fun x => Complex.normSq (f.fn x) :=
    Complex.continuous_normSq.comp f.continuous_fn
  rw [mvInner_self_eq, Complex.ofReal_eq_zero] at h
  have hae : (fun x => Complex.normSq (f.fn x)) =ᵐ[muK ε] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun x => Complex.normSq_nonneg _)
      (by
        have := compactSpace_KG ε
        exact hc.integrable_of_hasCompactSupport (isClosed_tsupport _).isCompact)).mp h
  have hz : (fun x => Complex.normSq (f.fn x)) = 0 :=
    (Continuous.ae_eq_iff_eq (muK ε) hc continuous_const).mp hae
  apply MV.ext
  funext x
  simpa using congrFun hz x
@[instance_reducible]
def mvCore (ε : Fin n → Bool) (m : Fin n → ℤ) : InnerProductSpace.Core ℂ (MV ε m) where
  inner := mvInner
  conj_inner_symm := mvInner_conj
  re_inner_nonneg := mvInner_re_nonneg
  add_left := mvInner_add_left
  smul_left := mvInner_smul_left
  definite := mvInner_definite
instance (ε : Fin n → Bool) (m : Fin n → ℤ) : NormedAddCommGroup (MV ε m) :=
  @InnerProductSpace.Core.toNormedAddCommGroup ℂ (MV ε m) _ _ _ (mvCore ε m)
instance (ε : Fin n → Bool) (m : Fin n → ℤ) : InnerProductSpace ℂ (MV ε m) :=
  InnerProductSpace.ofCore (mvCore ε m).toCore
instance (ε : Fin n → Bool) (m : Fin n → ℤ) : FiniteDimensional ℂ (MV ε m) :=
  finiteDimensional_Vsp ε m
instance (ε : Fin n → Bool) (m : Fin n → ℤ) : CompleteSpace (MV ε m) := FiniteDimensional.complete ℂ _
end ReciprocityTheory.ChartRestriction.DS.HW


