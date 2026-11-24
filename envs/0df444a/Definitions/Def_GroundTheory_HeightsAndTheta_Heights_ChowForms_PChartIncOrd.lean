-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartIncOrd
-- name    : GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartIncOrd
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:59:02.834697+00:00
-- url     : https://prove2.me/theorems/4cb49413-9e59-4ccd-8c86-026a80f8c4a5
-- title:
--   PChart Inc Ord
-- statement:
--   Definitions and structural lemmas for PChart Inc Ord, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PChartIncOrd.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsChartIncOrd
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartLocalOrder
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
namespace ChartIncOrd
variable {F : Type} [Field F] {n : ℕ} (I : Ideal (MvPolynomial (Fin n) F)) (t : Fin n → F) (e : ℕ)
abbrev ChartQ : Type := MvPolynomial (Fin n) F ⧸ (I ⊔ Ideal.span {linForm t - 1})
abbrev mkQ : MvPolynomial (Fin n) F →+* ChartQ I t := Ideal.Quotient.mk _
def mkS : MvPolynomial (Fin n ⊕ Fin e × Fin n) F →+* ChartInc I t e := Ideal.Quotient.mk _
theorem mkS_surjective : Function.Surjective (mkS I t e) := Ideal.Quotient.mk_surjective
theorem mkS_eq_zero {a : MvPolynomial (Fin n ⊕ Fin e × Fin n) F} (h : a ∈ chartIncIdeal I t e) :
    mkS I t e a = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr h
theorem chartX_apply (x : MvPolynomial (Fin n) F) :
    chartX I t e x = mkS I t e (rename Sum.inl x) := rfl
def toInc : ChartQ I t →+* ChartInc I t e :=
  Ideal.Quotient.lift _ (chartX I t e) fun a ha => by
    rw [chartX_apply]
    exact mkS_eq_zero I t e (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ ha))
theorem toInc_mk (x : MvPolynomial (Fin n) F) :
    toInc I t e (mkQ I t x) = chartX I t e x := rfl
theorem sum_tQ : (∑ m, mkQ I t (C (t m) * X m)) = 1 := by
  rw [← map_sum, ← map_one (mkQ I t), Ideal.Quotient.eq]
  exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)
theorem sum_tS : (∑ m, chartX I t e (C (t m) * X m)) = 1 := by
  have := congrArg (toInc I t e) (sum_tQ I t)
  simpa [map_sum, toInc_mk] using this
theorem sum_uS (i : Fin e) :
    (∑ m, mkS I t e (X (Sum.inr (i, m)) * X (Sum.inl m))) = 0 := by
  rw [← map_sum]
  exact mkS_eq_zero I t e (Ideal.mem_sup_right (Ideal.subset_span ⟨i, rfl⟩))
def fwd : MvPolynomial (Fin e × Fin n) (ChartQ I t) →+* MvPolynomial (Fin e) (ChartInc I t e) :=
  eval₂Hom (C.comp (toInc I t e)) fun ij =>
    C (mkS I t e (X (Sum.inr ij))) + X ij.1 * C (chartX I t e (C (t ij.2)))
theorem fwd_C (q : ChartQ I t) : fwd I t e (C q) = C (toInc I t e q) := by
  simp [fwd]
theorem fwd_X (ij : Fin e × Fin n) :
    fwd I t e (X ij) = C (mkS I t e (X (Sum.inr ij))) + X ij.1 * C (chartX I t e (C (t ij.2))) := by
  simp [fwd]
def back₀ : MvPolynomial (Fin n ⊕ Fin e × Fin n) F →+* MvPolynomial (Fin e × Fin n) (ChartQ I t) :=
  eval₂Hom (C.comp ((mkQ I t).comp C))
    (Sum.elim (fun m => C (mkQ I t (X m)))
      (fun ij => genSubst (fun m => mkQ I t (X m)) (fun m => mkQ I t (C (t m))) ij))
theorem back₀_C (r : F) : back₀ I t e (C r) = C (mkQ I t (C r)) := by
  simp [back₀]
theorem back₀_inl (m : Fin n) : back₀ I t e (X (Sum.inl m)) = C (mkQ I t (X m)) := by
  simp [back₀]
theorem back₀_inr (ij : Fin e × Fin n) :
    back₀ I t e (X (Sum.inr ij)) = genSubst (fun m => mkQ I t (X m)) (fun m => mkQ I t (C (t m))) ij := by
  simp [back₀]
theorem back₀_rename (x : MvPolynomial (Fin n) F) :
    back₀ I t e (rename Sum.inl x) = C (mkQ I t x) := by
  have : (back₀ I t e).comp (rename Sum.inl).toRingHom =
      (C : ChartQ I t →+* MvPolynomial (Fin e × Fin n) (ChartQ I t)).comp (mkQ I t) := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun m => ?_)
    · simp [back₀_C]
    · simp [back₀_inl]
  exact congrArg (fun f => f x) this
theorem chartIncIdeal_le_ker : chartIncIdeal I t e ≤ RingHom.ker (back₀ I t e) := by
  refine sup_le ?_ ?_
  · rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, RingHom.mem_ker]
    rw [back₀_rename, Ideal.Quotient.eq_zero_iff_mem.mpr ha, map_zero]
  · rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, RingHom.mem_ker]
    have h1 := congrArg (C : ChartQ I t →+* MvPolynomial (Fin e × Fin n) (ChartQ I t)) (sum_tQ I t)
    simp only [map_sum, map_mul, map_one] at h1
    simp only [map_sum, map_mul, back₀_inl, back₀_inr, genSubst]
    set S := ∑ l, X (i, l) * C (mkQ I t (X l))
    have : ∑ m, (X (i, m) - S * C (mkQ I t (C (t m)))) * C (mkQ I t (X m)) = S - S * 1 := by
      rw [← h1, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun m _ => ?_
      ring
    simpa using this
def back : ChartInc I t e →+* MvPolynomial (Fin e × Fin n) (ChartQ I t) :=
  Ideal.Quotient.lift (chartIncIdeal I t e) (back₀ I t e) fun _ ha => chartIncIdeal_le_ker I t e ha
theorem back_mk (a : MvPolynomial (Fin n ⊕ Fin e × Fin n) F) :
    back I t e (mkS I t e a) = back₀ I t e a := rfl
def bwd : MvPolynomial (Fin e) (ChartInc I t e) →+* MvPolynomial (Fin e × Fin n) (ChartQ I t) :=
  eval₂Hom (back I t e) fun i => ∑ m, X (i, m) * C (mkQ I t (X m))
theorem back_toInc (q : ChartQ I t) : back I t e (toInc I t e q) = C q := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
  exact (congrArg (back I t e) (toInc_mk I t e x)).trans (back₀_rename I t e x)
theorem sum_fwd (i : Fin e) :
    (∑ l, (C (mkS I t e (X (Sum.inr (i, l)))) + X i * C (chartX I t e (C (t l)))) *
      C (chartX I t e (X l))) = (X i : MvPolynomial (Fin e) (ChartInc I t e)) := by
  have hu := congrArg (C : ChartInc I t e →+* MvPolynomial (Fin e) (ChartInc I t e)) (sum_uS I t e i)
  have ht := congrArg (C : ChartInc I t e →+* MvPolynomial (Fin e) (ChartInc I t e)) (sum_tS I t e)
  simp only [map_sum, map_mul, map_one, map_zero] at hu ht
  have hX : ∀ l, chartX I t e (X l) = mkS I t e (X (Sum.inl l)) := fun l => by
    rw [chartX_apply, rename_X]
  simp only [hX] at ht ⊢
  calc _ = (∑ l, C (mkS I t e (X (Sum.inr (i, l)))) * C (mkS I t e (X (Sum.inl l)))) +
        X i * ∑ l, C (chartX I t e (C (t l))) * C (mkS I t e (X (Sum.inl l))) := by
          rw [Finset.mul_sum, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun l _ => ?_
          ring
    _ = X i := by rw [hu, ht]; ring
theorem fwd_back (s : ChartInc I t e) : fwd I t e (back I t e s) = C s := by
  have : ((fwd I t e).comp (back I t e)).comp (mkS I t e) = C.comp (mkS I t e) := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun v => ?_)
    · simp only [RingHom.comp_apply, back_mk, back₀_C, fwd_C, toInc_mk, chartX_apply, rename_C]
    · rcases v with m | ⟨i, m⟩
      · simp only [RingHom.comp_apply, back_mk, back₀_inl, fwd_C, toInc_mk, chartX_apply, rename_X]
      · simp only [RingHom.comp_apply, back_mk, back₀_inr, genSubst, map_sub, map_mul, map_sum, fwd_X,
          fwd_C, toInc_mk]
        linear_combination (-(C (chartX I t e (C (t m))))) * sum_fwd I t e i
  obtain ⟨a, rfl⟩ := mkS_surjective I t e s
  exact congrArg (fun f => f a) this
theorem fwd_bwd : (fwd I t e).comp (bwd I t e) = RingHom.id _ := by
  refine MvPolynomial.ringHom_ext (fun s => ?_) (fun i => ?_)
  · simp [bwd, fwd_back]
  · simp only [bwd, RingHom.comp_apply, eval₂Hom_X', map_sum, map_mul, fwd_X, fwd_C, toInc_mk,
      RingHom.id_apply]
    exact sum_fwd I t e i
theorem bwd_fwd : (bwd I t e).comp (fwd I t e) = RingHom.id _ := by
  refine MvPolynomial.ringHom_ext (fun q => ?_) (fun ij => ?_)
  · simp [fwd, bwd, back_toInc]
  · obtain ⟨i, m⟩ := ij
    simp only [RingHom.comp_apply, fwd_X, map_add, map_mul, bwd, eval₂Hom_C, eval₂Hom_X',
      RingHom.id_apply, chartX_apply, rename_C, back_mk, back₀_C, back₀_inr, genSubst]
    ring
def equiv : MvPolynomial (Fin e × Fin n) (ChartQ I t) ≃+* MvPolynomial (Fin e) (ChartInc I t e) :=
  RingEquiv.ofRingHom (fwd I t e) (bwd I t e) (fwd_bwd I t e) (bwd_fwd I t e)
end ChartIncOrd
end
end GroundTheory.Heights₂.Heights


