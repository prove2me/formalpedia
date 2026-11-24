-- Prove2me | Definitions.Def_Development_WeilBound_ThetaLifts_FrameEstimates_CoefSumA
-- name    : Development_WeilBound_ThetaLifts_FrameEstimates_CoefSumA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T03:57:03.949808+00:00
-- url     : https://prove2.me/theorems/7ed20c82-3288-4914-a2a4-36fc371cac0f
-- title:
--   Coef Sum A
-- statement:
--   Definitions and structural lemmas for Coef Sum A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/FrameEstimates/CoefSumA.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Topology Filter
open scoped ENNReal ComplexConjugate Pointwise
namespace PositivityTheory.ThKEst.CS
variable {G Γ : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [AddCommGroup Γ]
structure Dual (r : Γ →+ G) (e : Γ → G → ℂ) : Prop where
  inj : Function.Injective r
  cont : ∀ ξ, Continuous (e ξ)
  norm : ∀ ξ u, ‖e ξ u‖ = 1
  addl : ∀ ξ η u, e (ξ + η) u = e ξ u * e η u
  addr : ∀ ξ u v, e ξ (u + v) = e ξ u * e ξ v
  triv : ∀ ξ η, e ξ (r η) = 1
  sep : ∀ u, (∀ ξ, e ξ u = 1) → u ∈ r.range
  nondeg : ∀ ξ, ξ ≠ 0 → ∃ u, e ξ u ≠ 1
  cpt : ∃ K : Set G, IsCompact K ∧ ∀ u, ∃ ξ, u - r ξ ∈ K
variable {r : Γ →+ G} {e : Γ → G → ℂ}
omit [IsTopologicalAddGroup G] in
theorem Dual.ne (h : Dual r e) (ξ u) : e ξ u ≠ 0 := fun h0 => by
  have := h.norm ξ u
  rw [h0, norm_zero] at this
  exact zero_ne_one this
omit [IsTopologicalAddGroup G] in
theorem Dual.zero (h : Dual r e) (u) : e 0 u = 1 := by
  have := h.addl 0 0 u
  rw [add_zero] at this
  exact (mul_eq_left₀ (h.ne 0 u)).1 this.symm
omit [IsTopologicalAddGroup G] in
theorem Dual.conj (h : Dual r e) (ξ u) : conj (e ξ u) = e (-ξ) u := by
  have h1 : e ξ u * e (-ξ) u = 1 := by rw [← h.addl, add_neg_cancel, h.zero]
  have h2 : e ξ u * conj (e ξ u) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, h.norm]; simp
  exact mul_left_cancel₀ (h.ne ξ u) (h2.trans h1.symm)
omit [IsTopologicalAddGroup G] in
theorem Dual.per (h : Dual r e) (ξ η u) : e ξ (r η + u) = e ξ u := by
  rw [h.addr, h.triv, one_mul]
def liftC (f : G → ℂ) (hf : ∀ ξ u, f (r ξ + u) = f u) (hc : Continuous f) : C(G ⧸ r.range, ℂ) :=
  ⟨Quotient.lift f (by
    intro x y hxy
    obtain ⟨ξ, hξ⟩ : -x + y ∈ r.range := QuotientAddGroup.leftRel_apply.1 hxy
    have := hf ξ x
    rw [hξ, show -x + y + x = y by abel] at this
    exact this.symm), hc.quotient_lift _⟩
def chiC (h : Dual r e) (ξ : Γ) : C(G ⧸ r.range, ℂ) := liftC (e ξ) (h.per ξ) (h.cont ξ)
omit [IsTopologicalAddGroup G] in
theorem chiC_apply (h : Dual r e) (ξ : Γ) (u : G) : chiC h ξ (u : G ⧸ r.range) = e ξ u := rfl
omit [IsTopologicalAddGroup G] in
theorem chiC_mul (h : Dual r e) (ξ η : Γ) : chiC h ξ * chiC h η = chiC h (ξ + η) := by
  ext q
  obtain ⟨u, rfl⟩ := QuotientAddGroup.mk_surjective q
  simp only [ContinuousMap.mul_apply, chiC_apply, h.addl]
omit [IsTopologicalAddGroup G] in
theorem chiC_zero (h : Dual r e) : chiC h 0 = 1 := by
  ext q
  obtain ⟨u, rfl⟩ := QuotientAddGroup.mk_surjective q
  simp only [ContinuousMap.one_apply, chiC_apply, h.zero]
omit [IsTopologicalAddGroup G] in
theorem chiC_star (h : Dual r e) (ξ : Γ) : star (chiC h ξ) = chiC h (-ξ) := by
  ext q
  obtain ⟨u, rfl⟩ := QuotientAddGroup.mk_surjective q
  rw [ContinuousMap.star_apply, chiC_apply, chiC_apply]
  exact h.conj ξ u
def Achar (h : Dual r e) : StarSubalgebra ℂ C(G ⧸ r.range, ℂ) where
  carrier := Submodule.span ℂ (Set.range (chiC h))
  add_mem' := fun ha hb => Submodule.add_mem _ ha hb
  zero_mem' := Submodule.zero_mem _
  mul_mem' := by
    intro f g hf hg
    induction hf using Submodule.span_induction with
    | mem x hx =>
      induction hg using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨ξ, rfl⟩ := hx
        obtain ⟨η, rfl⟩ := hy
        rw [chiC_mul]
        exact Submodule.subset_span ⟨ξ + η, rfl⟩
      | zero => rw [mul_zero]; exact Submodule.zero_mem _
      | add y y' _ _ h1 h2 => rw [mul_add]; exact Submodule.add_mem _ h1 h2
      | smul c y _ h => rw [mul_smul_comm]; exact Submodule.smul_mem _ c h
    | zero => rw [zero_mul]; exact Submodule.zero_mem _
    | add x x' _ _ h1 h2 => rw [add_mul]; exact Submodule.add_mem _ h1 h2
    | smul c x _ h => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c h
  one_mem' := by
    rw [← chiC_zero h]; exact Submodule.subset_span ⟨0, rfl⟩
  algebraMap_mem' := by
    intro c
    rw [Algebra.algebraMap_eq_smul_one, ← chiC_zero h]
    exact Submodule.smul_mem _ c (Submodule.subset_span ⟨0, rfl⟩)
  star_mem' := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨ξ, rfl⟩ := hx
      rw [chiC_star]; exact Submodule.subset_span ⟨-ξ, rfl⟩
    | zero => rw [star_zero]; exact Submodule.zero_mem _
    | add x x' _ _ h1 h2 => rw [star_add]; exact Submodule.add_mem _ h1 h2
    | smul c x _ h => rw [star_smul]; exact Submodule.smul_mem _ _ h
variable [MeasurableSpace G] [BorelSpace G] [Countable Γ] {μ : Measure G} [μ.IsAddHaarMeasure] {D : Set G}
instance countable_range (r : Γ →+ G) : Countable r.range := r.rangeRestrict_surjective.countable
instance mcv (Λ : AddSubgroup G) : MeasurableConstVAdd Λ G :=
  ⟨fun c => (continuous_const.add continuous_id : Continuous fun x : G => (c : G) + x).measurable⟩
instance viv (Λ : AddSubgroup G) : VAddInvariantMeasure Λ G μ :=
  ⟨fun c s _ => measure_preimage_add μ (c : G) s⟩
end PositivityTheory.ThKEst.CS
end


