-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TiledBoundaries_ETSymmApply
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TiledBoundaries_ETSymmApply
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T15:04:05.15602+00:00
-- url     : https://prove2.me/theorems/f44a5dc6-b865-41f1-85e8-45c61df52315
-- title:
--   ETSymm Apply
-- statement:
--   Definitions and structural lemmas for ETSymm Apply, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/SquareIntegrability/TiledBoundaries/ETSymmApply.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TiledBoundaries_MemSpanBn
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_dim
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_nA_epsprod_norm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries
open ReciprocityTheory.ChartRestriction.G.I2 MeasureTheory Complex Module
noncomputable section
variable {E : Type} [Field E] [NumberField E]
def eT (X : PT E) (n : ℕ) : (Fin n → Vsp X.dim) ≃ₗ[ℂ] EuclideanSpace ℂ (Fin n × Idx X.dim) where
  toFun v := WithLp.toLp 2 fun p => v p.1 p.2
  invFun w := fun k => WithLp.toLp 2 fun i => w (k, i)
  map_add' v w := by ext p; simp
  map_smul' c v := by ext p; simp
  left_inv v := rfl
  right_inv w := rfl
theorem eT_apply (X : PT E) (n : ℕ) (v : Fin n → Vsp X.dim) (p : Fin n × Idx X.dim) :
    eT X n v p = v p.1 p.2 := rfl
theorem Hf_eT (X : PT E) (n : ℕ) (v w : Fin n → Vsp X.dim) :
    Hf (eT X n v) (eT X n w) = HC v w := by
  simp only [Hf, HC, eT_apply]
  rw [Fintype.sum_prod_type]
theorem card_eq (X : PT E) (n : ℕ) :
    Fintype.card (Σ _ : Fin n, Fin (2 * Fintype.card (Idx X.dim))) =
      2 * Fintype.card (Fin n × Idx X.dim) := by
  simp only [Fintype.card_sigma, Fintype.card_prod, Fintype.card_fin, Finset.sum_const,
    Finset.card_univ, smul_eq_mul]
  ring
def bT (X : PT E) (n : ℕ) :
    Basis (Fin (2 * Fintype.card (Fin n × Idx X.dim))) ℝ (EuclideanSpace ℂ (Fin n × Idx X.dim)) :=
  ((Bn X n).map ((eT X n).restrictScalars ℝ)).reindex (Fintype.equivFinOfCardEq (card_eq X n))
theorem bT_repr (X : PT E) (n : ℕ) (w : EuclideanSpace ℂ (Fin n × Idx X.dim))
    (j : Fin (2 * Fintype.card (Fin n × Idx X.dim))) :
    (bT X n).repr w j =
      (Bn X n).repr ((eT X n).symm w) ((Fintype.equivFinOfCardEq (card_eq X n)).symm j) := by
  simp [bT, Basis.map_repr]
theorem mem_latT (X : PT E) (n : ℕ) (w : EuclideanSpace ℂ (Fin n × Idx X.dim)) :
    w ∈ lat (bT X n) ↔ ∀ k, (eT X n).symm w k ∈ X.L := by
  rw [lat, Basis.mem_span_iff_repr_mem]
  simp only [bT_repr]
  constructor
  · intro h k
    rw [PT.L, lat, Basis.mem_span_iff_repr_mem]
    intro i
    have := h ((Fintype.equivFinOfCardEq (card_eq X n)) ⟨k, i⟩)
    simpa [Bn, Pi.basis_repr] using this
  · intro h j
    generalize (Fintype.equivFinOfCardEq (card_eq X n)).symm j = p
    obtain ⟨k, i⟩ := p
    have hk := h k
    rw [PT.L, lat, Basis.mem_span_iff_repr_mem] at hk
    simpa [Bn, Pi.basis_repr] using hk i
theorem single_mem (X : PT E) (n : ℕ) (k : Fin n) {l : Vsp X.dim} (hl : l ∈ X.L) :
    eT X n (Pi.single k l) ∈ lat (bT X n) := by
  rw [mem_latT, LinearEquiv.symm_apply_apply]
  intro k'
  by_cases h : k' = k
  · subst h
    simpa using hl
  · rw [Pi.single_eq_of_ne h]
    exact Submodule.zero_mem _
def YT (X : PT E) (n q : ℕ) : GT (Fin n × Idx X.dim) where
  b := bT X n
  integral := by
    intro x y hx hy
    rw [mem_latT] at hx hy
    choose m hm using fun k => X.integral _ _ (hx k) (hy k)
    refine ⟨∑ k, m k, ?_⟩
    rw [← (eT X n).apply_symm_apply x, ← (eT X n).apply_symm_apply y, Hf_eT, HC, Complex.im_sum,
      Int.cast_sum]
    exact Finset.sum_congr rfl fun k _ => hm k
  perfect := by
    intro φ
    let incl : Fin n → (X.L →+ lat (bT X n)) := fun k =>
      AddMonoidHom.mk' (fun l => ⟨eT X n (Pi.single k l), single_mem X n k l.2⟩) (fun a b => by
        apply Subtype.ext
        simp [Pi.single_add])
    choose x hxL hx using fun k => X.perfect (φ.comp (incl k))
    refine ⟨eT X n x, ?_, ?_⟩
    · rw [mem_latT, LinearEquiv.symm_apply_apply]
      exact hxL
    · intro y
      have hy := (mem_latT X n y).mp y.2
      have hdec : y = ∑ k, incl k ⟨(eT X n).symm y k, hy k⟩ := by
        apply Subtype.ext
        simp only [incl, AddMonoidHom.mk'_apply, Submodule.coe_sum]
        rw [← map_sum, Finset.univ_sum_single, LinearEquiv.apply_symm_apply]
      have hL : ((φ y : ℤ) : ℝ) = ∑ k, (((φ.comp (incl k)) ⟨(eT X n).symm y k, hy k⟩ : ℤ) : ℝ) := by
        conv_lhs => rw [hdec]
        rw [map_sum, Int.cast_sum]
        rfl
      have hR : (Hf (eT X n x) (y : EuclideanSpace ℂ (Fin n × Idx X.dim))).im =
          ∑ k, (Hf (x k) ((eT X n).symm y k)).im := by
        conv_lhs => rw [← (eT X n).apply_symm_apply (y : EuclideanSpace ℂ (Fin n × Idx X.dim))]
        rw [Hf_eT, HC, Complex.im_sum]
      rw [hL, hR]
      exact Finset.sum_congr rfl fun k _ => hx k _
  ka := fun γ => (∏ k, (X.eps ((eT X n).symm γ k) : ℂ)) ^ q
  ka_abs := fun x hx => by rw [norm_pow, nA_epsprod_norm X ((mem_latT X n x).mp hx), one_pow]
theorem sec_map (X : PT E) {q n : ℕ} {F : (Fin n → Vsp X.dim) → ℂ} (hF : F ∈ X.Sec q n) :
    (fun w => F ((eT X n).symm w)) ∈ (YT X n q).Sec q := by
  refine ⟨hF.1.comp (LinearMap.toContinuousLinearMap
    ((eT X n).symm : EuclideanSpace ℂ (Fin n × Idx X.dim) →ₗ[ℂ] (Fin n → Vsp X.dim))).differentiable,
    fun γ hγ v => ?_⟩
  have hγ' := (mem_latT X n γ).mp hγ
  show F ((eT X n).symm (v + γ)) = (∏ k, (X.eps ((eT X n).symm γ k) : ℂ)) ^ q *
    cexp (q * Real.pi * Hf v γ + q * Real.pi * Hf γ γ / 2) * F ((eT X n).symm v)
  rw [map_add, hF.2 _ hγ' _]
  have e1 : Hf v γ = HC ((eT X n).symm v) ((eT X n).symm γ) := by
    rw [← Hf_eT, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  have e2 : Hf γ γ = HC ((eT X n).symm γ) ((eT X n).symm γ) := by
    rw [← Hf_eT, LinearEquiv.apply_symm_apply]
  rw [e1, e2]
def secMap (X : PT E) (q n : ℕ) : X.Sec q n →ₗ[ℂ] (YT X n q).Sec q where
  toFun F := ⟨fun w => F.1 ((eT X n).symm w), sec_map X F.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
end
end ReciprocityTheory.ChartRestriction.G.I2.TiledBoundaries


