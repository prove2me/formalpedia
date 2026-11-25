-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsBasisSpanEqOfCommensurable
-- name    : Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsBasisSpanEqOfCommensurable
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T17:13:40.100197+00:00
-- url     : https://prove2.me/theorems/1380115a-f7ce-4b54-abd7-55c533d69124
-- title:
--   Exists Basis Span Eq Of Commensurable
-- statement:
--   Definitions and structural lemmas for Exists Basis Span Eq Of Commensurable, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsBasisSpanEqOfCommensurable.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_FlatMemLatIffStdLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_NsmulApplyMemOfMemTensorLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_IntegrableOnFundamentalDomainOfContinuous
import Theorems.Thm_GlobalTheory_TensorLat_HC_flat_symm
import Theorems.Thm_GlobalTheory_TensorLat_exists_nsmul_commensurable
import Theorems.Thm_GlobalTheory_TensorLat_flat_symm_eq_eT_symm
import Theorems.Thm_GlobalTheory_TensorLat_im_HC_int
import Theorems.Thm_GlobalTheory_TensorLat_mem_stdLat_iff_herm
import Theorems.Thm_GlobalTheory_TensorLat_mem_tensorLat_stdLat
import Theorems.Thm_GlobalTheory_TensorLat_norm_tensorEps
import Theorems.Thm_GlobalTheory_TensorLat_stdLat_fg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_actE_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_dim
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.I2.actE_apply


set_option autoImplicit false
namespace GlobalTheory.TensorLat
open NumberField Complex ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.FD MeasureTheory
open ReciprocityTheory.GeometryOfNumbersTheory (stdLat)
theorem exists_basis_span_eq_of_commensurable {V κ : Type} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] [Fintype κ] (b : Module.Basis κ ℝ V)
    (L : Submodule ℤ V) {M : ℕ} (hM : 1 ≤ M)
    (h1 : ∀ x ∈ Submodule.span ℤ (Set.range b), M • x ∈ L)
    (h2 : ∀ x ∈ L, M • x ∈ Submodule.span ℤ (Set.range b)) :
    ∃ b' : Module.Basis κ ℝ V, Submodule.span ℤ (Set.range b') = L := by
  have hM0 : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have h2' : ∀ x ∈ L, (M : ℝ) • x ∈ Submodule.span ℤ (Set.range b) := by
    intro x hx
    rw [Nat.cast_smul_eq_nsmul]
    exact h2 x hx
  let f : L → Submodule.span ℤ (Set.range b) := fun x => ⟨(M : ℝ) • (x : V), h2' x x.2⟩
  have hfc : Continuous f := (continuous_const.smul continuous_subtype_val).subtype_mk _
  have hfi : Function.Injective f := by
    intro x y h
    have h' : (M : ℝ) • (x : V) = (M : ℝ) • (y : V) := congrArg Subtype.val h
    exact Subtype.ext (smul_right_injective V hM0 h')
  have : DiscreteTopology L := DiscreteTopology.of_continuous_injective hfc hfi
  have : IsZLattice ℝ L := by
    refine ⟨?_⟩
    rw [eq_top_iff, ← b.span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have hm : M • b i ∈ L := h1 (b i) (Submodule.subset_span ⟨i, rfl⟩)
    have hbi : b i = (M : ℝ)⁻¹ • (M • b i) := by
      rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀ hM0, one_smul]
    rw [SetLike.mem_coe, hbi]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hm)
  have := ZLattice.module_free ℝ L
  have := ZLattice.module_finite ℝ L
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ L) = Fintype.card κ := by
    rw [← Module.finrank_eq_card_chooseBasisIndex, ZLattice.rank ℝ L,
      Module.finrank_eq_card_basis b]
  exact ⟨((Module.Free.chooseBasis ℤ L).reindex (Fintype.equivOfCardEq hcard)).ofZLatticeBasis ℝ L,
    Module.Basis.ofZLatticeBasis_span ℝ L _⟩
variable {E : Type} [Field E] [NumberField E] {dim : (E →+* ℂ) → ℕ} {n : ℕ}
variable [IsCMField E]
variable {X : PT E} {Λ' : Submodule (𝓞 E) (Fin n → E)}
theorem exists_basis_tensorLat (hfg : Λ'.FG)
    (hint : ∀ x ∈ Λ', ∀ y ∈ Λ', IsIntegral ℤ (herm 1 x y))
    (hdual : ∀ x, (∀ y ∈ Λ', IsIntegral ℤ (herm 1 x y)) → x ∈ Λ') :
    ∃ b : Module.Basis (Fin (2 * Fintype.card (Fin n × Idx X.dim))) ℝ
        (EuclideanSpace ℂ (Fin n × Idx X.dim)),
      ∀ γ, flat γ ∈ lat b ↔ γ ∈ tensorLat X Λ' := by
  obtain ⟨M, hM, hM1, hM2⟩ := exists_nsmul_commensurable (X := X) hfg hint hdual
  let L : Submodule ℤ (EuclideanSpace ℂ (Fin n × Idx X.dim)) :=
    (tensorLat X Λ').map
      (((flat (n := n) (ι := Idx X.dim)).toLinearEquiv.restrictScalars ℤ : _ ≃ₗ[ℤ] _) :
        (Fin n → Vsp X.dim) →ₗ[ℤ] EuclideanSpace ℂ (Fin n × Idx X.dim))
  have hmemL : ∀ γ, flat γ ∈ L ↔ γ ∈ tensorLat X Λ' := by
    intro γ
    constructor
    · rintro ⟨γ', hγ', h⟩
      have hγγ : γ' = γ := flat.injective h
      rw [← hγγ]
      exact hγ'
    · intro h
      exact ⟨γ, h, rfl⟩
  have hlatT : ∀ w, w ∈ lat (TiledBoundaries.bT X n) ↔ ∀ k, flat.symm w k ∈ X.L := by
    intro w
    rw [TiledBoundaries.mem_latT, flat_symm_eq_eT_symm]
  have h1 : ∀ x ∈ Submodule.span ℤ (Set.range (TiledBoundaries.bT X n)), M • x ∈ L := by
    intro x hx
    have h := hM1 _ ((hlatT x).1 hx)
    rw [← ContinuousLinearEquiv.apply_symm_apply flat x, ← map_nsmul]
    exact (hmemL _).2 h
  have h2 : ∀ x ∈ L, M • x ∈ Submodule.span ℤ (Set.range (TiledBoundaries.bT X n)) := by
    rintro x ⟨γ, hγ, rfl⟩
    refine (hlatT _).2 fun k => ?_
    have hfl : (((flat (n := n) (ι := Idx X.dim)).toLinearEquiv.restrictScalars ℤ : _ ≃ₗ[ℤ] _) :
        (Fin n → Vsp X.dim) →ₗ[ℤ] EuclideanSpace ℂ (Fin n × Idx X.dim)) γ = flat γ := rfl
    rw [hfl, ← map_nsmul, ContinuousLinearEquiv.symm_apply_apply]
    exact hM2 γ hγ k
  obtain ⟨b', hb'⟩ := exists_basis_span_eq_of_commensurable (TiledBoundaries.bT X n) L hM h1 h2
  refine ⟨b', fun γ => ?_⟩
  show flat γ ∈ Submodule.span ℤ (Set.range b') ↔ _
  rw [hb', hmemL]
theorem exists_tensorTorus (hfg : Λ'.FG)
    (hint : ∀ x ∈ Λ', ∀ y ∈ Λ', IsIntegral ℤ (herm 1 x y))
    (hdual : ∀ x, (∀ y ∈ Λ', IsIntegral ℤ (herm 1 x y)) → x ∈ Λ') (w₀ : 𝓞 E) :
    ∃ Y : GT (Fin n × Idx X.dim), (∀ γ, flat γ ∈ lat Y.b ↔ γ ∈ tensorLat X Λ') ∧
      ∀ γ, Y.ka (flat γ) = tensorEps w₀ γ := by
  obtain ⟨b, hb⟩ := exists_basis_tensorLat (X := X) hfg hint hdual
  have hmem : ∀ x, x ∈ lat b ↔ flat.symm x ∈ tensorLat X Λ' := fun x => by
    rw [← hb, ContinuousLinearEquiv.apply_symm_apply]
  let g : tensorLat X Λ' →+ lat b :=
    { toFun := fun γ => ⟨flat (γ : Fin n → Vsp X.dim), (hb γ).2 γ.2⟩
      map_zero' := by
        ext
        simp
      map_add' := fun x y => by
        ext
        simp }
  refine ⟨⟨b, ?_, ?_, fun x => tensorEps w₀ (flat.symm x), ?_⟩, hb, ?_⟩
  · intro x y hx hy
    rw [← HC_flat_symm]
    exact im_HC_int hfg hint hdual ((hmem x).1 hx) ((hmem y).1 hy)
  · intro φ
    obtain ⟨γ0, hγ0, hφ⟩ := exists_im_HC_eq hfg hint hdual (φ.comp g)
    refine ⟨flat γ0, (hb γ0).2 hγ0, fun y => ?_⟩
    have hy : flat.symm (y : EuclideanSpace ℂ (Fin n × Idx X.dim)) ∈ tensorLat X Λ' :=
      (hmem y).1 y.2
    have hyy : g ⟨flat.symm (y : EuclideanSpace ℂ (Fin n × Idx X.dim)), hy⟩ = y := by
      ext
      simp [g]
    have h := hφ ⟨flat.symm (y : EuclideanSpace ℂ (Fin n × Idx X.dim)), hy⟩
    rw [AddMonoidHom.comp_apply, hyy] at h
    rw [h]
    show (HC γ0 (flat.symm (y : EuclideanSpace ℂ (Fin n × Idx X.dim)))).im = _
    rw [← Hf_flat, ContinuousLinearEquiv.apply_symm_apply]
  · intro x _
    exact norm_tensorEps w₀ _
  · intro γ
    show tensorEps w₀ (flat.symm (flat γ)) = _
    rw [ContinuousLinearEquiv.symm_apply_apply]
example (X : PT E) (w₀ : 𝓞 E) :
    ∃ Y : GT (Fin n × Idx X.dim), (∀ γ, flat γ ∈ lat Y.b ↔ ∀ k, γ k ∈ X.L) ∧
      ∀ γ, Y.ka (flat γ) = tensorEps w₀ γ := by
  obtain ⟨Y, h1, h2⟩ := exists_tensorTorus (X := X) (n := n) stdLat_fg
    (fun _ hx => mem_stdLat_iff_herm.1 hx) (fun _ hx => mem_stdLat_iff_herm.2 hx) w₀
  exact ⟨Y, fun γ => (h1 γ).trans mem_tensorLat_stdLat, h2⟩
end GlobalTheory.TensorLat


