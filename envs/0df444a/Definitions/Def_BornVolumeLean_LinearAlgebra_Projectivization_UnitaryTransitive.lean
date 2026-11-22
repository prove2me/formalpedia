-- Prove2me | Definitions.Def_BornVolumeLean_LinearAlgebra_Projectivization_UnitaryTransitive
-- name    : BornVolumeLean_LinearAlgebra_Projectivization_UnitaryTransitive
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T11:56:29.022994+00:00
-- url     : https://prove2.me/theorems/de549b5d-faf7-4429-8965-1bb1a5f74fda
-- title:
--   Unitary Transitive
-- statement:
--   Definitions and structural lemmas for Unitary Transitive, from zblore's pinned Born weights as Fubini–Study volumes development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/LinearAlgebra/Projectivization/UnitaryTransitive.lean

module
public import Definitions.Def_BornVolumeLean_LinearAlgebra_Projectivization_Unitary
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Matrix.Basis
set_option autoImplicit false
@[expose] public section
@[expose] public section
open Matrix
open scoped LinearAlgebra.Projectivization
namespace Matrix.UnitaryGroup
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
noncomputable def unitaryOfONB (b : OrthonormalBasis ι ℂ
      (EuclideanSpace ℂ ι)) : Matrix.unitaryGroup ι ℂ :=
  ⟨(EuclideanSpace.basisFun ι ℂ).toBasis.toMatrix b.toBasis,
   (EuclideanSpace.basisFun ι ℂ).toMatrix_orthonormalBasis_mem_unitary b⟩
lemma unitaryOfONB_apply_single (b : OrthonormalBasis ι ℂ
      (EuclideanSpace ℂ ι)) (j : ι) :
    (Matrix.toEuclideanLin (unitaryOfONB b).val) (EuclideanSpace.single j (1 : ℂ))
      = b j := by
  ext i
  show ((Matrix.toEuclideanLin (unitaryOfONB b).val)
          (EuclideanSpace.single j (1 : ℂ))).ofLp i = (b j).ofLp i
  -- toEuclideanLin M v reduces to (M *ᵥ v.ofLp) componentwise
  show (((unitaryOfONB b).val) *ᵥ (EuclideanSpace.single j (1 : ℂ)).ofLp) i
        = (b j).ofLp i
  -- (single j 1).ofLp = Pi.single j 1
  have h_sng : ((EuclideanSpace.single j (1 : ℂ)).ofLp : ι → ℂ)
                = Pi.single j (1 : ℂ) :=
    WithLp.ofLp_toLp _ _
  rw [h_sng, Matrix.mulVec_single]
  simp only [MulOpposite.op_one, one_smul, Matrix.col_apply]
  -- Goal: ((unitaryOfONB b).val) i j = (b j).ofLp i
  show (EuclideanSpace.basisFun ι ℂ).toBasis.toMatrix b.toBasis i j
       = (b j).ofLp i
  rw [Module.Basis.toMatrix_apply,
      (EuclideanSpace.basisFun ι ℂ).coe_toBasis_repr_apply,
      EuclideanSpace.basisFun_repr]
  rfl
lemma exists_unitary_single_eq (i₀ : ι) (v : EuclideanSpace ℂ ι) (hv : ‖v‖ = 1) :
    ∃ M : Matrix.unitaryGroup ι ℂ,
      (Matrix.toEuclideanLin M.val) (EuclideanSpace.single i₀ (1 : ℂ)) = v := by
  -- Build a single-element "orthonormal subset" {v} indexed via s = {i₀} ⊂ ι.
  let s : Set ι := {i₀}
  let f : ι → EuclideanSpace ℂ ι := fun i => if i = i₀ then v else 0
  have hf_orth : Orthonormal ℂ (s.domRestrict f) := by
    rw [orthonormal_iff_ite]
    rintro ⟨i, (hi : i = i₀)⟩ ⟨j, (hj : j = i₀)⟩
    subst hi; subst hj
    simp only [Set.domRestrict_apply, ite_true, f]
    rw [inner_self_eq_norm_sq_to_K, hv]
    simp
  have card_eq : Module.finrank ℂ (EuclideanSpace ℂ ι) = Fintype.card ι :=
    finrank_euclideanSpace
  obtain ⟨b_v, hb_v⟩ :=
    hf_orth.exists_orthonormalBasis_extension_of_card_eq card_eq
  have hb_v_i₀ : b_v i₀ = v := by
    have := hb_v i₀ (by simp [s])
    simpa [f] using this
  refine ⟨unitaryOfONB b_v, ?_⟩
  rw [unitaryOfONB_apply_single, hb_v_i₀]
lemma exists_unitary_e_zero_eq [Nonempty ι] (v : EuclideanSpace ℂ ι) (hv : ‖v‖ = 1) :
    ∃ M : Matrix.unitaryGroup ι ℂ,
      (Matrix.toEuclideanLin M.val) (EuclideanSpace.single (Classical.arbitrary ι) (1 : ℂ)) = v :=
  exists_unitary_single_eq (Classical.arbitrary ι) v hv
lemma exists_unitary_map_unit [Nonempty ι]
    (v w : EuclideanSpace ℂ ι) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) :
    ∃ U : Matrix.unitaryGroup ι ℂ,
      (Matrix.toEuclideanLin U.val) v = w := by
  obtain ⟨M_v, hM_v⟩ := exists_unitary_e_zero_eq v hv
  obtain ⟨M_w, hM_w⟩ := exists_unitary_e_zero_eq w hw
  refine ⟨M_w * M_v⁻¹, ?_⟩
  -- Rewrite v = M_v · e_0 (from hM_v), then collapse the matrix product.
  rw [← hM_v]
  -- Goal: toEuclideanLin (M_w * M_v⁻¹).val (toEuclideanLin M_v.val e_0) = w
  -- Compose via toLpLin_mul_same:
  --   toEuclideanLin A (toEuclideanLin B v) = toEuclideanLin (A * B) v
  -- Specifically: toEuclideanLin (M_w * M_v⁻¹).val (toEuclideanLin M_v.val e_0)
  --             = toEuclideanLin ((M_w * M_v⁻¹).val * M_v.val) e_0
  have h_collapse :
      Matrix.toEuclideanLin (M_w * M_v⁻¹).val
          ((Matrix.toEuclideanLin M_v.val) (EuclideanSpace.single (Classical.arbitrary ι) (1 : ℂ)))
        = Matrix.toEuclideanLin ((M_w * M_v⁻¹).val * M_v.val)
            (EuclideanSpace.single (Classical.arbitrary ι) (1 : ℂ)) := by
    rw [Matrix.toLpLin_mul_same]; rfl
  rw [h_collapse]
  -- (M_w * M_v⁻¹).val * M_v.val = (M_w * M_v⁻¹ * M_v).val = M_w.val
  -- (by group axioms: M_v⁻¹ * M_v = 1)
  have h_simp : (M_w * M_v⁻¹).val * M_v.val = M_w.val := by
    rw [← Matrix.UnitaryGroup.mul_val, mul_assoc, inv_mul_cancel,
        mul_one]
  rw [h_simp]
  exact hM_w
lemma toEuclideanLin_unitary_ne_zero
    (U : Matrix.unitaryGroup ι ℂ)
    {v : EuclideanSpace ℂ ι} (hv : v ≠ 0) :
    (Matrix.toEuclideanLin U.val) v ≠ 0 := by
  intro h
  apply hv
  exact (toEuclideanLinearEquiv U).injective (h.trans (LinearEquiv.map_zero _).symm)
lemma exists_unitary_mapping_nonzero [Nonempty ι]
    {v w : EuclideanSpace ℂ ι} (hv : v ≠ 0) (hw : w ≠ 0) :
    ∃ (U : Matrix.unitaryGroup ι ℂ) (c : ℂ), c ≠ 0 ∧
      (Matrix.toEuclideanLin U.val) v = c • w := by
  -- Normalise both vectors.
  have hv_norm : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  have hw_norm : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
  have hv_norm_cx : ((‖v‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hv_norm
  have hw_norm_cx : ((‖w‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hw_norm
  have hw_norm_inv_cx : ((‖w‖⁻¹ : ℝ) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_inv]
    exact inv_ne_zero hw_norm_cx
  set v' : EuclideanSpace ℂ ι := ((‖v‖⁻¹ : ℝ) : ℂ) • v with v'_def
  set w' : EuclideanSpace ℂ ι := ((‖w‖⁻¹ : ℝ) : ℂ) • w with w'_def
  have hv' : ‖v'‖ = 1 := by
    rw [v'_def, norm_smul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr (norm_pos_iff.mpr hv)), inv_mul_cancel₀ hv_norm]
  have hw' : ‖w'‖ = 1 := by
    rw [w'_def, norm_smul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr (norm_pos_iff.mpr hw)), inv_mul_cancel₀ hw_norm]
  obtain ⟨U, hU⟩ := exists_unitary_map_unit v' w' hv' hw'
  refine ⟨U, ((‖v‖ : ℂ) * (‖w‖⁻¹ : ℂ)), ?_, ?_⟩
  · -- c ≠ 0
    exact mul_ne_zero hv_norm_cx (inv_ne_zero hw_norm_cx)
  · -- (toEuclideanLin U.val) v = c • w
    have h_v_recover : v = ((‖v‖ : ℝ) : ℂ) • v' := by
      rw [v'_def, ← smul_assoc, smul_eq_mul, Complex.ofReal_inv,
          mul_inv_cancel₀ hv_norm_cx, one_smul]
    calc (Matrix.toEuclideanLin U.val) v
        = (Matrix.toEuclideanLin U.val) (((‖v‖ : ℝ) : ℂ) • v') := by
            conv_lhs => rw [h_v_recover]
      _ = ((‖v‖ : ℝ) : ℂ) • (Matrix.toEuclideanLin U.val) v' := by
            rw [map_smul]
      _ = ((‖v‖ : ℝ) : ℂ) • w' := by rw [hU]
      _ = ((‖v‖ : ℝ) : ℂ) • (((‖w‖⁻¹ : ℝ) : ℂ) • w) := rfl
      _ = (((‖v‖ : ℝ) : ℂ) * ((‖w‖⁻¹ : ℝ) : ℂ)) • w := by rw [smul_smul]
      _ = ((‖v‖ : ℂ) * (‖w‖⁻¹ : ℂ)) • w := by rw [Complex.ofReal_inv]
lemma smul_mk_eq_mk
    (U : Matrix.unitaryGroup ι ℂ)
    (v : EuclideanSpace ℂ ι) (hv : v ≠ 0) :
    U • Projectivization.mk ℂ v hv
      = Projectivization.mk ℂ ((Matrix.toEuclideanLin U.val) v)
          (toEuclideanLin_unitary_ne_zero U hv) :=
  rfl
instance instIsPretransitive_projectivization [Nonempty ι] :
    MulAction.IsPretransitive (Matrix.unitaryGroup ι ℂ)
      (ℙ ℂ (EuclideanSpace ℂ ι)) where
  exists_smul_eq p q := by
    obtain ⟨U, c, hc, hUv⟩ :=
      exists_unitary_mapping_nonzero p.rep_nonzero q.rep_nonzero
    refine ⟨U, ?_⟩
    -- Goal: U • p = q. Rewrite both sides via mk_rep.
    conv_lhs => rw [← p.mk_rep]
    conv_rhs => rw [← q.mk_rep]
    rw [smul_mk_eq_mk]
    -- Goal: mk ℂ ((toEuclideanLin U.val) p.rep) (...) = mk ℂ q.rep q.rep_nonzero
    -- Use hUv : (toEuclideanLin U.val) p.rep = c • q.rep, then mk_eq_mk_iff' with a := c.
    -- The `rw` form trips the motive check (the `mk`'s non-vanishing proof is
    -- proof-irrelevant but Lean can't abstract); apply `.mpr` directly.
    exact (Projectivization.mk_eq_mk_iff' ℂ _ _
            (hUv ▸ toEuclideanLin_unitary_ne_zero U p.rep_nonzero)
            q.rep_nonzero).mpr ⟨c, hUv.symm⟩
end Matrix.UnitaryGroup


