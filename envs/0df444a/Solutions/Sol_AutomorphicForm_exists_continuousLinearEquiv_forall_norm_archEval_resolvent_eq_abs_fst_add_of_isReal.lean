-- Prove2me | solution 1 for AutomorphicForm.exists_continuousLinearEquiv_forall_norm_archEval_resolvent_eq_abs_fst_add_of_isReal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/089d7ab3-8ccc-5db5-8ca1-b12c5c85909d

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_AutomorphicForm_RowIsometryInvariance
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification
import Theorems.Thm_AutomorphicForm_archEval_archIdent_sigmaTensor_eq_mapRingHom_and_ringEquiv_mixedSpace_fst_eq_and_snd_eq_or_eq_conj
import Theorems.Thm_NumberField_InfiniteAdeleRing_isHomeomorph_ringEquiv_mixedSpace
import Theorems.Thm_AutomorphicForm_sigmaTensor_twistedResolvent_sub_mul_eq_one_sub_norm_smul_and_twistedResolvent_sigmaTensor_sub_mul_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_continuousLinearEquiv_forall_norm_archEval_resolvent_eq_abs_fst_add_of_isReal

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions

attribute [local instance] AutomorphicForm.centralizerBorel AutomorphicForm.twistedCentralizerBorel

open LanglandsTunnell.CubicInduction (diagUnits2)

open scoped Classical

namespace CoordSplit

open NumberField
open scoped Classical

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

noncomputable def coordR (w : {w : InfinitePlace L // w.IsReal}) (z : L ⊗[K] InfiniteAdeleRing K) : ℝ :=
  (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L z)).1 w

theorem coordR_eq (w : {w : InfinitePlace L // w.IsReal}) (z : L ⊗[K] InfiniteAdeleRing K) :
    coordR K L w z = InfinitePlace.Completion.extensionEmbeddingOfIsReal w.2 (AutomorphicForm.archIdent K L z w.1) := rfl

noncomputable def coordRHom (w : {w : InfinitePlace L // w.IsReal}) : (L ⊗[K] InfiniteAdeleRing K) →+* ℝ :=
  ((Pi.evalRingHom _ w).comp (RingHom.fst _ _)).comp
    ((NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L).toRingHom.comp (AutomorphicForm.archIdentEquiv K L).toRingHom)

theorem coordRHom_apply (w : {w : InfinitePlace L // w.IsReal}) (z : L ⊗[K] InfiniteAdeleRing K) :
    coordRHom K L w z = coordR K L w z := rfl

theorem norm_archEval_archIdent_eq_abs_coordR (w : InfinitePlace L) (hw : w.IsReal) (z : L ⊗[K] InfiniteAdeleRing K) :
    ‖NumberField.AdelicLevel.archEval L w (AutomorphicForm.archIdent K L z)‖ = |coordR K L ⟨w, hw⟩ z| := by
  rw [coordR_eq, ← Real.norm_eq_abs,
    (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero (map_zero _)]
  rfl

theorem coordR_sigmaTensor (g : L ≃ₐ[K] L) (w : InfinitePlace L) (hw : w.IsReal) (y : L ⊗[K] InfiniteAdeleRing K) :
    coordR K L ⟨w, hw⟩ (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) g y) =
      coordR K L ⟨w.comap (g : L →+* L), hw.comap _⟩ y :=
  (AutomorphicForm.archEval_archIdent_sigmaTensor_eq_mapRingHom_and_ringEquiv_mixedSpace_fst_eq_and_snd_eq_or_eq_conj
    K L g w).2.2.2.1 (w.comap (g : L →+* L)) hw (hw.comap _) rfl y

theorem coordR_iterate_sigmaTensor_symm (σ : L ≃ₐ[K] L) (w : InfinitePlace L) (hw : w.IsReal)
    (k : ℕ) (y : L ⊗[K] InfiniteAdeleRing K) :
    coordR K L ⟨w, hw⟩ ((AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ.symm)^[k] y) =
      coordR K L ⟨w.comap ((σ.symm ^ k : L ≃ₐ[K] L) : L →+* L), hw.comap _⟩ y := by

  have hmul : ∀ (g h : L ≃ₐ[K] L) (z : L ⊗[K] InfiniteAdeleRing K),
      AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) (g * h) z =
        AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) g (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) h z) := by
    intro g h z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [AutomorphicForm.sigmaTensor, Algebra.TensorProduct.map_tmul, AlgEquiv.mul_apply]
    | add x y hx hy => simp only [map_add, hx, hy]

  have hiter : ∀ (k : ℕ) (z : L ⊗[K] InfiniteAdeleRing K),
      (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ.symm)^[k] z =
        AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) (σ.symm ^ k) z := by
    intro k
    induction k with
    | zero =>
      intro z
      simp only [Function.iterate_zero, id_eq, pow_zero]
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul a b => simp [AutomorphicForm.sigmaTensor, Algebra.TensorProduct.map_tmul]
      | add x y hx hy => simp only [map_add, ← hx, ← hy]
    | succ k ih =>
      intro z
      rw [Function.iterate_succ_apply', ih, pow_succ', hmul]
  rw [hiter, coordR_sigmaTensor]

theorem resolvent_unique (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    [FiniteDimensional K L] [IsGalois K L]
    (r : L ⊗[K] InfiniteAdeleRing K) (c : (InfiniteAdeleRing K)ˣ)
    (hc : (c : InfiniteAdeleRing K) = 1 - Algebra.norm (InfiniteAdeleRing K) r)
    (M : (L ⊗[K] InfiniteAdeleRing K) →ₗ[InfiniteAdeleRing K] (L ⊗[K] InfiniteAdeleRing K))
    (hM1 : ∀ y, AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ (M y) - r * M y = (c : InfiniteAdeleRing K) • y)
    (hM2 : ∀ y, M (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ y - r * y) = (c : InfiniteAdeleRing K) • y)
    (y : L ⊗[K] InfiniteAdeleRing K) :
    M y = ∑ j ∈ Finset.range (Module.finrank K L),
          (∏ i ∈ Finset.range j, (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ.symm)^[i + 1] r) *
            (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ.symm)^[j + 1] y := by
  obtain ⟨hC1, -⟩ :=
    AutomorphicForm.sigmaTensor_twistedResolvent_sub_mul_eq_one_sub_norm_smul_and_twistedResolvent_sigmaTensor_sub_mul_eq
      K L σ hgen (InfiniteAdeleRing K) r y
  set M₀y := ∑ j ∈ Finset.range (Module.finrank K L),
          (∏ i ∈ Finset.range j, (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ.symm)^[i + 1] r) *
            (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ.symm)^[j + 1] y with hM₀y

  have hsmul : ∀ (a : InfiniteAdeleRing K) (z : L ⊗[K] InfiniteAdeleRing K),
      a • z = algebraMap (InfiniteAdeleRing K) (L ⊗[K] InfiniteAdeleRing K) a * z := fun a z =>
    AutomorphicForm.rightActions_smul_eq K L (InfiniteAdeleRing K) a z

  have hσlin : ∀ (a : InfiniteAdeleRing K) (z : L ⊗[K] InfiniteAdeleRing K),
      AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ (a • z) =
        a • AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ z := by
    intro a z
    rw [hsmul, hsmul, map_mul]
    congr 1
    simp [AutomorphicForm.sigmaTensor, Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.map_tmul]
  have hT : AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ M₀y - r * M₀y = (c : InfiniteAdeleRing K) • y := by
    rw [hM₀y, hC1, ← hc, hsmul]

  have hy : AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ (((c⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) • M₀y) -
      r * (((c⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) • M₀y) = y := by
    rw [hσlin, show r * ((((c⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K)) • M₀y) =
        (((c⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K)) • (r * M₀y) by rw [hsmul, hsmul, mul_left_comm],
      ← smul_sub, hT, smul_smul, Units.inv_mul, one_smul]
  calc M y = M (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ (((c⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) • M₀y) -
      r * (((c⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) • M₀y)) := by rw [hy]
    _ = (c : InfiniteAdeleRing K) • (((c⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) • M₀y) := hM2 _
    _ = M₀y := by rw [smul_smul, Units.mul_inv, one_smul]

theorem exists_coordinates [MeasurableSpace (L ⊗[K] InfiniteAdeleRing K)] [BorelSpace (L ⊗[K] InfiniteAdeleRing K)]
    (lam : Measure (L ⊗[K] InfiniteAdeleRing K)) [lam.IsAddHaarMeasure]
    (w₀ : {w : InfinitePlace L // w.IsReal}) :
    ∃ (d : ℕ) (e : mixedEmbedding.mixedSpace L ≃L[ℝ] (ℝ × EuclideanSpace ℝ (Fin d))) (κ : NNReal), κ ≠ 0 ∧
      Measure.map (fun y : L ⊗[K] InfiniteAdeleRing K =>
          e (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L y))) lam =
        κ • ((volume : Measure ℝ).prod (volume : Measure (EuclideanSpace ℝ (Fin d)))) ∧
      (∀ x : mixedEmbedding.mixedSpace L, (e x).1 = x.1 w₀) ∧
      ∀ w : {w : InfinitePlace L // w.IsReal}, w ≠ w₀ →
        ∃ π : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ, ∀ x : mixedEmbedding.mixedSpace L, π (e x).2 = x.1 w := by
  classical

  let V : Type := ({v : {w : InfinitePlace L // w.IsReal} // v ≠ w₀} → ℝ) × ({w : InfinitePlace L // w.IsComplex} → ℂ)
  let d : ℕ := Module.finrank ℝ V
  have hd : Module.finrank ℝ V = Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) := by
    rw [finrank_euclideanSpace_fin]
  let f : V ≃L[ℝ] EuclideanSpace ℝ (Fin d) := ContinuousLinearEquiv.ofFinrankEq hd

  let L₁ : mixedEmbedding.mixedSpace L ≃ₗ[ℝ] ℝ × V :=
    { toFun := fun x => (x.1 w₀, (fun v => x.1 v.1, x.2))
      map_add' := by intro x y; rfl
      map_smul' := by intro a x; rfl
      invFun := fun p => (fun w => if h : w = w₀ then p.1 else p.2.1 ⟨w, h⟩, p.2.2)
      left_inv := by
        intro x
        refine Prod.ext ?_ rfl
        funext w
        by_cases h : w = w₀
        · subst h; simp
        · simp [h]
      right_inv := by
        rintro ⟨a, g, z⟩
        refine Prod.ext (by simp) (Prod.ext ?_ rfl)
        funext v
        have hv : (v.1 : {w : InfinitePlace L // w.IsReal}) ≠ w₀ := v.2
        simp [hv] }
  let e₁ : mixedEmbedding.mixedSpace L ≃L[ℝ] ℝ × V := L₁.toContinuousLinearEquiv
  let e : mixedEmbedding.mixedSpace L ≃L[ℝ] ℝ × EuclideanSpace ℝ (Fin d) :=
    e₁.trans ((ContinuousLinearEquiv.refl ℝ ℝ).prodCongr f)
  have he1 : ∀ x : mixedEmbedding.mixedSpace L, (e x).1 = x.1 w₀ := fun x => rfl
  have he2 : ∀ x : mixedEmbedding.mixedSpace L, (e x).2 = f ((fun v => x.1 v.1, x.2) : V) := fun x => rfl

  haveI := AutomorphicForm.isTopologicalRing_tensor K L (InfiniteAdeleRing K)
  let ιA : (L ⊗[K] InfiniteAdeleRing K) ≃+ mixedEmbedding.mixedSpace L :=
    ((AutomorphicForm.archIdentEquiv K L).trans (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L)).toAddEquiv
  have hιc : Continuous ιA :=
    (NumberField.InfiniteAdeleRing.isHomeomorph_ringEquiv_mixedSpace L).continuous.comp
      (AutomorphicForm.archIdentHomeomorph K L).continuous
  have hιsc : Continuous ιA.symm := by
    have h1 : Continuous (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L).symm :=
      (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L).toEquiv.continuous_symm_iff.mpr
        (NumberField.InfiniteAdeleRing.isHomeomorph_ringEquiv_mixedSpace L).isOpenMap
    exact (AutomorphicForm.archIdentHomeomorph K L).symm.continuous.comp h1
  let ιE : (L ⊗[K] InfiniteAdeleRing K) ≃+ (ℝ × EuclideanSpace ℝ (Fin d)) := ιA.trans e.toLinearEquiv.toAddEquiv
  have hιEc : Continuous ιE := e.continuous.comp hιc
  have hιEsc : Continuous ιE.symm := hιsc.comp e.symm.continuous
  haveI : IsTopologicalAddGroup (L ⊗[K] InfiniteAdeleRing K) := inferInstance
  haveI hH : (Measure.map ιE lam).IsAddHaarMeasure := ιE.isAddHaarMeasure_map lam hιEc hιEsc
  set κ := (Measure.map ιE lam).addHaarScalarFactor ((volume : Measure ℝ).prod (volume : Measure (EuclideanSpace ℝ (Fin d)))) with hκ
  have hmap : Measure.map ιE lam = κ • ((volume : Measure ℝ).prod (volume : Measure (EuclideanSpace ℝ (Fin d)))) :=
    Measure.isAddLeftInvariant_eq_smul _ _
  have hκ0 : κ ≠ 0 :=
    (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _).ne'
  refine ⟨d, e, κ, hκ0, ?_, he1, ?_⟩
  · exact hmap
  · intro w hw
    refine ⟨(ContinuousLinearMap.proj (R := ℝ) (⟨w, hw⟩ : {v : {w : InfinitePlace L // w.IsReal} // v ≠ w₀})).comp
        ((ContinuousLinearMap.fst ℝ _ _).comp (f.symm : EuclideanSpace ℝ (Fin d) →L[ℝ] V)), fun x => ?_⟩
    simp only [he2, ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.symm_apply_apply]
    rfl

end CoordSplit

open CoordSplit in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) (hdeg : (Module.finrank K L).Prime)
    [MeasurableSpace (L ⊗[K] InfiniteAdeleRing K)] [BorelSpace (L ⊗[K] InfiniteAdeleRing K)]
    (lam : Measure (L ⊗[K] InfiniteAdeleRing K)) [lam.IsAddHaarMeasure]
    (w' : NumberField.InfinitePlace L) (hw' : w'.IsReal) :
    ∃ (d : ℕ) (e : NumberField.mixedEmbedding.mixedSpace L ≃L[ℝ] (ℝ × EuclideanSpace ℝ (Fin d))) (κ : NNReal), κ ≠ 0 ∧
      Measure.map (fun y : L ⊗[K] InfiniteAdeleRing K => e (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L (y)))) lam =
        κ • ((volume : Measure ℝ).prod (volume : Measure (EuclideanSpace ℝ (Fin d)))) ∧
      ∃ Λ : NumberField.mixedEmbedding.mixedSpace L → (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ), ContDiff ℝ (⊤ : ℕ∞) Λ ∧
        ∀ (r : L ⊗[K] InfiniteAdeleRing K) (c : (InfiniteAdeleRing K)ˣ),
          (c : InfiniteAdeleRing K) = 1 - Algebra.norm (InfiniteAdeleRing K) r →
        ∀ M : (L ⊗[K] InfiniteAdeleRing K) →ₗ[InfiniteAdeleRing K] (L ⊗[K] InfiniteAdeleRing K),
          (∀ y, AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ (M y) - r * M y = (c : InfiniteAdeleRing K) • y) →
          (∀ y, M (AutomorphicForm.sigmaTensor K L (InfiniteAdeleRing K) σ y - r * y) = (c : InfiniteAdeleRing K) • y) →
        ∀ y : L ⊗[K] InfiniteAdeleRing K,
          ‖NumberField.AdelicLevel.archEval L w' (AutomorphicForm.archIdent K L (M y))‖ =
            |(e (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L (y)))).1 + Λ (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L (r))) (e (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L (y)))).2| := by
  classical

  let wk : ℕ → {w : InfinitePlace L // w.IsReal} := fun k =>
    ⟨w'.comap ((σ.symm ^ k : L ≃ₐ[K] L) : L →+* L), hw'.comap _⟩
  have hwk_smul : ∀ k, ((wk k) : InfinitePlace L) = (σ ^ k) • w' := by
    intro k
    show w'.comap ((σ.symm ^ k : L ≃ₐ[K] L) : L →+* L) = (σ ^ k) • w'
    rw [InfinitePlace.smul_eq_comap]
    congr 2
    change σ⁻¹ ^ k = (σ ^ k)⁻¹
    exact inv_pow σ k

  have horder : orderOf σ = Module.finrank K L := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hgen, IsGalois.card_aut_eq_finrank]
  have hstab : MulAction.stabilizer (L ≃ₐ[K] L) w' = ⊥ := (hw'.isUnramified (k := K)).stabilizer_eq_bot
  have hneq : ∀ k, 2 ≤ k → k ≤ Module.finrank K L → wk k ≠ wk 1 := by
    intro k hk2 hkl heq
    have h1 : (σ ^ k) • w' = (σ ^ 1) • w' := by
      rw [← hwk_smul, ← hwk_smul, heq]
    have h2 : σ ^ (k - 1) ∈ MulAction.stabilizer (L ≃ₐ[K] L) w' := by
      rw [MulAction.mem_stabilizer_iff]
      have : σ ^ (k - 1) = (σ ^ 1)⁻¹ * σ ^ k := by
        rw [pow_one, ← zpow_natCast, ← zpow_natCast, ← zpow_neg_one, ← zpow_add]
        congr 1
        push_cast
        omega
      rw [this, mul_smul, h1, ← mul_smul, inv_mul_cancel, one_smul]
    rw [hstab, Subgroup.mem_bot] at h2
    have h3 : σ ^ (k - 1) ≠ 1 := pow_ne_one_of_lt_orderOf (by omega) (by rw [horder]; omega)
    exact h3 h2

  obtain ⟨d, e, κ, hκ, hmap, he1, hπ⟩ := CoordSplit.exists_coordinates K L lam (wk 1)

  have hπ' : ∀ k, ∃ π : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ, (2 ≤ k → k ≤ Module.finrank K L →
      ∀ x : mixedEmbedding.mixedSpace L, π (e x).2 = x.1 (wk k)) := by
    intro k
    by_cases hk : 2 ≤ k ∧ k ≤ Module.finrank K L
    · obtain ⟨π, hπk⟩ := hπ (wk k) (hneq k hk.1 hk.2)
      exact ⟨π, fun _ _ => hπk⟩
    · exact ⟨0, fun h1 h2 => (hk ⟨h1, h2⟩).elim⟩
  choose π hπk using hπ'

  let Λ : mixedEmbedding.mixedSpace L → (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) := fun ρ =>
    ∑ j ∈ Finset.range (Module.finrank K L - 1), (∏ i ∈ Finset.range (j + 1), ρ.1 (wk (i + 1))) • π (j + 2)
  have hΛ : ContDiff ℝ (⊤ : ℕ∞) Λ := by
    apply ContDiff.sum
    intro j _
    have hprod : ContDiff ℝ (⊤ : ℕ∞) (fun x : mixedEmbedding.mixedSpace L => ∏ i ∈ Finset.range (j + 1), x.1 (wk (i + 1))) :=
      contDiff_prod (fun i _ => by
        have : (fun x : mixedEmbedding.mixedSpace L => x.1 (wk (i + 1))) =
            ⇑((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : {w : InfinitePlace L // w.IsReal} => ℝ) (wk (i + 1))).comp
              (ContinuousLinearMap.fst ℝ ({w : InfinitePlace L // w.IsReal} → ℝ) ({w : InfinitePlace L // w.IsComplex} → ℂ))) := rfl
        rw [this]
        exact ContinuousLinearMap.contDiff _)
    exact hprod.smul contDiff_const
  refine ⟨d, e, κ, hκ, hmap, Λ, hΛ, ?_⟩
  intro r c hc M hM1 hM2 y

  rw [CoordSplit.resolvent_unique K L σ hgen r c hc M hM1 hM2 y,
    CoordSplit.norm_archEval_archIdent_eq_abs_coordR K L w' hw']
  congr 1

  rw [← CoordSplit.coordRHom_apply, map_sum]
  simp only [map_mul, map_prod, CoordSplit.coordRHom_apply, CoordSplit.coordR_iterate_sigmaTensor_symm]

  have hℓ : 1 ≤ Module.finrank K L := Module.finrank_pos
  rw [show Module.finrank K L = (Module.finrank K L - 1) + 1 by omega, Finset.sum_range_succ']
  simp only [Finset.range_zero, Finset.prod_empty, one_mul, zero_add]

  have h0 : CoordSplit.coordR K L ⟨w'.comap ((σ.symm ^ 1 : L ≃ₐ[K] L) : L →+* L), hw'.comap _⟩ y =
      (e (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace L (AutomorphicForm.archIdent K L y))).1 := by
    rw [he1]; rfl
  rw [h0, add_comm]
  congr 1

  simp only [Λ, ContinuousLinearMap.coe_sum', ContinuousLinearMap.coe_smul', Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : j < Module.finrank K L - 1 := Finset.mem_range.mp hj
  rw [hπk (j + 2) (by omega) (by omega)]
  rfl

end S_AutomorphicForm_exists_continuousLinearEquiv_forall_norm_archEval_resolvent_eq_abs_fst_add_of_isReal
end P2MW
export P2MW.S_AutomorphicForm_exists_continuousLinearEquiv_forall_norm_archEval_resolvent_eq_abs_fst_add_of_isReal (solution)
