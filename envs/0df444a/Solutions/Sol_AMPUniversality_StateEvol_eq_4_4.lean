-- Prove2me | solution 1 for AMPUniversality.StateEvol.eq_4_4
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T07:37:55.922953+00:00
-- url     : https://prove2.me/submissions/35c0ae9a-9bca-4e96-ac86-0ec2687ecf8e

import Definitions.Def_AMPUniversality_StateEvol_SETwo

set_option autoImplicit false

open MeasureTheory ProbabilityTheory


namespace AMPUniversality.StateEvol

/-- duplication map -/
noncomputable def dupL (q : ℕ) : EuclideanSpace ℝ (Fin q) →L[ℝ] EuclideanSpace ℝ (Fin q ⊕ Fin q) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => WithLp.toLp 2 (Sum.elim (fun r => x r) (fun r => x r))
      map_add' := by intro x y; ext r; cases r <;> simp
      map_smul' := by intro c x; ext r; cases r <;> simp }

lemma dupL_apply {q : ℕ} (x : EuclideanSpace ℝ (Fin q)) (r : Fin q ⊕ Fin q) :
    dupL q x r = Sum.elim (fun r => x r) (fun r => x r) r := by
  simp [dupL]

lemma dupL_adjoint {q : ℕ} (u : EuclideanSpace ℝ (Fin q ⊕ Fin q)) :
    (dupL q).adjoint u = WithLp.toLp 2 (fun r => u (Sum.inl r) + u (Sum.inr r)) := by
  apply ext_inner_left ℝ
  intro x
  rw [ContinuousLinearMap.adjoint_inner_right]
  simp [PiLp.inner_apply, dupL_apply, Fintype.sum_sum_type]
  rw [← Finset.sum_add_distrib]; simp [add_mul]


lemma psd_dup {q : ℕ} {S : Matrix (Fin q) (Fin q) ℝ} (hS : S.PosSemidef) :
    (Matrix.fromBlocks S S S S).PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨?_, ?_⟩
  · have := hS.1.eq
    show Matrix.conjTranspose (Matrix.fromBlocks S S S S) = _
    rw [Matrix.fromBlocks_conjTranspose]
    rw [Matrix.conjTranspose_eq_transpose_of_trivial] at this
    simp [Matrix.conjTranspose_eq_transpose_of_trivial, this]
  · intro x
    have hx : x = Sum.elim (fun r => x (Sum.inl r)) (fun r => x (Sum.inr r)) := by
      ext r; cases r <;> simp
    set a : Fin q → ℝ := fun r => x (Sum.inl r)
    set b : Fin q → ℝ := fun r => x (Sum.inr r)
    rw [hx, Matrix.fromBlocks_mulVec]
    have h2 := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hS).2 (a + b)
    simp only [star_trivial] at h2 ⊢
    simp only [dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Pi.add_apply, Matrix.mulVec_add, Sum.elim_comp_inl, Sum.elim_comp_inr] at h2 ⊢
    convert h2 using 1
    simp only [Pi.add_apply, mul_add, add_mul, Finset.sum_add_distrib]
    ring

lemma mvg_dup {q : ℕ} {S : Matrix (Fin q) (Fin q) ℝ} (hS : S.PosSemidef) :
    multivariateGaussian 0 (Matrix.fromBlocks S S S S) =
      (multivariateGaussian 0 S).map (dupL q) := by
  have hS4 := psd_dup hS
  have : IsGaussian ((multivariateGaussian (0 : EuclideanSpace ℝ (Fin q)) S).map (dupL q)) := inferInstance
  apply IsGaussian.ext
  · simp only [id_eq]
    rw [integral_id_multivariateGaussian, ContinuousLinearMap.integral_id_map IsGaussian.integrable_id,
      integral_id_multivariateGaussian]
    ext r; cases r <;> simp [dupL_apply]
  · ext u v
    rw [covarianceBilin_map IsGaussian.memLp_two_id, covarianceBilin_multivariateGaussian hS4,
      covarianceBilin_multivariateGaussian hS, dupL_adjoint, dupL_adjoint]
    simp only [dotProduct, Matrix.mulVec, Fintype.sum_sum_type, Matrix.fromBlocks_apply₁₁,
      Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂]
    simp only [PiLp.add_apply, Finset.sum_add_distrib, mul_add, add_mul]
    ring

instance gaussianVec_prob {q : ℕ} (S : Matrix (Fin q) (Fin q) ℝ) :
    IsProbabilityMeasure (gaussianVec S) := by
  unfold gaussianVec
  exact Measure.isProbabilityMeasure_map (by fun_prop)

/-- duplication on coordinates -/
def dupF {q : ℕ} (x : Fin q → ℝ) : (Fin q ⊕ Fin q) → ℝ := Sum.elim x x

lemma dupF_measEmb (q : ℕ) : MeasurableEmbedding (dupF (q := q)) := by
  have h1 : Measurable (dupF (q := q)) := by
    refine measurable_pi_lambda _ (fun r => ?_)
    cases r <;> simp [dupF] <;> exact measurable_pi_apply _
  have h2 : MeasurableSet (Set.range (dupF (q := q))) := by
    have : Set.range (dupF (q := q)) = ⋂ r : Fin q, {z : (Fin q ⊕ Fin q) → ℝ | z (Sum.inl r) = z (Sum.inr r)} := by
      ext z
      simp only [Set.mem_range, Set.mem_iInter, Set.mem_setOf_eq]
      constructor
      · rintro ⟨x, rfl⟩ r; simp [dupF]
      · intro h
        refine ⟨fun r => z (Sum.inl r), ?_⟩
        ext r; cases r <;> simp [dupF, h]
    rw [this]
    exact MeasurableSet.iInter (fun r => measurableSet_eq_fun (measurable_pi_apply _) (measurable_pi_apply _))
  exact MeasurableEmbedding.of_measurable_inverse h1 h2
    (g := fun z r => z (Sum.inl r)) (measurable_pi_lambda _ (fun r => measurable_pi_apply _))
    (by intro x; ext r; simp [dupF])

lemma gaussianPair_dup {q : ℕ} {S : Matrix (Fin q) (Fin q) ℝ} (hS : S.PosSemidef) :
    gaussianPair (Matrix.fromBlocks S S S S) = (gaussianVec S).map dupF := by
  unfold gaussianPair gaussianVec
  rw [mvg_dup hS, Measure.map_map (by fun_prop) (by fun_prop), Measure.map_map (dupF_measEmb q).measurable (by fun_prop)]
  congr 1

lemma integral_gaussianPair_dup {q : ℕ} {S : Matrix (Fin q) (Fin q) ℝ} (hS : S.PosSemidef)
    {β : Type*} [MeasurableSpace β] (ν : Measure β) [SFinite ν]
    (F : ((Fin q ⊕ Fin q) → ℝ) × β → ℝ) :
    ∫ zy, F zy ∂((gaussianPair (Matrix.fromBlocks S S S S)).prod ν) =
      ∫ xy, F (dupF xy.1, xy.2) ∂((gaussianVec S).prod ν) := by
  rw [gaussianPair_dup hS]
  have : ν = ν.map id := (Measure.map_id).symm
  conv_lhs => rw [this]
  rw [Measure.map_prod_map _ _ (dupF_measEmb q).measurable measurable_id]
  rw [((dupF_measEmb q).prodMap MeasurableEmbedding.id).integral_map]
  rfl

lemma gram_psd {X : Type*} [MeasurableSpace X] (μ : Measure X) {q : ℕ} (f : Fin q → X → ℝ)
    (hf : ∀ r s, Integrable (fun x => f r x * f s x) μ) :
    (Matrix.of fun r s : Fin q => ∫ x, f r x * f s x ∂μ).PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨?_, ?_⟩
  · show Matrix.conjTranspose _ = _
    rw [Matrix.conjTranspose_eq_transpose_of_trivial]
    ext r s
    simp [mul_comm]
  · intro v
    have e1 : ∀ x, (∑ r, v r * f r x) ^ 2 = ∑ r, ∑ s, (v r * v s) * (f r x * f s x) := by
      intro x
      rw [sq, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl (fun r _ => Finset.sum_congr rfl (fun s _ => by ring))
    have key : dotProduct (star v) (Matrix.mulVec (Matrix.of fun r s : Fin q => ∫ x, f r x * f s x ∂μ) v) =
        ∫ x, (∑ r, v r * f r x) ^ 2 ∂μ := by
      simp_rw [e1]
      rw [integral_finsetSum]
      · simp only [star_trivial, dotProduct, Matrix.mulVec, Matrix.of_apply, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun r _ => ?_)
        rw [integral_finsetSum]
        · refine Finset.sum_congr rfl (fun s _ => ?_)
          rw [integral_const_mul]
          ring
        · intro s _
          exact (hf r s).const_mul _
      · intro r _
        exact integrable_finsetSum _ (fun s _ => (hf r s).const_mul _)
    rw [key]
    exact integral_nonneg (fun x => sq_nonneg _)

lemma int_monomial {q : ℕ} (S : Matrix (Fin q) (Fin q) ℝ) (m : Fin q → ℕ) :
    Integrable (fun x : Fin q → ℝ => ∏ s, x s ^ m s) (gaussianVec S) := by
  unfold gaussianVec
  have hmeas : Measurable (fun z : EuclideanSpace ℝ (Fin q) => fun r => z r) := by fun_prop
  rw [integrable_map_measure (by exact (by fun_prop : Continuous fun x : Fin q → ℝ => ∏ s, x s ^ m s).aestronglyMeasurable) hmeas.aemeasurable]
  have hn : Integrable (fun z : EuclideanSpace ℝ (Fin q) => ‖z‖ ^ (∑ s, m s)) (multivariateGaussian 0 S) := by
    by_cases h0 : (∑ s, m s) = 0
    · rw [h0]; simp
    · exact (IsGaussian.memLp_id _ (∑ s, m s : ℕ) (by simp)).integrable_norm_pow h0
  refine hn.mono' (by fun_prop : Continuous fun z : EuclideanSpace ℝ (Fin q) => ∏ s, (fun r => z r) s ^ m s).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun z => ?_))
  simp only [Function.comp, norm_prod, norm_pow, Real.norm_eq_abs]
  rw [← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_le_prod (fun _ _ => by positivity) (fun s _ => ?_)
  exact pow_le_pow_left₀ (abs_nonneg _) (by simpa using PiLp.norm_apply_le z s) _

lemma mixture_prob {h : ℕ} {μ : Measure (EuclideanSpace ℝ (Fin h))} (hμ : IsGaussianMixture μ) :
    IsProbabilityMeasure μ := by
  obtain ⟨l, w, mean, cov, hw, hc, rfl⟩ := hμ
  constructor
  rw [Measure.finset_sum_apply]
  simp only [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.coe_finset_sum, hw]
  simp

lemma int_gg {Ω : Type*} [MeasurableSpace Ω] {q h k d : ℕ} (M : Model Ω q h k d)
    (hbd : ∀ y a t r m, |M.gc y a t r m| ≤ M.C)
    (hgm : ∀ a t r m, Measurable (fun y => M.gc y a t r m))
    (hprob : ∀ a, IsProbabilityMeasure (M.Pa a))
    (S : Matrix (Fin q) (Fin q) ℝ) (a : Fin k) (t : ℕ) (r s : Fin q) :
    Integrable (fun zy : (Fin q → ℝ) × EuclideanSpace ℝ (Fin h) =>
      M.gvec zy.1 zy.2 a t r * M.gvec zy.1 zy.2 a t s) ((gaussianVec S).prod (M.Pa a)) := by
  haveI := hprob a
  unfold Model.gvec polyEval
  simp only [Finset.sum_mul_sum]
  refine integrable_finsetSum _ (fun m _ => integrable_finsetSum _ (fun m' _ => ?_))
  have hI : Integrable (fun zy : (Fin q → ℝ) × EuclideanSpace ℝ (Fin h) =>
      (∏ u, zy.1 u ^ ((m u : ℕ) + (m' u : ℕ))) * (M.gc zy.2 a t r m * M.gc zy.2 a t s m')) ((gaussianVec S).prod (M.Pa a)) := by
    have h2 : Integrable (fun y : EuclideanSpace ℝ (Fin h) => M.gc y a t r m * M.gc y a t s m') (M.Pa a) := by
      refine Integrable.of_bound (C := M.C * M.C) ?_ ?_
      · exact ((hgm a t r m).mul (hgm a t s m')).aestronglyMeasurable
      · refine Filter.Eventually.of_forall (fun y => ?_)
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul (hbd _ _ _ _ _) (hbd _ _ _ _ _) (abs_nonneg _) ((abs_nonneg _).trans (hbd y a t r m))
    exact (int_monomial S (fun u => (m u : ℕ) + (m' u : ℕ))).mul_prod h2
  refine hI.congr (Filter.Eventually.of_forall (fun zy => ?_))
  simp only [pow_add, Finset.prod_mul_distrib]
  ring

lemma fromBlocks_dup {q : ℕ} (S : Matrix (Fin q) (Fin q) ℝ) :
    Matrix.fromBlocks S S S S = Matrix.of fun r u => S (Sum.elim id id r) (Sum.elim id id u) := by
  ext r u; cases r <;> cases u <;> simp

lemma seHatStep_psd {Ω : Type*} [MeasurableSpace Ω] {q h k d : ℕ} (M : Model Ω q h k d)
    (hbd : ∀ y a t r m, |M.gc y a t r m| ≤ M.C)
    (hgm : ∀ a t r m, Measurable (fun y => M.gc y a t r m))
    (hprob : ∀ a, IsProbabilityMeasure (M.Pa a))
    (t : ℕ) (cov : Fin k → Matrix (Fin q) (Fin q) ℝ) (a : Fin k) :
    (M.seHatStep t cov a).PosSemidef := by
  have := gram_psd ((gaussianVec (cov a)).prod (M.Pa a))
    (fun r (zy : (Fin q → ℝ) × EuclideanSpace ℝ (Fin h)) => M.gvec zy.1 zy.2 a t r)
    (fun r s => int_gg M hbd hgm hprob (cov a) a t r s)
  exact this

lemma seCovStep_psd {Ω : Type*} [MeasurableSpace Ω] {q h k d : ℕ} (M : Model Ω q h k d)
    (hW : ∀ a b, 0 ≤ M.W a b) (hca : ∀ a, 0 < M.ca a)
    (hat : Fin k → Matrix (Fin q) (Fin q) ℝ) (hh : ∀ b, (hat b).PosSemidef) (a : Fin k) :
    (M.seCovStep hat a).PosSemidef := by
  have : M.seCovStep hat a = ∑ b, (M.ca b * M.W a b) • hat b := by
    ext r s
    simp [Model.seCovStep, Matrix.sum_apply]
  rw [this]
  exact Matrix.posSemidef_sum _ (fun b _ => (hh b).smul (mul_nonneg (hca b).le (hW a b)))

lemma seState_psd {Ω : Type*} [MeasurableSpace Ω] {q h k d : ℕ} (M : Model Ω q h k d)
    (hbd : ∀ y a t r m, |M.gc y a t r m| ≤ M.C)
    (hgm : ∀ a t r m, Measurable (fun y => M.gc y a t r m))
    (hprob : ∀ a, IsProbabilityMeasure (M.Pa a))
    (hW : ∀ a b, 0 ≤ M.W a b) (hca : ∀ a, 0 < M.ca a) (hhat0 : ∀ a, (M.hat0 a).PosSemidef) :
    ∀ t, (∀ a, ((M.seState t).1 a).PosSemidef) ∧ (∀ a, ((M.seState t).2 a).PosSemidef) := by
  intro t
  induction t with
  | zero =>
    refine ⟨fun a => ?_, hhat0⟩
    show (0 : Matrix (Fin q) (Fin q) ℝ).PosSemidef
    exact Matrix.PosSemidef.zero
  | succ t ih =>
    have h1 : ∀ a, (M.seCovStep (M.seState t).2 a).PosSemidef :=
      seCovStep_psd M hW hca _ ih.2
    refine ⟨fun a => h1 a, fun a => ?_⟩
    exact seHatStep_psd M hbd hgm hprob _ _ a

lemma seTwoHat_diag {Ω : Type*} [MeasurableSpace Ω] {q h k d : ℕ} (M : Model Ω q h k d)
    (hbd : ∀ y a t r m, |M.gc y a t r m| ≤ M.C)
    (hgm : ∀ a t r m, Measurable (fun y => M.gc y a t r m))
    (hprob : ∀ a, IsProbabilityMeasure (M.Pa a))
    (hW : ∀ a b, 0 ≤ M.W a b) (hca : ∀ a, 0 < M.ca a) (hhat0 : ∀ a, (M.hat0 a).PosSemidef) :
    ∀ t a, M.seTwoHat t t a =
      Matrix.fromBlocks (M.seHat t a) (M.seHat t a) (M.seHat t a) (M.seHat t a) := by
  intro t
  induction t with
  | zero =>
    intro a
    simp [Model.seTwoHat, Model.seHat, Model.seState]
  | succ t ih =>
    intro a
    have hpsd := seState_psd M hbd hgm hprob hW hca hhat0 t
    have hcov : (fun b r u => ∑ c, M.ca c * M.W b c * M.seTwoHat t t c r u) =
        fun b => Matrix.fromBlocks (M.seCovStep (M.seHat t) b) (M.seCovStep (M.seHat t) b)
          (M.seCovStep (M.seHat t) b) (M.seCovStep (M.seHat t) b) := by
      funext b
      ext r u
      simp only [ih]
      cases r <;> cases u <;> simp [Model.seCovStep]
    have hSigma : (M.seCovStep (M.seHat t) a).PosSemidef := seCovStep_psd M hW hca _ hpsd.2 a
    rw [Model.seTwoHat]
    rw [hcov]
    have hseHat : M.seHat (t+1) = M.seHatStep (t+1) (M.seCovStep (M.seHat t)) := rfl
    rw [hseHat, fromBlocks_dup]
    ext r u
    simp only [Model.seTwoHatStep, Matrix.of_apply]
    rw [integral_gaussianPair_dup hSigma]
    simp only [Model.seHatStep]
    congr 1
    funext xy
    have e : ∀ r' : Fin q ⊕ Fin q, M.pairG (t+1) (t+1) a (dupF xy.1) xy.2 r' =
        M.gvec xy.1 xy.2 a (t+1) (Sum.elim id id r') := by
      intro r'; cases r' <;> rfl
    rw [e, e]

theorem eq44_core {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {q h k d : ℕ}
    (M : Model Ω q h k d) (hconv : IsConverging P M)
    (t : ℕ) (ht : 1 ≤ t) (a : Fin k) :
    (M.seTwo t t a).PosSemidef ∧
    M.seTwo t t a = Matrix.fromBlocks (M.se t a) (M.se t a)
      (M.se t a) (M.se t a) := by
  obtain ⟨hreg, hWs, hW, hvar, hhat, hmix, hca, hY1, hY2, hYm, hgc, hgm, hlim⟩ := hconv
  have hprob : ∀ a, IsProbabilityMeasure (M.Pa a) := fun a => mixture_prob (hmix a)
  have hbd : ∀ y a t r m, |M.gc y a t r m| ≤ M.C := hgc
  have hca' : ∀ a, 0 < M.ca a := fun a => (hca a).1
  obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
  have hpsd := seState_psd M hbd hgm hprob hW hca' hhat (t' + 1)
  have hdiag := seTwoHat_diag M hbd hgm hprob hW hca' hhat
  have heq : M.seTwo (t'+1) (t'+1) a = Matrix.fromBlocks (M.se (t'+1) a) (M.se (t'+1) a)
      (M.se (t'+1) a) (M.se (t'+1) a) := by
    show (fun r u => ∑ b, M.ca b * M.W a b * M.seTwoHat t' t' b r u) = _
    funext r u
    simp only [hdiag]
    cases r <;> cases u <;> simp [Model.se, Model.seState, Model.seCovStep, Model.seHat]
  exact ⟨heq ▸ psd_dup (hpsd.1 a), heq⟩

end AMPUniversality.StateEvol

open AMPUniversality.StateEvol


theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {q h k d : ℕ}
    (M : Model Ω q h k d) (hconv : IsConverging P M)
    (t : ℕ) (ht : 1 ≤ t) (a : Fin k) :
    (M.seTwo t t a).PosSemidef ∧
    M.seTwo t t a = Matrix.fromBlocks (M.se t a) (M.se t a)
      (M.se t a) (M.se t a) := by
  exact eq44_core P M hconv t ht a
