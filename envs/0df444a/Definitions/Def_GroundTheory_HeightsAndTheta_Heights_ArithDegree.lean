-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithDegree
-- name    : GroundTheory_HeightsAndTheta_Heights_ArithDegree
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T03:51:26.986244+00:00
-- url     : https://prove2.me/theorems/e8472747-d4ce-49a9-bac2-f771cc6485e1
-- title:
--   Arith Degree
-- statement:
--   Definitions and structural lemmas for Arith Degree, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithDegree.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HermitianTensor
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HermitianMetric_integers_inner_66e5d940cc4d

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.Heights₂.Heights
open NumberField NumberField.ComplexEmbedding TensorProduct ComplexAt Matrix
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
instance (σ : K →+* ℂ) : Module.IsTorsionFree (𝓞 K) (ComplexAt σ) := by
  refine ⟨fun a ha z w hzw ↦ ?_⟩
  have ha0 : a ≠ 0 := ha.ne_zero
  have h1 : σ (a : K) ≠ 0 := by
    rw [map_ne_zero]; exact_mod_cast ha0
  simp only [smul_def] at hzw
  exact mul_left_cancel₀ (M₀ := ℂ) h1 hzw
example (σ : K →+* ℂ) : Module.Flat (𝓞 K) (ComplexAt σ) := inferInstance
variable {E : Type*} [AddCommGroup E] [Module (𝓞 K) E] [Module.Finite (𝓞 K) E]
  [Module.Projective (𝓞 K) E]
example : Module.IsTorsionFree (𝓞 K) E := inferInstance
omit [Module.Projective (𝓞 K) E] in

theorem finite_quotient_span {ι : Type*} [Fintype ι] {s : ι → E} (hs : LinearIndependent (𝓞 K) s)
    (hcard : Fintype.card ι = Module.finrank (𝓞 K) E) :
    Finite (E ⧸ Submodule.span (𝓞 K) (Set.range s)) := by
  set N := Submodule.span (𝓞 K) (Set.range s)
  have hN : Module.rank (𝓞 K) N = Fintype.card ι := by
    classical
    rw [rank_span hs, Cardinal.mk_fintype, Set.card_range_of_injective hs.injective]
  have hE : Module.rank (𝓞 K) E = Module.finrank (𝓞 K) E := (Module.finrank_eq_rank _ _).symm
  have hQ := rank_quotient_add_rank_of_isDomain N
  rw [hN, hE, hcard] at hQ
  have hlt : Module.rank (𝓞 K) (E ⧸ N) < Cardinal.aleph0 := by
    refine lt_of_le_of_lt (le_self_add.trans hQ.le) Cardinal.natCast_lt_aleph0
  obtain ⟨m, hm⟩ := Cardinal.lt_aleph0.mp hlt
  rw [hm] at hQ
  norm_cast at hQ
  have hQ0 : Module.rank (𝓞 K) (E ⧸ N) = 0 := by rw [hm]; norm_cast; omega
  have htors : ∀ x : E ⧸ N, ∃ n : ℤ, n ≠ 0 ∧ n • x = 0 := by
    intro x
    obtain ⟨a, ha, hax⟩ := (rank_eq_zero_iff.mp hQ0) x
    have hI : Ideal.span ({a} : Set (𝓞 K)) ≠ ⊥ := by
      rwa [Ne, Ideal.span_singleton_eq_bot]
    have hmem := Ideal.absNorm_mem (Ideal.span ({a} : Set (𝓞 K)))
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp hmem
    refine ⟨(Ideal.absNorm (Ideal.span ({a} : Set (𝓞 K))) : ℤ), ?_, ?_⟩
    · exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr hI
    · rw [← Int.cast_smul_eq_zsmul (𝓞 K), Int.cast_natCast, ← hb, mul_smul, hax, smul_zero]
  have : Module.Finite ℤ (E ⧸ N) := Module.Finite.trans (𝓞 K) (E ⧸ N)
  refine Module.finite_of_fg_torsion _ fun x ↦ ?_
  obtain ⟨n, hn, hnx⟩ := htors x
  exact ⟨⟨n, mem_nonZeroDivisors_of_ne_zero hn⟩, hnx⟩
def fibreVec (h : HermitianMetric K E) (σ : K →+* ℂ) (e : E) : FibreSpace h σ :=
  FibreSpace.equiv h σ ((1 : ComplexAt σ) ⊗ₜ e)
section FibreVec
variable (h : HermitianMetric K E) (σ : K →+* ℂ)
theorem fibreVec_add (e f : E) : fibreVec h σ (e + f) = fibreVec h σ e + fibreVec h σ f := by
  simp only [fibreVec, tmul_add, map_add]
theorem fibreVec_smul (a : 𝓞 K) (e : E) :
    fibreVec h σ (a • e) = (σ (a : K)) • fibreVec h σ e := by
  simp only [fibreVec]
  rw [← map_smul, ← TensorProduct.smul_tmul, smul_tmul', smul_def, complex_smul_def]
theorem fibreVec_sum {ι : Type*} (S : Finset ι) (c : ι → 𝓞 K) (s : ι → E) :
    fibreVec h σ (∑ i ∈ S, c i • s i) = ∑ i ∈ S, (σ (c i : K)) • fibreVec h σ (s i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [fibreVec]
  | insert a S ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, fibreVec_add, fibreVec_smul, ih]
theorem linearIndependent_fibreVec {ι : Type*} {s : ι → E} (hs : LinearIndependent (𝓞 K) s) :
    LinearIndependent ℂ (fun i ↦ fibreVec h σ (s i)) := by
  set N := Submodule.span (𝓞 K) (Set.range s)
  let b : Module.Basis ι (𝓞 K) N := Module.Basis.span hs
  let bC := Algebra.TensorProduct.basis (ComplexAt σ) b
  let f : ComplexAt σ ⊗[𝓞 K] N →ₗ[ComplexAt σ] ComplexAt σ ⊗[𝓞 K] E :=
    AlgebraTensorModule.lTensor (ComplexAt σ) (ComplexAt σ) N.subtype
  have hf : Function.Injective f :=
    Module.Flat.lTensor_preserves_injective_linearMap N.subtype N.injective_subtype
  have h1 : LinearIndependent (ComplexAt σ) (fun i ↦ f (bC i)) :=
    bC.linearIndependent.map' f (LinearMap.ker_eq_bot.mpr hf)
  have h2 : (fun i ↦ f (bC i)) = fun i ↦ (1 : ComplexAt σ) ⊗ₜ[𝓞 K] s i := by
    funext i
    simp only [bC, f, b, Algebra.TensorProduct.basis_apply, AlgebraTensorModule.lTensor_tmul,
      Submodule.subtype_apply]
    rw [Module.Basis.span_apply]
  rw [h2] at h1
  have h3 : LinearIndependent ℂ (fun i ↦ (1 : ComplexAt σ) ⊗ₜ[𝓞 K] s i) :=
    h1.restrict_scalars (R := ℂ) (fun a c hac ↦ by
      simp only [complex_smul_def, mul_one] at hac; exact hac)
  exact h3.map' (FibreSpace.equiv h σ).toLinearMap (FibreSpace.equiv h σ).ker
end FibreVec
section Gram
theorem gram_comb {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {ι : Type*}
    [Fintype ι] (v : ι → V) (B : Matrix ι ι ℂ) :
    gram ℂ (fun j ↦ ∑ i, B i j • v i) = Bᴴ * gram ℂ v * B := by
  ext j k
  simp only [gram_apply, sum_inner, inner_sum, inner_smul_left, inner_smul_right, mul_apply,
    conjTranspose_apply, Finset.sum_mul, Finset.mul_sum, RCLike.star_def]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun l _ ↦ ?_
  ring
end Gram
def gramDet (h : HermitianMetric K E) (σ : K →+* ℂ) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : ι → E) : ℝ :=
  (det (gram ℂ fun i ↦ fibreVec h σ (s i))).re
section GramDet
variable (h : HermitianMetric K E) (σ : K →+* ℂ) {ι : Type*} [Fintype ι] [DecidableEq ι]
theorem gramDet_pos {s : ι → E} (hs : LinearIndependent (𝓞 K) s) : 0 < gramDet h σ s := by
  have := (posDef_gram_of_linearIndependent (linearIndependent_fibreVec h σ hs)).det_pos
  exact (RCLike.pos_iff.mp this).1
theorem gramDet_comb (A : Matrix ι ι (𝓞 K)) (s : ι → E) :
    gramDet h σ (fun j ↦ ∑ i, A i j • s i) = ‖σ (A.det : K)‖ ^ 2 * gramDet h σ s := by
  set τ : 𝓞 K →+* ℂ := σ.comp (algebraMap (𝓞 K) K)
  have hv : (fun j ↦ fibreVec h σ (∑ i, A i j • s i)) =
      fun j ↦ ∑ i, (τ.mapMatrix A) i j • fibreVec h σ (s i) := by
    funext j; rw [fibreVec_sum]; rfl
  have hz : τ A.det = σ (A.det : K) := rfl
  simp only [gramDet]
  rw [hv, gram_comb, det_mul, det_mul, det_conjTranspose, ← RingHom.map_det, hz,
    mul_comm _ (σ (A.det : K)), ← mul_assoc, RCLike.star_def, Complex.mul_conj,
    Complex.re_ofReal_mul, Complex.normSq_eq_norm_sq]
theorem gramDet_reindex {ι' : Type*} [Fintype ι'] [DecidableEq ι'] (e : ι' ≃ ι) (s : ι → E) :
    gramDet h σ (s ∘ e) = gramDet h σ s := by
  simp only [gramDet]
  have : (gram ℂ fun i ↦ fibreVec h σ ((s ∘ e) i)) =
      (gram ℂ fun i ↦ fibreVec h σ (s i)).submatrix e e := by
    ext i j; rfl
  rw [this, det_submatrix_equiv_self]
end GramDet
def degreeWith (h : HermitianMetric K E) {ι : Type*} [Fintype ι] [DecidableEq ι] (s : ι → E) : ℝ :=
  Real.log (Nat.card (E ⧸ Submodule.span (𝓞 K) (Set.range s))) -
    (1 / 2) * ∑ σ : K →+* ℂ, Real.log (gramDet h σ s)
section Index
omit [NumberField K] [Module.Finite (𝓞 K) E] [Module.Projective (𝓞 K) E] in

theorem card_quotient_range_comp {M : Type*} [AddCommGroup M] [Module (𝓞 K) M]
    (Φ : M →ₗ[𝓞 K] E) (hΦ : Function.Injective Φ) (g : M →ₗ[𝓞 K] M) :
    Nat.card (E ⧸ LinearMap.range (Φ ∘ₗ g)) =
      Nat.card (M ⧸ LinearMap.range g) * Nat.card (E ⧸ LinearMap.range Φ) := by
  rw [← Submodule.card_quotient_mul_card_quotient (LinearMap.range Φ) (LinearMap.range (Φ ∘ₗ g))
    (LinearMap.range_comp_le_range _ _)]
  congr 1
  have hker : LinearMap.ker ((LinearMap.range (Φ ∘ₗ g)).mkQ ∘ₗ Φ) = LinearMap.range g := by
    ext x
    simp only [LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero, LinearMap.mem_range]
    constructor
    · rintro ⟨y, hy⟩; exact ⟨y, hΦ hy⟩
    · rintro ⟨y, rfl⟩; exact ⟨y, rfl⟩
  rw [← LinearMap.range_comp, ← hker]
  exact Nat.card_congr (LinearMap.quotKerEquivRange _).toEquiv.symm
theorem card_quotient_mulVecLin {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι (𝓞 K))
    (hA : A.det ≠ 0) :
    Nat.card ((ι → 𝓞 K) ⧸ LinearMap.range A.mulVecLin) = (Algebra.norm ℤ A.det).natAbs := by
  have hinj : Function.Injective A.mulVecLin := by
    intro x y hxy
    by_contra hne
    refine hA (Matrix.exists_mulVec_eq_zero_iff.mp ⟨x - y, sub_ne_zero.mpr hne, ?_⟩)
    rw [mulVec_sub]
    exact sub_eq_zero.mpr hxy
  set N := LinearMap.range A.mulVecLin
  let e : (ι → 𝓞 K) ≃ₗ[ℤ] N.restrictScalars ℤ :=
    (LinearEquiv.ofInjective A.mulVecLin hinj).restrictScalars ℤ
  have h1 := Submodule.natAbs_det_equiv (N.restrictScalars ℤ) e
  rw [← Nat.card_congr (Submodule.Quotient.restrictScalarsEquiv ℤ N).toEquiv, ← h1]
  have h2 : (N.restrictScalars ℤ).subtype ∘ₗ (e : (ι → 𝓞 K) →+ N.restrictScalars ℤ).toIntLinearMap
      = A.mulVecLin.restrictScalars ℤ := by
    ext x; rfl
  rw [h2, LinearMap.det_restrictScalars, ← Matrix.toLin'_apply', LinearMap.det_toLin']
end Index
theorem sum_log_norm_embedding (d : 𝓞 K) (hd : d ≠ 0) :
    ∑ σ : K →+* ℂ, Real.log ‖σ (d : K)‖ = Real.log ((Algebra.norm ℤ d).natAbs : ℝ) := by
  have h1 : (((Algebra.norm ℚ (d : K) : ℚ) : ℂ)) = ∏ σ : K →+* ℂ, σ (d : K) := by
    have := Algebra.norm_eq_prod_embeddings ℚ ℂ (d : K)
    rw [eq_ratCast] at this
    rw [this]
    exact (Fintype.prod_equiv (RingHom.equivRatAlgHom K ℂ) _ _ fun σ ↦ rfl).symm
  have h2 : ((Algebra.norm ℤ d).natAbs : ℝ) = ‖∏ σ : K →+* ℂ, σ (d : K)‖ := by
    rw [← h1, ← Algebra.coe_norm_int, Nat.cast_natAbs, Complex.norm_ratCast]
    push_cast; rfl
  rw [h2, norm_prod, Real.log_prod]
  intro σ _
  rw [norm_ne_zero_iff, map_ne_zero]
  exact_mod_cast hd
section Degree
variable (h : HermitianMetric K E)
omit [NumberField K] [Module.Finite (𝓞 K) E] [Module.Projective (𝓞 K) E] in

theorem linearCombination_comb {ι : Type*} [Fintype ι] (s : ι → E) (A : Matrix ι ι (𝓞 K)) :
    Fintype.linearCombination (𝓞 K) s ∘ₗ A.mulVecLin =
      Fintype.linearCombination (𝓞 K) (fun j ↦ ∑ i, A i j • s i) := by
  refine LinearMap.ext fun x ↦ ?_
  simp only [LinearMap.comp_apply, Matrix.mulVecLin_apply, Fintype.linearCombination_apply,
    Matrix.mulVec, dotProduct, Finset.sum_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun i _ ↦ by rw [mul_comm]
theorem degreeWith_reindex {ι ι' : Type*} [Fintype ι] [DecidableEq ι] [Fintype ι']
    [DecidableEq ι'] (e : ι' ≃ ι) (s : ι → E) : degreeWith h (s ∘ e) = degreeWith h s := by
  simp only [degreeWith, gramDet_reindex, e.surjective.range_comp]
theorem degreeWith_comb {ι : Type*} [Fintype ι] [DecidableEq ι] {s : ι → E}
    (hs : LinearIndependent (𝓞 K) s) (hcard : Fintype.card ι = Module.finrank (𝓞 K) E)
    (A : Matrix ι ι (𝓞 K)) (hA : A.det ≠ 0) :
    degreeWith h (fun j ↦ ∑ i, A i j • s i) = degreeWith h s := by
  have hinj := hs.fintypeLinearCombination_injective
  have hfin := finite_quotient_span hs hcard
  have hc : Nat.card (E ⧸ Submodule.span (𝓞 K) (Set.range (fun j ↦ ∑ i, A i j • s i))) =
      (Algebra.norm ℤ A.det).natAbs * Nat.card (E ⧸ Submodule.span (𝓞 K) (Set.range s)) := by
    rw [← Fintype.range_linearCombination, ← linearCombination_comb,
      card_quotient_range_comp _ hinj, card_quotient_mulVecLin A hA, Fintype.range_linearCombination]
  have hcpos : (0 : ℝ) < Nat.card (E ⧸ Submodule.span (𝓞 K) (Set.range s)) := by
    exact_mod_cast Nat.card_pos
  have hN : (0 : ℝ) < (Algebra.norm ℤ A.det).natAbs := by
    have : Algebra.norm ℤ A.det ≠ 0 := Algebra.norm_ne_zero_iff.mpr hA
    exact_mod_cast Int.natAbs_pos.mpr this
  have hσ : ∀ σ : K →+* ℂ, ‖σ (A.det : K)‖ ≠ 0 := fun σ ↦ by
    rw [norm_ne_zero_iff, map_ne_zero]; exact_mod_cast hA
  have hlog : ∀ σ : K →+* ℂ, Real.log (gramDet h σ (fun j ↦ ∑ i, A i j • s i)) =
      2 * Real.log ‖σ (A.det : K)‖ + Real.log (gramDet h σ s) := fun σ ↦ by
    rw [gramDet_comb, Real.log_mul (pow_ne_zero 2 (hσ σ)) (gramDet_pos h σ hs).ne', Real.log_pow]
    push_cast; ring
  simp only [degreeWith]
  rw [hc, Nat.cast_mul, Real.log_mul hN.ne' hcpos.ne']
  simp only [hlog]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, sum_log_norm_embedding _ hA]
  ring
theorem degreeWith_eq_of_linearIndependent {ι : Type*} [Fintype ι] [DecidableEq ι] {s t : ι → E}
    (hs : LinearIndependent (𝓞 K) s) (ht : LinearIndependent (𝓞 K) t)
    (hcard : Fintype.card ι = Module.finrank (𝓞 K) E) : degreeWith h t = degreeWith h s := by
  have hfin := finite_quotient_span hs hcard
  set n := Nat.card (E ⧸ Submodule.span (𝓞 K) (Set.range s))
  have hn : n ≠ 0 := Nat.card_pos.ne'
  have hmem : ∀ j, (n : 𝓞 K) • t j ∈ Submodule.span (𝓞 K) (Set.range s) := by
    intro j
    have := card_nsmul_eq_zero' (G := E ⧸ Submodule.span (𝓞 K) (Set.range s))
      (x := Submodule.Quotient.mk (t j))
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at this
    rwa [Nat.cast_smul_eq_nsmul]
  choose c hc using fun j ↦ (Submodule.mem_span_range_iff_exists_fun (𝓞 K)).mp (hmem j)
  let A : Matrix ι ι (𝓞 K) := Matrix.of fun i j ↦ c j i
  let D : Matrix ι ι (𝓞 K) := (n : 𝓞 K) • 1
  have hu1 : (fun j ↦ ∑ i, A i j • s i) = fun j ↦ (n : 𝓞 K) • t j := funext hc
  have hu2 : (fun j ↦ ∑ i, D i j • t i) = fun j ↦ (n : 𝓞 K) • t j := by
    funext j
    simp [D, Matrix.smul_apply, Matrix.one_apply, ite_smul, Finset.sum_ite_eq']
  have hn' : (n : 𝓞 K) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hD : D.det ≠ 0 := by
    simp only [D, det_smul, det_one, mul_one]
    exact pow_ne_zero _ hn'
  have hA : A.det ≠ 0 := by
    intro h0
    obtain ⟨x, hx0, hx⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    apply hx0
    have key : (n : 𝓞 K) • Fintype.linearCombination (𝓞 K) t x = 0 := by
      have e1 := congrArg (· x) (linearCombination_comb s A)
      simp only [LinearMap.comp_apply, Matrix.mulVecLin_apply, hx, map_zero, hu1] at e1
      rw [← map_smul, e1, Fintype.linearCombination_apply, Fintype.linearCombination_apply]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [Pi.smul_apply, smul_eq_mul, smul_smul, mul_comm]
    have key2 : Fintype.linearCombination (𝓞 K) t x = 0 := (smul_eq_zero.mp key).resolve_left hn'
    exact ht.fintypeLinearCombination_injective (key2.trans (map_zero _).symm)
  rw [← degreeWith_comb h ht hcard D hD, hu2, ← hu1, degreeWith_comb h hs hcard A hA]
omit [NumberField K] [Module.Projective (𝓞 K) E] in

theorem exists_linearIndependent_fin :
    ∃ s : Fin (Module.finrank (𝓞 K) E) → E, LinearIndependent (𝓞 K) s := by
  obtain ⟨S, hS, hli⟩ := exists_set_linearIndependent_of_isDomain (𝓞 K) E
  rw [← Module.finrank_eq_rank] at hS
  obtain ⟨e⟩ := Cardinal.mk_eq_nat_iff.mp hS
  exact ⟨fun i ↦ (e.symm i : E), hli.comp _ e.symm.injective⟩
end Degree
def arithDegree (h : HermitianMetric K E) : ℝ :=
  degreeWith h (exists_linearIndependent_fin (K := K) (E := E)).choose
theorem arithDegree_eq (h : HermitianMetric K E) {ι : Type*} [Fintype ι] [DecidableEq ι]
    {s : ι → E} (hs : LinearIndependent (𝓞 K) s)
    (hcard : Fintype.card ι = Module.finrank (𝓞 K) E) : arithDegree h = degreeWith h s := by
  let e : ι ≃ Fin (Module.finrank (𝓞 K) E) := Fintype.equivFinOfCardEq hcard
  rw [← degreeWith_reindex h e.symm s]
  exact (degreeWith_eq_of_linearIndependent h
    (exists_linearIndependent_fin (K := K) (E := E)).choose_spec
    (hs.comp e.symm e.symm.injective) (Fintype.card_fin _)).symm
theorem norm_fibreVec_sq (h : HermitianMetric K E) (σ : K →+* ℂ) (e : E) :
    ‖fibreVec h σ e‖ ^ 2 = ((h.form σ).inner ((1 : ComplexAt σ) ⊗ₜ e) (1 ⊗ₜ e)).re := by
  rw [@norm_sq_eq_re_inner ℂ]
  rfl
theorem arithDegree_line (h : HermitianMetric K E) (hE : Module.finrank (𝓞 K) E = 1) {s : E}
    (hs : s ≠ 0) :
    arithDegree h = Real.log (Nat.card (E ⧸ Submodule.span (𝓞 K) {s})) -
      ∑ σ : K →+* ℂ, Real.log ‖fibreVec h σ s‖ := by
  have hli : LinearIndependent (𝓞 K) (fun _ : Fin 1 ↦ s) := linearIndependent_unique_iff.mpr hs
  rw [arithDegree_eq h hli (by simp [hE]), degreeWith, Set.range_const]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ ↦ ?_
  simp only [gramDet, det_unique, gram_apply]
  have hv : (inner ℂ (fibreVec h σ s) (fibreVec h σ s)).re = ‖fibreVec h σ s‖ ^ 2 :=
    (norm_sq_eq_re_inner (𝕜 := ℂ) _).symm
  rw [hv, Real.log_pow]
  push_cast; ring
theorem arithDegree_integers : arithDegree (HermitianMetric.integers K) = 0 := by
  rw [arithDegree_line _ (Module.finrank_self (𝓞 K)) one_ne_zero]
  have h1 : Submodule.span (𝓞 K) {(1 : 𝓞 K)} = ⊤ := by
    rw [← Ideal.span, Ideal.span_singleton_one]
  have h2 : ∀ σ : K →+* ℂ, ‖fibreVec (HermitianMetric.integers K) σ 1‖ = 1 := by
    intro σ
    have := norm_fibreVec_sq (HermitianMetric.integers K) σ 1
    rw [HermitianMetric.integers_inner] at this
    simp only [map_one, one_mul] at this
    rw [Complex.one_re] at this
    have h4 := norm_nonneg (fibreVec (HermitianMetric.integers K) σ 1)
    nlinarith [sq_nonneg (‖fibreVec (HermitianMetric.integers K) σ 1‖ - 1)]
  simp only [h1, h2, Real.log_one, Finset.sum_const_zero, sub_zero]
  rw [Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, ⟨0⟩⟩]
  · simp
section Scale
variable {V : Type*} [AddCommGroup V] [Module ℂ V]
@[instance_reducible]
def coreScale (hV : InnerProductSpace.Core ℂ V) (c : ℝ) (hc : 0 < c) :
    InnerProductSpace.Core ℂ V where
  inner x y := ((c ^ 2 : ℝ) : ℂ) * hV.inner x y
  conj_inner_symm x y := by
    rw [map_mul, Complex.conj_ofReal, hV.conj_inner_symm]
  re_inner_nonneg x := by
    change 0 ≤ Complex.re _
    rw [Complex.re_ofReal_mul]
    exact mul_nonneg (by positivity) (hV.re_inner_nonneg x)
  add_left x y z := by
    simp only [hV.add_left]
    ring
  smul_left x y r := by
    simp only [hV.smul_left]
    ring
  definite x hx := by
    have hc2 : ((c ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (pow_pos hc 2).ne'
    exact hV.definite x ((mul_eq_zero.mp hx).resolve_left hc2)
theorem coreScale_inner (hV : InnerProductSpace.Core ℂ V) (c : ℝ) (hc : 0 < c) (x y : V) :
    (coreScale hV c hc).inner x y = ((c ^ 2 : ℝ) : ℂ) * hV.inner x y := rfl
end Scale
def HermitianMetric.scale (h : HermitianMetric K E) (c : ℝ) (hc : 0 < c) : HermitianMetric K E where
  form σ := coreScale (h.form σ) c hc
  form_conj σ x y := by
    rw [coreScale_inner, coreScale_inner, h.form_conj, map_mul, Complex.conj_ofReal]
theorem gramDet_scale (h : HermitianMetric K E) (c : ℝ) (hc : 0 < c) (σ : K →+* ℂ) {ι : Type*}
    [Fintype ι] [DecidableEq ι] (s : ι → E) :
    gramDet (h.scale c hc) σ s = c ^ (2 * Fintype.card ι) * gramDet h σ s := by
  simp only [gramDet]
  have : (gram ℂ fun i ↦ fibreVec (h.scale c hc) σ (s i)) =
      ((c ^ 2 : ℝ) : ℂ) • gram ℂ fun i ↦ fibreVec h σ (s i) := by
    ext i j
    rfl
  rw [this, det_smul, ← Complex.ofReal_pow, Complex.re_ofReal_mul, pow_mul]
theorem arithDegree_scale (h : HermitianMetric K E) (c : ℝ) (hc : 0 < c) :
    arithDegree (h.scale c hc) =
      arithDegree h - Module.finrank (𝓞 K) E * Module.finrank ℚ K * Real.log c := by
  obtain ⟨s, hs⟩ := exists_linearIndependent_fin (K := K) (E := E)
  rw [arithDegree_eq (h.scale c hc) hs (Fintype.card_fin _), arithDegree_eq h hs (Fintype.card_fin _)]
  simp only [degreeWith, gramDet_scale, Fintype.card_fin]
  have hlog : ∀ σ : K →+* ℂ, Real.log (c ^ (2 * Module.finrank (𝓞 K) E) * gramDet h σ s) =
      2 * Module.finrank (𝓞 K) E * Real.log c + Real.log (gramDet h σ s) := fun σ ↦ by
    rw [Real.log_mul (pow_pos hc _).ne' (gramDet_pos h σ hs).ne', Real.log_pow]
    push_cast; ring
  simp only [hlog]
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, NumberField.Embeddings.card,
    nsmul_eq_mul]
  ring
theorem arithDegree_ratIntegers_scale (c : ℝ) (hc : 0 < c) :
    arithDegree ((HermitianMetric.integers ℚ).scale c hc) = -Real.log c := by
  rw [arithDegree_scale, arithDegree_integers, Module.finrank_self, Module.finrank_self]
  simp
example (c : ℝ) (hc : 0 < c) (n : 𝓞 ℚ) (hn : n ≠ 0) :
    Real.log (Nat.card (𝓞 ℚ ⧸ Submodule.span (𝓞 ℚ) {n})) -
      ∑ σ : ℚ →+* ℂ, Real.log ‖fibreVec ((HermitianMetric.integers ℚ).scale c hc) σ n‖ =
      -Real.log c := by
  rw [← arithDegree_line _ (Module.finrank_self (𝓞 ℚ)) hn, arithDegree_ratIntegers_scale]
example : arithDegree ((HermitianMetric.integers ℚ).scale 2 two_pos) = -Real.log 2 :=
  arithDegree_ratIntegers_scale 2 two_pos
end
end GroundTheory.Heights₂.Heights


