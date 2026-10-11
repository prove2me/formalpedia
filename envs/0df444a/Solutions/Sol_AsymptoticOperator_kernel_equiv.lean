-- Prove2me | solution 1 for AsymptoticOperator.kernel_equiv
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-11T00:18:08.860975+00:00
-- url     : https://prove2.me/submissions/a9f95e45-e28b-4f1e-a4e0-bb117c474315

import Theorems.Thm_AsymptoticOperator_graph_existsUnique
import Theorems.Thm_AsymptoticOperator_exists_continuous_of_inW12
import Theorems.Thm_AsymptoticOperator_hasDerivAt_iff_coeff
import Theorems.Thm_AsymptoticOperator_linearODE_existsUnique
import Theorems.Thm_AsymptoticOperator_hasSum_inner_coeff
import Mathlib.MeasureTheory.SpecificCodomains.Pi

open MeasureTheory Matrix ConleyZehnder AsymptoticOperator

lemma ao14_cont_coe : Continuous (fun y : ℝ => (y : UnitAddCircle)) :=
  continuous_quotient_mk'

/-- Uniqueness for `x' = J₀ S x` on vectors. -/
lemma ao14_unique {n : ℕ} (S : C(UnitAddCircle, Mat n)) (x y : ℝ → (Fin n ⊕ Fin n → ℝ))
    (hx : ∀ t : ℝ, HasDerivAt x ((J₀ n * S (t : UnitAddCircle)) *ᵥ x t) t)
    (hy : ∀ t : ℝ, HasDerivAt y ((J₀ n * S (t : UnitAddCircle)) *ᵥ y t) t)
    (h0 : x 0 = y 0) : x = y := by
  let B : ℝ → (Fin n ⊕ Fin n → ℝ) →L[ℝ] (Fin n ⊕ Fin n → ℝ) :=
    fun t => LinearMap.toContinuousLinearMap (Matrix.toLin' (J₀ n * S (t : UnitAddCircle)))
  have hB : Continuous B := by
    refine continuous_clm_apply.2 fun w => ?_
    show Continuous fun t : ℝ => (J₀ n * S (t : UnitAddCircle)) *ᵥ w
    exact (continuous_const.matrix_mul (S.continuous.comp ao14_cont_coe)).matrix_mulVec
      continuous_const
  obtain ⟨z, -, hz⟩ := linearODE_existsUnique B hB (x 0)
  have e1 := hz x ⟨rfl, fun t => by simpa [B] using hx t⟩
  have e2 := hz y ⟨h0.symm, fun t => by simpa [B] using hy t⟩
  rw [e1, e2]

/-- `t ↦ Ψ(t) v` solves `x' = J₀ S x`. -/
lemma ao14_deriv {n : ℕ} (S : C(UnitAddCircle, Mat n)) (Ψ : ℝ → Mat n)
    (hΨ : IsFundamentalSolution S Ψ) (v : Fin n ⊕ Fin n → ℝ) (t : ℝ) :
    HasDerivAt (fun t => Ψ t *ᵥ v) ((J₀ n * S (t : UnitAddCircle)) *ᵥ (Ψ t *ᵥ v)) t := by
  letI : NormedAddCommGroup (Mat n) := Matrix.normedAddCommGroup
  letI : NormedSpace ℝ (Mat n) := Matrix.normedSpace
  let L : Mat n →ₗ[ℝ] (Fin n ⊕ Fin n → ℝ) :=
    { toFun := fun M => M *ᵥ v
      map_add' := fun M N => Matrix.add_mulVec M N v
      map_smul' := fun c M => Matrix.smul_mulVec c M v }
  have := (LinearMap.toContinuousLinearMap L).hasFDerivAt.comp_hasDerivAt t (hΨ.2 t)
  rw [Matrix.mulVec_mulVec]
  exact this

lemma ao14_J_inl {n : ℕ} (v : Fin n ⊕ Fin n → ℂ) (a : Fin n) :
    ((J₀ n).map (fun x : ℝ => (x : ℂ)) *ᵥ v) (Sum.inl a) = -v (Sum.inr a) := by
  simp [J₀, Matrix.J, mulVec, dotProduct, Fintype.sum_sum_type, one_apply]
  simp only [apply_ite (fun x : ℝ => (x : ℂ)), Complex.ofReal_one, Complex.ofReal_zero, ite_mul,
    one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

lemma ao14_J_inr {n : ℕ} (v : Fin n ⊕ Fin n → ℂ) (a : Fin n) :
    ((J₀ n).map (fun x : ℝ => (x : ℂ)) *ᵥ v) (Sum.inr a) = v (Sum.inl a) := by
  simp [J₀, Matrix.J, mulVec, dotProduct, Fintype.sum_sum_type, one_apply]
  simp only [apply_ite (fun x : ℝ => (x : ℂ)), Complex.ofReal_one, Complex.ofReal_zero, ite_mul,
    one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

lemma ao14_JJ {n : ℕ} (u : Fin n ⊕ Fin n → ℂ) :
    (J₀ n).map (fun x : ℝ => (x : ℂ)) *ᵥ ((J₀ n).map (fun x : ℝ => (x : ℂ)) *ᵥ u) = -u := by
  funext i
  rcases i with a | a <;> simp [ao14_J_inl, ao14_J_inr]

lemma ao14_J_smul {n : ℕ} (c : ℂ) (u : Fin n ⊕ Fin n → ℂ) :
    (J₀ n).map (fun x : ℝ => (x : ℂ)) *ᵥ (c • u) = c • ((J₀ n).map (fun x : ℝ => (x : ℂ)) *ᵥ u) :=
  Matrix.mulVec_smul _ _ _

/-- The right-hand side `J₀ S φ` as a continuous loop. -/
noncomputable def ao14_h {n : ℕ} (S : C(UnitAddCircle, Mat n)) (φ : C(UnitAddCircle, Vec n)) :
    C(UnitAddCircle, Vec n) :=
  ⟨fun t => (EuclideanSpace.equiv (Fin n ⊕ Fin n) ℝ).symm
      ((J₀ n * S t) *ᵥ EuclideanSpace.equiv (Fin n ⊕ Fin n) ℝ (φ t)),
    (EuclideanSpace.equiv (Fin n ⊕ Fin n) ℝ).symm.continuous.comp
      ((continuous_const.matrix_mul S.continuous).matrix_mulVec
        ((EuclideanSpace.equiv (Fin n ⊕ Fin n) ℝ).continuous.comp φ.continuous))⟩

lemma ao14_integrable {n : ℕ} (g : UnitAddCircle → (Fin n ⊕ Fin n → ℂ)) (hg : Continuous g) :
    Integrable g (AddCircle.haarAddCircle : Measure UnitAddCircle) :=
  hg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

lemma ao14_coeff_h {n : ℕ} (S : C(UnitAddCircle, Mat n)) (φ : C(UnitAddCircle, Vec n)) (k : ℤ) :
    coeff (ao14_h S φ) k = (J₀ n).map (fun x : ℝ => (x : ℂ)) *ᵥ coeffMul S φ k := by
  set Jc := (J₀ n).map (fun x : ℝ => (x : ℂ))
  have hpt : ∀ t, complexify (ao14_h S φ t) =
      Jc *ᵥ ((S t).map (fun x : ℝ => (x : ℂ)) *ᵥ complexify (φ t)) := by
    intro t
    have hmap : Jc * (S t).map (fun x : ℝ => (x : ℂ)) =
        (J₀ n * S t).map (fun x : ℝ => (x : ℂ)) :=
      (Matrix.map_mul (f := Complex.ofRealHom)).symm
    rw [mulVec_mulVec, hmap]
    funext i
    exact RingHom.map_mulVec Complex.ofRealHom (J₀ n * S t)
      (EuclideanSpace.equiv (Fin n ⊕ Fin n) ℝ (φ t)) i
  let T : (Fin n ⊕ Fin n → ℂ) →L[ℂ] (Fin n ⊕ Fin n → ℂ) :=
    LinearMap.toContinuousLinearMap (Matrix.toLin' Jc)
  have hc : Continuous fun t => (S t).map (fun x : ℝ => (x : ℂ)) *ᵥ complexify (φ t) := by
    have h1 : Continuous fun t => complexify (φ t) := by
      refine continuous_pi fun i => ?_
      exact Complex.continuous_ofReal.comp ((EuclideanSpace.proj i).continuous.comp φ.continuous)
    refine Continuous.matrix_mulVec ?_ h1
    exact continuous_id.matrix_map Complex.continuous_ofReal |>.comp S.continuous
  have hint := (ao14_integrable _ hc).fourier_smul (-k)
  simp only [coeff, coeffMul, fourierCoeff]
  change _ = T (∫ t, fourier (-k) t • ((S t).map (fun x : ℝ => (x : ℂ)) *ᵥ complexify (φ t))
      ∂(AddCircle.haarAddCircle : Measure UnitAddCircle))
  rw [← T.integral_comp_comm hint]
  congr 1
  funext t
  rw [hpt t]
  simp [T, Matrix.toLin'_apply, Matrix.mulVec_smul]

/-- Coefficients of a continuous representative. -/
lemma ao14_coeff_ae {n : ℕ} (S : C(UnitAddCircle, Mat n)) (x : L2 n) (φ : C(UnitAddCircle, Vec n))
    (h : (x : UnitAddCircle → Vec n) =ᵐ[AddCircle.haarAddCircle] φ) :
    coeff x = coeff φ ∧ coeffMul S x = coeffMul S φ := by
  constructor
  · have h' : (fun t => complexify ((x : UnitAddCircle → Vec n) t)) =ᵐ[AddCircle.haarAddCircle]
        (fun t => complexify (φ t)) := by
      filter_upwards [h] with t ht
      rw [ht]
    funext k
    simp only [coeff]
    rw [fourierCoeff_congr_ae h']
  · have h' : (fun t => (S t).map (fun x : ℝ => (x : ℂ)) *ᵥ complexify ((x : UnitAddCircle → Vec n) t))
        =ᵐ[AddCircle.haarAddCircle]
        (fun t => (S t).map (fun x : ℝ => (x : ℂ)) *ᵥ complexify (φ t)) := by
      filter_upwards [h] with t ht
      rw [ht]
    funext k
    simp only [coeffMul]
    rw [fourierCoeff_congr_ae h']

lemma ao14_sq_summable {n : ℕ} (g : L2 n) :
    Summable fun k : ℤ => ∑ i, ‖coeff g k i‖ ^ 2 := by
  have := (hasSum_inner_coeff g g).summable
  refine this.congr fun k => ?_
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]

/-- The Fourier relation of the kernel equation, in both directions. -/
lemma ao14_rel {n : ℕ} (c : ℂ) (u M : Fin n ⊕ Fin n → ℂ) :
    (0 = -c • ((J₀ n).map (fun x : ℝ => (x : ℂ)) *ᵥ u) - M) ↔
      (J₀ n).map (fun x : ℝ => (x : ℂ)) *ᵥ M = c • u := by
  constructor
  · intro h
    have hM : M = -c • ((J₀ n).map (fun x : ℝ => (x : ℂ)) *ᵥ u) :=
      (sub_eq_zero.1 h.symm).symm
    rw [hM, ao14_J_smul, ao14_JJ, smul_neg, neg_smul, neg_neg]
  · intro h
    have hM : M = -c • ((J₀ n).map (fun x : ℝ => (x : ℂ)) *ᵥ u) := by
      have := congrArg (fun w => (J₀ n).map (fun x : ℝ => (x : ℂ)) *ᵥ w) h
      simp only [ao14_JJ, ao14_J_smul] at this
      rw [← neg_neg M, this, neg_smul]
    rw [hM, sub_self]

theorem solution {n : ℕ} (S : C(UnitAddCircle, Mat n)) (hS : IsSymLoop S)
    (Ψ : ℝ → Mat n) (hΨ : IsFundamentalSolution S Ψ) :
    Nonempty (eigenspace (asymptoticOperator S) 0 ≃ₗ[ℝ]
      LinearMap.ker (Matrix.toLin' (Ψ 1 - 1))) := by
  set A := asymptoticOperator S
  set μ : Measure UnitAddCircle := AddCircle.haarAddCircle with hμ
  set E := EuclideanSpace.equiv (Fin n ⊕ Fin n) ℝ
  set K := LinearMap.ker (Matrix.toLin' (Ψ 1 - 1))
  -- the graph of `A` is `graphSet S`
  have hex : ∃ A' : L2 n →ₗ.[ℝ] L2 n, (A'.graph : Set (L2 n × L2 n)) = graphSet S :=
    (graph_existsUnique S).exists
  have hgraph : (A.graph : Set (L2 n × L2 n)) = graphSet S := by
    simp only [A]
    rw [asymptoticOperator, dif_pos hex]
    exact hex.choose_spec
  have hact : ∀ x : A.domain, IsAsymptoticAction S x (A x) := by
    intro x
    have : ((x : L2 n), A x) ∈ (A.graph : Set (L2 n × L2 n)) := A.mem_graph x
    rw [hgraph] at this
    exact this
  have hdom : ∀ f g : L2 n, IsAsymptoticAction S f g →
      ∃ h : f ∈ A.domain, A ⟨f, h⟩ = g := by
    intro f g hfg
    have : (f, g) ∈ (A.graph : Set (L2 n × L2 n)) := by
      rw [hgraph]; exact hfg
    obtain ⟨y, hy1, hy2⟩ := (LinearPMap.mem_graph_iff _).1 this
    have hy1' : (y : L2 n) = f := hy1
    refine ⟨hy1' ▸ y.2, ?_⟩
    have hy2' : A y = g := hy2
    rw [← hy2']
    congr 1
    exact Subtype.ext hy1'.symm
  have hmem : ∀ x : A.domain, x ∈ eigenspace A 0 ↔ A x = 0 := by
    intro x
    simp only [eigenspace, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
      Submodule.subtype_apply, zero_smul, sub_zero]
    rfl
  have hcoeff0 : ∀ k, coeff ((0 : L2 n) : UnitAddCircle → Vec n) k = 0 := by
    intro k
    have h : (fun t => complexify (((0 : L2 n) : UnitAddCircle → Vec n) t)) =ᵐ[μ] fun _ => 0 := by
      filter_upwards [Lp.coeFn_zero (Vec n) 2 μ] with t ht
      rw [ht]; funext i; simp [complexify]
    simp only [coeff]
    rw [fourierCoeff_congr_ae h]
    simp [fourierCoeff]
  -- kernel elements of `A` correspond to continuous solutions of the Fourier relation
  have hkey : ∀ φ : C(UnitAddCircle, Vec n),
      (IsAsymptoticAction S (ContinuousMap.toLp (E := Vec n) 2 μ ℝ φ) 0 ↔
        ∀ x : ℝ, HasDerivAt (fun y : ℝ => φ (y : UnitAddCircle))
          (ao14_h S φ (x : UnitAddCircle)) x) := by
    intro φ
    have hae : ((ContinuousMap.toLp (E := Vec n) 2 μ ℝ φ : L2 n) : UnitAddCircle → Vec n) =ᵐ[μ] φ :=
      ContinuousMap.coeFn_toLp (p := 2) (μ := μ) (𝕜 := ℝ) φ
    obtain ⟨hc1, hc2⟩ := ao14_coeff_ae S _ φ hae
    rw [hasDerivAt_iff_coeff]
    constructor
    · rintro ⟨-, hk⟩ k
      have := hk k
      rw [hcoeff0, hc1, hc2] at this
      rw [ao14_coeff_h]
      exact (ao14_rel _ _ _).1 this
    · intro hk
      refine ⟨?_, fun k => ?_⟩
      · -- `W^{1,2}` regularity
        unfold InW12
        rw [hc1]
        have h1 := ao14_sq_summable (ContinuousMap.toLp (E := Vec n) 2 μ ℝ φ)
        have h2 := ao14_sq_summable (ContinuousMap.toLp (E := Vec n) 2 μ ℝ (ao14_h S φ))
        rw [(ao14_coeff_ae S _ _ (ContinuousMap.coeFn_toLp (p := 2) (μ := μ) (𝕜 := ℝ) (ao14_h S φ))).1] at h2
        rw [hc1] at h1
        refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_) (h1.add h2)
        have hpi : (1 : ℝ) ≤ (2 * Real.pi) ^ 2 := by nlinarith [Real.two_le_pi]
        have hterm : ∀ i, ‖coeff (ao14_h S φ) k i‖ ^ 2 =
            (2 * Real.pi * k) ^ 2 * ‖coeff φ k i‖ ^ 2 := by
          intro i
          rw [hk k, Pi.smul_apply, smul_eq_mul, norm_mul, norm_mul, Complex.norm_I, mul_one,
            Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
        simp only [hterm, ← Finset.mul_sum]
        have h0 : 0 ≤ ∑ i, ‖coeff φ k i‖ ^ 2 := by positivity
        have hk2 : (k : ℝ) ^ 2 ≤ (2 * Real.pi * k) ^ 2 := by
          rw [mul_pow]; nlinarith [sq_nonneg (k : ℝ)]
        nlinarith
      · rw [hcoeff0, hc1, hc2]
        apply (ao14_rel _ _ _).2
        rw [← ao14_coeff_h]
        exact hk k
  -- the vector form of the derivative condition
  have hvec : ∀ φ : C(UnitAddCircle, Vec n),
      (∀ x : ℝ, HasDerivAt (fun y : ℝ => φ (y : UnitAddCircle))
          (ao14_h S φ (x : UnitAddCircle)) x) ↔
        ∀ x : ℝ, HasDerivAt (fun y : ℝ => E (φ (y : UnitAddCircle)))
          ((J₀ n * S (x : UnitAddCircle)) *ᵥ E (φ (x : UnitAddCircle))) x := by
    intro φ
    constructor
    · intro h x
      have := E.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt x (h x)
      simp only [Function.comp_def, ContinuousLinearEquiv.coe_coe] at this
      exact this
    · intro h x
      have := E.symm.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt x (h x)
      simp only [Function.comp_def, ContinuousLinearEquiv.coe_coe,
        ContinuousLinearEquiv.symm_apply_apply] at this
      exact this
  -- the loop `t ↦ Ψ(t) v` for `v ∈ ker(Ψ(1) - 1)`
  have hker : ∀ v : Fin n ⊕ Fin n → ℝ, v ∈ K ↔ Ψ 1 *ᵥ v = v := by
    intro v
    simp only [K, LinearMap.mem_ker, Matrix.toLin'_apply, Matrix.sub_mulVec, one_mulVec,
      sub_eq_zero]
  have hper : ∀ v : K, Function.Periodic (fun t : ℝ => E.symm (Ψ t *ᵥ (v : Fin n ⊕ Fin n → ℝ))) 1 := by
    intro v t
    have hv := (hker v).1 v.2
    have e := ao14_unique S (fun t => Ψ (t + 1) *ᵥ (v : Fin n ⊕ Fin n → ℝ))
      (fun t => Ψ t *ᵥ (v : Fin n ⊕ Fin n → ℝ))
      (fun t => by
        have := (ao14_deriv S Ψ hΨ v (t + 1)).comp_add_const t 1
        simpa only [AddCircle.coe_add_period] using this)
      (fun t => ao14_deriv S Ψ hΨ v t)
      (by simp [hv, hΨ.1])
    simp only
    rw [show Ψ (t + 1) *ᵥ (v : Fin n ⊕ Fin n → ℝ) = Ψ t *ᵥ (v : Fin n ⊕ Fin n → ℝ) from
      congrFun e t]
  have hcontv : ∀ v : Fin n ⊕ Fin n → ℝ, Continuous fun t : ℝ => E.symm (Ψ t *ᵥ v) :=
    fun v => E.symm.continuous.comp (continuous_iff_continuousAt.2 fun t =>
      (ao14_deriv S Ψ hΨ v t).continuousAt)
  let P : K → C(UnitAddCircle, Vec n) := fun v =>
    ⟨(hper v).lift, (QuotientAddGroup.isQuotientMap_mk _).continuous_iff.2 (hcontv v)⟩
  have hP : ∀ (v : K) (t : ℝ), P v (t : UnitAddCircle) = E.symm (Ψ t *ᵥ (v : Fin n ⊕ Fin n → ℝ)) :=
    fun v t => rfl
  have hPadd : ∀ v w : K, P (v + w) = P v + P w := by
    intro v w
    ext1 t
    obtain ⟨s, rfl⟩ := QuotientAddGroup.mk_surjective t
    simp only [ContinuousMap.add_apply]
    rw [show (QuotientAddGroup.mk s : UnitAddCircle) = (s : UnitAddCircle) from rfl, hP, hP, hP,
      Submodule.coe_add, Matrix.mulVec_add, map_add]
  have hPsmul : ∀ (c : ℝ) (v : K), P (c • v) = c • P v := by
    intro c v
    ext1 t
    obtain ⟨s, rfl⟩ := QuotientAddGroup.mk_surjective t
    simp only [ContinuousMap.smul_apply]
    rw [show (QuotientAddGroup.mk s : UnitAddCircle) = (s : UnitAddCircle) from rfl, hP, hP,
      Submodule.coe_smul, Matrix.mulVec_smul, map_smul]
  have hPsol : ∀ v : K, IsAsymptoticAction S (ContinuousMap.toLp (E := Vec n) 2 μ ℝ (P v)) 0 := by
    intro v
    rw [hkey, hvec]
    intro x
    have := ao14_deriv S Ψ hΨ v x
    simpa only [hP, LinearEquiv.apply_symm_apply, ContinuousLinearEquiv.apply_symm_apply]
      using this
  let T : K → L2 n := fun v => ContinuousMap.toLp (E := Vec n) 2 μ ℝ (P v)
  have hTdom : ∀ v : K, T v ∈ A.domain := fun v => (hdom _ _ (hPsol v)).1
  have hTeig : ∀ v : K, (⟨T v, hTdom v⟩ : A.domain) ∈ eigenspace A 0 := by
    intro v
    rw [hmem]
    obtain ⟨h, hA⟩ := hdom _ _ (hPsol v)
    exact hA
  let Φ : K →ₗ[ℝ] eigenspace A 0 :=
    { toFun := fun v => ⟨⟨T v, hTdom v⟩, hTeig v⟩
      map_add' := by
        intro v w
        apply Subtype.ext; apply Subtype.ext
        simp only [T, Submodule.coe_add, hPadd, map_add]
      map_smul' := by
        intro c v
        apply Subtype.ext; apply Subtype.ext
        simp only [T, Submodule.coe_smul, hPsmul, map_smul, RingHom.id_apply] }
  refine ⟨(LinearEquiv.ofBijective Φ ⟨?_, ?_⟩).symm⟩
  · -- injectivity
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    have h1 : T v = 0 := congrArg (fun z : eigenspace A 0 => ((z : A.domain) : L2 n)) hv
    have h2 : P v = 0 := by
      apply ContinuousMap.toLp_injective (p := 2) (μ := μ) (𝕜 := ℝ)
      rw [map_zero]
      exact h1
    have h3 := congrArg (fun F : C(UnitAddCircle, Vec n) => F ((0 : ℝ) : UnitAddCircle)) h2
    simp only [hP, hΨ.1, one_mulVec, ContinuousMap.zero_apply] at h3
    ext i
    have := congrArg (fun w => E w i) h3
    simpa using this
  · -- surjectivity
    rintro ⟨⟨x, hxd⟩, hxe⟩
    have hAx : A ⟨x, hxd⟩ = 0 := (hmem _).1 hxe
    have hx0 := hact ⟨x, hxd⟩
    rw [hAx] at hx0
    have hx : IsAsymptoticAction S x 0 := hx0
    obtain ⟨φ, hφ⟩ := exists_continuous_of_inW12 x hx.1
    have hxφ : x = ContinuousMap.toLp (E := Vec n) 2 μ ℝ φ := by
      apply Lp.ext
      filter_upwards [hφ, ContinuousMap.coeFn_toLp (𝕜 := ℝ) (p := 2) (μ := μ) φ] with t h1 h2
      rw [h1, h2]
    rw [hxφ, hkey, hvec] at hx
    set v : Fin n ⊕ Fin n → ℝ := E (φ ((0 : ℝ) : UnitAddCircle))
    have hsol := ao14_unique S (fun y : ℝ => E (φ (y : UnitAddCircle))) (fun t => Ψ t *ᵥ v)
      hx (fun t => ao14_deriv S Ψ hΨ v t) (by simp [v, hΨ.1])
    have hvK : v ∈ K := by
      rw [hker]
      have := congrFun hsol 1
      rw [← this]
      simp only [v]
      rw [show ((1 : ℝ) : UnitAddCircle) = ((0 : ℝ) : UnitAddCircle) by
        rw [AddCircle.coe_period, QuotientAddGroup.mk_zero]]
    refine ⟨⟨v, hvK⟩, ?_⟩
    have hPφ : P ⟨v, hvK⟩ = φ := by
      ext1 t
      obtain ⟨s, rfl⟩ := QuotientAddGroup.mk_surjective t
      rw [show (QuotientAddGroup.mk s : UnitAddCircle) = (s : UnitAddCircle) from rfl, hP]
      have := congrFun hsol s
      rw [← this]
      simp
    apply Subtype.ext; apply Subtype.ext
    show T ⟨v, hvK⟩ = x
    simp only [T, hPφ, hxφ]
