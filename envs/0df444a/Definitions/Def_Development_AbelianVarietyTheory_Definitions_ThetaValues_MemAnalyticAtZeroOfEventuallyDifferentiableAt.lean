-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_MemAnalyticAtZeroOfEventuallyDifferentiableAt
-- name    : Development_AbelianVarietyTheory_Definitions_ThetaValues_MemAnalyticAtZeroOfEventuallyDifferentiableAt
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-24T23:37:37.544538+00:00
-- url     : https://prove2.me/theorems/74dcc1b5-04f3-43b1-991e-89d323aa3ee2
-- title:
--   Mem Analytic At Zero Of Eventually Differentiable At
-- statement:
--   Definitions and structural lemmas for Mem Analytic At Zero Of Eventually Differentiable At, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaValues/MemAnalyticAtZeroOfEventuallyDifferentiableAt.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LineDerivListEqIteratedFDeriv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Theorems.Thm_GlobalTheory_SCV_analyticAt_iff_eventually_differentiableAt
import Theorems.Thm_GlobalTheory_analyticAt_lineDerivList
import Theorems.Thm_GlobalTheory_lineDerivList_add
import Theorems.Thm_GlobalTheory_lineDerivList_append
import Theorems.Thm_GlobalTheory_lineDerivList_const_smul
import Theorems.Thm_GlobalTheory_lineDerivList_nil
import Theorems.Thm_GlobalTheory_lineDerivList_ofFn
import Theorems.Thm_GlobalTheory_lineDerivList_perm
import Theorems.Thm_GlobalTheory_lineDerivList_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.lineDerivList_nil
attribute [local simp] GlobalTheory.lineDerivList_zero


set_option autoImplicit false
open Filter Topology
namespace GlobalTheory
section Formal
variable {σ R : Type*} [CommRing R] [IsAddTorsionFree R]
theorem mvPowerSeries_eq_zero_of_pderiv_mem_span (S : Set (MvPowerSeries σ R))
    (h0 : ∀ F ∈ S, MvPowerSeries.constantCoeff F = 0)
    (hd : ∀ F ∈ S, ∀ i, MvPowerSeries.pderiv R i F ∈ Ideal.span S) : ∀ F ∈ S, F = 0 := by
  classical
  have key : ∀ n : ℕ, ∀ F ∈ Ideal.span S, ∀ m : σ →₀ ℕ, m.degree < n →
      MvPowerSeries.coeff m F = 0 := by
    intro n
    induction n with
    | zero => intro F _ m hm; omega
    | succ n ih =>
      intro F hF
      induction hF using Submodule.span_induction with
      | mem F hF =>
        intro m hm
        by_cases h : m = 0
        · rw [h, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, h0 F hF]
        obtain ⟨i, hi⟩ : ∃ i, m i ≠ 0 := by simpa using Finsupp.ne_iff.1 h
        have hle : Finsupp.single i 1 ≤ m := by
          rw [Finsupp.single_le_iff]; omega
        obtain ⟨m', rfl⟩ := exists_add_of_le hle
        have h1 := ih _ (hd F hF i) m' (by
          rw [map_add, Finsupp.degree_single] at hm; omega)
        rw [MvPowerSeries.coeff_pderiv, add_comm m', mul_comm, ← Nat.cast_succ, ← nsmul_eq_mul,
          smul_eq_zero_iff_right (Nat.succ_ne_zero _)] at h1
        exact h1
      | zero => intro m _; simp
      | add F G _ _ hF hG => intro m hm; rw [map_add, hF m hm, hG m hm, add_zero]
      | smul G F _ hF =>
        intro m hm
        rw [smul_eq_mul, MvPowerSeries.coeff_mul]
        refine Finset.sum_eq_zero fun p hp => ?_
        rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
        rw [hF p.2 (by rw [← hp, map_add] at hm; omega), mul_zero]
  intro F hF
  ext m
  rw [key _ F (Ideal.subset_span hF) m (Nat.lt_succ_self _), map_zero]
end Formal
section Operator
variable {σ W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]
theorem dirPolyDeriv_monomial_one (m : σ →₀ ℕ) (u : σ → W) (F : W → ℂ) (x : W) :
    ReciprocityTheory.ChartRestriction.G.I2.polyDeriv (MvPolynomial.monomial m 1) u F x =
      iteratedFDeriv ℂ (Multiset.card (Finsupp.toMultiset m)) F x
        (fun k => u ((Finsupp.toMultiset m).toList.get
          (k.cast (Multiset.length_toList _).symm))) := by
  classical
  simp [ReciprocityTheory.ChartRestriction.G.I2.polyDeriv, MvPolynomial.support_monomial]
theorem dirPolyDeriv_monomial_eq_lineDerivList {m : σ →₀ ℕ} {l : List σ}
    (hl : (l : Multiset σ) = Finsupp.toMultiset m) (u : σ → W) {F : W → ℂ} {x : W}
    (hF : AnalyticAt ℂ F x) :
    ReciprocityTheory.ChartRestriction.G.I2.polyDeriv (MvPolynomial.monomial m 1) u F x =
      lineDerivList ℂ (l.map u) F x := by
  rw [dirPolyDeriv_monomial_one, ← lineDerivList_ofFn hF]
  have h1 : (List.ofFn fun k : Fin (Multiset.card (Finsupp.toMultiset m)) =>
      u ((Finsupp.toMultiset m).toList.get (k.cast (Multiset.length_toList _).symm)))
      = (Finsupp.toMultiset m).toList.map u := by
    apply List.ext_getElem <;> simp
  rw [h1]
  refine lineDerivList_perm hF (List.Perm.map _ ?_)
  rw [← Multiset.coe_eq_coe, Multiset.coe_toList, hl]
end Operator
section Dir
variable {σ W : Type*} [Fintype σ] [NormedAddCommGroup W] [NormedSpace ℂ W]
noncomputable def taylorDir (u : σ → W) (f : W → ℂ) : MvPowerSeries σ ℂ :=
  fun m => ((∏ i, (m i).factorial : ℕ) : ℂ)⁻¹ *
    ReciprocityTheory.ChartRestriction.G.I2.polyDeriv (MvPolynomial.monomial m 1) u f 0
variable (u : σ → W) {f g : W → ℂ}
theorem coeff_taylorDir (f : W → ℂ) (m : σ →₀ ℕ) :
    MvPowerSeries.coeff m (taylorDir u f) = ((∏ i, (m i).factorial : ℕ) : ℂ)⁻¹ *
      ReciprocityTheory.ChartRestriction.G.I2.polyDeriv (MvPolynomial.monomial m 1) u f 0 := rfl
omit [NormedAddCommGroup W] [NormedSpace ℂ W] in

theorem cast_prod_factorial_ne_zero (m : σ →₀ ℕ) : ((∏ i, (m i).factorial : ℕ) : ℂ) ≠ 0 :=
  Nat.cast_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun i _ => (m i).factorial_ne_zero)
theorem dirPolyDeriv_monomial_eq_coeff (f : W → ℂ) (m : σ →₀ ℕ) :
    ReciprocityTheory.ChartRestriction.G.I2.polyDeriv (MvPolynomial.monomial m 1) u f 0 =
      ((∏ i, (m i).factorial : ℕ) : ℂ) * MvPowerSeries.coeff m (taylorDir u f) := by
  rw [coeff_taylorDir, mul_inv_cancel_left₀ (cast_prod_factorial_ne_zero m)]
theorem coeff_taylorDir_eq_lineDerivList (hf : AnalyticAt ℂ f 0) {m : σ →₀ ℕ} {l : List σ}
    (hl : (l : Multiset σ) = Finsupp.toMultiset m) :
    MvPowerSeries.coeff m (taylorDir u f) =
      ((∏ i, (m i).factorial : ℕ) : ℂ)⁻¹ * lineDerivList ℂ (l.map u) f 0 := by
  rw [coeff_taylorDir, dirPolyDeriv_monomial_eq_lineDerivList hl u hf]
theorem taylorDir_congr (h : f =ᶠ[𝓝 0] g) : taylorDir u f = taylorDir u g := by
  ext m
  rw [coeff_taylorDir, coeff_taylorDir, dirPolyDeriv_monomial_one, dirPolyDeriv_monomial_one,
    (h.iteratedFDeriv ℂ _).eq_of_nhds]
@[simp] theorem constantCoeff_taylorDir (f : W → ℂ) :
    MvPowerSeries.constantCoeff (taylorDir u f) = f 0 := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_taylorDir,
    dirPolyDeriv_monomial_one]
  have : ∀ (n : ℕ) (_ : n = 0) (v : Fin n → W), iteratedFDeriv ℂ n f 0 v = f 0 := by
    rintro n rfl v; simp
  rw [this _ (by simp)]
  simp
theorem taylorDir_add (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) :
    taylorDir u (f + g) = taylorDir u f + taylorDir u g := by
  ext m
  rw [map_add, coeff_taylorDir_eq_lineDerivList u (hf.add hg) (Multiset.coe_toList _),
    coeff_taylorDir_eq_lineDerivList u hf (Multiset.coe_toList _),
    coeff_taylorDir_eq_lineDerivList u hg (Multiset.coe_toList _), ← mul_add,
    ← lineDerivList_add hf hg]
  rfl
theorem taylorDir_smul (c : ℂ) (hf : AnalyticAt ℂ f 0) :
    taylorDir u (c • f) = c • taylorDir u f := by
  ext m
  have h := congrFun (lineDerivList_const_smul ((Finsupp.toMultiset m).toList.map u) c f) 0
  rw [map_smul, coeff_taylorDir_eq_lineDerivList u hf.const_smul (Multiset.coe_toList _),
    coeff_taylorDir_eq_lineDerivList u hf (Multiset.coe_toList _)]
  change _ * lineDerivList ℂ _ (fun z => c • f z) 0 = _
  rw [h, smul_eq_mul, smul_eq_mul]
  ring
theorem analyticAt_fderiv_apply {x : W} (hf : AnalyticAt ℂ f x) (v : W) :
    AnalyticAt ℂ (fun z => fderiv ℂ f z v) x :=
  ((ContinuousLinearMap.apply ℂ ℂ v).analyticAt _).comp hf.fderiv
theorem taylorDir_fderiv (hf : AnalyticAt ℂ f 0) (i : σ) :
    taylorDir u (fun z => fderiv ℂ f z (u i)) = MvPowerSeries.pderiv ℂ i (taylorDir u f) := by
  classical
  have h1 : (fun z => fderiv ℂ f z (u i)) =ᶠ[𝓝 0] lineDerivList ℂ [u i] f := by
    filter_upwards [hf.eventually_analyticAt] with z hz
    exact hz.differentiableAt.lineDeriv_eq_fderiv.symm
  ext m
  rw [taylorDir_congr u h1, MvPowerSeries.coeff_pderiv,
    coeff_taylorDir_eq_lineDerivList u (analyticAt_lineDerivList hf _) (Multiset.coe_toList _),
    coeff_taylorDir_eq_lineDerivList u hf (l := (Finsupp.toMultiset m).toList ++ [i])
      (by rw [← Multiset.coe_add]; simp), List.map_append, lineDerivList_append]
  have h2 : (∏ j, ((m + Finsupp.single i 1 : σ →₀ ℕ) j).factorial : ℕ) = (m i + 1) * ∏ j, (m j).factorial := by
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i),
      ← Finset.mul_prod_erase _ (fun j => (m j).factorial) (Finset.mem_univ i), ← mul_assoc]
    congr 1
    · simp [Nat.factorial_succ]
    · refine Finset.prod_congr rfl fun j hj => ?_
      simp [Finsupp.single_eq_of_ne (Finset.ne_of_mem_erase hj)]
  have h3 := cast_prod_factorial_ne_zero m
  have h4 : ((m i : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (m i)
  rw [h2, Nat.cast_mul, Nat.cast_succ, List.map_singleton]
  field_simp
@[simp] theorem taylorDir_const (c : ℂ) : taylorDir u (fun _ => c) = MvPowerSeries.C c := by
  have h0 : taylorDir u (fun _ => (0 : ℂ)) = 0 := by
    have := taylorDir_smul u 0 (analyticAt_const (v := (0 : ℂ)) (x := (0 : W)))
    rw [zero_smul, zero_smul] at this
    exact this
  refine MvPowerSeries.pderiv.ext (fun i => ?_) (by simp)
  rw [← taylorDir_fderiv u analyticAt_const]
  simp [h0]
@[simp] theorem taylorDir_zero : taylorDir u (0 : W → ℂ) = 0 :=
  (taylorDir_const u 0).trans (map_zero _)
@[simp] theorem taylorDir_one : taylorDir u (1 : W → ℂ) = 1 :=
  (taylorDir_const u 1).trans (map_one _)
theorem taylorDir_mul (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) :
    taylorDir u (f * g) = taylorDir u f * taylorDir u g := by
  rw [← sub_eq_zero]
  refine mvPowerSeries_eq_zero_of_pderiv_mem_span
    {F | ∃ f g : W → ℂ, AnalyticAt ℂ f 0 ∧ AnalyticAt ℂ g 0 ∧
      F = taylorDir u (f * g) - taylorDir u f * taylorDir u g} ?_ ?_ _ ⟨f, g, hf, hg, rfl⟩
  · rintro _ ⟨f, g, -, -, rfl⟩
    simp
  · rintro _ ⟨f, g, hf, hg, rfl⟩ i
    have hf' := analyticAt_fderiv_apply hf (u i)
    have hg' := analyticAt_fderiv_apply hg (u i)
    have h1 : (fun z => fderiv ℂ (f * g) z (u i)) =ᶠ[𝓝 0]
        f * (fun z => fderiv ℂ g z (u i)) + (fun z => fderiv ℂ f z (u i)) * g := by
      filter_upwards [hf.eventually_analyticAt, hg.eventually_analyticAt] with z hz hz'
      rw [fderiv_mul hz.differentiableAt hz'.differentiableAt]
      simp [mul_comm]
    rw [map_sub, ← taylorDir_fderiv u (hf.mul hg), taylorDir_congr u h1,
      taylorDir_add u (hf.mul hg') (hf'.mul hg), Derivation.leibniz, ← taylorDir_fderiv u hf,
      ← taylorDir_fderiv u hg, smul_eq_mul, smul_eq_mul, add_sub_add_comm,
      mul_comm (taylorDir u g)]
    exact Ideal.add_mem _ (Ideal.subset_span ⟨_, _, hf, hg', rfl⟩)
      (Ideal.subset_span ⟨_, _, hf', hg, rfl⟩)
theorem taylorDir_clm (ℓ : W →L[ℂ] ℂ) :
    taylorDir u ℓ = ∑ i, ℓ (u i) • (MvPowerSeries.X i : MvPowerSeries σ ℂ) := by
  classical
  refine MvPowerSeries.pderiv.ext (fun i => ?_) (by simp)
  rw [← taylorDir_fderiv u (ℓ.analyticAt 0)]
  simp [MvPowerSeries.pderiv_X, Pi.single_apply, MvPowerSeries.smul_eq_C_mul]
variable (W) in

def analyticAtZero : Subalgebra ℂ (W → ℂ) where
  carrier := {f | AnalyticAt ℂ f 0}
  mul_mem' hf hg := hf.mul hg
  add_mem' hf hg := hf.add hg
  algebraMap_mem' _ := analyticAt_const
omit [Fintype σ] in

@[simp] theorem mem_analyticAtZero : f ∈ analyticAtZero W ↔ AnalyticAt ℂ f 0 := Iff.rfl
noncomputable def taylorDirAlgHom : analyticAtZero W →ₐ[ℂ] MvPowerSeries σ ℂ where
  toFun f := taylorDir u f
  map_one' := taylorDir_one u
  map_mul' f g := taylorDir_mul u f.2 g.2
  map_zero' := taylorDir_zero u
  map_add' f g := taylorDir_add u f.2 g.2
  commutes' c := taylorDir_const u c
@[simp] theorem taylorDirAlgHom_apply (f : analyticAtZero W) :
    taylorDirAlgHom u f = taylorDir u f := rfl
theorem taylorDir_eval {κ : Type*} {φ : κ → W → ℂ} (hφ : ∀ k, AnalyticAt ℂ (φ k) 0)
    (P : MvPolynomial κ ℂ) :
    taylorDir u (fun z => MvPolynomial.eval (fun k => φ k z) P) =
      MvPolynomial.aeval (fun k => taylorDir u (φ k)) P := by
  have h := MvPolynomial.comp_aeval_apply (f := fun k => (⟨φ k, hφ k⟩ : analyticAtZero W))
    (taylorDirAlgHom u) P
  simp only [taylorDirAlgHom_apply] at h
  rw [← h]
  congr 1
  funext z
  exact (MvPolynomial.comp_aeval_apply (f := fun k => (⟨φ k, hφ k⟩ : analyticAtZero W))
    ((Pi.evalAlgHom ℂ (fun _ : W => ℂ) z).comp (analyticAtZero W).val) P).symm
end Dir
section Coord
variable {σ : Type*} [Fintype σ] [DecidableEq σ]
noncomputable def taylor (f : (σ → ℂ) → ℂ) : MvPowerSeries σ ℂ :=
  taylorDir (fun i => (Pi.single i 1 : σ → ℂ)) f
variable {f g : (σ → ℂ) → ℂ}
theorem taylor_eq_taylorDir (f : (σ → ℂ) → ℂ) :
    taylor f = taylorDir (fun i => (Pi.single i 1 : σ → ℂ)) f := rfl
@[simp] theorem constantCoeff_taylor (f : (σ → ℂ) → ℂ) :
    MvPowerSeries.constantCoeff (taylor f) = f 0 := constantCoeff_taylorDir _ f
@[simp] theorem taylor_const (c : ℂ) :
    taylor (fun _ : σ → ℂ => c) = MvPowerSeries.C c := taylorDir_const _ c
@[simp] theorem taylor_zero : taylor (0 : (σ → ℂ) → ℂ) = 0 := taylorDir_zero _
@[simp] theorem taylor_one : taylor (1 : (σ → ℂ) → ℂ) = 1 := taylorDir_one _
theorem taylor_fderiv (hf : AnalyticAt ℂ f 0) (i : σ) :
    taylor (fun z => fderiv ℂ f z (Pi.single i 1)) = MvPowerSeries.pderiv ℂ i (taylor f) :=
  taylorDir_fderiv (fun i => (Pi.single i 1 : σ → ℂ)) hf i
theorem taylor_clm (ℓ : (σ → ℂ) →L[ℂ] ℂ) :
    taylor ℓ = ∑ i, ℓ (Pi.single i 1) • (MvPowerSeries.X i : MvPowerSeries σ ℂ) :=
  taylorDir_clm _ ℓ
@[simp] theorem taylor_coord (i : σ) : taylor (fun z : σ → ℂ => z i) = MvPowerSeries.X i := by
  have h := taylor_clm (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : σ => ℂ) i)
  simp only [ContinuousLinearMap.proj_apply, Pi.single_apply, ite_smul, one_smul, zero_smul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true] at h
  exact h
noncomputable def taylorAlgHom : analyticAtZero (σ → ℂ) →ₐ[ℂ] MvPowerSeries σ ℂ :=
  taylorDirAlgHom fun i => (Pi.single i 1 : σ → ℂ)
@[simp] theorem taylorAlgHom_apply (f : analyticAtZero (σ → ℂ)) : taylorAlgHom f = taylor f := rfl
theorem taylor_eval_comp {κ : Type*} {φ : κ → (σ → ℂ) → ℂ} (hφ : ∀ k, AnalyticAt ℂ (φ k) 0)
    (P : MvPolynomial κ ℂ) :
    taylor (fun z => MvPolynomial.eval (fun k => φ k z) P) =
      MvPolynomial.aeval (fun k => taylor (φ k)) P := taylorDir_eval _ hφ P
theorem taylor_eval (P : MvPolynomial σ ℂ) :
    taylor (fun z : σ → ℂ => MvPolynomial.eval z P) = (P : MvPowerSeries σ ℂ) := by
  have h := taylor_eval_comp (φ := fun (k : σ) (z : σ → ℂ) => z k)
    (fun k => (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : σ => ℂ) k).analyticAt 0) P
  simp only [taylor_coord] at h
  refine h.trans ?_
  have : MvPolynomial.aeval (fun k : σ => (MvPowerSeries.X k : MvPowerSeries σ ℂ))
      = MvPolynomial.coeToMvPowerSeries.algHom (R := ℂ) ℂ := by
    ext1 k; simp
  rw [this]
  simp
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]
end Coord
section Examples
example : taylor (fun z : Fin 2 → ℂ => z 0 * z 1 + 3) =
    MvPowerSeries.X 0 * MvPowerSeries.X 1 + MvPowerSeries.C 3 := by
  have h := taylor_eval (MvPolynomial.X 0 * MvPolynomial.X 1 + MvPolynomial.C 3 :
    MvPolynomial (Fin 2) ℂ)
  simpa using h
example : ReciprocityTheory.ChartRestriction.G.I2.polyDeriv (MvPolynomial.monomial (Finsupp.single 0 2) 1)
    (fun i : Fin 1 => (Pi.single i 1 : Fin 1 → ℂ)) (fun z => z 0 ^ 2) 0 = 2 := by
  have h := taylor_eval (MvPolynomial.X 0 ^ 2 : MvPolynomial (Fin 1) ℂ)
  simp only [map_pow, MvPolynomial.eval_X] at h
  rw [dirPolyDeriv_monomial_eq_coeff, ← taylor_eq_taylorDir, h, MvPolynomial.coeff_coe,
    MvPolynomial.coeff_X_pow]
  simp
example : MvPowerSeries.pderiv ℂ 0 (taylor fun z : Fin 1 → ℂ => Complex.exp (z 0)) =
    taylor fun z : Fin 1 → ℂ => Complex.exp (z 0) := by
  have hd : ∀ z : Fin 1 → ℂ, HasFDerivAt (fun z : Fin 1 → ℂ => Complex.exp (z 0))
      (Complex.exp (z 0) • ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 => ℂ) 0) z :=
    fun z => (hasFDerivAt_apply 0 z).cexp
  rw [← taylor_fderiv (SCV.analyticAt_iff_eventually_differentiableAt.2
    (Eventually.of_forall fun z => (hd z).differentiableAt))]
  simp [fun z => (hd z).fderiv]
end Examples
end GlobalTheory


