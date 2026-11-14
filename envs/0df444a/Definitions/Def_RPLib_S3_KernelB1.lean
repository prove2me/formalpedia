-- Prove2me | Definitions.Def_RPLib_S3_KernelB1
-- name    : RPLib_S3_KernelB1
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-13T20:55:31.510847+00:00
-- url     : https://prove2.me/theorems/15fe75da-65a5-4dbe-858f-fbef04a6e618
-- title:
--   The Eichler-Selberg trace formula, kernel part B1: unfolding and the reproducing identity
-- statement:
--   For $M \ge 3$: unfolding $\int_{\Gamma_1(M) \backslash \mathbb{H}} \sum_{\gamma \in \Gamma_1(M)} \Phi(\gamma z) = \int_{\mathbb{H}} \Phi$ for integrable $\Phi$, and, for coset representatives $\alpha_i$ of $\Gamma_1(M) \backslash \Delta$, the Petersson product of $\omega(\cdot, -\bar w)$ with a cusp form $f$ as $\sum_i (a_i - c_i w)^{-k} f(\operatorname{adj}(\alpha_i) w)$ times the Bergman constant.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture (trace-formula layer: the Eichler-Selberg trace formula on $S_k(\Gamma_1(M))$ for $k \ge 3$, proved by Zagier's kernel method). It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   D. Zagier, The Eichler-Selberg trace formula on SL2(Z), appendix to S. Lang, Introduction to Modular Forms, Grundlehren 222, Springer 1976 (with the Correction in later printings); F. Diamond and J. Shurman, A First Course in Modular Forms, GTM 228, Springer 2005, doi:10.1007/978-0-387-27226-9, Section 5.4

import Mathlib
import Definitions.Def_RPLib_S3_KernelA2
import Definitions.Def_RPLib_S1_PeterssonInner
import Definitions.Def_RPLib_S1_Hecke
import Definitions.Def_RPLib_S3_Bergman

/-!
# S3-Kernel, part B1: unfolding and the reproducing identity (abstract coset representatives)

* `integral_fdom_tsum` (`M ≥ 3`): `∫_{fdom Γ₁(M)} Σ'_{γ ∈ Γ₁(M)} Φ(γ z) = ∫_ℍ Φ` for integrable `Φ`;
* `integral_term`: the Bergman step for one matrix `α` of positive determinant;
* `reproducing_abstract`: for representatives `α_i` with `Γ₁(M) × I ≃ Δ^{(δ')}_n(M)`,
  `⟪ω(·, -conj w), f⟫ = bergmanConst k * Σ_i (a_i - c_i w)^(-k) f(adj α_i · w)`.
-/

open Filter Complex UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups Topology Manifold ComplexConjugate

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.Kernel

open RP.FundDomain RP.Petersson RamanujanPetersson.Bergman RamanujanPetersson.Diamond
  RamanujanPetersson.Hecke

attribute [local instance] measurableConstSMul_pgl smulInvariantMeasure_pgl
  smulInvariantMeasure_subgroup

/-! ### (i) Unfolding over `Γ₁(M)`, `M ≥ 3` -/

lemma neg_not_mem_Gamma1 {M : ℕ} (hM : 3 ≤ M) {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma1 M) :
    -γ ∉ Gamma1 M := by
  intro h
  have h1 := ((Gamma1_mem M γ).1 hγ).1
  have h2 := ((Gamma1_mem M (-γ)).1 h).1
  have e : ((-γ : SL(2, ℤ)) 0 0 : ℤ) = -(γ 0 0) := by simp
  rw [e, Int.cast_neg, h1] at h2
  have h3 : ((2 : ℕ) : ZMod M) = 0 := by
    have e2 : ((2 : ℕ) : ZMod M) = 1 - (-1) := by push_cast; ring
    rw [e2, h2, sub_self]
  rw [ZMod.natCast_eq_zero_iff] at h3
  have := Nat.le_of_dvd (by norm_num) h3
  omega

/-- `Γ₁(M) ≅ its image in PGL(2, ℝ)` for `M ≥ 3`. -/
def gammaPGL (M : ℕ) (hM : 3 ≤ M) :
    Gamma1 M ≃ pglImage ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) :=
  Equiv.ofBijective (fun γ => ⟨toPGLR γ, toPGLR_mem_pglImage γ.2⟩) (by
    constructor
    · intro x y hxy
      have h : toPGLR (x : SL(2, ℤ)) = toPGLR (y : SL(2, ℤ)) := congrArg Subtype.val hxy
      rcases (toPGLR_eq_toPGLR_iff _ _).1 h with h' | h'
      · exact Subtype.ext h'
      · exfalso
        have hx : -(y : SL(2, ℤ)) ∈ Gamma1 M := by rw [← h']; exact x.2
        exact neg_not_mem_Gamma1 hM y.2 hx
    · rintro ⟨g, hg⟩
      obtain ⟨γ, hγ, rfl⟩ := mem_pglImage_coe.1 hg
      exact ⟨⟨γ, hγ⟩, rfl⟩)

lemma gammaPGL_smul {M : ℕ} (hM : 3 ≤ M) (γ : Gamma1 M) (z : ℍ) :
    (gammaPGL M hM γ) • z = (γ : SL(2, ℤ)) • z :=
  toPGLR_smul _ _

/-- **Unfolding.** -/
theorem integral_fdom_tsum {M : ℕ} (hM : 3 ≤ M) {Φ : ℍ → ℂ} (hΦ : Integrable Φ) :
    ∫ z in fdom (Gamma1 M), ∑' γ : Gamma1 M, Φ ((γ : SL(2, ℤ)) • z) = ∫ z, Φ z := by
  have := countable_SL2Z
  have hc := countable_pglImage_coe (Gamma1 M)
  have hF := isFundamentalDomain_fdom (Gamma1 M)
  have hmeas : ∀ γ : Gamma1 M, AEStronglyMeasurable (fun z => Φ ((γ : SL(2, ℤ)) • z))
      (volume.restrict (fdom (Gamma1 M))) := by
    intro γ
    have h1 : (fun z : ℍ => Φ ((γ : SL(2, ℤ)) • z)) = fun z => Φ (toPGLR (γ : SL(2, ℤ)) • z) := by
      funext z; rw [toPGLR_smul]
    rw [h1]
    exact (hΦ.1.comp_measurePreserving (measurePreserving_smul (toPGLR (γ : SL(2, ℤ))) volume)).restrict
  have h3 : ∑' γ : Gamma1 M, ∫⁻ z in fdom (Gamma1 M), ‖Φ ((γ : SL(2, ℤ)) • z)‖ₑ =
      ∑' g : pglImage ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)),
        ∫⁻ z in fdom (Gamma1 M), ‖Φ (g • z)‖ₑ := by
    rw [← (gammaPGL M hM).tsum_eq (fun g => ∫⁻ z in fdom (Gamma1 M), ‖Φ (g • z)‖ₑ)]
    refine tsum_congr fun γ => ?_
    simp only [gammaPGL_smul]
  have hlin : ∑' γ : Gamma1 M, ∫⁻ z in fdom (Gamma1 M), ‖Φ ((γ : SL(2, ℤ)) • z)‖ₑ ≠ ⊤ := by
    rw [h3, ← hF.lintegral_eq_tsum'' (fun z => ‖Φ z‖ₑ)]
    exact ne_of_lt hΦ.2
  rw [integral_tsum hmeas hlin, hF.integral_eq_tsum'' Φ hΦ,
    ← (gammaPGL M hM).tsum_eq (fun g => ∫ z in fdom (Gamma1 M), Φ (g • z))]
  refine tsum_congr fun γ => ?_
  simp only [gammaPGL_smul]

/-! ### (ii) The Bergman step for one matrix -/

/-- `adj g = [[d, -b], [-c, a]]`. -/
def adjM (g : Matrix (Fin 2) (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ := !![g 1 1, -g 0 1; -g 1 0, g 0 0]

lemma det_adjM (g : Matrix (Fin 2) (Fin 2) ℤ) : (adjM g).det = g.det := by
  rw [adjM, Matrix.det_fin_two_of, det_eq]; ring

/-- `adj g` in `GL(2, ℝ)` (identity if `det g = 0`). -/
def adjGL (g : Matrix (Fin 2) (Fin 2) ℤ) : GL (Fin 2) ℝ :=
  if h : g.det ≠ 0 then toGL (adjM g) (by rwa [det_adjM]) else 1

lemma adjGL_eq {g : Matrix (Fin 2) (Fin 2) ℤ} (h : g.det ≠ 0) :
    adjGL g = toGL (adjM g) (by rwa [det_adjM]) := by
  rw [adjGL, dif_pos h]

lemma adjGL_apply {g : Matrix (Fin 2) (Fin 2) ℤ} (h : g.det ≠ 0) (i j : Fin 2) :
    (adjGL g : Matrix (Fin 2) (Fin 2) ℝ) i j = (adjM g i j : ℝ) := by
  rw [adjGL_eq h, toGL_apply]

lemma det_adjGL {g : Matrix (Fin 2) (Fin 2) ℤ} (h : g.det ≠ 0) :
    (adjGL g).det.val = (g.det : ℝ) := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two (adjGL g : Matrix (Fin 2) (Fin 2) ℝ),
    adjGL_apply h, adjGL_apply h, adjGL_apply h, adjGL_apply h, det_eq]
  simp [adjM]
  all_goals ring

lemma denom_adjGL {g : Matrix (Fin 2) (Fin 2) ℤ} (h : g.det ≠ 0) (w : ℂ) :
    denom (adjGL g) w = (g 0 0 : ℂ) - (g 1 0 : ℂ) * w := by
  rw [denom, adjGL_apply h, adjGL_apply h]
  simp [adjM]
  all_goals ring

/-- The point `adj g · w`. -/
def adjPt (g : Matrix (Fin 2) (Fin 2) ℤ) (w : ℍ) : ℍ := adjGL g • w

lemma coe_adjPt {g : Matrix (Fin 2) (Fin 2) ℤ} (h : 0 < g.det) (w : ℍ) :
    (adjPt g w : ℂ) = ((g 1 1 : ℂ) * w - (g 0 1 : ℂ)) / ((g 0 0 : ℂ) - (g 1 0 : ℂ) * w) := by
  have h0 : g.det ≠ 0 := ne_of_gt h
  have hd : 0 < (adjGL g).det.val := by rw [det_adjGL h0]; exact_mod_cast h
  rw [adjPt, coe_smul_of_det_pos hd w, denom_adjGL h0, num, adjGL_apply h0, adjGL_apply h0]
  simp [adjM]
  all_goals ring

lemma denom_adj_ne {g : Matrix (Fin 2) (Fin 2) ℤ} (h : 0 < g.det) (w : ℍ) :
    (g 0 0 : ℂ) - (g 1 0 : ℂ) * w ≠ 0 := by
  rw [← denom_adjGL (ne_of_gt h)]
  exact denom_ne_zero _ w

/-- `Q(α; z, -conj w) = conj(a - c w) (z - conj(adj α · w))`. -/
lemma Q_negConj (g : Matrix (Fin 2) (Fin 2) ℤ) (z w : ℂ) (hD : (g 0 0 : ℂ) - (g 1 0 : ℂ) * w ≠ 0) :
    Q g z (-conj w) = conj ((g 0 0 : ℂ) - (g 1 0 : ℂ) * w) *
      (z - conj (((g 1 1 : ℂ) * w - (g 0 1 : ℂ)) / ((g 0 0 : ℂ) - (g 1 0 : ℂ) * w))) := by
  have hD' : conj ((g 0 0 : ℂ) - (g 1 0 : ℂ) * w) ≠ 0 := (map_ne_zero _).2 hD
  rw [map_div₀, mul_sub, mul_div_assoc', mul_div_cancel_left₀ _ hD']
  simp only [map_sub, map_mul, map_intCast, Q]
  ring

/-- The unfolded integrand for one matrix. -/
def PhiA (k : ℕ) (g : Matrix (Fin 2) (Fin 2) ℤ) (f : ℍ → ℂ) (w : ℍ) (z : ℍ) : ℂ :=
  conj ((Q g z (-conj (w : ℂ)) ^ k)⁻¹) * f z * ((z.im : ℂ) ^ k)

lemma PhiA_eq (k : ℕ) {g : Matrix (Fin 2) (Fin 2) ℤ} (h : 0 < g.det) (f : ℍ → ℂ) (w : ℍ) (z : ℍ) :
    PhiA k g f w z = ((((g 0 0 : ℂ) - (g 1 0 : ℂ) * w) ^ k)⁻¹) *
      (f z * conj ((((z : ℂ) - conj (adjPt g w : ℂ)) ^ k)⁻¹) * ((z.im : ℂ) ^ k)) := by
  have hD := denom_adj_ne h w
  have e1 : conj ((Q g z (-conj (w : ℂ)) ^ k)⁻¹) =
      ((((g 0 0 : ℂ) - (g 1 0 : ℂ) * w) ^ k)⁻¹) * conj ((((z : ℂ) - conj (adjPt g w : ℂ)) ^ k)⁻¹) := by
    rw [Q_negConj g z w hD, ← coe_adjPt h w, mul_pow, mul_inv, map_mul]
    congr 1
    rw [map_inv₀, map_pow, Complex.conj_conj]
  rw [PhiA, e1]
  ring

/-- **The Bergman step.** -/
theorem integral_term {M k : ℕ} [NeZero M] (hk : 3 ≤ k) (f : S1 M k) {g : Matrix (Fin 2) (Fin 2) ℤ}
    (h : 0 < g.det) (w : ℍ) :
    Integrable (PhiA k g f w) ∧ ∫ z, PhiA k g f w z =
      ((((g 0 0 : ℂ) - (g 1 0 : ℂ) * w) ^ k)⁻¹) * (bergmanConst k * f (adjPt g w)) := by
  obtain ⟨C, hC⟩ := CuspFormClass.exists_bound f
  have hC' : ∀ z : ℍ, ‖f z‖ ≤ C / z.im ^ ((k : ℝ) / 2) := fun z => by
    have hz := hC z
    rwa [Int.cast_natCast] at hz
  have hholo : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (f : ℍ → ℂ) := CuspFormClass.holo f
  have hfun : PhiA k g f w = fun z => ((((g 0 0 : ℂ) - (g 1 0 : ℂ) * w) ^ k)⁻¹) *
      (f z * conj ((((z : ℂ) - conj (adjPt g w : ℂ)) ^ k)⁻¹) * ((z.im : ℂ) ^ k)) := by
    funext z; exact PhiA_eq k h f w z
  rw [hfun]
  refine ⟨(integrable_reproducing_of_bound hk hholo.continuous (adjPt g w) hC').const_mul _, ?_⟩
  rw [integral_const_mul, bergman_reproducing_of_bound hk hholo (adjPt g w) hC']

/-! ### (iii) Abstract representatives and the reproducing identity -/

/-- `(γ, i) ↦ α_i γ`. -/
def repMap {M : ℕ} {n : ℤ} {δ' : ZMod M} {I : Type*} (α : I → Matrix (Fin 2) (Fin 2) ℤ)
    (hα : ∀ i, α i ∈ DeltaSet M n δ') (p : Gamma1 M × I) : DeltaSet M n δ' :=
  ⟨α p.2 * ((p.1 : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ), mul_mem_DeltaSet (hα p.2) p.1.2⟩

lemma term_unfold {M k : ℕ} (f : S1 M k) (g : Matrix (Fin 2) (Fin 2) ℤ) {γ : SL(2, ℤ)}
    (hγ : γ ∈ Gamma1 M) (z : ℍ) (w : ℂ) :
    conj ((Q (g * (γ : Matrix (Fin 2) (Fin 2) ℤ)) z w ^ k)⁻¹) * f z * ((z.im : ℂ) ^ k) =
      conj ((Q g ((γ • z : ℍ) : ℂ) w ^ k)⁻¹) * f (γ • z) * (((γ • z).im : ℂ) ^ k) := by
  have hJ : denom γ z ≠ 0 := denom_ne_zero _ z
  have hJc : conj (denom γ z) ≠ 0 := (map_ne_zero _).2 hJ
  have hf : f (γ • z) = f z * denom γ z ^ k := by
    have h := congrFun (slash_Gamma1 (k : ℤ) f hγ) z
    rw [SL_slash_apply, zpow_neg, zpow_natCast] at h
    rw [← h, inv_mul_cancel_right₀ (pow_ne_zero _ hJ)]
  have him : (((γ • z).im : ℝ) : ℂ) = ((z.im : ℝ) : ℂ) / (denom γ z * conj (denom γ z)) := by
    rw [Complex.mul_conj, ModularGroup.im_smul_eq_div_normSq, Complex.ofReal_div]
  rw [← Q_smul g γ z w, mul_pow, mul_inv, map_mul, map_inv₀ (starRingEnd ℂ) (denom γ z ^ k), map_pow,
    hf, him]
  generalize conj ((Q g ((γ • z : ℍ) : ℂ) w ^ k)⁻¹) = A
  have hX : denom γ z ^ k * (denom γ z ^ k)⁻¹ = 1 := mul_inv_cancel₀ (pow_ne_zero _ hJ)
  rw [div_pow, mul_pow]
  linear_combination (-(A * f z * ((z.im : ℂ) ^ k) * (conj (denom γ z) ^ k)⁻¹)) * hX

lemma petersson_nat (k : ℕ) (h f : ℍ → ℂ) (z : ℍ) :
    petersson (k : ℤ) h f z = conj (h z) * f z * ((z.im : ℂ) ^ k) := by
  simp only [petersson, zpow_natCast]

/-- Pointwise unfolding of the Petersson integrand. -/
theorem petersson_omega_eq_tsum {M k : ℕ} [NeZero M] {n : ℤ} (hn : 0 < n) {δ' : ZMod M} (hk : 3 ≤ k)
    {I : Type*} [Fintype I] (α : I → Matrix (Fin 2) (Fin 2) ℤ) (hα : ∀ i, α i ∈ DeltaSet M n δ')
    (hbij : Function.Bijective (repMap α hα)) (f : S1 M k) (w z : ℍ) :
    petersson (k : ℤ) (omegaH M k n δ' (-conj (w : ℂ))) f z =
      ∑' γ : Gamma1 M, ∑ i, PhiA k (α i) f w ((γ : SL(2, ℤ)) • z) := by
  have hv : 0 < (-conj (w : ℂ)).im := by simpa using w.im_pos
  have hs : Summable fun g : DeltaSet M n δ' =>
      conj ((Q g.1 z (-conj (w : ℂ)) ^ k)⁻¹) * (f z * ((z.im : ℂ) ^ k)) :=
    (Complex.summable_conj.2 (summable_omega M k hn δ' hk (z := (z : ℂ)) (w := -conj (w : ℂ))
      z.im_pos hv)).mul_right _
  have hs' : Summable fun p : Gamma1 M × I =>
      conj ((Q (Equiv.ofBijective (repMap α hα) hbij p).1 z (-conj (w : ℂ)) ^ k)⁻¹) *
        (f z * ((z.im : ℂ) ^ k)) :=
    ((Equiv.ofBijective (repMap α hα) hbij).summable_iff (f := fun g : DeltaSet M n δ' =>
      conj ((Q g.1 z (-conj (w : ℂ)) ^ k)⁻¹) * (f z * ((z.im : ℂ) ^ k)))).2 hs
  rw [petersson_nat, mul_assoc]
  simp only [omegaH, omega]
  rw [Complex.conj_tsum, ← tsum_mul_right,
    ← (Equiv.ofBijective (repMap α hα) hbij).tsum_eq (fun g : DeltaSet M n δ' =>
      conj ((Q g.1 z (-conj (w : ℂ)) ^ k)⁻¹) * (f z * ((z.im : ℂ) ^ k))), hs'.tsum_prod]
  refine tsum_congr fun γ => ?_
  rw [tsum_fintype]
  refine Finset.sum_congr rfl fun i _ => ?_
  have e := term_unfold (k := k) f (α i) γ.2 z (-conj (w : ℂ))
  simp only [Equiv.ofBijective_apply, repMap]
  rw [← mul_assoc, e]
  rfl

/-- **Reproducing identity with abstract representatives** (`M ≥ 3`, `k ≥ 3`, `n > 0`). -/
theorem reproducing_abstract {M k : ℕ} [NeZero M] (hM : 3 ≤ M) {n : ℤ} (hn : 0 < n) {δ' : ZMod M}
    (hk : 3 ≤ k) {I : Type*} [Fintype I] (α : I → Matrix (Fin 2) (Fin 2) ℤ)
    (hα : ∀ i, α i ∈ DeltaSet M n δ') (hbij : Function.Bijective (repMap α hα)) (f : S1 M k) (w : ℍ) :
    peterssonInner (Gamma1 M) k (omegaH M k n δ' (-conj (w : ℂ))) f =
      bergmanConst k * ∑ i, ((((α i 0 0 : ℂ) - (α i 1 0 : ℂ) * w) ^ k)⁻¹) * f (adjPt (α i) w) := by
  have hpos : ∀ i, 0 < (α i).det := fun i => by rw [(mem_DeltaSet.1 (hα i)).1]; exact hn
  have hint : Integrable (fun z => ∑ i, PhiA k (α i) f w z) :=
    integrable_finsetSum _ fun i _ => (integral_term hk f (hpos i) w).1
  rw [peterssonInner]
  simp_rw [petersson_omega_eq_tsum hn hk α hα hbij f w]
  rw [integral_fdom_tsum hM hint, integral_finsetSum _ fun i _ => (integral_term hk f (hpos i) w).1,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [(integral_term hk f (hpos i) w).2]
  ring

end RamanujanPetersson.Kernel


