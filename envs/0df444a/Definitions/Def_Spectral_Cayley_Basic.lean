-- Prove2me | Definitions.Def_Spectral_Cayley_Basic
-- name    : Spectral_Cayley_Basic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T11:52:02.770634+00:00
-- url     : https://prove2.me/theorems/97c5d48d-8d17-49d7-a014-6ae59ca9ce67
-- title:
--   Basic
-- statement:
--   Definitions and structural lemmas for Basic, from Ezzeri Esa (savarin/lean-spectral-theory; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Spectral theorem for unbounded self-adjoint operators and Stone's theorem development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/savarin/lean-spectral-theory/blob/d19e279f0ab244657f02ce678e8d67fa69e2f407/Spectral/Cayley/Basic.lean

import Mathlib.Analysis.InnerProductSpace.LinearPMap
set_option autoImplicit false
open scoped LinearPMap
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
def plusI (A : E →ₗ.[ℂ] E) : A.domain →ₗ[ℂ] E :=
  A.toFun + Complex.I • A.domain.subtype
def minusI (A : E →ₗ.[ℂ] E) : A.domain →ₗ[ℂ] E :=
  A.toFun - Complex.I • A.domain.subtype
theorem formalSelfAdjoint (A : E →ₗ.[ℂ] E) (hA : IsSelfAdjoint A) :
    A.IsFormalAdjoint A := by
  have h := LinearPMap.adjoint_isFormalAdjoint hA.dense_domain
  rw [LinearPMap.isSelfAdjoint_def.mp hA] at h
  exact h
theorem inner_apply_self_im (A : E →ₗ.[ℂ] E) (hA : IsSelfAdjoint A)
    (x : A.domain) : (inner ℂ (A x) (x : E)).im = 0 := by
  rw [← Complex.conj_eq_iff_im]
  rw [inner_conj_symm]
  exact (formalSelfAdjoint A hA x x).symm
theorem plusI_norm_sq (A : E →ₗ.[ℂ] E) (hA : IsSelfAdjoint A)
    (x : A.domain) :
    ‖plusI A x‖ ^ 2 = ‖A x‖ ^ 2 + ‖(x : E)‖ ^ 2 := by
  change ‖A x + Complex.I • (x : E)‖ ^ 2 = _
  rw [norm_add_sq (𝕜 := ℂ)]
  have hcross : RCLike.re (Complex.I * inner ℂ (A x) (x : E)) = 0 := by
    change (Complex.I * inner ℂ (A x) (x : E)).re = 0
    rw [Complex.I_mul_re, inner_apply_self_im A hA x, neg_zero]
  rw [inner_smul_right, hcross, mul_zero, add_zero, norm_smul, Complex.norm_I, one_mul]
theorem minusI_norm_sq (A : E →ₗ.[ℂ] E) (hA : IsSelfAdjoint A)
    (x : A.domain) :
    ‖minusI A x‖ ^ 2 = ‖A x‖ ^ 2 + ‖(x : E)‖ ^ 2 := by
  change ‖A x - Complex.I • (x : E)‖ ^ 2 = _
  rw [norm_sub_sq (𝕜 := ℂ)]
  have hcross : RCLike.re (Complex.I * inner ℂ (A x) (x : E)) = 0 := by
    change (Complex.I * inner ℂ (A x) (x : E)).re = 0
    rw [Complex.I_mul_re, inner_apply_self_im A hA x, neg_zero]
  rw [inner_smul_right, hcross, mul_zero, sub_zero, norm_smul, Complex.norm_I, one_mul]
theorem norm_le_plusI (A : E →ₗ.[ℂ] E) (hA : IsSelfAdjoint A)
    (x : A.domain) : ‖(x : E)‖ ≤ ‖plusI A x‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [plusI_norm_sq A hA]
  exact le_add_of_nonneg_left (sq_nonneg _)
theorem norm_le_minusI (A : E →ₗ.[ℂ] E) (hA : IsSelfAdjoint A)
    (x : A.domain) : ‖(x : E)‖ ≤ ‖minusI A x‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [minusI_norm_sq A hA]
  exact le_add_of_nonneg_left (sq_nonneg _)
theorem plusI_injective (A : E →ₗ.[ℂ] E) (hA : IsSelfAdjoint A) :
    Function.Injective (plusI A) := by
  intro x y hxy
  have hzero : plusI A (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  have hnorm : ‖((x - y : A.domain) : E)‖ ≤ 0 := by
    simpa only [hzero, norm_zero] using norm_le_plusI A hA (x - y)
  have hxy0 : (x - y : A.domain) = 0 := by
    apply Subtype.ext
    apply norm_eq_zero.mp
    exact le_antisymm hnorm (norm_nonneg _)
  exact sub_eq_zero.mp hxy0
theorem isClosed_range_plusI (A : E →ₗ.[ℂ] E) (hA : IsSelfAdjoint A) :
    IsClosed ((LinearMap.range (plusI A) : Submodule ℂ E) : Set E) := by
  rw [← isSeqClosed_iff_isClosed]
  intro y y₀ hy hylim
  choose x hx using hy
  have hyCauchy : CauchySeq y := hylim.cauchySeq
  have hdist (m n : ℕ) :
      dist ((x m : A.domain) : E) ((x n : A.domain) : E) ≤ dist (y m) (y n) := by
    rw [dist_eq_norm, dist_eq_norm]
    calc
      ‖(((x m - x n : A.domain) : E))‖ ≤ ‖plusI A (x m - x n)‖ :=
        norm_le_plusI A hA (x m - x n)
      _ = ‖y m - y n‖ := by rw [map_sub, hx m, hx n]
  have hxCauchy : CauchySeq (fun n => ((x n : A.domain) : E)) := by
    rw [Metric.cauchySeq_iff] at hyCauchy ⊢
    intro ε hε
    obtain ⟨N, hN⟩ := hyCauchy ε hε
    exact ⟨N, fun m hm n hn => (hdist m n).trans_lt (hN m hm n hn)⟩
  obtain ⟨x₀, hxlim⟩ := cauchySeq_tendsto_of_complete hxCauchy
  have hIlim :
      Filter.Tendsto (fun n => Complex.I • ((x n : A.domain) : E)) Filter.atTop
        (nhds (Complex.I • x₀)) :=
    tendsto_const_nhds.smul hxlim
  have hAlim : Filter.Tendsto (fun n => A (x n)) Filter.atTop
      (nhds (y₀ - Complex.I • x₀)) := by
    have heq : (fun n => A (x n)) =
        (fun n => y n - Complex.I • ((x n : A.domain) : E)) := by
      funext n
      rw [← hx n]
      change A (x n) = (A (x n) + Complex.I • ((x n : A.domain) : E)) -
        Complex.I • ((x n : A.domain) : E)
      rw [add_sub_cancel_right]
    rw [heq]
    exact hylim.sub hIlim
  have hgraph : (x₀, y₀ - Complex.I • x₀) ∈ A.graph := by
    apply hA.isClosed.mem_of_tendsto (hxlim.prodMk_nhds hAlim)
    exact Filter.Eventually.of_forall fun n => A.mem_graph (x n)
  rw [LinearPMap.mem_graph_iff] at hgraph
  obtain ⟨x₀', hx₀', hAx₀'⟩ := hgraph
  refine ⟨x₀', ?_⟩
  change A x₀' + Complex.I • (x₀' : E) = y₀
  rw [hAx₀', hx₀', sub_add_cancel]
theorem orthogonal_range_plusI_eq_bot (A : E →ₗ.[ℂ] E)
    (hA : IsSelfAdjoint A) : (LinearMap.range (plusI A))ᗮ = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro y hy
  have hyOrth := (LinearMap.range (plusI A)).mem_orthogonal' y |>.mp hy
  have hwitness (x : A.domain) :
      inner ℂ (Complex.I • y) (x : E) = inner ℂ y (A x) := by
    have hzero := hyOrth (plusI A x) (LinearMap.mem_range.mpr ⟨x, rfl⟩)
    change inner ℂ y (A x + Complex.I • (x : E)) = 0 at hzero
    rw [inner_add_right, inner_smul_right] at hzero
    rw [inner_smul_left, Complex.conj_I]
    linear_combination -hzero
  have hyAdj : y ∈ A†.domain :=
    LinearPMap.mem_adjoint_domain_of_exists y ⟨Complex.I • y, hwitness⟩
  have hyDom : y ∈ A.domain := by
    rw [← LinearPMap.isSelfAdjoint_def.mp hA]
    exact hyAdj
  let yDom : A.domain := ⟨y, hyDom⟩
  have hAy : A yDom = Complex.I • y := by
    apply hA.dense_domain.eq_of_inner_left ℂ
    intro x hx
    let xDom : A.domain := ⟨x, hx⟩
    calc
      inner ℂ (A yDom) x = inner ℂ y (A xDom) := formalSelfAdjoint A hA yDom xDom
      _ = inner ℂ (Complex.I • y) x := (hwitness xDom).symm
  have hminus : minusI A yDom = 0 := by
    change A yDom - Complex.I • y = 0
    rw [hAy, sub_self]
  have hynorm : ‖y‖ ≤ 0 := by
    simpa only [hminus, norm_zero] using norm_le_minusI A hA yDom
  exact norm_eq_zero.mp (le_antisymm hynorm (norm_nonneg _))
theorem plusI_surjective (A : E →ₗ.[ℂ] E) (hA : IsSelfAdjoint A) :
    Function.Surjective (plusI A) := by
  let K : Submodule ℂ E := LinearMap.range (plusI A)
  have hclosed : IsClosed (K : Set E) := isClosed_range_plusI A hA
  have horth : Kᗮ = ⊥ := orthogonal_range_plusI_eq_bot A hA
  have hclosure : K.topologicalClosure = ⊤ := by
    rw [← K.orthogonal_orthogonal_eq_closure, horth, Submodule.bot_orthogonal_eq_top]
  have htop : K = ⊤ := by
    calc
      K = K.topologicalClosure := hclosed.submodule_topologicalClosure_eq.symm
      _ = ⊤ := hclosure
  intro y
  apply LinearMap.mem_range.mp
  change y ∈ K
  rw [htop]
  exact Submodule.mem_top
noncomputable def cayleyLinearMap (A : E →ₗ.[ℂ] E)
    (hA : IsSelfAdjoint A) : E →ₗ[ℂ] E :=
  let e := LinearEquiv.ofBijective (plusI A) ⟨plusI_injective A hA, plusI_surjective A hA⟩
  (minusI A).comp e.symm.toLinearMap
theorem cayleyLinearMap_norm_le (A : E →ₗ.[ℂ] E)
    (hA : IsSelfAdjoint A) (y : E) : ‖cayleyLinearMap A hA y‖ ≤ 1 * ‖y‖ := by
  let e := LinearEquiv.ofBijective (plusI A) ⟨plusI_injective A hA, plusI_surjective A hA⟩
  let x : A.domain := e.symm y
  have hplus : plusI A x = y := by
    change e x = y
    exact e.apply_symm_apply y
  have hnorm : ‖minusI A x‖ = ‖plusI A x‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [minusI_norm_sq A hA, plusI_norm_sq A hA]
  change ‖minusI A x‖ ≤ 1 * ‖y‖
  rw [hnorm, hplus, one_mul]
noncomputable def cayleyTransform
    (A : E →ₗ.[ℂ] E) (hA : IsSelfAdjoint A) : E →L[ℂ] E :=
  (cayleyLinearMap A hA).mkContinuous 1 (cayleyLinearMap_norm_le A hA)


