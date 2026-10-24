-- Prove2me | Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Resolvent_Basic
-- name    : KLS408915f_FunctionalInequalities_Analysis_Semigroup_Resolvent_Basic
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-23T12:11:14.958644+00:00
-- url     : https://prove2.me/theorems/b9780155-dc96-4512-be19-c4062bc50371
-- title:
--   Existence and construction of the weak resolvent
-- statement:
--   For a closed partial operator $T:H_0\to H_1$ and $s>0$, `weakResolvent_unique` gives uniqueness of a solution to the weak resolvent equation, while `exists_weakResolvent` and `existsUnique_weakResolvent` give existence and unique existence for every datum $f\in H_0$. The auxiliary definitions `rescale` and `scaledGraphL2` represent the graph of $T$ after scaling the second coordinate by $(\sqrt{s})^{-1}$; `resolventDomain` selects the unique solution and `resolventLinear` and `resolventCLM` package it as a linear and continuous linear map. The resulting resolvent is contractive and symmetric through `norm_resolventCLM_le` and `resolventCLM_symm`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Semigroup/Resolvent/Basic.lean#L37-L258 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Semigroup.Resolvent.Basic`, definition bundle `KLS408915f_FunctionalInequalities_Analysis_Semigroup_Resolvent_Basic`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Semigroup_Resolvent_Form
import Mathlib.Analysis.InnerProductSpace.LaxMilgram
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Analysis.InnerProductSpace.ProdL2

noncomputable section
open InnerProductSpace
open scoped RealInnerProductSpace
namespace FunctionalInequalities
namespace Analysis
namespace Semigroup
variable {H₀ H₁ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
  [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
omit [CompleteSpace H₀] [CompleteSpace H₁] in
/-- resolvent solvability, uniqueness half: the weak resolvent equation has at most one solution.

The difference of two solutions is tested against itself, giving `‖w‖² + s ‖T w‖² = 0`; strict
positivity of `s` is not even needed for the norm to vanish, but it is kept to match the route.
No closedness, density or Lax–Milgram input is used. -/
theorem weakResolvent_unique {T : H₀ →ₗ.[ℝ] H₁} {s : ℝ} (hs : 0 < s) {f : H₀} {u₁ u₂ : T.domain}
    (h₁ : WeakResolvent T s f u₁) (h₂ : WeakResolvent T s f u₂) : u₁ = u₂ := by
  have hTsub : T (u₁ - u₂) = T u₁ - T u₂ := T.map_sub u₁ u₂
  have key : ‖((u₁ - u₂ : T.domain) : H₀)‖ ^ 2 + s * ‖T (u₁ - u₂)‖ ^ 2 = 0 := by
    have e := hTsub
    have h := h₁ (u₁ - u₂)
    have h' := h₂ (u₁ - u₂)
    have hcoe : ((u₁ - u₂ : T.domain) : H₀) = (u₁ : H₀) - (u₂ : H₀) := rfl
    have expand : ⟪((u₁ - u₂ : T.domain) : H₀), ((u₁ - u₂ : T.domain) : H₀)⟫
        + s * ⟪T (u₁ - u₂), T (u₁ - u₂)⟫ = 0 := by
      rw [hcoe, e] at h h' ⊢
      simp only [inner_sub_left, inner_sub_right] at h h' ⊢
      linarith
    rwa [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at expand
  have hw : ‖((u₁ - u₂ : T.domain) : H₀)‖ = 0 := by
    nlinarith [sq_nonneg ‖((u₁ - u₂ : T.domain) : H₀)‖, sq_nonneg ‖T (u₁ - u₂)‖,
      norm_nonneg ((u₁ - u₂ : T.domain) : H₀)]
  have : (u₁ : H₀) - (u₂ : H₀) = 0 := by
    have := norm_eq_zero.mp hw
    simpa using this
  exact Subtype.ext (sub_eq_zero.mp this)
/-- The second coordinate rescaled by `(√s)⁻¹`, used to present the rescaled graph as a preimage. -/
def rescale (s : ℝ) : WithLp 2 (H₀ × H₁) →L[ℝ] (H₀ × H₁) :=
  ((ContinuousLinearMap.id ℝ H₀).prodMap ((Real.sqrt s)⁻¹ • ContinuousLinearMap.id ℝ H₁)).comp
    ((WithLp.prodContinuousLinearEquiv 2 ℝ H₀ H₁) : WithLp 2 (H₀ × H₁) →L[ℝ] (H₀ × H₁))
omit [CompleteSpace H₀] [CompleteSpace H₁] in
@[simp] theorem rescale_apply (s : ℝ) (z : WithLp 2 (H₀ × H₁)) :
    rescale s z = ((WithLp.ofLp z).1, (Real.sqrt s)⁻¹ • (WithLp.ofLp z).2) := rfl
/-- The graph of `√s • T`, inside the `L²` product. -/
def scaledGraphL2 (T : H₀ →ₗ.[ℝ] H₁) (s : ℝ) : Submodule ℝ (WithLp 2 (H₀ × H₁)) :=
  T.graph.comap (rescale s).toLinearMap
omit [CompleteSpace H₀] [CompleteSpace H₁] in
theorem toLp_mem_scaledGraphL2 (T : H₀ →ₗ.[ℝ] H₁) {s : ℝ} (hs : 0 < s) (u : T.domain) :
    (WithLp.toLp 2 ((u : H₀), Real.sqrt s • T u)) ∈ scaledGraphL2 T s := by
  have hne : Real.sqrt s ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hs)
  simp only [scaledGraphL2, Submodule.mem_comap, ContinuousLinearMap.coe_coe, rescale_apply,
    inv_smul_smul₀ hne]
  exact T.mem_graph u
omit [CompleteSpace H₀] [CompleteSpace H₁] in
theorem exists_of_mem_scaledGraphL2 {T : H₀ →ₗ.[ℝ] H₁} {s : ℝ} (hs : 0 < s)
    {z : WithLp 2 (H₀ × H₁)} (hz : z ∈ scaledGraphL2 T s) :
    ∃ u : T.domain, (WithLp.ofLp z).1 = (u : H₀) ∧ (WithLp.ofLp z).2 = Real.sqrt s • T u := by
  have hne : Real.sqrt s ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hs)
  simp only [scaledGraphL2, Submodule.mem_comap, ContinuousLinearMap.coe_coe, rescale_apply] at hz
  obtain ⟨u, hu1, hu2⟩ := T.mem_graph_iff.mp hz
  dsimp only at hu1 hu2
  exact ⟨u, hu1.symm, by rw [hu2]; exact (smul_inv_smul₀ hne _).symm⟩
omit [CompleteSpace H₀] [CompleteSpace H₁] in
/-- The rescaled graph of a closed operator is closed. -/
theorem isClosed_scaledGraphL2 (T : H₀ →ₗ.[ℝ] H₁) (s : ℝ) (hT : T.IsClosed) :
    IsClosed ((scaledGraphL2 T s : Submodule ℝ (WithLp 2 (H₀ × H₁))) : Set (WithLp 2 (H₀ × H₁))) :=
  hT.preimage (rescale s).continuous
/-- The rescaled graph of a closed operator is a Hilbert space. -/
theorem completeSpace_scaledGraphL2 (T : H₀ →ₗ.[ℝ] H₁) (s : ℝ) (hT : T.IsClosed) :
    CompleteSpace (scaledGraphL2 T s) :=
  (isClosed_scaledGraphL2 T s hT).completeSpace_coe
/-- resolvent solvability, existence half: the weak resolvent equation has a solution.

The solution is the orthogonal projection of `(f, 0)` onto the rescaled graph; density of the
domain is **not** needed, only closedness. -/
theorem exists_weakResolvent (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed) {s : ℝ} (hs : 0 < s) (f : H₀) :
    ∃ u : T.domain, WeakResolvent T s f u := by
  have hcs : CompleteSpace (scaledGraphL2 T s) := completeSpace_scaledGraphL2 T s hT
  set K := scaledGraphL2 T s with hKdef
  set x : WithLp 2 (H₀ × H₁) := WithLp.toLp 2 (f, (0 : H₁)) with hxdef
  have hgK : K.starProjection x ∈ K := K.starProjection_apply_mem x
  obtain ⟨u, hu1, hu2⟩ := exists_of_mem_scaledGraphL2 hs hgK
  refine ⟨u, fun v => ?_⟩
  have hv : (WithLp.toLp 2 ((v : H₀), Real.sqrt s • T v)) ∈ K := toLp_mem_scaledGraphL2 T hs v
  have h0 := K.starProjection_inner_eq_zero x _ hv
  rw [inner_sub_left] at h0
  simp only [WithLp.prod_inner_apply, hxdef] at h0
  rw [hu1, hu2] at h0
  simp only [inner_zero_left, real_inner_smul_left, real_inner_smul_right] at h0
  have hprod : Real.sqrt s * (Real.sqrt s * ⟪T u, T v⟫) = s * ⟪T u, T v⟫ := by
    rw [← mul_assoc, Real.mul_self_sqrt hs.le]
  linarith [h0, hprod]
/-- resolvent solvability: the weak resolvent equation is uniquely solvable for every datum. -/
theorem existsUnique_weakResolvent (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed) {s : ℝ} (hs : 0 < s)
    (f : H₀) : ∃! u : T.domain, WeakResolvent T s f u := by
  obtain ⟨u, hu⟩ := exists_weakResolvent T hT hs f
  exact ⟨u, hu, fun u' hu' => weakResolvent_unique hs hu' hu⟩
section ResolventOperator
variable (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed) {s : ℝ} (hs : 0 < s)
/-- The solution of the weak resolvent equation, as an element of the domain. -/
def resolventDomain (f : H₀) : T.domain :=
  (existsUnique_weakResolvent T hT hs f).choose
theorem resolventDomain_spec (f : H₀) : WeakResolvent T s f (resolventDomain T hT hs f) :=
  (existsUnique_weakResolvent T hT hs f).choose_spec.1
theorem eq_resolventDomain {f : H₀} {u : T.domain} (hu : WeakResolvent T s f u) :
    u = resolventDomain T hT hs f :=
  (existsUnique_weakResolvent T hT hs f).choose_spec.2 u hu
/-- The resolvent as a linear map: additivity and homogeneity both come from uniqueness. -/
def resolventLinear : H₀ →ₗ[ℝ] H₀ where
  toFun f := (resolventDomain T hT hs f : H₀)
  map_add' f g := by
    have hsum : WeakResolvent T s (f + g)
        (resolventDomain T hT hs f + resolventDomain T hT hs g) := by
      intro v
      have h₁ := resolventDomain_spec T hT hs f v
      have h₂ := resolventDomain_spec T hT hs g v
      have hT' : T (resolventDomain T hT hs f + resolventDomain T hT hs g)
          = T (resolventDomain T hT hs f) + T (resolventDomain T hT hs g) := T.map_add _ _
      have hc : ((resolventDomain T hT hs f + resolventDomain T hT hs g : T.domain) : H₀)
          = (resolventDomain T hT hs f : H₀) + (resolventDomain T hT hs g : H₀) := rfl
      rw [hc, hT']
      simp only [inner_add_left]
      linear_combination h₁ + h₂
    rw [← eq_resolventDomain T hT hs hsum]
    simp
  map_smul' c f := by
    have hsmul : WeakResolvent T s (c • f) (c • resolventDomain T hT hs f) := by
      intro v
      have h₁ := resolventDomain_spec T hT hs f v
      have hT' : T (c • resolventDomain T hT hs f) = c • T (resolventDomain T hT hs f) :=
        T.map_smul c _
      have hc : ((c • resolventDomain T hT hs f : T.domain) : H₀)
          = c • (resolventDomain T hT hs f : H₀) := rfl
      rw [hc, hT']
      simp only [real_inner_smul_left]
      linear_combination c * h₁
    rw [← eq_resolventDomain T hT hs hsmul]
    simp
/-- The resolvent `J_s = (1 + s T*T)⁻¹`, as a contraction of the ambient space. -/
def resolventCLM : H₀ →L[ℝ] H₀ :=
  (resolventLinear T hT hs).mkContinuous 1 fun f => by
    simpa [resolventLinear] using norm_le_of_weakResolvent hs (resolventDomain_spec T hT hs f)
@[simp] theorem resolventCLM_apply (f : H₀) :
    resolventCLM T hT hs f = (resolventDomain T hT hs f : H₀) := rfl
/-- `J_s` is a contraction. -/
theorem norm_resolventCLM_le (f : H₀) : ‖resolventCLM T hT hs f‖ ≤ ‖f‖ :=
  norm_le_of_weakResolvent hs (resolventDomain_spec T hT hs f)
/-- `J_s` is self-adjoint: the form is symmetric, so the two test identities have equal left
sides. -/
theorem resolventCLM_symm (f g : H₀) :
    ⟪resolventCLM T hT hs f, g⟫ = ⟪f, resolventCLM T hT hs g⟫ := by
  have h₁ := resolventDomain_spec T hT hs f (resolventDomain T hT hs g)
  have h₂ := resolventDomain_spec T hT hs g (resolventDomain T hT hs f)
  have c₁ : ⟪(resolventDomain T hT hs f : H₀), (resolventDomain T hT hs g : H₀)⟫
      = ⟪(resolventDomain T hT hs g : H₀), (resolventDomain T hT hs f : H₀)⟫ := real_inner_comm _ _
  have c₂ : ⟪T (resolventDomain T hT hs f), T (resolventDomain T hT hs g)⟫
      = ⟪T (resolventDomain T hT hs g), T (resolventDomain T hT hs f)⟫ := real_inner_comm _ _
  have c₃ : ⟪g, (resolventDomain T hT hs f : H₀)⟫
      = ⟪(resolventDomain T hT hs f : H₀), g⟫ := real_inner_comm _ _
  rw [← c₁, ← c₂] at h₂
  simp only [resolventCLM_apply]
  linarith
end ResolventOperator
end Semigroup
end Analysis
end FunctionalInequalities


