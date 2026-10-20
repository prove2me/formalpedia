-- Prove2me | Definitions.Def_OAI_Analysis_LipschitzEquivalence_FiniteApproximants
-- name    : OAI_Analysis_LipschitzEquivalence_FiniteApproximants
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T17:43:37.407553+00:00
-- url     : https://prove2.me/theorems/9dae0794-71e5-432e-ac58-85ff8791105f
-- title:
--   Finite approximants of moving-slot maps are bi-Lipschitz bijections
-- statement:
--   Properties of the approximants $\Phi_N$ of a moving-slot map $\Phi$ on $\mathcal D=\mathcal H\oplus_2\ell^2$ with finite-dimensional slots $E_n$, under the speed bound $\|Dw_n(x)\|\le\gamma(\rho_n(x))$.
--
--   1. **Derivatives.** The modified unit vectors still obey the speed bound, and $D\Phi_N(x)$ is within $\frac1{25}\|z\|$ of a surjective linear isometry at every point.
--   2. **Finite blocks.** The span of the first $N$ slots is finite dimensional.
--   3. **Approximants.** Each $\Phi_N$ is a bijection, being a norm-preserving finite perturbation of an isometry with local inverses, and
--   $$
--   \tfrac{24}{25}\|x-y\|\le\|\Phi_N(x)-\Phi_N(y)\|\le\tfrac{26}{25}\|x-y\| .
--   $$
--   4. **Limit.** $\Phi_N$ agrees with $\Phi$ in the first $N$ slots and $\Phi_N(x)\to\Phi(x)$. Hence $\Phi$ satisfies the same two-sided bounds and is a bijection.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/LipschitzEquivalence/FiniteApproximants.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzEquivalence/FiniteApproximants.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the LipschitzEquivalence mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_LipschitzEquivalence
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_FreeSpace
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_NullSequences
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_WeightedGraph
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_Schur
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_WeakSums
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_GraphObstruction
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_Localization
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_GraphEquivalence
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_HilbertDecomposition
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_InverseTails
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SlotRadii
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_GraphEmbedding
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_RadialBudget
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_SlotBudget
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_BanachAssembly
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_GlobalInverse
import Definitions.Def_OAI_Analysis_LipschitzEquivalence_MovingSlots

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e

namespace OAI

universe uE

noncomputable section

namespace LipschitzCounterexample.HilbertSlots
open scoped ENNReal NNReal InnerProductSpace
open Filter Topology RadialBudget
variable {E : ℕ → Type uE} [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]
variable (w : ∀ n, SlotDomain E → E n) (hw : ∀ n x, ‖w n x‖ = 1)
  (ξ : ∀ n, E n) (hξ : ∀ n, ‖ξ n‖ = 1)

omit hw hξ in
theorem approxSlots_derivative_budget
    (hb : ∀ n x, 0 < radius n x → ‖fderiv ℝ (w n) x‖ ≤ gamma (radius n x))
    (N n : ℕ) (x : SlotDomain E) (hr : 0 < radius n x) :
    ‖fderiv ℝ (approxSlots w ξ N n) x‖ ≤ gamma (radius n x) := by
  unfold approxSlots
  split_ifs
  · exact hb n x hr
  · rw [fderiv_const_apply]
    rw [ContinuousLinearMap.opNorm_zero]
    exact gamma_nonneg (radius n x)

theorem approximant_derivative_close
    (hd : ∀ n, ContDiff ℝ 1 (w n))
    (hb : ∀ n x, 0 < radius n x → ‖fderiv ℝ (w n) x‖ ≤ gamma (radius n x))
    (N : ℕ) (x z : SlotDomain E) :
    ‖fderiv ℝ (approximant w hw ξ hξ N) x z -
      frozenEquiv (fun n => approxSlots w ξ N n x)
        (fun n => approxSlots_norm w hw ξ hξ N n x) z‖ ≤ (1/25:ℝ)*‖z‖ := by
  have hm := (approximant_contDiff w hw ξ hξ hd N).differentiable (by norm_num) x
  have ha := norm_fderiv_movingSlotsMap_sub_frozen
    (approxSlots w ξ N) (approxSlots_norm w hw ξ hξ N)
    (fun n => (approxSlots_contDiff w ξ hd N n).differentiable (by norm_num) x)
    hm (fun n => approxSlots_derivative_budget w ξ hb N n x)
  have h := (fderiv ℝ (approximant w hw ξ hξ N) x -
    (frozen (fun n => approxSlots w ξ N n x)
      (fun n => approxSlots_norm w hw ξ hξ N n x)).toContinuousLinearMap).le_opNorm z
  change ‖fderiv ℝ (approximant w hw ξ hξ N) x z -
    frozenEquiv (fun n => approxSlots w ξ N n x)
      (fun n => approxSlots_norm w hw ξ hξ N n x) z‖ ≤ _ at h
  rw [show 4*c = (1/25:ℝ) by norm_num [c]] at ha
  exact h.trans (mul_le_mul_of_nonneg_right ha (norm_nonneg z))

variable [∀ n, FiniteDimensional ℝ (E n)]

def finiteBlocks (N : ℕ) : Submodule ℝ (HilbertSum E) :=
  (Finset.range N).sup (fun n => LinearMap.range (lp.singleContinuousLinearMap ℝ E 2 n).toLinearMap)

instance finiteBlocks_finiteDimensional (N : ℕ) : FiniteDimensional ℝ (finiteBlocks (E := E) N) := by
  unfold finiteBlocks
  infer_instance

omit ξ hξ hw w [∀ n, FiniteDimensional ℝ (E n)] in
theorem single_mem_finiteBlocks {N n : ℕ} (hn : n < N) (u : E n) :
    lp.single 2 n u ∈ finiteBlocks (E := E) N := by
  apply (Finset.le_sup (f := fun n => LinearMap.range
    (lp.singleContinuousLinearMap ℝ E 2 n).toLinearMap) (Finset.mem_range.mpr hn))
  exact ⟨u, rfl⟩

theorem approximant_bijective
    (hd : ∀ n, ContDiff ℝ 1 (w n))
    (hb : ∀ n x, 0 < radius n x → ‖fderiv ℝ (w n) x‖ ≤ gamma (radius n x))
    (N : ℕ) : Function.Bijective (approximant w hw ξ hξ N) := by
  let L := frozenEquiv ξ hξ
  let f : HilbertSum E → HilbertSum E := fun y => approximant w hw ξ hξ N (L.symm y)
  have hl : IsLocalHomeomorph (approximant w hw ξ hξ N) :=
    GlobalInverse.localHomeomorph_of_deriv_close _ _
      (fun x => frozenEquiv (fun n => approxSlots w ξ N n x)
        (fun n => approxSlots_norm w hw ξ hξ N n x)) (1/25) (by norm_num) (by norm_num)
      (fun x => (approximant_contDiff w hw ξ hξ hd N).hasStrictFDerivAt (by norm_num))
      (approximant_derivative_close w hw ξ hξ hd hb N)
  have hn (y : HilbertSum E) : ‖f y‖ = ‖y‖ := by
    dsimp [f]
    rw [approximant, norm_movingSlotsMap, L.symm.norm_map]
  have hS (y : HilbertSum E) : y - f y ∈ finiteBlocks (E := E) (2*N) := by
    have he := approximant_eq_sum w hw ξ hξ N (L.symm y)
    have hy : frozen ξ hξ (L.symm y) = y := L.apply_symm_apply y
    rw [hy] at he
    change approximant w hw ξ hξ N (L.symm y) = _ at he
    change y - approximant w hw ξ hξ N (L.symm y) ∈ _
    rw [he, sub_add_cancel_left]
    apply Submodule.neg_mem
    apply Submodule.sum_mem
    intro n hn
    exact single_mem_finiteBlocks (Finset.mem_range.mp hn) _
  have hf : Function.Bijective f := GlobalInverse.finite_perturbation_bijective
    (finiteBlocks (E := E) (2*N)) f (hl.comp L.symm.toHomeomorph.isLocalHomeomorph) hn hS
  constructor
  · intro x y hxy
    have he : f (L x) = f (L y) := by simpa only [f, L.symm_apply_apply] using hxy
    exact L.injective (hf.1 he)
  · intro y
    obtain ⟨x, hx⟩ := hf.2 y
    exact ⟨L.symm x, hx⟩

theorem approximant_bounds
    (hd : ∀ n, ContDiff ℝ 1 (w n))
    (hb : ∀ n x, 0 < radius n x → ‖fderiv ℝ (w n) x‖ ≤ gamma (radius n x))
    (N : ℕ) (x y : SlotDomain E) :
    (24/25:ℝ)*‖x-y‖ ≤ ‖approximant w hw ξ hξ N x - approximant w hw ξ hξ N y‖ ∧
    ‖approximant w hw ξ hξ N x - approximant w hw ξ hξ N y‖ ≤ (26/25:ℝ)*‖x-y‖ := by
  let e := Equiv.ofBijective (approximant w hw ξ hξ N) (approximant_bijective w hw ξ hξ hd hb N)
  have h := GlobalInverse.global_bounds_of_deriv_close e
    (fun x => fderiv ℝ (approximant w hw ξ hξ N) x)
    (fun x => frozenEquiv (fun n => approxSlots w ξ N n x)
      (fun n => approxSlots_norm w hw ξ hξ N n x)) (1/25) (by norm_num) (by norm_num)
    (fun x => (approximant_contDiff w hw ξ hξ hd N).hasStrictFDerivAt (by norm_num))
    (approximant_derivative_close w hw ξ hξ hd hb N)
  constructor
  · simpa only [e, Equiv.ofBijective_apply, show (1:ℝ)-1/25 = 24/25 by norm_num] using h.2 x y
  · simpa only [e, Equiv.ofBijective_apply, show (1:ℝ)+1/25 = 26/25 by norm_num] using h.1 x y

end LipschitzCounterexample.HilbertSlots

namespace LipschitzCounterexample.HilbertSlots
open scoped ENNReal NNReal InnerProductSpace
open Filter Topology
variable {E : ℕ → Type uE} [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]
variable (w : ∀ n, SlotDomain E → E n) (hw : ∀ n x, ‖w n x‖ = 1)
  (ξ : ∀ n, E n) (hξ : ∀ n, ‖ξ n‖ = 1)

theorem approximant_head (N : ℕ) (x : SlotDomain E) (n : ℕ) (hn : n < N) :
    approximant w hw ξ hξ N x n = movingSlotsMap w hw x n := by
  rw [approximant, movingSlotsMap_apply, movingSlotsMap_apply]
  simp only [slotCoord, approxSlots, ite_eq_left hn]
  congr 2
  unfold scalarSlot
  generalize he : Equiv.natSumNatEquivNat.symm n = i
  rcases i with m | m
  · rfl
  · have heq : n = 2*m+1 := by
      have h := congrArg Equiv.natSumNatEquivNat he
      simpa only [Equiv.apply_symm_apply, Equiv.natSumNatEquivNat_apply, Sum.elim_inr] using h
    simp only [Sum.elim_inr, approxSlots, ite_eq_left (show m < N by omega)]

theorem approximant_prefix (N K : ℕ) (hk : K ≤ N) (x : SlotDomain E) :
    cutHead K (approximant w hw ξ hξ N x) = cutHead K (movingSlotsMap w hw x) := by
  apply Finset.sum_congr rfl
  intro n hn
  rw [approximant_head w hw ξ hξ N x n ((Finset.mem_range.mp hn).trans_le hk)]

theorem approximant_tendsto (x : SlotDomain E) :
    Tendsto (fun N => approximant w hw ξ hξ N x) atTop (𝓝 (movingSlotsMap w hw x)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have ht : Tendsto (fun K => movingSlotsMap w hw x - cutHead K (movingSlotsMap w hw x))
      atTop (𝓝 0) := by
    simpa only [sub_self] using (tendsto_const_nhds (x := movingSlotsMap w hw x)).sub
      (prefix_tendsto (movingSlotsMap w hw x))
  obtain ⟨K, hK⟩ := Filter.Eventually.exists
    ((NormedAddGroup.tendsto_nhds_zero.1 ht) (ε/2) (by positivity))
  refine ⟨K, fun N hN => ?_⟩
  have hp := approximant_prefix w hw ξ hξ N K hN x
  have he : ‖approximant w hw ξ hξ N x - cutHead K (approximant w hw ξ hξ N x)‖ =
      ‖movingSlotsMap w hw x - cutHead K (movingSlotsMap w hw x)‖ := by
    have h₁ := norm_sub_prefix_sq (approximant w hw ξ hξ N x) K
    have h₂ := norm_sub_prefix_sq (movingSlotsMap w hw x) K
    have hn : ‖approximant w hw ξ hξ N x‖ = ‖movingSlotsMap w hw x‖ := by
      rw [approximant, norm_movingSlotsMap, norm_movingSlotsMap]
    have hs : (∑ n ∈ Finset.range K, ‖approximant w hw ξ hξ N x n‖^2) =
        (∑ n ∈ Finset.range K, ‖movingSlotsMap w hw x n‖^2) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [approximant_head w hw ξ hξ N x n ((Finset.mem_range.mp hn).trans_le hN)]
    rw [hn, hs] at h₁
    nlinarith [norm_nonneg (approximant w hw ξ hξ N x - cutHead K (approximant w hw ξ hξ N x)),
      norm_nonneg (movingSlotsMap w hw x - cutHead K (movingSlotsMap w hw x))]
  have htri := norm_sub_le (approximant w hw ξ hξ N x - cutHead K (approximant w hw ξ hξ N x))
    (movingSlotsMap w hw x - cutHead K (movingSlotsMap w hw x))
  rw [hp, sub_sub_sub_cancel_right] at htri
  rw [hp] at he
  rw [he] at htri
  rw [dist_eq_norm]
  linarith

end LipschitzCounterexample.HilbertSlots

namespace LipschitzCounterexample.HilbertSlots
open scoped ENNReal NNReal InnerProductSpace
open Filter Topology RadialBudget
variable {E : ℕ → Type uE} [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]
  [∀ i, FiniteDimensional ℝ (E i)]
variable (w : ∀ n, SlotDomain E → E n) (hw : ∀ n x, ‖w n x‖ = 1)
  (ξ : ∀ n, E n) (hξ : ∀ n, ‖ξ n‖ = 1)

include ξ hξ in
theorem movingSlotsMap_bounds
    (hd : ∀ n, ContDiff ℝ 1 (w n))
    (hb : ∀ n x, 0 < radius n x → ‖fderiv ℝ (w n) x‖ ≤ gamma (radius n x))
    (x y : SlotDomain E) :
    (24/25:ℝ)*‖x-y‖ ≤ ‖movingSlotsMap w hw x - movingSlotsMap w hw y‖ ∧
    ‖movingSlotsMap w hw x - movingSlotsMap w hw y‖ ≤ (26/25:ℝ)*‖x-y‖ := by
  have ht := ((approximant_tendsto w hw ξ hξ x).sub (approximant_tendsto w hw ξ hξ y)).norm
  exact ⟨ge_of_tendsto' ht (fun N => (approximant_bounds w hw ξ hξ hd hb N x y).1),
    le_of_tendsto' ht (fun N => (approximant_bounds w hw ξ hξ hd hb N x y).2)⟩

include ξ hξ in
theorem movingSlotsMap_bijective
    (hd : ∀ n, ContDiff ℝ 1 (w n))
    (hb : ∀ n x, 0 < radius n x → ‖fderiv ℝ (w n) x‖ ≤ gamma (radius n x)) :
    Function.Bijective (movingSlotsMap w hw) := by
  constructor
  · intro x y hxy
    have hb := (movingSlotsMap_bounds w hw ξ hξ hd hb x y).1
    rw [hxy, sub_self, norm_zero] at hb
    exact sub_eq_zero.mp (norm_eq_zero.mp (by nlinarith [norm_nonneg (x-y)]))
  · exact moving_limit_surjective
      (fun N x n => approxSlots w ξ N n x)
      (fun N x n => approxSlots_norm w hw ξ hξ N n x)
      (movingSlotsMap w hw) ⟨26/25, by norm_num⟩
      (fun N => (approximant_bijective w hw ξ hξ hd hb N).2)
      (fun N => lipschitzWith_iff_norm_sub_le.mpr
        (fun x y => (approximant_bounds w hw ξ hξ hd hb N x y).2))
      (approximant_tendsto w hw ξ hξ)

end LipschitzCounterexample.HilbertSlots

end

end OAI


