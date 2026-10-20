-- Prove2me | Definitions.Def_OAI_Analysis_LipschitzEquivalence_MovingSlots
-- name    : OAI_Analysis_LipschitzEquivalence_MovingSlots
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T17:42:15.721532+00:00
-- url     : https://prove2.me/theorems/d4406f7f-4921-4b7e-9484-aef0bf7dec52
-- title:
--   Moving-slot maps and their derivatives
-- statement:
--   Nonlinear maps on the slot domain $\mathcal D=\mathcal H\oplus_2\ell^2$, $\mathcal H=\bigl(\bigoplus_nE_n\bigr)_{\ell^2}$, obtained from the frozen isometry by letting the unit vectors depend on the point.
--
--   1. **Slot coordinates.** Given $C^1$ maps $w_n:\mathcal D\to E_n$ with $\|w_n(x)\|=1$, the scalar slot $\sigma_n(x)$ is $v_m$ for $n=2m$ and $\langle w_m(x),u_m\rangle$ for $n=2m+1$. The moving-slot map is
--   $$
--   \Phi(x)_n=u_n+\bigl(\sigma_n(x)-\langle w_n(x),u_n\rangle\bigr)\,w_n(x),
--   $$
--   which equals the frozen isometry with unit vectors $w(x)$; in particular $\|\Phi(x)\|=\|x\|$.
--   2. **Approximants.** Replacing $w_n$ by a fixed unit vector $\xi_n$ for $n\ge N$ gives $C^1$ approximants $\Phi_N$. These agree with the frozen isometry for $\xi$ in slots $n\ge2N$, so they differ from it only in finitely many slots.
--   3. **Derivative estimate.** The derivative of each slot coordinate is computed by the product rule. If the derivatives of the $w_n$ are bounded by the speed profile, $\|Dw_n(x)\|\le\gamma(\rho_n(x))$ whenever the radius $\rho_n(x)>0$, then
--   $$
--   \bigl\|D\Phi(x)-\mathrm{frozen}_{w(x)}\bigr\|\le4c=\tfrac1{25}.
--   $$
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/LipschitzEquivalence/MovingSlots.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzEquivalence/MovingSlots.lean by skeleton subtraction
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

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

universe uE

noncomputable section

namespace LipschitzCounterexample.HilbertSlots
open scoped ENNReal NNReal InnerProductSpace
open Filter Topology
variable {E : ℕ → Type uE} [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]

def scalarSlot (w : ∀ n, SlotDomain E → E n) (x : SlotDomain E) (n : ℕ) : ℝ :=
  Sum.elim (fun i => x.snd i) (fun i => ⟪w i x, x.fst i⟫_ℝ) (Equiv.natSumNatEquivNat.symm n)

def slotCoord (w : ∀ n, SlotDomain E → E n) (x : SlotDomain E) (n : ℕ) : E n :=
  x.fst n + (scalarSlot w x n - ⟪w n x, x.fst n⟫_ℝ) • w n x

variable (w : ∀ n, SlotDomain E → E n) (hw : ∀ n x, ‖w n x‖ = 1)

def movingSlotsMap (x : SlotDomain E) : HilbertSum E := frozen (fun n => w n x) (fun n => hw n x) x

theorem movingSlotsMap_apply (x : SlotDomain E) (n : ℕ) : movingSlotsMap w hw x n = slotCoord w x n := by
  rw [movingSlotsMap, frozen_apply]
  rfl

theorem norm_movingSlotsMap (x : SlotDomain E) : ‖movingSlotsMap w hw x‖ = ‖x‖ := (frozen _ _).norm_map x

omit hw in
theorem scalarSlot_contDiff (hd : ∀ n, ContDiff ℝ 1 (w n)) (n : ℕ) :
    ContDiff ℝ 1 (fun x => scalarSlot w x n) := by
  unfold scalarSlot
  cases Equiv.natSumNatEquivNat.symm n with
  | inl i => exact ((lp.evalCLM ℝ (fun _ : ℕ => ℝ) 2 i).comp
      (WithLp.sndL 2 ℝ (HilbertSum E) RealL2)).contDiff
  | inr i => exact (hd i).inner ℝ (((lp.evalCLM ℝ E 2 i).comp
      (WithLp.fstL 2 ℝ (HilbertSum E) RealL2)).contDiff)

omit hw in
theorem slotCoord_contDiff (hd : ∀ n, ContDiff ℝ 1 (w n)) (n : ℕ) :
    ContDiff ℝ 1 (fun x => slotCoord w x n) := by
  have hu := ((lp.evalCLM ℝ E 2 n).comp (WithLp.fstL 2 ℝ (HilbertSum E) RealL2)).contDiff (n := 1)
  exact hu.add (((scalarSlot_contDiff w hd n).sub ((hd n).inner ℝ hu)).smul (hd n))

variable (ξ : ∀ n, E n) (hξ : ∀ n, ‖ξ n‖ = 1)

def approxSlots (N : ℕ) (n : ℕ) (x : SlotDomain E) : E n := if n < N then w n x else ξ n

omit [∀ i, InnerProductSpace ℝ (E i)] in
include hw hξ in
theorem approxSlots_norm (N n : ℕ) (x : SlotDomain E) : ‖approxSlots w ξ N n x‖ = 1 := by
  unfold approxSlots
  split_ifs
  · exact hw n x
  · exact hξ n

omit hw hξ in
theorem approxSlots_contDiff (hd : ∀ n, ContDiff ℝ 1 (w n)) (N n : ℕ) :
    ContDiff ℝ 1 (approxSlots w ξ N n) := by
  unfold approxSlots
  split_ifs
  · exact hd n
  · exact contDiff_const

def approximant (N : ℕ) : SlotDomain E → HilbertSum E :=
  movingSlotsMap (approxSlots w ξ N) (approxSlots_norm w hw ξ hξ N)

theorem approximant_tail (N : ℕ) (x : SlotDomain E) (n : ℕ) (hn : 2*N ≤ n) :
    approximant w hw ξ hξ N x n = frozen ξ hξ x n := by
  rw [approximant, movingSlotsMap_apply, frozen_apply]
  have hn' : ¬n<N := by omega
  simp only [slotCoord, approxSlots, ite_eq_right hn']
  congr 2
  unfold scalarSlot interleaveRaw
  generalize he : Equiv.natSumNatEquivNat.symm n = i
  rcases i with m | m
  · rfl
  · have heq : n = 2*m+1 := by
      have h := congrArg Equiv.natSumNatEquivNat he
      simpa only [Equiv.apply_symm_apply, Equiv.natSumNatEquivNat_apply, Sum.elim_inr] using h
    have hm : ¬m<N := by omega
    apply congrArg (fun c : ℝ => c - ⟪ξ n, x.fst n⟫_ℝ)
    change ⟪approxSlots w ξ N m x, x.fst m⟫_ℝ = ⟪ξ m, x.fst m⟫_ℝ
    rw [approxSlots, ite_eq_right hm]

theorem approximant_eq_sum (N : ℕ) (x : SlotDomain E) :
    approximant w hw ξ hξ N x = frozen ξ hξ x + ∑ n ∈ Finset.range (2*N),
      lp.single 2 n (slotCoord (approxSlots w ξ N) x n - frozen ξ hξ x n) := by
  apply lp.ext
  funext n
  rw [lp.coeFn_add, lp.coeFn_sum]
  simp only [Pi.add_apply, Finset.sum_apply, lp.single_apply]
  by_cases hn : n < 2*N
  · simp only [Finset.sum_pi_single, Finset.mem_range, hn, ite_true]
    rw [← movingSlotsMap_apply (approxSlots w ξ N) (approxSlots_norm w hw ξ hξ N)]
    change _ = _ + (approximant w hw ξ hξ N x n - _)
    abel
  · simp only [Finset.sum_pi_single, Finset.mem_range, hn, ite_false, add_zero]
    exact approximant_tail w hw ξ hξ N x n (Nat.le_of_not_gt hn)

theorem approximant_contDiff (hd : ∀ n, ContDiff ℝ 1 (w n)) (N : ℕ) :
    ContDiff ℝ 1 (approximant w hw ξ hξ N) := by
  have he : approximant w hw ξ hξ N = fun x => frozen ξ hξ x + ∑ n ∈ Finset.range (2*N),
      lp.single 2 n (slotCoord (approxSlots w ξ N) x n - frozen ξ hξ x n) :=
    funext (approximant_eq_sum w hw ξ hξ N)
  rw [he]
  apply (frozen ξ hξ).toContinuousLinearMap.contDiff.add
  apply ContDiff.sum
  intro n hn
  exact (lp.singleContinuousLinearMap ℝ E 2 n).contDiff.comp
    ((slotCoord_contDiff _ (approxSlots_contDiff w ξ hd N) n).sub
      (((lp.evalCLM ℝ E 2 n).comp (frozen ξ hξ).toContinuousLinearMap).contDiff))

end LipschitzCounterexample.HilbertSlots

namespace LipschitzCounterexample.HilbertSlots
open scoped ENNReal NNReal InnerProductSpace
open Filter Topology RadialBudget
variable {E : ℕ → Type uE} [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]

@[simp] theorem fderiv_fstCoord (n : ℕ) (x z : SlotDomain E) :
    fderiv ℝ (fun y : SlotDomain E => y.fst n) x z = z.fst n := by
  exact congrArg (fun T : SlotDomain E →L[ℝ] E n => T z)
    (((lp.evalCLM ℝ E 2 n).comp (WithLp.fstL 2 ℝ (HilbertSum E) RealL2)).hasFDerivAt.fderiv)

@[simp] theorem fderiv_sndCoord (n : ℕ) (x z : SlotDomain E) :
    fderiv ℝ (fun y : SlotDomain E => y.snd n) x z = z.snd n := by
  exact congrArg (fun T : SlotDomain E →L[ℝ] ℝ => T z)
    (((lp.evalCLM ℝ (fun _ : ℕ => ℝ) 2 n).comp
      (WithLp.sndL 2 ℝ (HilbertSum E) RealL2)).hasFDerivAt.fderiv)

theorem differentiable_fstCoord (n : ℕ) : Differentiable ℝ (fun y : SlotDomain E => y.fst n) :=
  ((lp.evalCLM ℝ E 2 n).comp (WithLp.fstL 2 ℝ (HilbertSum E) RealL2)).differentiable

theorem differentiable_sndCoord (n : ℕ) : Differentiable ℝ (fun y : SlotDomain E => y.snd n) :=
  ((lp.evalCLM ℝ (fun _ : ℕ => ℝ) 2 n).comp
      (WithLp.sndL 2 ℝ (HilbertSum E) RealL2)).differentiable

variable (w : ∀ n, SlotDomain E → E n) (hw : ∀ n x, ‖w n x‖ = 1)

variable {x : SlotDomain E}

omit hw in
theorem fderiv_scalarSlot_apply (hd : ∀ n, DifferentiableAt ℝ (w n) x) (n : ℕ)
    (z : SlotDomain E) :
    fderiv ℝ (fun y => scalarSlot w y n) x z =
      Sum.elim (fun i => z.snd i)
        (fun i => ⟪w i x, z.fst i⟫_ℝ + ⟪fderiv ℝ (w i) x z, x.fst i⟫_ℝ)
        (Equiv.natSumNatEquivNat.symm n) := by
  unfold scalarSlot
  cases Equiv.natSumNatEquivNat.symm n with
  | inl i => exact fderiv_sndCoord i x z
  | inr i => simpa only [Sum.elim_inr, fderiv_fstCoord] using
      fderiv_inner_apply (𝕜 := ℝ) (hd i) (differentiable_fstCoord i x) z

omit hw in
theorem differentiable_scalarSlot (hd : ∀ n, DifferentiableAt ℝ (w n) x) (n : ℕ) :
    DifferentiableAt ℝ (fun y => scalarSlot w y n) x := by
  unfold scalarSlot
  cases Equiv.natSumNatEquivNat.symm n with
  | inl i => exact differentiable_sndCoord i x
  | inr i => exact (hd i).inner ℝ (differentiable_fstCoord i x)

omit hw in
theorem fderiv_slotCoord_apply (hd : ∀ n, DifferentiableAt ℝ (w n) x) (n : ℕ)
    (z : SlotDomain E) :
    fderiv ℝ (fun y => slotCoord w y n) x z = z.fst n +
      (scalarSlot w x n - ⟪w n x, x.fst n⟫_ℝ) • fderiv ℝ (w n) x z +
      (fderiv ℝ (fun y => scalarSlot w y n) x z -
        (⟪w n x, z.fst n⟫_ℝ + ⟪fderiv ℝ (w n) x z, x.fst n⟫_ℝ)) • w n x := by
  have hu := differentiable_fstCoord (E := E) n x
  have hi := (hd n).inner ℝ hu
  have hs := differentiable_scalarSlot w hd n
  have h := (hu.hasFDerivAt.add ((hs.hasFDerivAt.sub hi.hasFDerivAt).smul (hd n).hasFDerivAt)).fderiv
  change fderiv ℝ (fun y => slotCoord w y n) x = _ at h
  rw [h]
  simp only [Pi.sub_apply, add_apply, sub_apply, smul_apply, ContinuousLinearMap.smulRight_apply,
    fderiv_fstCoord, fderiv_inner_apply (𝕜 := ℝ) (hd n) hu]
  abel

theorem fderiv_movingSlotsMap_apply (_hd : ∀ n, DifferentiableAt ℝ (w n) x)
    (hm : DifferentiableAt ℝ (movingSlotsMap w hw) x) (n : ℕ) (z : SlotDomain E) :
    fderiv ℝ (movingSlotsMap w hw) x z n =
      fderiv ℝ (fun y => slotCoord w y n) x z := by
  have he := ((lp.evalCLM ℝ E 2 n).hasFDerivAt.comp x hm.hasFDerivAt).fderiv
  have he' := congrArg (fun T : SlotDomain E →L[ℝ] E n => T z) he
  have hc : (fun y => (lp.evalCLM ℝ E 2 n) (movingSlotsMap w hw y)) =
      (fun y => slotCoord w y n) := funext (fun y => movingSlotsMap_apply w hw y n)
  change fderiv ℝ (fun y => (lp.evalCLM ℝ E 2 n) (movingSlotsMap w hw y)) x z =
    fderiv ℝ (movingSlotsMap w hw) x z n at he'
  rw [hc] at he'
  exact he'.symm

end LipschitzCounterexample.HilbertSlots

namespace LipschitzCounterexample.HilbertSlots
open scoped ENNReal NNReal InnerProductSpace
open Filter Topology RadialBudget
variable {E : ℕ → Type uE} [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]
variable (w : ∀ n, SlotDomain E → E n) (hw : ∀ n x, ‖w n x‖ = 1)

variable {x : SlotDomain E}

theorem fderiv_movingSlotsMap_sub_frozen (hd : ∀ n, DifferentiableAt ℝ (w n) x)
    (hm : DifferentiableAt ℝ (movingSlotsMap w hw) x) (z : SlotDomain E)
    (hb : ∀ n, 0 < radius n x → ‖fderiv ℝ (w n) x z‖ ≤ gamma (radius n x)) :
    fderiv ℝ (movingSlotsMap w hw) x z - frozen (fun n => w n x) (fun n => hw n x) z =
      slotError (fun n => w n x) (fun n => hw n x) x (fun n => fderiv ℝ (w n) x z) hb := by
  apply lp.ext
  funext n
  simp only [lp.coeFn_sub, Pi.sub_apply, fderiv_movingSlotsMap_apply w hw hd hm,
    fderiv_slotCoord_apply w hd, fderiv_scalarSlot_apply w hd, frozen_apply]
  simp only [slotError, lp.coeFn_add, Pi.add_apply, ofSqBound_apply, embed_apply,
    lp.coeFn_sub, Pi.sub_apply]
  have hi (a b : RealL2) (k : ℕ) :
      interleave (WithLp.toLp 2 (a, b)) k = interleaveRaw a b k := rfl
  simp only [hi]
  unfold scalarSlot interleaveRaw
  cases Equiv.natSumNatEquivNat.symm n with
  | inl i =>
    simp only [Sum.elim_inl, coeff_apply]
    change _ = (x.snd i - ⟪w n x, x.fst n⟫_ℝ) • fderiv ℝ (w n) x z +
      (0 - ⟪fderiv ℝ (w n) x z, x.fst n⟫_ℝ) • w n x
    module
  | inr i =>
    simp only [Sum.elim_inr, coeff_apply]
    change _ = (⟪w i x, x.fst i⟫_ℝ - ⟪w n x, x.fst n⟫_ℝ) • fderiv ℝ (w n) x z +
      (⟪fderiv ℝ (w i) x z, x.fst i⟫_ℝ - ⟪fderiv ℝ (w n) x z, x.fst n⟫_ℝ) • w n x
    module

theorem norm_fderiv_movingSlotsMap_sub_frozen (hd : ∀ n, DifferentiableAt ℝ (w n) x)
    (hm : DifferentiableAt ℝ (movingSlotsMap w hw) x)
    (hb : ∀ n, 0 < radius n x → ‖fderiv ℝ (w n) x‖ ≤ gamma (radius n x)) :
    ‖fderiv ℝ (movingSlotsMap w hw) x -
      (frozen (fun n => w n x) (fun n => hw n x)).toContinuousLinearMap‖ ≤ 4*c := by
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (mul_nonneg (by norm_num) c_pos.le)
  intro z hz
  have hbd (n : ℕ) (hn : 0 < radius n x) :
      ‖fderiv ℝ (w n) x z‖ ≤ gamma (radius n x) := by
    have h := (fderiv ℝ (w n) x).le_opNorm z
    rw [hz, mul_one] at h
    exact h.trans (hb n hn)
  change ‖fderiv ℝ (movingSlotsMap w hw) x z - frozen _ _ z‖ ≤ _
  rw [fderiv_movingSlotsMap_sub_frozen w hw hd hm z hbd]
  exact norm_slotError _ _ x _ hbd

end LipschitzCounterexample.HilbertSlots

end

end OAI


