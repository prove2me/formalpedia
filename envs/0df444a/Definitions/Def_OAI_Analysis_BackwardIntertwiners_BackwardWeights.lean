-- Prove2me | Definitions.Def_OAI_Analysis_BackwardIntertwiners_BackwardWeights
-- name    : OAI_Analysis_BackwardIntertwiners_BackwardWeights
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T02:00:39.684013+00:00
-- url     : https://prove2.me/theorems/67595894-a226-4895-9a2a-edbf04248690
-- title:
--   Digit-driven fiber weights and normalized backward coefficients over the 2-adic odometer
-- statement:
--   This file turns the 2-adic digits of a base point into explicit fiber weights and constructs the normalized coefficients of the backward operator.
--
--   **Setting.** Let $\mathbb{Z}_2$ be the 2-adic integers with completed normalized Haar measure $\mu$, let $\rho_m(x)\in\{0,\dots,2^m-1\}$ be the residue of $x\in\mathbb{Z}_2$ modulo $2^m$, and let $X_{\mathrm{good}}=\mathbb{Z}_2\setminus\mathbb{Z}$. For $t:\mathbb{N}\to\mathbb{N}$ and $k\in\mathbb{N}$ put $m(k)=\lfloor\log_8k\rfloor+1$ (with $m(0)=1$), $E_t(0)=10$, $E_t(k)=10(k+1)+100\bigl(2^{m(k)}-2+t(m(k))\bigr)$ for $k\ge1$, and $\Sigma_t(n)=\sum_{k=0}^{n-1}E_t(k)$.
--
--   1. **Digit sequences.** $t_x(m)=\rho_m(x)$ and $u_x(m)=2^m-1-\rho_m(x)$, the residue of $-1-x$ modulo $2^m$. Both satisfy $t_x(m),u_x(m)<2^m$.
--   2. **Explicit exponent, ratio and weight.** For $j\in\mathbb{Z}$,
--   $$\varepsilon_x(j)=\begin{cases}E_{t_x}(j),&j\ge0,\\E_{u_x}(-j-1),&j<0,\end{cases}\qquad\beta_x(j)=e^{-\varepsilon_x(j)},\qquad w_x(j)=\begin{cases}e^{-\Sigma_{t_x}(j)},&j\ge0,\\e^{\Sigma_{u_x}(-j)},&j<0.\end{cases}$$
--   3. **Raw backward ratio.**
--   $$r_x(j)=\frac{w_{x+1}(j-1)}{e^{10}\,w_x(j)}\qquad(j\in\mathbb{Z}).$$
--   4. **Backward bound.** $L(x)=\sup_{j\in\mathbb{Z}}r_x(j)$.
--   5. **Backward coefficients.** $c_x(j)=r_x(j)/L(x)$ if $x\in X_{\mathrm{good}}$, and $c_x(j)=0$ otherwise.
--
--   The file establishes the properties used later. For each fixed $j$ all these quantities are measurable functions of $x$. Always $\beta_x(j)\in(0,e^{-10}]$ with $\beta_x(0)=e^{-10}$, $w_x(j)>0$, $w_x(0)=1$, $w_x(-1)=e^{10}$, $r_x(j)>0$ and $r_x(0)=1$. For $x\in X_{\mathrm{good}}$ and all sufficiently large $k$,
--   $$E_{t_{x+1}}(k)-E_{t_x}(k)=100,\qquad E_{u_{x+1}}(k)-E_{u_x}(k)=-100,$$
--   so the corresponding partial sums differ by an eventually affine function of $n$, and $r_x(n+1)\to0$ and $r_x(-n)\to0$ as $n\to\infty$. Hence for good $x$ the sequence $r_x$ is bounded, $L(x)\ge1$ and $r_x(j)\le L(x)$; and $0\le c_x(j)\le1$ for every $x$ and $j$.
--
--   Since $w_x(j+1)=\beta_x(j)\,w_x(j)$, the ratio satisfies $\beta_{x+1}(j-1)\,r_x(j)=r_x(j+1)\,\beta_x(j)$, and the same identity holds for $c_x$. This is the intertwining relation that makes the backward operator $(Vf)(x)_j=c_{x-1}(j+1)\,f(x-1)_{j+1}$ commute with the forward operator $(Sf)(x)_j=\beta_x(j-1)\,f(x)_{j-1}$ on $L^2(\mathbb{Z}_2,\mu;\ell^2(\mathbb{Z}))$, while the normalization by $L(x)$ keeps $V$ a contraction.
--
--   **Formalization Note** The names are `plusResidue`, `minusResidue`, `explicitExponent`, `explicitBeta`, `explicitWeight`, `rawBackward`, `backwardBound` (an `iSup` over the integers) and `backwardCoeff`. `minusResidue` uses natural-number subtraction, which does not truncate because $\rho_m(x)<2^m$. In Lean the supremum of a set of reals that is not bounded above is $0$; this case does not arise because $c_x$ is set to $0$ off the good set and $r_x$ is bounded on it. Auxiliary lemmas include `halfExponent_drift`, `halfSum_eventually_affine`, `rawBackward_nat_succ`, `rawBackward_neg_nat`, `rawBackward_decay`, `backwardBound_ge_one`, `backwardCoeff_bounds`, the measurability lemmas, and the elementary bounds $400\sqrt{n}\le45n+1000$ and $E_t(n)-10\le55n+1000$ for $t$ with $t(m)<2^m$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/BackwardIntertwiners/BackwardWeights.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/BackwardIntertwiners/BackwardWeights.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the BackwardIntertwiners mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_BackwardIntertwiners
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_ConvexEnvelope
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_ConvolutionBounds
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_CoefficientSupport
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_WeightSeparation
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_FiberTails
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_ExplicitWeights
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_HaarBase
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_FiberMaps

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

namespace BackwardIntertwiners
open Filter
open scoped Topology
noncomputable section

open Topology MeasureTheory Set
open scoped ENNReal

def plusResidue (x : Base) (m : ℕ) : ℕ := residue m x
def minusResidue (x : Base) (m : ℕ) : ℕ := 2^m-1-residue m x
lemma plusResidue_bounds (x : Base) : ResidueBounds (plusResidue x) := fun m => residue_lt m x
lemma minusResidue_bounds (x : Base) : ResidueBounds (minusResidue x) := by
  intro m
  have hp : 0 < 2^m := pow_pos (by norm_num) _
  dsimp [minusResidue]
  omega

def explicitExponent (x : Base) (j : ℤ) : ℝ :=
  bilateralExponent (plusResidue x) (minusResidue x) j
def explicitBeta (x : Base) (j : ℤ) : ℝ :=
  bilateralBeta (plusResidue x) (minusResidue x) j
def explicitWeight (x : Base) (j : ℤ) : ℝ :=
  bilateralWeight (plusResidue x) (minusResidue x) j

lemma measurable_halfExponent (t : Base → ℕ → ℕ) (ht : ∀ m, Measurable (fun x => t x m))
    (k : ℕ) : Measurable (fun x => halfExponent (t x) k) := by
  dsimp [halfExponent, residueCorrection]
  split_ifs
  · exact measurable_const
  · fun_prop

lemma measurable_plusResidue (m : ℕ) : Measurable (fun x => plusResidue x m) := measurable_residue m
lemma measurable_minusResidue (m : ℕ) : Measurable (fun x => minusResidue x m) :=
  measurable_const.sub (measurable_residue m)
lemma measurable_explicitExponent (j : ℤ) : Measurable (fun x => explicitExponent x j) := by
  cases j with
  | ofNat n => exact measurable_halfExponent plusResidue measurable_plusResidue n
  | negSucc n => exact measurable_halfExponent minusResidue measurable_minusResidue n
lemma measurable_explicitBeta (j : ℤ) : Measurable (fun x => explicitBeta x j) :=
  Real.measurable_exp.comp (measurable_explicitExponent j).neg
lemma measurable_halfSum (t : Base → ℕ → ℕ) (ht : ∀ m, Measurable (fun x => t x m))
    (n : ℕ) : Measurable (fun x => halfSum (t x) n) :=
  Finset.measurable_sum _ (fun k _ => measurable_halfExponent t ht k)
lemma measurable_explicitWeight (j : ℤ) : Measurable (fun x => explicitWeight x j) := by
  cases j with
  | ofNat n => exact Real.measurable_exp.comp (measurable_halfSum plusResidue measurable_plusResidue n).neg
  | negSucc n => exact Real.measurable_exp.comp (measurable_halfSum minusResidue measurable_minusResidue (n+1))
lemma explicitBeta_pos (x : Base) (j : ℤ) : 0 < explicitBeta x j := Real.exp_pos _
lemma explicitWeight_pos (x : Base) (j : ℤ) : 0 < explicitWeight x j := bilateralWeight_pos _ _ _
lemma explicitBeta_le (x : Base) (j : ℤ) : explicitBeta x j ≤ Real.exp (-10) := by
  apply Real.exp_le_exp.mpr
  exact neg_le_neg (bilateralExponent_nonneg _ _ _)
@[simp] lemma explicitBeta_zero (x : Base) : explicitBeta x 0 = Real.exp (-10) := by
  simp [explicitBeta, bilateralBeta, bilateralExponent, halfExponent, residueCorrection]
@[simp] lemma explicitWeight_zero (x : Base) : explicitWeight x 0 = 1 := by
  simp [explicitWeight, bilateralWeight]
@[simp] lemma explicitWeight_neg_one (x : Base) : explicitWeight x (-1) = Real.exp 10 := by
  change Real.exp (halfSum (minusResidue x) 1) = _
  simp [halfSum_succ, halfExponent, residueCorrection]
lemma weightBlock_eventually_ge (M : ℕ) : ∀ᶠ k : ℕ in atTop, M ≤ weightBlock k := by
  filter_upwards [eventually_ge_atTop (8^M)] with k hk
  have h := Nat.le_log_of_pow_le (by norm_num : 1 < 8) hk
  exact h.trans (Nat.le_succ _)

lemma halfExponent_drift {x : Base} (hx : x ∈ goodBase) :
    ∀ᶠ k : ℕ in atTop,
      halfExponent (plusResidue (odometer x)) k - halfExponent (plusResidue x) k = 100 ∧
      halfExponent (minusResidue (odometer x)) k - halfExponent (minusResidue x) k = -100 := by
  obtain ⟨M,hM⟩ := goodBase_eventually_nonexceptional hx
  filter_upwards [weightBlock_eventually_ge M, eventually_ge_atTop 1] with k hk hk1
  have hstep := residue_step (show 1 ≤ weightBlock k by unfold weightBlock; omega) x
  rw [ite_eq_right (hM _ hk)] at hstep
  have hcomp y : ((minusResidue y (weightBlock k)):ℝ) =
      (residueScale k:ℝ)-1-residue (weightBlock k) y := by
    have hr := residue_lt (weightBlock k) y
    have hN : 0 < 2^weightBlock k := pow_pos (by norm_num) _
    dsimp [minusResidue, residueScale]
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    norm_num
  dsimp [halfExponent, residueCorrection]
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
  dsimp [plusResidue]
  rw [hcomp, hcomp, hstep]
  push_cast
  constructor <;> ring

lemma halfSum_eventually_affine {t u : ℕ → ℕ} {d : ℝ}
    (hd : ∀ᶠ k : ℕ in atTop, halfExponent u k-halfExponent t k = d) :
    ∃ C : ℝ, ∀ᶠ n : ℕ in atTop, halfSum u n-halfSum t n = d*(n:ℝ)+C := by
  obtain ⟨N,hN⟩ := eventually_atTop.mp hd
  refine ⟨halfSum u N-halfSum t N-d*(N:ℝ), ?_⟩
  filter_upwards [eventually_ge_atTop N] with n hn
  induction n, hn using Nat.le_induction with
  | base => ring
  | succ n hn ih =>
    rw [halfSum_succ, halfSum_succ]
    have he := hN n hn
    push_cast
    linarith

def rawBackward (x : Base) (j : ℤ) : ℝ :=
  explicitWeight (odometer x) (j-1) / (explicitWeight x j * Real.exp 10)
lemma rawBackward_pos (x : Base) (j : ℤ) : 0 < rawBackward x j := by
  exact div_pos (explicitWeight_pos _ _) (mul_pos (explicitWeight_pos _ _) (Real.exp_pos _))
@[simp] lemma rawBackward_zero (x : Base) : rawBackward x 0 = 1 := by
  simp [rawBackward, ne_of_gt (Real.exp_pos (10:ℝ))]
lemma measurable_rawBackward (j : ℤ) : Measurable (fun x => rawBackward x j) := by
  exact ((measurable_explicitWeight (j-1)).comp odometer_ergodic.measurable).div
    ((measurable_explicitWeight j).mul_const _)
lemma rawBackward_nat_succ (x : Base) (n : ℕ) :
    rawBackward x (n+1) = Real.exp
      (halfSum (plusResidue x) n - halfSum (plusResidue (odometer x)) n +
        halfExponent (plusResidue x) n - 10) := by
  have he : (n:ℤ)+1 = ((n+1:ℕ):ℤ) := by omega
  unfold rawBackward
  rw [add_sub_cancel_right, he]
  simp only [explicitWeight, bilateralWeight_nat, ← Real.exp_add, ← Real.exp_sub, halfSum_succ]
  congr 1
  ring
lemma rawBackward_neg_nat (x : Base) (n : ℕ) :
    rawBackward x (-(n:ℤ)) = Real.exp
      (halfSum (minusResidue (odometer x)) n - halfSum (minusResidue x) n +
        halfExponent (minusResidue (odometer x)) n - 10) := by
  have he : -(n:ℤ)-1 = -((n+1:ℕ):ℤ) := by omega
  simp only [rawBackward, he, explicitWeight, bilateralWeight_neg_nat,
    ← Real.exp_add, ← Real.exp_sub, halfSum_succ]
  congr 1
  ring

lemma sqrt_error_linear (n : ℕ) : 400*Real.sqrt (n:ℝ) ≤ 45*(n:ℝ)+1000 := by
  have hs := Real.sq_sqrt (Nat.cast_nonneg n : (0:ℝ) ≤ n)
  have hp := Real.sqrt_nonneg (n:ℝ)
  nlinarith [sq_nonneg (3*Real.sqrt (n:ℝ)-14)]

lemma halfExponent_linear_upper {t : ℕ → ℕ} (ht : ResidueBounds t) (n : ℕ) :
    halfExponent t n - 10 ≤ 55*(n:ℝ)+1000 := by
  have hh := (residueCorrection_sqrt_bound ht n).trans (sqrt_error_linear n)
  dsimp [halfExponent]
  linarith

lemma tendsto_exp_neg45 (C : ℝ) :
    Tendsto (fun n : ℕ => Real.exp (-45*(n:ℝ)+C)) atTop (𝓝 0) := by
  apply Real.tendsto_exp_atBot.comp
  have ht : Tendsto (fun n : ℕ => (45:ℝ)*(n:ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num)
  simpa only [Function.comp_def, neg_mul] using
    (tendsto_atBot_add_const_right atTop C (tendsto_neg_atTop_atBot.comp ht))

lemma rawBackward_decay {x : Base} (hx : x ∈ goodBase) :
    Tendsto (fun n : ℕ => rawBackward x (n+1)) atTop (𝓝 0) ∧
    Tendsto (fun n : ℕ => rawBackward x (-(n:ℤ))) atTop (𝓝 0) := by
  have hd := halfExponent_drift hx
  obtain ⟨Cp,hCp⟩ := halfSum_eventually_affine (hd.mono (fun _ h => h.1))
  obtain ⟨Cm,hCm⟩ := halfSum_eventually_affine (hd.mono (fun _ h => h.2))
  constructor
  · apply squeeze_zero' (g := fun n : ℕ => Real.exp (-45*(n:ℝ)+(1000-Cp)))
    · exact Filter.Eventually.of_forall fun n => (rawBackward_pos x _).le
    · filter_upwards [hCp] with n hn
      rw [rawBackward_nat_succ]
      apply Real.exp_le_exp.mpr
      have hu := halfExponent_linear_upper (plusResidue_bounds x) n
      linarith
    · exact tendsto_exp_neg45 _
  · apply squeeze_zero' (g := fun n : ℕ => Real.exp (-45*(n:ℝ)+(1000+Cm)))
    · exact Filter.Eventually.of_forall fun n => (rawBackward_pos x _).le
    · filter_upwards [hCm] with n hn
      rw [rawBackward_neg_nat]
      apply Real.exp_le_exp.mpr
      have hu := halfExponent_linear_upper (minusResidue_bounds (odometer x)) n
      linarith
    · exact tendsto_exp_neg45 _

lemma rawBackward_bddAbove {x : Base} (hx : x ∈ goodBase) : BddAbove (Set.range (rawBackward x)) := by
  obtain ⟨C,hC⟩ := (rawBackward_decay hx).1.bddAbove_range
  obtain ⟨D,hD⟩ := (rawBackward_decay hx).2.bddAbove_range
  refine ⟨max C D, ?_⟩
  rintro y ⟨j,rfl⟩
  by_cases hj : 1 ≤ j
  · have he : j = ((j-1).toNat:ℤ)+1 := by omega
    rw [he]
    exact (hC (Set.mem_range_self _)).trans (le_max_left _ _)
  · have he : j = -((-j).toNat:ℤ) := by omega
    rw [he]
    exact (hD (Set.mem_range_self _)).trans (le_max_right _ _)

def backwardBound (x : Base) : ℝ := ⨆ j : ℤ, rawBackward x j
lemma measurable_backwardBound : Measurable backwardBound :=
  Measurable.iSup measurable_rawBackward
lemma backwardBound_ge_one {x : Base} (hx : x ∈ goodBase) : 1 ≤ backwardBound x := by
  rw [← rawBackward_zero x]
  exact le_ciSup (rawBackward_bddAbove hx) 0
lemma rawBackward_le_bound {x : Base} (hx : x ∈ goodBase) (j : ℤ) :
    rawBackward x j ≤ backwardBound x := le_ciSup (rawBackward_bddAbove hx) j

def backwardCoeff (x : Base) (j : ℤ) : ℝ := by
  classical
  exact if x ∈ goodBase then rawBackward x j / backwardBound x else 0
lemma measurable_backwardCoeff (j : ℤ) : Measurable (fun x => backwardCoeff x j) := by
  exact Measurable.ite measurableSet_goodBase
    ((measurable_rawBackward j).div measurable_backwardBound) measurable_const
lemma backwardCoeff_bounds (x : Base) (j : ℤ) :
    0 ≤ backwardCoeff x j ∧ backwardCoeff x j ≤ 1 := by
  unfold backwardCoeff
  split_ifs with hx
  · have hL : 0 < backwardBound x := lt_of_lt_of_le (by norm_num) (backwardBound_ge_one hx)
    exact ⟨(div_pos (rawBackward_pos x j) hL).le, (div_le_one hL).mpr (rawBackward_le_bound hx j)⟩
  · norm_num
end
end BackwardIntertwiners

end OAI


