-- Prove2me | Definitions.Def_OAI_MathematicalPhysics_SheetFlows_Profiles
-- name    : OAI_MathematicalPhysics_SheetFlows_Profiles
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-16T00:53:26.533628+00:00
-- url     : https://prove2.me/theorems/bffe9c39-27e3-4498-8a34-f3b4938a6178
-- title:
--   Smooth plateau and linear cut-off profiles and their $10$-periodizations
-- statement:
--   Let $\psi:\mathbb{R}\to[0,1]$ be the standard smooth transition function, $\psi(s)=E(s)/\bigl(E(s)+E(1-s)\bigr)$ with $E(s)=e^{-1/s}$ for $s>0$ and $E(s)=0$ for $s\le0$; it is $C^\infty$, vanishes on $(-\infty,0]$ and equals $1$ on $[1,\infty)$. This file builds one-dimensional cut-off profiles from $\psi$ and periodizes them.
--
--   1. **Plateau.** For $h,d\in\mathbb{R}$,
--   $$
--   \beta_{h,d}(s)=\psi\Bigl(\frac{2(s+h+d)}{d}\Bigr)\,\psi\Bigl(\frac{2(h+d-s)}{d}\Bigr).
--   $$
--   It is $C^\infty$ and even, and if $d>0$ then $\beta_{h,d}(s)=0$ whenever $|s|\ge h+d$. (By construction, for $d>0$ it equals $1$ when $|s|\le h+d/2$.)
--   2. **Linear profile.** $\lambda_{h,d}(s)=s\,\beta_{h,d}(s)$. It is $C^\infty$ and odd, it vanishes for $|s|\ge h+d$ when $d>0$, and
--   $$
--   \int_{\mathbb{R}}\lambda_{h,d}(s)\,ds=0 .
--   $$
--   3. **Periodization.** For $T\in\mathbb{R}$ and $g:\mathbb{R}\to\mathbb{R}$,
--   $$
--   \Pi_Tg(x)=\sum_{k\in\mathbb{Z}}g(x-Tk).
--   $$
--      - $\Pi_Tg$ is $T$-periodic.
--      - If $T>0$ and $g(x)=0$ for all $x\notin[a,b]$, then every point has a neighbourhood on which $\Pi_Tg$ coincides with a sum over one fixed finite set of indices $k$; if moreover $g$ is $C^\infty$, then so is $\Pi_Tg$.
--      - If $T>0$ and $g(x)=0$ whenever $x\le0$ or $x\ge T$, then $\Pi_Tg(x)=g(x)$ for $x\in[0,T]$, and $\int_{[0,T)}\Pi_Tg(x)\,dx=\int_{\mathbb{R}}g(x)\,dx$.
--      - If $g(x)=0$ whenever $|x|\ge r$, and $r\le c$, $c+r\le T$, then the shifted function $x\mapsto g(x-c)$ vanishes whenever $x\le0$ or $x\ge T$.
--   4. **Periodic profiles.** For $h,d,c\in\mathbb{R}$,
--   $$
--   C_{h,d,c}=\Pi_{10}\bigl[\beta_{h,d}(\cdot-c)\bigr],\qquad D_{h,d,c}=\Pi_{10}\bigl[\lambda_{h,d}(\cdot-c)\bigr].
--   $$
--   Both are $10$-periodic, and both are $C^\infty$ when $d>0$. If $d>0$, $h+d\le c$ and $c+h+d\le10$, then
--   $$
--   \int_{[0,10)}C_{h,d,c}(s)\,ds=\int_{\mathbb{R}}\beta_{h,d}(s)\,ds,\qquad \int_{[0,10)}D_{h,d,c}(s)\,ds=0,
--   $$
--   and if $c'$ satisfies the same two inequalities $h+d\le c'$ and $c'+h+d\le10$, then $\int_{[0,10)}\bigl(C_{h,d,c}(s)-C_{h,d,c'}(s)\bigr)\,ds=0$.
--
--   For $d>0$ and $h+d\le5$ (as in all uses), $C_{h,d,c}$ is a smooth $10$-periodic bump that equals $1$ within distance $h+d/2$ of $c+10\mathbb{Z}$, and $D_{h,d,c}$ is a smooth $10$-periodic profile that equals $s-c$ for $|s-c|\le h+d/2$. Products of such one-dimensional profiles in the three coordinates give the localized, spatially periodic shear velocity fields of an explicit Navier–Stokes flow construction, and the integral identities supply their zero-mean property: either one factor is a $D$-profile, or a $C$-bump is compensated by a translated copy $C_{h,d,c'}$ elsewhere in the period.
--
--   **Formalization Note** The objects are `plateau`, `linearProfile`, `periodize`, `Cprofile` and `Dprofile`; $\psi$ is `Real.smoothTransition` and $E$ is `expNegInvGlue`. `periodize` is a `tsum` over the integers, which Lean evaluates to $0$ for a non-summable family; in all uses $g$ has compact support and the sum is locally finite. Because Lean sets $x/0=0$, the smoothness and parity statements hold for all real $h,d$ (for $d=0$ the plateau is identically $0$).
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/SheetFlows/Profiles.lean

-- Generated from openai/math@1581d4c lean/OAI/MathematicalPhysics/SheetFlows/Profiles.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the SolenoidalSheetPrograms mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_SolenoidalSheetPrograms
import Definitions.Def_OAI_MathematicalPhysics_SheetFlows_DirectForce

namespace OAI

/-! SheetFlows profiles. -/

section
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace Solenoidal

open Filter
open scoped Topology

def plateau (h d : ℝ) (s : ℝ) : ℝ :=
  Real.smoothTransition (2 * (s + h + d) / d) *
    Real.smoothTransition (2 * (h + d - s) / d)

theorem plateau_contDiff (h d : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (plateau h d) := by
  unfold plateau
  fun_prop

theorem plateau_even (h d : ℝ) : Function.Even (plateau h d) := by
  intro s
  have h₁ : -s + h + d = h + d - s := by ring
  have h₂ : h + d - -s = s + h + d := by ring
  simp only [plateau, h₁, h₂, mul_comm]

theorem plateau_zero {h d s : ℝ} (hd : 0 < d) (hs : h + d ≤ |s|) :
    plateau h d s = 0 := by
  rcases le_abs.mp hs with hl | hr
  · have : 2 * (h + d - s) / d ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hd.le
    simp [plateau, Real.smoothTransition.zero_of_nonpos this]
  · have : 2 * (s + h + d) / d ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hd.le
    simp [plateau, Real.smoothTransition.zero_of_nonpos this]

def linearProfile (h d : ℝ) (s : ℝ) : ℝ := s * plateau h d s

theorem linearProfile_contDiff (h d : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (linearProfile h d) :=
  contDiff_id.mul (plateau_contDiff h d)

theorem linearProfile_odd (h d : ℝ) : Function.Odd (linearProfile h d) := by
  intro s
  dsimp [linearProfile]
  rw [plateau_even h d s]
  ring

theorem linearProfile_zero {h d s : ℝ} (hd : 0 < d) (hs : h + d ≤ |s|) :
    linearProfile h d s = 0 := by simp [linearProfile, plateau_zero hd hs]

theorem linearProfile_integral_zero (h d : ℝ) :
    (∫ s : ℝ, linearProfile h d s) = 0 := by
  have he := integral_neg_eq_self (linearProfile h d) (volume : Measure ℝ)
  have ho : (fun s => linearProfile h d (-s)) = fun s => -linearProfile h d s :=
    funext (linearProfile_odd h d)
  rw [ho, integral_neg] at he
  linarith

def periodize (T : ℝ) (g : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∑' k : ℤ, g (x - T * k)

theorem periodize_periodic (T : ℝ) (g : ℝ → ℝ) :
    Function.Periodic (periodize T g) T := by
  intro x
  unfold periodize
  calc
    (∑' k : ℤ, g (x + T - T * k)) =
        ∑' k : ℤ, g (x - T * ((Equiv.subRight (1 : ℤ)) k : ℤ)) := by
      congr 1
      funext k
      congr 1
      simp only [Equiv.subRight_apply, Int.cast_sub, Int.cast_one]
      ring
    _ = ∑' k : ℤ, g (x - T * k) :=
      (Equiv.subRight (1 : ℤ)).tsum_eq (fun k : ℤ => g (x - T * k))

theorem periodize_locally_finite {T a b : ℝ} (hT : 0 < T) (g : ℝ → ℝ)
    (hg : ∀ x, x < a ∨ b < x → g x = 0) (x : ℝ) :
    ∃ K : Finset ℤ, ∀ᶠ y in 𝓝 x,
      periodize T g y = ∑ k ∈ K, g (y - T * k) := by
  let L : ℤ := ⌊(x - 1 - b) / T⌋
  let U : ℤ := ⌈(x + 1 - a) / T⌉
  refine ⟨Finset.Icc L U, ?_⟩
  filter_upwards [Metric.ball_mem_nhds x (show (0 : ℝ) < 1 by norm_num)] with y hy
  apply tsum_eq_sum
  intro k hk
  have hy' : |y - x| < 1 := by simpa [Real.dist_eq] using hy
  rcases abs_lt.mp hy' with ⟨hy₀, hy₁⟩
  have hL : (L : ℝ) * T ≤ x - 1 - b :=
    (le_div_iff₀ hT).mp (Int.floor_le ((x - 1 - b) / T))
  have hU : x + 1 - a ≤ (U : ℝ) * T :=
    (div_le_iff₀ hT).mp (Int.le_ceil ((x + 1 - a) / T))
  simp only [Finset.mem_Icc, not_and_or, not_le] at hk
  rcases hk with hk | hk
  · have hk' : (k : ℝ) < (L : ℝ) := by exact_mod_cast hk
    apply hg
    right
    have he := mul_lt_mul_of_pos_right hk' hT
    linarith
  · have hk' : (U : ℝ) < (k : ℝ) := by exact_mod_cast hk
    apply hg
    left
    have he := mul_lt_mul_of_pos_right hk' hT
    linarith

theorem periodize_contDiff {T a b : ℝ} (hT : 0 < T) (g : ℝ → ℝ)
    (hg : ∀ x, x < a ∨ b < x → g x = 0)
    (hsm : ContDiff ℝ (⊤ : ℕ∞) g) :
    ContDiff ℝ (⊤ : ℕ∞) (periodize T g) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  obtain ⟨K, hK⟩ := periodize_locally_finite hT g hg x
  have h : ContDiff ℝ (⊤ : ℕ∞) (fun y => ∑ k ∈ K, g (y - T * k)) :=
    ContDiff.sum (fun k _ => hsm.comp (contDiff_id.sub contDiff_const))
  exact h.contDiffAt.congr_of_eventuallyEq hK

theorem periodize_on_chart {T : ℝ} (hT : 0 < T) (g : ℝ → ℝ)
    (hg : ∀ x, x ≤ 0 ∨ T ≤ x → g x = 0) {x : ℝ} (hx : x ∈ Set.Icc 0 T) :
    periodize T g x = g x := by
  unfold periodize
  rw [tsum_eq_single (0 : ℤ)]
  · simp
  · intro k hk
    rcases lt_or_gt_of_ne hk with hk | hk
    · have hk' : (k : ℝ) ≤ -1 := by exact_mod_cast (show k ≤ -1 by omega)
      apply hg
      right
      have he := mul_le_mul_of_nonneg_left hk' hT.le
      linarith [hx.1]
    · have hk' : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
      apply hg
      left
      have he := mul_le_mul_of_nonneg_left hk' hT.le
      linarith [hx.2]

theorem periodize_integral_eq {T : ℝ} (hT : 0 < T) (g : ℝ → ℝ)
    (hg : ∀ x, x ≤ 0 ∨ T ≤ x → g x = 0) :
    (∫ x in Set.Ico 0 T, periodize T g x) = ∫ x : ℝ, g x := by
  calc
    (∫ x in Set.Ico 0 T, periodize T g x) = ∫ x in Set.Ico 0 T, g x := by
      apply setIntegral_congr_fun measurableSet_Ico
      intro x hx
      exact periodize_on_chart hT g hg ⟨hx.1, hx.2.le⟩
    _ = ∫ x : ℝ, g x := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      apply hg
      by_cases hl : x < 0
      · exact Or.inl hl.le
      · exact Or.inr (le_of_not_gt (fun hu => hx ⟨le_of_not_gt hl, hu⟩))

theorem shifted_profile_zero_outside {T r c : ℝ} (g : ℝ → ℝ)
    (hg : ∀ x, r ≤ |x| → g x = 0) (hl : r ≤ c) (hu : c + r ≤ T) :
    ∀ x, x ≤ 0 ∨ T ≤ x → g (x - c) = 0 := by
  intro x hx
  apply hg
  rcases hx with hx | hx
  · exact le_abs.mpr (Or.inr (by linarith))
  · exact le_abs.mpr (Or.inl (by linarith))

def Cprofile (h d c : ℝ) : ℝ → ℝ :=
  periodize 10 (fun s => plateau h d (s - c))

def Dprofile (h d c : ℝ) : ℝ → ℝ :=
  periodize 10 (fun s => linearProfile h d (s - c))

theorem Cprofile_periodic (h d c : ℝ) : Function.Periodic (Cprofile h d c) 10 :=
  periodize_periodic _ _

theorem Dprofile_periodic (h d c : ℝ) : Function.Periodic (Dprofile h d c) 10 :=
  periodize_periodic _ _

theorem Cprofile_contDiff (h c : ℝ) {d : ℝ} (hd : 0 < d) :
    ContDiff ℝ (⊤ : ℕ∞) (Cprofile h d c) := by
  apply periodize_contDiff (a := c - (h+d)) (b := c + (h+d)) (by norm_num)
  · intro x hx
    apply plateau_zero hd
    rcases hx with hx | hx
    · exact le_abs.mpr (Or.inr (by linarith))
    · exact le_abs.mpr (Or.inl (by linarith))
  · exact (plateau_contDiff h d).comp (contDiff_id.sub contDiff_const)

theorem Dprofile_contDiff (h c : ℝ) {d : ℝ} (hd : 0 < d) :
    ContDiff ℝ (⊤ : ℕ∞) (Dprofile h d c) := by
  apply periodize_contDiff (a := c - (h+d)) (b := c + (h+d)) (by norm_num)
  · intro x hx
    apply linearProfile_zero hd
    rcases hx with hx | hx
    · exact le_abs.mpr (Or.inr (by linarith))
    · exact le_abs.mpr (Or.inl (by linarith))
  · exact (linearProfile_contDiff h d).comp (contDiff_id.sub contDiff_const)

theorem Cprofile_integral_eq {h d c : ℝ} (hd : 0 < d)
    (hl : h + d ≤ c) (hu : c + (h+d) ≤ 10) :
    (∫ s in Set.Ico 0 10, Cprofile h d c s) = ∫ s : ℝ, plateau h d s := by
  rw [Cprofile, periodize_integral_eq (by norm_num) _
    (shifted_profile_zero_outside _ (fun _ => plateau_zero hd) hl hu)]
  exact integral_sub_right_eq_self _ _

theorem Dprofile_integral_zero {h d c : ℝ} (hd : 0 < d)
    (hl : h + d ≤ c) (hu : c + (h+d) ≤ 10) :
    (∫ s in Set.Ico 0 10, Dprofile h d c s) = 0 := by
  rw [Dprofile, periodize_integral_eq (by norm_num) _
    (shifted_profile_zero_outside _ (fun _ => linearProfile_zero hd) hl hu),
    integral_sub_right_eq_self]
  exact linearProfile_integral_zero h d

theorem Cprofile_corrected_integral_zero {h d c c' : ℝ} (hd : 0 < d)
    (hl : h + d ≤ c) (hu : c + (h+d) ≤ 10)
    (hl' : h + d ≤ c') (hu' : c' + (h+d) ≤ 10) :
    (∫ s in Set.Ico 0 10, Cprofile h d c s - Cprofile h d c' s) = 0 := by
  rw [integral_sub
    ((Cprofile_contDiff h c hd).continuous.integrableOn_Icc.mono_set Set.Ico_subset_Icc_self)
    ((Cprofile_contDiff h c' hd).continuous.integrableOn_Icc.mono_set Set.Ico_subset_Icc_self),
    Cprofile_integral_eq hd hl hu, Cprofile_integral_eq hd hl' hu', sub_self]

end Solenoidal
end
end

end OAI


