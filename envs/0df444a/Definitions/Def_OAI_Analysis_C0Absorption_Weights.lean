-- Prove2me | Definitions.Def_OAI_Analysis_C0Absorption_Weights
-- name    : OAI_Analysis_C0Absorption_Weights
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T21:18:40.613458+00:00
-- url     : https://prove2.me/theorems/624a805c-c9af-4fad-98e6-1ba7e9df5cdf
-- title:
--   Radius schedules and transition angles
-- statement:
--   These notions belong to the construction of a separable Banach space $Z$ that contains no linear copy of $c_0$, yet $Z\times c_0$ is bi-Lipschitz equivalent to $Z$ and $Z$ is Lipschitz-universal for separable metric spaces. $Z$ is a completion of the space of molecules on the unit ball of $c_0$ (finitely supported functions with total sum zero), normed by test functions from carefully chosen Lipschitz classes. Fix $\eta=\frac1{1000}$ and $H=10000$.
--
--   1. **Radii.** $\rho_0=\frac12$ and $\rho_{j+1}=\min\bigl(e^{-H}\rho_j/2,\ \eta/(8L_{j+1})\bigr)$. So $\rho_{j+1}<e^{-H}\rho_j$, $\rho_j\le2^{-(j+1)}$, and $L_j\rho_j\le\eta/4$ for $j\ge1$. The band lengths are $\ell_j=e^{-H}\rho_{j+1}$.
--   2. **Transition angles.**
--   $$
--   \theta_j(u)=\frac\pi{2H}\min\bigl(H,\max(0,\log\rho_j-u)\bigr)\in[0,\tfrac\pi2],
--   $$
--   a function of $u=\log r$. It is $0$ for $u\ge\log\rho_j$ and $\frac\pi2$ for $u\le\log\rho_j-H$, and changes only on the interval $[\log\rho_j-H,\log\rho_j]$.
--   3. **Disjointness.** These transition intervals are pairwise disjoint. So for each $u$ at most one angle is strictly between $0$ and $\frac\pi2$, and $\sum_j|\theta_{j+1}(u)-\theta_{j+1}(v)|\le\frac\pi{2H}|u-v|$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/C0Absorption/Weights.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/C0Absorption/Weights.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the C0Absorption mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_C0Absorption
import Definitions.Def_OAI_Analysis_C0Absorption_Molecules
import Definitions.Def_OAI_Analysis_C0Absorption_Norm
import Definitions.Def_OAI_Analysis_C0Absorption_Completion
import Definitions.Def_OAI_Analysis_C0Absorption_Signs
import Definitions.Def_OAI_Analysis_C0Absorption_Lists
import Definitions.Def_OAI_Analysis_C0Absorption_Pairings
import Definitions.Def_OAI_Analysis_C0Absorption_Localization
import Definitions.Def_OAI_Analysis_C0Absorption_Coordinates
import Definitions.Def_OAI_Analysis_C0Absorption_Triangular
import Definitions.Def_OAI_Analysis_C0Absorption_Tests
import Definitions.Def_OAI_Analysis_C0Absorption_Duality
import Definitions.Def_OAI_Analysis_C0Absorption_Selection
import Definitions.Def_OAI_Analysis_C0Absorption_Supports
import Definitions.Def_OAI_Analysis_C0Absorption_Operations
import Definitions.Def_OAI_Analysis_C0Absorption_Detection
import Definitions.Def_OAI_Analysis_C0Absorption_Grid

namespace OAI

open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
open NormedSpace

namespace C0Absorption
noncomputable section
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

def eta : ℝ := 1/1000
def scheduleH : ℝ := 10000

theorem eta_pos : 0 < eta := by norm_num [eta]
theorem scheduleH_pos : 0 < scheduleH := by norm_num [scheduleH]
theorem schedule_speed : Real.pi/scheduleH ≤ eta/2 := by
  have h := Real.pi_lt_four
  norm_num [scheduleH,eta]
  linarith

theorem bandL_pos (j : ℕ) : 0 < (bandL j : ℝ) := by
  let : Nonempty (BandGrid j) := ⟨fun _ => ⟨0,by constructor; exact neg_nonpos.mpr (Int.natCast_nonneg _); exact Int.natCast_nonneg _⟩⟩
  have hc : (0 : ℝ) < Fintype.card (BandGrid j) := by exact_mod_cast Fintype.card_pos
  simp only [bandL,NNReal.coe_mul,NNReal.coe_ofNat,NNReal.coe_natCast,NNReal.coe_pow]
  positivity

def rho : ℕ → ℝ
  | 0 => 1/2
  | j+1 => min (Real.exp (-scheduleH)*rho j/2) (eta/(8*bandL (j+1)))

theorem rho_pos (j : ℕ) : 0 < rho j := by
  induction j with
  | zero => norm_num [rho]
  | succ j ih =>
    change 0 < min _ _
    exact lt_min (by positivity) (div_pos eta_pos (mul_pos (by norm_num) (bandL_pos _)))

theorem rho_step (j : ℕ) : rho (j+1) < Real.exp (-scheduleH)*rho j := by
  have hp : 0 < Real.exp (-scheduleH)*rho j := mul_pos (Real.exp_pos _) (rho_pos j)
  exact (min_le_left _ _).trans_lt (by linarith)

theorem rho_half_step (j : ℕ) : rho (j+1) ≤ rho j/2 := by
  have he : Real.exp (-scheduleH) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num [scheduleH])
  exact (min_le_left _ _).trans (div_le_div_of_nonneg_right
    (by nlinarith [rho_pos j]) (by norm_num))

theorem rho_bound (j : ℕ) : rho j ≤ (1/2 : ℝ)^(j+1) := by
  induction j with
  | zero => norm_num [rho]
  | succ j ih =>
    refine (rho_half_step j).trans ?_
    rw [pow_succ]
    linarith

theorem rho_lip_budget {j : ℕ} (hj : 0 < j) : bandL j*rho j ≤ eta/4 := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hj)
  have hh : rho (k+1) ≤ eta/(8*bandL (k+1)) := min_le_right _ _
  have hp := bandL_pos (k+1)
  have he := (le_div_iff₀ (mul_pos (by norm_num : (0:ℝ)<8) hp)).mp hh
  linarith [eta_pos]

theorem rho_tendsto : Tendsto rho atTop (nhds 0) := by
  apply squeeze_zero (fun j => (rho_pos j).le) rho_bound
  exact (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ)≤1/2) (by norm_num)).comp
    (tendsto_add_atTop_nat 1)

def ell (j : ℕ) : ℝ := Real.exp (-scheduleH)*rho (j+1)

theorem ell_pos (j : ℕ) : 0 < ell j := mul_pos (Real.exp_pos _) (rho_pos _)
theorem ell_tendsto : Tendsto ell atTop (nhds 0) := by
  change Tendsto (fun j => Real.exp (-scheduleH)*rho (j+1)) atTop (nhds 0)
  convert (tendsto_const_nhds (x := Real.exp (-scheduleH))).mul (rho_tendsto.comp (tendsto_add_atTop_nat 1)) using 1 <;> simp

theorem log_rho_step (j : ℕ) : Real.log (rho (j+1)) < Real.log (rho j)-scheduleH := by
  have hh := Real.strictMonoOn_log (rho_pos (j+1))
    (mul_pos (Real.exp_pos _) (rho_pos j)) (rho_step j)
  rwa [Real.log_mul (Real.exp_pos _).ne' (rho_pos j).ne',Real.log_exp,neg_add_eq_sub] at hh

def transitionAngle (j : ℕ) (u : ℝ) : ℝ :=
  Real.pi/(2*scheduleH) * min scheduleH (max 0 (Real.log (rho j)-u))

theorem transitionAngle_nonneg (j : ℕ) (u : ℝ) : 0 ≤ transitionAngle j u := by
  unfold transitionAngle
  exact mul_nonneg (div_nonneg Real.pi_pos.le (by norm_num [scheduleH] : 0 ≤ 2*scheduleH))
    (le_min scheduleH_pos.le (le_max_left _ _))

theorem transitionAngle_le (j : ℕ) (u : ℝ) : transitionAngle j u ≤ Real.pi/2 := by
  have hh : min scheduleH (max 0 (Real.log (rho j)-u)) ≤ scheduleH := min_le_left _ _
  have hc : 0 ≤ Real.pi/(2*scheduleH) := div_nonneg Real.pi_pos.le (by norm_num [scheduleH])
  have hb := mul_le_mul_of_nonneg_left hh hc
  have he : Real.pi/(2*scheduleH)*scheduleH=Real.pi/2 := by norm_num [scheduleH]; ring
  exact hb.trans_eq he

theorem transitionAngle_zero (j : ℕ) {u : ℝ} (hu : Real.log (rho j) ≤ u) :
    transitionAngle j u=0 := by
  simp only [transitionAngle,max_eq_left (by linarith : Real.log (rho j)-u ≤ 0),
    min_eq_right scheduleH_pos.le,mul_zero]

theorem transitionAngle_full (j : ℕ) {u : ℝ} (hu : u ≤ Real.log (rho j)-scheduleH) :
    transitionAngle j u=Real.pi/2 := by
  unfold transitionAngle
  rw [min_eq_left (le_max_of_le_right (by linarith : scheduleH ≤ Real.log (rho j)-u))]
  norm_num [scheduleH]
  ring

theorem transitionAngle_dichotomy (j : ℕ) (u : ℝ) :
    transitionAngle (j+1) u=0 ∨ transitionAngle j u=Real.pi/2 := by
  by_cases hu : Real.log (rho (j+1)) ≤ u
  · exact Or.inl (transitionAngle_zero (j+1) hu)
  · exact Or.inr (transitionAngle_full j (by linarith [log_rho_step j]))

def transitionInterval (j : ℕ) : Set ℝ := Icc (Real.log (rho j)-scheduleH) (Real.log (rho j))

theorem log_rho_antitone : Antitone (fun j => Real.log (rho j)) := by
  apply antitone_nat_of_succ_le
  intro j
  linarith [log_rho_step j,scheduleH_pos]

theorem transitionInterval_disjoint : Pairwise (fun i j => Disjoint (transitionInterval i) (transitionInterval j)) := by
  suffices ∀ i j, i<j → Disjoint (transitionInterval i) (transitionInterval j) by
    intro i j hij
    rcases lt_or_gt_of_ne hij with hh|hh
    · exact this i j hh
    · exact (this j i hh).symm
  intro i j hij
  have hh := (log_rho_antitone (Nat.succ_le_of_lt hij)).trans_lt (log_rho_step i)
  apply Set.disjoint_left.mpr
  intro u hi hj
  exact (not_le_of_gt hh) (hi.1.trans hj.2)

end
end C0Absorption

namespace C0Absorption
noncomputable section
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

theorem finite_variation_sum_lipschitz {A : Type*} [Fintype A]
    (f : A → ℝ → ℝ) (C : A → Set ℝ) {K : ℝ≥0}
    (hdis : Pairwise (fun i j => Disjoint (C i) (C j)))
    (hf : ∀ i, LipschitzWith K (f i))
    (hconst : ∀ i x, x ∉ C i → ∀ᶠ y in nhds x, f i y=f i x) :
    LipschitzWith K (fun x => ∑ i,f i x) := by
  classical
  have hloc (x : ℝ) : ∀ᶠ y in nhds x,
      dist (∑ i,f i x) (∑ i,f i y) ≤ K*dist x y := by
    by_cases h : ∃ i, x ∈ C i
    · obtain ⟨j,hj⟩ := h
      have hh (i : A) : i ≠ j → ∀ᶠ y in nhds x, f i y=f i x := by
        intro hij
        exact hconst i x (fun hi => Set.disjoint_left.mp (hdis hij) hi hj)
      have he : ∀ᶠ y in nhds x, ∀ i, i≠j → f i y=f i x :=
        Filter.eventually_all.mpr (fun i => by
          by_cases hij : i=j
          · exact Filter.Eventually.of_forall (by simp [hij])
          · filter_upwards [hh i hij] with y hy using fun _ => hy)
      filter_upwards [he] with y hy
      rw [Real.dist_eq,← Finset.sum_sub_distrib,
        Finset.sum_eq_single j (fun i _ hij => by rw [hy i hij,sub_self]) (by simp)]
      exact (hf j).dist_le_mul x y
    · push Not at h
      filter_upwards [Filter.eventually_all.mpr (fun i => hconst i x (h i))] with y hy
      simp only [hy,dist_self]
      positivity
  have hc : Continuous (fun x => ∑ i,f i x) := continuous_finsetSum _ (fun i _ => (hf i).continuous)
  have hl := lipschitzOn_convex_of_local (convex_univ : Convex ℝ (univ : Set ℝ)) hc.continuousOn
    (fun x _ => by simpa only [nhdsWithin_univ] using hloc x)
  apply LipschitzWith.of_dist_le_mul
  intro x y
  exact hl.dist_le_mul x (mem_univ _) y (mem_univ _)

def angleSpeed : ℝ≥0 := ⟨Real.pi/(2*scheduleH),div_nonneg Real.pi_pos.le (by norm_num [scheduleH])⟩

theorem transitionAngle_lipschitz (j : ℕ) : LipschitzWith angleSpeed (transitionAngle j) := by
  have hl : LipschitzWith 1 (fun u : ℝ => Real.log (rho j)-u) := by
    apply LipschitzWith.of_dist_le_mul
    intro u v
    simp only [Real.dist_eq,sub_sub_sub_cancel_left,NNReal.coe_one,one_mul,abs_sub_comm,le_refl]
  have hb := (hl.const_max 0).const_min scheduleH
  apply LipschitzWith.of_dist_le_mul
  intro u v
  change |angleSpeed*(min scheduleH (max 0 (Real.log (rho j)-u)))-
      angleSpeed*(min scheduleH (max 0 (Real.log (rho j)-v)))| ≤ _
  rw [← mul_sub,abs_mul,abs_of_nonneg angleSpeed.coe_nonneg]
  exact mul_le_mul_of_nonneg_left (by simpa only [NNReal.coe_one,one_mul,Real.dist_eq] using hb.dist_le_mul u v) angleSpeed.coe_nonneg

theorem transitionAngle_antitone (j : ℕ) : Antitone (transitionAngle j) := by
  intro u v huv
  apply mul_le_mul_of_nonneg_left _ angleSpeed.coe_nonneg
  exact min_le_min_left _ (max_le_max_left _ (by linarith))

theorem transitionAngle_locally_constant (j : ℕ) (u : ℝ) (hu : u ∉ transitionInterval j) :
    ∀ᶠ v in nhds u, transitionAngle j v=transitionAngle j u := by
  have h : u < Real.log (rho j)-scheduleH ∨ Real.log (rho j)<u := by
    change ¬(Real.log (rho j)-scheduleH ≤ u ∧ u ≤ Real.log (rho j)) at hu
    rcases lt_or_ge u (Real.log (rho j)-scheduleH) with h|h
    · exact Or.inl h
    · right
      by_contra hn
      exact hu ⟨h,le_of_not_gt hn⟩
  rcases h with h|h
  · filter_upwards [eventually_lt_nhds h] with v hv
    rw [transitionAngle_full j hv.le,transitionAngle_full j h.le]
  · filter_upwards [eventually_gt_nhds h] with v hv
    rw [transitionAngle_zero j hv.le,transitionAngle_zero j h.le]

theorem angle_sum_distance (J : ℕ) (u v : ℝ) :
    (∑ j : Fin J, |transitionAngle (j+1) u-transitionAngle (j+1) v|) ≤
      angleSpeed*dist u v := by
  have hh := finite_variation_sum_lipschitz
    (fun j : Fin J => transitionAngle (j+1)) (fun j : Fin J => transitionInterval (j+1))
    (fun i j hij => transitionInterval_disjoint (by intro he; exact hij (Fin.ext (by omega))))
    (fun j => transitionAngle_lipschitz (j+1))
    (fun j => transitionAngle_locally_constant (j+1))
  have he (x y : ℝ) (hxy : x≤y) :
      (∑ j : Fin J, |transitionAngle (j+1) x-transitionAngle (j+1) y|) =
        dist (∑ j : Fin J,transitionAngle (j+1) x) (∑ j : Fin J,transitionAngle (j+1) y) := by
    rw [Real.dist_eq,← Finset.sum_sub_distrib,abs_of_nonneg]
    · apply Finset.sum_congr rfl
      intro j _
      exact abs_of_nonneg (sub_nonneg.mpr (transitionAngle_antitone (j+1) hxy))
    · exact Finset.sum_nonneg (fun j _ => sub_nonneg.mpr (transitionAngle_antitone (j+1) hxy))
  rcases le_total u v with huv|hvu
  · rw [he u v huv]
    exact hh.dist_le_mul u v
  · have heq : (∑ j : Fin J, |transitionAngle (j+1) u-transitionAngle (j+1) v|)=
        ∑ j : Fin J, |transitionAngle (j+1) v-transitionAngle (j+1) u| :=
        Finset.sum_congr rfl (fun j _ => abs_sub_comm _ _)
    rw [heq,he v u hvu]
    simpa only [dist_comm] using hh.dist_le_mul v u

end
end C0Absorption

end OAI


