-- Prove2me | Definitions.Def_CountingMatroid_Analysis_PositiveTimeTraceKernel
-- name    : CountingMatroid_Analysis_PositiveTimeTraceKernel
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-24T14:08:07.288826+00:00
-- url     : https://prove2.me/theorems/4761397b-b70f-43ca-ab6c-136524068c83
-- title:
--   Finite-horizon and uncapped positive-time return kernels
-- statement:
--   On a finite state space $\Omega$, a subkernel is a real array $K(x,y)\ge0$ with $\sum_yK(x,y)\le1$. Composition, identity, and iteration are
--   $$
--   (KQ)(x,y)=\sum_zK(x,z)Q(z,y),\qquad
--   I(x,y)=\mathbf1_{\{x=y\}},\qquad K^0=I,\quad K^{m+1}=KK^m.
--   $$
--   A stochastic chain is a subkernel with full row mass. For a chain $P$ and target set $A$, the zero-time hitting kernels $H_k$ and positive-time return kernels $R_k$ are
--   $$
--   H_0(x,y)=\mathbf1_{\{x\in A,\ x=y\}},\qquad
--   H_{k+1}(x,y)=
--   \begin{cases}
--   I(x,y),&x\in A,\\
--   \sum_zP(x,z)H_k(z,y),&x\notin A,
--   \end{cases}
--   \qquad
--   R_0=0,\quad R_{k+1}=PH_k.
--   $$
--   Thus hitting can stop at time zero, whereas a return requires at least one transition. Missing mass is retained. Both kernels vanish outside target endpoints, and their entries increase with the horizon. Every subkernel entry is at most one. Consequently the uncapped return subkernel is the entrywise increasing limit
--   $$
--   R_\infty(x,y)=\sup_{k\in\mathbb N}R_k(x,y).
--   $$
--   Writing $v_k(x)$ for the probability of avoiding $A$ at times $0,\ldots,k$, the included identities give $\sum_yH_k(x,y)=1-v_k(x)$ and $\sum_yR_{k+1}(x,y)=1-\sum_zP(x,z)v_k(z)$.
--
--   If a probability distribution $\mu$ is stationary for $P$, its survival mass $V_k=\sum_x\mu(x)v_k(x)$ satisfies
--   $$
--   \sum_{x\in A}\mu(x)\sum_zP(x,z)v_k(z)=V_k-V_{k+1}.
--   $$
--   It follows that for each $x\in A$ with $\mu(x)>0$, positive-time survival tends to zero and $\sum_yR_\infty(x,y)=1$. No irreducibility or full support of $\mu$ is required. This is a probabilistic return statement for those starting states, not a claim that every tape-driven algorithm execution terminates.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/PositiveTimeTraceKernel.lean#L20-L25

import Definitions.Def_CountingMatroidSupport_MarkovChains_Techniques_Dirichlet
import Definitions.Def_CountingMatroidSupport_MarkovChains_Techniques_HittingTime
import Definitions.Def_CountingMatroidSupport_MarkovChains_Techniques_PotentialDecay
import Definitions.Def_CountingMatroidSupport_MarkovChains_Techniques_SpectralGap
import Definitions.Def_CountingMatroidSupport_Probability_Bilinear
import Definitions.Def_CountingMatroidSupport_Probability_FinDist
import Definitions.Def_CountingMatroidSupport_Probability_FinDistFunctional
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Topology.Order.MonotoneConvergence

namespace Arlib.MarkovChains
end Arlib.MarkovChains
namespace Arlib.MarkovChains.FinChain
end Arlib.MarkovChains.FinChain
namespace Arlib.MarkovChains.FinKernel
end Arlib.MarkovChains.FinKernel
namespace Arlib
end Arlib
namespace Arlib.Probability
end Arlib.Probability
namespace Arlib.Probability.FinDist
end Arlib.Probability.FinDist
namespace Arlib.Probability.FinKernel
end Arlib.Probability.FinKernel
section


set_option autoImplicit false

/-!
Finite positive-time return kernels. Each row counts only returns completed
within the horizon; missing mass is retained as abort mass. The construction
uses the library's zero-time hitting recursion only after an initial transition,
so a starting transversal is not mistaken for an immediate return. Stationarity
also proves almost-sure return from positive-mass target states. This module
does not claim the spectral estimate or finite-bit operational coupling.
-/
namespace CountingMatroid.Analysis.PositiveTimeTraceKernel

open Arlib.Probability Arlib.MarkovChains

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]

/-- INTERNAL: A finite nonnegative transition array retaining missing mass.
TEXLINE: main.tex:1023-1030,1207-1212 -/
structure Subkernel (Ω : Type) [Fintype Ω] where
  entry : Ω → Ω → ℝ
  nonneg : ∀ x y, 0 ≤ entry x y
  mass_le_one : ∀ x, ∑ y, entry x y ≤ 1

/-- INTERNAL: Composition retains abort mass rather than conditioning it away.
TEXLINE: main.tex:1207-1212 -/
noncomputable def compose (K Q : Subkernel Ω) : Subkernel Ω where
  entry x y := ∑ z, K.entry x z * Q.entry z y
  nonneg x y := Finset.sum_nonneg fun z _ => mul_nonneg (K.nonneg x z) (Q.nonneg z y)
  mass_le_one x := by
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum]
    calc
      (∑ z, K.entry x z * ∑ y, Q.entry z y) ≤ ∑ z, K.entry x z * 1 :=
        Finset.sum_le_sum fun z _ =>
          mul_le_mul_of_nonneg_left (Q.mass_le_one z) (K.nonneg x z)
      _ ≤ 1 := by simpa only [mul_one] using K.mass_le_one x

/-- INTERNAL: The identity subkernel, for zero trace transitions. -/
noncomputable def identity : Subkernel Ω where
  entry x y := if x = y then 1 else 0
  nonneg x y := by split_ifs <;> norm_num
  mass_le_one x := by simp

/-- INTERNAL: Iterated positive-time return subkernels, keeping every abort.
TEXLINE: main.tex:1163-1176 -/
noncomputable def iterate (K : Subkernel Ω) : ℕ → Subkernel Ω
  | 0 => identity
  | k + 1 => compose K (iterate K k)

/-- INTERNAL: A stochastic underlying chain is a subkernel with no lost mass. -/
noncomputable def ofChain (P : FinChain Ω) : Subkernel Ω where
  entry := P
  nonneg := P.coe_nonneg
  mass_le_one x := (P.sum_coe x).le

/-- INTERNAL: Zero-time hitting restricted to the target set. -/
noncomputable def targetIdentity (A : Finset Ω) : Subkernel Ω where
  entry x y := if x ∈ A ∧ x = y then 1 else 0
  nonneg x y := by split_ifs <;> norm_num
  mass_le_one x := by
    by_cases hx : x ∈ A
    · simp [hx]
    · simp [hx]

/-- INTERNAL: Hitting within k transitions, stopping as soon as A is reached.
At horizon zero this counts only starts already in A.
TEXLINE: main.tex:1047-1053 -/
noncomputable def hitWithin (P : FinChain Ω) (A : Finset Ω) : ℕ → Subkernel Ω
  | 0 => targetIdentity A
  | k + 1 =>
      let Q := compose (ofChain P) (hitWithin P A k)
      { entry := fun x y => if x ∈ A then identity.entry x y else Q.entry x y
        nonneg := fun x y => by
          split_ifs
          · exact identity.nonneg x y
          · exact Q.nonneg x y
        mass_le_one := fun x => by
          by_cases hx : x ∈ A
          · simp only [hx, if_true]
            exact identity.mass_le_one x
          · simp only [hx, if_false]
            exact Q.mass_le_one x }

/-- INTERNAL: Next visit to A within k transitions, including a return at time
one but excluding time zero. Aborts contribute zero.
TEXLINE: main.tex:1023-1030,1163-1176 -/
noncomputable def returnWithin (P : FinChain Ω) (A : Finset Ω) : ℕ → Subkernel Ω
  | 0 =>
      { entry := fun _ _ => 0
        nonneg := fun _ _ => le_rfl
        mass_le_one := fun _ => by simp }
  | k + 1 => compose (ofChain P) (hitWithin P A k)

/-- INTERNAL: Hitting at a target starts and stops there even at horizon zero.
TEXLINE: main.tex:1047-1053 -/
theorem hitWithin_on_target (P : FinChain Ω) (A : Finset Ω) (k : ℕ)
    (x y : Ω) (hx : x ∈ A) :
    (hitWithin P A k).entry x y = if x = y then 1 else 0 := by
  cases k <;> simp [hitWithin, targetIdentity, identity, hx]

/-- INTERNAL: The finite hitting row is exactly the complement of the
library's zero-time survival probability, fixing the time convention.
TEXLINE: main.tex:1023-1030,1047-1053 -/
theorem hitWithin_mass (P : FinChain Ω) (A : Finset Ω) (k : ℕ) (x : Ω) :
    (∑ y, (hitWithin P A k).entry x y) = 1 - survive P A k x := by
  induction k generalizing x with
  | zero =>
      by_cases hx : x ∈ A <;>
        simp [hitWithin, targetIdentity, survive, offTarget, hx]
  | succ k ih =>
      by_cases hx : x ∈ A
      · simp [hitWithin_on_target P A (k + 1) x _ hx,
          survive_eq_zero_of_mem P A (k + 1) hx]
      · simp only [hitWithin, hx, if_false, compose, ofChain]
        rw [Finset.sum_comm]
        simp only [← Finset.mul_sum, ih, mul_sub, mul_one, Finset.sum_sub_distrib,
          P.sum_coe]
        rw [survive_succ_apply, if_neg hx]

/-- INTERNAL: A return is one initial underlying step followed by a
zero-time hit. Its deficit is positive-time survival, rather than zero-time
survival (which vanishes for a starting transversal).
TEXLINE: main.tex:1023-1030 -/
theorem returnWithin_mass_succ (P : FinChain Ω) (A : Finset Ω) (k : ℕ) (x : Ω) :
    (∑ y, (returnWithin P A (k + 1)).entry x y) =
      1 - ∑ z, P x z * survive P A k z := by
  simp only [returnWithin, compose, ofChain]
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum, hitWithin_mass, mul_sub, mul_one,
    Finset.sum_sub_distrib, P.sum_coe]

/-- INTERNAL: Successful finite hits have their endpoint in the target.
TEXLINE: main.tex:1023-1030 -/
theorem hitWithin_supported (P : FinChain Ω) (A : Finset Ω) (k : ℕ)
    (x y : Ω) (hy : y ∉ A) : (hitWithin P A k).entry x y = 0 := by
  induction k generalizing x with
  | zero =>
      simp only [hitWithin, targetIdentity]
      split_ifs with h
      · exact (hy (h.2 ▸ h.1)).elim
      · rfl
  | succ k ih =>
      by_cases hx : x ∈ A
      · rw [hitWithin_on_target P A (k + 1) x y hx]
        exact if_neg (fun h : x = y => hy (h ▸ hx))
      · simp [hitWithin, hx, compose, ofChain, ih]

/-- INTERNAL: Enlarging the allowed hitting horizon can only add successful
endpoint mass; already reached targets remain stopped.
TEXLINE: main.tex:1023-1030,1207-1212 -/
theorem hitWithin_succ_le (P : FinChain Ω) (A : Finset Ω) (k : ℕ) (x y : Ω) :
    (hitWithin P A k).entry x y ≤ (hitWithin P A (k + 1)).entry x y := by
  induction k generalizing x with
  | zero =>
      by_cases hx : x ∈ A
      · rw [hitWithin_on_target P A 0 x y hx,
          hitWithin_on_target P A 1 x y hx]
      · simpa only [hitWithin, targetIdentity, hx, false_and, if_false] using
          (hitWithin P A 1).nonneg x y
  | succ k ih =>
      by_cases hx : x ∈ A
      · rw [hitWithin_on_target P A (k + 1) x y hx,
          hitWithin_on_target P A (k + 1 + 1) x y hx]
      · simp only [hitWithin, hx, if_false, compose, ofChain]
        exact Finset.sum_le_sum fun z _ =>
          mul_le_mul_of_nonneg_left (ih z) (P.coe_nonneg x z)

/-- INTERNAL: Return horizons are monotone, with horizon zero carrying no mass.
TEXLINE: main.tex:1023-1030,1207-1212 -/
theorem returnWithin_monotone (P : FinChain Ω) (A : Finset Ω) (x y : Ω) :
    Monotone (fun k => (returnWithin P A k).entry x y) := by
  apply monotone_nat_of_le_succ
  intro k
  cases k with
  | zero => exact (returnWithin P A 1).nonneg x y
  | succ k =>
      simp only [returnWithin, compose, ofChain]
      exact Finset.sum_le_sum fun z _ =>
        mul_le_mul_of_nonneg_left (hitWithin_succ_le P A k z y) (P.coe_nonneg x z)

omit [DecidableEq Ω] in
/-- INTERNAL: Every individual subkernel entry is bounded by its row budget. -/
theorem entry_le_one (K : Subkernel Ω) (x y : Ω) : K.entry x y ≤ 1 := by
  exact (Finset.single_le_sum (fun z _ => K.nonneg x z) (Finset.mem_univ y)).trans
    (K.mass_le_one x)

/-- INTERNAL: Uniform boundedness makes the uncapped positive-return limit
well defined, even before almost-sure return has been proved.
TEXLINE: main.tex:1023-1030 -/
theorem returnWithin_bddAbove (P : FinChain Ω) (A : Finset Ω) (x y : Ω) :
    BddAbove (Set.range (fun k => (returnWithin P A k).entry x y)) := by
  refine ⟨1, ?_⟩
  rintro z ⟨k, rfl⟩
  exact entry_le_one _ x y

/-- INTERNAL: Monotone convergence of the capped positive-return entries.
TEXLINE: main.tex:1023-1030 -/
theorem returnWithin_tendsto (P : FinChain Ω) (A : Finset Ω) (x y : Ω) :
    Filter.Tendsto (fun k => (returnWithin P A k).entry x y) Filter.atTop
      (nhds (⨆ k, (returnWithin P A k).entry x y)) :=
  tendsto_atTop_ciSup (returnWithin_monotone P A x y) (returnWithin_bddAbove P A x y)

/-- INTERNAL: The uncapped positive-time return subkernel is the increasing
limit of the finite horizons. No normalisation of successful returns is used.
TEXLINE: main.tex:1023-1030,1207-1212 -/
noncomputable def uncappedReturn (P : FinChain Ω) (A : Finset Ω) : Subkernel Ω where
  entry x y := ⨆ k, (returnWithin P A k).entry x y
  nonneg x y := le_trans ((returnWithin P A 0).nonneg x y)
    (le_ciSup (returnWithin_bddAbove P A x y) 0)
  mass_le_one x := by
    have hlim := tendsto_finset_sum Finset.univ
      (fun y _ => returnWithin_tendsto P A x y)
    exact le_of_tendsto hlim (Filter.Eventually.of_forall
      (fun k => (returnWithin P A k).mass_le_one x))









/-- INTERNAL: Stationarity makes the mass of excursions begun on A the
drop in stationary zero-time survival mass.
TEXLINE: main.tex:1023-1030,1072-1087 -/
theorem stationary_survival_drop (P : FinChain Ω) (A : Finset Ω)
    (μ : FinDist Ω) (hstationary : Stationary μ P) (k : ℕ) :
    (∑ x, if x ∈ A then μ x * (∑ z, P x z * survive P A k z) else 0) =
      (∑ x, μ x * survive P A k x) - (∑ x, μ x * survive P A (k + 1) x) := by
  have hstep (x : Ω) :
      (if x ∈ A then μ x * (∑ z, P x z * survive P A k z) else 0) =
        μ x * (∑ z, P x z * survive P A k z) - μ x * survive P A (k + 1) x := by
    rw [survive_succ_apply]
    by_cases hx : x ∈ A <;> simp [hx]
  simp_rw [hstep, Finset.sum_sub_distrib]
  congr 1
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z _
  simp_rw [← mul_assoc]
  rw [← Finset.sum_mul, hstationary z]

/-- INTERNAL: A finite stationary chain returns almost surely from every
positive-mass target state, without a full-support or irreducibility promise.
TEXLINE: main.tex:1023-1030 -/
theorem return_survival_tendsto_zero (P : FinChain Ω) (A : Finset Ω)
    (μ : FinDist Ω) (hstationary : Stationary μ P) (x : Ω)
    (hx : x ∈ A) (hμ : 0 < μ x) :
    Filter.Tendsto (fun k => ∑ z, P x z * survive P A k z)
      Filter.atTop (nhds 0) := by
  let V := fun k => ∑ z, μ z * survive P A k z
  have hanti : Antitone V := by
    intro k l hkl
    exact Finset.sum_le_sum fun z _ =>
      mul_le_mul_of_nonneg_left (survive_antitone P A hkl z) (μ.coe_nonneg z)
  have hbounded : BddBelow (Set.range V) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨k, rfl⟩
    exact Finset.sum_nonneg fun z _ =>
      mul_nonneg (μ.coe_nonneg z) (survive_nonneg P A k z)
  have hlim := tendsto_atTop_ciInf hanti hbounded
  have hdrop : Filter.Tendsto (fun k => V k - V (k + 1)) Filter.atTop (nhds 0) := by
    simpa only [Function.comp_def, sub_self] using hlim.sub (hlim.comp (Filter.tendsto_add_atTop_nat 1))
  have hlower (k : ℕ) : 0 ≤ μ x * (∑ z, P x z * survive P A k z) := by
    exact mul_nonneg hμ.le (Finset.sum_nonneg fun z _ =>
      mul_nonneg (P.coe_nonneg x z) (survive_nonneg P A k z))
  have hupper (k : ℕ) :
      μ x * (∑ z, P x z * survive P A k z) ≤ V k - V (k + 1) := by
    rw [← stationary_survival_drop P A μ hstationary k]
    have hs := Finset.single_le_sum (s := Finset.univ) (a := x)
      (f := fun u => if u ∈ A then μ u * (∑ z, P u z * survive P A k z) else 0)
      (fun u _ => by
        split_ifs
        · exact mul_nonneg (μ.coe_nonneg u) (Finset.sum_nonneg fun z _ =>
            mul_nonneg (P.coe_nonneg u z) (survive_nonneg P A k z))
        · exact le_rfl) (Finset.mem_univ x)
    simpa only [if_pos hx] using hs
  have hprod := squeeze_zero hlower hupper hdrop
  have hdiv := hprod.div_const (μ x)
  simpa only [mul_div_cancel_left₀ _ hμ.ne', zero_div] using hdiv
/-- INTERNAL: The uncapped return row has full mass from positive stationary
target states, as the finite deficits tend to zero.
TEXLINE: main.tex:1023-1030 -/
theorem uncappedReturn_mass_eq_one (P : FinChain Ω) (A : Finset Ω)
    (μ : FinDist Ω) (hstationary : Stationary μ P) (x : Ω)
    (hx : x ∈ A) (hμ : 0 < μ x) :
    (∑ y, (uncappedReturn P A).entry x y) = 1 := by
  have hlim := tendsto_finsetSum Finset.univ
    (fun y _ => (returnWithin_tendsto P A x y).comp (Filter.tendsto_add_atTop_nat 1))
  have hrow : Filter.Tendsto (fun k => ∑ y, (returnWithin P A (k + 1)).entry x y)
      Filter.atTop (nhds 1) := by
    simp_rw [returnWithin_mass_succ]
    simpa only [sub_zero] using
      (return_survival_tendsto_zero P A μ hstationary x hx hμ).const_sub 1
  exact tendsto_nhds_unique hlim hrow
/-- INTERNAL: Positive-time returns are supported on the target set.
TEXLINE: main.tex:1023-1030 -/
theorem returnWithin_supported (P : FinChain Ω) (A : Finset Ω) (k : ℕ)
    (x y : Ω) (hy : y ∉ A) : (returnWithin P A k).entry x y = 0 := by
  cases k with
  | zero => rfl
  | succ k => simp [returnWithin, compose, ofChain, hitWithin_supported P A k _ y hy]

/-- INTERNAL: The increasing uncapped limit preserves target support.
TEXLINE: main.tex:1023-1030 -/
theorem uncappedReturn_supported (P : FinChain Ω) (A : Finset Ω)
    (x y : Ω) (hy : y ∉ A) : (uncappedReturn P A).entry x y = 0 := by
  simp only [uncappedReturn, returnWithin_supported P A _ x y hy, ciSup_const]

end CountingMatroid.Analysis.PositiveTimeTraceKernel

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* 2026-10-09 · proved · built finite and uncapped positive-time return subkernels, their row budgets and cap domination; stationarity proves full return mass at positive-mass target states. The scheduled spectral estimate and finite-bit coupling belong to the consuming children.
-/


end


