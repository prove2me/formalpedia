-- Prove2me | Definitions.Def_ArdaRH65K_Turing121_RHInBoxAnalytic
-- name    : ArdaRH65K_Turing121_RHInBoxAnalytic
-- status  : Definition
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:04:28.022027+00:00
-- url     : https://prove2.me/theorems/e7432eb1-25b8-4f06-9fef-99dca1c249fe
-- title:
--   RHInBoxAnalytic certificate definitions
-- statement:
--   This bundle defines the finite collection of zeta zeros in a complex ball. Let $\mathcal D$ be the set of declarations it provides. Among its named definitions are
--
--   $$\mathcal D\supseteq\{\mathtt{RHInBoxAnalytic.divisor\_ball\_support\_finite\_of\_one\_notMem},\;\mathtt{RHInBoxAnalytic.zeroFinset}\}.$$
--
--   The accompanying theorems establish the mathematical properties of these definitions.
-- source:
--   https://github.com/DrMurphyIsIn/Arda/blob/af4fde8972eb6d4e78c7d9a95933b18b81adf52d/telperion/examples/zeta_zero_localization/lean/RHInBoxAnalytic.lean

import Mathlib
/- Task 2 (parameterized RH-in-a-box): generalize the zeta Blaschke split + box argument
   principle from the merged FIXED ball `ball cB 13` / fixed corners to an ARBITRARY box
   `[sigma0, sigma1] x [T0, T1]` with a VARIABLE Blaschke ball `(c, R)`, the geometry entering
   only as hypotheses `hRpos`, `hbox_ball`, `hs1` (and the box-ordering `hsig`, `hT`).

   This file reproduces, over variable corners and a variable ball, the three merged atoms
     - the per-pole interior winding `Bd((z-ρ)^{-1}) = 2*pi*I` (branch-split primitive),
     - the residue-sum linearity `Bd(∑ d/(z-ρ)) = 2*pi*I*∑ d`,
     - the analytic E-arg-principle `Bd(E) = 0` (Mathlib `integral_boundary_rect_eq_zero...`),
   and the KERNEL-DERIVED local Blaschke split of `logDeriv riemannZeta` over the variable ball
   (`MeromorphicOn.extract_zeros_poles`, E-holomorphicity in-kernel), then composes them into
     `RHInBoxAnalytic.zeta_count_eq_winding_generic`:
   the actual divisor of `riemannZeta` over `ball c R` is nonneg, captures every box zero, and its
   total equals the Arb winding integer `N` (derived from `hwind` via the argument principle).

   Divisor-support finiteness is obtained from `IsCompact.inter_riemannZetaZeros_finite`
   (compact `closedBall c R` meets `riemannZetaZeros` finitely), NOT from meromorphy on the closed
   ball -- so no assumption is needed about the pole `1` on the closed-ball boundary; only
   `1 ∉ ball c R` (open) enters, exactly as the brief requires.

   conjecture1_proved = False.  This is a kernel derivation of a parameterized argument-principle
   count; it does NOT prove RH. -/


open Complex Filter MeasureTheory Real
open scoped Topology

namespace RHInBoxAnalytic

/-! ## Part A: function-agnostic log-derivative transfer across a codiscrete equality.
    (Verbatim from the merged `BlaschkeBox.lean`; pure Mathlib, function-agnostic.) -/







/-! ## Part B: log-derivative of the factorized-rational product.  (Verbatim.) -/





/-! ## Part C: `riemannZeta` meromorphic-order facts on `{1}ᶜ`.  (Verbatim from merged.) -/



/-! ## Part D: generic per-pole interior winding and residue-sum atoms over variable corners.

    Generalizes `WindingCount.winding_lambda_five_rect_winding` and
    `BoxArgPrinciple.box_residue_sum_lambda` from the fixed corners `2/5,3/5,10,35` to variable
    `sigma0 < ρ.re < sigma1`, `T0 < ρ.im < T1`. -/











/-! ## Part E: variable-ball local Blaschke split of `logDeriv riemannZeta`.

    Generalizes `BlaschkeBox.zeta_blaschke_split_box` to an arbitrary ball `(c, R)` whose interior
    avoids `1` (`hs1`) and whose box `[σ0,σ1]x[T0,T1] ⊆ ball c R` (`hbox_ball`).  Divisor
    finiteness comes from `IsCompact.inter_riemannZetaZeros_finite`. -/

/-- The support of `riemannZeta`'s divisor over `ball c R` is finite whenever `1 ∉ ball c R`:
    it sits inside the compact intersection `closedBall c R ∩ riemannZetaZeros`. -/
theorem divisor_ball_support_finite_of_one_notMem
    (c : ℂ) (R : ℝ) (hs1 : (1 : ℂ) ∉ Metric.ball c R) :
    (MeromorphicOn.divisor riemannZeta (Metric.ball c R)).support.Finite := by
  set U := Metric.ball c R with hUdef
  have hUsub : U ⊆ ({1}ᶜ : Set ℂ) := by
    intro z hz
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    rintro rfl; exact hs1 hz
  have hζU : AnalyticOnNhd ℂ riemannZeta U := analyticOn_riemannZeta.mono hUsub
  have hZfin : ((Metric.closedBall c R) ∩ riemannZetaZeros).Finite :=
    (isCompact_closedBall c R).inter_riemannZetaZeros_finite
  apply hZfin.subset
  intro u hu
  rw [Function.mem_support] at hu
  have huU : u ∈ U := (MeromorphicOn.divisor riemannZeta U).supportWithinDomain
    (by rw [Function.mem_support]; exact hu)
  refine ⟨Metric.ball_subset_closedBall huU, ?_⟩
  rw [mem_riemannZetaZeros]
  by_contra hne
  apply hu
  rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hζU huU,
    (hζU u huU).analyticOrderAt_eq_zero.mpr hne]; simp

/-- The actual divisor-support Finset of `riemannZeta` over `ball c R` (needs `1 ∉ ball c R`). -/
noncomputable def zeroFinset (c : ℂ) (R : ℝ) (hs1 : (1 : ℂ) ∉ Metric.ball c R) : Finset ℂ :=
  (divisor_ball_support_finite_of_one_notMem c R hs1).toFinset





/-! ## Part F: the parameterized capstone. -/



end RHInBoxAnalytic


def ArdaRH65K_Turing121_RHInBoxAnalytic : Nat := 0


