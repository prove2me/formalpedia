-- Prove2me | Definitions.Def_PrivateContinualCounting_Kraft_Supplement_Hypertree
-- name    : PrivateContinualCounting_Kraft_Supplement_Hypertree
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T21:27:49.199123+00:00
-- url     : https://prove2.me/theorems/291949fc-dc96-4af4-a0cb-3d6a91249868
-- title:
--   The concrete A/B/C hypertree factors and releases
-- statement:
--   At positive time $t$ set $K=\lfloor\log_2t\rfloor$, $J=\lfloor\log_2(K+1)\rfloor$, $\tau=t-2^K+1$, $\kappa=K-(2^J-1)$. For fixed $a>0$ and $0<\xi<1$, set
--   $$q_J=\min\{1/2,a\ln(2^J+2)/(2^J+1)\},\quad y_J=\xi q_J,\quad z_J=(1-\xi)q_J.$$
--   For any raw inner family, explicitly form the decoder and strategy matrices on the countable disjoint union of A coordinates $(K,u)$, B coordinates $(J,u)$ and C coordinates $J$. A uses horizon $2^K$ at budget $1-q_J$, B uses horizon $2^J$ on epoch sums at budget $y_J$, and C uses one independent total release at budget $z_J$. Strategy coefficients are multiplied by square roots of budgets and decoder coefficients are divided by them.
--
--   One fixed product Gaussian seed supplies all coordinates. The noise is the finite sum of the current A decoder row, the B row for the $\kappa$ completed epochs, and every earlier C release. The release is
--   $$Y_t=S_t+N_t=\sum_{j<J}\widehat T_j+\widehat B_J(\kappa)+\widehat A_K(\tau),\qquad N_0=0.$$
--   At $\kappa=0$ the B sum is empty. The matrix product, row/column summability, exact sensitivity and privacy are not built into these raw formulas. The identification predicate relates them to an actual published Gaussian counter; its existence must be proved. Actual variance is defined from the Gaussian noise law. Separate predicates express the all-time envelope $v_t\le(\ln t/\pi)^2+C_0\ln t\ln\ln t$ for $t\ge3$ and the running-maximum ratio limit $\bar v_t/\gamma_2(A_t)^2\to1$.
-- source:
--   Kisung Park, STOC 2027 submission #86 (October 2026), pp. 10–12, PDF pp. 12–14, Section 5 construction; p. 23, PDF p. 25, Appendix E.2

import Definitions.Def_PrivateContinualCounting_Kraft_Supplement_Benchmarks

open MeasureTheory ProbabilityTheory Filter

set_option autoImplicit false

namespace PrivateContinualCounting.Kraft.Supplement

/-- All local times below are positive source times; rows/columns of factors remain zero-based. -/
def epoch (t : ℕ) : ℕ := Nat.log 2 t
def superEpoch (K : ℕ) : ℕ := Nat.log 2 (K+1)
def localTime (t : ℕ) : ℕ := t - 2^(epoch t) + 1
def localEpoch (K : ℕ) : ℕ := K - (2^(superEpoch K)-1)

noncomputable def qBudget (a : ℝ) (J : ℕ) : ℝ :=
  min (1/2) (a * Real.log ((2:ℝ)^J+2) / ((2:ℝ)^J+1))
noncomputable def yBudget (a ξ : ℝ) (J : ℕ) : ℝ := ξ * qBudget a J
noncomputable def zBudget (a ξ : ℝ) (J : ℕ) : ℝ := (1-ξ) * qBudget a J

/-- Disjoint A, B and C coordinates of the one fixed Gaussian seed. -/
abbrev TreeIndex := (ℕ × ℕ) ⊕ ((ℕ × ℕ) ⊕ ℕ)

noncomputable def treeDecoder (F : InnerFamily) (a ξ : ℝ) (r : ℕ) (i : TreeIndex) : ℝ :=
  let t := r+1
  let K := epoch t
  let J := superEpoch K
  let τ := localTime t
  let κ := localEpoch K
  match i with
  | .inl (k,u) => if k = K ∧ u < τ then
      F.decoder (2^K) (τ-1-u) / Real.sqrt (1-qBudget a J) else 0
  | .inr (.inl (j,u)) => if j = J ∧ u < κ then
      F.decoder (2^J) (κ-1-u) / Real.sqrt (yBudget a ξ J) else 0
  | .inr (.inr j) => if j < J then 1 / Real.sqrt (zBudget a ξ j) else 0

noncomputable def treeStrategy (F : InnerFamily) (a ξ : ℝ) (i : TreeIndex) (c : ℕ) : ℝ :=
  let t := c+1
  let K := epoch t
  let J := superEpoch K
  let τ := localTime t
  let κ := localEpoch K
  match i with
  | .inl (k,u) => if k = K ∧ τ-1 ≤ u ∧ u < 2^K then
      Real.sqrt (1-qBudget a J) * F.strategy (2^K) (u-(τ-1)) else 0
  | .inr (.inl (j,u)) => if j = J ∧ κ ≤ u ∧ u < 2^J then
      Real.sqrt (yBudget a ξ J) * F.strategy (2^J) (u-κ) else 0
  | .inr (.inr j) => if j = J then Real.sqrt (zBudget a ξ J) else 0

/-- Direct finite row sum, not defined by a proposed variance identity. -/
noncomputable def treeNoise (F : InnerFamily) (a ξ : ℝ) (t : ℕ) (ω : TreeIndex → ℝ) : ℝ :=
  if t = 0 then 0 else
  let K := epoch t
  let J := superEpoch K
  let τ := localTime t
  let κ := localEpoch K
  (∑ u ∈ Finset.range τ,
      F.decoder (2^K) (τ-1-u) * ω (.inl (K,u))) / Real.sqrt (1-qBudget a J) +
    (∑ u ∈ Finset.range κ,
      F.decoder (2^J) (κ-1-u) * ω (.inr (.inl (J,u)))) / Real.sqrt (yBudget a ξ J) +
    ∑ j ∈ Finset.range J, ω (.inr (.inr j)) / Real.sqrt (zBudget a ξ j)

noncomputable def treeLaw (F : InnerFamily) (a ξ : ℝ) (x : Stream) (n : ℕ) :
    Measure (Fin n → ℝ) :=
  (gaussianSeed TreeIndex).map (fun ω k => prefixSum x (k.val+1) + treeNoise F a ξ (k.val+1) ω)

/-- Exact identification with a counter is a proposition to prove, never construction data. -/
def IsTree (M : GaussianCounter TreeIndex) (F : InnerFamily) (a ξ : ℝ) : Prop :=
  M.factors.L = treeDecoder F a ξ ∧ M.factors.R = treeStrategy F a ξ ∧
  (∀ t, M.noise.value t = treeNoise F a ξ (t+1))

noncomputable def treeVariance (F : InnerFamily) (a ξ : ℝ) (t : ℕ) : ℝ :=
  variance (treeNoise F a ξ t) (gaussianSeed TreeIndex)

/-- The theorem's all-time envelope; C is fixed before time t. -/
def ClockEnvelope (v : ℕ → ℝ) (C : ℝ) : Prop :=
  ∀ t : ℕ, 3 ≤ t → v t ≤ (Real.log (t:ℝ) / Real.pi)^2 +
    C * Real.log (t:ℝ) * Real.log (Real.log (t:ℝ))

def OptimalRatio (v : ℕ → ℝ) : Prop :=
  Tendsto (fun t => runningMax v t / (matrixGamma2 (prefixMatrix t))^2) atTop (nhds 1)

end PrivateContinualCounting.Kraft.Supplement


