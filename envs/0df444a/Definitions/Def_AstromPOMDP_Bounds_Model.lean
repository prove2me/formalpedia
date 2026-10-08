-- Prove2me | Definitions.Def_AstromPOMDP_Bounds_Model
-- name    : AstromPOMDP_Bounds_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T09:55:06.13577+00:00
-- url     : https://prove2.me/theorems/5f91f4ba-d73c-46d7-ab4a-251d0108cbf0
-- title:
--   Finite partially observed controlled Markov model and the values in (2.6), (3.28), (5.3)–(5.4), (5.7)
-- statement:
--   Let the hidden state set $S$ and output set $Y$ be finite and nonempty, let the horizon be $N\ge 1$, and let the control set $U\subseteq\mathbb R^d$ be compact and nonempty. The transition probabilities $p_{ij}(u,t)$ have nonnegative rows summing to one and are continuous in $u\in U$. The output probabilities $q_{ij}$ likewise have nonnegative rows summing to one. The stage loss $g(u,i,t)$ is continuous in $u$, and $p_1$ is the distribution of the state at time one.
--
--   A control law selects $u(t)\in U$ from the first $t$ outputs. Its expected loss is calculated directly from the joint probability of state and output paths:
--   $$J(c)=\sum_{x_{1:N},y_{1:N}}\Pr_c(x_{1:N},y_{1:N})\sum_{t=1}^{N}g(c(y_{1:t},t),x_t,t),\qquad \mathrm{OPT}=\inf_{c\ \mathrm{admissible}}J(c).$$
--
--   The definition also gives the Bayesian vector $z^j_i(u,w)=q_{ij}\sum_s p_{si}(u,t+1)w_s$, its $\ell^1$ norm, the posterior after output $j$, and the three backward values: $V$ for partial observation by (3.28), $V'_k(w)=\sum_i S_k(i)w_i$ with $S$ from (5.4), and $V''$ for open-loop control by (5.7). Each has zero terminal value after stage $N$. These shared objects support the comparison of the three information regimes.
--
--   **Formalization Note** `Fin N` index zero represents time one. The transition controlled at time $t$ has index $t+1$ in (2.1). The model takes the law of $x_1$ as data because the paper gives no control or transition from $x_0$ to $x_1$. Zero-probability outputs use Lean's totalized zero posterior and contribute zero to finite expectations. The minimum over $U$ is a real infimum; compactness and continuity ensure the relevant control families attain finite minima on probability beliefs.
-- source:
--   Åström, Optimal Control of Markov Processes with Incomplete State Information, J. Math. Anal. Appl. 10(1):174–205 (1965), https://doi.org/10.1016/0022-247X(65)90154-X, pp. 177–179 §II (2.1)–(2.6), pp. 183–185 (3.22)–(3.28), pp. 190–191 (5.3)–(5.7)

import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Compactness.Compact
import Mathlib.Data.Finset.Interval

namespace AstromPOMDP.Bounds

/-! Åström, *Optimal Control of Markov Processes with Incomplete State Information*,
J. Math. Anal. Appl. 10 (1965), §II, pp. 177–179, (2.1)–(2.6), and
§III.B–C, pp. 183–185, (3.22)–(3.28). -/

/-- A finite controlled hidden Markov chain with the standing assumptions of §II.
The initial distribution is that of `x₁`; the transition controlled at stage `t`
is `P u (t+1)`, consistently with (3.22) and (3.28). -/
structure Model (St Obs : Type*) [Fintype St] [Fintype Obs]
    (d N : ℕ) where
  U : Set (Fin d → ℝ)
  U_nonempty : U.Nonempty
  U_compact : IsCompact U
  P : (Fin d → ℝ) → ℕ → St → St → ℝ
  P_nonneg : ∀ u ∈ U, ∀ t i j, 0 ≤ P u t i j
  P_sum : ∀ u ∈ U, ∀ t i, ∑ j, P u t i j = 1
  P_cont : ∀ t i j, ContinuousOn (fun u => P u t i j) U
  q : St → Obs → ℝ
  q_nonneg : ∀ i j, 0 ≤ q i j
  q_sum : ∀ i, ∑ j, q i j = 1
  g : (Fin d → ℝ) → St → ℕ → ℝ
  g_cont : ∀ i t, ContinuousOn (fun u => g u i t) U
  p1 : St → ℝ
  p1_nonneg : ∀ i, 0 ≤ p1 i
  p1_sum : ∑ i, p1 i = 1

variable {St Obs : Type*} [Fintype St] [DecidableEq St] [Nonempty St]
  [Fintype Obs] [DecidableEq Obs] [Nonempty Obs]
  {d N : ℕ} [NeZero N]

abbrev Control (d : ℕ) := Fin d → ℝ
abbrev History (Obs : Type*) (t : ℕ) := Fin t → Obs
abbrev Policy (Obs : Type*) (d : ℕ) := (t : ℕ) → History Obs t → Control d
abbrev Belief (St : Type*) := St → ℝ

/-- Restrict a full output path to the first `t` outputs. The `Fin N` index 0
represents the paper's output at time 1. -/
def historyPrefix (y : Fin N → Obs) (t : ℕ) : History Obs t :=
  fun i => y (Fin.ofNat N i.val)

/-- A policy is admissible at every stage 1 through N and every output history. -/
def Admissible (m : Model St Obs d N) (c : Policy Obs d) : Prop :=
  ∀ t, 1 ≤ t → t ≤ N → ∀ h, c t h ∈ m.U

/-- Probability of a complete state/output path under an output-history policy,
using (2.1), (2.2), and conditional independence. -/
noncomputable def jointWeight (m : Model St Obs d N) (c : Policy Obs d)
    (x : Fin N → St) (y : Fin N → Obs) : ℝ :=
  m.p1 (x (Fin.ofNat N 0)) * m.q (x (Fin.ofNat N 0)) (y (Fin.ofNat N 0)) *
    ∏ t ∈ Finset.Icc 1 (N - 1),
      m.P (c t (historyPrefix y t)) (t + 1)
        (x (Fin.ofNat N (t - 1))) (x (Fin.ofNat N t)) *
        m.q (x (Fin.ofNat N t)) (y (Fin.ofNat N t))

/-- Total loss (2.5) on one path, at the paper's times 1 through N. -/
noncomputable def pathCost (m : Model St Obs d N) (c : Policy Obs d)
    (x : Fin N → St) (y : Fin N → Obs) : ℝ :=
  ∑ t ∈ Finset.Icc 1 N, m.g (c t (historyPrefix y t))
    (x (Fin.ofNat N (t - 1))) t

/-- The objective (2.6), calculated directly from the joint law of states
and outputs, without using posterior beliefs. -/
noncomputable def expectedCost (m : Model St Obs d N) (c : Policy Obs d) : ℝ :=
  ∑ x : Fin N → St, ∑ y : Fin N → Obs,
    jointWeight m c x y * pathCost m c x y

/-- P.1's minimal expected loss, over every admissible observation-history law. -/
noncomputable def optimalCost (m : Model St Obs d N) : ℝ :=
  sInf {v : ℝ | ∃ c : Policy Obs d, Admissible m c ∧ v = expectedCost m c}

/-- The finite probability simplex of hidden-state distributions. -/
def IsBelief (w : Belief St) : Prop :=
  (∀ i, 0 ≤ w i) ∧ (∑ i, w i) = 1

/-- The ℓ¹ norm in (3.24), which is not the function type's sup norm. -/
noncomputable def l1 (z : Belief St) : ℝ := ∑ i, |z i|

/-- The vector `z^j(u,w)` in (3.22); the step from time `t` uses `P u (t+1)`. -/
noncomputable def z (m : Model St Obs d N) (t : ℕ)
    (u : Control d) (w : Belief St) (j : Obs) : Belief St :=
  fun i => ∑ s, m.q i j * m.P u (t + 1) s i * w s

/-- Bayes update (3.25). At a zero-probability output the update is the zero
vector; its contribution to (3.28) has coefficient zero. -/
noncomputable def posterior (m : Model St Obs d N) (t : ℕ)
    (u : Control d) (w : Belief St) (j : Obs) : Belief St :=
  fun i => z m t u w j i / l1 (z m t u w j)

/-- The distribution after one unobserved transition, `w P(u)`. -/
noncomputable def predict (m : Model St Obs d N) (t : ℕ)
    (u : Control d) (w : Belief St) : Belief St :=
  fun i => ∑ s, w s * m.P u (t + 1) s i

/-- The law of the first output. -/
noncomputable def firstOutputProb (m : Model St Obs d N) (j : Obs) : ℝ :=
  ∑ i, m.p1 i * m.q i j

/-- The posterior distribution of `x₁` after observing the first output.
It is used only with positive `firstOutputProb` in probability claims. -/
noncomputable def firstBelief (m : Model St Obs d N) (j : Obs) : Belief St :=
  fun i => m.p1 i * m.q i j / firstOutputProb m j

/-- Expectation over the first observation. Zero-probability outputs contribute
zero even though their totalized Bayes posterior is not a probability vector. -/
noncomputable def firstExpectation (m : Model St Obs d N)
    (F : Belief St → ℝ) : ℝ :=
  ∑ j, firstOutputProb m j * F (firstBelief m j)

/-- The right-hand side of (3.28) at a fixed control. -/
noncomputable def bellmanRHS (m : Model St Obs d N) (t : ℕ)
    (Vnext : Belief St → ℝ) (w : Belief St) (u : Control d) : ℝ :=
  (∑ i, m.g u i t * w i) +
    ∑ j, l1 (z m t u w j) * Vnext (posterior m t u w j)

/-- The complete-information right-hand side of (5.4). -/
noncomputable def completeRHS (m : Model St Obs d N) (t : ℕ)
    (Snext : St → ℝ) (i : St) (u : Control d) : ℝ :=
  m.g u i t + ∑ j, m.P u (t + 1) i j * Snext j

/-- The open-loop right-hand side of (5.7). -/
noncomputable def openRHS (m : Model St Obs d N) (t : ℕ)
    (Wnext : Belief St → ℝ) (w : Belief St) (u : Control d) : ℝ :=
  (∑ i, m.g u i t * w i) + Wnext (predict m t u w)

/-- Backward recursion (3.28), indexed by stages remaining. -/
noncomputable def beliefStages (m : Model St Obs d N) : ℕ → Belief St → ℝ
  | 0, _ => 0
  | n + 1, w => ⨅ u : m.U, bellmanRHS m (N - n) (beliefStages m n) w u.val

/-- Backward recursion (5.4), indexed by stages remaining. -/
noncomputable def completeStages (m : Model St Obs d N) : ℕ → St → ℝ
  | 0, _ => 0
  | n + 1, i => ⨅ u : m.U, completeRHS m (N - n) (completeStages m n) i u.val

/-- Backward recursion (5.7), indexed by stages remaining. -/
noncomputable def openStages (m : Model St Obs d N) : ℕ → Belief St → ℝ
  | 0, _ => 0
  | n + 1, w => ⨅ u : m.U, openRHS m (N - n) (openStages m n) w u.val

/-- The solution `V_k` of (3.28), with `V_{N+1}=0`. -/
noncomputable def V (m : Model St Obs d N) (t : ℕ) : Belief St → ℝ :=
  beliefStages m (N + 1 - t)

/-- The solution `S_k` of (5.4), with `S_{N+1}=0`. -/
noncomputable def S (m : Model St Obs d N) (t : ℕ) : St → ℝ :=
  completeStages m (N + 1 - t)

/-- The linear complete-information value `V'_k` of (5.3). -/
noncomputable def Vprime (m : Model St Obs d N) (t : ℕ)
    (w : Belief St) : ℝ := ∑ i, S m t i * w i

/-- The open-loop value `V''_k` of (5.7), with `V''_{N+1}=0`. -/
noncomputable def Vdouble (m : Model St Obs d N) (t : ℕ) : Belief St → ℝ :=
  openStages m (N + 1 - t)

/-- Belief computed recursively from an observation history and a feedback
selector. At time 1 it is the Bayes update of `p₁`; later it uses (3.25). -/
noncomputable def beliefAt (m : Model St Obs d N)
    (a : ℕ → Belief St → Control d) :
    (t : ℕ) → History Obs t → Belief St
  | 0, _ => m.p1
  | t + 1, h =>
      if t = 0 then firstBelief m (h ⟨0, Nat.zero_lt_succ t⟩)
      else posterior m t (a t (beliefAt m a t (fun i => h i.castSucc)))
        (beliefAt m a t (fun i => h i.castSucc))
        (h ⟨t, Nat.lt_succ_self t⟩)

/-- The observation-history policy induced by a feedback selector. -/
noncomputable def feedbackPolicy (m : Model St Obs d N)
    (a : ℕ → Belief St → Control d) : Policy Obs d :=
  fun t h => a t (beliefAt m a t h)

end AstromPOMDP.Bounds


