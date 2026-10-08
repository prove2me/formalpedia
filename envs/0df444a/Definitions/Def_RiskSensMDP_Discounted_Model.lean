-- Prove2me | Definitions.Def_RiskSensMDP_Discounted_Model
-- name    : RiskSensMDP_Discounted_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T06:27:54.206019+00:00
-- url     : https://prove2.me/theorems/4bc690e7-b1ef-4f39-b119-f4f5ee9e950a
-- title:
--   Bounded positive-cost discounted risk-sensitive model and extended-state operators
-- statement:
--   On the controlled process, let $c(x,a)$ be a measurable cost satisfying $0<\underline c<\overline c$ and $\underline c\le c(x,a)\le\overline c$ for $(x,a)\in D$. Fix $0<\beta<1$ and a utility $U$ continuous and strictly increasing on $[0,\infty)$. The paper's compactness and continuity assumptions (CC) require compact $D(x)$, sequential upper semicontinuity of the action correspondence, lower semicontinuity of $c$ on $D$, and weak continuity of $Q$ for bounded continuous test functions.
--
--   For a history policy $\sigma$, $V_{n\sigma}(x,y,z)$ is its finite-dimensional expectation of $U(y+zC^n_\beta)$, where $C^n_\beta=\sum_{k=0}^{n-1}\beta^kc(X_k,A_k)$. The optimized value and the original objective are
--
--   $$V_n(x,y,z)=\inf_{\sigma\in\Pi}V_{n\sigma}(x,y,z),\qquad J_N(x)=V_N(x,0,1).$$
--
--   The extended state is $\hat E=E\times[0,\infty)\times(0,1]$. A decision rule $f$ is measurable and chooses in $D(x)$. For $(x,y,z)\in\hat E$ the minimal-cost operator is
--
--   $$(Tv)(x,y,z)=\inf_{a\in D(x)}\int v(x',y+zc(x,a),z\beta)\,Q(dx'\mid x,a).$$
--
--   These definitions keep policy evaluation separate from the Bellman identity in Theorem 3.6(b). **Formalization Note** Expectations use nested kernels, the finite-dimensional law of the induced path measure. Lean represents $\hat E$ using real coordinates restricted by the stated domain. The class $C(\hat E)$ uses componentwise nondecreasing sections. Integrability of an arbitrary continuation value is separately named because real integrals otherwise return zero on nonintegrable functions.
-- source:
--   Bäuerle & Rieder, More Risk-Sensitive Markov Decision Processes, authors' manuscript (KIT repository 1000039663; published Math. Oper. Res. 39(1):105–120, 2014), pp. 3–4, §2, pp. 10–11, §3.3, (3.7)–(3.9)

import Mathlib
import Definitions.Def_RiskSensMDP_Discounted_ControlledMDP

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology

namespace RiskSensMDP.Discounted

variable {E A : Type*} [MeasurableSpace E] [MeasurableSpace A]

/-- The strictly discounted bounded-positive-cost setting of §2, pp. 3–4 and §3.3, p. 10. -/
structure Model (E A : Type*) [MeasurableSpace E] [MeasurableSpace A] where
  P : ControlledMDP E A
  c : E × A → ℝ
  lowerCost : ℝ
  upperCost : ℝ
  β : ℝ
  U : ℝ → ℝ

/-- Standing cost and discount assumptions of §2 and §3.3. -/
def HasBounds (M : Model E A) : Prop :=
  Measurable M.c ∧ 0 < M.lowerCost ∧ M.lowerCost < M.upperCost ∧
  (∀ p ∈ M.P.D, M.lowerCost ≤ M.c p ∧ M.c p ≤ M.upperCost) ∧
  0 < M.β ∧ M.β < 1

/-- The five standing conditions (CC), §2, p. 4. Continuity of the kernel is imposed
on `D`, its declared domain. -/
def HasCC [TopologicalSpace E] [TopologicalSpace A] (M : Model E A) : Prop :=
  ContinuousOn M.U (Set.Ici 0) ∧
  StrictMonoOn M.U (Set.Ici 0) ∧
  (∀ x, IsCompact (M.P.actions x)) ∧
  (∀ (xs : ℕ → E) (as : ℕ → A) (x : E),
    Tendsto xs atTop (𝓝 x) →
    (∀ n, as n ∈ M.P.actions (xs n)) →
    ∃ a ∈ M.P.actions x, MapClusterPt a atTop as) ∧
  LowerSemicontinuousOn M.c M.P.D ∧
  (∀ v : BoundedContinuousFunction E ℝ,
    ContinuousOn (fun p : E × A => ∫ x', v x' ∂(M.P.Q p)) M.P.D)

/-- The sum `Σ_{k<length h} βᵏ c(x_k,a_k)` in chronological order (§2, p. 3). -/
def discountedHistoryCost (M : Model E A) : List (E × A) → ℝ
  | [] => 0
  | p :: ps => M.c p + M.β * discountedHistoryCost M ps

/-- Nested transition-kernel integrals giving `E_x^σ[U(z Cⁿ_β+y)]` (3.8),
from a history with current stage `k`. This is the finite-dimensional marginal of
`P_x^σ`, with the accumulated cost and discount carried only to evaluate the terminal
payoff. It is not the Bellman minimum recursion. -/
noncomputable def expectedFrom (M : Model E A) (g : ℕ → History E A → A) :
    ℕ → History E A → ℕ → ℝ → ℝ → ℝ
  | _, _, 0, y, _ => M.U y
  | k, h, n + 1, y, z =>
      ∫ x', expectedFrom M g (k + 1) (h.1 ++ [(h.2, g k h)], x') n
        (y + z * M.c (h.2, g k h)) (z * M.β) ∂(M.P.Q (h.2, g k h))

/-- The policy value in (3.8), expressed by the finite-dimensional law. -/
noncomputable def policyValue (M : Model E A) (σ : Policy M.P)
    (n : ℕ) (x : E) (y z : ℝ) : ℝ :=
  expectedFrom M σ.g 0 ([], x) n y z

/-- `V_n(x,y,z)`, the infimum over every admissible history-dependent policy (3.8). -/
noncomputable def value (M : Model E A) (n : ℕ) (x : E) (y z : ℝ) : ℝ :=
  ⨅ σ : Policy M.P, policyValue M σ n x y z

/-- `J_N(x)` of (3.7), with the empty cost sum zero at `N=0`. -/
noncomputable def objective (M : Model E A) (N : ℕ) (x : E) : ℝ :=
  value M N x 0 1

/-- The extended state `Ê = E × ℝ₊ × (0,1]` is represented by a product of real
types restricted to this domain (§3.3, p. 10). -/
abbrev ExtendedState (E : Type*) := E × (ℝ × ℝ)

def extendedDomain (E : Type*) : Set (ExtendedState E) :=
  {s | 0 ≤ s.2.1 ∧ 0 < s.2.2 ∧ s.2.2 ≤ 1}

def yzDomain : Set (ℝ × ℝ) :=
  {yz | 0 ≤ yz.1 ∧ 0 < yz.2 ∧ yz.2 ≤ 1}

/-- A measurable decision rule on the extended state, admissible at every point of `Ê`. -/
structure DecisionRule (M : Model E A) where
  f : ExtendedState E → A
  measurable_f : Measurable f
  admissible_f : ∀ s ∈ extendedDomain E, (s.1, f s) ∈ M.P.D

/-- The paper's `C(Ê)` (§3.3, p. 10). “Increasing” means nondecreasing in the
product order on `(y,z)`. -/
def InClass [TopologicalSpace E] (M : Model E A)
    (v : ExtendedState E → ℝ) : Prop :=
  LowerSemicontinuousOn v (extendedDomain E) ∧
  (∀ x, ContinuousOn (fun yz : ℝ × ℝ => v (x, yz)) yzDomain) ∧
  (∀ x, MonotoneOn (fun yz : ℝ × ℝ => v (x, yz)) yzDomain) ∧
  (∀ s ∈ extendedDomain E, M.U s.2.1 ≤ v s)

/-- The one-step expected continuation value in (3.9). -/
noncomputable def oneStep (M : Model E A) (v : ExtendedState E → ℝ)
    (s : ExtendedState E) (a : A) : ℝ :=
  ∫ x', v (x', (s.2.1 + s.2.2 * M.c (s.1, a), s.2.2 * M.β))
    ∂(M.P.Q (s.1, a))

/-- Finiteness of the one-step expectation on every admissible extended state.
This is needed when using a real Bochner integral for arbitrary `v ∈ C(Ê)`:
the paper's real-valued class alone does not ensure it on unbounded state spaces. -/
def ContinuationIntegrable (M : Model E A) (v : ExtendedState E → ℝ) : Prop :=
  ∀ s ∈ extendedDomain E, ∀ a ∈ M.P.actions s.1,
    Integrable (fun x' =>
      v (x', (s.2.1 + s.2.2 * M.c (s.1, a), s.2.2 * M.β)))
      (M.P.Q (s.1, a))

/-- `T_f v` in (3.9). -/
noncomputable def decisionOperator (M : Model E A) (f : DecisionRule M)
    (v : ExtendedState E → ℝ) (s : ExtendedState E) : ℝ :=
  oneStep M v s (f.f s)

/-- `T v` in (3.9), the infimum over precisely `D(x)`. -/
noncomputable def minimumOperator (M : Model E A)
    (v : ExtendedState E → ℝ) (s : ExtendedState E) : ℝ :=
  ⨅ a : M.P.actions s.1, oneStep M v s a.1

/-- A minimizer of `v` (§3.1, p. 5, carried into §3.3). -/
def IsMinimizer (M : Model E A) (v : ExtendedState E → ℝ)
    (f : DecisionRule M) : Prop :=
  ∀ s ∈ extendedDomain E, decisionOperator M f v s = minimumOperator M v s

/-- The terminal value `(x,y,z) ↦ U(y)` in Theorem 3.6. -/
def terminal (M : Model E A) (s : ExtendedState E) : ℝ := M.U s.2.1

/-- A Markov policy is an infinite sequence of extended-state decision rules. -/
abbrev MarkovPolicy (M : Model E A) := ℕ → DecisionRule M

/-- The `(y,z)`-shifted embedding of a Markov policy into history rules. At
`(y,z)=(0,1)` it is the policy embedding displayed in Theorem 3.6(c). -/
def historyRule (M : Model E A) (π : MarkovPolicy M) (y z : ℝ)
    (k : ℕ) (h : History E A) : A :=
  (π k).f (h.2, (y + z * discountedHistoryCost M h.1,
    z * M.β ^ k))

/-- `V_{nπ}` in Theorem 3.6(a), evaluated under the shifted embedding. -/
noncomputable def markovValue (M : Model E A) (π : MarkovPolicy M)
    (n : ℕ) (x : E) (y z : ℝ) : ℝ :=
  expectedFrom M (historyRule M π y z) 0 ([], x) n y z

/-- The composition `T_{f₀}⋯T_{f_{n−1}}U` of Theorem 3.6(a). -/
noncomputable def policyIteration (M : Model E A) (π : MarkovPolicy M) :
    ℕ → ExtendedState E → ℝ
  | 0 => terminal M
  | n + 1 => decisionOperator M (π 0)
      (policyIteration M (fun k => π (k + 1)) n)

end RiskSensMDP.Discounted


