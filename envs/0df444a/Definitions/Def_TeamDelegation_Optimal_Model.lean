-- Prove2me | Definitions.Def_TeamDelegation_Optimal_Model
-- name    : TeamDelegation_Optimal_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T05:15:37.617122+00:00
-- url     : https://prove2.me/theorems/f3e87b6e-85b1-43b0-9f35-3a2715a70aa4
-- title:
--   Repeated two-agent team production, delegation, wages and collusion
-- statement:
--   Two agents choose binary effort in a two-state repeated team-production game. State $\omega_1$ occurs with probability $r$, state $\omega_2$ with probability $1-r$; method $\gamma_j$ is correct in state $\omega_j$. With $l\in\{0,1,2\}$ workers, project success has probability $p_l$ under the correct method and $q_l$ otherwise. A's and B's expected one-period utilities are their success bonuses times that probability, less effort cost $e$ if they work and their method-specific adoption costs. Assumption 1 fixes the strict ordering and complementarity relations among these probabilities.
--
--   Under centralisation the principal fixes the correct method. Under delegation A chooses it. The predicate $\operatorname{Implements}(w_A,w_B)$ requires nonnegative success bonuses, a possibly mixed Nash equilibrium of each state game for grim-trigger punishment, and every feasible one-shot deviation inequality with the paper's $(1-\delta)$-normalised continuation and punishment values. The closed forms $w^{\mathrm{cent}},\widehat\Delta_A,\Delta_A^{\max},\Delta_B^{\max},\Delta_A^{\mathrm{crit}},w_A^{\mathrm{del}},w_B^{\mathrm{del}}$ and the aggregate thresholds reproduce equations (9), (16), (19)–(23), (70)–(72), and (74).
--
--   The joint-surplus predicate compares the desired profile with every feasible pure outcome in each state. Collusion-proofness says that no state-contingent distribution over feasible joint outcomes gives both agents weakly greater expected payoffs and at least one a strictly greater payoff.
--
--   **Formalization Note** States and methods are indexed $0,1$ in Lean, representing the paper's $1,2$; effort is Boolean. The standing assumptions explicitly include $0\le r<1$ and $0\le q_0,p_2\le1$. The collusion predicate is stronger than footnote 30's comparison with other subgame-perfect equilibria; the paper's statewise surplus argument establishes this stronger form.
-- source:
--   Upton, Implicit Incentives and Delegation in Teams, TRR 266 Working Paper No. 67 (SSRN 3991736, 17 Dec 2021), p. 7 (PDF 8), §2–§4, Assumption 1, Figures 1–3, equations (4)–(5), (9)–(23), (70)–(74), and footnote 30 on p. 28 (PDF 29)

import Mathlib
import Definitions.Def_TeamDelegation_Optimal_FiniteGame

namespace TeamDelegation.Optimal

noncomputable section

/-- Primitives of Upton's repeated two-agent team production model. -/
structure Params where
  p0 : ℝ
  p1 : ℝ
  p2 : ℝ
  q0 : ℝ
  q1 : ℝ
  q2 : ℝ
  e : ℝ
  δ : ℝ
  r : ℝ

/-- Assumption 1, pp. 8: monotone success probabilities, correct-method advantage,
strict effort complementarity, and a stronger correct-method marginal effort effect. -/
def Params.Assumption1 (P : Params) : Prop :=
  P.p0 < P.p1 ∧ P.p1 < P.p2 ∧ P.q0 < P.q1 ∧ P.q1 < P.q2 ∧
  P.q0 < P.p0 ∧ P.q1 < P.p1 ∧ P.q2 < P.p2 ∧
  P.p1 - P.p0 < P.p2 - P.p1 ∧ P.q1 - P.q0 < P.q2 - P.q1 ∧
  P.q2 - P.q1 < P.p2 - P.p1 ∧ P.q1 - P.q0 < P.p1 - P.p0

/-- The model's standing restrictions. The endpoints on `r`, `q0` and `p2` spell out
that the parameters are probabilities; `r < 1` excludes the degenerate single-state case. -/
def Params.Standing (P : Params) : Prop :=
  0 < P.e ∧ 0 < P.δ ∧ P.δ < 1 ∧ 0 ≤ P.r ∧ P.r < 1 ∧
  0 ≤ P.q0 ∧ P.p2 ≤ 1

/-- Adoption costs of method 1 and method 2 for agents A and B. -/
structure Costs where
  c1A : ℝ
  c2A : ℝ
  c1B : ℝ
  c2B : ℝ

/-- The paper labels the methods so that A weakly prefers method 1 by adoption cost. -/
def Costs.Standing (C : Costs) : Prop := C.c1A ≤ C.c2A

def Costs.deltaA (C : Costs) : ℝ := C.c2A - C.c1A
def Costs.deltaB (C : Costs) : ℝ := C.c2B - C.c1B

def Costs.ofDeltas (c1A c1B ΔA ΔB : ℝ) : Costs :=
  ⟨c1A, c1A + ΔA, c1B, c1B + ΔB⟩

inductive Org | cent | deleg
  deriving DecidableEq

/-- State 0 is ω₁ (probability `r`), state 1 is ω₂ (probability `1-r`). -/
abbrev State := Fin 2
/-- Method 0 is γ₁, method 1 is γ₂; the correct method has the state's index. -/
abbrev Method := Fin 2
/-- Agent A selects a method when delegated and chooses whether to work. -/
abbrev ActA := Method × Bool
/-- Agent B chooses whether to work. -/
abbrev ActB := Bool

/-- With centralisation the principal fixes the correct method; under delegation A may choose either. -/
def FeasibleA (org : Org) (k : State) (a : ActA) : Prop :=
  match org with
  | .cent => a.1 = k
  | .deleg => True

/-- Project success probability at aggregate effort `l` and method `m` in state `k`.
Only `l = 0, 1, 2` arises from the two binary effort choices. -/
def succProb (P : Params) (k : State) (m : Method) (l : ℕ) : ℝ :=
  if m = k then
    if l = 0 then P.p0 else if l = 1 then P.p1 else P.p2
  else
    if l = 0 then P.q0 else if l = 1 then P.q1 else P.q2

/-- Number of working agents. -/
def workers (a : ActA) (b : ActB) : ℕ := a.2.toNat + b.toNat

/-- A's one-period expected payoff from a success-only wage. -/
def payA (P : Params) (C : Costs) (k : State) (a : ActA) (b : ActB)
    (wA : ℝ) : ℝ :=
  succProb P k a.1 (workers a b) * wA -
  (if a.2 then P.e else 0) - (if a.1 = (0 : Method) then C.c1A else C.c2A)

/-- B's one-period expected payoff from a success-only wage. -/
def payB (P : Params) (C : Costs) (k : State) (a : ActA) (b : ActB)
    (wB : ℝ) : ℝ :=
  succProb P k a.1 (workers a b) * wB -
  (if b then P.e else 0) - (if a.1 = (0 : Method) then C.c1B else C.c2B)

/-- The Figure 1–3 stage games. -/
def stageGame (P : Params) (C : Costs) (org : Org) (k : State)
    (wA wB : ℝ) : FiniteGame ActA ActB where
  feasibleA := FeasibleA org k
  feasibleB := fun _ => True
  payoffA := fun a b => payA P C k a b wA
  payoffB := fun a b => payB P C k a b wB

/-- A mixed Nash punishment in one state, including pure profiles as Dirac cases. -/
def IsStageNE (P : Params) (C : Costs) (org : Org) (k : State)
    (wA wB : ℝ) (σ : Mixed ActA ActB) : Prop :=
  (stageGame P C org k wA wB).IsNash σ

/-- Both agents work and the correct production method is used. -/
def desiredA (k : State) : ActA := (k, true)

/-- The `(1-δ)`-normalised continuation value of the desired path for A. -/
def contValueA (P : Params) (C : Costs) (wA : ℝ) : ℝ :=
  P.r * payA P C 0 (desiredA 0) true wA +
  (1 - P.r) * payA P C 1 (desiredA 1) true wA

/-- The `(1-δ)`-normalised continuation value of the desired path for B. -/
def contValueB (P : Params) (C : Costs) (wB : ℝ) : ℝ :=
  P.r * payB P C 0 (desiredA 0) true wB +
  (1 - P.r) * payB P C 1 (desiredA 1) true wB

/-- Expected per-period payoff for A during state-contingent Nash punishments. -/
def punValueA (P : Params) (C : Costs) (org : Org) (wA wB : ℝ)
    (σ : State → Mixed ActA ActB) : ℝ :=
  P.r * (stageGame P C org 0 wA wB).expPayA (σ 0) +
  (1 - P.r) * (stageGame P C org 1 wA wB).expPayA (σ 1)

/-- Expected per-period payoff for B during state-contingent Nash punishments. -/
def punValueB (P : Params) (C : Costs) (org : Org) (wA wB : ℝ)
    (σ : State → Mixed ActA ActB) : ℝ :=
  P.r * (stageGame P C org 0 wA wB).expPayB (σ 0) +
  (1 - P.r) * (stageGame P C org 1 wA wB).expPayB (σ 1)

/-- The §4 grim-trigger implementation test: nonnegative success bonuses, statewise
stage-game Nash punishments, and every feasible one-shot deviation constraint for A
and B. Current-period payoffs have weight `1-δ`; future values have weight `δ`. -/
def Implements (P : Params) (C : Costs) (org : Org) (wA wB : ℝ) : Prop :=
  0 ≤ wA ∧ 0 ≤ wB ∧
  ∃ σ : State → Mixed ActA ActB,
    (∀ k, IsStageNE P C org k wA wB (σ k)) ∧
    ∀ k,
      (∀ a, FeasibleA org k a →
        (1 - P.δ) * payA P C k a true wA + P.δ * punValueA P C org wA wB σ ≤
        (1 - P.δ) * payA P C k (desiredA k) true wA + P.δ * contValueA P C wA) ∧
      ((1 - P.δ) * payB P C k (desiredA k) false wB + P.δ * punValueB P C org wA wB σ ≤
        (1 - P.δ) * payB P C k (desiredA k) true wB + P.δ * contValueB P C wB)

/-- Expected bonus payment for the desired outcome in one period. -/
def wageCost (P : Params) (wA wB : ℝ) : ℝ := P.p2 * (wA + wB)

/-- Success probability under the pure γ₁/shirk punishment, averaged across states. -/
def punishmentMean (P : Params) : ℝ := P.r * P.p0 + (1 - P.r) * P.q0

/-- Equation (9), the optimal equal success bonus under centralisation. -/
def wcent (P : Params) : ℝ := P.e / (P.p2 - (1 - P.δ) * P.p1 - P.δ * P.p0)
/-- Equation (16), A's adoption-cost threshold. -/
def DeltaHatA (P : Params) : ℝ :=
  P.e * (P.p0 - P.q0) / (P.p2 - (1 - P.δ) * P.p1 - P.δ * P.p0)
/-- Equation (19), upper adoption-cost threshold for A. -/
def DeltaMaxA (P : Params) : ℝ :=
  P.e * (P.p1 - (1 - P.δ) * P.q1 - P.δ * punishmentMean P) /
  ((1 - P.δ * P.r) * (P.p2 - P.p1))
/-- Equation (20), upper adoption-cost threshold for B. -/
def DeltaMaxB (P : Params) : ℝ :=
  P.e * (P.p1 - punishmentMean P) / ((1 - P.r) * (P.p2 - P.p1))
/-- Equation (22), the branch threshold in A's delegation wage. -/
def DeltaCritA (P : Params) : ℝ :=
  (P.p1 - P.q1) * P.e /
  (P.p2 - P.p1 * (1 - P.δ * P.r) + P.q1 * P.δ * (1 - P.r) -
    P.δ * punishmentMean P)
/-- Equation (21), A's piecewise delegation bonus. -/
def wdelA (P : Params) (ΔA : ℝ) : ℝ :=
  if ΔA ≤ DeltaCritA P then
    (P.e + P.δ * (1 - P.r) * ΔA) /
      (P.p2 - (1 - P.δ) * P.p1 - P.δ * punishmentMean P)
  else
    (P.e + (1 - P.δ * P.r) * ΔA) /
      (P.p2 - (1 - P.δ) * P.q1 - P.δ * punishmentMean P)
/-- Equation (23), B's delegation bonus. -/
def wdelB (P : Params) (ΔB : ℝ) : ℝ :=
  (P.e + P.δ * (1 - P.r) * ΔB) /
    (P.p2 - (1 - P.δ) * P.p1 - P.δ * punishmentMean P)
/-- Equation (74), the upper aggregate adoption-cost difference for cheaper delegation. -/
def DeltaStarSum (P : Params) : ℝ :=
  2 * P.e * (P.p0 - P.q0) /
    (P.p2 - (1 - P.δ) * P.p1 - P.δ * P.p0)
/-- Equation (70), the lower surplus threshold. -/
def DeltaTilde1 (P : Params) : ℝ :=
  2 * P.e * (P.p0 - (1 - P.δ) * P.p1 - P.δ * punishmentMean P) /
    ((P.p2 - P.p0) * P.δ * (1 - P.r))
/-- Equation (71), the first upper surplus threshold. -/
def DeltaTilde2 (P : Params) : ℝ :=
  (P.p2 - P.q2) * (2 * P.e) /
    (P.p2 - (1 - P.δ) * P.p1 - P.δ * punishmentMean P -
      (P.p2 - P.q2) * P.δ * (1 - P.r))
/-- Equation (72), the second upper surplus threshold. -/
def DeltaTilde3 (P : Params) : ℝ :=
  2 * P.e * ((1 - P.δ) * P.p1 + P.δ * punishmentMean P - P.q0) /
    (P.p2 - P.p2 * P.δ * (1 - P.r) - (1 - P.δ) * P.p1 -
      P.δ * P.r * P.p0)

/-- Equations (59)–(66): eight pure-outcome surplus comparisons. -/
def SurplusConstraints (P : Params) (W Δsum : ℝ) : Prop :=
  (P.p2 - P.p1) * W ≥ P.e ∧
  (P.p2 - P.p0) * W ≥ 2 * P.e ∧
  (P.p2 - P.q2) * W ≥ -Δsum ∧
  (P.p2 - P.q1) * W ≥ P.e - Δsum ∧
  (P.p2 - P.q0) * W ≥ 2 * P.e - Δsum ∧
  (P.p2 - P.q2) * W ≥ Δsum ∧
  (P.p2 - P.q1) * W ≥ P.e + Δsum ∧
  (P.p2 - P.q0) * W ≥ 2 * P.e + Δsum

/-- The desired profile has at least the joint payoff of every feasible pure outcome
in each state. -/
def SurplusMax (P : Params) (C : Costs) (org : Org) (wA wB : ℝ) : Prop :=
  ∀ k a b, FeasibleA org k a →
    payA P C k a b wA + payB P C k a b wB ≤
    payA P C k (desiredA k) true wA + payB P C k (desiredA k) true wB

/-- A statewise probability distribution over feasible joint stage outcomes. -/
def IsOutcomeDist (org : Org) (k : State) (μ : ActA × ActB → ℝ) : Prop :=
  (∀ x, 0 ≤ μ x) ∧ (∑ x, μ x) = 1 ∧
  (∀ x, ¬ FeasibleA org k x.1 → μ x = 0)

/-- Agent A's expected one-period payoff from state-contingent joint lotteries. -/
def avgPayA (P : Params) (C : Costs) (wA : ℝ)
    (μ : State → ActA × ActB → ℝ) : ℝ :=
  P.r * (∑ x, μ 0 x * payA P C 0 x.1 x.2 wA) +
  (1 - P.r) * (∑ x, μ 1 x * payA P C 1 x.1 x.2 wA)

/-- Agent B's expected one-period payoff from state-contingent joint lotteries. -/
def avgPayB (P : Params) (C : Costs) (wB : ℝ)
    (μ : State → ActA × ActB → ℝ) : ℝ :=
  P.r * (∑ x, μ 0 x * payB P C 0 x.1 x.2 wB) +
  (1 - P.r) * (∑ x, μ 1 x * payB P C 1 x.1 x.2 wB)

/-- Strong form of footnote 30: no state-contingent distribution over feasible
stage outcomes Pareto dominates the desired payoff. It implies the paper's
no-other-subgame-perfect-equilibrium criterion. -/
def CollusionProof (P : Params) (C : Costs) (org : Org) (wA wB : ℝ) : Prop :=
  ∀ μ : State → ActA × ActB → ℝ,
    (∀ k, IsOutcomeDist org k (μ k)) →
    ¬ (contValueA P C wA ≤ avgPayA P C wA μ ∧
       contValueB P C wB ≤ avgPayB P C wB μ ∧
       (contValueA P C wA < avgPayA P C wA μ ∨
        contValueB P C wB < avgPayB P C wB μ))

end
end TeamDelegation.Optimal


