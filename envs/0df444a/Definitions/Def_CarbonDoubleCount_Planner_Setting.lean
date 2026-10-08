-- Prove2me | Definitions.Def_CarbonDoubleCount_Planner_Setting
-- name    : CarbonDoubleCount_Planner_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T07:46:53.770666+00:00
-- url     : https://prove2.me/theorems/ed41fda5-a9b6-4d96-869c-6e4f8cb6ac79
-- title:
--   §3, pp. 8–11 — effort boxes, marginal footprints, social first best (1), and decentralized Nash equilibrium (4)
-- statement:
--   This definition fixes the supply-chain model of §3 of the paper. There are finitely many firms $n\in\mathcal N$, each with finitely many abatement actions $j\in\{1,\dots,m_n\}$, and finitely many emission-producing processes $i\in\mathcal I$. An effort profile is $e=(e_{n,j})$, and firm $n$'s own vector is $e_n$. Firm $n$ has profit $V_n(e_n)$, and the footprint of process $i$ is $f_i(e)$. A payment rule $h=(h_n)$ makes firm $n$ pay $h_n(\phi)$ when the footprint vector is $\phi$.
--
--   1. **Effort boxes.** The collective box is $[0,A]^M$, i.e. $0\le e_{n,j}\le A$ for every firm and action. Firm $n$'s box is $[0,A]^{m_n}$.
--   2. **Partial derivatives.** $\partial F/\partial e_{n,j}$ at $e$ is the derivative of $t\mapsto F(e)$ with the single coordinate $e_{n,j}$ replaced by $t$. Likewise, $\partial H/\partial f_i$ at $\phi$ is the derivative of $t\mapsto H(\phi)$ with the coordinate $\phi_i$ replaced by $t$.
--   3. **Social value and first best (1).** For a carbon price $c$,
--   $$
--   S_c(e)=\sum_{n\in\mathcal N}V_n(e_n)-c\sum_{i\in\mathcal I}f_i(e).
--   $$
--   A profile $e$ is a **first best** at price $c$ if it lies in the box and $S_c(e')\le S_c(e)$ for every $e'$ in the box.
--   4. **Nash equilibrium of (4).** A profile $e$ in the box is a Nash equilibrium under $h$ if, for every firm $n$ and every vector $x$ in firm $n$'s box,
--   $$
--   V_n(x)-h_n\big(f(x,e_{-n})\big)\le V_n(e_n)-h_n\big(f(e)\big).
--   $$
--   Here $(x,e_{-n})$ replaces firm $n$'s vector by $x$ and keeps the other firms' efforts fixed. This is the pure Nash definition of the preceding item, applied to these boxes and payoffs.
--   5. **Joint carbon production.** A real matrix $B=(b_{n,i})$ exhibits joint production if $\sum_n b_{n,i}\ge2$ for some process $i$.
--   6. **Double counting at $\phi$.** A rule $h$ double-counts at price $c$ and footprint vector $\phi$ if $\sum_n \partial h_n/\partial f_i(\phi)>c$ for some process $i$.
--
--   These are the objects that the statements of Lemma 7 and Propositions 2 and 3 are about. None of the paper's analytic assumptions (differentiability, concavity, convexity, monotonicity, non-negativity) is built into the definitions; each theorem states them as hypotheses.
--
--   **Formalization Note** Firms, actions and processes are arbitrary finite types. The first best is a feasible global maximizer, not a real supremum, so it is never a default value. The Nash condition tests every feasible deviation of a firm's whole effort vector, not a first-order condition. A partial derivative of a function that is not differentiable is $0$ in Lean, so every theorem using them assumes the differentiability the paper assumes.
-- source:
--   Caro, Corbett, Tan and Zuidwijk, Double-Counting in Supply Chain Carbon Footprinting, working paper dated December 21, 2012, pp. 8–11, §§3.1–3.3 and §4; https://www.anderson.ucla.edu/documents/areas/fac/dotm/bio/pdf_FC16.pdf

import Mathlib
import Definitions.Def_CarbonDoubleCount_Planner_PureGame

namespace CarbonDoubleCount.Planner

variable {ι : Type} {act : ι → Type} {κ : Type}
variable [Fintype ι] [DecidableEq ι]
variable [∀ n, Fintype (act n)] [∀ n, DecidableEq (act n)]
variable [Fintype κ] [DecidableEq κ]

/-- The collective effort box `[0,A]^M` of §3.1. -/
def effortBox (A : ℝ) : Set ((n : ι) → act n → ℝ) :=
  {e | ∀ n j, 0 ≤ e n j ∧ e n j ≤ A}

/-- The feasible actions for firm `n`. -/
def firmBox (A : ℝ) (n : ι) : Set (act n → ℝ) :=
  {x | ∀ j, 0 ≤ x j ∧ x j ≤ A}

/-- Partial derivative with respect to firm `n`'s action `j`. -/
noncomputable def dEff (F : ((n : ι) → act n → ℝ) → ℝ)
    (e : (n : ι) → act n → ℝ) (n : ι) (j : act n) : ℝ :=
  deriv (fun t => F (Function.update e n (Function.update (e n) j t))) (e n j)

/-- Partial derivative with respect to the footprint of process `i`. -/
noncomputable def dFoot (H : (κ → ℝ) → ℝ) (φ : κ → ℝ) (i : κ) : ℝ :=
  deriv (fun t => H (Function.update φ i t)) (φ i)

/-- The objective of the social planner's problem (1). -/
def socialValue (V : (n : ι) → (act n → ℝ) → ℝ)
    (f : ((n : ι) → act n → ℝ) → κ → ℝ) (c : ℝ)
    (e : (n : ι) → act n → ℝ) : ℝ :=
  (∑ n, V n (e n)) - c * (∑ i, f e i)

/-- Feasible global maximizer of the social planner's problem (1). -/
def IsFirstBest (A : ℝ) (V : (n : ι) → (act n → ℝ) → ℝ)
    (f : ((n : ι) → act n → ℝ) → κ → ℝ) (c : ℝ)
    (e : (n : ι) → act n → ℝ) : Prop :=
  e ∈ effortBox A ∧ ∀ e' ∈ effortBox A, socialValue V f c e' ≤ socialValue V f c e

/-- Global unilateral best responses in the decentralized game (4). -/
def IsNash (A : ℝ) (V : (n : ι) → (act n → ℝ) → ℝ)
    (f : ((n : ι) → act n → ℝ) → κ → ℝ)
    (h : ι → (κ → ℝ) → ℝ) (e : (n : ι) → act n → ℝ) : Prop :=
  IsPureNash (fun n => firmBox A n)
    (fun n e => V n (e n) - h n (f e)) e

/-- At least two firms influence one process, as in §3.1. -/
def JointProduction (B : ι → κ → ℝ) : Prop :=
  ∃ i, 2 ≤ ∑ n, B n i

/-- Aggregate marginal payment exceeds the carbon price at `φ`, as in §3.3. -/
noncomputable def DoubleCounts (h : ι → (κ → ℝ) → ℝ)
    (c : ℝ) (φ : κ → ℝ) : Prop :=
  ∃ i, c < ∑ n, dFoot (h n) φ i

end CarbonDoubleCount.Planner


