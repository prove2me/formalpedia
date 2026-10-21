-- Prove2me | Definitions.Def_FlowsNetworks_TwoArcs_TwoArcValue
-- name    : FlowsNetworks_TwoArcs_TwoArcValue
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-20T15:36:16.185466+00:00
-- url     : https://prove2.me/theorems/10e527f0-7447-447e-b588-6862b0f30f5e
-- title:
--   $\bar v_i(\xi)$, $\bar v_{ij}(\xi,\eta)$, the difference quotient $q_{ij}$ of (13.12) and the constant $p_{ij}$ of (13.11)
-- statement:
--   Fix a network $[N;\mathcal A]$ with sources $S$ and sinks $T$, finite nonnegative capacities $c$ on its arcs, and arcs $A_i$, $A_j$.
--
--   1. $\bar v_i(\xi)$, for $\xi\in[0,\infty]$, is the maximal flow value from $S$ to $T$ when the capacity $c(A_i)$ is replaced by $\xi$ and all other capacities are kept.
--   2. $\bar v_{ij}(\xi,\eta)$, for $\xi,\eta\in[0,\infty]$, is the maximal flow value when $c(A_i)$ is replaced by $\xi$ and $c(A_j)$ by $\eta$.
--   3. For real $\xi,\eta,h,k$ with $\xi\ge0$, $\eta\ge0$, $\xi+h\ge0$, $\eta+k\ge0$ and $hk\neq0$ (an **admissible rectangle** in the nonnegative $\xi$–$\eta$ quadrant), the **difference quotient** is
--   $$q_{ij} = \frac{\bar v_{ij}(\xi+h,\eta+k) - \bar v_{ij}(\xi+h,\eta) - \bar v_{ij}(\xi,\eta+k) + \bar v_{ij}(\xi,\eta)}{hk}.$$
--   4. The constant
--   $$p_{ij} = \bar v_{ij}(\infty,\infty) - \bar v_{ij}(0,\infty) - \bar v_{ij}(\infty,0) + \bar v_{ij}(0,0)$$
--   is evaluated in extended arithmetic: writing $P=\bar v_{ij}(\infty,\infty)+\bar v_{ij}(0,0)$ and $M=\bar v_{ij}(0,\infty)+\bar v_{ij}(\infty,0)$, $p_{ij}$ is **indeterminate** ($\infty-\infty$) if $P=M=\infty$, equal to $+\infty$ if only $P=\infty$, to $-\infty$ if only $M=\infty$, and to the real number $P-M$ otherwise.
--
--   The sign of $q_{ij}$ measures whether the two arcs reinforce ($q_{ij}>0$) or interfere with ($q_{ij}<0$) each other as their capacities vary, and $p_{ij}$ classifies which of the two happens.
--
--   **Formalization Note** $\xi,\eta$ range over `ℝ≥0∞` in $\bar v_i$ and $\bar v_{ij}$, so the book's $\bar v_{ij}(0,\infty)$ etc. are literal values. The quotient uses the real-valued $\bar v_{ij}$ at finite arguments (`toReal` of the `ℝ≥0∞` value, which is finite there because all capacities are then finite), and is only ever asserted about on admissible rectangles. The book prints the third term of (13.12) as $\bar v_{ij}(\xi,\eta+h)$; the rectangle with corners $(\xi,\eta)$, $(\xi+h,\eta)$, $(\xi,\eta+k)$, $(\xi+h,\eta+k)$ that Theorem 13.1 names requires $\bar v_{ij}(\xi,\eta+k)$, which is what is used here. $p_{ij}$ is a four-way value (indeterminate, $+\infty$, $-\infty$, real) rather than an `EReal` expression, so $\infty-\infty$ is never silently given a value.
-- source:
--   Ford & Fulkerson, Flows in Networks, RAND Report R-375-PR (1962), Chapter I, §13, p. 53, p. 55 (13.11), p. 57 (13.12)

import Mathlib
import Definitions.Def_FlowsNetworks_TwoArcs_Network

namespace FlowsNetworks.TwoArcs

open scoped ENNReal NNReal

variable {N : Type} [Fintype N] [DecidableEq N]

/-- The capacities `c` (all finite) with the capacity of the arc `A_i` replaced by the variable
`ξ ∈ [0, ∞]` (Ch. I, §13, p. 53). -/
def capOne (c : N × N → ℝ≥0) (Ai : N × N) (ξ : ℝ≥0∞) : N × N → ℝ≥0∞ :=
  fun a => if a = Ai then ξ else (c a : ℝ≥0∞)

/-- `v̄_i(ξ)`: the maximal flow value when `c(A_i)` has been replaced by `ξ ∈ [0, ∞]`. -/
noncomputable def vbarOne (G : Network N) (c : N × N → ℝ≥0) (Ai : N × N) (ξ : ℝ≥0∞) : ℝ≥0∞ :=
  maxFlowValue G (capOne c Ai ξ)

/-- The capacities `c` (all finite) with `c(A_i)` replaced by `ξ` and `c(A_j)` by `η`,
`ξ, η ∈ [0, ∞]` (Ch. I, §13, p. 53). The two arcs are meant to be distinct. -/
def capTwo (c : N × N → ℝ≥0) (Ai Aj : N × N) (ξ η : ℝ≥0∞) : N × N → ℝ≥0∞ :=
  fun a => if a = Ai then ξ else if a = Aj then η else (c a : ℝ≥0∞)

/-- `v̄_ij(ξ, η)`: the maximal flow value when `c(A_i)` and `c(A_j)` have been replaced by
`ξ, η ∈ [0, ∞]`. -/
noncomputable def vbarTwo (G : Network N) (c : N × N → ℝ≥0) (Ai Aj : N × N) (ξ η : ℝ≥0∞) : ℝ≥0∞ :=
  maxFlowValue G (capTwo c Ai Aj ξ η)

/-- `v̄_ij(ξ, η)` at finite real arguments `ξ, η ≥ 0`, as a real number. With all capacities
finite the maximal flow value is finite, so `toReal` loses nothing there. It is only ever applied
to nonnegative arguments (see `IsAdmissible`). -/
noncomputable def vbarTwoReal (G : Network N) (c : N × N → ℝ≥0) (Ai Aj : N × N) (ξ η : ℝ) : ℝ :=
  (vbarTwo G c Ai Aj (ENNReal.ofReal ξ) (ENNReal.ofReal η)).toReal

/-- The difference quotient (13.12) (Ch. I, p. 57) of `v̄_ij` over the rectangle with corners
`(ξ, η)`, `(ξ + h, η)`, `(ξ, η + k)`, `(ξ + h, η + k)`:
`q_ij = [v̄_ij(ξ + h, η + k) − v̄_ij(ξ + h, η) − v̄_ij(ξ, η + k) + v̄_ij(ξ, η)] / hk`.
The book prints the third term as `v̄_ij(ξ, η + h)`; the rectangle the theorem names requires
`η + k`, which is used here. -/
noncomputable def diffQuotient (G : Network N) (c : N × N → ℝ≥0) (Ai Aj : N × N) (ξ η h k : ℝ) : ℝ :=
  (vbarTwoReal G c Ai Aj (ξ + h) (η + k) - vbarTwoReal G c Ai Aj (ξ + h) η
      - vbarTwoReal G c Ai Aj ξ (η + k) + vbarTwoReal G c Ai Aj ξ η) / (h * k)

/-- The rectangle `(ξ, η, h, k)` lies in the nonnegative quadrant and `q_ij` is well defined
there: `ξ ≥ 0`, `η ≥ 0`, `ξ + h ≥ 0`, `η + k ≥ 0` and `hk ≠ 0` (p. 57). -/
def IsAdmissible (ξ η h k : ℝ) : Prop :=
  0 ≤ ξ ∧ 0 ≤ η ∧ 0 ≤ ξ + h ∧ 0 ≤ η + k ∧ h * k ≠ 0

/-- A value of an expression in extended reals that may be indeterminate (`∞ − ∞`). -/
inductive ExtValue where
  | indeterminate : ExtValue
  | posInf : ExtValue
  | negInf : ExtValue
  | real : ℝ → ExtValue

/-- The constant (13.11) (Ch. I, p. 55):
`p_ij = v̄_ij(∞, ∞) − v̄_ij(0, ∞) − v̄_ij(∞, 0) + v̄_ij(0, 0)`, evaluated in extended
arithmetic. With `P = v̄_ij(∞, ∞) + v̄_ij(0, 0)` and `M = v̄_ij(0, ∞) + v̄_ij(∞, 0)` (both in
`[0, ∞]`), `p_ij = P − M` is indeterminate (`∞ − ∞`) if `P = M = ∞`, `+∞` if only `P = ∞`,
`−∞` if only `M = ∞`, and the real number `P − M` otherwise. -/
noncomputable def pValue (G : Network N) (c : N × N → ℝ≥0) (Ai Aj : N × N) : ExtValue :=
  let P := vbarTwo G c Ai Aj ⊤ ⊤ + vbarTwo G c Ai Aj 0 0
  let M := vbarTwo G c Ai Aj 0 ⊤ + vbarTwo G c Ai Aj ⊤ 0
  if P = ⊤ ∧ M = ⊤ then ExtValue.indeterminate
  else if P = ⊤ then ExtValue.posInf
  else if M = ⊤ then ExtValue.negInf
  else ExtValue.real (P.toReal - M.toReal)

end FlowsNetworks.TwoArcs


