-- Prove2me | Definitions.Def_Sennott1989_AvgCost_Assumptions
-- name    : Sennott1989_AvgCost_Assumptions
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:40:58.777108+00:00
-- url     : https://prove2.me/theorems/154d05cd-b3cf-4e54-988e-4eca82ca3b75
-- title:
--   Assumptions 1, 2, 3, 3* (pp. 627–628), h_α = V_α − V_α(0), average cost optimality with a constant g, (5), (6), the induced chain and the conditions of Proposition 4
-- statement:
--   This file collects the objects of Sennott (1989), §§1–2, on top of the Markov decision chain of Sennott's 1999 book (states $0,1,2,\dots$, finite nonempty action sets $A_i$, nonnegative costs $C(i,a)$, transition probabilities $P_{ij}(a)$). Write $V_\alpha(i)=\inf_\theta V_{\theta,\alpha}(i)\in[0,\infty]$ for the $\alpha$-discounted value ($0<\alpha<1$, infimum over all history-dependent randomized policies) and $g_\theta(i)=\limsup_N N^{-1}E_\theta[\sum_{t=0}^{N-1}C(X_t,a_t)\mid X_0=i]$ for the average cost (3).
--
--   1. **Assumption 1.** $V_\alpha(i)<\infty$ for every state $i$ and every $\alpha\in(0,1)$.
--   2. **Relative value.** $h_\alpha(i)=V_\alpha(i)-V_\alpha(0)$.
--   3. **Assumption 2** (with constant $N$). $N\ge 0$ and $-N\le h_\alpha(i)$ for all $i$ and all $\alpha\in(0,1)$.
--   4. **Assumption 3** (with bounds $M_i$). $M_i\ge 0$, $h_\alpha(i)\le M_i$ for all $i$ and $\alpha$, and for every $i$ there is an action $a(i)\in A_i$ with $\sum_j P_{ij}(a(i))M_j<\infty$.
--   5. **Assumption 3\***. Assumption 3 holds and, with the same $M_j$, $\sum_j P_{ij}(a)M_j<\infty$ for every $i$ and every $a\in A_i$.
--   6. **Average cost optimality.** A stationary policy $f$ is average cost optimal with average cost $g$ if $g$ is a finite constant with
--   $$g=g_f(i)\le g_\theta(i)\qquad\text{for every policy }\theta\text{ and every state }i.$$
--   7. **The optimality inequalities (5) and equation (6)** for a constant $g$, a function $h$ and a stationary policy $f$:
--   $$g+h(i)\ \ge\ C(i,f)+\sum_j P_{ij}(f)h(j)\ \ge\ \min_{a\in A_i}\Big\{C(i,a)+\sum_j P_{ij}(a)h(j)\Big\},\qquad g+h(i)=\min_{a\in A_i}\Big\{C(i,a)+\sum_j P_{ij}(a)h(j)\Big\},$$
--   and the statement that a stationary policy $e$ realizes the minimum, and that $g=\lim_{\alpha\uparrow1}(1-\alpha)V_\alpha(i)$ for every $i$.
--   8. **The induced chain** of a stationary policy $f$, with transition probabilities $P_{ij}(f(i))$; a chain is **irreducible ergodic** if it is irreducible and every state is positive recurrent; and the three conditions of Proposition 4 for a cost $c(i)\ge0$: (i) $\sum_i\pi_i c(i)<\infty$; (ii) $c_{i0}<\infty$ for every $i$; (iii) there are an integer $N\ge0$ and a function $r\ge0$ with $\sum_jP_{ij}r(j)<\infty$ for $i\le N$ and $\sum_jP_{ij}r(j)-r(i)\le-c(i)$ for $i>N$. A stationary policy satisfies the hypotheses of Proposition 5 (i) if its induced chain is irreducible ergodic and satisfies one of these conditions with $c(i)=C(i,f(i))$.
--
--   These are the shared vocabulary of every statement of the mission.
--
--   **Formalization Note** $h_\alpha$ is a real number computed with `ENNReal.toReal`, which is meaningful only under Assumption 1; every statement that uses it assumes or concludes Assumption 1. The constants $N$ and $M_i$ are explicit arguments, chosen before $i$ and $\alpha$. Average costs are in $[0,\infty]$ and compared with $g$ through `ENNReal.ofReal`, with $g\ge0$ required. The sums $\sum_jP_{ij}(a)h(j)$ against a real function are extended reals (positive part minus negative part, `SennottDP.SEN.wsum`), finite from below whenever $h$ is bounded below; the minimum in (5)–(6) is taken in the extended reals. "Ergodic" requires no aperiodicity. $c_{00}$ is the cost of a return to $0$.
-- source:
--   Sennott, Average Cost Optimal Stationary Policies in Infinite State Markov Decision Processes with Unbounded Costs, Oper. Res. 37(4):626–633 (1989), DOI 10.1287/opre.37.4.626, p. 627, Assumption 1; p. 628, (3), h_α, Assumptions 2, 3, 3*, average cost optimality, (5), (6); p. 629, Proposition 4 (i)–(iii), Proposition 5

import Mathlib
import Definitions.Def_SennottDP_SEN_Criteria
import Definitions.Def_SennottDP_Discounted_Optimality
import Definitions.Def_SennottDP_MarkovCost_Costs

open scoped ENNReal NNReal
open Filter Topology

namespace Sennott1989.AvgCost

open SennottDP.Discounted

variable {Act : Type}

/-- Sennott (1989), §1, p. 627, Assumption 1: for every state `i` and every discount factor
`α ∈ (0, 1)`, the discounted value `V_α(i) = inf_θ V_{θ,α}(i)` is finite. -/
def Assumption1 (M : MDC ℕ Act) : Prop :=
  ∀ α : ℝ≥0, 0 < α → α < 1 → ∀ i : ℕ, valueFn M α i < ⊤

/-- Sennott (1989), §2, p. 628: the relative value `h_α(i) = V_α(i) − V_α(0)`, a real number.

**Formalization Note** `h_α` is a real number only when `V_α(i)` and `V_α(0)` are finite, i.e.
under Assumption 1; it is computed with `ENNReal.toReal`, which sends `∞` to `0`. Every statement
of this development that uses `relValue` assumes `Assumption1` (or concludes it together with the
property of `relValue`), so this junk value never enters. -/
noncomputable def relValue (M : MDC ℕ Act) (α : ℝ≥0) (i : ℕ) : ℝ :=
  (valueFn M α i).toReal - (valueFn M α 0).toReal

/-- Sennott (1989), §2, p. 628, Assumption 2, with its constant `N` made explicit: `N` is a
nonnegative real and `−N ≤ h_α(i)` for every state `i` and every discount factor `α ∈ (0, 1)`.
"Assumption 2 holds" is `∃ N, Assumption2 M N`; the constant does not depend on `i` or `α`.
Meaningful together with `Assumption1` (see `relValue`). -/
def Assumption2 (M : MDC ℕ Act) (N : ℝ) : Prop :=
  0 ≤ N ∧ ∀ α : ℝ≥0, 0 < α → α < 1 → ∀ i : ℕ, -N ≤ relValue M α i

/-- Sennott (1989), §2, p. 628, Assumption 3, with its bounds `M_i` made explicit: the `M_i` are
nonnegative reals with `h_α(i) ≤ M_i` for every state `i` and every `α ∈ (0, 1)`, and for every
state `i` there is an action `a(i) ∈ A_i` with `∑_j P_{ij}(a(i)) M_j < ∞`.
"Assumption 3 holds" is `∃ Mb, Assumption3 M Mb`. Meaningful together with `Assumption1`. -/
def Assumption3 (M : MDC ℕ Act) (Mb : ℕ → ℝ) : Prop :=
  (∀ i, 0 ≤ Mb i) ∧
    (∀ α : ℝ≥0, 0 < α → α < 1 → ∀ i : ℕ, relValue M α i ≤ Mb i) ∧
    ∀ i : ℕ, ∃ a ∈ M.A i, ∑' j, M.P i a j * ENNReal.ofReal (Mb j) < ⊤

/-- Sennott (1989), §2, p. 628, Assumption 3*: Assumption 3 holds and, with the **same** bounds
`M_j`, `∑_j P_{ij}(a) M_j < ∞` for every state `i` and every action `a ∈ A_i`. -/
def Assumption3Star (M : MDC ℕ Act) (Mb : ℕ → ℝ) : Prop :=
  Assumption3 M Mb ∧ ∀ i : ℕ, ∀ a ∈ M.A i, ∑' j, M.P i a j * ENNReal.ofReal (Mb j) < ⊤

/-- Sennott (1989), §2, p. 628: the stationary policy `f` is **average cost optimal with average
cost `g`**: `g` is a finite constant with `g = g_f(i) ≤ g_θ(i)` for every (history-dependent,
randomized) policy `θ` and every state `i`, where `g_θ(i)` is the lim sup average cost (3).

**Formalization Note** `g_θ(i)` is `SennottDP.SEN.avgCost`, a value in `[0, ∞]`; the finite
constant `g` is a real number, required to be `≥ 0` (it equals an average of nonnegative costs),
and compared through `ENNReal.ofReal`. -/
def IsACOptimal (M : MDC ℕ Act) (f : StationaryPolicy M) (g : ℝ) : Prop :=
  0 ≤ g ∧ ∀ i : ℕ, SennottDP.SEN.avgCost M f.toPolicy i = ENNReal.ofReal g ∧
    ∀ θ : Policy M, SennottDP.SEN.avgCost M f.toPolicy i ≤ SennottDP.SEN.avgCost M θ i

/-- The one-step quantity `C(i, a) + ∑_j P_{ij}(a) h(j)` of the average cost optimality
inequality (5) and equation (6), p. 628, for a real function `h`, as an extended real.

**Formalization Note** The sum `∑_j P_{ij}(a) h(j)` is `SennottDP.SEN.wsum`: the sum of the
positive parts minus the sum of the negative parts, each in `[0, ∞]`. A lower bound on `h`
makes the negative part finite; an upper bound makes the positive part finite. -/
noncomputable def acoiTerm (M : MDC ℕ Act) (h : ℕ → ℝ) (i : ℕ) (a : Act) : EReal :=
  ((M.C i a : ℝ) : EReal) + SennottDP.SEN.wsum (M.P i a) h

/-- The right side of (5) and (6), p. 628: `min_{a ∈ A_i} { C(i, a) + ∑_j P_{ij}(a) h(j) }`, a
minimum over the finite nonempty action set `A_i`, in the extended reals. -/
noncomputable def acoiMin (M : MDC ℕ Act) (h : ℕ → ℝ) (i : ℕ) : EReal :=
  (M.A i).inf' (M.A_nonempty i) (acoiTerm M h i)

/-- Sennott (1989), (5), p. 628: the average cost optimality inequalities for a constant `g`, a
function `h` and a stationary policy `f`:
`g + h(i) ≥ C(i, f) + ∑_j P_{ij}(f) h(j) ≥ min_a { C(i, a) + ∑_j P_{ij}(a) h(j) }`, `i ≥ 0`. -/
def ACOI (M : MDC ℕ Act) (g : ℝ) (h : ℕ → ℝ) (f : StationaryPolicy M) : Prop :=
  ∀ i : ℕ, acoiTerm M h i (f.1 i) ≤ ((g + h i : ℝ) : EReal) ∧ acoiMin M h i ≤ acoiTerm M h i (f.1 i)

/-- Sennott (1989), (6), p. 628: the average cost optimality equation
`g + h(i) = min_a { C(i, a) + ∑_j P_{ij}(a) h(j) }`, `i ≥ 0`. -/
def ACOE (M : MDC ℕ Act) (g : ℝ) (h : ℕ → ℝ) : Prop :=
  ∀ i : ℕ, ((g + h i : ℝ) : EReal) = acoiMin M h i

/-- A stationary policy `e` realizes the minimum in (5) (equivalently (6)), p. 628, for the
function `h`: `C(i, e) + ∑_j P_{ij}(e) h(j) = min_a { C(i, a) + ∑_j P_{ij}(a) h(j) }` for every
`i`. -/
def RealizesACOI (M : MDC ℕ Act) (h : ℕ → ℝ) (e : StationaryPolicy M) : Prop :=
  ∀ i : ℕ, acoiTerm M h i (e.1 i) = acoiMin M h i

/-- Sennott (1989), Theorem (i), p. 628: `g = lim_{α↑1} (1 − α) V_α(i)` for every state `i`, the
limit taken as `α → 1` with `α < 1`, in `[0, ∞]`. -/
def IsAbelLimit (M : MDC ℕ Act) (g : ℝ) : Prop :=
  ∀ i : ℕ, Tendsto (fun α : ℝ≥0 => ((1 - α : ℝ≥0) : ℝ≥0∞) * valueFn M α i) (𝓝[<] 1)
    (𝓝 (ENNReal.ofReal g))

/-- Sennott (1989), Proposition 5, p. 629: the Markov chain on `0, 1, 2, …` induced by the
stationary policy `f`, with transition probabilities `P_{ij}(f) = P_{ij}(f(i))`. -/
noncomputable def inducedChain (M : MDC ℕ Act) (f : StationaryPolicy M) :
    SennottDP.MarkovCost.MC ℕ where
  P i j := M.P i (f.1 i) j
  P_sum i := M.P_sum i (f.1 i) (f.2 i)

/-- Sennott (1989), Proposition 4, p. 629: an **irreducible ergodic** Markov chain on
`0, 1, 2, …`: irreducible, and every state positive recurrent.

**Formalization Note** The paper's "ergodic" requires no aperiodicity: it is used only through the
steady state distribution `π_i = 1/m_ii` and finite mean passage times, so it is read as positive
recurrence of every state. -/
def IrredErgodic (Γ : SennottDP.MarkovCost.MC ℕ) : Prop :=
  SennottDP.MarkovCost.Irreducible Γ ∧ ∀ i, SennottDP.MarkovCost.PositiveRecurrent Γ i

/-- Sennott (1989), Proposition 4 (i), p. 629: `∑_i π_i c(i) < ∞`, with `π_i` the steady state
distribution of the chain and `c(i) ≥ 0` the cost incurred in state `i`. -/
def CostCondI (Γ : SennottDP.MarkovCost.MC ℕ) (c : ℕ → ℝ≥0) : Prop :=
  ∑' i, SennottDP.MarkovCost.steadyState Γ i * (c i : ℝ≥0∞) < ⊤

/-- Sennott (1989), Proposition 4 (ii), p. 629: for every state `i`, `c_{i0} < ∞`, where `c_{i0}`
is the expected cost of a first passage from `i` to `0` (for `i = 0`, of a return to `0`). -/
def CostCondII (Γ : SennottDP.MarkovCost.MC ℕ) (c : ℕ → ℝ≥0) : Prop :=
  ∀ i, SennottDP.MarkovCost.passageCost Γ c {0} i < ⊤

/-- Sennott (1989), Proposition 4 (iii), p. 629: there exist a nonnegative integer `N` and a
nonnegative (finite) function `r` with `∑_j P_{ij} r(j) < ∞` for `0 ≤ i ≤ N` and
`∑_j P_{ij} r(j) − r(i) ≤ −c(i)` for `i > N`.

**Formalization Note** Since `r(i)` is finite, the drift inequality is written
`∑_j P_{ij} r(j) + c(i) ≤ r(i)` in `[0, ∞]`; it forces `∑_j P_{ij} r(j)` to be finite, as the
paper's subtraction presupposes. -/
def CostCondIII (Γ : SennottDP.MarkovCost.MC ℕ) (c : ℕ → ℝ≥0) : Prop :=
  ∃ (N : ℕ) (r : ℕ → ℝ≥0), (∀ i, i ≤ N → ∑' j, Γ.P i j * (r j : ℝ≥0∞) < ⊤) ∧
    ∀ i, N < i → ∑' j, Γ.P i j * (r j : ℝ≥0∞) + (c i : ℝ≥0∞) ≤ (r i : ℝ≥0∞)

/-- The hypothesis of Sennott (1989), Proposition 5 (i), p. 629, on a stationary policy `f`: it
induces an irreducible, ergodic Markov chain satisfying any of the three conditions of
Proposition 4, with the cost `c(i) = C(i, f(i))`. -/
def GoodPolicy (M : MDC ℕ Act) (f : StationaryPolicy M) : Prop :=
  IrredErgodic (inducedChain M f) ∧
    (CostCondI (inducedChain M f) (fun i => M.C i (f.1 i)) ∨
      CostCondII (inducedChain M f) (fun i => M.C i (f.1 i)) ∨
      CostCondIII (inducedChain M f) (fun i => M.C i (f.1 i)))

end Sennott1989.AvgCost


