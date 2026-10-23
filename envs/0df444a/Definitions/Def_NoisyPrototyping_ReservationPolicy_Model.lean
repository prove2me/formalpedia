-- Prove2me | Definitions.Def_NoisyPrototyping_ReservationPolicy_Model
-- name    : NoisyPrototyping_ReservationPolicy_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T23:03:15.936973+00:00
-- url     : https://prove2.me/theorems/4825efd7-7c5b-414d-ae91-6e444f7418b7
-- title:
--   §3, (1)–(2), pp. 9–11 — noisy sequential search: laws of (true value, measurement), adaptive policies, net payoff, value; Q_i, g_i, V_n, B_n, the fidelity-adjusted reservation price policy, P₂ and P̂
-- statement:
--   The noisy sequential search model of §3 and the objects used in Theorem 1 and its proof.
--
--   1. **Search problem and model.** There are $N$ prototypes. Prototype $i$ has a true value $P_i$ and a measurement $m_i$; the pair $(P_i, m_i)$ has a joint law $\mu_i$ on $\mathbb R^2$ (first coordinate the value, second the measurement), and evaluating $i$ costs $w_i$. A *model* is such a problem in which every $\mu_i$ is a probability measure, $E|P_i| < \infty$, and $w_i > 0$. The outcome $\omega = ((P_1,m_1),\dots,(P_N,m_N))$ has law $\mu_1 \otimes \cdots \otimes \mu_N$: prototypes are independent.
--
--   2. **Histories, decisions, policies.** A history is the list of evaluated prototypes, in evaluation order, each with its measurement $m_i$; true values are never recorded. A decision is *evaluate $j$*, *launch $j$*, or *stop and launch nothing* (outside option $0$). A policy maps every history to a decision; it may stop at the empty history.
--
--   3. **Run and payoff.** Starting from the empty history, the policy's decisions are executed: evaluating $j$ appends $(j, m_j)$. Evaluating a prototype twice, or launching one that was not evaluated, is treated as stopping with nothing. At most $N$ evaluations take place. The net payoff is
--   $$\text{(value of the launched prototype, or } 0) - \sum_{j \text{ evaluated}} w_j .$$
--   A policy is *admissible* if the events "the evaluation order was $l$ and the final decision was $d$" are measurable and the net payoff is integrable; its *value* is the expected net payoff.
--
--   4. **Fidelity-adjusted expected value**, formula (1):
--   $$Q_i(m) = \frac{\int_{-\infty}^{\infty} P\, f_i(P,m)\, dP}{\int_{-\infty}^{\infty} f_i(P,m)\, dP},$$
--   for a joint density $f_i$; and $g_i$, the law of $X_i = Q_i(m_i)$, the post-measurement (expected) value.
--
--   5. **$V$ and $B$.** Along a history, $V_0 = 0$, $B_0 = 0$ (nothing), and after the next evaluated prototype $i$, $V_i = \max\{V_{i-1}, Q_i(m_i)\}$, with $B_i = B_{i-1}$ if $V_{i-1} > Q_i(m_i)$ and $B_i = i$ otherwise.
--
--   6. **The fidelity-adjusted reservation price policy** $\pi^*$, for prices $R_i$ and an order $\sigma$ of the prototypes: after $n$ evaluations, if $n < N$ and $V_n < R_{\sigma(n+1)}$, evaluate prototype $\sigma(n+1)$; otherwise stop and accept $B_n$ (nothing if $B_n = 0$).
--
--   7. **Auxiliary problems.** $\mathcal P_2$: launching $i$ pays $Q_i(m_i)$ instead of $P_i$, the observation is still $m_i$. $\hat{\mathcal P}$: Pandora's box problem in which prototype $i$ has value distribution $G_i$, observed exactly when evaluated, and cost $w_i$.
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** Prototypes are indexed by `Fin N` from $0$; the paper's prototype $n+1$ in the reordered list is `σ n`. The paper prints $dm$ in the denominator of (1); it is read as $dP$, which is what makes $Q_i(m)$ the conditional expectation of $P_i$ given $m_i = m$ (the paper's own description, proof of Claim 1). Lean's `Q f m` returns $0$ where the denominator vanishes; under a density this happens only on a null set of $m$. $g_i$ is defined as the push-forward law of $Q_i(m_i)$, not by formula (2), which lacks the Jacobian factor. `V`, `B` are computed from any history; on the histories the policy actually reaches (the order $\sigma$) they are the paper's $V_n$, $B_n$, and off that path the policy's decision is never used. Independence across prototypes, $E|P_i| < \infty$, $w_i > 0$, at most one evaluation per prototype, and the integrability/measurability requirement on policies are not written on the page and are the standard readings of Weitzman's model that the paper generalizes.
-- source:
--   Bhaskaran and Erat, Optimal Prototyping with Noisy Measurements, author manuscript of 6 Nov 2024 (MSOM 2025, doi:10.1287/msom.2024.1133), §3, pp. 9–11, (1)–(2), definitions of R_i, V_i, B_i; Technical Appendix, proof of Theorem 1, pp. A1–A2 (PDF 32–33), problems P₂ and P̂

import Mathlib

namespace NoisyPrototyping.ReservationPolicy

open MeasureTheory

/-- The data of a sequential search problem with `N` prototypes: for each prototype `i` the joint
law `law i` of the pair (true value `P_i`, measurement `m_i`) on `ℝ × ℝ` (first coordinate the
value, second the measurement), and the evaluation cost `cost i`. -/
structure SearchProblem (N : ℕ) where
  law : Fin N → Measure (ℝ × ℝ)
  cost : Fin N → ℝ

/-- The noisy search model of §3: a search problem whose laws are probability measures, whose true
values have finite mean, and whose evaluation costs are positive. -/
structure Model (N : ℕ) extends SearchProblem N where
  law_prob : ∀ i, IsProbabilityMeasure (law i)
  value_integrable : ∀ i, Integrable (fun z : ℝ × ℝ => z.1) (law i)
  cost_pos : ∀ i, 0 < cost i

/-- The joint law of all outcomes `ω : Fin N → ℝ × ℝ`; prototypes are independent. -/
noncomputable def SearchProblem.outcomeLaw {N : ℕ} (S : SearchProblem N) :
    Measure (Fin N → ℝ × ℝ) :=
  Measure.pi S.law

/-- What the firm has seen: the evaluated prototypes, in evaluation order, each with its
measurement. True values are never recorded. -/
abbrev History (N : ℕ) := List (Fin N × ℝ)

/-- A decision: evaluate prototype `j`, launch prototype `j`, or stop and launch nothing
(outside option `0`). -/
inductive Decision (N : ℕ)
  | evaluate (j : Fin N)
  | launch (j : Fin N)
  | stopNone

/-- An adaptive policy maps each history of measurements to a decision. -/
structure Policy (N : ℕ) where
  next : History N → Decision N

/-- The run with `fuel` steps left from history `h`. Evaluating an already evaluated prototype, or
launching a prototype not yet evaluated, is illegal and is treated as `stopNone`. -/
def runAux {N : ℕ} (ρ : Policy N) (ω : Fin N → ℝ × ℝ) :
    ℕ → History N → History N × Decision N
  | 0, h => (h, Decision.stopNone)
  | k + 1, h =>
    match ρ.next h with
    | Decision.evaluate j =>
        if j ∈ h.map Prod.fst then (h, Decision.stopNone)
        else runAux ρ ω k (h ++ [(j, (ω j).2)])
    | Decision.launch j =>
        if j ∈ h.map Prod.fst then (h, Decision.launch j) else (h, Decision.stopNone)
    | Decision.stopNone => (h, Decision.stopNone)

/-- The run of `ρ` on outcome `ω`, from the empty history with fuel `N + 1`: the terminal history
and the terminal decision (`launch j` or `stopNone`). Evaluating prototype `j` appends its
measurement `(ω j).2` only. -/
def run {N : ℕ} (ρ : Policy N) (ω : Fin N → ℝ × ℝ) : History N × Decision N :=
  runAux ρ ω (N + 1) []

/-- The true value of the launched prototype, `0` if nothing is launched. -/
def launchedValue {N : ℕ} (ω : Fin N → ℝ × ℝ) : Decision N → ℝ
  | Decision.launch j => (ω j).1
  | _ => 0

/-- Undiscounted net payoff: value of the launched prototype minus the evaluation costs paid. -/
def netPayoff {N : ℕ} (S : SearchProblem N) (ρ : Policy N) (ω : Fin N → ℝ × ℝ) : ℝ :=
  launchedValue ω (run ρ ω).2 - ((run ρ ω).1.map (fun e => S.cost e.1)).sum

/-- Admissible policy: every event "the prototypes were evaluated in the order `l` and the final
decision was `d`" is measurable, and the net payoff is integrable. -/
def Admissible {N : ℕ} (S : SearchProblem N) (ρ : Policy N) : Prop :=
  (∀ (l : List (Fin N)) (d : Decision N),
    MeasurableSet {ω : Fin N → ℝ × ℝ | ((run ρ ω).1.map Prod.fst, (run ρ ω).2) = (l, d)}) ∧
  Integrable (netPayoff S ρ) S.outcomeLaw

/-- Expected net payoff of a policy. -/
noncomputable def value {N : ℕ} (S : SearchProblem N) (ρ : Policy N) : ℝ :=
  ∫ ω, netPayoff S ρ ω ∂S.outcomeLaw

/-- Formula (1), with the denominator integrated in `P`:
`Q f m = (∫ P · f(P, m) dP) / (∫ f(P, m) dP)`. -/
noncomputable def Q (f : ℝ × ℝ → ℝ) (m : ℝ) : ℝ :=
  (∫ P : ℝ, P * f (P, m)) / ∫ P : ℝ, f (P, m)

/-- The law `g_i` of the post-measurement value `X_i = q_i(m_i)`. -/
noncomputable def g {N : ℕ} (S : SearchProblem N) (q : Fin N → ℝ → ℝ) (i : Fin N) : Measure ℝ :=
  (S.law i).map (fun z => q i z.2)

/-- The pair `(V, B)` after a history: `V = 0`, `B = none` initially; after evaluating `j` with
measurement `m`, keep `(V, B)` if `V > q j m`, otherwise set `(V, B) := (q j m, some j)`. -/
noncomputable def VB {N : ℕ} (q : Fin N → ℝ → ℝ) (h : History N) : ℝ × Option (Fin N) :=
  h.foldl (fun vb e => if vb.1 > q e.1 e.2 then vb else (q e.1 e.2, some e.1)) (0, none)

/-- `V`: the best fidelity-adjusted expected value seen so far (`0` = outside option). -/
noncomputable def V {N : ℕ} (q : Fin N → ℝ → ℝ) (h : History N) : ℝ := (VB q h).1

/-- `B`: the corresponding alternative (`none` = prototype 0, launch nothing). -/
noncomputable def B {N : ℕ} (q : Fin N → ℝ → ℝ) (h : History N) : Option (Fin N) := (VB q h).2

/-- Stop and accept `B`: launch it, or launch nothing when `B = none`. -/
def stopDecision {N : ℕ} : Option (Fin N) → Decision N
  | some b => Decision.launch b
  | none => Decision.stopNone

/-- The fidelity-adjusted reservation price policy π*: after `n` evaluations, if `n < N` and
`V < R (σ n)` evaluate `σ n`; otherwise stop and accept `B`. -/
noncomputable def fidelityPolicy {N : ℕ} (q : Fin N → ℝ → ℝ) (σ : Fin N ≃ Fin N)
    (R : Fin N → ℝ) : Policy N where
  next h :=
    if hn : h.length < N then
      if V q h < R (σ ⟨h.length, hn⟩) then Decision.evaluate (σ ⟨h.length, hn⟩)
      else stopDecision (B q h)
    else stopDecision (B q h)

/-- The problem P₂ of Claim 1: launching `i` pays `q_i(m_i)`; the observation is still `m_i`. -/
noncomputable def SearchProblem.posteriorProblem {N : ℕ} (S : SearchProblem N)
    (q : Fin N → ℝ → ℝ) : SearchProblem N where
  law i := (S.law i).map (fun z => (q i z.2, z.2))
  cost := S.cost

/-- The Pandora's box problem P̂ of Claim 2: prototype `i` has value distribution `G i`, observed
exactly on evaluation, and cost `w i`. -/
noncomputable def pandoraProblem {N : ℕ} (G : Fin N → Measure ℝ) (w : Fin N → ℝ) :
    SearchProblem N where
  law i := (G i).map (fun x => (x, x))
  cost := w

end NoisyPrototyping.ReservationPolicy


