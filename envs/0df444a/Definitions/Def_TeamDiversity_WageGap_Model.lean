-- Prove2me | Definitions.Def_TeamDiversity_WageGap_Model
-- name    : TeamDiversity_WageGap_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T01:19:31.292997+00:00
-- url     : https://prove2.me/theorems/017c13dd-7ccd-46d3-b6d4-9533974816a9
-- title:
--   §2–§3 and Appendix A, pp. 7–19, 31 — specialized vs diverse team technologies, Assumptions A.1–A.3, the (IR)/(M-IC)/(No-cycling) programs, V_s, V_d, Δ, S*(δ)
-- statement:
--   This file sets up the repeated team-production model of Glover and Kim.
--
--   A principal hires four agents for two tasks each period. Each task is done by a two-agent team; each agent chooses effort $e \in \{0,1\}$ (shirk or work) at cost $ce$, and the agents discount the future at a common factor $\delta \in [0,1]$. A team of kind $k \in \{s,d\}$ (specialized or diverse) succeeds, producing $S>0$, with probability $f_k(n)$ when $n \in \{0,1,2\}$ of its members work, and otherwise produces $0$. A **technology** is the triple $(f_k(0), f_k(1), f_k(2))$. The agent is paid a wage $w_k \ge 0$ on success and nothing on failure.
--
--   **Standing assumptions.** The effort cost satisfies $c > 0$; each technology satisfies $0 < f_k(0) < f_k(1) < f_k(2) < 1$; specialization is more productive, $f_s(2) > f_d(2)$; and
--
--   1. (A.1) $\dfrac{f_s(2)-f_s(0)}{f_s(2)-f_s(1)} > 2 > \dfrac{f_d(2)-f_d(0)}{f_d(2)-f_d(1)}$ (substitutes under specialized, complements under diverse assignment);
--   2. (A.2) $\dfrac{f_s(1)-f_s(0)}{f_s(2)-f_s(1)} < 2$ (weak substitutability);
--   3. (A.3) $\dfrac{f_s(1)}{f_s(2)} > \dfrac{f_d(1)}{f_d(2)}$.
--
--   **Thresholds.** The normalized punishment is $x_k = \frac{f_k(2)-f_k(0)}{f_k(2)-f_k(1)}$, and
--   $$\delta^m = \frac{2f_s(1)-f_s(2)-f_s(0)}{f_s(1)-f_s(0)}, \qquad \delta^C = \sqrt{\frac{f_s(2)-f_s(1)}{f_s(1)-f_s(0)}}.$$
--
--   **Programs.** The expected wage of a success wage $w$ is $E[w_k] = f_k(2)\,w$. A diverse wage $w_d \ge 0$ is feasible if
--   $$f_d(2)w_d - c \ge 0 \ \text{(IR)}, \qquad f_d(2)w_d - c \ge (1-\delta)f_d(1)w_d + \delta f_d(0)w_d \ \text{(M-IC)}.$$
--   A specialized wage $w_s \ge 0$ satisfies the mutual-monitoring program if $f_s(2)w_s - c \ge 0$ (IR) and the (M-IC) constraint holds, which is
--   $$f_s(2)w_s - c \ge (1-\delta)f_s(1)w_s + \delta f_s(0)w_s \quad (\delta \ge \delta^m), \qquad f_s(2)w_s - c \ge (1-\delta)f_s(1)w_s + \delta(f_s(1)w_s - c) \quad (\delta < \delta^m).$$
--   It is feasible for the full specialized program if in addition the (No-cycling) constraint holds:
--   $$f_s(2)w_s - c \ge \frac{f_s(1)w_s - c}{1+\delta} + \delta\,\frac{f_s(1)w_s}{1+\delta}.$$
--   The optimal wages $w_d^*$, $w_s^*$ (mutual monitoring) and $w_s^{**}$ (collusion-proof) are the least elements of these feasible sets, since the principal's objective $2f_k(2)(S - 2w_k)$ is decreasing in $w_k$.
--
--   **Payoffs and the threshold.** The principal's per-period payoffs are $V_s = 2f_s(2)S - 4E[w_s]$ and $V_d = 2f_d(2)S - 4E[w_d]$; with $\Delta = f_s(2) - f_d(2)$, the threshold is $S^*(\delta) = \frac{2}{\Delta}\left(E[w_s^{**}] - E[w_d^*]\right)$.
--
--   **Stage game.** In the one-shot team game, an agent exerting $e$ while the teammate exerts $e'$ earns $f_k(e+e')\,w - ce$; a profile $(e_1,e_2) \in \{0,1\}^2$ is a stage-game equilibrium if neither agent gains by switching effort.
--
--   These objects are the vocabulary of every statement in the mission.
--
--   **Formalization Note** A technology is a structure with three real fields $f_0,f_1,f_2$. The failure payment $v_k$ of the paper is fixed at $0$, as in every program of Appendix A, and is not modelled. "Increasing in effort" is read strictly. The specialized (M-IC) constraint is kept piecewise at $\delta^m$, exactly as printed, and is not merged into a maximum. The threshold $S^*$ is a function of the wage gap, so that it can be applied to any candidate optimal wages. The constraints are stated after the paper's normalization by $(1-\delta)$.
-- source:
--   Glover & Kim, Optimal Team Composition: Diversity to Foster Implicit Team Incentives, SSRN working paper 3344922 (June 2020 version), pp. 7–19, 31 (PDF 8–20, 32), §2, §3, Assumptions A.1–A.3, eq. (1), (2), Appendix A (The Programs for Optimal Incentives)

import Mathlib

namespace TeamDiversity.WageGap

/-- A team production technology `f_k`: the success probabilities `f_k(0), f_k(1), f_k(2)` when
zero, one or two of the two teammates work (Glover–Kim, §2, p. 7: `f_k(∑_i e_i)`). -/
structure Tech where
  f0 : ℝ
  f1 : ℝ
  f2 : ℝ

/-- The success probability `f_k(n)` as a function of the number `n` of working teammates
(`n ≥ 2` is read as `2`; only `n ∈ {0, 1, 2}` ever occurs). -/
def Tech.f (T : Tech) : ℕ → ℝ
  | 0 => T.f0
  | 1 => T.f1
  | _ => T.f2

/-- §2, p. 7: `f_k(e_i, e_j) ∈ (0,1)` and `f_k` is (strictly) increasing in the agents' efforts. -/
def TechOrder (T : Tech) : Prop :=
  0 < T.f0 ∧ T.f0 < T.f1 ∧ T.f1 < T.f2 ∧ T.f2 < 1

/-- Assumption A.1, p. 12: substitutes under specialized and complements under diverse assignment. -/
def AssumptionA1 (fs fd : Tech) : Prop :=
  (fs.f2 - fs.f0) / (fs.f2 - fs.f1) > 2 ∧ 2 > (fd.f2 - fd.f0) / (fd.f2 - fd.f1)

/-- Assumption A.2, p. 12: weak productive substitutability under specialized assignment. -/
def AssumptionA2 (fs : Tech) : Prop :=
  (fs.f1 - fs.f0) / (fs.f2 - fs.f1) < 2

/-- Assumption A.3, p. 12: in the one-shot game diverse teams are less costly to incentivize. -/
def AssumptionA3 (fs fd : Tech) : Prop :=
  fs.f1 / fs.f2 > fd.f1 / fd.f2

/-- The standing assumptions of §2–§3: effort cost `c > 0`, both technologies with
`0 < f(0) < f(1) < f(2) < 1`, Assumptions A.1–A.3, and the benefit of specialization
`f_s(2) > f_d(2)` (p. 7). -/
def Standing (c : ℝ) (fs fd : Tech) : Prop :=
  0 < c ∧ TechOrder fs ∧ TechOrder fd ∧ AssumptionA1 fs fd ∧ AssumptionA2 fs ∧
    AssumptionA3 fs fd ∧ fs.f2 > fd.f2

/-- The normalized punishment `x_k = (f_k(2) − f_k(0)) / (f_k(2) − f_k(1))` (p. 13). -/
noncomputable def xk (T : Tech) : ℝ := (T.f2 - T.f0) / (T.f2 - T.f1)

/-- `δ^m = (2 f_s(1) − f_s(2) − f_s(0)) / (f_s(1) − f_s(0))` (Lemma 1, p. 12). -/
noncomputable def deltaM (fs : Tech) : ℝ := (2 * fs.f1 - fs.f2 - fs.f0) / (fs.f1 - fs.f0)

/-- `δ^C = √((f_s(2) − f_s(1)) / (f_s(1) − f_s(0)))` (p. 16). -/
noncomputable def deltaC (fs : Tech) : ℝ := Real.sqrt ((fs.f2 - fs.f1) / (fs.f1 - fs.f0))

/-- The expected per-agent wage `E[w_k] = f_k(2) w_k` of a success wage `w_k` (eq. (1), p. 13;
the failure payment is `0`). -/
def expWage (T : Tech) (w : ℝ) : ℝ := T.f2 * w

/-- Feasible wages of the diverse program (Appendix A, p. 31): `w ≥ 0`, (IR) and (M-IC). -/
def FeasD (c : ℝ) (fd : Tech) (δ : ℝ) : Set ℝ :=
  {w | 0 ≤ w ∧ fd.f2 * w - c ≥ 0 ∧
    fd.f2 * w - c ≥ (1 - δ) * fd.f1 * w + δ * fd.f0 * w}

/-- The specialized (M-IC) constraint of Appendix A, p. 31, piecewise in `δ` exactly as printed:
the (shirk, shirk) punishment for `δ ≥ δ^m` and the (work, shirk) punishment for `δ < δ^m`. -/
noncomputable def MICs (c : ℝ) (fs : Tech) (δ w : ℝ) : Prop :=
  if deltaM fs ≤ δ then fs.f2 * w - c ≥ (1 - δ) * fs.f1 * w + δ * fs.f0 * w
  else fs.f2 * w - c ≥ (1 - δ) * fs.f1 * w + δ * (fs.f1 * w - c)

/-- The (No-cycling) constraint (p. 15 and Appendix A, p. 31). -/
noncomputable def NoCycling (c : ℝ) (fs : Tech) (δ w : ℝ) : Prop :=
  fs.f2 * w - c ≥ (fs.f1 * w - c) / (1 + δ) + δ * (fs.f1 * w) / (1 + δ)

/-- Feasible wages of the specialized mutual-monitoring program without the collusion constraint:
`w ≥ 0`, (IR) and (M-IC) (the program behind Lemma 1 and Proposition 1). -/
noncomputable def FeasSMM (c : ℝ) (fs : Tech) (δ : ℝ) : Set ℝ :=
  {w | 0 ≤ w ∧ fs.f2 * w - c ≥ 0 ∧ MICs c fs δ w}

/-- Feasible wages of the specialized program of Appendix A, p. 31: (IR), (M-IC), (No-cycling). -/
noncomputable def FeasS (c : ℝ) (fs : Tech) (δ : ℝ) : Set ℝ :=
  {w | w ∈ FeasSMM c fs δ ∧ NoCycling c fs δ w}

/-- The principal's per-period payoff `V_s = 2 f_s(2) S − 4 E[w_s]` under specialized teams (p. 18). -/
def Vs (fs : Tech) (S w : ℝ) : ℝ := 2 * fs.f2 * S - 4 * expWage fs w

/-- The principal's per-period payoff `V_d = 2 f_d(2) S − 4 E[w_d]` under diverse teams (p. 18). -/
def Vd (fd : Tech) (S w : ℝ) : ℝ := 2 * fd.f2 * S - 4 * expWage fd w

/-- The benefit of specialization `Δ = f_s(2) − f_d(2)` (p. 18). -/
def Delta (fs fd : Tech) : ℝ := fs.f2 - fd.f2

/-- The threshold `S*(δ) = (2/Δ)(E[w_s**] − E[w_d*])` (p. 19), as a function of the gap. -/
noncomputable def Sstar (fs fd : Tech) (gap : ℝ) : ℝ := 2 / Delta fs fd * gap

/-- Stage-game payoff of an agent who exerts effort `e` while the teammate exerts `e'`:
`f(e + e') w − c e` (success wage `w`, failure payment `0`). -/
def stagePayoff (T : Tech) (c w : ℝ) (e e' : ℕ) : ℝ := T.f (e + e') * w - c * e

/-- `(e₁, e₂)` is a pure Nash equilibrium of the one-shot team stage game with binary efforts. -/
def IsStageNE (T : Tech) (c w : ℝ) (e₁ e₂ : ℕ) : Prop :=
  e₁ ≤ 1 ∧ e₂ ≤ 1 ∧
    (∀ e : ℕ, e ≤ 1 → stagePayoff T c w e e₂ ≤ stagePayoff T c w e₁ e₂) ∧
    (∀ e : ℕ, e ≤ 1 → stagePayoff T c w e e₁ ≤ stagePayoff T c w e₂ e₁)

end TeamDiversity.WageGap


