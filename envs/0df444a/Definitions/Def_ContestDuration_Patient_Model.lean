-- Prove2me | Definitions.Def_ContestDuration_Patient_Model
-- name    : ContestDuration_Patient_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T02:22:51.232169+00:00
-- url     : https://prove2.me/theorems/acc8fce1-cfc2-4ae9-88fa-408b5a38d076
-- title:
--   Fixed-award innovation contest model and patient threshold
-- statement:
--   Consider $N$ agents, cost exponent $b>1$, cost coefficient $c>0$, fixed participation cost $F>0$, total present-value award $A>0$, award shares $\gamma(j)$, and organizer discount factor $\delta\ge0$. For productivity $\theta$, define
--
--   $$\tau(T)=\int_0^T\theta(t)^{b/(b-1)}dt,\qquad \psi(e,T)=c e^b\tau(T)^{1-b},\qquad e^*(T)=\left(\frac{Ax}{cb}\right)^{1/(b-1)}\tau(T),$$
--
--   where $x=\sum_{j=1}^N I_j^N\gamma(j)$ and $I_j^N$ is the marginal rank probability of equation (4). The organizer's profit is $\Pi(T)=e^{-\delta T}(e^*(T)+E_N(h))-A$. A feasible duration satisfies the agent's participation condition (8); an optimal duration maximizes this profit among feasible positive durations. The patient threshold $\delta_1$ is the expression in the proof of Lemma 2, evaluated at a positive solution $\bar T$ of equation (9).
--
--   These definitions fix the award scheme while duration varies, as in §3, and expose the participation constraint and the regime threshold used by Theorem 1.
--
--   **Formalization Note** Ranks are natural numbers from $1$ through $N$. The real-power expressions are used at positive duration and positive $x$. The rank-probability integral from p. 11 defines the agent's best-response condition (7). An optimal duration satisfies both that condition and participation (8). At the proposed patient duration, best-response feasibility is required as in footnote 11 on p. 13. Unimodality means either strict increase throughout or strict increase up to one mode followed by strict decrease.
-- source:
--   Korpeoglu, Körpeoğlu & Tunç, Optimal Duration of Innovation Contests, SSRN 3064763 (authors' version, forthcoming at M&SOM; PDF of 2020-07-23), pp. 8–13, §2 and §3, Lemma 1 and equations (1)–(9); p. 27, proof of Lemma 2 (δ1)

import Mathlib
import Definitions.Def_ContestDuration_Patient_Shock

open MeasureTheory
open CrowdContest.Pooling (cdf)

namespace ContestDuration.Patient

/-- Primitives of the fixed-award innovation contest. -/
structure Params where
  N : ℕ
  b : ℝ
  c : ℝ
  F : ℝ
  A : ℝ
  γ : ℕ → ℝ
  δ : ℝ

/-- The standing assumptions of §2, pp. 8–12. -/
def Params.Standing (P : Params) : Prop :=
  2 ≤ P.N ∧ 1 < P.b ∧ 0 < P.c ∧ 0 < P.F ∧ 0 < P.A ∧
  P.F < P.A / P.N ∧ 0 ≤ P.δ ∧
  (∀ j ∈ Finset.Icc 1 P.N, 0 ≤ P.γ j) ∧
  (∀ j, 1 ≤ j → j < P.N → P.γ (j + 1) ≤ P.γ j) ∧
  ∑ j ∈ Finset.Icc 1 P.N, P.γ j = 1

def ProductivityOK (θ : ℝ → ℝ) : Prop :=
  Continuous θ ∧ ∀ t, 0 ≤ t → 0 < θ t

/-- Equation (4), expanded so natural-number exponents behave correctly at ranks 1 and N. -/
noncomputable def Irank (N j : ℕ) (h : ℝ → ℝ) : ℝ :=
  ((N - 1).choose (j - 1) : ℝ) *
    ∫ s, ((((N - j : ℕ) : ℝ) * cdf h s ^ (N - j - 1) * (1 - cdf h s) ^ (j - 1)
      - ((j - 1 : ℕ) : ℝ) * cdf h s ^ (N - j) * (1 - cdf h s) ^ (j - 2)) * h s ^ 2)

/-- Award-weighted marginal rank probability x from equation (5). -/
noncomputable def xOf (P : Params) (h : ℝ → ℝ) : ℝ :=
  ∑ j ∈ Finset.Icc 1 P.N, Irank P.N j h * P.γ j

/-- τ(T) from Lemma 1. -/
noncomputable def tau (b : ℝ) (θ : ℝ → ℝ) (T : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..T, θ t ^ (b / (b - 1))

/-- Optimal per-time allocation from Lemma 1. -/
noncomputable def allocation (b : ℝ) (θ : ℝ → ℝ) (e T : ℝ) (t : ℝ) : ℝ :=
  e * θ t ^ (1 / (b - 1)) / tau b θ T

/-- Total deterministic output improvement of a per-time effort path. -/
noncomputable def totalEffort (θ η : ℝ → ℝ) (T : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..T, θ t * η t

/-- Total per-time effort cost. -/
noncomputable def allocationCost (c b : ℝ) (η : ℝ → ℝ) (T : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..T, c * η t ^ b

/-- Optimally allocated effort cost ψ(e,T) from Lemma 1. -/
noncomputable def psi (P : Params) (θ : ℝ → ℝ) (e T : ℝ) : ℝ :=
  P.c * e ^ P.b * tau P.b θ T ^ (1 - P.b)

/-- Symmetric equilibrium effort from equation (5). -/
noncomputable def effort (P : Params) (θ h : ℝ → ℝ) (T : ℝ) : ℝ :=
  (P.A * xOf P h / (P.c * P.b)) ^ (1 / (P.b - 1)) * tau P.b θ T

/-- Probability of rank `j` when one agent chooses `e` and the others choose `es` (p. 11). -/
noncomputable def rankProb (N j : ℕ) (h : ℝ → ℝ) (e es : ℝ) : ℝ :=
  ((N - 1).choose (j - 1) : ℝ) *
    ∫ s, cdf h (s + e - es) ^ (N - j) *
      (1 - cdf h (s + e - es)) ^ (j - 1) * h s

/-- The symmetric effort from (5) solves the agent's actual best-response problem (7). -/
def IsEquilibrium (P : Params) (θ h : ℝ → ℝ) (T : ℝ) : Prop :=
  0 ≤ effort P θ h T ∧
    ∀ e : ℝ, 0 ≤ e →
      (∑ j ∈ Finset.Icc 1 P.N,
        rankProb P.N j h e (effort P θ h T) * (P.γ j * P.A)) -
          psi P θ e T - P.F ≤
      (∑ j ∈ Finset.Icc 1 P.N,
        rankProb P.N j h (effort P θ h T) (effort P θ h T) * (P.γ j * P.A)) -
          psi P θ (effort P θ h T) T - P.F

/-- Organizer profit (6), with the award scheme held fixed as in §3. -/
noncomputable def profit (P : Params) (θ h : ℝ → ℝ) (T : ℝ) : ℝ :=
  Real.exp (-P.δ * T) * (effort P θ h T + CrowdContest.Pooling.expMax h P.N) -
    ∑ j ∈ Finset.Icc 1 P.N, P.γ j * P.A

/-- Participation condition (8). -/
def Participates (P : Params) (θ h : ℝ → ℝ) (T : ℝ) : Prop :=
  0 ≤ (1 / (P.N : ℝ)) * (∑ j ∈ Finset.Icc 1 P.N, P.γ j * P.A) -
    psi P θ (effort P θ h T) T - P.F

/-- Maximizer of (6) over positive durations satisfying (7) and (8). -/
def IsOptDuration (P : Params) (θ h : ℝ → ℝ) (T : ℝ) : Prop :=
  0 < T ∧ IsEquilibrium P θ h T ∧ Participates P θ h T ∧
    ∀ T', 0 < T' → IsEquilibrium P θ h T' → Participates P θ h T' →
      profit P θ h T' ≤ profit P θ h T

/-- Explicit reading of the paper's unimodality assumption. -/
def Unimodal (f : ℝ → ℝ) : Prop :=
  StrictMonoOn f (Set.Ici 0) ∨
    ∃ m, 0 < m ∧ StrictMonoOn f (Set.Icc 0 m) ∧ StrictAntiOn f (Set.Ici m)

/-- The regularity assumptions on the organizer's profit on p. 12. -/
def RegularProfit (P : Params) (θ h : ℝ → ℝ) : Prop :=
  Unimodal (profit P θ h) ∧ 0 < derivWithin (profit P θ h) (Set.Ici 0) 0

/-- Right-hand side of equation (9). -/
noncomputable def Kbar (P : Params) (h : ℝ → ℝ) : ℝ :=
  (P.A - P.N * P.F) / (P.c * P.N) *
    (P.A * xOf P h / (P.c * P.b)) ^ (-(P.b / (P.b - 1)))

/-- δ₁ from the proof of Lemma 2 on p. 27, evaluated at T̄. -/
noncomputable def delta1 (P : Params) (θ h : ℝ → ℝ) (Tb : ℝ) : ℝ :=
  θ Tb ^ (P.b / (P.b - 1)) *
    (P.A * xOf P h / (P.c * P.b)) ^ (1 / (P.b - 1)) /
      (P.b * (P.A - P.N * P.F) / (P.N * xOf P h * P.A) +
        CrowdContest.Pooling.expMax h P.N)

/-- The patient regime, including a usable solution T̄ to (9), as required in footnote 11. -/
def IsPatient (P : Params) (θ h : ℝ → ℝ) : Prop :=
  ∃ Tb, 0 < Tb ∧ tau P.b θ Tb = Kbar P h ∧
    P.δ < delta1 P θ h Tb ∧ IsEquilibrium P θ h Tb

end ContestDuration.Patient


