-- Prove2me | Definitions.Def_ProxBundle_GPB_Supplement_Adaptive
-- name    : ProxBundle_GPB_Supplement_Adaptive
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T03:34:15.024323+00:00
-- url     : https://prove2.me/theorems/e9b11bc2-ba3e-4246-bd9d-0e46e4722173
-- title:
--   §5, pp. 19–20 — operational 1C-APB trials, accepted runs and cycles
-- statement:
--   Fix a composite instance on $D=\operatorname{dom}h$, an initial point $x_0\in D$, a stepsize $\lambda>0$, a tolerance $\varepsilon>0$, and $\beta\ge1$. An adaptive run stores accepted $(x_j,y_j,x_j^c,\Gamma_j,\tau_j)$ and, at every positive accepted index, a finite nonempty history of trials. It initializes $y_0=x_0$, $t_0=\tau_0=0$. The first trial uses $\tau=\tau_{j-1}/\beta$. Every trial performs exactly the serious or null model update of step 2, computes a proximal minimizer over $D$, and picks a best point among the previously accepted points and that trial point. Its gap is $t=\phi(y)-\Gamma(x)-\|x-x^c\|^2/(2\lambda)$.
--
--   $$
--   \Gamma=\begin{cases}\ell_f(\cdot;x_{j-1})+h,&t_{j-1}\le\varepsilon/2,\\
--   \tau\Gamma_{j-1}+(1-\tau)(\ell_f(\cdot;x_{j-1})+h),&t_{j-1}>\varepsilon/2.
--   \end{cases}
--   $$
--   A trial is rejected precisely when $t_{j-1}>\varepsilon/2$ and $t>\tau t_{j-1}+(1-\tau)\varepsilon/4$; its successor sets $\tau\leftarrow(1+\tau)/2$ and recomputes the model and point. Every nonfinal trial is rejected and the final trial is accepted, providing the stored accepted data. Rejected points never enter later best-point sets. A cycle has endpoints $a<b$ that are consecutive serious indices, with cycle indices $a+1,\ldots,b$. The auxiliary threshold is
--
--   $$
--   \bar\tau=\frac{8\lambda_\mu T_\varepsilon^2}{\varepsilon+8\lambda_\mu T_\varepsilon^2},\qquad T_\varepsilon^2=\bar M_f^2+\varepsilon\bar L_f.
--   $$
--   This operational interface permits all $\beta\ge1$ and distinguishes accepted iterations from trial work. It assumes neither coefficient bounds nor gap contraction nor a complexity estimate.
--
--   **Formalization Note** This extends the published run data, using its proximal minimizer, cut, objective and gap definitions. Models are real-valued on $D$ and extended by $+\infty$ outside it when required; all model identities and minimizations are relative to $D$. The formula for $\bar\tau$ continuously extends (67) by zero at $T_\varepsilon^2=0$. Infinite accepted runs retain finite histories at each index; no fixed-$\tau$ GPB run condition is imposed. Trial counts and fields at index zero are unused. Cycles are characterized by consecutive serious endpoints, including endpoint zero.
-- source:
--   Liang & Monteiro, arXiv:2110.01084v3, pp. 19–20, 1C-APB steps 0–4, (67)–(68); pp. 8–9, (28), (31)–(33)

import Mathlib
import Definitions.Def_ProxBundle_GPB_Model

noncomputable section

namespace ProxBundle.GPB.Supplement

/-- One execution of steps 2 and 3, before the acceptance test. -/
structure Trial (n : ℕ) where
  τ : ℝ
  x : E n
  y : E n
  xc : E n
  Γ : E n → ℝ

def Trial.m {n : ℕ} (U : Trial n) (lam : ℝ) : ℝ :=
  U.Γ U.x + ‖U.x - U.xc‖ ^ 2 / (2 * lam)

def Trial.t {n : ℕ} (U : Trial n) (P : Instance n) (lam : ℝ) : ℝ :=
  P.φ U.y - U.m lam

/-- Accepted data and finite, nonempty histories of trials at each positive index.
Only indices q < count j are used. No contraction or complexity is stored here. -/
structure APBRun (n : ℕ) where
  accepted : Run n
  τ : ℕ → ℝ
  count : ℕ → ℕ
  trial : ℕ → ℕ → Trial n

/-- Exactly the rejection test in step 4 of 1C-APB. -/
def Reject {n : ℕ} (P : Instance n) (lam ε : ℝ) (R : Run n)
    (j : ℕ) (U : Trial n) : Prop :=
  ε / 2 < R.t P lam (j - 1) ∧
    U.τ * R.t P lam (j - 1) + (1 - U.τ) * ε / 4 < U.t P lam

/-- Steps 2 and 3 of a trial. The best point uses only accepted previous points
and the current trial point; rejected points never enter the accepted history. -/
def IsTrial {n : ℕ} (P : Instance n) (lam ε : ℝ) (R : Run n)
    (j : ℕ) (U : Trial n) : Prop :=
  (R.t P lam (j - 1) ≤ ε / 2 →
    U.xc = R.x (j - 1) ∧
      ∀ u ∈ P.D, U.Γ u = P.ellf u (R.x (j - 1)) + P.h u) ∧
  (ε / 2 < R.t P lam (j - 1) →
    U.xc = R.xc (j - 1) ∧ ∀ u ∈ P.D,
      U.Γ u = U.τ * R.Γ (j - 1) u +
        (1 - U.τ) * (P.ellf u (R.x (j - 1)) + P.h u)) ∧
  P.IsProxMin U.Γ U.xc lam U.x ∧
  ((∃ i : ℕ, i < j ∧ U.y = R.x i) ∨ U.y = U.x) ∧
  (∀ i : ℕ, i < j → P.φ U.y ≤ P.φ (R.x i)) ∧
  P.φ U.y ≤ P.φ U.x

/-- Initialization and steps 1–4 of 1C-APB. A finite history records all failed
trials followed by the first accepted one. Bounds on τ and gaps are conclusions,
not fields of this predicate. -/
def IsAPBRun {n : ℕ} (P : Instance n) (lam ε β : ℝ) (x0 : E n)
    (A : APBRun n) : Prop :=
  A.accepted.x 0 = x0 ∧ A.accepted.y 0 = x0 ∧ A.τ 0 = 0 ∧
  ∀ j : ℕ, 1 ≤ j →
    0 < A.count j ∧
    (A.trial j 0).τ = A.τ (j - 1) / β ∧
    (∀ q : ℕ, q < A.count j → IsTrial P lam ε A.accepted j (A.trial j q)) ∧
    (∀ q : ℕ, q + 1 < A.count j →
      Reject P lam ε A.accepted j (A.trial j q) ∧
        (A.trial j (q + 1)).τ = (1 + (A.trial j q).τ) / 2) ∧
    ¬ Reject P lam ε A.accepted j (A.trial j (A.count j - 1)) ∧
    A.τ j = (A.trial j (A.count j - 1)).τ ∧
    A.accepted.x j = (A.trial j (A.count j - 1)).x ∧
    A.accepted.y j = (A.trial j (A.count j - 1)).y ∧
    A.accepted.xc j = (A.trial j (A.count j - 1)).xc ∧
    (∀ u ∈ P.D, A.accepted.Γ j u = (A.trial j (A.count j - 1)).Γ u)

/-- Continuous form of (67); τ̄ = 0 at T² = 0. It is not imposed on accepted τ. -/
def tauBar (μ lam ε Mbar Lbar : ℝ) : ℝ :=
  8 * lamMu μ lam * (Mbar ^ 2 + ε * Lbar) /
    (ε + 8 * lamMu μ lam * (Mbar ^ 2 + ε * Lbar))

/-- Endpoints of a cycle: consecutive serious indices a<b; index zero is allowed. -/
def IsCycle {n : ℕ} (P : Instance n) (R : Run n) (lam ε : ℝ) (a b : ℕ) : Prop :=
  a < b ∧ R.t P lam a ≤ ε / 2 ∧ R.t P lam b ≤ ε / 2 ∧
    ∀ i : ℕ, a < i → i < b → ε / 2 < R.t P lam i

end ProxBundle.GPB.Supplement


