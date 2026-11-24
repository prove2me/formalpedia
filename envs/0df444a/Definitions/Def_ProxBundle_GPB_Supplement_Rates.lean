-- Prove2me | Definitions.Def_ProxBundle_GPB_Supplement_Rates
-- name    : ProxBundle_GPB_Supplement_Rates
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T03:33:44.529899+00:00
-- url     : https://prove2.me/theorems/49ceb9f1-2be0-4454-bbd8-4cbcb4f2a718
-- title:
--   Equations (5), (16), (37), (39), (70) — uniform rates and iteration bounds
-- statement:
--   Let $\varepsilon>0$ denote the target accuracy, $\mu\ge0$ the strong convexity parameter, $r=d_0^2$ the squared distance to the solution set, and $S\ge0$ a hybrid squared scale. Define the two-regime rate
--
--   $$
--   B_\mu(\varepsilon,S,r)=\begin{cases}Sr/\varepsilon^2,&\mu=0,\\
--   \min\{Sr/\varepsilon^2,(S/(\mu\varepsilon)+1)\log(1+\mu r/\varepsilon)\},&\mu>0.
--   \end{cases}
--   $$
--   For the initial-cycle bound $\bar t$ of (58), set $L=0$ when $\bar t=0$ and $L=\max\{\log(4\bar t/\varepsilon),0\}$ otherwise. The stepsize interval means $S>0$ and $\varepsilon/(CS)\le\lambda\le Cr/\varepsilon$. The constants used below are $K_{31}(C)=10(1+2\max\{C,1\})$ and $K_{53}(C)=18(1+2\max\{C,1\})$. A run obtains a solution within a real bound $B$ if there is an accepted index $j\ge0$ with $j\le B$ and $\phi(y_j)-\phi^*\le\varepsilon$. The corrected adaptive product is $(\lceil2(1+8\lambda_\mu T_\varepsilon^2/\varepsilon)L\rceil+1)(\operatorname{serBound}+1)$.
--
--   These scalar definitions expose the uniform meaning of rates (5) and (16), without hiding parameter dependence inside asymptotic notation.
--
--   **Formalization Note** The functions are used only with $\mu\ge0$, $\varepsilon,\lambda,C>0$, $r,S\ge0$. The interval requires $S>0$ to make its denominator meaningful; this affects only the interval-qualified claims. The zero and small-log cases and integer ceiling correct the boundary omission in (70); they do not restrict the arbitrary-stepsize claim. The explicit constants are supported universal choices, not constants printed in the paper. The model and its domain conventions are the published ones.
-- source:
--   Liang & Monteiro, arXiv:2110.01084v3, pp. 2, 4, 6, 11, 18–21, (5), (16), (37), (39), proof (62)–(66), (70)

import Mathlib
import Definitions.Def_ProxBundle_GPB_Model

noncomputable section

namespace ProxBundle.GPB.Supplement

/-- The two regimes in (5)/(16), with the convex-case convention. -/
def rate (μ ε S r : ℝ) : ℝ :=
  if μ = 0 then S * r / ε ^ 2
  else min (S * r / ε ^ 2)
    ((S / (μ * ε) + 1) * Real.log (1 + μ * r / ε))

/-- The explicit logarithmic factor, including the zero-gap convention. -/
def logFactor (tb ε : ℝ) : ℝ :=
  if tb = 0 then 0 else max (Real.log (4 * tb / ε)) 0

/-- Full stepsize interval (37) or (39), with definedness of its denominator. -/
def StepInterval (C ε S lam r : ℝ) : Prop :=
  0 < S ∧ ε / (C * S) ≤ lam ∧ lam ≤ C * r / ε

/-- A successful accepted index, including the initial point. -/
def Obtains {n : ℕ} (P : Instance n) (R : Run n) (x0s : E n) (ε bound : ℝ) : Prop :=
  ∃ j : ℕ, (j : ℝ) ≤ bound ∧ P.φ (R.y j) - P.φ x0s ≤ ε

/-- Explicit universal choices: only C, never problem data, enters these constants. -/
def K31 (C : ℝ) : ℝ := 10 * (1 + 2 * max C 1)

def K53 (C : ℝ) : ℝ := 18 * (1 + 2 * max C 1)

/-- The corrected accepted-iteration product (70); not a run premise. -/
def adaptiveBound (μ lam ε Mbar Lbar d0 : ℝ) : ℝ :=
  ((⌈2 * (1 + 8 * lamMu μ lam * (Mbar ^ 2 + ε * Lbar) / ε) *
    logFactor (tbar Mbar Lbar lam d0) ε⌉ : ℝ) + 1) *
    (serBound μ lam ε (d0 ^ 2) + 1)

end ProxBundle.GPB.Supplement


