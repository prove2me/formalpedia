-- Prove2me | Definitions.Def_OLPDual_EventE2
-- name    : OLPDual_EventE2
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:21:17.172638+00:00
-- url     : https://prove2.me/theorems/b2ac9656-3a4c-462f-97f4-3f6131876bb1
-- title:
--   The constants $q$, $N$, $\kappa$ and the events $\mathcal E_1$, $\mathcal E_2$
-- statement:
--   This module defines the quantities of Proposition 4 and of the proof of Theorem 1. With $\bar a,\bar r,\underline d,\lambda,\mu,\lambda_{\min}$ the parameters of the family $\Xi$,
--
--   $$
--   q=\max\Bigl\{\frac{1}{1+\frac{1}{\sqrt m}},\ \frac{1}{1+\frac{1}{\sqrt m}\bigl(\frac{\lambda\lambda_{\min}}{8\mu\bar a^2}\bigr)^{1/3}}\Bigr\},\qquad
--   N=\Bigl\lfloor\log_q\frac{\underline d\epsilon^2}{\bar a\bar r\sqrt m}\Bigr\rfloor+1,
--   $$
--
--   and
--
--   $$
--   \kappa=\frac{2\bar a+1+\sqrt{(2\bar a+1)^2+\lambda\lambda_{\min}/8}}{\lambda\lambda_{\min}/16}.
--   $$
--
--   For a point $p^*$ and $\epsilon>0$, the events on the sample are
--
--   $$
--   \mathcal E_1=\Bigl\{\Bigl\|\frac1n\sum_{j=1}^n\phi(p^*,u_j)-\nabla f(p^*)\Bigr\|\le\epsilon\Bigr\},
--   $$
--
--   $$
--   \mathcal E_2=\Bigl\{\frac1n\sum_{j=1}^n\int_{a_j^\top p}^{a_j^\top p^*}\bigl(I(r_j>v)-I(r_j>a_j^\top p^*)\bigr)\,dv\ge-\epsilon^2-2\epsilon\bar a\|p^*-p\|+\frac{\lambda\lambda_{\min}}{32}\|p^*-p\|^2\ \text{ for all }p\in\Omega_p\Bigr\}.
--   $$
--
--   The first controls the first-order term of the identity (11) and the second its second-order term; on their intersection the sampled dual optimum is within $\kappa\epsilon$ of $p^*$.
--
--   **Formalization Note** The $d$ in the printed formula for $N$ is the underlined lower bound $\underline d$. `covRatio` is $q$ and `covLayers` is $N$, an integer. The quantifier over $p$ in $\mathcal E_2$ is inside the event.
-- source:
--   Li–Ye, Online Linear Programming: Dual Convergence, New Algorithms, and Regret Bounds, arXiv:1909.05499v5 (19 Apr 2021), Proposition 4 p.13 (q, N, event (12)), proof of Theorem 1 pp.40–41 (ℰ₁, ℰ₂, κ)

import Mathlib
import Definitions.Def_OLPDual_Model

open scoped RealInnerProductSpace

namespace OLPDual

/-- The ratio `q = max{1/(1 + 1/√m), 1/(1 + (1/√m)(λλ_min/(8μā²))^{1/3})}` of Proposition 4,
Li–Ye, arXiv:1909.05499v5, p.13 (PDF 13). -/
noncomputable def covRatio (Θ : Model) (m : ℕ) : ℝ :=
  max (1 / (1 + 1 / Real.sqrt m))
    (1 / (1 + (1 / Real.sqrt m) *
      (Θ.lam * Θ.lamMin / (8 * Θ.mu * Θ.abar ^ 2)) ^ ((1 : ℝ) / 3)))

/-- The number of layers `N = ⌊log_q(d̲ε²/(ā r̄ √m))⌋ + 1` of Proposition 4,
Li–Ye, arXiv:1909.05499v5, p.13 (PDF 13). The `d` of the printed formula is the underlined `d̲`. -/
noncomputable def covLayers (Θ : Model) (m : ℕ) (ε : ℝ) : ℤ :=
  ⌊Real.logb (covRatio Θ m) (Θ.dlow * ε ^ 2 / (Θ.abar * Θ.rbar * Real.sqrt m))⌋ + 1

/-- The sample second-order term `(1/n) Σ_j ∫_{a_jᵀp}^{a_jᵀp*} (I(r_j > v) − I(r_j > a_jᵀp*)) dv`
of (11) and (12), Li–Ye, arXiv:1909.05499v5, pp.12–13 (PDF 12–13). -/
noncomputable def secondOrderTerm {m n : ℕ} (ω : Sample m n) (p pstar : E m) : ℝ :=
  (1 / (n : ℝ)) * ∑ j, knightTerm (ω j).1 (ω j).2 p pstar

/-- The event `ℰ₁ = {‖(1/n) Σ_j φ(p*, u_j) − ∇f(p*)‖ ≤ ε}`, Li–Ye, arXiv:1909.05499v5, proof of
Theorem 1, p.40 (PDF 40). -/
def EventE1 {m : ℕ} (d : E m) (law : MeasureTheory.Measure (E m × ℝ)) (pstar : E m) (ε : ℝ)
    (n : ℕ) : Set (Sample m n) :=
  {ω | ‖(1 / (n : ℝ)) • ∑ j, phi d pstar (ω j) - gradf d law pstar‖ ≤ ε}

/-- The event of (12), `ℰ₂ = {(1/n) Σ_j ∫_{a_jᵀp}^{a_jᵀp*} (I(r_j > v) − I(r_j > a_jᵀp*)) dv ≥
−ε² − 2εā‖p* − p‖ + (λλ_min/32)‖p* − p‖² for all p ∈ Ω_p}`, Li–Ye, arXiv:1909.05499v5,
Proposition 4, p.13 (PDF 13), and proof of Theorem 1, p.40 (PDF 40). The quantifier over `p` is
inside the event. -/
def EventE2 (Θ : Model) {m : ℕ} (pstar : E m) (ε : ℝ) (n : ℕ) : Set (Sample m n) :=
  {ω | ∀ p ∈ OmegaP Θ m,
    -ε ^ 2 - 2 * ε * Θ.abar * ‖pstar - p‖ + Θ.lam * Θ.lamMin / 32 * ‖pstar - p‖ ^ 2 ≤
      secondOrderTerm ω p pstar}

/-- `κ = (2ā + 1 + √((2ā + 1)² + λλ_min/8)) / (λλ_min/16)`, Li–Ye, arXiv:1909.05499v5, proof of
Theorem 1, p.41 (PDF 41). -/
noncomputable def kappa (Θ : Model) : ℝ :=
  (2 * Θ.abar + 1 + Real.sqrt ((2 * Θ.abar + 1) ^ 2 + Θ.lam * Θ.lamMin / 8)) /
    (Θ.lam * Θ.lamMin / 16)

end OLPDual


