-- Prove2me | Definitions.Def_ALADIN_LocalStab_Supplement_Algorithm
-- name    : ALADIN_LocalStab_Supplement_Algorithm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T02:07:53.860788+00:00
-- url     : https://prove2.me/theorems/85fb04de-80ea-4d3e-be9a-cb274057df43
-- title:
--   Algorithms 2 and 3: NLP/QP solutions, stopping tests, and ordered globalization branches
-- statement:
--   One step contains all chosen NLP solutions $y_i$, inequality multipliers $\kappa_i$, matrices $\Sigma_i,C_i,H_i$, penalties $\rho,\mu$, QP variables $(\Delta y,s)$ and the actual coupling multiplier $\lambda_{QP}$. The exact active Jacobian has zero rows on inactive constraints, and $g_i=\nabla f_i+(C_i^*-C_i)^T\kappa_i$. The QP is
--   $$\min_{\Delta y,s}\sum_i\left(\tfrac12\Delta y_i^T H_i\Delta y_i+g_i^T\Delta y_i\right)+\lambda^Ts+\tfrac\mu2\|s\|_2^2,\quad r(y+\Delta y)=s,\quad C_i\Delta y_i=0.$$
--   Prepared requires positive penalties, positive definite scaling, positive semidefinite Hessian approximations, feasible local NLP solutions with KKT multipliers and LICQ, and global primal QP optimality with its stationarity multipliers. Global NLP solutions are included. The stop test uses the coupling one-norm and every block's $\rho\|\Sigma_i(y_i-x_i)\|_1$.
--
--   The ordered branch relation first accepts $(1,1,1)$ if (6.2) holds at $y+\Delta y$, then $(1,0,0)$ if it holds at $y$, otherwise chooses $(0,0,a)$ with $a\in(0,1]$ globally maximizing the exact dual value along the QP direction. The updates are $x^+=x+\alpha_1(y-x)+\alpha_2\Delta y$ and $\lambda^+=\lambda+\alpha_3(\lambda_{QP}-\lambda)$. InfiniteRun retains all per-iteration choices and imposes no convergence premise. Existence of a line-search maximizer is not built into the step data.
--
--   **Formalization Note** Prepared is a per-step admissibility predicate, not a substitute for the paper's qualitative parameter thresholds. The counterexamples quantify arbitrarily large penalties directly. The stationarity sign on p. 1108 is corrected to plus, as required by differentiating (3.2).
-- source:
--   Houska, Frasch, Diehl, An augmented Lagrangian based algorithm for distributed nonconvex optimization, SIAM J. Optim. 26 (2016), DOI 10.1137/140975991, pp. 1108, 1112–1113, Algorithms 2/3, (3.2), (3.3), (6.2); footnote 5

import Mathlib
import Definitions.Def_ALADIN_LocalStab_Supplement_Values

noncomputable section

namespace ALADIN.LocalStab.Supplement

open Matrix

variable {N n m nh : ℕ}

noncomputable def grad {d : ℕ} (f : (Fin d → ℝ) → ℝ) (z : Fin d → ℝ) : Fin d → ℝ :=
  fun j => fderiv ℝ f z (Pi.single j 1)

noncomputable def activeJac (P : Problem N n m nh) (y : Fin N → Fin n → ℝ)
    (i : Fin N) : Matrix (Fin nh) (Fin n) ℝ :=
  fun j k => if P.h i (y i) j = 0 then grad (fun z => P.h i z j) (y i) k else 0

noncomputable def exactHessian (P : Problem N n m nh) (y : Fin N → Fin n → ℝ)
    (κ : Fin N → Fin nh → ℝ) (i : Fin N) : Matrix (Fin n) (Fin n) ℝ :=
  fun j k => fderiv ℝ (fderiv ℝ (P.lagBlock i (κ i))) (y i)
    (Pi.single j 1) (Pi.single k 1)

/-- Arbitrary choices in one iteration of Algorithm 2, before choosing step lengths. -/
structure Step (N n m nh : ℕ) where
  ρ : ℝ
  Sig : Fin N → Matrix (Fin n) (Fin n) ℝ
  μ : ℝ
  y : Fin N → Fin n → ℝ
  κ : Fin N → Fin nh → ℝ
  C : Fin N → Matrix (Fin nh) (Fin n) ℝ
  H : Fin N → Matrix (Fin n) (Fin n) ℝ
  dy : Fin N → Fin n → ℝ
  s : Fin m → ℝ
  lamQP : Fin m → ℝ

noncomputable def modifiedGradient (P : Problem N n m nh) (D : Step N n m nh)
    (i : Fin N) : Fin n → ℝ :=
  grad (P.f i) (D.y i) + (activeJac P D.y i - D.C i).transpose *ᵥ D.κ i

noncomputable def qpObjective (P : Problem N n m nh) (lam : Fin m → ℝ)
    (D : Step N n m nh) (dy : Fin N → Fin n → ℝ) (s : Fin m → ℝ) : ℝ :=
  (∑ i, ((dy i ⬝ᵥ (D.H i *ᵥ dy i)) / 2 + modifiedGradient P D i ⬝ᵥ dy i)) +
    lam ⬝ᵥ s + D.μ / 2 * sq s

def QPFeasible (P : Problem N n m nh) (D : Step N n m nh)
    (dy : Fin N → Fin n → ℝ) (s : Fin m → ℝ) : Prop :=
  residual P (D.y + dy) = s ∧ ∀ i, D.C i *ᵥ dy i = 0

/-- Primal global optimality and the actual QP multiplier, with the sign of (3.3). -/
noncomputable def QPSolved (P : Problem N n m nh) (lam : Fin m → ℝ) (D : Step N n m nh) : Prop :=
  QPFeasible P D D.dy D.s ∧
  (∀ dy s, QPFeasible P D dy s → qpObjective P lam D D.dy D.s ≤ qpObjective P lam D dy s) ∧
  lam + D.μ • D.s - D.lamQP = 0 ∧
  ∃ η : Fin N → Fin nh → ℝ, ∀ i,
    D.H i *ᵥ D.dy i + modifiedGradient P D i + (P.A i).transpose *ᵥ D.lamQP +
      (D.C i).transpose *ᵥ η i = 0

/-- Local or global NLP solutions are both permitted. The stationarity sign is +rho Sigma(y-x). -/
noncomputable def NLPSolved (P : Problem N n m nh) (x : Fin N → Fin n → ℝ)
    (lam : Fin m → ℝ) (D : Step N n m nh) : Prop :=
  (∀ i, IsDecoupledLocalMin P D.ρ D.Sig x lam i (D.y i)) ∧
  (∀ i j, 0 ≤ D.κ i j ∧ D.κ i j * P.h i (D.y i) j = 0) ∧
  (∀ i, grad (P.f i) (D.y i) + (P.A i).transpose *ᵥ lam +
      (activeJac P D.y i).transpose *ᵥ D.κ i + D.ρ • (D.Sig i *ᵥ (D.y i - x i)) = 0) ∧
  (∀ i (ν : Fin nh → ℝ),
    (∀ j, P.h i (D.y i) j ≠ 0 → ν j = 0) →
    (activeJac P D.y i).transpose *ᵥ ν = 0 → ν = 0)

def Stops (P : Problem N n m nh) (x : Fin N → Fin n → ℝ)
    (ε : ℝ) (D : Step N n m nh) : Prop :=
  oneNorm (residual P D.y) ≤ ε ∧
    ∀ i, D.ρ * oneNorm (D.Sig i *ᵥ (D.y i - x i)) ≤ ε

noncomputable def Prepared (P : Problem N n m nh) (x : Fin N → Fin n → ℝ)
    (lam : Fin m → ℝ) (D : Step N n m nh) : Prop :=
  0 < D.ρ ∧ 0 < D.μ ∧ (∀ i, (D.Sig i).PosDef) ∧ (∀ i, (D.H i).PosSemidef) ∧
  NLPSolved P x lam D ∧ QPSolved P lam D

def Accept (P : Problem N n m nh) (L K γ : ℝ) (x z : Fin N → Fin n → ℝ)
    (D : Step N n m nh) : Prop :=
  γ * (D.ρ * proxTerm D.Sig x D.y + L * oneNorm (residual P D.y)) ≤
    phi P L K x - phi P L K z

/-- Ordered branches (a), (b), (c); no existence of a maximizer is built into the data. -/
noncomputable def Globalization (P : Problem N n m nh) (L K γ : ℝ)
    (x : Fin N → Fin n → ℝ) (lam : Fin m → ℝ) (D : Step N n m nh)
    (a₁ a₂ a₃ : ℝ) : Prop :=
  (Accept P L K γ x (D.y + D.dy) D ∧ a₁ = 1 ∧ a₂ = 1 ∧ a₃ = 1) ∨
  (¬ Accept P L K γ x (D.y + D.dy) D ∧ Accept P L K γ x D.y D ∧
    a₁ = 1 ∧ a₂ = 0 ∧ a₃ = 0) ∨
  (¬ Accept P L K γ x (D.y + D.dy) D ∧ ¬ Accept P L K γ x D.y D ∧
    a₁ = 0 ∧ a₂ = 0 ∧ a₃ ∈ Set.Ioc 0 1 ∧
    ∀ a ∈ Set.Ioc (0 : ℝ) 1,
      dualValue P D.Sig D.ρ x (lam + a • (D.lamQP - lam)) ≤
        dualValue P D.Sig D.ρ x (lam + a₃ • (D.lamQP - lam)))

def nextX (x : Fin N → Fin n → ℝ) (D : Step N n m nh) (a₁ a₂ : ℝ) :=
  x + a₁ • (D.y - x) + a₂ • D.dy

def nextLam (lam : Fin m → ℝ) (D : Step N n m nh) (a₃ : ℝ) :=
  lam + a₃ • (D.lamQP - lam)

/-- An unrestricted infinite nonterminating execution, with all per-iteration choices retained.
This predicate assumes neither convergence nor eventual progress. A finite prefix can fail to
extend when Algorithm 3's open-interval maximizer does not exist. -/
noncomputable def InfiniteRun (P : Problem N n m nh) (L K γ ε : ℝ)
    (x : ℕ → Fin N → Fin n → ℝ) (lam : ℕ → Fin m → ℝ)
    (D : ℕ → Step N n m nh) (a : ℕ → Fin 3 → ℝ) : Prop :=
  0 < ε ∧ ∀ k, Prepared P (x k) (lam k) (D k) ∧ ¬ Stops P (x k) ε (D k) ∧
    Globalization P L K γ (x k) (lam k) (D k) (a k 0) (a k 1) (a k 2) ∧
    x (k+1) = nextX (x k) (D k) (a k 0) (a k 1) ∧
    lam (k+1) = nextLam (lam k) (D k) (a k 2)

end ALADIN.LocalStab.Supplement


