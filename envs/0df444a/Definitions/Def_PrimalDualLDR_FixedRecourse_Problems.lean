-- Prove2me | Definitions.Def_PrimalDualLDR_FixedRecourse_Problems
-- name    : PrimalDualLDR_FixedRecourse_Problems
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T07:52:59.231537+00:00
-- url     : https://prove2.me/theorems/623bf107-7dc5-4cd6-8947-82a9b15b8bb7
-- title:
--   The problems $\mathcal{SP}^u$, (2.3), $\mathcal{SP}^l$, (2.6), (2.8), their optimal values, and the cones $\mathcal K$, $\mathcal K_{\mathbb P}$
-- statement:
--   Fix a fixed-recourse setting $(k,n,m,l,\mathbb P, A, B, C, W, h)$ with moment matrix $M = \mathbb E(\xi\xi^\top)$. Every problem below is a minimization, and its **optimal value** is the infimum of the objective over the feasible set, taken in the extended reals $[-\infty, +\infty]$: it is $+\infty$ when the feasible set is empty and $-\infty$ when the objective is unbounded below.
--
--   1. **Primal linear-decision-rule problem** $\mathcal{SP}^u$ (p. 4): minimize $\operatorname{Tr}(MC^\top X)$ over $X \in \mathbb R^{n\times k}$, $S \in \mathbb R^{m\times k}$ subject to $AX\xi + S\xi = B\xi$ and $S\xi \ge 0$ for $\mathbb P$-almost every $\xi$.
--   2. **Linear program (2.3)** (p. 5): minimize $\operatorname{Tr}(MC^\top X)$ over $X \in \mathbb R^{n\times k}$, $\Lambda \in \mathbb R^{m\times l}$ subject to
--   $$AX + \Lambda W = B,\qquad \Lambda h \ge 0,\qquad \Lambda \ge 0.$$
--   3. **Dual linear-decision-rule problem** $\mathcal{SP}^l$ (p. 6): minimize $\mathbb E\big(c(\xi)^\top x(\xi)\big)$ over $x \in \mathcal L^2_{k,n}$, $s \in \mathcal L^2_{k,m}$ subject to
--   $$\mathbb E\big([Ax(\xi) + s(\xi) - b(\xi)]\,\xi^\top\big) = 0,\qquad s(\xi) \ge 0\ \ \mathbb P\text{-a.s.}$$
--   4. **Problem (2.6)** (p. 7): minimize $\operatorname{Tr}(MC^\top X)$ over $X \in \mathbb R^{n\times k}$, $S \in \mathbb R^{m\times k}$ subject to $AX + S = B$, the existence of $x \in \mathcal L^2_{k,n}$ with $XM = \mathbb E(x(\xi)\xi^\top)$, and the existence of $s \in \mathcal L^2_{k,m}$ with $SM = \mathbb E(s(\xi)\xi^\top)$ and $s(\xi) \ge 0$ $\mathbb P$-a.s.
--   5. **Linear program (2.8)** (p. 8): minimize $\operatorname{Tr}(MC^\top X)$ over $X \in \mathbb R^{n\times k}$, $S \in \mathbb R^{m\times k}$ subject to
--   $$AX + S = B,\qquad \big(W - h e_1^\top\big) M S^\top \ge 0.$$
--   6. The **cones of Proposition 3** (p. 7):
--   $$\mathcal K := \{z \in \mathbb R^k : (W - h e_1^\top) z \ge 0\},\qquad \mathcal K_{\mathbb P} := \{z \in \mathbb R^k : \exists s \in \mathcal L^2_{k,1} \text{ with } \mathbb E(s(\xi)\xi) = z,\ s(\xi) \ge 0\ \mathbb P\text{-a.s.}\}.$$
--
--   All inequalities between vectors and matrices are componentwise (Notation, p. 3). $\mathcal{SP}^u$ restricts the decision rules of $\mathcal{SP}$ to linear ones and so bounds its value from above; $\mathcal{SP}^l$ restricts the dual multipliers to linear ones and bounds it from below. Theorem 1 identifies the two bounds with the linear programs (2.3) and (2.8).
--
--   **Formalization Note** The objective $\mathbb E(c(\xi)^\top x(\xi))$ and the constraint $\mathbb E([Ax+s-b]\xi^\top) = 0$ are Bochner integrals, written entrywise: the $(i,j)$ entry of $\mathbb E(y(\xi)\xi^\top)$ is $\int y_i(\xi)\xi_j\,d\mathbb P$. Under the standing assumptions $\xi$ is bounded $\mathbb P$-a.s., so these integrands are integrable for every $x, s \in \mathcal L^2$ and no integral silently defaults to $0$. A feasible point of $\mathcal{SP}^u$, (2.6) or (2.8) is a pair $(X,S)$; of (2.3) a pair $(X,\Lambda)$; of $\mathcal{SP}^l$ a pair of functions $(x,s)$.
-- source:
--   Kuhn, Wiesemann, Georghiou, Primal and dual linear decision rules in stochastic and robust optimization, Optimization Online 2009/02/2218, p. 4 (SP^u), p. 5 (2.3), p. 6 (SP^l), p. 7 (2.6) and Proposition 3, p. 8 (2.8)

import Mathlib
import Definitions.Def_PrimalDualLDR_FixedRecourse_Basic
import Definitions.Def_PrimalDualLDR_FixedRecourse_Setting

open MeasureTheory Matrix

namespace PrimalDualLDR.FixedRecourse

namespace Setting

variable (σ : Setting)

/-- The objective `Tr(M Cᵀ X)` shared by `SP^u`, (2.3), (2.6) and (2.8). -/
noncomputable def linObj (X : Matrix (Fin σ.n) (Fin σ.k) ℝ) : ℝ :=
  Matrix.trace (σ.M * σ.Cᵀ * X)

/-- The feasible set of the primal linear-decision-rule problem `SP^u` (p. 4): matrices
`X ∈ ℝ^{n×k}`, `S ∈ ℝ^{m×k}` with `AXξ + Sξ = Bξ` and `Sξ ≥ 0` `P`-almost surely. -/
def feasSPu : Set (Matrix (Fin σ.n) (Fin σ.k) ℝ × Matrix (Fin σ.m) (Fin σ.k) ℝ) :=
  {p | ∀ᵐ ξ ∂σ.P, σ.A.mulVec (p.1.mulVec ξ) + p.2.mulVec ξ = σ.B.mulVec ξ ∧
      ∀ i, 0 ≤ (p.2.mulVec ξ) i}

/-- The optimal value of `SP^u` (p. 4): `inf Tr(MCᵀX)` over its feasible set, in `EReal`
(`⊤` if infeasible, `⊥` if unbounded below). -/
noncomputable def valSPu : EReal :=
  ⨅ p ∈ σ.feasSPu, ((σ.linObj p.1 : ℝ) : EReal)

/-- The feasible set of the linear program (2.3) (p. 5): `X ∈ ℝ^{n×k}`, `Λ ∈ ℝ^{m×l}` with
`AX + ΛW = B`, `Λh ≥ 0` and `Λ ≥ 0` (componentwise). -/
def feasLP23 : Set (Matrix (Fin σ.n) (Fin σ.k) ℝ × Matrix (Fin σ.m) (Fin σ.l) ℝ) :=
  {p | σ.A * p.1 + p.2 * σ.W = σ.B ∧ (∀ i, 0 ≤ (p.2.mulVec σ.h) i) ∧ ∀ i j, 0 ≤ p.2 i j}

/-- The optimal value of the linear program (2.3), in `EReal`. -/
noncomputable def valLP23 : EReal :=
  ⨅ p ∈ σ.feasLP23, ((σ.linObj p.1 : ℝ) : EReal)

/-- The objective `E(c(ξ)ᵀx(ξ)) = ∫ (Cξ)ᵀ x(ξ) dP` of `SP`, (2.2) and `SP^l`. -/
noncomputable def ruleObj (x : (Fin σ.k → ℝ) → (Fin σ.n → ℝ)) : ℝ :=
  ∫ ξ, (σ.C.mulVec ξ) ⬝ᵥ x ξ ∂σ.P

/-- The feasible set of the dual linear-decision-rule problem `SP^l` (p. 6): decision rules
`x ∈ 𝓛²_{k,n}`, `s ∈ 𝓛²_{k,m}` with `E([Ax(ξ) + s(ξ) − b(ξ)] ξᵀ) = 0` (an `m × k` matrix of
expectations) and `s(ξ) ≥ 0` `P`-almost surely. -/
def feasSPl : Set (((Fin σ.k → ℝ) → (Fin σ.n → ℝ)) × ((Fin σ.k → ℝ) → (Fin σ.m → ℝ))) :=
  {p | IsL2Rule σ.P p.1 ∧ IsL2Rule σ.P p.2 ∧
    (∀ i j, ∫ ξ, (σ.A.mulVec (p.1 ξ) + p.2 ξ - σ.B.mulVec ξ) i * ξ j ∂σ.P = 0) ∧
    ∀ᵐ ξ ∂σ.P, ∀ i, 0 ≤ p.2 ξ i}

/-- The optimal value of `SP^l`, in `EReal`. -/
noncomputable def valSPl : EReal :=
  ⨅ p ∈ σ.feasSPl, ((σ.ruleObj p.1 : ℝ) : EReal)

/-- The feasible set of problem (2.6) (p. 7): `X ∈ ℝ^{n×k}`, `S ∈ ℝ^{m×k}` with `AX + S = B`, such that
some `x ∈ 𝓛²_{k,n}` has `XM = E(x(ξ)ξᵀ)` and some `s ∈ 𝓛²_{k,m}` has `SM = E(s(ξ)ξᵀ)` and
`s(ξ) ≥ 0` `P`-almost surely. -/
def feasLP26 : Set (Matrix (Fin σ.n) (Fin σ.k) ℝ × Matrix (Fin σ.m) (Fin σ.k) ℝ) :=
  {p | σ.A * p.1 + p.2 = σ.B ∧
    (∃ x : (Fin σ.k → ℝ) → (Fin σ.n → ℝ), IsL2Rule σ.P x ∧
      p.1 * σ.M = fun i j => ∫ ξ, x ξ i * ξ j ∂σ.P) ∧
    (∃ s : (Fin σ.k → ℝ) → (Fin σ.m → ℝ), IsL2Rule σ.P s ∧
      p.2 * σ.M = (fun i j => ∫ ξ, s ξ i * ξ j ∂σ.P) ∧ ∀ᵐ ξ ∂σ.P, ∀ i, 0 ≤ s ξ i)}

/-- The optimal value of problem (2.6), in `EReal`. -/
noncomputable def valLP26 : EReal :=
  ⨅ p ∈ σ.feasLP26, ((σ.linObj p.1 : ℝ) : EReal)

/-- The `l × k` matrix `W − h e_1ᵀ` of Proposition 3 and (2.8). -/
def Wtilde : Matrix (Fin σ.l) (Fin σ.k) ℝ := σ.W - Matrix.vecMulVec σ.h (e1 σ.k)

/-- The feasible set of the linear program (2.8) (p. 8): `X ∈ ℝ^{n×k}`, `S ∈ ℝ^{m×k}` with
`AX + S = B` and `(W − h e_1ᵀ) M Sᵀ ≥ 0` (componentwise, an `l × m` matrix). -/
def feasLP28 : Set (Matrix (Fin σ.n) (Fin σ.k) ℝ × Matrix (Fin σ.m) (Fin σ.k) ℝ) :=
  {p | σ.A * p.1 + p.2 = σ.B ∧ ∀ i j, 0 ≤ (σ.Wtilde * σ.M * p.2ᵀ) i j}

/-- The optimal value of the linear program (2.8), in `EReal`. -/
noncomputable def valLP28 : EReal :=
  ⨅ p ∈ σ.feasLP28, ((σ.linObj p.1 : ℝ) : EReal)

/-- The cone `𝒦 := {z ∈ ℝ^k : (W − h e_1ᵀ) z ≥ 0}` of Proposition 3 (p. 7). -/
def coneK : Set (Fin σ.k → ℝ) := {z | ∀ i, 0 ≤ (σ.Wtilde.mulVec z) i}

/-- The cone `𝒦_P := {z ∈ ℝ^k : ∃ s ∈ 𝓛²_{k,1} with E(s(ξ)ξ) = z and s(ξ) ≥ 0 P-a.s.}` of
Proposition 3 (p. 7); `s` is a real-valued square-integrable Borel function. -/
def coneKP : Set (Fin σ.k → ℝ) :=
  {z | ∃ s : (Fin σ.k → ℝ) → ℝ, Measurable s ∧ MemLp s 2 σ.P ∧
    (∀ j, ∫ ξ, s ξ * ξ j ∂σ.P = z j) ∧ ∀ᵐ ξ ∂σ.P, 0 ≤ s ξ}

end Setting

end PrimalDualLDR.FixedRecourse


