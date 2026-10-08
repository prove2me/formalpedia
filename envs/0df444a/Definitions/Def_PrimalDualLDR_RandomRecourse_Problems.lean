-- Prove2me | Definitions.Def_PrimalDualLDR_RandomRecourse_Problems
-- name    : PrimalDualLDR_RandomRecourse_Problems
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T08:41:54.881356+00:00
-- url     : https://prove2.me/theorems/07e171c0-3952-4346-8e44-c39daa21c8aa
-- title:
--   The primal linear decision rule problem 𝒮𝒫^u (§3.1, p. 11), the SDP (3.14) (p. 13), their optimal values, and H_μ (p. 12)
-- statement:
--   Fix the data and notation of the random-recourse setting ($\mathbb P$, $C$, $B$ with rows $b_\mu^\top$, $A_\mu$, $W_\ell$, $e_1$, $M=\mathbb E(\xi\xi^\top)$). Let $\mathbb S$ be the symmetric $k\times k$ matrices.
--
--   1. **Objective.** For $X\in\mathbb R^{n\times k}$ both problems minimize $\operatorname{Tr}(MC^\top X)$.
--
--   2. **$\mathcal{SP}^u$ (§3.1, p. 11).** Restricting $\mathcal{SP}$ to linear decisions $x(\xi)=X\xi$ and quadratic slacks $s_\mu(\xi)=\xi^\top S_\mu\xi$ gives
--   $$
--   \begin{aligned}
--   \text{minimize}\quad & \operatorname{Tr}(MC^\top X)\\
--   \text{subject to}\quad & X\in\mathbb R^{n\times k},\ S=(S_1,\dots,S_m)\in\mathbb S^m,\\
--   & \xi^\top A_\mu X\xi+\xi^\top S_\mu\xi=b_\mu^\top\xi,\quad \xi^\top S_\mu\xi\ge0\quad \mathbb P\text{-a.s.},\ \mu=1,\dots,m .
--   \end{aligned}
--   $$
--
--   3. **The SDP (3.14) (p. 13).**
--   $$
--   \begin{aligned}
--   \text{minimize}\quad & \operatorname{Tr}(MC^\top X)\\
--   \text{subject to}\quad & X\in\mathbb R^{n\times k},\ S=(S_1,\dots,S_m)\in\mathbb S^m,\ \Lambda\in\mathbb R^{m\times l},\\
--   & \tfrac12\big(A_\mu X+X^\top A_\mu^\top\big)+S_\mu=\tfrac12\big(e_1b_\mu^\top+b_\mu e_1^\top\big)\quad \forall\mu,\\
--   & S_\mu-\textstyle\sum_{\ell=1}^l\Lambda_{\mu\ell}W_\ell\succeq0\quad\forall\mu,\qquad \Lambda\ge0 .
--   \end{aligned}
--   $$
--   Here $\succeq0$ is positive semidefiniteness and $\Lambda\ge0$ is componentwise.
--
--   4. **Optimal values.** $\operatorname{val}\mathcal{SP}^u$ and $\operatorname{val}(3.14)$ are the infima of the objective over the respective feasible sets, taken in the extended reals: $+\infty$ for an empty feasible set, $-\infty$ if the objective is unbounded below.
--
--   5. **The matrix $H_\mu$ (§3.2, p. 12).** For $X$ and a matrix $S_\mu$,
--   $$
--   H_\mu:=\tfrac12\big(A_\mu X+X^\top A_\mu^\top-e_1b_\mu^\top-b_\mu e_1^\top\big)+S_\mu .
--   $$
--
--   $\mathcal{SP}^u$ is a semi-infinite program with finitely many variables; (3.14) is a finite semidefinite program. Theorem 2 of the paper compares the two.
--
--   **Formalization Note** $\mathbb S^m$ is encoded as a family `S : Fin m → Matrix (Fin k) (Fin k) ℝ` with every `S μ` symmetric, imposed in both feasible sets. The optimal values are `EReal` infima of the real objective over the feasible set. The name $\mathcal{SP}^u$ is the paper's reuse of its §2 name for a different problem (quadratic slacks); it is `FeasSPu`/`valSPu` here.
-- source:
--   Kuhn, Wiesemann, Georghiou, Primal and dual linear decision rules in stochastic and robust optimization, Optimization Online 2009/02/2218, p. 11 (SP^u, §3.1), p. 12 (H_μ), p. 13 ((3.14))

import Mathlib
import Definitions.Def_PrimalDualLDR_RandomRecourse_Setting

namespace PrimalDualLDR.RandomRecourse

open MeasureTheory Matrix

namespace Setting

variable (σ : Setting)

/-- The common objective `Tr(M Cᵀ X)` of `𝒮𝒫^u` and (3.14) (pp. 11, 13). -/
noncomputable def objective (X : Matrix (Fin σ.n) (Fin σ.k) ℝ) : ℝ :=
  Matrix.trace (σ.M * σ.Cᵀ * X)

/-- **§3.2, p. 12.** `H_μ := ½(A_μX + XᵀA_μᵀ − e_1b_μᵀ − b_μe_1ᵀ) + S_μ`, for a decision `X` and a
slack matrix `S_μ`. -/
noncomputable def H (X : Matrix (Fin σ.n) (Fin σ.k) ℝ) (Sμ : Matrix (Fin σ.k) (Fin σ.k) ℝ) (μ : Fin σ.m) :
    Matrix (Fin σ.k) (Fin σ.k) ℝ :=
  (1 / 2 : ℝ) • (σ.A μ * X + Xᵀ * (σ.A μ)ᵀ - vecMulVec σ.e1 (σ.B μ) - vecMulVec (σ.B μ) σ.e1) + Sμ

/-- **Feasible set of `𝒮𝒫^u` with random recourse, §3.1 p. 11.** `X ∈ ℝ^{n×k}` and
`S = (S_1, …, S_m) ∈ 𝕊^m` (each `S_μ` symmetric) such that, for every `μ`, `P`-almost surely,
`ξᵀA_μXξ + ξᵀS_μξ = b_μᵀξ` and `ξᵀS_μξ ≥ 0`. -/
def FeasSPu (X : Matrix (Fin σ.n) (Fin σ.k) ℝ) (S : Fin σ.m → Matrix (Fin σ.k) (Fin σ.k) ℝ) :
    Prop :=
  (∀ μ, (S μ).IsSymm) ∧
    ∀ μ : Fin σ.m, ∀ᵐ ξ ∂σ.P,
      ξ ⬝ᵥ ((σ.A μ * X) *ᵥ ξ) + ξ ⬝ᵥ (S μ *ᵥ ξ) = σ.B μ ⬝ᵥ ξ ∧ 0 ≤ ξ ⬝ᵥ (S μ *ᵥ ξ)

/-- **Feasible set of the SDP (3.14), p. 13.** `X ∈ ℝ^{n×k}`, `S = (S_1, …, S_m) ∈ 𝕊^m` and
`Λ ∈ ℝ^{m×l}` with, for every `μ`,
`½(A_μX + XᵀA_μᵀ) + S_μ = ½(e_1b_μᵀ + b_μe_1ᵀ)` and `S_μ − Σ_ℓ Λ_{μℓ} W_ℓ ⪰ 0`, and `Λ ≥ 0`
componentwise. -/
def Feas314 (X : Matrix (Fin σ.n) (Fin σ.k) ℝ) (S : Fin σ.m → Matrix (Fin σ.k) (Fin σ.k) ℝ)
    (Λ : Matrix (Fin σ.m) (Fin σ.l) ℝ) : Prop :=
  (∀ μ, (S μ).IsSymm) ∧
    (∀ μ, (1 / 2 : ℝ) • (σ.A μ * X + Xᵀ * (σ.A μ)ᵀ) + S μ =
      (1 / 2 : ℝ) • (vecMulVec σ.e1 (σ.B μ) + vecMulVec (σ.B μ) σ.e1)) ∧
    (∀ μ, (S μ - ∑ ℓ : Fin σ.l, Λ μ ℓ • σ.W ℓ).PosSemidef) ∧
    ∀ μ ℓ, 0 ≤ Λ μ ℓ

/-- Optimal value of `𝒮𝒫^u`: the infimum of `Tr(MCᵀX)` over its feasible set, in `EReal`
(`⊤` if infeasible, `⊥` if unbounded below). -/
noncomputable def valSPu : EReal :=
  ⨅ (p : Matrix (Fin σ.n) (Fin σ.k) ℝ × (Fin σ.m → Matrix (Fin σ.k) (Fin σ.k) ℝ))
    (_ : σ.FeasSPu p.1 p.2), ((σ.objective p.1 : ℝ) : EReal)

/-- Optimal value of the SDP (3.14): the infimum of `Tr(MCᵀX)` over its feasible set, in `EReal`
(`⊤` if infeasible, `⊥` if unbounded below). -/
noncomputable def valSDP314 : EReal :=
  ⨅ (p : Matrix (Fin σ.n) (Fin σ.k) ℝ × (Fin σ.m → Matrix (Fin σ.k) (Fin σ.k) ℝ) ×
      Matrix (Fin σ.m) (Fin σ.l) ℝ)
    (_ : σ.Feas314 p.1 p.2.1 p.2.2), ((σ.objective p.1 : ℝ) : EReal)

end Setting

end PrimalDualLDR.RandomRecourse


