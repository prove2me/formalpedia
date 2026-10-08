-- Prove2me | Definitions.Def_PrimalDualLDR_Multistage_Problems
-- name    : PrimalDualLDR_Multistage_Problems
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T08:42:23.108564+00:00
-- url     : https://prove2.me/theorems/c505e6bb-7bc9-4f75-ba8d-64bf6c7d6abe
-- title:
--   The problems 𝓜𝒮𝒫^u, (4.2), 𝓜𝒮𝒫^l, (4.6) and their optimal values (pp. 19–21)
-- statement:
--   The four optimization problems of §4 and their optimal values, for a multistage setting with data $A_{ts}, B_t, C_t, W, h, M_t$ and moment matrix $M = \mathbb E(\xi\xi^\top)$. All share the objective $\sum_{t=1}^T \mathrm{Tr}(P_tMP_t^\top C_t^\top X_t)$ or, for decision rules, $\mathbb E\big(\sum_t c_t(\xi^t)^\top x_t(\xi^t)\big)$.
--
--   1. **$\mathcal{MSP}^u$** (p. 19), the primal linear-decision-rule problem: minimize $\sum_t \mathrm{Tr}(P_tMP_t^\top C_t^\top X_t)$ over $X_t \in \mathbb R^{n_t\times k^t}$, $S_t \in \mathbb R^{m_t\times k^t}$ subject to, $\mathbb P$-a.s. for all $t$,
--   $$\sum_{s=1}^T A_{ts}X_sP_sM_tP_t\xi + S_tP_t\xi = B_tP_t\xi, \qquad S_tP_t\xi \ge 0.$$
--   2. **(4.2)** (p. 19): minimize the same objective over $X_t \in \mathbb R^{n_t\times k^t}$, $\Lambda_t \in \mathbb R^{m_t\times l}$ subject to, for all $t$,
--   $$\sum_{s=1}^T A_{ts}X_sP_sM_tP_t + \Lambda_tW = B_tP_t, \qquad \Lambda_th \ge 0, \qquad \Lambda_t \ge 0.$$
--   3. **$\mathcal{MSP}^l$** (p. 20), the dual linear-decision-rule problem: minimize $\mathbb E\big(\sum_t c_t(\xi^t)^\top x_t(\xi^t)\big)$ over $x_t \in \mathcal L^2_{k^t,n_t}$, $s_t \in \mathcal L^2_{k^t,m_t}$ subject to, for all $t$,
--   $$\mathbb E\Big(\Big[\sum_{s=1}^T A_{ts}x_s(\xi^s) + s_t(\xi^t) - b_t(\xi^t)\Big][P_t\xi]^\top\Big) = 0, \qquad s_t(\xi^t) \ge 0 \ \ \mathbb P\text{-a.s.}$$
--   4. **(4.6)** (p. 21): minimize $\sum_t \mathrm{Tr}(P_tMP_t^\top C_t^\top X_t)$ over $X_t \in \mathbb R^{n_t\times k^t}$, $S_t \in \mathbb R^{m_t\times k^t}$ subject to, for all $t$,
--   $$\sum_{s=1}^T A_{ts}X_sP_sN_tP_t + S_tP_t = B_tP_t, \qquad (W - he_1^\top)MP_t^\top S_t^\top \ge 0,$$
--   where $N_t := MP_t^\top(P_tMP_t^\top)^{-1}$.
--
--   The optimal value of each problem is the infimum of its objective over its feasible set, in the extended reals: $+\infty$ if the problem is infeasible and $-\infty$ if it is unbounded below. The module also names the moment matrix $\mathbb E(x(\xi^t)\xi^\top)$ of a stage-$t$ rule (the right-hand side of (4.3)) and the $t$-th equality constraint of $\mathcal{MSP}^l$.
--
--   $\mathcal{MSP}^u$ is a conservative (upper) and $\mathcal{MSP}^l$ a progressive (lower) approximation of $\mathcal{MSP}$; Theorem 3 identifies them with the linear programs (4.2) and (4.6).
--
--   **Formalization Note** The page prints the equality constraint of $\mathcal{MSP}^l$ with the whole bracket $[A_{ts}x_s(\xi^s) + s_t(\xi^t) - b_t(\xi^t)]$ inside $\sum_{s=1}^T$, which would count $s_t - b_t$ $T$ times; (4.7) on p. 21 shows that the sum covers only $A_{ts}x_s(\xi^s)$, and that corrected reading is formalized. Componentwise orders are `∀ i j, 0 ≤ ·`. $(\cdot)^{-1}$ is Mathlib's `Matrix.inv`, which is $0$ on a singular matrix; under the standing assumptions $P_tMP_t^\top$ is positive definite. Expectations are entrywise Bochner integrals; under the standing assumptions $\xi$ is bounded almost surely, so every integrand involving $\mathcal L^2$ rules is integrable.
-- source:
--   Kuhn, Wiesemann, Georghiou, Primal and dual linear decision rules in stochastic and robust optimization, Optimization Online 2009/02/2218, p. 19 (𝓜𝒮𝒫^u, (4.2)), p. 20 (𝓜𝒮𝒫^l, (4.3)), p. 21 ((4.6), N_t)

import Mathlib
import Definitions.Def_PrimalDualLDR_Multistage_Basic
import Definitions.Def_PrimalDualLDR_Multistage_Setting

open MeasureTheory Matrix

namespace PrimalDualLDR.Multistage

namespace Setting

variable (σ : Setting)

/-- A family of stage-wise coefficient matrices `X_t ∈ ℝ^{n_t × k^t}`, `t ∈ 𝕋`. -/
abbrev XFam : Type := (t : Fin σ.T) → Matrix (Fin (σ.n t)) (Fin (σ.kb t)) ℝ

/-- A family of stage-wise slack matrices `S_t ∈ ℝ^{m_t × k^t}`, `t ∈ 𝕋`. -/
abbrev SFam : Type := (t : Fin σ.T) → Matrix (Fin (σ.m t)) (Fin (σ.kb t)) ℝ

/-- A family of non-anticipative primal decision rules `x_t : ℝ^{k^t} → ℝ^{n_t}`, `t ∈ 𝕋`. -/
abbrev XRules : Type := (t : Fin σ.T) → (Fin (σ.kb t) → ℝ) → (Fin (σ.n t) → ℝ)

/-- A family of non-anticipative slack rules `s_t : ℝ^{k^t} → ℝ^{m_t}`, `t ∈ 𝕋`. -/
abbrev SRules : Type := (t : Fin σ.T) → (Fin (σ.kb t) → ℝ) → (Fin (σ.m t) → ℝ)

/-- The objective `Σ_t Tr(P_t M P_tᵀ C_tᵀ X_t)` shared by `𝓜𝒮𝒫^u`, (4.2) and (4.6). -/
noncomputable def linObj (X : σ.XFam) : ℝ :=
  ∑ t, Matrix.trace (σ.Pt t * σ.M * (σ.Pt t)ᵀ * (σ.C t)ᵀ * X t)

/-- The objective `𝔼(Σ_t c_t(ξ^t)ᵀ x_t(ξ^t))` of `𝓜𝒮𝒫`, (4.1) and `𝓜𝒮𝒫^l`, with
`c_t(ξ^t) = C_t P_t ξ`. -/
noncomputable def ruleObj (x : σ.XRules) : ℝ :=
  ∫ ξ, ∑ t, ((σ.C t * σ.Pt t).mulVec ξ) ⬝ᵥ x t (σ.tr t ξ) ∂σ.P

/-- The feasible set of the primal linear-decision-rule problem `𝓜𝒮𝒫^u` (p. 19): matrices
`X_t ∈ ℝ^{n_t × k^t}`, `S_t ∈ ℝ^{m_t × k^t}` with
`Σ_s A_ts X_s P_s M_t P_t ξ + S_t P_t ξ = B_t P_t ξ` and `S_t P_t ξ ≥ 0` `P`-a.s. for every `t`. -/
def feasMSPu : Set (σ.XFam × σ.SFam) :=
  {p | ∀ t : Fin σ.T, ∀ᵐ ξ ∂σ.P,
    (∑ s, σ.A t s * p.1 s * σ.Pt s * σ.Mt t * σ.Pt t).mulVec ξ + (p.2 t * σ.Pt t).mulVec ξ =
        (σ.B t * σ.Pt t).mulVec ξ ∧
      ∀ i, 0 ≤ (p.2 t * σ.Pt t).mulVec ξ i}

/-- The optimal value of `𝓜𝒮𝒫^u`, in `EReal` (`⊤` if infeasible, `⊥` if unbounded below). -/
noncomputable def valMSPu : EReal :=
  ⨅ p ∈ σ.feasMSPu, ((σ.linObj p.1 : ℝ) : EReal)

/-- The feasible set of the linear program (4.2) (p. 19): matrices `X_t ∈ ℝ^{n_t × k^t}`,
`Λ_t ∈ ℝ^{m_t × l}` with `Σ_s A_ts X_s P_s M_t P_t + Λ_t W = B_t P_t`, `Λ_t h ≥ 0` and `Λ_t ≥ 0`
(componentwise) for every `t`. -/
def feasLP42 : Set (σ.XFam × ((t : Fin σ.T) → Matrix (Fin (σ.m t)) (Fin σ.l) ℝ)) :=
  {p | ∀ t : Fin σ.T,
    ∑ s, σ.A t s * p.1 s * σ.Pt s * σ.Mt t * σ.Pt t + p.2 t * σ.W = σ.B t * σ.Pt t ∧
      (∀ i, 0 ≤ (p.2 t).mulVec σ.h i) ∧ ∀ i j, 0 ≤ p.2 t i j}

/-- The optimal value of the linear program (4.2), in `EReal`. -/
noncomputable def valLP42 : EReal :=
  ⨅ p ∈ σ.feasLP42, ((σ.linObj p.1 : ℝ) : EReal)

/-- The `t`-th equality constraint of `𝓜𝒮𝒫^l` (p. 20), in the corrected reading
`𝔼([Σ_s A_ts x_s(ξ^s) + s_t(ξ^t) − b_t(ξ^t)] [P_t ξ]ᵀ) = 0` (an `m_t × k^t` matrix of expectations;
the sum runs over the terms `A_ts x_s(ξ^s)` only). -/
def eqMSPl (t : Fin σ.T) (x : σ.XRules) (s : (Fin (σ.kb t) → ℝ) → (Fin (σ.m t) → ℝ)) : Prop :=
  ∀ i j, ∫ ξ, ((∑ r, (σ.A t r).mulVec (x r (σ.tr r ξ))) + s (σ.tr t ξ) -
      (σ.B t * σ.Pt t).mulVec ξ) i * σ.tr t ξ j ∂σ.P = 0

/-- The feasible set of the dual linear-decision-rule problem `𝓜𝒮𝒫^l` (p. 20): non-anticipative rules
`x_t ∈ 𝓛²_{k^t,n_t}`, `s_t ∈ 𝓛²_{k^t,m_t}` satisfying the equality constraints `eqMSPl` and
`s_t(ξ^t) ≥ 0` `P`-a.s. for every `t`. -/
def feasMSPl : Set (σ.XRules × σ.SRules) :=
  {p | (∀ t, σ.IsL2RuleAt t (p.1 t)) ∧ (∀ t, σ.IsL2RuleAt t (p.2 t)) ∧
    ∀ t : Fin σ.T, σ.eqMSPl t p.1 (p.2 t) ∧ ∀ᵐ ξ ∂σ.P, ∀ i, 0 ≤ p.2 t (σ.tr t ξ) i}

/-- The optimal value of `𝓜𝒮𝒫^l`, in `EReal`. -/
noncomputable def valMSPl : EReal :=
  ⨅ p ∈ σ.feasMSPl, ((σ.ruleObj p.1 : ℝ) : EReal)

/-- The moment matrix `𝔼(x(ξ^t) ξᵀ) ∈ ℝ^{d × k}` of a stage-`t` rule `x : ℝ^{k^t} → ℝ^d`, the right-hand
side of (4.3) (p. 20). -/
noncomputable def moment (t : Fin σ.T) {d : ℕ} (x : (Fin (σ.kb t) → ℝ) → (Fin d → ℝ)) :
    Matrix (Fin d) (Fin σ.k) ℝ :=
  fun i j => ∫ ξ, x (σ.tr t ξ) i * ξ j ∂σ.P

/-- The matrix `N_t := M P_tᵀ (P_t M P_tᵀ)⁻¹ ∈ ℝ^{k × k^t}` of (4.6) (p. 21). `⁻¹` is Mathlib's
`Matrix.inv`, which returns `0` on a singular matrix; under the standing assumptions `P_t M P_tᵀ` is
positive definite. -/
noncomputable def N (t : Fin σ.T) : Matrix (Fin σ.k) (Fin (σ.kb t)) ℝ :=
  σ.M * (σ.Pt t)ᵀ * (σ.Pt t * σ.M * (σ.Pt t)ᵀ)⁻¹

/-- The `l × k` matrix `W − h e_1ᵀ` of (4.6). -/
def Wtilde : Matrix (Fin σ.l) (Fin σ.k) ℝ := σ.W - Matrix.vecMulVec σ.h (PrimalDualLDR.FixedRecourse.e1 σ.k)

/-- The feasible set of the linear program (4.6) (p. 21): matrices `X_t ∈ ℝ^{n_t × k^t}`,
`S_t ∈ ℝ^{m_t × k^t}` with `Σ_s A_ts X_s P_s N_t P_t + S_t P_t = B_t P_t` and
`(W − h e_1ᵀ) M P_tᵀ S_tᵀ ≥ 0` (componentwise, an `l × m_t` matrix) for every `t`. -/
def feasLP46 : Set (σ.XFam × σ.SFam) :=
  {p | ∀ t : Fin σ.T,
    ∑ s, σ.A t s * p.1 s * σ.Pt s * σ.N t * σ.Pt t + p.2 t * σ.Pt t = σ.B t * σ.Pt t ∧
      ∀ i j, 0 ≤ (σ.Wtilde * σ.M * (σ.Pt t)ᵀ * (p.2 t)ᵀ) i j}

/-- The optimal value of the linear program (4.6), in `EReal`. -/
noncomputable def valLP46 : EReal :=
  ⨅ p ∈ σ.feasLP46, ((σ.linObj p.1 : ℝ) : EReal)

end Setting

end PrimalDualLDR.Multistage


