-- Prove2me | Definitions.Def_MDPFinance_POMDPFinance_MeanVariance
-- name    : MDPFinance_POMDPFinance_MeanVariance
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T22:34:39.29003+00:00
-- url     : https://prove2.me/theorems/b4f43d14-61eb-4c05-a5d7-b23af0bf01d8
-- title:
--   The mean-variance auxiliary recursion and the (MV)/QP(b) problems under partial observation
-- statement:
--   Section 6.2 solves the partially-observed analogue of the dynamic Markowitz problem by the same
--   Lagrangian-embedding technique as the fully-observed case: minimize $\mathbb E^\pi_{x_0}[(X_N-b)^2]$
--   (problem $QP(b)$) over history-dependent strategies, for a well-chosen constant $b$.
--
--   The bond price is $S^0_n := \prod_{k=1}^n(1+i_k)$ (rates now non-stationary), and the key
--   backward recursion (6.7), in stages-remaining form ($k=0$ at the horizon), is
--   $$
--   d_0 \equiv 1, \qquad
--   d_{k+1}(\rho) = \bar d_k(\rho) - \ell_k(\rho)^\top C_k(\rho)^{-1}\ell_k(\rho),
--   $$
--   where $\bar d_k(\rho) := \int d_k(\Phi(\rho,z))\,d(\text{predictive}(\rho))(z)$,
--   $\ell_k(\rho) := \int d_k(\Phi(\rho,z))\,z\,d(\text{predictive}(\rho))(z)$, and
--   $C_k(\rho) := \int d_k(\Phi(\rho,z))\,zz^\top\,d(\text{predictive}(\rho))(z)$. The matrix inverse
--   used is Mathlib's total inverse (junk zero if singular); genuine invertibility is a hypothesis of
--   the theorems that use it (Assumption FM(iii), positive-definite return covariance), not of this
--   definition.
--
--   The first and second moments of terminal wealth under a strategy $\pi$, $\mathbb E^\pi_{x_0}
--   [X_N]$ and $\mathbb E^\pi_{x_0}[X_N^2]$, instantiate the shared value-function scaffold with
--   terminal payoff $x \mapsto x$ and $x \mapsto x^2$ respectively. Finally, $(MV)$'s feasible set
--   restricts to strategies meeting the mean constraint $\mathbb E^\pi_{x_0}[X_N] \ge \mu$, and the
--   **value of $(MV)$** is the infimum of $\mathrm{Var}^\pi_{x_0}[X_N] = \mathbb E^\pi_{x_0}[X_N^2] -
--   (\mathbb E^\pi_{x_0}[X_N])^2$ over that feasible set.
--
--   **Moderation note.** `MeanVarianceMarket` carries the rates ($1+i_n>0$) and the section's standing Assumption (FM) (p. 184): $\sup_y\mathbb E\|R(y)\|<\infty$, finite second moments, a coordinate with sign-definite mean for all $y$, and a positive definite covariance matrix for all $y$; without them Lemma 6.2.1 is false (e.g. $R\equiv 0$ gives $d_k\equiv 1$) and the matrix inverse in (6.7) is a default value. The variance of a strategy is `VarPi`, which is $\infty$ when the second moment is infinite: the draft's $\mathbb E[X_N^2]-(\mathbb E[X_N])^2$ in $[-\infty,\infty]$ is $\top-\top=\bot$ for such strategies, which would make the infimum $-\infty$.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 184-186, Eq. (6.7) and the problems (MV)/QP(b)

import Mathlib
import Definitions.Def_MDPFinance_POMDPFinance_Filter
import Definitions.Def_MDPFinance_POMDPFinance_HistPolicy

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace MDPFinance.POMDPFinance

variable {EY : Type*} [MeasurableSpace EY] {d : ℕ}

/-- The bond price `S^0_n := \prod_{k=1}^n (1+i_k)`, `S^0_0 := 1` (Bäuerle–Rieder, p. 61, PDF 75,
restated in this chunk's own namespace, matching `MDPFinance.TerminalWealth.S0` (chunk `04a`)). -/
noncomputable def S0 (i : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∏ k ∈ Finset.range n, (1 + i (k + 1))

/-- The backward recursion `(d_k)` of (6.7), indexed by stages-remaining `k` (`d_0 \equiv 1`,
matching the book's terminal `d_N(ρ) = 1` at `k = N-n = 0`; `d_{k+1}(ρ) := \bar d_k(ρ) -
ℓ_k(ρ)^\top C_k(ρ)^{-1} ℓ_k(ρ)` where `\bar d_k(ρ) := \int d_k(\Phi(ρ,z)) \,
d(\text{predictive }ρ)(z)`, `ℓ_k`/`C_k` below) (Bäuerle–Rieder, Lemma 6.2.1/Theorem 6.2.2, p.
185-186, PDF 198-199). `Matrix.inv` is Mathlib's total inverse (junk `0` if singular; genuinely
invertible under Assumption `FM`(iii), a hypothesis of the consuming theorems, not of this
definition). -/
noncomputable def dRem (M : FilterMarket EY d) (Fd : FilterOp M) : ℕ → Measure EY → ℝ
  | 0, _ => 1
  | (k + 1), ρ =>
      let dk : Measure EY → ℝ := dRem M Fd k
      let l : Fin d → ℝ := fun a => ∫ z, dk (Fd.Phi ρ z) * z a ∂(M.predictive ρ)
      let C : Matrix (Fin d) (Fin d) ℝ :=
        Matrix.of fun a b => ∫ z, dk (Fd.Phi ρ z) * z a * z b ∂(M.predictive ρ)
      (∫ z, dk (Fd.Phi ρ z) ∂(M.predictive ρ)) - dotProduct l (C⁻¹.mulVec l)

/-- `ℓ_k(ρ) := \int d_k(\Phi(ρ,z)) \, z \, d(\text{predictive }ρ)(z)` (Bäuerle–Rieder, Eq. (6.7),
p. 185, PDF 198), stated standalone (not only inlined inside `dRem`) since Theorem 6.2.2b/6.2.3b's
optimal portfolio formulas cite `ℓ_{n+1}(ρ)` directly. -/
noncomputable def lRem (M : FilterMarket EY d) (Fd : FilterOp M) (k : ℕ) (ρ : Measure EY) :
    Fin d → ℝ :=
  fun a => ∫ z, dRem M Fd k (Fd.Phi ρ z) * z a ∂(M.predictive ρ)

/-- `C_k(ρ) := \int d_k(\Phi(ρ,z)) \, zz^\top \, d(\text{predictive }ρ)(z)` (Bäuerle–Rieder, Eq.
(6.7), p. 185, PDF 198), stated standalone for the same reason as `lRem`. -/
noncomputable def CRem (M : FilterMarket EY d) (Fd : FilterOp M) (k : ℕ) (ρ : Measure EY) :
    Matrix (Fin d) (Fin d) ℝ :=
  Matrix.of fun a b => ∫ z, dRem M Fd k (Fd.Phi ρ z) * z a * z b ∂(M.predictive ρ)

/-- The dynamic mean-variance market of §6.2 (Bäuerle–Rieder, p. 184, PDF 197): non-stationary
rates `i_n` with `1+i_n > 0`, and the section's standing Assumption (FM): (i) `sup_y 𝔼‖R(y)‖ <
∞`, (ii) some coordinate `k` has `𝔼R_k(y) > 0` for all `y` or `< 0` for all `y`, (iii) the
covariance matrix of `R(y)` is positive definite for all `y` (which presupposes finite second
moments, `hmom2`). (iv) `x_0 S^0_N < μ` is a hypothesis of Theorem 6.2.3. -/
structure MeanVarianceMarket (M : FilterMarket EY d) where
  i : ℕ → ℝ
  hi_pos : ∀ n, 0 < 1 + i n
  hmom1 : ∃ K : ℝ≥0∞, K < ⊤ ∧ ∀ y, ∫⁻ z, ‖z‖ₑ ∂(M.law y) ≤ K
  hmom2 : ∀ y, ∫⁻ z, ‖z‖ₑ ^ 2 ∂(M.law y) < ⊤
  hmean : ∃ k : Fin d, (∀ y, 0 < ∫ z, z k ∂(M.law y)) ∨ (∀ y, ∫ z, z k ∂(M.law y) < 0)
  hcov : ∀ y, (Matrix.of fun j k : Fin d =>
    ∫ z, (z j - ∫ w, w j ∂(M.law y)) * (z k - ∫ w, w k ∂(M.law y)) ∂(M.law y)).PosDef

/-- The expected terminal wealth `𝔼^π_{x_0}[X_N]` of a (possibly history-dependent) strategy `π`
(Bäuerle–Rieder, p. 186-188, via `term := id` in `Vpi`). -/
noncomputable def EXN (M : FilterMarket EY d) (Fd : FilterOp M) (i : ℕ → ℝ) (π : HistPolicy d)
    (N : ℕ) (x0 : ℝ) : EReal :=
  Vpi M Fd i id π N 0 (fun _ => 0) x0 M.Q0

/-- The second moment `𝔼^π_{x_0}[X_N^2]` of a (possibly history-dependent) strategy `π`
(Bäuerle–Rieder, Theorem 6.2.2c). -/
noncomputable def EXN2 (M : FilterMarket EY d) (Fd : FilterOp M) (i : ℕ → ℝ) (π : HistPolicy d)
    (N : ℕ) (x0 : ℝ) : EReal :=
  Vpi M Fd i (fun x => x ^ 2) π N 0 (fun _ => 0) x0 M.Q0

/-- `\ΠN` restricted to the mean-constraint of `(MV)`: feasible strategies (Definition
`IsFeasiblePolicy` with the unconstrained `D ≡ Set.univ` of §6.2) whose expected terminal wealth
meets the target `μ` (Bäuerle–Rieder, p. 184, `(MV)`'s constraint `𝔼^π_{x_0}[X_N] \ge μ`). -/
def IsMVFeasible (M : FilterMarket EY d) (Fd : FilterOp M) (i : ℕ → ℝ) (N : ℕ) (x0 μ : ℝ)
    (π : HistPolicy d) : Prop :=
  IsFeasiblePolicy (fun _ => Set.univ) i x0 N π ∧ μ ≤ EXN M Fd i π N x0

/-- `\text{Var}^π_{x_0}[X_N] = 𝔼^π_{x_0}[X_N^2] - (𝔼^π_{x_0}[X_N])^2 ∈ [0,∞]`: `∞` when the second
moment is infinite (then `𝔼[X_N]` may be `±∞` too and the difference would be a default value),
otherwise the genuine difference. -/
noncomputable def VarPi (M : FilterMarket EY d) (Fd : FilterOp M) (i : ℕ → ℝ) (π : HistPolicy d)
    (N : ℕ) (x0 : ℝ) : EReal :=
  if EXN2 M Fd i π N x0 = ⊤ then ⊤ else EXN2 M Fd i π N x0 - (EXN M Fd i π N x0) ^ 2

/-- The **value of `(MV)`**: `\inf` of `\text{Var}^π_{x_0}[X_N]` over mean-feasible strategies
(Bäuerle–Rieder, p. 184, problem `(MV)`). -/
noncomputable def VarMV (M : FilterMarket EY d) (Fd : FilterOp M) (i : ℕ → ℝ) (N : ℕ)
    (x0 μ : ℝ) : EReal :=
  ⨅ π ∈ {π : HistPolicy d | IsMVFeasible M Fd i N x0 μ π}, VarPi M Fd i π N x0

end MDPFinance.POMDPFinance


