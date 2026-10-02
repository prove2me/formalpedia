-- Prove2me | Definitions.Def_MDPFinance_MeanVariance_MVMarket
-- name    : MDPFinance_MeanVariance_MVMarket
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T22:05:46.063011+00:00
-- url     : https://prove2.me/theorems/63eb4bea-7379-43b5-a0b3-12fd455d335c
-- title:
--   The mean-variance financial market, (MV)/(MV=), the Lagrangian, and the auxiliary problems P(lambda)/QP(b)
-- statement:
--   State space $E:=\mathbb{R}$ (wealth), action space $A:=\mathbb{R}^d$ (amounts invested
--   in $d$ risky assets, no short-selling restriction), transition
--   $T_n(x,a,z) := (1+i_{n+1})(x+a\cdot z)$ (Bäuerle–Rieder, p. 117). Writing $X_N$ for the terminal
--   wealth reached from $x_0$ under a policy $\pi$, the **mean-variance problem**
--   $$\mathrm{(MV)}\qquad \mathrm{Var}_{x_0}^\pi[X_N] \to \min \text{ over admissible } \pi
--   \text{ with } \mathbb{E}_{x_0}^\pi[X_N]\ge\mu,$$
--   its equality-constrained variant (MV=) (with $\mathbb{E}_{x_0}^\pi[X_N]=\mu$), the Lagrangian
--   $L_{x_0}(\pi,\lambda) := \mathrm{Var}_{x_0}^\pi[X_N] + 2\lambda(\mu-\mathbb{E}_{x_0}^\pi[X_N])$,
--   saddle points of $L_{x_0}$, and the two auxiliary problems $P(\lambda)$ (minimize
--   $L_{x_0}(\cdot,\lambda)$) and $QP(b)$ (minimize $\mathbb{E}_{x_0}^\pi[(X_N-b)^2]$) are all
--   bundled here as predicates on the market data, matching the book's own sequence of named
--   optimization problems in §4.6.
--
--   **Formalization Note.** None of (MV), (MV=), $P(\lambda)$, $QP(b)$ is a numbered definition in
--   the book — each is introduced in prose as a displayed optimization problem — so this file pins
--   each one down as an explicit `Prop`-valued predicate (`IsOptimalMV`, `IsOptimalMVeq`,
--   `IsSaddlePoint`, `IsOptimalPLambda`, `IsOptimalQP`) rather than leaving any of them implicit, per
--   this chunk's pitfall about named-but-unnumbered problems.
--
--   **Formalization Note (moderation).** The model carries Section 4.6's standing Assumption (FM)
--   (finite second moments and nonzero means of the independent relative risks, positive definite
--   covariance matrices, $x_0S^0_N<\mu$), $x_0>0$ and positive bond factors. Admissible policies
--   are the measurable ones whose terminal wealth from the given state is square integrable, so
--   that the means and variances in (MV), (MV=), $P(\lambda)$, $QP(b)$ exist (for others the
--   Bochner integrals would return $0$).
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 117-120, PDF 131-134, model summary and unnumbered displays

import Mathlib

open MeasureTheory ProbabilityTheory

namespace MDPFinance.MeanVariance

/-- The non-stationary financial market underlying the mean-variance problem (Bäuerle–Rieder,
p. 117, PDF 131): state space `E := ℝ` (wealth), action space `A := ℝ^d`, `D_n(x) := A`,
transition `T_n(x,a,z) := (1+i_{n+1})(x+a\cdot z)`, no restriction on short-selling; the
section's standing Assumption (FM) (finite second moments and nonzero means of the independent
relative risks, positive definite covariance matrices, `x0 S⁰_N < μ`), initial wealth `x0 > 0` and
positive bond factors are fields. -/
structure MVMarket (Ω : Type*) [MeasurableSpace Ω] (d : ℕ) where
  measIP : Measure Ω
  isProb : IsProbabilityMeasure measIP
  N : ℕ
  i : ℕ → ℝ
  hi_pos : ∀ n, 1 ≤ n → n ≤ N → 0 < 1 + i n
  R : ℕ → Ω → (Fin d → ℝ)
  hR_meas : ∀ n, 1 ≤ n → n ≤ N → Measurable (R n)
  /-- The relative risks `R_1, …, R_N` are independent (Section 4.2's market). -/
  hR_indep : iIndepFun (fun n : Fin N => R (n.val + 1)) measIP
  /-- Assumption (FM)(i): `𝔼‖R_n‖ < ∞` (here with second moments, which the covariance matrix
  of (FM)(ii) presupposes) and `𝔼 R_n ≠ 0`. -/
  hR_L2 : ∀ n, 1 ≤ n → n ≤ N → ∀ k, MemLp (fun ω => R n ω k) 2 measIP
  hR_mean_ne : ∀ n, 1 ≤ n → n ≤ N → (fun k => ∫ ω, R n ω k ∂measIP) ≠ 0
  /-- Assumption (FM)(ii): the covariance matrix of `R_n` is positive definite. -/
  hCov_posdef : ∀ n, 1 ≤ n → n ≤ N →
    Matrix.PosDef (Matrix.of (fun j k =>
      ∫ ω, (R n ω j - ∫ ω', R n ω' j ∂measIP) * (R n ω k - ∫ ω', R n ω' k ∂measIP) ∂measIP))
  x0 : ℝ
  hx0 : 0 < x0
  μ : ℝ
  /-- Assumption (FM)(iii): `x0 S⁰_N < μ`. -/
  hμ : x0 * ∏ k ∈ Finset.range N, (1 + i (k + 1)) < μ

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

/-- The bond price `S⁰_n := ∏_{k=1}^n (1+i_k)`. -/
noncomputable def MVMarket.S0 (M : MVMarket Ω d) (n : ℕ) : ℝ :=
  ∏ k ∈ Finset.range n, (1 + M.i (k + 1))

/-- The terminal wealth `X_N` reached from state `x` at time `n`, under `π`, on path `ω`
(Bäuerle–Rieder's wealth recursion, restated). -/
noncomputable def MVMarket.terminalWealth (M : MVMarket Ω d) (π : ℕ → ℝ → (Fin d → ℝ)) :
    (k : ℕ) → (n : ℕ) → (x : ℝ) → (ω : Ω) → ℝ
  | 0, _, x, _ => x
  | (k + 1), n, x, ω =>
      M.terminalWealth π k (n + 1)
        ((1 + M.i (n + 1)) * (x + ∑ j, π n x j * M.R (n + 1) ω j)) ω

/-- A policy sequence `π : ℕ → ℝ → ℝ^d` is admissible over `[n,N)` from the state `x` if `π k` is
measurable for every `n ≤ k < N` (`D_n(x) = A`, no other constraint on the actions) and the
terminal wealth it produces from `(n,x)` is square integrable, so that the mean and the variance
of `X_N` the problems (MV), (MV=), `P(λ)`, `QP(b)` are stated with exist. -/
def MVMarket.IsAdmissibleFrom (M : MVMarket Ω d) (n : ℕ) (x : ℝ) (π : ℕ → ℝ → (Fin d → ℝ)) :
    Prop :=
  (∀ k, n ≤ k → k < M.N → Measurable (π k)) ∧
    MemLp (fun ω => M.terminalWealth π (M.N - n) n x ω) 2 M.measIP

/-- Admissibility of an `N`-stage policy from the initial wealth `x0`, `π ∈ F^N`. -/
def MVMarket.IsAdmissible (M : MVMarket Ω d) (n : ℕ) (π : ℕ → ℝ → (Fin d → ℝ)) : Prop :=
  M.IsAdmissibleFrom n M.x0 π

/-- `𝔼^π_{x_0}[X_N]`. -/
noncomputable def MVMarket.meanXN (M : MVMarket Ω d) (π : ℕ → ℝ → (Fin d → ℝ)) : ℝ :=
  ∫ ω, M.terminalWealth π M.N 0 M.x0 ω ∂M.measIP

/-- `𝔼^π_{x_0}[X_N^2]`. -/
noncomputable def MVMarket.meanXNsq (M : MVMarket Ω d) (π : ℕ → ℝ → (Fin d → ℝ)) : ℝ :=
  ∫ ω, (M.terminalWealth π M.N 0 M.x0 ω) ^ 2 ∂M.measIP

/-- `Var^π_{x_0}[X_N] := 𝔼^π_{x_0}[X_N^2] - (𝔼^π_{x_0}[X_N])^2`. -/
noncomputable def MVMarket.varXN (M : MVMarket Ω d) (π : ℕ → ℝ → (Fin d → ℝ)) : ℝ :=
  M.meanXNsq π - (M.meanXN π) ^ 2

/-- `π*` is optimal for `(MV)` (Bäuerle–Rieder, p. 117, PDF 131): `π* ∈ F^N`,
`𝔼^{π*}_{x_0}[X_N] ≥ μ`, and `Var^{π*}_{x_0}[X_N] ≤ Var^π_{x_0}[X_N]` for every admissible `π`
with `𝔼^π_{x_0}[X_N] ≥ μ`. -/
def MVMarket.IsOptimalMV (M : MVMarket Ω d) (πstar : ℕ → ℝ → (Fin d → ℝ)) : Prop :=
  M.IsAdmissible 0 πstar ∧ M.μ ≤ M.meanXN πstar ∧
    ∀ π, M.IsAdmissible 0 π → M.μ ≤ M.meanXN π → M.varXN πstar ≤ M.varXN π

/-- `π*` is optimal for `(MV=)` (Bäuerle–Rieder, p. 117, PDF 131): as `(MV)` but with the
equality constraint `𝔼^{π*}_{x_0}[X_N] = μ`. -/
def MVMarket.IsOptimalMVeq (M : MVMarket Ω d) (πstar : ℕ → ℝ → (Fin d → ℝ)) : Prop :=
  M.IsAdmissible 0 πstar ∧ M.meanXN πstar = M.μ ∧
    ∀ π, M.IsAdmissible 0 π → M.meanXN π = M.μ → M.varXN πstar ≤ M.varXN π

/-- The Lagrange function `L_{x_0}(π,λ) := Var^π_{x_0}[X_N] + 2λ(μ - 𝔼^π_{x_0}[X_N])`
(Bäuerle–Rieder, p. 119, PDF 133). -/
noncomputable def MVMarket.Lagrangian (M : MVMarket Ω d) (π : ℕ → ℝ → (Fin d → ℝ)) (lam : ℝ) :
    ℝ :=
  M.varXN π + 2 * lam * (M.μ - M.meanXN π)

/-- `(π^*,λ^*)` is a saddle-point of `L_{x_0}` (Bäuerle–Rieder, p. 119, PDF 133):
`sup_{λ≥0} L_{x_0}(π^*,λ) = L_{x_0}(π^*,λ^*) = inf_{π∈F^N} L_{x_0}(π,λ^*)`. -/
def MVMarket.IsSaddlePoint (M : MVMarket Ω d) (πstar : ℕ → ℝ → (Fin d → ℝ)) (lamstar : ℝ) :
    Prop :=
  M.IsAdmissible 0 πstar ∧ 0 ≤ lamstar ∧
    (∀ lam ≥ (0 : ℝ), M.Lagrangian πstar lam ≤ M.Lagrangian πstar lamstar) ∧
    (∀ π, M.IsAdmissible 0 π → M.Lagrangian πstar lamstar ≤ M.Lagrangian π lamstar)

/-- `π*` is optimal for `P(λ)` (Bäuerle–Rieder, p. 120, PDF 134): minimizes `L_{x_0}(\cdot,λ)`
over admissible `π`. -/
def MVMarket.IsOptimalPLambda (M : MVMarket Ω d) (lam : ℝ) (πstar : ℕ → ℝ → (Fin d → ℝ)) :
    Prop :=
  M.IsAdmissible 0 πstar ∧ ∀ π, M.IsAdmissible 0 π → M.Lagrangian πstar lam ≤ M.Lagrangian π lam

/-- `π*` is optimal for `QP(b)` (Bäuerle–Rieder, p. 120, PDF 134): minimizes
`𝔼^π_{x_0}[(X_N-b)^2]` over admissible `π`. -/
def MVMarket.IsOptimalQP (M : MVMarket Ω d) (b : ℝ) (πstar : ℕ → ℝ → (Fin d → ℝ)) : Prop :=
  M.IsAdmissible 0 πstar ∧
    ∀ π, M.IsAdmissible 0 π →
      ∫ ω, (M.terminalWealth πstar M.N 0 M.x0 ω - b) ^ 2 ∂M.measIP ≤
        ∫ ω, (M.terminalWealth π M.N 0 M.x0 ω - b) ^ 2 ∂M.measIP

end MDPFinance.MeanVariance


