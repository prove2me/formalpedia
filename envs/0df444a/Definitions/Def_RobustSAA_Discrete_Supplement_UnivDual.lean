-- Prove2me | Definitions.Def_RobustSAA_Discrete_Supplement_UnivDual
-- name    : RobustSAA_Discrete_Supplement_UnivDual
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T19:39:49.020919+00:00
-- url     : https://prove2.me/theorems/2283f825-b0f3-4a3c-9aa5-67fc68361ccb
-- title:
--   §5.2, (30)–(31) — univariate worst case on $\mathcal P(\Xi)$, the cells $(\xi^{(i-1)},\xi^{(i)}]$ and the dual programs
-- statement:
--   Let $\Xi\subseteq\mathbb R$ be closed, $\xi^{(1)}\le\dots\le\xi^{(N)}$ the sorted data, $\xi^{(0)}=\underline\xi$ and $\xi^{(N+1)}=\overline\xi$ the (possibly infinite) support bounds.
--
--   1. $\mathcal P(\Xi)$ is represented by laws on $\mathbb R$ giving no mass to $\mathbb R\setminus\Xi$; the KS, Kuiper, CvM, Watson and AD regions (7) are restricted to $\mathcal P(\Xi)$.
--   2. $\mathbb E_G[f(\xi)]$ is the integral when $f$ is $G$-integrable and $+\infty$ otherwise, and $C(x;\mathcal G)=\sup_{G\in\mathcal G}\mathbb E_G[c(x;\xi)]$.
--   3. The cells of (30), for $i=1,\dots,N+1$: $\Xi\cap(-\infty,\xi^{(1)}]$, $\Xi\cap(\xi^{(i-1)},\xi^{(i)}]$ for $2\le i\le N$, and $\Xi\cap(\xi^{(N)},\infty)$. Repeated data values give empty cells.
--   4. The objective values $b^\top r+c_{N+1}$ of the dual program (30) for cone data $(A,b,K)$: $-r\in K^*$, $c\in\mathbb R^{N+1}$, $(A^\top r)_i=c_i-c_{i+1}$ for $i\le N$, and $c_i\ge c(x;\xi)$ for every $\xi$ in the $i$-th cell, i.e. $c_i\ge\sup$ of the cost over that cell.
--   5. The generalized-moment region of (11), p. 10: $\mathbb E_{F_0}[\varphi(\xi)]<\infty$ and $|\mathbb E_{F_0}[\varphi(\xi)]-\hat\mu|\le Q_{M_N}(\alpha_2)$ with $\hat\mu=\frac1N\sum_i\varphi(\xi^i)$, and the objective values $b^\top r+c_{N+1}+(\hat\mu+Q_M)t-(\hat\mu-Q_M)s$ of (31) with $t,s\ge0$ and $c_i\ge c(x;\xi)-(t-s)\varphi(\xi)$ on the $i$-th cell.
--
--   **Formalization Note** The first cell is closed at the lower end, so that a finite lower support endpoint, which a law in $\mathcal P(\Xi)$ may charge, belongs to a cell; the page writes $(\xi^{(0)},\xi^{(1)}]$ (see Theorem 11). The expectation convention is that of the published `RobustSAA.Convergence.expect`.
-- source:
--   Bertsimas, Gupta, Kallus, Robust Sample Average Approximation, arXiv:1408.4445v3, §3.2 p. 9, (11) p. 10, §5.2 pp. 17–18, (30)–(31) p. 18

import Mathlib
import Definitions.Def_RobustSAA_Univariate_Setting
import Definitions.Def_RobustSAA_Discrete_Supplement_UnivStat

namespace RobustSAA.Discrete.Supplement

open MeasureTheory RobustSAA.Univariate
open scoped BigOperators ENNReal

/-! Univariate objects of §3.2 and §5.2 (pp. 9–10, 17–18) on a closed support `Ξ ⊆ ℝ`. -/

/-- `F₀ ∈ 𝒫(Ξ)`: a probability law on `ℝ` giving no mass outside `Ξ`. -/
def SupportedOn (Ξ : Set ℝ) (F₀ : ProbabilityMeasure ℝ) : Prop :=
  (F₀ : Measure ℝ) Ξᶜ = 0

/-- Expectation `E_G[f(ξ)]` in `EReal`: the integral when `f` is `G`-integrable and `+∞` otherwise
(the convention of the published `RobustSAA.Convergence.expect`). -/
noncomputable def expectR (G : ProbabilityMeasure ℝ) (f : ℝ → ℝ) : EReal := by
  classical
  exact if Integrable f (G : Measure ℝ) then ((∫ ξ, f ξ ∂(G : Measure ℝ) : ℝ) : EReal) else ⊤

/-- Worst-case expectation (4): `C(x; 𝒢) = sup_{G ∈ 𝒢} E_G[c(x; ξ)]` with `f = c(x; ·)`. -/
noncomputable def worstCaseR (𝒢 : Set (ProbabilityMeasure ℝ)) (f : ℝ → ℝ) : EReal :=
  ⨆ G ∈ 𝒢, expectR G f

/-- The cells of the dual constraints (30)/(31) for `k = 0, …, N` (the paper's `i = k + 1`):
the points of `Ξ` in `(ξ^(k), ξ^(k+1)]` with `ξ^(0) = ξ̲`, `ξ^(N+1) = ξ̄`. The first cell is
closed at the lower end (`Ξ ∩ (−∞, ξ^(1)]`, so it contains a finite lower support endpoint) and
the last cell is `Ξ ∩ (ξ^(N), ∞)`. Repeated sample values give empty cells. -/
noncomputable def cell {N : ℕ} (Ξ : Set ℝ) (s : Fin N → ℝ) (k : Fin (N + 1)) : Set ℝ :=
  {ξ | ξ ∈ Ξ ∧ (∀ h : 0 < (k : ℕ), ord s ⟨(k : ℕ) - 1, by omega⟩ < ξ) ∧
    (∀ h : (k : ℕ) < N, ξ ≤ ord s ⟨k, h⟩)}

/-- Objective values of the dual program (30) of Theorem 11 for cone data `(A, b, K)`:
`bᵀr + c_{N+1}` over `r` with `−r ∈ K*` and `c ∈ ℝ^{N+1}` with `(Aᵀr)ᵢ = cᵢ − c_{i+1}`
(`i = 1, …, N`) and `cᵢ ≥ c(x; ξ)` for every `ξ` in the `i`-th cell (so `cᵢ ≥ sup` of the cost
over the cell; the constraint is void on an empty cell). Index `k : Fin (N+1)` is `i = k + 1`. -/
def univDualValues {ι : Type*} [Fintype ι] {N : ℕ} (A : Matrix ι (Fin N) ℝ) (b : ι → ℝ)
    (K : Set (ι → ℝ)) (Ξ : Set ℝ) (f : ℝ → ℝ) (s : Fin N → ℝ) : Set ℝ :=
  {v | ∃ (r : ι → ℝ) (c : Fin (N + 1) → ℝ), (fun i => -r i) ∈ dualCone K ∧
    (∀ i : Fin N, (A.transpose.mulVec r) i = c i.castSucc - c i.succ) ∧
    (∀ k : Fin (N + 1), ∀ ξ ∈ cell Ξ s k, f ξ ≤ c k) ∧
    v = (∑ j, b j * r j) + c (Fin.last N)}

/-- The sample mean `μ̂ = (1/N) Σᵢ φ(ξⁱ)` (p. 10). -/
noncomputable def phiHat {N : ℕ} (φ : ℝ → ℝ) (s : Fin N → ℝ) : ℝ :=
  (1 / (N : ℝ)) * ∑ i, φ (s i)

/-- The generalized-moment part of the region (11), p. 10: `E_{F₀}[φ(ξ)] < ∞` and
`|E_{F₀}[φ(ξ)] − μ̂| ≤ Q_{M_N}(α₂)`. -/
noncomputable def momentRegion {N : ℕ} (φ : ℝ → ℝ) (QM : ℝ) (s : Fin N → ℝ) :
    Set (ProbabilityMeasure ℝ) :=
  {F₀ | ∫⁻ ξ, ENNReal.ofReal (φ ξ) ∂(F₀ : Measure ℝ) < ⊤ ∧
    |(∫ ξ, φ ξ ∂(F₀ : Measure ℝ)) - phiHat φ s| ≤ QM}

/-- Objective values of the dual program (31) of Theorem 12 for cone data `(A, b, K)`:
`bᵀr + c_{N+1} + (μ̂ + Q_M) t − (μ̂ − Q_M) s'` over `−r ∈ K*`, `t ≥ 0`, `s' ≥ 0`,
`c ∈ ℝ^{N+1}` with `(Aᵀr)ᵢ = cᵢ − c_{i+1}` and `cᵢ ≥ c(x; ξ) − (t − s')φ(ξ)` on the `i`-th
cell. -/
def momentDualValues {ι : Type*} [Fintype ι] {N : ℕ} (A : Matrix ι (Fin N) ℝ) (b : ι → ℝ)
    (K : Set (ι → ℝ)) (Ξ : Set ℝ) (f φ : ℝ → ℝ) (QM : ℝ) (s : Fin N → ℝ) : Set ℝ :=
  {v | ∃ (r : ι → ℝ) (t s' : ℝ) (c : Fin (N + 1) → ℝ), (fun i => -r i) ∈ dualCone K ∧
    0 ≤ t ∧ 0 ≤ s' ∧
    (∀ i : Fin N, (A.transpose.mulVec r) i = c i.castSucc - c i.succ) ∧
    (∀ k : Fin (N + 1), ∀ ξ ∈ cell Ξ s k, f ξ - (t - s') * φ ξ ≤ c k) ∧
    v = (∑ j, b j * r j) + c (Fin.last N) + (phiHat φ s + QM) * t -
      (phiHat φ s - QM) * s'}

/-- The KS confidence region (7) on `𝒫(Ξ)`: `{F₀ ∈ 𝒫(Ξ) : D_N(F₀) ≤ Q}`. -/
noncomputable def ksRegionOn (Ξ : Set ℝ) {N : ℕ} (Q : ℝ) (s : Fin N → ℝ) :
    Set (ProbabilityMeasure ℝ) :=
  {F₀ | SupportedOn Ξ F₀ ∧ ksStat F₀ s ≤ Q}

/-- The Kuiper confidence region (7) on `𝒫(Ξ)`. -/
noncomputable def kuiperRegionOn (Ξ : Set ℝ) {N : ℕ} (Q : ℝ) (s : Fin N → ℝ) :
    Set (ProbabilityMeasure ℝ) :=
  {F₀ | SupportedOn Ξ F₀ ∧ kuiperStat F₀ s ≤ Q}

/-- The CvM confidence region (7) on `𝒫(Ξ)`. -/
noncomputable def cvmRegionOn (Ξ : Set ℝ) {N : ℕ} (Q : ℝ) (s : Fin N → ℝ) :
    Set (ProbabilityMeasure ℝ) :=
  {F₀ | SupportedOn Ξ F₀ ∧ cvmStat F₀ s ≤ Q}

/-- The Watson confidence region (7) on `𝒫(Ξ)`. -/
noncomputable def watsonRegionOn (Ξ : Set ℝ) {N : ℕ} (Q : ℝ) (s : Fin N → ℝ) :
    Set (ProbabilityMeasure ℝ) :=
  {F₀ | SupportedOn Ξ F₀ ∧ watsonStat F₀ s ≤ Q}

/-- The AD confidence region (7) on `𝒫(Ξ)`. -/
noncomputable def adRegionOn (Ξ : Set ℝ) {N : ℕ} (Q : ℝ) (s : Fin N → ℝ) :
    Set (ProbabilityMeasure ℝ) :=
  {F₀ | SupportedOn Ξ F₀ ∧ adStat F₀ s ≤ ENNReal.ofReal Q}

end RobustSAA.Discrete.Supplement


