-- Prove2me | Definitions.Def_ComonoNetPricing_DebtEquity_Model
-- name    : ComonoNetPricing_DebtEquity_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T04:15:52.161982+00:00
-- url     : https://prove2.me/theorems/7c3ed1a5-5196-4c1e-a445-be60c963fefd
-- title:
--   (3)–(4), Definition 3.4, Assumption 3.5, Theorem 3.6, Corollary A.4, pp. 11–13, 35 — Δ, δ, Δₖ, δₖ, thresholds q*, fictitious default algorithm
-- statement:
--   The paper-specific constructions of Banerjee and Feinstein on top of the Rogers–Veraart network ($n$ banks, relative liabilities $\Pi$, total liabilities $\bar p$, recovery rates $\alpha_x, \alpha_L$, greatest clearing wealth $V(x)$).
--
--   **Piecewise linear maps (3)–(4).** For a set of defaulting banks with indicator $z \in \{0,1\}^n$,
--   $$\Delta(z) = \big(I - (I - (1-\alpha_L)\operatorname{diag}(z))\,\Pi^\top \operatorname{diag}(z)\big)^{-1}\big(I - (1-\alpha_x)\operatorname{diag}(z)\big),$$
--   $$\delta(z) = \big(I - (I - (1-\alpha_L)\operatorname{diag}(z))\,\Pi^\top \operatorname{diag}(z)\big)^{-1}\big[I - (I - (1-\alpha_L)\operatorname{diag}(z))\,\Pi^\top\big]\bar p.$$
--
--   **The matrices of Theorem 3.6.** $\Delta_0 = I$, $\delta_0 = (I - \Pi^\top)\bar p$, and for $k = 1,\dots,n$, $\Delta_k = \Delta\big(\sum_{j=1}^k e_j\big)$, $\delta_k = \delta\big(\sum_{j=1}^k e_j\big)$: the default set is the first $k$ banks.
--
--   **Thresholds (Definition 3.4, Assumption 3.5).** For a comonotonic endowment map $f : \mathbb R_+ \to \mathbb R^n_+$,
--   $$q^*_i = \inf\{q \ge 0 \mid V_i(f(q)) \ge 0\} \in [0,\infty],$$
--   the lowest factor level at which bank $i$ is solvent, extended by $q^*_0 = \infty$ and $q^*_{n+1} = 0$. For a random factor $q$, the event $\{q \in [q^*_{k+1}, q^*_k)\}$ is the $k$-th interval of Theorem 3.6.
--
--   **Fictitious default algorithm (Corollary A.4).** $V^{(0)} = x + \Pi^\top\bar p - \bar p$, $z^{(0)} = 0$, and for $k \ge 1$, $z^{(k)} = \mathbb I_{\{V^{(k-1)}<0\}}$, $\Lambda = \operatorname{diag}(z^{(k)})$ and
--   $$V^{(k)} = \big(I - (I - (1-\alpha_L)\Lambda)\,\Pi^\top\Lambda\big)^{-1}\big[(I - (1-\alpha_x)\Lambda)x + (I - (1-\alpha_L)\Lambda)\Pi^\top\bar p - \bar p\big].$$
--
--   **Formalization Note** A default set is a `Finset (Fin n)` and $\operatorname{diag}(z)$ is the diagonal 0–1 matrix of that set; bank `j : Fin n` is the paper's bank $j+1$, so the paper's first $k$ banks are those with `j.val < k`. The thresholds are valued in $[0,\infty]$ (`ℝ≥0∞`): the paper writes $q^* \in \mathbb R^n_+$, but the infimum of the empty set (a bank that is never solvent) is $\infty$, consistent with $q^*_0 = \infty$; a real-valued `sInf` would return $0$ there. The inverse is Mathlib's `Matrix.inv`, which returns $0$ on a singular matrix; nonsingularity of every such matrix under Assumption 2.1 is part of the Corollary A.4 milestone. The algorithm uses the closed form (second line) of step (iv); the printed first line drops $\alpha_L$ before $\Pi^\top\Lambda V^{(k)}$ in the default bracket.
-- source:
--   Banerjee & Feinstein, Pricing of debt and equity in a financial network with comonotonic endowments, arXiv:1810.01372v5, pp. 11–13, 35, (3)–(4) p. 11, Definition 3.4 and Assumption 3.5 p. 12, Theorem 3.6 (Δₖ, δₖ) p. 13, Corollary A.4 p. 35

import Mathlib
import Definitions.Def_ComonoNetPricing_DebtEquity_Network

namespace ComonoNetPricing.DebtEquity

open Matrix MeasureTheory

namespace Network

variable {n : ℕ} (N : Network n)

/-- `diag(z)` for the indicator vector `z ∈ {0, 1}^n` of a set `S` of banks: the diagonal
matrix with `1` at the banks of `S` and `0` elsewhere. -/
noncomputable def dg (S : Finset (Fin n)) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.diagonal (fun i => if i ∈ S then (1 : ℝ) else 0)

/-- The matrix `I − (I − (1 − α_L) diag(z)) Π⊤ diag(z)` inverted in (3)–(4), p. 11, and in
Corollary A.4 (iv), p. 35. -/
noncomputable def Mmat (S : Finset (Fin n)) : Matrix (Fin n) (Fin n) ℝ :=
  1 - (1 - (1 - N.aL) • dg S) * N.piMᵀ * dg S

/-- `Δ(z) := (I − (I − (1 − α_L) diag(z)) Π⊤ diag(z))⁻¹ (I − (1 − α_x) diag(z))`, (3), p. 11. -/
noncomputable def DeltaM (S : Finset (Fin n)) : Matrix (Fin n) (Fin n) ℝ :=
  (N.Mmat S)⁻¹ * (1 - (1 - N.ax) • dg S)

/-- `δ(z) := (I − (I − (1 − α_L) diag(z)) Π⊤ diag(z))⁻¹ [I − (I − (1 − α_L) diag(z)) Π⊤] p̄`,
(4), p. 11. -/
noncomputable def deltaV (S : Finset (Fin n)) : Fin n → ℝ :=
  (N.Mmat S)⁻¹ *ᵥ ((1 - (1 - (1 - N.aL) • dg S) * N.piMᵀ) *ᵥ N.pbar)

/-- The set `{1, …, k}` of the paper's first `k` banks, i.e. the banks `j : Fin n` with
`j.val < k`; its indicator is `∑_{j=1}^k e_j` (Theorem 3.6, p. 13). -/
def firstBanks (k : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun j : Fin n => j.val < k)

/-- `Δ_k` of Theorem 3.6, p. 13: `Δ(∑_{j=1}^k e_j)` for `k = 1, …, n` and `I` for `k = 0`. -/
noncomputable def DeltaK (k : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  if k = 0 then 1 else N.DeltaM (firstBanks k)

/-- `δ_k` of Theorem 3.6, p. 13: `δ(∑_{j=1}^k e_j)` for `k = 1, …, n` and `(I − Π⊤) p̄` for
`k = 0`. -/
noncomputable def deltaK (k : ℕ) : Fin n → ℝ :=
  if k = 0 then (1 - N.piMᵀ) *ᵥ N.pbar else N.deltaV (firstBanks k)

/-- The solvency threshold `q*_i = inf {q ≥ 0 | V_i(f(q)) ≥ 0}` of Definition 3.4, p. 12, for
the comonotonic endowment map `f`. It takes values in `[0, ∞]`: the infimum of the empty set
(bank `i` is never solvent) is `∞`. -/
noncomputable def qstar (f : ℝ → Fin n → ℝ) (i : Fin n) : ENNReal :=
  sInf (ENNReal.ofReal '' {s : ℝ | 0 ≤ s ∧ 0 ≤ N.clearingWealth (f s) i})

/-- The thresholds extended as in Assumption 3.5, p. 12: `q*_0 = ∞`, `q*_k` for
`k = 1, …, n` (the paper's bank `k`, which is `⟨k - 1⟩ : Fin n`), and `q*_{n+1} = 0` (also used
for every `k > n`). -/
noncomputable def qExt (f : ℝ → Fin n → ℝ) (k : ℕ) : ENNReal :=
  if hk : k = 0 then ⊤ else if h : k ≤ n then N.qstar f ⟨k - 1, by omega⟩ else 0

/-- The event `{q ∈ [q*_{k+1}, q*_k)}` of Theorem 3.6, p. 13. -/
def Ik {Ω : Type*} (f : ℝ → Fin n → ℝ) (q : Ω → ℝ) (k : ℕ) : Set Ω :=
  {ω | N.qExt f (k + 1) ≤ ENNReal.ofReal (q ω) ∧ ENNReal.ofReal (q ω) < N.qExt f k}

/-- The wealth iterates `V^{(k)}` of the fictitious default algorithm, Corollary A.4, p. 35:
`V^{(0)} = x + Π⊤ p̄ − p̄` and, with `Λ = diag(z^{(k+1)})` for the default set
`z^{(k+1)} = 1{V^{(k)} < 0}`,
`V^{(k+1)} = (I − (I − (1 − α_L)Λ) Π⊤ Λ)⁻¹ [(I − (1 − α_x)Λ) x + (I − (1 − α_L)Λ) Π⊤ p̄ − p̄]`
(the closed form, second line of step (iv)). -/
noncomputable def fdaV (x : Fin n → ℝ) : ℕ → Fin n → ℝ
  | 0 => x + N.piMᵀ *ᵥ N.pbar - N.pbar
  | k + 1 =>
    (N.Mmat (Finset.univ.filter (fun i => fdaV x k i < 0)))⁻¹ *ᵥ
      ((1 - (1 - N.ax) • dg (Finset.univ.filter (fun i => fdaV x k i < 0))) *ᵥ x
        + ((1 - (1 - N.aL) • dg (Finset.univ.filter (fun i => fdaV x k i < 0))) * N.piMᵀ) *ᵥ N.pbar
        - N.pbar)

/-- The default sets `z^{(k)}` of the fictitious default algorithm, Corollary A.4, p. 35:
`z^{(0)} = 0` (no bank) and `z^{(k+1)} = 1{V^{(k)} < 0}`. -/
noncomputable def fdaZ (x : Fin n → ℝ) : ℕ → Finset (Fin n)
  | 0 => ∅
  | k + 1 => Finset.univ.filter (fun i => N.fdaV x k i < 0)

end Network

end ComonoNetPricing.DebtEquity


