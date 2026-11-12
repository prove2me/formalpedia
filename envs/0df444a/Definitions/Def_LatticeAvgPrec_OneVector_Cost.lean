-- Prove2me | Definitions.Def_LatticeAvgPrec_OneVector_Cost
-- name    : LatticeAvgPrec_OneVector_Cost
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T06:49:02.336854+00:00
-- url     : https://prove2.me/theorems/1e3b315f-17c8-4a37-b990-c61bd6058c2e
-- title:
--   Subpolynomial factors, available exponent $\omega$, single-vector oracle (Def. 3.2)
-- statement:
--   **Subpolynomial factor.** Following p.4 ("$\widetilde O$ suppresses subpolynomial factors in the dimension and precision parameters"), a function $g(x,y)$ of a dimension $x$ and a precision $y$ is subpolynomial if for every $\varepsilon>0$ there is $C$ with $g(x,y)\le C(x+y+2)^{\varepsilon}$ for all $x,y$. Every $\widetilde O(f)$ of the mission is $g\cdot f$ with such a $g$ fixed before the input.
--
--   **Available exponent** (pp.4, 9). $\omega$ is available if a coin-free program of the logarithmic-cost RAM multiplies two order-$n$ integer matrices with entries of bitlength at most $b$ within bit cost $g_0(n,b)\,n^{\omega}b$, $g_0$ subpolynomial, input and output included ($n,b\ge1$).
--
--   **Definition 3.2** (p.12, single-vector oracle with approximation exponent $c_0$ and cost bound $\mathsf T$). $\mathsf T(k,h)$ is nondecreasing in both arguments; on every nonsingular $A\in\mathbb Z^{k\times k}$ every halting run returns
--   $$0\ne v\in A\mathbb Z^k,\qquad \|v\|_2\le 2^{c_0k}\lambda_1(A\mathbb Z^k);$$
--   and when $h\ge k$, $\|A\|_2\le2^h$ and $\|A^{-1}\|_2\le2$, the run is Las Vegas within expected bit cost $\mathsf T(k,h)$, input and output included.
--
--   The file also names the output guarantee of Theorem 3.3 for an HNF input $H$ of order $n$ with $\mathcal D=\log_2\det H$: $0\ne v\in\Lambda(H)$, $\|v\|_2\le 2^{cn}\lambda_1(\Lambda(H))$ and $\|v\|_2\le 2^{cn}2^{\mathcal D/n}$.
--
--   **Formalization Note** Programs, runs, bit cost and Las Vegas expectations are those of the published definitions `TimeSpaceMA_RAM` and `SoftmaxAttnFD_Machine` (cost $+\infty$ on a non-halting coin tape, so a finite expected cost forces halting with probability one). The paper's $2^{O(k)}$ is $2^{c_0k}$; $h$ and $\mathsf T$ take natural-number arguments.
-- source:
--   yang zhou, Mingsheng Wang, Zhedong Wang, Lattice Reduction at Average Precision, STOC 2027 submission #1574 (October 2026), §1.1.1 p.4 (Õ, ω, Las Vegas); §2 p.9 (bit operations, ω); Definition 3.2 p.12; Theorem 3.3 p.12

import Definitions.Def_SoftmaxAttnFD_Machine
import Definitions.Def_LatticeAvgPrec_OneVector_Conditioning
import Definitions.Def_LatticeAvgPrec_OneVector_NormalForms
open Matrix

namespace LatticeAvgPrec.OneVector

/-- A subpolynomial factor in a dimension `x` and a precision `y` (p.4, the convention behind `Õ`):
for every `ε > 0` there is `C` with `g x y ≤ C (x + y + 2)^ε` for all `x, y`. -/
def IsSubpoly (g : ℕ → ℕ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ x y : ℕ, g x y ≤ C * ((x : ℝ) + y + 2) ^ ε

/-- `ω` is an available matrix-multiplication exponent (pp.4, 9): a coin-free program of the
published logarithmic-cost RAM multiplies two order-`n` integer matrices with entries of bitlength
at most `b` within bit cost `g₀(n, b) · n^ω · b`, `g₀` subpolynomial, input and output included
(input `matCode X ++ matCode Y` from cell `0`, output `matCode (X * Y)` at cell `0`). -/
def MatMulAvailable (ω : ℝ) : Prop :=
  ∃ (M : TimeSpaceMA.Program) (g₀ : ℕ → ℕ → ℝ), IsSubpoly g₀ ∧
    ∀ (n b : ℕ) (X Y : Matrix (Fin n) (Fin n) ℤ), 1 ≤ n → 1 ≤ b →
      (∀ i j, bits (X i j) ≤ b) → (∀ i j, bits (Y i j) ≤ b) →
      SoftmaxAttnFD.DeterministicWithin M (TimeSpaceMA.memOf (matCode X ++ matCode Y))
        (fun mem => memHolds mem (matCode (X * Y))) (g₀ n b * (n : ℝ) ^ ω * b)

/-- Correct answer of the single-vector oracle with approximation exponent `c₀`
(Definition 3.2, p.12): the memory holds the code of `v` with `0 ≠ v ∈ AZ^k` and
`‖v‖₂ ≤ 2^{c₀ k} λ₁(AZ^k)`. -/
def OracleOut (c₀ : ℝ) {k : ℕ} (A : Matrix (Fin k) (Fin k) ℤ) (mem : ℕ → ℕ) : Prop :=
  ∃ v : Fin k → ℤ, memHolds mem (vecCode v) ∧ v ≠ 0 ∧ v ∈ lat A ∧
    ivNorm v ≤ (2 : ℝ) ^ (c₀ * k) * lam (lat A) 1

/-- Definition 3.2 (p.12): `R` is a single-vector oracle with approximation exponent `c₀` and
nondecreasing cost bound `T`: on every nonsingular integer `A` every halting run returns a correct
vector, and when `h ≥ k`, `‖A‖₂ ≤ 2^h`, `‖A⁻¹‖₂ ≤ 2`, the run is Las Vegas within expected bit cost
`T(k, h)`, input and output included. -/
def IsSingleVectorOracle (c₀ : ℝ) (R : TimeSpaceMA.Program) (T : ℕ → ℕ → ℝ) : Prop :=
  (∀ k k' h h' : ℕ, k ≤ k' → h ≤ h' → T k h ≤ T k' h') ∧
  (∀ (k : ℕ) (A : Matrix (Fin k) (Fin k) ℤ), 1 ≤ k → A.det ≠ 0 →
    ∀ τ, SoftmaxAttnFD.cost R (TimeSpaceMA.memOf (matCode A)) τ < ⊤ →
      OracleOut c₀ A (SoftmaxAttnFD.final R (TimeSpaceMA.memOf (matCode A)) τ)) ∧
  (∀ (k h : ℕ) (A : Matrix (Fin k) (Fin k) ℤ), 1 ≤ k → A.det ≠ 0 → k ≤ h →
    specNorm (rmat A) ≤ (2 : ℝ) ^ h → specNorm (rmat A)⁻¹ ≤ 2 →
    SoftmaxAttnFD.LasVegasWithin R (TimeSpaceMA.memOf (matCode A)) (OracleOut c₀ A) (T k h))

/-- The output guarantee of Theorem 3.3 / Corollary 3.4 for an HNF input `H` of order `n` with
`D = log₂ det H`: `0 ≠ v ∈ Λ(H)`, `‖v‖₂ ≤ 2^{cn} λ₁(Λ(H))` and `‖v‖₂ ≤ 2^{cn} 2^{D/n}`. -/
def HNFVecGood (c : ℝ) {n : ℕ} (H : Matrix (Fin n) (Fin n) ℤ) (v : Fin n → ℤ) : Prop :=
  v ≠ 0 ∧ v ∈ lat H ∧ ivNorm v ≤ (2 : ℝ) ^ (c * n) * lam (lat H) 1 ∧
    ivNorm v ≤ (2 : ℝ) ^ (c * n) * (2 : ℝ) ^ (Real.logb 2 (H.det : ℝ) / n)

end LatticeAvgPrec.OneVector


