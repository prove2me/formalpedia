-- Prove2me | Definitions.Def_L0BnB_Reduced_Setup
-- name    : L0BnB_Reduced_Setup
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T23:13:17.148588+00:00
-- url     : https://prove2.me/theorems/7b1102ea-7c65-4f0a-87f5-89544d8d9a85
-- title:
--   The interval relaxation of the perspective formulation (3), the reduced problem (5) and the one-coordinate problem (36)
-- statement:
--   Let $X\in\mathbb R^{n\times p}$, $y\in\mathbb R^n$, regularization parameters $\lambda_0,\lambda_2>0$ and a Big-M bound $M>0$. Write $[p]=\{1,\dots,p\}$.
--
--   **Perspective formulation and its interval relaxation.** The perspective formulation $\mathrm{PR}(M)$ of $\ell_0\ell_2$-regularized least squares (problem (3)) is
--
--   $$
--   \min_{\beta,z,s}\ \tfrac12\|y-X\beta\|_2^2+\lambda_0\sum_{i\in[p]}z_i+\lambda_2\sum_{i\in[p]}s_i
--   \quad\text{s.t.}\quad \beta_i^2\le s_iz_i,\ \ -Mz_i\le\beta_i\le Mz_i,\ \ z_i\in\{0,1\},\ \ s_i\ge0,\quad i\in[p].
--   $$
--
--   Its **interval relaxation** replaces every $z_i\in\{0,1\}$ by $z_i\in[0,1]$. A triple $(\beta,z,s)\in(\mathbb R^p)^3$ is feasible for the relaxation when, for every $i$,
--   $$\beta_i^2\le s_iz_i,\qquad -Mz_i\le \beta_i\le Mz_i,\qquad 0\le z_i\le 1,\qquad s_i\ge 0,$$
--   which are the constraints (35b)–(35d). Its objective is $\tfrac12\|y-X\beta\|_2^2+\lambda_0\sum_i z_i+\lambda_2\sum_i s_i$. We consider the set of objective values at a fixed $\beta$ and the set of all objective values.
--
--   **The penalties and the reduced problem.** With $\mathcal B$ the reverse Huber penalty (4),
--   $$
--   \psi_1(b;\lambda_0,\lambda_2)=2\lambda_0\,\mathcal B\big(b\sqrt{\lambda_2/\lambda_0}\big),\qquad
--   \psi_2(b;\lambda_0,\lambda_2,M)=\Big(\frac{\lambda_0}{M}+\lambda_2M\Big)|b|,
--   $$
--   and $\psi(b;\lambda_0,\lambda_2,M)$ equals $\psi_1(b;\lambda_0,\lambda_2)$ if $\sqrt{\lambda_0/\lambda_2}\le M$ and $\psi_2(b;\lambda_0,\lambda_2,M)$ if $\sqrt{\lambda_0/\lambda_2}>M$. The reduced problem (5) is
--   $$
--   \min_{\beta\in\mathbb R^p}\ F(\beta):=\tfrac12\|y-X\beta\|_2^2+\sum_{i\in[p]}\psi(\beta_i;\lambda_0,\lambda_2,M)\quad\text{s.t.}\quad\|\beta\|_\infty\le M,
--   $$
--   and $V_{\mathrm{PR}(M)}$ denotes its optimal value, the infimum of $F$ over the box $\|\beta\|_\infty\le M$.
--
--   **The one-coordinate problem.** For $b\in\mathbb R$, $\omega(b;\lambda_0,\lambda_2,M)$ is the minimum of $\lambda_0z+\lambda_2s$ over the pairs $(z,s)$ with $b^2\le sz$, $-Mz\le b\le Mz$, $0\le z\le 1$, $s\ge0$; we record the set of these values. We also define $\hat z=\max\{b^2/s,\,|b|/M\}$ (with $b^2/s=0$ when $b=s=0$), and the objective of (36),
--   $$
--   \max\Big\{\lambda_0\frac{b^2}{s}+\lambda_2 s,\ \lambda_0\frac{|b|}{M}+\lambda_2 s\Big\},
--   $$
--   together with the set of its values over $s\ge b^2$.
--
--   These objects are the common vocabulary of Theorem 1 and the three steps of its proof.
--
--   **Formalization Note** Indices are `Fin p`; $\|y-X\beta\|_2^2$ is the explicit sum $\sum_r (y_r-(X\beta)_r)^2$ and $\|\beta\|_\infty\le M$ is $|\beta_i|\le M$ for all $i$. The rotated cone constraint is kept in the product form $\beta_i^2\le s_iz_i$, so no division occurs in the feasible set. $V_{\mathrm{PR}(M)}$ is a real `sInf`; the theorems that use it also state that the infimum is attained, so the junk value of `sInf` on an empty or unbounded set never enters. In $\hat z$ and (36), Lean's convention $b^2/0=0$ is exactly the paper's convention $\beta_i^2/s_i=0$ for $\beta_i=s_i=0$ (and $s=0$ with $b\ne0$ is excluded by $s\ge b^2$).
-- source:
--   Hazimeh, Mazumder, Saab, Sparse Regression at Scale: Branch-and-Bound rooted in First-Order Optimization, arXiv:2004.06152v2, pp. 5–6, (3), (5), Theorem 1; p. 28, Proof of Theorem 1, (35a)–(35d), (36)

import Mathlib
import Definitions.Def_L0BnB_Reduced_ReverseHuber

namespace L0BnB.Reduced

/-! Objects of Hazimeh, Mazumder, Saab, *Sparse Regression at Scale: Branch-and-Bound rooted in
First-Order Optimization*, arXiv:2004.06152v2: the perspective formulation (3) with its binaries
relaxed to `[0, 1]` (p. 5, p. 6, and (35b)–(35d), p. 28), the penalties `ψ, ψ₁, ψ₂` and the reduced
problem (5) of Theorem 1 (p. 6), and the one-coordinate problem `ω` and its reduction (36) (p. 28).

Conventions: `X : Matrix (Fin n) (Fin p) ℝ`, `y : Fin n → ℝ`, `β z s : Fin p → ℝ`; the paper's
`[p] = {1, …, p}` is `Fin p`; `‖y − Xβ‖₂²` is written as the explicit sum `∑ r, (y r − (X *ᵥ β) r)²` (`Matrix.mulVec X β`)
and `‖β‖_∞ ≤ M` as `∀ i, |β i| ≤ M`. -/

/-- `ψ₁(b; λ₀, λ₂) := 2λ₀ B(b √(λ₂/λ₀))` (Theorem 1, p. 6), with `B` the reverse Huber penalty (4). -/
noncomputable def psi1 (lam0 lam2 b : ℝ) : ℝ :=
  2 * lam0 * reverseHuber (b * Real.sqrt (lam2 / lam0))

/-- `ψ₂(b; λ₀, λ₂, M) := (λ₀/M + λ₂M)|b|` (Theorem 1, p. 6). -/
noncomputable def psi2 (lam0 lam2 M b : ℝ) : ℝ :=
  (lam0 / M + lam2 * M) * |b|

/-- `ψ(b; λ₀, λ₂, M)` equals `ψ₁(b; λ₀, λ₂)` if `√(λ₀/λ₂) ≤ M` and `ψ₂(b; λ₀, λ₂, M)` if
`√(λ₀/λ₂) > M` (Theorem 1, p. 6). -/
noncomputable def psi (lam0 lam2 M b : ℝ) : ℝ :=
  if Real.sqrt (lam0 / lam2) ≤ M then psi1 lam0 lam2 b else psi2 lam0 lam2 M b

/-- The least squares loss `½‖y − Xβ‖₂²`. -/
noncomputable def lsLoss {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ)
    (β : Fin p → ℝ) : ℝ :=
  (1 / 2) * ∑ r, (y r - Matrix.mulVec X β r) ^ 2

/-- The objective of (5): `F(β) := ½‖y − Xβ‖₂² + ∑_{i ∈ [p]} ψ(βᵢ; λ₀, λ₂, M)` (p. 6). -/
noncomputable def F {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ)
    (lam0 lam2 M : ℝ) (β : Fin p → ℝ) : ℝ :=
  lsLoss X y β + ∑ i, psi lam0 lam2 M (β i)

/-- The feasible set `‖β‖_∞ ≤ M` of (5), written coordinatewise. -/
def box (p : ℕ) (M : ℝ) : Set (Fin p → ℝ) := {β | ∀ i, |β i| ≤ M}

/-- `V_{PR(M)}`, the optimal objective value of (5) (p. 6): the infimum of `F` over `‖β‖_∞ ≤ M`. -/
noncomputable def VPR {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ)
    (lam0 lam2 M : ℝ) : ℝ :=
  sInf (F X y lam0 lam2 M '' box p M)

/-- The constraints (35b)–(35d) for one coordinate (p. 28), i.e. the constraints of the interval
relaxation of (3) for index `i` (pp. 5–6): `b² ≤ s z`, `−M z ≤ b ≤ M z`, `z ∈ [0, 1]`, `s ≥ 0`. -/
def CoordFeas (M b z s : ℝ) : Prop :=
  b ^ 2 ≤ s * z ∧ -M * z ≤ b ∧ b ≤ M * z ∧ 0 ≤ z ∧ z ≤ 1 ∧ 0 ≤ s

/-- Feasibility of `(β, z, s)` for the interval relaxation of the perspective formulation (3)
(pp. 5–6): every constraint of (3) for every `i ∈ [p]`, with `zᵢ ∈ {0, 1}` relaxed to `zᵢ ∈ [0, 1]`. -/
def PRFeas {p : ℕ} (M : ℝ) (β z s : Fin p → ℝ) : Prop :=
  ∀ i, CoordFeas M (β i) (z i) (s i)

/-- The objective of (3): `½‖y − Xβ‖₂² + λ₀ ∑_{i ∈ [p]} zᵢ + λ₂ ∑_{i ∈ [p]} sᵢ` (p. 5). -/
noncomputable def PRObj {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ)
    (lam0 lam2 : ℝ) (β z s : Fin p → ℝ) : ℝ :=
  lsLoss X y β + lam0 * ∑ i, z i + lam2 * ∑ i, s i

/-- The objective values of the interval relaxation of (3) at a fixed `β`:
`{½‖y − Xβ‖₂² + λ₀ ∑ zᵢ + λ₂ ∑ sᵢ : (β, z, s) feasible}`. -/
def PRValuesAt {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ)
    (lam0 lam2 M : ℝ) (β : Fin p → ℝ) : Set ℝ :=
  {v | ∃ z s : Fin p → ℝ, PRFeas M β z s ∧ v = PRObj X y lam0 lam2 β z s}

/-- All objective values of the interval relaxation of (3). -/
def PRValues {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ)
    (lam0 lam2 M : ℝ) : Set ℝ :=
  {v | ∃ β z s : Fin p → ℝ, PRFeas M β z s ∧ v = PRObj X y lam0 lam2 β z s}

/-- The values `λ₀ z + λ₂ s` over the one-coordinate feasible set (35b)–(35d); their minimum is
`ω(b; λ₀, λ₂, M)` (p. 28). -/
def omegaValues (lam0 lam2 M b : ℝ) : Set ℝ :=
  {v | ∃ z s : ℝ, CoordFeas M b z s ∧ v = lam0 * z + lam2 * s}

/-- `ẑ := max{b²/s, |b|/M}` (p. 28). Lean's `b² / 0 = 0` is the paper's convention
"for `βᵢ = sᵢ = 0` we define `βᵢ²/sᵢ = 0`". -/
noncomputable def zhat (M b s : ℝ) : ℝ :=
  max (b ^ 2 / s) (|b| / M)

/-- The objective of (36), p. 28: `max{λ₀ b²/s + λ₂ s, λ₀ |b|/M + λ₂ s}`. -/
noncomputable def obj36 (lam0 lam2 M b s : ℝ) : ℝ :=
  max (lam0 * (b ^ 2 / s) + lam2 * s) (lam0 * (|b| / M) + lam2 * s)

/-- The values of the objective of (36) over its feasible set `s ≥ b²` (p. 28). -/
def values36 (lam0 lam2 M b : ℝ) : Set ℝ :=
  {v | ∃ s : ℝ, b ^ 2 ≤ s ∧ v = obj36 lam0 lam2 M b s}

end L0BnB.Reduced


