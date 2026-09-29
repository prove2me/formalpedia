-- Prove2me | Definitions.Def_RobustSDP_Structured_Model
-- name    : RobustSDP_Structured_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T14:00:49.662098+00:00
-- url     : https://prove2.me/theorems/29ec01fb-1a05-4ee2-ba0f-913067ae70bd
-- title:
--   Structured linear-fractional perturbation model: the LFR (5), the robust feasible set (2), the scaling set (11) and the LMI of Theorem 3.2 (corrected)
-- statement:
--   This file fixes the objects of the structured robust semidefinite program of El Ghaoui, Oustry and Lebret (§2 and §3.2).
--
--   Let $m, n, p, q$ be natural numbers and $x \in \mathbb{R}^m$ the decision variable.
--
--   1. **Affine matrix maps.** Given coefficient matrices $A_0, A_1, \dots, A_m$ of a common size, the affine map is
--   $$A(x) = A_0 + \sum_{i=1}^{m} x_i A_i .$$
--   It is used for $F(x) = F_0 + \sum_i x_i F_i$ with $F_i \in \mathbb{R}^{n\times n}$ (Eq. (1)) and for $R(x) = R_0 + \sum_i x_i R_i$ with $R_i \in \mathbb{R}^{q\times n}$ (§2.2).
--
--   2. **Linear-fractional representation (5).** For $L \in \mathbb{R}^{n\times p}$, $D \in \mathbb{R}^{q\times p}$ and a perturbation $\Delta \in \mathbb{R}^{p\times q}$,
--   $$\mathbf{F}(x,\Delta) = F(x) + L\Delta(I - D\Delta)^{-1}R(x) + R(x)^T(I - \Delta^T D^T)^{-1}\Delta^T L^T .$$
--
--   3. **Robust feasible set (2).** For an arbitrary linear subspace $\mathcal{D} \subseteq \mathbb{R}^{p\times q}$ and a level $\rho$,
--   $$\mathcal{X}_\rho = \bigl\{x \in \mathbb{R}^m \;:\; \text{for every } \Delta \in \mathcal{D},\ \|\Delta\| \le \rho,\ \det(I - D\Delta) \ne 0 \text{ and } \mathbf{F}(x,\Delta) \succeq 0\bigr\},$$
--   where $\|\Delta\|$ is the largest singular value of $\Delta$ and $X \succeq 0$ means that $X$ is symmetric positive semidefinite. The condition $\det(I - D\Delta) \neq 0$ is the paper's "$\mathbf{F}(x,\Delta)$ is well defined".
--
--   4. **The scaling set $\mathcal{B}$ of $\mathcal{D}$ (11), corrected.** The set of triples
--   $$\mathcal{B} = \bigl\{(S,T,G) \in \mathbb{R}^{p\times p}\times\mathbb{R}^{q\times q}\times\mathbb{R}^{p\times q} \;:\; S\Delta = \Delta T,\ G\Delta^T = -\Delta G^T \text{ for every } \Delta \in \mathcal{D}\bigr\}.$$
--   It is a linear subspace; it always contains $(0,0,0)$, and the sign conditions $S \succ 0$, $T \succ 0$ are imposed separately wherever $\mathcal{B}$ is used.
--
--   5. **The LMI of Theorem 3.2, corrected.** For $(S,T,G)$ and $\rho$, the $(n+q)\times(n+q)$ block matrix
--   $$\begin{bmatrix} F(x) - LSL^T & R(x)^T - LSD^T + LG \\ R(x) - DSL^T + G^T L^T & \rho^{-2}T - DSD^T + DG + G^T D^T\end{bmatrix}.$$
--   At $\rho = 1$, with constant $F$ and $R$, this is the matrix (13) of Lemma 3.2.
--
--   6. **Block concatenations (§5.8).** For matrices $L_i \in \mathbb{R}^{n\times r_i}$ and $R_i \in \mathbb{R}^{r_i\times n}$, $i = 1,\dots,m$, the matrices $L = [L_1\ \cdots\ L_m] \in \mathbb{R}^{n\times(r_1+\cdots+r_m)}$ and $R = [R_1; \dots; R_m] \in \mathbb{R}^{(r_1+\cdots+r_m)\times n}$.
--
--   These objects are shared by every statement of the mission: the robust feasible set is the set the robust SDP (4) optimizes over, and the scaling set together with the block matrix define the SDP whose feasible points are shown to be robustly feasible.
--
--   **Correction of (11) and (13).** As printed, (11) takes $G \in \mathbb{R}^{q\times p}$ with $G\Delta = -\Delta^T G^T$, and (13) contains the products $LG$, $DSL$ and $DG$, which are undefined for $L \in \mathbb{R}^{n\times p}$, $D \in \mathbb{R}^{q\times p}$. (13) as printed is dimensionally inconsistent; we state the condition the proof yields, which coincides with the printed one when $G$ is square and skew-symmetric and $\mathcal{D}$ consists of symmetric matrices (the case used in Theorem 5.6).
--
--   **Formalization Note** The coefficient list is indexed by `Fin (m + 1)`, with `A 0` the constant term and `A (i+1)` the coefficient of the 0-based coordinate `x i`. The LFR and the block matrix take the values $F(x)$, $R(x)$ as matrix arguments. Mathlib's matrix inverse returns $0$ at a singular matrix, so the LFR is meaningful only where $\det(I - D\Delta) \neq 0$; the robust feasible set requires that condition in the same clause as positive semidefiniteness. The norm is Mathlib's $\ell^2$ operator norm (`Matrix.Norms.L2Operator`), i.e. the largest singular value. $\mathcal{D}$ is a `Submodule`. $\rho^{-2}$ is written `(ρ ^ 2)⁻¹`. Block concatenations are indexed by the sigma type `Σ i, Fin (r i)`.
-- source:
--   El Ghaoui, Oustry and Lebret, Robust Solutions to Uncertain Semidefinite Programs, SIAM J. Optim. 9(1) (1998), p. 33, Notation and Eq. (1); p. 35, Eq. (2) and Eq. (5); p. 37, Eq. (11), Eq. (13) and Theorem 3.2 (corrected); p. 47, §5.8 (definition of L and R)

import Mathlib

open Matrix
open scoped Matrix.Norms.L2Operator

namespace RobustSDP.Structured

/-- An affine matrix-valued map given by its coefficients (El Ghaoui–Oustry–Lebret 1998, (1),
p. 33, and §2.2, p. 35): `affineMap A x = A₀ + ∑ᵢ xᵢ Aᵢ`, where the coefficient `A (i+1)` is the
paper's `A_{i+1}` multiplying the `i`-th coordinate of `x : Fin m → ℝ` (0-based). Used both for
`F(x) = F₀ + ∑ xᵢ Fᵢ` (`n × n`) and for `R(x) = R₀ + ∑ xᵢ Rᵢ` (`q × n`). -/
def affineMap {m r c : ℕ} (A : Fin (m + 1) → Matrix (Fin r) (Fin c) ℝ) (x : Fin m → ℝ) :
    Matrix (Fin r) (Fin c) ℝ :=
  A 0 + ∑ i : Fin m, x i • A i.succ

/-- The linear-fractional representation (5), p. 35:
`F(x, Δ) = F(x) + L Δ (I − DΔ)⁻¹ R(x) + R(x)ᵀ (I − ΔᵀDᵀ)⁻¹ Δᵀ Lᵀ`, written for given values
`Fx = F(x)` (`n × n`) and `Rx = R(x)` (`q × n`), with `L : n × p`, `D : q × p`, `Δ : p × q`.
Mathlib's `⁻¹` returns `0` on a singular matrix, so this expression is only meaningful where
`det (1 - D * Δ) ≠ 0`; every use states that guard next to it. -/
noncomputable def lfr {n p q : ℕ} (Fx : Matrix (Fin n) (Fin n) ℝ) (Rx : Matrix (Fin q) (Fin n) ℝ)
    (L : Matrix (Fin n) (Fin p) ℝ) (D : Matrix (Fin q) (Fin p) ℝ) (Δ : Matrix (Fin p) (Fin q) ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  Fx + L * Δ * (1 - D * Δ)⁻¹ * Rx + Rxᵀ * (1 - Δᵀ * Dᵀ)⁻¹ * Δᵀ * Lᵀ

/-- The robust feasible set (2), p. 35, for the perturbation model `(F(·), R(·), L, D, 𝒟, ρ)`:
`x` is robustly feasible iff for every `Δ ∈ 𝒟` with spectral norm `‖Δ‖ ≤ ρ`, `F(x, Δ)` is well
defined (`det (I − DΔ) ≠ 0`) and `F(x, Δ) ⪰ 0`. The norm is the largest singular value
(`Matrix.Norms.L2Operator`), and `⪰ 0` is `Matrix.PosSemidef` (symmetric positive semidefinite).
`𝒟` is an arbitrary linear subspace of `ℝ^{p×q}` (§3.2, p. 37). -/
def robustFeasibleSet {m n p q : ℕ} (Fs : Fin (m + 1) → Matrix (Fin n) (Fin n) ℝ)
    (Rs : Fin (m + 1) → Matrix (Fin q) (Fin n) ℝ) (L : Matrix (Fin n) (Fin p) ℝ)
    (D : Matrix (Fin q) (Fin p) ℝ) (𝒟 : Submodule ℝ (Matrix (Fin p) (Fin q) ℝ)) (ρ : ℝ) :
    Set (Fin m → ℝ) :=
  {x | ∀ Δ ∈ 𝒟, ‖Δ‖ ≤ ρ →
    (1 - D * Δ).det ≠ 0 ∧ (lfr (affineMap Fs x) (affineMap Rs x) L D Δ).PosSemidef}

/-- The set `𝓑` of scaling triples associated with the subspace `𝒟` (§3.2, (11), p. 37),
**corrected** as the proof of Lemma 3.2 requires: triples
`(S, T, G) ∈ ℝ^{p×p} × ℝ^{q×q} × ℝ^{p×q}` with `S Δ = Δ T` and `G Δᵀ = −Δ Gᵀ` for every
`Δ ∈ 𝒟`. (The printed (11) takes `G ∈ ℝ^{q×p}` with `GΔ = −ΔᵀGᵀ`; with that shape the products
`LG`, `DG` of (13) are undefined. For square skew-symmetric `G` and symmetric `Δ` the two
conditions coincide.) -/
def scalingSet {p q : ℕ} (𝒟 : Submodule ℝ (Matrix (Fin p) (Fin q) ℝ)) :
    Set (Matrix (Fin p) (Fin p) ℝ × Matrix (Fin q) (Fin q) ℝ × Matrix (Fin p) (Fin q) ℝ) :=
  {STG | ∀ Δ ∈ 𝒟, STG.1 * Δ = Δ * STG.2.1 ∧ STG.2.2 * Δᵀ = -(Δ * STG.2.2ᵀ)}

/-- The `(n + q) × (n + q)` block matrix of the SDP of Theorem 3.2, p. 37, in the variables
`(x, S, T, G)`, **corrected** (see `scalingSet`), written for given values `Fx = F(x)`,
`Rx = R(x)`:
`[[F(x) − LSLᵀ, R(x)ᵀ − LSDᵀ + LG], [R(x) − DSLᵀ + GᵀLᵀ, ρ⁻²T − DSDᵀ + DG + GᵀDᵀ]]`
(`Matrix.fromBlocks A B C D` has `B` top-right and `C` bottom-left). At `ρ = 1` it is the
corrected matrix (13) of Lemma 3.2. -/
noncomputable def structuredLMI {n p q : ℕ} (Fx : Matrix (Fin n) (Fin n) ℝ)
    (Rx : Matrix (Fin q) (Fin n) ℝ) (L : Matrix (Fin n) (Fin p) ℝ) (D : Matrix (Fin q) (Fin p) ℝ)
    (S : Matrix (Fin p) (Fin p) ℝ) (T : Matrix (Fin q) (Fin q) ℝ) (G : Matrix (Fin p) (Fin q) ℝ)
    (ρ : ℝ) : Matrix (Fin n ⊕ Fin q) (Fin n ⊕ Fin q) ℝ :=
  fromBlocks (Fx - L * S * Lᵀ) (Rxᵀ - L * S * Dᵀ + L * G) (Rx - D * S * Lᵀ + Gᵀ * Lᵀ)
    ((ρ ^ 2)⁻¹ • T - D * S * Dᵀ + D * G + Gᵀ * Dᵀ)

/-- Horizontal block concatenation `[L₁ … L_m]` of `n × rᵢ` matrices (§5.8, p. 47), with the
column index `⟨i, k⟩ : Σ i, Fin (r i)` meaning column `k` of block `i`. -/
def blockRow {m n : ℕ} {r : Fin m → ℕ} (Ls : (i : Fin m) → Matrix (Fin n) (Fin (r i)) ℝ) :
    Matrix (Fin n) (Σ i, Fin (r i)) ℝ :=
  Matrix.of fun a b => Ls b.1 a b.2

/-- Vertical block concatenation `[R₁; …; R_m]` of `rᵢ × n` matrices (§5.8, p. 47), with the
row index `⟨i, k⟩ : Σ i, Fin (r i)` meaning row `k` of block `i`. -/
def blockCol {m n : ℕ} {r : Fin m → ℕ} (Rs : (i : Fin m) → Matrix (Fin (r i)) (Fin n) ℝ) :
    Matrix (Σ i, Fin (r i)) (Fin n) ℝ :=
  Matrix.of fun b a => Rs b.1 b.2 a

end RobustSDP.Structured


