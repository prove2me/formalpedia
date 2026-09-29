-- Prove2me | Definitions.Def_RobustSDP_Unstructured_Model
-- name    : RobustSDP_Unstructured_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T14:08:57.721548+00:00
-- url     : https://prove2.me/theorems/00173bcf-788a-4f7b-b60d-8790bee3e145
-- title:
--   Unstructured perturbation model: affine maps, block-row perturbations, the robust feasible set and the LMI (20)
-- statement:
--   This file fixes the objects of the unstructured-perturbation examples of El Ghaoui, Oustry and Lebret (§5.1 and §5.6).
--
--   Let $m, n$ be natural numbers and $x \in \mathbb{R}^m$ the decision variable. Throughout, $\|x\|^2 = \sum_{i=1}^m x_i^2$ is the squared Euclidean norm, $\|M\|$ of a matrix is its largest singular value, and $X \succeq 0$ means that $X$ is symmetric positive semidefinite.
--
--   1. **Affine matrix maps.** Given coefficient matrices $A_0, A_1, \dots, A_m$ of a common size,
--   $$A(x) = A_0 + \sum_{i=1}^{m} x_i A_i .$$
--   It is used for $F(x) = F_0 + \sum_i x_i F_i$ with $F_i \in \mathbb{R}^{n\times n}$ (Eq. (1)) and for $H(x) = H_0 + \sum_i x_i H_i$ with $H_i \in \mathbb{R}^{p\times q}$ (§5.6).
--
--   2. **Block rows.** A perturbation $\Delta = [\Delta_0 \ \cdots \ \Delta_m]$ is a row of $m+1$ blocks of equal size, regarded as **one** matrix (for $n\times n$ blocks, an $n \times n(m+1)$ matrix); its norm $\|\Delta\|$ is the largest singular value of that whole matrix.
--
--   3. **Unstructured perturbation of an LMI (§5.1).**
--   $$\mathbf{F}(x,\Delta) = F(x) + \Delta_0 + \Delta_0^T + \sum_{i=1}^m x_i(\Delta_i + \Delta_i^T).$$
--
--   4. **Robust feasible set.** For a level $\rho$,
--   $$\mathcal{X}_\rho = \{x \in \mathbb{R}^m : \mathbf{F}(x,\Delta) \succeq 0 \text{ for every } \Delta \in \mathbb{R}^{n\times n(m+1)} \text{ with } \|\Delta\| \le \rho\}.$$
--
--   5. **The matrix $R(x) = [1;\,x] \otimes I$ of (19)**, of size $n(m+1)\times n$: its $i$-th $n\times n$ block is $\tilde x_i I$, where $\tilde x = (1, x_1, \dots, x_m)$. With it, $\mathbf{F}(x,\Delta) = F(x) + \Delta R(x) + R(x)^T\Delta^T$.
--
--   6. **The LMI of (20)**: for $\tau \in \mathbb{R}$, the symmetric block matrix
--   $$\begin{bmatrix} F(x) - \tau I & [1\ \ x^T]\otimes \rho I \\ [1\ \ x^T]^T \otimes \rho I & \tau I \end{bmatrix} = \begin{bmatrix} F(x) - \tau I & \rho R(x)^T \\ \rho R(x) & \tau I\end{bmatrix}.$$
--
--   7. **Full perturbation of a norm-minimization problem (§5.6).** For $p\times q$ matrices $H_0, \dots, H_m$ and a block row $\Delta = [\Delta_0 \cdots \Delta_m]$ of $p\times q$ blocks,
--   $$\mathbf{H}(x,\Delta) = H_0 + \Delta_0 + \sum_{i=1}^m x_i (H_i + \Delta_i).$$
--
--   These objects are shared by every statement of the mission: the robust feasible set is what the robust SDP optimizes over, (20) is its SDP reformulation, and $\mathbf{H}$ is the perturbed data of the robust norm-minimization problem.
--
--   **Formalization Note** The coefficient list is indexed by `Fin (m + 1)`, with `A 0` the constant term and `A (i+1)` the coefficient of the 0-based coordinate `x i`. A block row is a matrix whose columns are indexed by pairs `(i, b)` with `i : Fin (m + 1)` the block and `b` the column inside the block; `block Δ i` extracts $\Delta_i$. The norm is Mathlib's $\ell^2$ operator norm (`Matrix.Norms.L2Operator`), not the default entrywise norm. In (19) the paper writes $\mathcal D = \mathbb R^{n\times nm}$; since $\Delta$ has $m+1$ blocks the space is $\mathbb R^{n\times n(m+1)}$, which is what is used here. There is no inverse in this model ($D = 0$), so no well-posedness condition appears.
-- source:
--   El Ghaoui, Oustry and Lebret, Robust Solutions to Uncertain Semidefinite Programs, SIAM J. Optim. 9(1) (1998), p. 33, Notation and Eq. (1); p. 35, Eq. (2); p. 41, §5.1, display defining F(x, Δ), Eq. (19) and Eq. (20); pp. 44–45, §5.6, Eq. (27) and the display defining H(x, Δ)

import Mathlib

open Matrix
open scoped Matrix.Norms.L2Operator

namespace RobustSDP.Unstructured

/-- An affine matrix-valued map given by its coefficients (El Ghaoui–Oustry–Lebret 1998, (1),
p. 33, and §5.6, p. 44): `affineMap A x = A₀ + ∑ᵢ xᵢ Aᵢ`, where the coefficient `A (i+1)` is the
paper's `A_{i+1}` multiplying the `i`-th coordinate of `x : Fin m → ℝ` (0-based). Used for
`F(x) = F₀ + ∑ xᵢ Fᵢ` (`n × n`) and for `H(x) = H₀ + ∑ xᵢ Hᵢ` (`p × q`). -/
def affineMap {m r c : ℕ} (A : Fin (m + 1) → Matrix (Fin r) (Fin c) ℝ) (x : Fin m → ℝ) :
    Matrix (Fin r) (Fin c) ℝ :=
  A 0 + ∑ i : Fin m, x i • A i.succ

/-- The `i`-th block `Δᵢ` (`r × c`) of a block row `Δ = [Δ₀ … Δ_m]`, stored as one
`r × (m+1)c` matrix whose columns are indexed by pairs `(i, b)`: `(block Δ i) a b = Δ a (i, b)`. -/
def block {m r c : ℕ} (Δ : Matrix (Fin r) (Fin (m + 1) × Fin c) ℝ) (i : Fin (m + 1)) :
    Matrix (Fin r) (Fin c) ℝ :=
  Matrix.of fun a b => Δ a (i, b)

/-- The unstructured perturbation of an LMI (§5.1, p. 41):
`F(x, Δ) = F(x) + Δ₀ + Δ₀ᵀ + ∑ᵢ xᵢ (Δᵢ + Δᵢᵀ)`, with `Δ = [Δ₀ … Δ_m]` a block row of `n × n`
blocks, stored as one `n × n(m+1)` matrix. -/
def perturbedLMI {m n : ℕ} (Fs : Fin (m + 1) → Matrix (Fin n) (Fin n) ℝ)
    (Δ : Matrix (Fin n) (Fin (m + 1) × Fin n) ℝ) (x : Fin m → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  affineMap Fs x + (block Δ 0 + (block Δ 0)ᵀ) +
    ∑ i : Fin m, x i • (block Δ i.succ + (block Δ i.succ)ᵀ)

/-- The robust feasible set (2), p. 35, of the unstructured model of §5.1 (`𝒟` the whole space
of `n × n(m+1)` matrices): `x` is robustly feasible iff `F(x, Δ) ⪰ 0` for every `Δ` whose
spectral norm (largest singular value, as one `n × n(m+1)` matrix) is at most `ρ`. There is no
inverse in this model (`D = 0`), so no well-posedness condition is needed. -/
def robustFeasibleSet {m n : ℕ} (Fs : Fin (m + 1) → Matrix (Fin n) (Fin n) ℝ) (ρ : ℝ) :
    Set (Fin m → ℝ) :=
  {x | ∀ Δ : Matrix (Fin n) (Fin (m + 1) × Fin n) ℝ, ‖Δ‖ ≤ ρ → (perturbedLMI Fs Δ x).PosSemidef}

/-- The matrix `R(x) = [1; x] ⊗ I` of (19), p. 41: an `n(m+1) × n` matrix whose `i`-th `n × n`
block is `x̃ᵢ I`, where `x̃ = (1, x₁, …, x_m)`. Rows are indexed by pairs `(i, a)`. -/
def rMat {m n : ℕ} (x : Fin m → ℝ) : Matrix (Fin (m + 1) × Fin n) (Fin n) ℝ :=
  Matrix.of fun ia b => (Fin.cons (1 : ℝ) x : Fin (m + 1) → ℝ) ia.1 * (1 : Matrix (Fin n) (Fin n) ℝ) ia.2 b

/-- The block matrix of the LMI (20), p. 41, in the variables `(x, τ)`:
`[[F(x) − τI, [1 xᵀ] ⊗ ρI], [[1 xᵀ]ᵀ ⊗ ρI, τI]]`, i.e.
`fromBlocks (F(x) − τI) (ρ R(x)ᵀ) (ρ R(x)) (τ I)` with `R(x) = [1; x] ⊗ I` (`rMat`); the
diagonal blocks are `n × n` and `n(m+1) × n(m+1)`. -/
def lmi20 {m n : ℕ} (Fs : Fin (m + 1) → Matrix (Fin n) (Fin n) ℝ) (ρ τ : ℝ) (x : Fin m → ℝ) :
    Matrix (Fin n ⊕ (Fin (m + 1) × Fin n)) (Fin n ⊕ (Fin (m + 1) × Fin n)) ℝ :=
  fromBlocks (affineMap Fs x - τ • (1 : Matrix (Fin n) (Fin n) ℝ)) (ρ • (rMat x)ᵀ) (ρ • rMat x)
    (τ • (1 : Matrix (Fin (m + 1) × Fin n) (Fin (m + 1) × Fin n) ℝ))

/-- The full perturbation of a norm-minimization problem (§5.6, pp. 44–45):
`H(x, Δ) = H₀ + Δ₀ + ∑ᵢ xᵢ (Hᵢ + Δᵢ)`, with `Δ = [Δ₀ … Δ_m]` a block row of `p × q` blocks,
stored as one `p × q(m+1)` matrix. -/
def perturbedH {m p q : ℕ} (Hs : Fin (m + 1) → Matrix (Fin p) (Fin q) ℝ)
    (Δ : Matrix (Fin p) (Fin (m + 1) × Fin q) ℝ) (x : Fin m → ℝ) : Matrix (Fin p) (Fin q) ℝ :=
  Hs 0 + block Δ 0 + ∑ i : Fin m, x i • (Hs i.succ + block Δ i.succ)

end RobustSDP.Unstructured


