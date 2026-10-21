-- Prove2me | Definitions.Def_MatrixAnalytic_Stability_Reducible
-- name    : MatrixAnalytic_Stability_Reducible
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-20T15:43:46.793194+00:00
-- url     : https://prove2.me/theorems/821ae86a-aa83-4fc3-b677-6a1730ea34b8
-- title:
--   The block form (7.11) of a reducible phase matrix A, the block D^{(0)}, class-stationary vectors γ^{(k)} and the rates γ^{(k)}C_r^{(k)}1
-- statement:
--   Let the set of phases be finite. Following §7.3 (p. 159), the stochastic phase matrix $A$ is written, after a permutation of its rows and columns, as
--   $$A = \begin{bmatrix} C^{(1)} & 0 & \cdots & 0 & 0 \\ 0 & C^{(2)} & \cdots & 0 & 0 \\ \vdots & & \ddots & & \vdots \\ 0 & 0 & \cdots & C^{(K)} & 0 \\ D^{(1)} & D^{(2)} & \cdots & D^{(K)} & D^{(0)} \end{bmatrix}, \tag{7.11}$$
--   which partitions the phases into classes $\phi(1), \dots, \phi(K)$ and a remainder $\phi(0)$.
--
--   1. $A$ **has the block form (7.11)** for a labelling of the phases by $\phi(1), \dots, \phi(K)$, $\phi(0)$ if every class $\phi(k)$, $k \ge 1$, is nonempty, a phase of $\phi(k)$ moves under $A$ only to phases of $\phi(k)$, and each diagonal block $C^{(k)}$ (the restriction of $A$ to $\phi(k)$) is irreducible. The rows of $\phi(0)$ are not restricted by this predicate.
--   2. $D^{(0)}$ is the restriction of $A$ to $\phi(0)$.
--   3. $\gamma$ is **the stationary probability vector of $C^{(k)}$** if it is a row vector vanishing outside $\phi(k)$ with $\gamma \ge 0$, $\gamma\mathbf 1 = 1$ and $\sum_{i \in \phi(k)} \gamma_i A_{ij} = \gamma_j$ for every $j \in \phi(k)$.
--   4. For $r \in \{0, 2\}$, $C_r^{(k)}$ is the diagonal block of $A_r$ on $\phi(k)$ (7.12), and $\gamma^{(k)}C_r^{(k)}\mathbf 1 = \sum_{i, j \in \phi(k)} \gamma^{(k)}_i (A_r)_{ij}$.
--
--   **Formalization Note** The partition is a function $\phi$ from phases to `Option (Fin K)`: `some k` is the class numbered $k + 1$ in the book (Lean counts from $0$) and `none` is $\phi(0)$, which may be empty. That each $C^{(k)}$ is stochastic follows from item 1 and the stochasticity of $A$, so it is not a separate clause. The condition on $D^{(0)}$ is left to each theorem, because the printed hypothesis and the hypothesis its proof uses differ (see Theorem 7.3.1 and its corrected variant).
-- source:
--   Latouche & Ramaswami, Introduction to Matrix Analytic Methods in Stochastic Modeling, SIAM 1999, p. 159, Eqs. (7.11)–(7.12); p. 160, Theorem 7.3.1

import Mathlib
import Definitions.Def_MatrixAnalytic_Stability_Chain
import Definitions.Def_MatrixAnalytic_Stability_QBD

namespace MatrixAnalytic.Stability

noncomputable section

open scoped ENNReal

/-!
The block form (7.11) of a reducible phase matrix `A` (§7.3, p. 159) on a finite phase set `ι`.
The partition of the phases into `φ(1), …, φ(K)` and `φ(0)` ("possibly after a permutation of
its rows and columns") is a labelling `φ : ι → Option (Fin K)`: `φ i = some k` puts the phase
`i` in `φ(k + 1)` (the classes are numbered from `0` in Lean) and `φ i = none` puts it in `φ(0)`.
-/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `A` has the block form (7.11) with diagonal blocks `C^{(1)}, …, C^{(K)}` on the classes of
`φ`: every class is nonempty, a phase of a class `k` moves under `A` only inside its class (the
off-diagonal blocks of the rows of `C^{(k)}` are `0`), and each diagonal block `C^{(k)}` is
irreducible. The rows of `φ(0)`, `[D^{(1)} ⋯ D^{(K)} D^{(0)}]`, are unrestricted here. -/
def IsBlockForm711 {K : ℕ} (A : ι → ι → ℝ) (φ : ι → Option (Fin K)) : Prop :=
  (∀ k : Fin K, ∃ i : ι, φ i = some k) ∧
  (∀ (k : Fin K) (i j : ι), φ i = some k → φ j ≠ some k → A i j = 0) ∧
  ∀ k : Fin K, IrreducibleC (fun a b : {i : ι // φ i = some k} => A a.1 b.1)

/-- The block `D^{(0)}` of (7.11): `A` restricted to the phases of `φ(0)`, in `ℝ≥0∞`. -/
def blockD0 {K : ℕ} (A : ι → ι → ℝ) (φ : ι → Option (Fin K)) :
    {i : ι // φ i = none} → {i : ι // φ i = none} → ℝ≥0∞ :=
  fun a b => ennMat A a.1 b.1

/-- `γ` is the stationary probability vector of the block `C^{(k)}` of `A`, written as a row
vector on all phases that vanishes outside the class `k`: `γ ≥ 0`, `γ1 = 1` and
`Σ_{i ∈ φ(k)} γ_i A_{ij} = γ_j` for every `j ∈ φ(k)`. -/
def IsClassStationary {K : ℕ} (A : ι → ι → ℝ) (φ : ι → Option (Fin K)) (k : Fin K)
    (γ : ι → ℝ) : Prop :=
  (∀ i : ι, φ i ≠ some k → γ i = 0) ∧ (∀ i : ι, 0 ≤ γ i) ∧ ∑ i, γ i = 1 ∧
    ∀ j : ι, φ j = some k →
      ∑ i ∈ Finset.univ.filter (fun i => φ i = some k), γ i * A i j = γ j

/-- `γ^{(k)} C_r^{(k)} 1`, where `C_r^{(k)}` is the diagonal block of `A_r` on the class `k`
(7.12): `Σ_{i, j ∈ φ(k)} γ_i (A_r)_{ij}`. -/
def classRate {K : ℕ} (Ar : ι → ι → ℝ) (φ : ι → Option (Fin K)) (k : Fin K)
    (γ : ι → ℝ) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i => φ i = some k),
    ∑ j ∈ Finset.univ.filter (fun j => φ j = some k), γ i * Ar i j

end

end MatrixAnalytic.Stability


