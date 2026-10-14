-- Prove2me | Definitions.Def_RobustQueueRatio_SPStability_RatioMatrix
-- name    : RobustQueueRatio_SPStability_RatioMatrix
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T01:23:20.04404+00:00
-- url     : https://prove2.me/theorems/03954801-9a97-4a58-9fb9-73cdc9e5e143
-- title:
--   Ratio matrices $\Delta$ ($CM\Delta=I$), static-priority $\Delta$, $R_\Delta=(CMQ\Delta)^{-1}$, $\theta_\Delta=R_\Delta(\rho-e)$, ratio-matrix neighbors
-- statement:
--   Fix an open multiclass network $(C,M,P,\alpha)$ with $J$ stations and $K$ classes, and let $Q=(I-P^\top)^{-1}$ and $\rho=CMQ\alpha$.
--
--   **Ratio matrix.** A queue-ratio policy is described by weights $\delta_k\ge 0$, one per class, collected in the $K\times J$ **ratio matrix** $\Delta$ with $\Delta_{kj}=\delta_k$ if class $k$ is served at station $j$ and $\Delta_{kj}=0$ otherwise. The proportions $\delta_\ell m_\ell$ of each station's workload sum to one, $\sum_{\ell\in C(j)}\delta_\ell m_\ell=1$, which in matrix form reads
--
--   $$
--   CM\Delta=I .
--   $$
--
--   **Static priority.** A ratio matrix is **static-priority** if at every station $j$ there is a class $k\in C(j)$ (the lowest-priority class) with $\Delta_{kj}=1/m_k$, and $\Delta_{lj}=0$ for every other $l\in C(j)$.
--
--   **Reflection matrix and drift.** For a ratio matrix $\Delta$, $R_\Delta^{-1}=CMQ\Delta$ is a $J\times J$ matrix. When it is invertible, the reflection matrix is $R_\Delta=(CMQ\Delta)^{-1}$ and the drift is $\theta_\Delta=R_\Delta(\rho-e)$, where $e$ is the all-ones vector.
--
--   **Neighbors.** A collection of ratio matrices $\Delta_i$ are **ratio-matrix neighbors** if they differ in at most one column.
--
--   The static-priority matrices are the corners of the set of ratio matrices. The mission's results transfer properties of $(R_\Delta,\theta_\Delta)$ from those corners to every ratio matrix, one column at a time along neighbors.
--
--   **Formalization Note.** `IsRatioMatrix N Δ` says that $\Delta_{kj}=0$ whenever $s(k)\neq j$, that every entry is $\ge 0$, and that $CM\Delta=I$; the value $\delta_k=\Delta_{k,s(k)}$ is then determined. The nonnegativity of $\delta$ is part of the definition: the paper calls $\delta_\ell m_\ell$ proportions and takes $\Delta\in\mathbb R^{K\times J}_+$. `reflInv N Δ` is $CMQ\Delta$ and `refl N Δ` is Lean's matrix inverse of it. Lean's inverse is $0$ when the matrix is singular, so every theorem assumes or concludes invertibility of $CMQ\Delta$. `theta N Δ` is $R_\Delta(\rho-e)$, a function of $\Delta$ and never a free vector. `AreNeighbors Δ` for a family $\Delta:\iota\to\mathbb R^{K\times J}$ says that the set of columns in which some two members differ has at most one element.
-- source:
--   Zhao, Gurvich & Hasenbein, A Hierarchical Approach to Robust Stability of Multiclass Queueing Networks, arXiv:2303.17746v3, p. 8 (ratio matrix, CM∆ = I; Definition 1, Static-priority ∆), pp. 9–10 (R = (CMQ∆)^{-1}, θ = R(ρ − e)), p. 13 (Definition 7, Ratio-matrix Neighbors)

import Mathlib
import Definitions.Def_RobustQueueRatio_SPStability_Network

noncomputable section

namespace RobustQueueRatio.SPStability

open Matrix

variable {J K : ℕ}

/-- `Δ` is a **ratio matrix** of the network `N` (arXiv:2303.17746v3, p. 8): a `K × J` matrix
with `Δ_kj = δ_k ≥ 0` if class `k` is served at station `j` and `Δ_kj = 0` otherwise, whose
weights satisfy `∑_{ℓ ∈ C(j)} δ_ℓ m_ℓ = 1` for every station `j`, i.e. `C M Δ = I`. -/
def IsRatioMatrix (N : Network J K) (Δ : Matrix (Fin K) (Fin J) ℝ) : Prop :=
  (∀ k j, N.s k ≠ j → Δ k j = 0) ∧ (∀ k j, 0 ≤ Δ k j) ∧ N.C * N.M * Δ = 1

/-- A ratio matrix is **static-priority** (arXiv:2303.17746v3, p. 8, Definition 1) if, at every
station `j`, `Δ_kj = 1/m_k` for some class `k ∈ C(j)` (the lowest-priority class) and
`Δ_lj = 0` for all other `l ∈ C(j)`. -/
def IsStaticPriority (N : Network J K) (Δ : Matrix (Fin K) (Fin J) ℝ) : Prop :=
  IsRatioMatrix N Δ ∧
    ∀ j, ∃ k, N.s k = j ∧ Δ k j = 1 / N.m k ∧ ∀ l, N.s l = j → l ≠ k → Δ l j = 0

/-- `R_Δ⁻¹ = C M Q Δ`, a `J × J` matrix (arXiv:2303.17746v3, p. 9). -/
def reflInv (N : Network J K) (Δ : Matrix (Fin K) (Fin J) ℝ) : Matrix (Fin J) (Fin J) ℝ :=
  N.C * N.M * N.Q * Δ

/-- The reflection matrix `R_Δ = (C M Q Δ)⁻¹` (arXiv:2303.17746v3, pp. 9–10). Lean's inverse is
`0` for a singular matrix; every statement using it assumes `C M Q Δ` invertible. -/
def refl (N : Network J K) (Δ : Matrix (Fin K) (Fin J) ℝ) : Matrix (Fin J) (Fin J) ℝ :=
  (reflInv N Δ)⁻¹

/-- The drift `θ_Δ = R_Δ (ρ − e)` of the Skorohod problem (arXiv:2303.17746v3, p. 10), where `e`
is the all-ones vector. -/
def theta (N : Network J K) (Δ : Matrix (Fin K) (Fin J) ℝ) : Fin J → ℝ :=
  refl N Δ *ᵥ (N.ρ - fun _ => (1 : ℝ))

/-- A collection `Δ_i, i ∈ ι` of `K × J` matrices are **ratio-matrix neighbors**
(arXiv:2303.17746v3, p. 13, Definition 7) if they differ in at most one column: the set of
columns `j` in which some two members of the collection differ has at most one element. -/
def AreNeighbors {ι : Type} (Δ : ι → Matrix (Fin K) (Fin J) ℝ) : Prop :=
  ({j | ∃ a b k, Δ a k j ≠ Δ b k j} : Set (Fin J)).Subsingleton

end RobustQueueRatio.SPStability

end


