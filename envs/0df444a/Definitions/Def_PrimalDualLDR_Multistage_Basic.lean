-- Prove2me | Definitions.Def_PrimalDualLDR_Multistage_Basic
-- name    : PrimalDualLDR_Multistage_Basic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T08:41:04.081739+00:00
-- url     : https://prove2.me/theorems/c1893f9c-2bb2-4f85-9236-716d6d76819a
-- title:
--   Polyhedron $\{W\xi\ge h\}$, support of a measure, $e_1$, $\mathcal L^2_{k,n}$, history dimensions $k^t$ and truncation operators $P_t$ (pp. 3–4, 17–18)
-- statement:
--   General objects used in §4 of Kuhn, Wiesemann and Georghiou.
--
--   1. For $W \in \mathbb R^{l\times k}$ and $h \in \mathbb R^l$, the **polyhedron** $\Xi(W,h) = \{\xi \in \mathbb R^k : W\xi \ge h\}$, with the componentwise order (Notation, p. 3, and (2.1a)).
--   2. A set $S \subseteq \mathbb R^k$ is the **support** of a measure $\mathbb P$ on $(\mathbb R^k,\mathfrak B(\mathbb R^k))$ if $S$ is closed, $\mathbb P(\mathbb R^k\setminus S) = 0$, and every open ball of positive radius centred at a point of $S$ has positive measure. These conditions say exactly that $S$ is the smallest closed set of probability one, the paper's definition.
--   3. $e_1 \in \mathbb R^k$ is the basis vector with first component $1$ and all others $0$.
--   4. $x : \mathbb R^k \to \mathbb R^n$ belongs to $\mathcal L^2_{k,n}$ if it is Borel measurable and $\mathbb E\|x(\xi)\|^2 < \infty$.
--   5. For stage dimensions $k_1,\dots,k_T$, the total dimension is $k = \sum_{t=1}^T k_t$ and the **history dimension** of stage $t$ is $k^t = \sum_{s=1}^t k_s \le k$.
--   6. The **truncation operator** $P_t : \mathbb R^k \to \mathbb R^{k^t}$, $\xi \mapsto \xi^t$, keeps the first $k^t$ coordinates; as a matrix, $P_t = [\,I\ \ 0\,] \in \mathbb R^{k^t\times k}$. Two structural lemmas record that the matrix acts as the truncation, $P_t\xi = \xi^t$, and that the truncation is Borel measurable.
--
--   These are the building blocks of the multistage setting: the sample $\xi = (\xi_1,\dots,\xi_T)$ is revealed stage by stage, a non-anticipative decision at stage $t$ is a function of the history $\xi^t = P_t\xi$, and decision rules are square integrable.
--
--   **Formalization Note** Vectors in $\mathbb R^k$ are functions `Fin k → ℝ`; the paper's index $1$ is the Lean index `0`, and stage $t \in \{1,\dots,T\}$ is the `Fin T` index $t-1$. The balls in the support are sup-metric balls, which generate the Euclidean topology. These objects restate those of the fixed-recourse mission of this series in the namespace `PrimalDualLDR.Multistage`.
-- source:
--   Kuhn, Wiesemann, Georghiou, Primal and dual linear decision rules in stochastic and robust optimization, Optimization Online 2009/02/2218, pp. 3–4 (Notation, (2.1a)) and pp. 17–18 (§4, k^t, P_t)

import Mathlib
import Definitions.Def_PrimalDualLDR_FixedRecourse_Basic

open MeasureTheory

namespace PrimalDualLDR.Multistage

/-- The total dimension `k = Σ_{t=1}^T k_t` of the sample space (p. 17), for stage dimensions
`kk : Fin T → ℕ` (stage `t` of the paper is the `Fin` index `t - 1`). -/
def ksum {T : ℕ} (kk : Fin T → ℕ) : ℕ := ∑ s, kk s

/-- The history dimension `k^t = Σ_{s=1}^t k_s` (p. 18). -/
def kbar {T : ℕ} (kk : Fin T → ℕ) (t : Fin T) : ℕ := ∑ s ∈ Finset.univ.filter (fun s => s ≤ t), kk s

/-- `k^t ≤ k`. -/
theorem kbar_le_ksum {T : ℕ} (kk : Fin T → ℕ) (t : Fin T) : kbar kk t ≤ ksum kk :=
  Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)

/-- The truncation operator `P_t : ℝ^k → ℝ^{k^t}`, `ξ ↦ ξ^t = (ξ_1, …, ξ_t)` (p. 18): it keeps the
first `k^t` coordinates of `ξ`. -/
def trunc {T : ℕ} (kk : Fin T → ℕ) (t : Fin T) (ξ : Fin (ksum kk) → ℝ) : Fin (kbar kk t) → ℝ :=
  fun i => ξ (Fin.castLE (kbar_le_ksum kk t) i)

/-- The truncation operator as a matrix `P_t = [I 0] ∈ ℝ^{k^t × k}` (p. 18). -/
def Pmat {T : ℕ} (kk : Fin T → ℕ) (t : Fin T) : Matrix (Fin (kbar kk t)) (Fin (ksum kk)) ℝ :=
  Matrix.of fun i j => if j = Fin.castLE (kbar_le_ksum kk t) i then 1 else 0

/-- The matrix `P_t` acts as the truncation operator: `P_t ξ = ξ^t`. -/
theorem Pmat_mulVec {T : ℕ} (kk : Fin T → ℕ) (t : Fin T) (ξ : Fin (ksum kk) → ℝ) :
    (Pmat kk t).mulVec ξ = trunc kk t ξ := by
  ext i
  simp [Pmat, trunc, Matrix.mulVec, dotProduct]

/-- The truncation operator is Borel measurable. -/
theorem measurable_trunc {T : ℕ} (kk : Fin T → ℕ) (t : Fin T) : Measurable (trunc kk t) :=
  measurable_pi_lambda _ (fun _ => measurable_pi_apply _)

end PrimalDualLDR.Multistage


