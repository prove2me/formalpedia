-- Prove2me | Definitions.Def_GraphSimOT_Gaps_Spectral
-- name    : GraphSimOT_Gaps_Spectral
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T18:06:01.302117+00:00
-- url     : https://prove2.me/theorems/d3e1f6ca-2122-46d9-b7af-32c41fd20b17
-- title:
--   The Q-weighted inner product, seminorm and the spectral discrepancy γ_Q(A′, B′) (App. F.2)
-- statement:
--   For $Q\in\mathrm{DS}(n)$ and functions $f, g : [n]^2\to\mathbb R$, the $Q$-weighted semi-inner product and seminorm are
--   $$\langle f, g\rangle_Q = \frac1n\sum_{i,j}Q_{ij}f(i,j)g(i,j),\qquad \|f\|_Q = \sqrt{\langle f,f\rangle_Q}$$
--   (`innerQ`, `normQ`). For $A', B'\in\mathbb R^{n\times n}$ (Eq. (40)),
--   $$\gamma_Q(A',B') = \max_{\|f\|_Q = \|g\|_Q = 1}\frac1{n^2}\Big|\sum_{i,j,k,\ell}f(i,j)\,Q_{ij}Q_{k\ell}(A'_{ik} - B'_{j\ell})\,g(k,\ell)\Big|$$
--   (`gammaQ`); with the adjacency matrices of $G, H$ it is $\gamma_Q$, and $\delta^{OT}_2 = \min_Q\gamma_Q$, $\delta_2 = \min_P\gamma_P$.
--
--   **Formalization Note.** `gammaQ` is the supremum of the set of these values. For $Q\in\mathrm{DS}(n)$ with $n\ge1$ the set is nonempty (constant functions $f = g = 1$ have $\|f\|_Q = 1$) and bounded (only the values of $f, g$ on $\mathrm{supp}(Q)$ enter), so the supremum is the paper's maximum; it is $0$ when the set is empty ($n = 0$).
-- source:
--   Breitung, Gervens, Grohe, Graph Similarity Meets Optimal Transport, arXiv:2611.05048 (held version, sha256 1cd10e91…), App. F.2, p. 47, Eq. (40)

import Mathlib

namespace GraphSimOT.Gaps

/-!
# The spectral discrepancy `γ_Q` (App. F.2)

Breitung, Gervens, Grohe, *Graph Similarity Meets Optimal Transport*, arXiv:2611.05048
(held version, sha256 1cd10e91…), App. F.2, p. 47, Eq. (40).

For `Q ∈ DS(n)` and test functions `f, g : [n]² → ℝ`:
`⟨f, g⟩_Q = (1/n) ∑_{i,j} Q_ij f(i, j) g(i, j)`, `‖f‖_Q = √⟨f, f⟩_Q`, and
`γ_Q(A', B') = max_{‖f‖_Q = ‖g‖_Q = 1} n^{-2} |∑_{i,j,k,ℓ} f(i, j) Q_ij Q_kℓ (A'_ik − B'_jℓ) g(k, ℓ)|`,
written as the supremum of the set of these values (nonempty and bounded for `Q ∈ DS(n)`,
`n ≥ 1`; it is `0` when the set is empty).
-/

/-- The `Q`-weighted semi-inner product `⟨f, g⟩_Q = (1/n) ∑_{i,j} Q_ij f(i, j) g(i, j)`. -/
noncomputable def innerQ {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ) (f g : Fin n → Fin n → ℝ) : ℝ :=
  (1 / (n : ℝ)) * ∑ i, ∑ j, Q i j * f i j * g i j

/-- The `Q`-weighted seminorm `‖f‖_Q = √⟨f, f⟩_Q`. -/
noncomputable def normQ {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ) (f : Fin n → Fin n → ℝ) : ℝ :=
  Real.sqrt (innerQ Q f f)

/-- `γ_Q(A', B')` of Eq. (40): the supremum over `f, g : [n]² → ℝ` with `‖f‖_Q = ‖g‖_Q = 1` of
`n^{-2} |∑_{i,j,k,ℓ} f(i, j) Q_ij Q_kℓ (A'_ik − B'_jℓ) g(k, ℓ)|`. -/
noncomputable def gammaQ {n : ℕ} (Q A' B' : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  sSup {r : ℝ | ∃ f g : Fin n → Fin n → ℝ, normQ Q f = 1 ∧ normQ Q g = 1 ∧
    r = |(1 / (n : ℝ) ^ 2) *
      ∑ i, ∑ j, ∑ k, ∑ l, f i j * Q i j * Q k l * (A' i k - B' j l) * g k l|}

end GraphSimOT.Gaps


