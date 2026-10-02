-- Prove2me | Definitions.Def_ProcessingNetworks_FluidStability_FluidEquationData
-- name    : ProcessingNetworks_FluidStability_FluidEquationData
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T17:32:35.783396+00:00
-- url     : https://prove2.me/theorems/4319204e-76ff-4383-a7c7-3b35009eae8b
-- title:
--   Model data and the fluid equations (6.1)-(6.6)
-- statement:
--   An SPN's **fluid-equation model data** collects the constants that the fluid equations of
--   this chapter are stated in terms of: $I$ buffers, $J$ activities, $K$ server pools, the
--   $I \times J$ material-requirement matrix $B$ and expected-output matrix $\Gamma$, the vector
--   $m$ of mean service times, the $K \times J$ capacity-consumption matrix $A$ and $K$-vector $b$
--   of server-pool capacities, and the vector $\lambda$ of external arrival rates.
--
--   A four-tuple $(\hat D, \hat F, \hat T, \hat Z)$ of functions on $[0,\infty)$ (with
--   $\hat D, \hat Z : [0,\infty) \to \mathbb{R}^I$ and $\hat F, \hat T : [0,\infty) \to
--   \mathbb{R}^J$) is a **fluid model solution** if, for every $t \ge 0$:
--   $$
--   \hat Z(t) = \hat Z(0) + \lambda t + \Gamma \hat F(t) - \hat D(t), \qquad
--   \hat Z(t) \ge 0, \qquad
--   \hat D(t) = B \hat F(t), \qquad
--   m_j \hat F_j(t) = \hat T_j(t)\ \ \forall j,
--   $$
--   $\hat T$ is nondecreasing with $\hat T(0) = 0$, and for every $0 \le s \le t$ and every pool
--   $k$, $\sum_j A_{kj}(\hat T_j(t) - \hat T_j(s)) \le b_k (t-s)$. These are exactly Dai and
--   Harrison's equations (6.1)-(6.6): despite the name, (6.2) and (6.6) are an inequality and a
--   Lipschitz bound rather than equalities, but the book calls the whole system "the fluid
--   equations" regardless.
--
--   **Formalization note.** $(6.4)$, $\hat F = M^{-1}\hat T$ for $M := \mathrm{diag}(m)$, is stated
--   directly as $m_j \hat F_j(t) = \hat T_j(t)$ to avoid introducing a matrix inverse, using that
--   every $m_j > 0$ (Assumption 2.1(b)). `Th 0 = 0 ∧ Monotone Th` captures (6.5) with `Monotone`
--   taken for the pointwise (product) order on `Fin J → ℝ`, i.e. every component $\hat T_j$ is a
--   nondecreasing scalar function — exactly the book's "$\hat T$ is nondecreasing."
-- source:
--   Dai & Harrison, Processing Networks: Fluid Models and Stability, pre-publication draft 2020-4-2, p. 106, Eqs. (6.1)-(6.6)

import Mathlib

namespace ProcessingNetworks.FluidStability

/-- Fluid-equation model data for an SPN, Dai & Harrison, Section 2.1/2.5 recap and Section 6.1:
`I` buffers, `J` activities, `K` server pools. `B`, `Γ` are the `I × J` material-requirement
matrix (2.9) and expected-output matrix (Assumption 2.1(b)/(2.13)); `m` is the vector of mean
service times (so `M := diag(m)` of Section 2.6, and (6.4)'s `F̂ = M⁻¹T̂` is stated directly as
`m j * F̂ j = T̂ j`, avoiding a matrix inverse); `A`, `b` are the `K × J` capacity-consumption
matrix and `K`-vector of server-pool capacities of (2.11)/(5.2); `lam` is the vector of external
arrival rates of Assumption 2.1(a). -/
structure FluidEquationData (I J K : ℕ) where
  B : Matrix (Fin I) (Fin J) ℝ
  Γ : Matrix (Fin I) (Fin J) ℝ
  m : Fin J → ℝ
  A : Matrix (Fin K) (Fin J) ℝ
  b : Fin K → ℝ
  lam : Fin I → ℝ

/-- The fluid equations (6.1)-(6.6), Dai & Harrison p. 106 (PDF p. 122): a four-tuple
`(D̂, F̂, T̂, Ẑ)` of functions on `ℝ` (only `t ≥ 0` is meaningful) is a *fluid model solution* for
the data `dat` if, for every `t ≥ 0`: the buffer-content balance (6.1) holds; `Ẑ(t) ≥ 0`
componentwise (6.2); the departure/completion relationship `D̂ = B F̂` holds (6.3); the
completion/effort relationship `m_j F̂_j(t) = T̂_j(t)` holds for every activity `j`, equivalent to
`F̂ = M⁻¹T̂` since every `m j > 0` (6.4); `T̂` is nondecreasing with `T̂(0) = 0` (6.5); and the
capacity/Lipschitz bound (6.6) holds for every `0 ≤ s ≤ t`. -/
def IsFluidModelSolution {I J K : ℕ} (dat : FluidEquationData I J K)
    (Dh : ℝ → Fin I → ℝ) (Fh Th : ℝ → Fin J → ℝ) (Zh : ℝ → Fin I → ℝ) : Prop :=
  (∀ t : ℝ, 0 ≤ t → ∀ i, Zh t i = Zh 0 i + dat.lam i * t + ∑ j, dat.Γ i j * Fh t j - Dh t i) ∧
  (∀ t : ℝ, 0 ≤ t → ∀ i, 0 ≤ Zh t i) ∧
  (∀ t : ℝ, 0 ≤ t → ∀ i, Dh t i = ∑ j, dat.B i j * Fh t j) ∧
  (∀ t : ℝ, 0 ≤ t → ∀ j, dat.m j * Fh t j = Th t j) ∧
  (Th 0 = 0 ∧ Monotone Th) ∧
  (∀ s t : ℝ, 0 ≤ s → s ≤ t → ∀ k, ∑ j, dat.A k j * (Th t j - Th s j) ≤ dat.b k * (t - s))

end ProcessingNetworks.FluidStability


