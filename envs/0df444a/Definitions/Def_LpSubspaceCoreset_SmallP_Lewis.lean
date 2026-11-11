-- Prove2me | Definitions.Def_LpSubspaceCoreset_SmallP_Lewis
-- name    : LpSubspaceCoreset_SmallP_Lewis
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T01:46:28.445298+00:00
-- url     : https://prove2.me/theorems/5ec47bf0-77f1-44e5-aa26-b46ddb6af779
-- title:
--   Leverage scores, ℓp Lewis weights and the Cohen–Peng iteration
-- statement:
--   For $M\in\mathbb R^{N\times c}$ with rows $m_i^\top$, the **leverage score** of row $i$ is $\tau_i(M)=m_i^\top(M^\top M)^\dagger m_i$ (Definition 2.7), which equals $\|P_{\mathrm{col}(M)}e_i\|_2^2$, the squared norm of the projection of the $i$-th standard basis vector onto the column space of $M$.
--
--   The **ℓp Lewis weights** of $M$ (Definition 2.8) are positive numbers $w_1,\dots,w_N$ with
--   $$w_i=\tau_i\big(W^{1/2-1/p}M\big),\qquad W=\operatorname{diag}(w_1,\dots,w_N),\qquad(2.2)$$
--   equivalently $m_i^\top(M^\top W^{1-2/p}M)^{-1}m_i=w_i^{2/p}$. Following §2.3, zero rows are deleted before computing Lewis weights and restored with weight zero afterward. Because leverage scores depend only on the column space, the Lewis weights of the rows of a rank-$r$ matrix $B\in\mathbb R^{n\times d}$ are those of $BU$ for any $d\times r$ matrix $U$ whose columns form a basis of the row space of $B$ (the basis-independent convention of p. 11). $\tilde w$ is an **$\alpha$-approximation** of $w$ if $\alpha^{-1}w_i\le\tilde w_i\le\alpha w_i$ for every positive-weight row.
--
--   **Algorithm 1** (Cohen–Peng) starts from $w^{(0)}=\mathbf 1$ and sets $w^{(t)}_i=\big((w^{(t-1)}_i)^{2/p-1}\tau^{(t)}_i\big)^{p/2}$, where $\tau^{(t)}$ is a constant-factor (factor $\beta$) approximation of the leverage scores of $(W^{(t-1)})^{1/2-1/p}M$.
--
--   **Formalization Note** `leverage` uses the projection form (no pseudoinverse needed; the value equals Definition 2.7 for every $M$). `IsLewisWeights p M w` says: a zero row has weight $0$, a nonzero row a positive weight satisfying (2.2) for the reweighted matrix (zero rows of $W^{1/2-1/p}M$ do not change the other leverage scores). The leverage-score approximations of Algorithm 1 are an arbitrary sequence `τ` constrained by `IsCPChoice`.
-- source:
--   Lin, Mirrokni, Woodruff, Nearly Optimal Strong Coresets for ℓp Subspace Approximation, arXiv:2608.26047 (held PDF of 2026-11-03, sha256 4c61606e…), pp. 10–11, §2.3, Definitions 2.7–2.8, Algorithm 1

import Mathlib

namespace LpSubspaceCoreset.SmallP

/-!
# Leverage scores, ℓp Lewis weights and the Cohen–Peng iteration

Lin, Mirrokni, Woodruff, arXiv:2608.26047, §2.3, Definitions 2.7 and 2.8 (p. 10), the
conventions of pp. 10–11 and Algorithm 1 (p. 11).

* **Leverage scores** (Definition 2.7). For `M ∈ ℝ^{N×r}` the paper writes
  `τ_i(M) = m_i^⊤ (M^⊤M)^† m_i`. Since `M (M^⊤M)^† M^⊤` is the orthogonal projector onto the
  column space of `M`, this is `τ_i(M) = ‖P_{col(M)} e_i‖₂²`, which is the form used here (no
  pseudoinverse is needed, and the value is the same for every `M`).
* **Lewis weights** (Definition 2.8, equation (2.2)): `w_i = τ_i(W^{1/2−1/p} M)`, `W = diag(w)`,
  with positive `w_i`. The §2.3 convention "zero rows are deleted before computing Lewis weights
  and restored with weight zero afterward" is built in: a zero row has weight `0`, a nonzero row
  a positive weight satisfying (2.2). Zero rows of `W^{1/2−1/p}M` do not change the leverage
  scores of the other rows, so this is (2.2) for the matrix with its zero rows deleted.
* The predicate is stated for any `M ∈ ℝ^{N×c}`. Because the leverage score depends only on the
  column space, the Lewis weights of the rows of a rank-`r` matrix `B ∈ ℝ^{n×d}` defined this way
  are exactly the Lewis weights of `BU` for any `d × r` matrix `U` whose columns are a basis of
  `rowspan(B)` (the basis-independent convention of p. 11): `col(W'B) = col(W'BU)`.
* **Algorithm 1** (Cohen–Peng): `w^{(0)} = 1`, and
  `w^{(t)}_i = ((w^{(t−1)}_i)^{2/p−1} τ^{(t)}_i)^{p/2}`, where `τ^{(t)}` is any constant-factor
  (factor `β`) approximation of the leverage scores of `(W^{(t−1)})^{1/2−1/p} M`. The choice of
  `τ^{(t)}` is an arbitrary sequence satisfying `IsCPChoice`.
-/

/-- Definition 2.7: the leverage score `τ_i(M) = ‖P_{col(M)} e_i‖₂² = m_i^⊤ (M^⊤M)^† m_i`. -/
noncomputable def leverage {N c : ℕ} (M : Matrix (Fin N) (Fin c) ℝ) (i : Fin N) : ℝ :=
  ‖(LinearMap.range (Matrix.toEuclideanLin M)).starProjection (EuclideanSpace.single i 1)‖ ^ 2

/-- `W^{1/2−1/p} M` for the row weights `w`: row `j` scaled by `w_j^{1/2−1/p}`. -/
noncomputable def lewisReweight {N c : ℕ} (p : ℝ) (w : Fin N → ℝ)
    (M : Matrix (Fin N) (Fin c) ℝ) : Matrix (Fin N) (Fin c) ℝ :=
  fun j => (w j) ^ ((1 : ℝ) / 2 - 1 / p) • M j

/-- Definition 2.8 with the §2.3 zero-row convention: `w` are the ℓp Lewis weights of the rows
of `M`. Zero rows get weight `0`; every nonzero row has a positive weight with
`w_i = τ_i(W^{1/2−1/p} M)` (equation (2.2)). -/
def IsLewisWeights {N c : ℕ} (p : ℝ) (M : Matrix (Fin N) (Fin c) ℝ) (w : Fin N → ℝ) : Prop :=
  ∀ i, (M i = 0 → w i = 0) ∧ (M i ≠ 0 → 0 < w i ∧ w i = leverage (lewisReweight p w M) i)

/-- `w̃` is an `α`-approximation to the Lewis weights `w`:
`α⁻¹ w_i ≤ w̃_i ≤ α w_i` for every positive-weight row. -/
def IsApproxLewis {N : ℕ} (α : ℝ) (wt w : Fin N → ℝ) : Prop :=
  ∀ i, 0 < w i → α⁻¹ * w i ≤ wt i ∧ wt i ≤ α * w i

/-- Algorithm 1, run with the leverage-score estimates `τ (t)` used at iteration `t ≥ 1`:
`w^{(0)} = 1` and `w^{(t)}_i = ((w^{(t−1)}_i)^{2/p−1} τ^{(t)}_i)^{p/2}`. -/
noncomputable def cohenPeng {N : ℕ} (p : ℝ) (τ : ℕ → Fin N → ℝ) : ℕ → Fin N → ℝ
  | 0 => fun _ => 1
  | t + 1 => fun i => ((cohenPeng p τ t i) ^ (2 / p - 1) * τ (t + 1) i) ^ (p / 2)

/-- Line 4 of Algorithm 1: at every iteration `t ≥ 1`, `τ^{(t)}` is a factor-`β` approximation of
the leverage scores of `(W^{(t−1)})^{1/2−1/p} M`. -/
def IsCPChoice {N c : ℕ} (p β : ℝ) (M : Matrix (Fin N) (Fin c) ℝ) (τ : ℕ → Fin N → ℝ) :
    Prop :=
  ∀ t : ℕ, ∀ i : Fin N,
    β⁻¹ * leverage (lewisReweight p (cohenPeng p τ t) M) i ≤ τ (t + 1) i ∧
      τ (t + 1) i ≤ β * leverage (lewisReweight p (cohenPeng p τ t) M) i

end LpSubspaceCoreset.SmallP


