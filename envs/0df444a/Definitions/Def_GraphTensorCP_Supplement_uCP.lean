-- Prove2me | Definitions.Def_GraphTensorCP_Supplement_uCP
-- name    : GraphTensorCP_Supplement_uCP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T04:22:18.656944+00:00
-- url     : https://prove2.me/theorems/d8d70440-49f5-44ed-803f-213f41b255a8
-- title:
--   Unstrengthened completely positive covering value $U_{\mathrm{CP}}(W)$
-- statement:
--   A real symmetric matrix $Z$ is **completely positive** if it has a finite factorization
--
--   $$
--   Z=\sum_{\nu=1}^{t} b^{(\nu)}(b^{(\nu)})^{\mathsf T},
--   \qquad b^{(\nu)}\in\mathbb R_{\ge0}^{n}.
--   $$
--
--   For a symmetric nonnegative zero-diagonal matrix $W$, the **unstrengthened completely positive covering value** is
--
--   $$
--   U_{\mathrm{CP}}(W)=\frac14\min\left\{\langle J,Z\rangle: Z\in\mathrm{CP}_n,\ Z_{i,j}\ge W_{i,j}\ (i<j)\right\},
--   $$
--
--   where $J$ is the all-one matrix and the objective includes every entry of $Z$, including its diagonal. This is the basic conic upper bound used in the graph-family applications; it has no path constraints.
--
--   **Formalization Note** Complete positivity is represented by an existentially quantified finite family of nonnegative factors. The minimum is a real infimum; the paper proves that the feasible set is nonempty and the minimum is attained on the stated domain.
-- source:
--   Zhou, Asymptotic Rank of Weighted Graph Tensors via Completely Positive Covers, arXiv:2610.34273 (version of 2026-11-03), Definition 2.32, p.28; Definition 5.2, eqs. (10)–(11), p.46

import Mathlib

namespace GraphTensorCP

namespace Supplement

/-- A real symmetric matrix is **completely positive** when it is a finite sum of outer
products `b bᵀ` with `b ≥ 0` (Zhou, *Asymptotic Rank of Weighted Graph Tensors via Completely
Positive Covers*, arXiv:2610.34273 (version of 2026-11-03), Definition 2.32, p.28, and
Definition 5.2, p.46).

**Formalization Note.** The finite number of factors is existentially quantified. Taking zero
factors represents the zero matrix. -/
def IsCompletelyPositive {n : ℕ} (Z : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∃ t : ℕ, ∃ b : Fin t → Fin n → ℝ,
    (∀ nu i, 0 ≤ b nu i) ∧ Z = fun i j => ∑ nu, b nu i * b nu j

/-- The **unstrengthened completely positive covering value** `U_CP(W)` (Zhou,
*Asymptotic Rank of Weighted Graph Tensors via Completely Positive Covers*,
arXiv:2610.34273 (version of 2026-11-03), Definition 5.2, eq. (10), p.46):
`(1/4) min {⟨J,Z⟩ | Z ∈ CP_n, Z_ij ≥ W_ij for i < j}`.

**Formalization Note.** `⟨J,Z⟩` is the sum of every entry of `Z`, including the diagonal.
The minimum is represented by `sInf`; the paper proves on p.46 that for every symmetric
nonnegative zero-diagonal `W` the feasible set is nonempty and the minimum is attained. No path
inequalities occur in this definition. -/
noncomputable def uCP {n : ℕ} (W : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  (1 / 4 : ℝ) * sInf {c : ℝ | ∃ Z : Matrix (Fin n) (Fin n) ℝ,
    IsCompletelyPositive Z ∧ (∀ i j, i < j → W i j ≤ Z i j) ∧
      c = ∑ i, ∑ j, Z i j}

end Supplement

end GraphTensorCP


