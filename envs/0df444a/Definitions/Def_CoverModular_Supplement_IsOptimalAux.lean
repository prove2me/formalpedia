-- Prove2me | Definitions.Def_CoverModular_Supplement_IsOptimalAux
-- name    : CoverModular_Supplement_IsOptimalAux
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T01:16:58.254802+00:00
-- url     : https://prove2.me/theorems/a18e93e1-3754-4037-9616-b91a0a4e622d
-- title:
--   Optimal solution $\alpha^k$ of the auxiliary LP (29)
-- statement:
--   Given a vector $\bar\alpha\in\mathbb R^m$ (in the paper, $\bar\alpha^{\mathcal S}$) and a subset index $k\in\mathcal U$, the **auxiliary LP** is
--
--   $$
--   \min_\alpha\ \sum_ib_i\alpha_i\quad\text{s.t.}\quad\sum_ia_{ij}\alpha_i\ge p_j-\sum_ia_{ij}\bar\alpha_i\ (j\in J_k),\qquad\alpha_i\ge0\ \ \forall i.\tag{29}
--   $$
--
--   A vector $\alpha$ is **feasible** (`IsFeasibleAux`) if it satisfies these constraints. It is an **optimal solution** if, in addition, $\sum_ib_i\alpha_i\le\sum_ib_i\beta_i$ for every feasible $\beta$. Lemma 3 combines the optimal solutions $\alpha^k$ into a dual solution for $h(\mathcal S\cup\mathcal T)$, and Lemma 4 bounds the marginal gain of $k$ from below by their values.
-- source:
--   L. DeValve, S. Pekeč, Y. Wei, Approximate submodularity in network design problems, SSRN 3844987 (author's copy, https://ssrn.com/abstract=3844987), Appendix A.3, Lemma 3, display (29), p.41

import Mathlib

namespace CoverModular.Supplement

/-- Feasibility in the **auxiliary LP (29)** for the subset index `k` (DeValve, Pekeč, Wei,
SSRN 3844987, Appendix A.3, Lemma 3, display (29), p.41), given a vector `ᾱ` (in the paper
`ᾱ^S`): `∑_i a_ij α_i ≥ p_j − ∑_i a_ij ᾱ_i` for `j ∈ J_k`, and `α_i ≥ 0` for all `i`. -/
def IsFeasibleAux {U : Type*} {m n : ℕ} (a : Fin m → Fin n → ℕ) (p : Fin n → ℝ)
    (J : U → Finset (Fin n)) (αbar : Fin m → ℝ) (k : U) (α : Fin m → ℝ) : Prop :=
  (∀ i, 0 ≤ α i) ∧ ∀ j ∈ J k, p j - ∑ i, (a i j : ℝ) * αbar i ≤ ∑ i, (a i j : ℝ) * α i

/-- `α` is an **optimal solution of the auxiliary LP (29)** for the subset index `k`
(DeValve, Pekeč, Wei, SSRN 3844987, Appendix A.3, Lemma 3, display (29), p.41):
`min_α ∑_i b_i α_i` s.t. `∑_i a_ij α_i ≥ p_j − ∑_i a_ij ᾱ_i` (`j ∈ J_k`), `α_i ≥ 0` (all `i`).
`α` is feasible and `∑_i b_i α_i ≤ ∑_i b_i β_i` for every feasible `β`. -/
def IsOptimalAux {U : Type*} {m n : ℕ} (a : Fin m → Fin n → ℕ) (p : Fin n → ℝ)
    (b : Fin m → ℝ) (J : U → Finset (Fin n)) (αbar : Fin m → ℝ) (k : U) (α : Fin m → ℝ) :
    Prop :=
  IsFeasibleAux a p J αbar k α ∧
    ∀ β, IsFeasibleAux a p J αbar k β → ∑ i, b i * α i ≤ ∑ i, b i * β i

end CoverModular.Supplement


