-- Prove2me | Definitions.Def_IncentiveFinNet_Supplement_negotiate
-- name    : IncentiveFinNet_Supplement_negotiate
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T02:28:47.567424+00:00
-- url     : https://prove2.me/theorems/86ac752c-53d3-547e-a4f8-25820edf80a0
-- title:
--   Pairwise negotiated price (Proposition 4) and the iterates $P(t)$ of Algorithm 1
-- statement:
--   Fix a network setting with matrices $Q_i = \Psi_i^{\top}(2\gamma_i\Psi_i\Sigma_i\Psi_i^{\top})^{-1}\Psi_i$. For a price matrix $P$, the **pairwise-negotiated price** of the pair $(i,j)$ is
--
--   $$
--   P'_{ij} = \frac{e_i^{\top}Q_j(M-P)e_j - e_j^{\top}Q_i(M-P)e_i}{Q_{i;j,j}+Q_{j;i,i}} + P_{ij},
--   $$
--
--   the price at which $i$'s optimal contract size with $j$ equals $j$'s optimal size with $i$ when all other prices stay at $P$ (Proposition 4). On a prohibited pair the numerator and denominator are both $0$, and the ratio is read as $0$ (A.8), so $P'_{ij} = P_{ij}$.
--
--   **Pairwise negotiations** (Algorithm 1) start from a price matrix $P(0)$ and, in every round, compute all negotiated prices $P'$ simultaneously and set
--
--   $$
--   P(t+1) = (1-\eta)P(t) + \eta P' ,
--   $$
--
--   with a dampening factor $\eta$. These iterates are the object of Definition 6 and of Theorems 4 and 9.
--
--   **Formalization Note** `negotiatedPrice S P` is the matrix $P'$; Lean's $x/0 = 0$ implements the paper's convention on prohibited pairs. `negotiate S η P₀ t` is $P(t)$, defined for every real $\eta$ and every $P(0)$; the statements restrict $\eta$ and $P(0)$ as the paper does (Algorithm 1 starts from a skew-symmetric $P(0)$; Theorem 4 takes $\eta\in(0,\eta^*)$). The stopping rule of the loop is not modelled.
-- source:
--   Jalan, Chakrabarti, Sarkar, Incentive-Aware Models of Financial Networks, arXiv:2212.06808v3, Algorithm 1, pp.13–14; price formula of Proposition 4, A.7, p.38; convention 0/0 = 0, A.8, p.39

import Mathlib
import Definitions.Def_IncentiveFinNet_NetworkSetting
import Definitions.Def_IncentiveFinNet_Q

open Matrix

namespace IncentiveFinNet.Supplement

/-- The **pairwise-negotiated price** of Proposition 4 (arXiv:2212.06808v3, A.7, p.38), the update
of line 5 of Algorithm 1 (p.14): for the pair `(i, j)`,
`P′_ij = (e_iᵀ Q_j (M − P) e_j − e_jᵀ Q_i (M − P) e_i) / (Q_{i;j,j} + Q_{j;i,i}) + P_ij`.

**Formalization Note** On a prohibited pair (`j ∉ J_i`) numerator and denominator are both `0`
(row `i` of `Q_j` and row `j` of `Q_i` vanish), and Lean's `x / 0 = 0` gives `P′_ij = P_ij`: this is
the convention of A.8 (p.39), "both the numerator and denominator become 0, and we can define their
ratio to be 0". On the diagonal the numerator is `0`, so `P′_ii = P_ii`. -/
noncomputable def negotiatedPrice {n : ℕ} (S : NetworkSetting n) (P : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j =>
    ((Q S j * (S.M - P)) i j - (Q S i * (S.M - P)) j i) / ((Q S i) j j + (Q S j) i i) + P i j

/-- **Algorithm 1 (Pairwise Negotiations)**, Jalan, Chakrabarti, Sarkar, arXiv:2212.06808v3,
§2.2, pp.13–14: starting from a price matrix `P(0)`, in every round all pairs compute their
pairwise-negotiated prices `P′` simultaneously and
`P(t + 1) = (1 − η) P(t) + η P′`.

`negotiate S η P₀ t` is `P(t)`.

**Formalization Note** The dampening factor `η` is any real number here; Algorithm 1 takes
`η ∈ (0, 1)` "for clarity of exposition", and Remark 1 (p.16) and Theorem 4 use `η ∈ (0, η*)`. The
statements that use `negotiate` restrict `η` and `P(0)` as the paper does. The loop's stopping
rule ("while `P(t)` has not converged") is not modelled: `negotiate` is the infinite sequence of
iterates. -/
noncomputable def negotiate {n : ℕ} (S : NetworkSetting n) (η : ℝ)
    (P₀ : Matrix (Fin n) (Fin n) ℝ) : ℕ → Matrix (Fin n) (Fin n) ℝ
  | 0 => P₀
  | t + 1 => (1 - η) • negotiate S η P₀ t + η • negotiatedPrice S (negotiate S η P₀ t)

end IncentiveFinNet.Supplement


