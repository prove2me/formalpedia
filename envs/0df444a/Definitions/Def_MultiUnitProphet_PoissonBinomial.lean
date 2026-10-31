-- Prove2me | Definitions.Def_MultiUnitProphet_PoissonBinomial
-- name    : MultiUnitProphet_PoissonBinomial
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:12:30.699323+00:00
-- url     : https://prove2.me/theorems/3d92cc7a-b1d0-4199-8417-0574ff3593d5
-- title:
--   $\delta_k$ and $\mu_k$ of a sum of independent Bernoullis
-- statement:
--   Let $X=\sum_{t=1}^n B_t$ with independent $B_t\sim\mathrm{Bernoulli}(b_t)$, $b_t\in[0,1]$ (a Poisson-binomial variable). Then
--
--   $$\delta_k(X)=\sum_{j=0}^{k-1}\mathbb P[X=j],\qquad \mu_k(X)=\frac1k\sum_{j=0}^{n}\min\{j,k\}\,\mathbb P[X=j].$$
--
--   These are the quantities of the programs (GenBern) of §5 and of the binomials $\mathrm{Bin}(n,\lambda)$ (bias $\lambda/n$) of §5.4.
--
--   **Formalization Note** $\mathbb P[X=j]$ is the published counting formula `CommitteeVoting.SingleVoter.pbPMF b Finset.univ j`; biases are indexed by `Fin n`.
-- source:
--   Chawla, Devanur & Lykouris, Static pricing for multi-unit prophet inequalities, arXiv:2007.07990v4, (3.1)–(3.2), p.7; §5.1, p.10

import Mathlib
import Definitions.Def_CommitteeVoting_SingleVoter_PoissonBinomial

namespace MultiUnitProphet

/-- **`δ_k(X)` for a sum `X` of independent Bernoullis with biases `b_1, …, b_n`**
(Chawla, Devanur & Lykouris, arXiv:2007.07990v4, (3.1), p.7, as used in §5.1, p.10):
`δ_k(X) = P[X ≤ k − 1] = Σ_{j=0}^{k−1} P[X = j]`.

**Formalization Note.** `P[X = j]` is the published Poisson-binomial pmf
`CommitteeVoting.SingleVoter.pbPMF b Finset.univ j`. -/
noncomputable def deltaPB {n : ℕ} (k : ℕ) (b : Fin n → ℝ) : ℝ :=
  ∑ j ∈ Finset.range k, CommitteeVoting.SingleVoter.pbPMF b Finset.univ j

/-- **`µ_k(X)` for a sum `X` of independent Bernoullis with biases `b_1, …, b_n`**
(arXiv:2007.07990v4, (3.2), p.7, as used in §5.1, p.10):
`µ_k(X) = (1/k) E[min{X, k}] = (1/k) Σ_{j=0}^{n} min{j, k} P[X = j]`.

**Formalization Note.** `P[X = j]` is `CommitteeVoting.SingleVoter.pbPMF b Finset.univ j`; `X`
takes values in `{0, …, n}`. -/
noncomputable def muPB {n : ℕ} (k : ℕ) (b : Fin n → ℝ) : ℝ :=
  (1 / (k : ℝ)) * ∑ j ∈ Finset.range (n + 1),
    ((min j k : ℕ) : ℝ) * CommitteeVoting.SingleVoter.pbPMF b Finset.univ j

end MultiUnitProphet


