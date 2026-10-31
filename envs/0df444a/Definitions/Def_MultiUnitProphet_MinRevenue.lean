-- Prove2me | Definitions.Def_MultiUnitProphet_MinRevenue
-- name    : MultiUnitProphet_MinRevenue
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:12:30.32771+00:00
-- url     : https://prove2.me/theorems/3c696a5a-34f8-411b-bedb-8d885b8312e2
-- title:
--   Two free biases and the (Min-Revenue) program
-- statement:
--   In §5.2 all but two biases are fixed. Let $\bar X$ be the sum of the fixed Bernoullis (biases $b'$), and let the two free Bernoullis have biases $b_1=1-r_1$, $b_2=1-r_2$. Write
--
--   $$Q_1=\mathbb P[\bar X=k-1],\qquad Q_2=\mathbb P[\bar X=k-2],\qquad Q_{\ge3}=\mathbb P[\bar X\le k-3].$$
--
--   The (Min-Revenue) program of Claim 1 is
--
--   $$\text{Maximize } (Q_2+Q_{\ge3})(r_1+r_2)+Q_1r_1r_2\quad\text{s.t. } r_1,r_2\in[0,1],\ \ r_1r_2(Q_1-Q_2)+(r_1+r_2)Q_2=\phi-Q_{\ge3}\ \ (5.1).$$
--
--   The module defines the bias vector of $\bar X+B_1+B_2$, the three probabilities, the objective and the feasible set.
--
--   **Formalization Note** The bias vector is `Fin.append b' ![1 - r1, 1 - r2]`. $Q_2=0$ for $k<2$ and $Q_{\ge3}=0$ for $k\le2$ (empty events), written without truncated subtraction. The constraint value $\phi$ is a parameter (the paper's $\phi^\star_k$).
-- source:
--   Chawla, Devanur & Lykouris, Static pricing for multi-unit prophet inequalities, arXiv:2007.07990v4, §5.2, Claim 1, pp.11–12

import Mathlib
import Definitions.Def_CommitteeVoting_SingleVoter_PoissonBinomial

namespace MultiUnitProphet

/-- **Biases of `X = X̄ + B_1 + B_2`** (Chawla, Devanur & Lykouris, arXiv:2007.07990v4, §5.2,
pp.11–12): the `m` fixed biases `b'` of the Bernoullis forming `X̄`, followed by the two free
biases `b_1 = 1 − r_1` and `b_2 = 1 − r_2` (`r_i` is the "rate" of the `i`-th free Bernoulli). -/
def twoBiasExtend {m : ℕ} (b' : Fin m → ℝ) (r1 r2 : ℝ) : Fin (m + 2) → ℝ :=
  Fin.append b' ![1 - r1, 1 - r2]

/-- **`Q_1 = P[X̄ = k − 1]`** (§5.2, p.12), for `X̄` the sum of independent Bernoullis with
biases `b'`. Used for `k ≥ 1`. -/
noncomputable def Qone {m : ℕ} (k : ℕ) (b' : Fin m → ℝ) : ℝ :=
  CommitteeVoting.SingleVoter.pbPMF b' Finset.univ (k - 1)

/-- **`Q_2 = P[X̄ = k − 2]`** (§5.2, p.12).

**Formalization Note.** For `k < 2` the event is empty and `Q_2 = 0`; the `if` avoids reading
`k − 2` as a truncated natural number. -/
noncomputable def Qtwo {m : ℕ} (k : ℕ) (b' : Fin m → ℝ) : ℝ :=
  if 2 ≤ k then CommitteeVoting.SingleVoter.pbPMF b' Finset.univ (k - 2) else 0

/-- **`Q_{≥3} = P[X̄ ≤ k − 3]`** (§5.2, p.12): `Σ_{j=0}^{k−3} P[X̄ = j]`.

**Formalization Note.** Written as a sum over `j < k − 2`; for `k ≤ 2` the range is empty and
`Q_{≥3} = 0`, as the event `X̄ ≤ k − 3 < 0` is empty. -/
noncomputable def Qge3 {m : ℕ} (k : ℕ) (b' : Fin m → ℝ) : ℝ :=
  ∑ j ∈ Finset.range (k - 2), CommitteeVoting.SingleVoter.pbPMF b' Finset.univ j

/-- **Objective of the (Min-Revenue) program** (Claim 1, p.12):
`(Q_2 + Q_{≥3}) · (r_1 + r_2) + Q_1 r_1 r_2`, to be maximized. -/
def minRevObj (Q1 Q2 Q3 : ℝ) (r : ℝ × ℝ) : ℝ :=
  (Q2 + Q3) * (r.1 + r.2) + Q1 * r.1 * r.2

/-- **Feasible set of the (Min-Revenue) program** (Claim 1, p.12): `r_1, r_2 ∈ [0, 1]` and
`r_1 r_2 · (Q_1 − Q_2) + (r_1 + r_2) · Q_2 = φ − Q_{≥3}` (5.1), for a constant value `φ`
(the paper's `φ⋆_k`). -/
def minRevFeasible (Q1 Q2 Q3 φ : ℝ) : Set (ℝ × ℝ) :=
  {r | r.1 ∈ Set.Icc (0 : ℝ) 1 ∧ r.2 ∈ Set.Icc (0 : ℝ) 1 ∧
    r.1 * r.2 * (Q1 - Q2) + (r.1 + r.2) * Q2 = φ - Q3}

end MultiUnitProphet


