-- Prove2me | Definitions.Def_MultiUnitProphet_GenBern
-- name    : MultiUnitProphet_GenBern
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:13:10.467999+00:00
-- url     : https://prove2.me/theorems/e8ed8639-a4f7-4391-a060-d07c391837c5
-- title:
--   The programs (GenBern) and their value $\phi^\star_k(n)$
-- statement:
--   For a supply $k$ and $n$ Bernoullis, the program
--
--   $$\phi^\star_k := \min_{b_1,\dots,b_n,\phi}\ \phi\quad\text{s.t. } X=\textstyle\sum_t \mathrm{Bernoulli}(b_t),\ \delta_k(X)=\mu_k(X)=\phi \qquad (\textsc{GenBern}: \min\phi \text{ s.t. } \delta=\mu=\phi)$$
--
--   and the program
--
--   $$\min\ \mu_k(X)\quad\text{s.t. } \delta_k(X)=\phi^\star_k,\ X \text{ a sum of Bernoullis} \qquad (\textsc{GenBern}: \min\mu \text{ s.t. } \delta=\phi).$$
--
--   The module defines the set of feasible values of the first program, its infimum $\phi^\star_k(n)$, and the set of feasible objective values of the second program for a constraint value $\phi$.
--
--   **Formalization Note** The value depends on $n$ and is written $\phi^\star_k(n)$. Biases range over $[0,1]^n$. The second program uses the same $n$. $\phi^\star_k(n)$ is a real infimum: for $1\le k\le n$ the feasible set is nonempty and bounded below by $0$; for $n<k$ it is empty and the infimum is the junk value $0$, so every statement about $\phi^\star_k(n)$ assumes $0<k<n$.
-- source:
--   Chawla, Devanur & Lykouris, Static pricing for multi-unit prophet inequalities, arXiv:2007.07990v4, §5.1, pp.10–11

import Mathlib
import Definitions.Def_MultiUnitProphet_PoissonBinomial

namespace MultiUnitProphet

/-- **Feasible values of (GenBern : min φ s.t. δ = µ = φ)** (Chawla, Devanur & Lykouris,
arXiv:2007.07990v4, §5.1, p.10): the values `φ` with `δ_k(X) = µ_k(X) = φ` for some sum `X` of
`n` independent Bernoullis with biases `b_1, …, b_n ∈ [0, 1]`. -/
def genBernValues (k n : ℕ) : Set ℝ :=
  {φ | ∃ b : Fin n → ℝ, (∀ t, b t ∈ Set.Icc (0 : ℝ) 1) ∧ deltaPB k b = φ ∧ muPB k b = φ}

/-- **`φ⋆_k`, the optimal value of (GenBern : min φ s.t. δ = µ = φ)** (§5.1, p.10), for `n`
Bernoullis: `φ⋆_k(n) := min_{b_1, …, b_n, φ} φ` s.t. `δ_k(X) = µ_k(X) = φ`.

**Formalization Note.** The value depends on `n`, so it is `phiStar k n`. It is the infimum of
`genBernValues k n`, a set bounded below by `0`; that set is nonempty for `1 ≤ k ≤ n` (equal
biases, by the intermediate value theorem) and empty for `n < k`, where the real `sInf` returns
the junk value `0`. Every statement about `phiStar k n` assumes `0 < k < n`, and Lemma 3
(`lemma_3`) states that the minimum is attained. -/
noncomputable def phiStar (k n : ℕ) : ℝ := sInf (genBernValues k n)

/-- **Feasible objective values of (GenBern : min µ s.t. δ = φ)** (§5.1, p.11), for the
constraint value `φ` and `n` Bernoullis: the values `µ_k(X)` over sums `X` of `n` independent
Bernoullis with biases in `[0, 1]` and `δ_k(X) = φ`.

**Formalization Note.** The paper's program has `φ = φ⋆_k` and leaves the number of Bernoullis
unspecified ("X is the sum of Bernoulli r.v.s"); it is read as the same `n` as in
(GenBern : min φ s.t. δ = µ = φ). -/
def genBernMuValues (k n : ℕ) (φ : ℝ) : Set ℝ :=
  {μ | ∃ b : Fin n → ℝ, (∀ t, b t ∈ Set.Icc (0 : ℝ) 1) ∧ deltaPB k b = φ ∧ muPB k b = μ}

end MultiUnitProphet


