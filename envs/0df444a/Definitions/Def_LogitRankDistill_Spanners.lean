-- Prove2me | Definitions.Def_LogitRankDistill_Spanners
-- name    : LogitRankDistill_Spanners
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T05:58:02.189215+00:00
-- url     : https://prove2.me/theorems/64256369-c491-420c-addd-b8e478d52ce8
-- title:
--   The weighted norm ‖·‖_{2,Q}, (B, R, ε)-bounded rank-d vector sequences, β-barycentric and (η, β)-distributional spanners
-- statement:
--   For a weight vector $Q$ on a finite index set, $\|v\|_{2,Q}=\sqrt{\sum_iQ(i)v(i)^2}$ (§4.1).
--
--   Vectors $L_1,\dots,L_m\in\mathbb R^N$ are **$(B,R,\varepsilon)$-bounded of rank $d$** with respect to indices $I_1,\dots,I_m$ (Definition 5.1) if there are $\Phi\in\mathbb R^{N\times d}$ whose rows have Euclidean norm at most $R$ and $v_1,\dots,v_m\in\mathbb R^d$ with $\|v_j\|_2\le B$ such that $|(L_j)_{I_k}-(\Phi v_j)_{I_k}|\le\varepsilon$ for all $k\le j\le m$.
--
--   $v_1,\dots,v_d$ is a **$\beta$-barycentric spanner** for $S\subseteq\mathbb R^N$ (Definition 5.2) if every $w\in S$ is $\sum_ic_iv_i$ with $\|c\|_\infty\le\beta$.
--
--   $B_1,\dots,B_d$ is an **$(\eta,\beta)$-distributional spanner** for a distribution $P$ of vectors (Definition 5.3) if with probability at least $1-\eta$ over $L\sim P$ there is $c\in\mathbb R^d$ with $\|c\|_\infty\le\beta$ and $L=\sum_ic_iB_i$.
--
--   **Formalization Note.** Vectors of $\mathbb R^N$ are functions on an index type (`Fin N`, or a finite set of futures inside the algorithm). The distributional spanner is stated for the law of a random vector $X$ under a probability measure $P$ (a distribution on $\mathbb R^N$ is $X=\mathrm{id}$), as: the outer probability of $\{X$ not representable$\}$ is at most $\eta$. The published `StochLinOpt_ConfBall2_IsBarycentricSpanner` fixes $\beta=1$, $d=n$ and requires the spanner to lie in the set, so it is not reused.
-- source:
--   Golowich, Liu, Shetty, Provably Distilling from Modern Language Models via Low Logit Rank, manuscript of November 3, 2026 (arXiv:2512.09892; sha256 2ce0606e…), p. 18 (weighted norm); p. 21 Definition 5.1; p. 22 Definitions 5.2, 5.3

import Mathlib

namespace LogitRankDistill

/-!
# Approximately low-rank vector sequences, barycentric and distributional spanners

Golowich, Liu, Shetty, *Provably Distilling from Modern Language Models via Low Logit Rank*,
manuscript of November 3, 2026 (arXiv:2512.09892; sha256 2ce0606e…): §4.1 p. 18 (the weighted
norm `‖·‖_{2,Q}`), §5.1 pp. 21–23 (Definitions 5.1, 5.2, 5.3).

Vectors of `ℝ^N` are functions `ι → ℝ` on an index type `ι` (`Fin N` for `ℝ^N`; a finite set of
futures inside the algorithm). Spanner members are indexed by `Fin d`.
-/

/-- The `Q`-weighted norm `‖v‖_{2,Q} = √(∑_i Q(i) v(i)²)` (§4.1, p. 18). -/
noncomputable def wnorm {ι : Type*} [Fintype ι] (Q : ι → ℝ) (v : ι → ℝ) : ℝ :=
  Real.sqrt (∑ i, Q i * v i ^ 2)

/-- Vectors `L_1, …, L_m ∈ ℝ^ι` are **`(B, R, ε)`-bounded of rank `d`** with respect to indices
`I_1, …, I_m ∈ ι` (Definition 5.1): there are a matrix `Φ ∈ ℝ^{ι × d}` (rows `Φ i`) whose rows
have Euclidean norm at most `R`, and vectors `v_1, …, v_m ∈ ℝ^d` with `‖v_j‖₂ ≤ B`, such that
`|(L_j)_{I_k} − (Φ v_j)_{I_k}| ≤ ε` for all `k ≤ j ≤ m`. -/
def IsBoundedRankSeq {ι : Type*} {m : ℕ} (B R ε : ℝ) (d : ℕ) (L : Fin m → ι → ℝ)
    (I : Fin m → ι) : Prop :=
  ∃ (Φ : ι → EuclideanSpace ℝ (Fin d)) (v : Fin m → EuclideanSpace ℝ (Fin d)),
    (∀ i, ‖Φ i‖ ≤ R) ∧ (∀ j, ‖v j‖ ≤ B) ∧
    ∀ k j : Fin m, k ≤ j → |L j (I k) - inner ℝ (Φ (I k)) (v j)| ≤ ε

/-- `v_1, …, v_d` is a **`β`-barycentric spanner** for `S ⊆ ℝ^ι` (Definition 5.2): every
`w ∈ S` is `∑_i c_i v_i` for some `c ∈ ℝ^d` with `‖c‖_∞ ≤ β`. The `v_i` need not lie in `S`. -/
def IsBarySpanner {ι : Type*} {d : ℕ} (β : ℝ) (v : Fin d → ι → ℝ) (S : Set (ι → ℝ)) : Prop :=
  ∀ w ∈ S, ∃ c : Fin d → ℝ, (∀ i, |c i| ≤ β) ∧ w = ∑ i, c i • v i

/-- `B_1, …, B_d` is an **`(η, β)`-distributional spanner** for the distribution of the random
vector `X` under the probability measure `P` (Definition 5.3): with probability at least `1 − η`
over `ω ∼ P` there is `c ∈ ℝ^d` with `‖c‖_∞ ≤ β` and `X ω = ∑_i c_i B_i`. It is stated as: the
(outer) probability of the complementary event is at most `η`. A distribution `P ∈ Δ(ℝ^N)` is the
case `X = id`. -/
def IsDistSpanner {Ω ι : Type*} [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
    (X : Ω → ι → ℝ) {d : ℕ} (B : Fin d → ι → ℝ) (η β : ℝ) : Prop :=
  P {ω | ¬ ∃ c : Fin d → ℝ, (∀ i, |c i| ≤ β) ∧ X ω = ∑ i, c i • B i} ≤ ENNReal.ofReal η

end LogitRankDistill


