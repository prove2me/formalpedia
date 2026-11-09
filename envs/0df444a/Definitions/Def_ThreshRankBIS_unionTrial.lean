-- Prove2me | Definitions.Def_ThreshRankBIS_unionTrial
-- name    : ThreshRankBIS_unionTrial
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T05:53:46.402616+00:00
-- url     : https://prove2.me/theorems/cafd33d2-5c83-4b0b-b406-f97e23edac94
-- title:
--   Weighted coverage: the union $\bigcup_j 2^{I_j}$ and one trial of the union sampler
-- statement:
--   Let $I_1,\dots,I_M$ ($M\ge1$) be a list of finite sets, $\lambda>0$, $q=1+\lambda$. The **union** is $\mathcal J=\bigcup_j 2^{I_j}$ with weight $Z=\sum_{J\in\mathcal J}\lambda^{|J|}$; put $W_0=\sum_j q^{|I_j|}$ and let $a(J)=|\{j:J\subseteq I_j\}|$ count repeated list entries.
--
--   **One trial** of the union sampler chooses $j$ with probability $q^{|I_j|}/W_0$, includes each element of $I_j$ independently with probability $\lambda/q$ to obtain a proposal $J$, queries fresh uniform indices $\ell\in[M]$ until $J\subseteq I_\ell$, and accepts $J$ iff this first containing index is $\ell=j$. The module defines the probability that a trial proposes $J$, the law of the query stream (independent uniform indices), the first containing index, and the probability that a trial proposes **and** accepts $J$:
--
--   $$
--   \Pr[\text{accept }J]=\sum_{j:\,J\subseteq I_j}\frac{q^{|I_j|}}{W_0}\Bigl(\frac{\lambda}{q}\Bigr)^{|J|}\Bigl(1-\frac{\lambda}{q}\Bigr)^{|I_j|-|J|}\Pr\bigl[\text{first containing index}=j\bigr].
--   $$
--
--   This is the Karp–Luby–Madras weighted coverage step with which the paper counts and samples the covered family $\mathcal J_T$ without overcounting.
--
--   **Formalization Note** The list is a function on $\{1,\dots,M\}$, so repeated entries count separately. The query stream is a random element of $[M]^{\mathbb N}$ under the product of uniform laws; the finite choices of $j$ and of the subset are written as their explicit probabilities.
-- source:
--   Carlson–Kolla, Efficient Algorithms for Approximately Counting Bipartite Independent Sets in Low Threshold Rank Graphs, STOC 2027 submission (manuscript sha256 9b315e04…), Proof of Lemma 9, Sampling from the union, p.11; §3.3, p.11

import Mathlib
set_option autoImplicit false

namespace ThreshRankBIS

open Finset MeasureTheory

/-- The union `𝒥 = ⋃_j 2^{I_j}` of the subset families of a list `I_1, …, I_M` of finite sets
(§3.3, p.11; Lemma 9, p.11). Each set of the union occurs once. -/
def unionFamily {α : Type} [DecidableEq α] {M : ℕ} (I : Fin M → Finset α) : Finset (Finset α) :=
  univ.biUnion (fun j => (I j).powerset)

/-- The total weight `Z = ∑_{J ∈ 𝒥} λ^{|J|}` of the union (Lemma 9, p.11; `Z_T` of §3.3, p.11). -/
noncomputable def unionWeight {α : Type} [DecidableEq α] {M : ℕ} (I : Fin M → Finset α)
    (lam : ℝ) : ℝ :=
  ∑ J ∈ unionFamily I, lam ^ #J

/-- The multiplicity `a(J) = |{j : J ⊆ I_j}|`, counting repeated list entries (p.11). -/
def mult {α : Type} [DecidableEq α] {M : ℕ} (I : Fin M → Finset α) (J : Finset α) : ℕ :=
  #(univ.filter (fun j => J ⊆ I j))

/-- `W_0 = ∑_j q^{|I_j|}`, `q = 1 + λ` (p.11). -/
noncomputable def W0 {α : Type} {M : ℕ} (I : Fin M → Finset α) (lam : ℝ) : ℝ :=
  ∑ j, (1 + lam) ^ #(I j)

/-- The probability that the proposal step outputs `J` (p.11): choose `j` with probability
`q^{|I_j|}/W_0`, then include each vertex of `I_j` independently with probability `λ/q`. -/
noncomputable def proposalProb {α : Type} [DecidableEq α] {M : ℕ} (I : Fin M → Finset α)
    (lam : ℝ) (J : Finset α) : ℝ :=
  ∑ j, if J ⊆ I j then
      ((1 + lam) ^ #(I j) / W0 I lam) * (lam / (1 + lam)) ^ #J *
        (1 - lam / (1 + lam)) ^ (#(I j) - #J)
    else 0

/-- The law of the stream of fresh uniform query indices `ℓ_1, ℓ_2, … ∈ [M]`: the infinite
product of uniform distributions on `Fin M`. -/
noncomputable def queryMeasure (M : ℕ) [NeZero M] : Measure (ℕ → Fin M) :=
  Measure.infinitePi (fun _ : ℕ => (PMF.uniformOfFintype (Fin M)).toMeasure)

/-- The first index `ℓ_r` of a query stream `ω` with `J ⊆ I_{ℓ_r}` (`none` if there is none). -/
noncomputable def firstContaining {α : Type} [DecidableEq α] {M : ℕ} (I : Fin M → Finset α)
    (J : Finset α) (ω : ℕ → Fin M) : Option (Fin M) := by
  classical
  exact if h : ∃ r, J ⊆ I (ω r) then some (ω (Nat.find h)) else none

/-- **One trial of the union sampler of Lemma 9** (p.11): the probability that a trial proposes
`J` and accepts it. The trial chooses `j` with probability `q^{|I_j|}/W_0`, includes each vertex
of `I_j` independently with probability `λ/q` to get the proposal `J`, queries fresh uniform
indices `ℓ ∈ [M]` until `J ⊆ I_ℓ`, and accepts iff that first containing index is `ℓ = j`.

Source: Carlson–Kolla, STOC 2027 submission (manuscript sha256 9b315e04…), Proof of Lemma 9,
*Sampling from the union*, p.11.

The module also defines the union `𝒥 = ⋃_j 2^{I_j}` and its weight `Z`, the multiplicity
`a(J)`, `W_0`, the proposal probability, the query-stream law and the first containing index.

**Formalization Note.** The list is a function `Fin M → Finset α`, so repeated entries count
separately in `a(J)` and `W_0`, as the paper says. The query stream is a random element of
`ℕ → Fin M` under the product of uniform laws; the discrete choices of `j` and of the subset
are written as their explicit probabilities. -/
noncomputable def acceptProb {α : Type} [DecidableEq α] {M : ℕ} [NeZero M]
    (I : Fin M → Finset α) (lam : ℝ) (J : Finset α) : ℝ :=
  ∑ j, if J ⊆ I j then
      ((1 + lam) ^ #(I j) / W0 I lam) * (lam / (1 + lam)) ^ #J *
        (1 - lam / (1 + lam)) ^ (#(I j) - #J) *
        (queryMeasure M).real {ω | firstContaining I J ω = some j}
    else 0

end ThreshRankBIS


