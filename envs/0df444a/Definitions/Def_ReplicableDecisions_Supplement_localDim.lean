-- Prove2me | Definitions.Def_ReplicableDecisions_Supplement_localDim
-- name    : ReplicableDecisions_Supplement_localDim
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:02:41.930569+00:00
-- url     : https://prove2.me/theorems/e574a710-d8a3-4170-afda-f971a2b6b1c0
-- title:
--   Hellinger balls, local packing numbers $\mathrm{Pack}(Q,r;\eta)$ and the local packing dimension $\mathsf D(\eta)$ (Definition 6.7)
-- statement:
--   For a model $Q$ of the family and $r,\eta>0$, let $B(Q,r)=\{P\in\mathcal P:h(P,Q)\le r\}$, and let $\mathrm{Pack}(Q,r;\eta)$ be the largest size of a subset of $B(Q,r)$ whose distinct elements are at Hellinger distance greater than $\eta$. The **local packing dimension** is
--   $$\mathsf D(\eta)=\max_{Q\in\mathcal P}\ \max_{j\ge0}\ 4^{-j}\log\mathrm{Pack}\big(Q,2^{j+4}\eta;\eta\big),\qquad \mathsf D_\rho=\mathsf D(s_\rho/9).$$
--
--   It replaces the global count $\log M$ in the upper bound of Theorem 6.10; $0\le\mathsf D(\eta)\le\log M$.
--
--   **Formalization Note** The maxima are real suprema of a bounded family (over $j\in\mathbb N$ and the finite family), equal to the page's attained maxima. $h$ is the published normalized Hellinger distance.
-- source:
--   Chen, Replicable Decisions in Finite Experiments: A Chain Converse and Its Limits, STOC 2027 submission (sha256 52d181db50a1641806d046c9e7d92377e64271681f0fc36c7e6be16d6dabb868), Definition 6.7, p.32 (PDF p.34)

import Mathlib
import Definitions.Def_ReplicableDecisions_Experiment
import Definitions.Def_ReplicableDecisions_hellinger

namespace ReplicableDecisions.Supplement

/-- **The Hellinger ball** `B(Q, r) = {P ∈ P : h(P, Q) ≤ r}` within the family. Chen, *Replicable
Decisions in Finite Experiments*, STOC 2027 submission (sha256 52d181db…), §6.2, p.32 (PDF p.34).

**Formalization Note.** Models are referred to by their index; `q` is the index of `Q`. -/
def hBall {ι : Type*} {Z : Type} [Fintype Z] (E : Experiment ι Z) (q : ι) (r : ℝ) : Set ι :=
  {i | hellinger (E.P i) (E.P q) ≤ r}

/-- **η-separated sets of models:** distinct elements are at Hellinger distance greater than `η`.
Chen, STOC 2027 submission (sha256 52d181db…), §6.2, p.32 (PDF p.34). -/
def IsSeparated {ι : Type*} {Z : Type} [Fintype Z] (E : Experiment ι Z) (S : Set ι) (η : ℝ) :
    Prop :=
  ∀ i ∈ S, ∀ j ∈ S, i ≠ j → η < hellinger (E.P i) (E.P j)

open Classical in
/-- **The local packing number** `Pack(Q, r; η)`: "the largest size of a subset of B(Q, r) whose
distinct elements are at Hellinger distance greater than η". Chen, STOC 2027 submission
(sha256 52d181db…), §6.2, p.32 (PDF p.34).

**Formalization Note.** The maximum over the finitely many subsets, as `Finset.sup` of the
cardinalities; the empty set is a candidate, so the value is `0` only when no model lies in the
ball (never the case when `r ≥ 0`, since `Q ∈ B(Q, r)`). -/
noncomputable def pack {ι : Type*} [Fintype ι] {Z : Type} [Fintype Z] (E : Experiment ι Z)
    (q : ι) (r η : ℝ) : ℕ :=
  (Finset.filter (fun S : Finset ι => (S : Set ι) ⊆ hBall E q r ∧ IsSeparated E (S : Set ι) η)
    Finset.univ).sup Finset.card

/-- **The local packing dimension** (Definition 6.7):
`D(η) = max_{Q∈P} max_{j≥0} 4^{−j} log Pack(Q, 2^{j+4}η; η)`. Chen, STOC 2027 submission
(sha256 52d181db…), Definition 6.7, p.32 (PDF p.34). The profile `D_ρ` is `localDim E (s_ρ / 9)`.

**Formalization Note.** The maxima are real suprema. The family is bounded (`0 ≤` each term
`≤ log M` when `η > 0`, since `1 ≤ Pack ≤ M`), so the inner supremum over `j ∈ ℕ` is the page's
maximum (attained: `Pack` is nondecreasing in `r` and bounded, so it is eventually constant); the
outer one is over the finite nonempty family. The page states `0 ≤ D(η) ≤ log M`. -/
noncomputable def localDim {ι : Type*} [Fintype ι] {Z : Type} [Fintype Z] (E : Experiment ι Z)
    (η : ℝ) : ℝ :=
  ⨆ q : ι, ⨆ j : ℕ, (1 / 4 : ℝ) ^ j * Real.log (pack E q (2 ^ (j + 4) * η) η)

end ReplicableDecisions.Supplement


