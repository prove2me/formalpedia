-- Prove2me | Definitions.Def_ReplicableDecisions_Supplement_tournament
-- name    : ReplicableDecisions_Supplement_tournament
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:03:13.56521+00:00
-- url     : https://prove2.me/theorems/a8e828e1-38ba-49cb-8896-2469a96abe27
-- title:
--   Robust pairwise test (Lemma 6.8), maximal η-separated nets and the tournament estimate (Lemma 6.9)
-- statement:
--   For two distinct laws $Q_1\ne Q_2$ put
--   $$\psi(z)=\frac{\sqrt{Q_2(z)}-\sqrt{Q_1(z)}}{\sqrt{Q_1(z)}+\sqrt{Q_2(z)}}\quad(\psi(z)=0\text{ if both vanish}),$$
--   and let $t_\star$ be the midpoint of $\mathbb E_{Q_1}\psi$ and $\mathbb E_{Q_2}\psi$. On observations $Z_1,\dots,Z_n$ the **robust pairwise test** chooses $Q_2$ if $\frac1n\sum_i\psi(Z_i)>t_\star$ and $Q_1$ otherwise.
--
--   Let $\mathcal N\subseteq\mathcal P$ be a maximal subset whose distinct elements are at Hellinger distance greater than $\eta$, in a fixed order. Run the test on every pair of elements of $\mathcal N$ at distance at least $\theta$, all on the same sample. The **tournament estimate** $\hat Q$ is the first element of $\mathcal N$ chosen by every test in which it takes part, or the first element of $\mathcal N$ if there is none. Lemma 6.9 uses $\theta=8\eta$; the robust estimate of Theorem 6.11 uses all models and $\theta=s/2$.
--
--   **Formalization Note** $\mathcal N$ is a duplicate-free list; maximality says every model outside $\mathcal N$ is within $\eta$ of some element. Each test is oriented by the order (the earlier element plays $Q_1$), which only decides ties. A fallback model is returned for an empty list, which never occurs for a maximal net or the list of all models.
-- source:
--   Chen, Replicable Decisions in Finite Experiments: A Chain Converse and Its Limits, STOC 2027 submission (sha256 52d181db50a1641806d046c9e7d92377e64271681f0fc36c7e6be16d6dabb868), Lemma 6.8, p.32 (PDF p.34); Lemma 6.9, p.33 (PDF p.35); proof of Theorem 6.11, p.35 (PDF p.37)

import Mathlib
import Definitions.Def_ReplicableDecisions_Experiment
import Definitions.Def_ReplicableDecisions_hellinger
import Definitions.Def_ReplicableDecisions_Supplement_localDim

namespace ReplicableDecisions.Supplement

/-- **The score of the robust pairwise test** (Lemma 6.8):
`ψ(z) = (√Q₂(z) − √Q₁(z))/(√Q₁(z) + √Q₂(z))`, with `ψ(z) = 0` when both probabilities vanish. Chen,
*Replicable Decisions in Finite Experiments*, STOC 2027 submission (sha256 52d181db…), Lemma 6.8,
p.32 (PDF p.34). -/
noncomputable def psiScore {Z : Type} (Q1 Q2 : Z → ℝ) (z : Z) : ℝ :=
  if Q1 z = 0 ∧ Q2 z = 0 then 0
  else (Real.sqrt (Q2 z) - Real.sqrt (Q1 z)) / (Real.sqrt (Q1 z) + Real.sqrt (Q2 z))

/-- **The threshold** `t⋆`, the midpoint of `E_{Q₁}ψ` and `E_{Q₂}ψ` (Lemma 6.8). Chen, STOC 2027
submission (sha256 52d181db…), Lemma 6.8, p.32 (PDF p.34). -/
noncomputable def tStar {Z : Type} [Fintype Z] (Q1 Q2 : Z → ℝ) : ℝ :=
  ((∑ z, Q1 z * psiScore Q1 Q2 z) + ∑ z, Q2 z * psiScore Q1 Q2 z) / 2

/-- **The robust pairwise test chooses `Q₂`** on the sample `Z₁, …, Zₙ`: "the test chooses Q₂ if
(1/n) ∑ᵢ ψ(Zᵢ) > t⋆ and chooses Q₁ otherwise". Chen, STOC 2027 submission (sha256 52d181db…),
Lemma 6.8, p.32 (PDF p.34). -/
def choosesSecond {Z : Type} [Fintype Z] {n : ℕ} (Q1 Q2 : Z → ℝ) (x : Fin n → Z) : Prop :=
  tStar Q1 Q2 < (1 / (n : ℝ)) * ∑ r, psiScore Q1 Q2 (x r)

open Classical in
/-- **`e` is chosen by its test against `f`**, the pair oriented by position in the ordered list
`N`: the earlier element plays `Q₁`, the later one `Q₂`. Chen, STOC 2027 submission
(sha256 52d181db…), Lemma 6.9, p.33 (PDF p.35): "apply Lemma 6.8 to every pair of elements of N …,
all on the same sample".

**Formalization Note.** The page fixes the order of `N` "by a fixed rule" but not the orientation of
each test; orientation only decides ties `(1/n)∑ψ = t⋆`. Orienting by the order is one fixed rule. -/
def chosenAgainst {ι : Type*} {Z : Type} [Fintype Z] {n : ℕ} (E : Experiment ι Z) (N : List ι)
    (e f : ι) (x : Fin n → Z) : Prop :=
  if N.idxOf e < N.idxOf f then ¬ choosesSecond (E.P e) (E.P f) x
  else choosesSecond (E.P f) (E.P e) x

/-- **`e` wins every test in which it takes part:** against every other `f ∈ N` at Hellinger
distance at least `θ`. Chen, STOC 2027 submission (sha256 52d181db…), Lemma 6.9, p.33 (PDF p.35),
with `θ = 8η`; proof of Theorem 6.11, p.35 (PDF p.37), with `θ = s/2` and `N` all models. -/
def winsAll {ι : Type*} {Z : Type} [Fintype Z] {n : ℕ} (E : Experiment ι Z) (N : List ι)
    (θ : ℝ) (e : ι) (x : Fin n → Z) : Prop :=
  ∀ f ∈ N, f ≠ e → θ ≤ hellinger (E.P e) (E.P f) → chosenAgainst E N e f x

open Classical in
/-- **The tournament estimate** `Q̂`: "the first element of N that is chosen by every test in which
it takes part, or the first element of N if there is none". Chen, STOC 2027 submission
(sha256 52d181db…), Lemma 6.9, p.33 (PDF p.35), and the robust estimate `P̂` of the proof of
Theorem 6.11, p.35 (PDF p.37).

**Formalization Note.** `N` is an ordered list of model indices; tests are run between the pairs at
distance at least `θ`. The model `i₀` is returned only when `N = []`, which the theorems exclude
(a maximal net, or the list of all models, of a nonempty family is nonempty). -/
noncomputable def tournament {ι : Type*} {Z : Type} [Fintype Z] {n : ℕ}
    (E : Experiment ι Z) (N : List ι) (θ : ℝ) (i₀ : ι) (x : Fin n → Z) : ι :=
  (N.find? (fun e => decide (winsAll E N θ e x))).getD (N.headD i₀)

/-- **A maximal η-separated net, ordered** (Lemma 6.9): `N` lists distinct models, its distinct
elements are at distance greater than `η`, and no model can be added. Chen, STOC 2027 submission
(sha256 52d181db…), Lemma 6.9, p.33 (PDF p.35): "let N ⊆ P be a maximal subset whose distinct
elements are at Hellinger distance greater than η, selected and ordered by a fixed rule".

**Formalization Note.** Maximality is stated directly: every model outside `N` is within `η` of
some element of `N`. -/
def IsMaximalNet {ι : Type*} {Z : Type} [Fintype Z] (E : Experiment ι Z) (N : List ι) (η : ℝ) :
    Prop :=
  N.Nodup ∧ IsSeparated E {i | i ∈ N} η ∧ ∀ i, i ∉ N → ∃ a ∈ N, hellinger (E.P i) (E.P a) ≤ η

end ReplicableDecisions.Supplement


