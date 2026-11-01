-- Prove2me | Definitions.Def_RecoveringBandits_IsRSRun
-- name    : RecoveringBandits_IsRSRun
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T07:55:09.044341+00:00
-- url     : https://prove2.me/theorems/af59f409-3196-4418-b95d-e1e0b1f4dc8c
-- title:
--   Outputs of the rounding–scheduling procedure R-S (Algorithm 1)
-- statement:
--   Fix $x\in[0,1]^N$, $K$ and $a\ge1$, and let $d_i$ be the rounding (4) of $x_i$. For $j\in[a]$ let $I_j=\{i: d_i\in D_j\}$ and $K_j=\sum_{i\in I_j}1/d_i$. A policy $\pi$ is an **output of R-S$(x,K,a)$** when there are
--
--   1. for each $j\in[a]$, pairwise disjoint groups with union $I_j$, at most $\lceil K_j\rceil$ of them, each with $\sum_{i\in G}1/d_i\le1$ (Lemma 4, first bullet);
--   2. offsets $o_i\in(-d_i,0]$ making each group a 1-PPP: no period $t\ge1$ is a pull time of two arms of one group (Lemma 4, second bullet);
--   3. a selection of $\min(K,\text{number of groups})$ groups whose total long-run average reward $\sum_{i\in G}R_i(d_i)/d_i$ is maximal among selections of that size (line 12, "top $K$");
--
--   and $\pi$ pulls each arm of a selected group with period $d_i$ and offset $o_i$, and never pulls the other arms.
--
--   **Formalization Note** The procedure's internal choices (the grouping, the offsets, ties in the top-$K$ selection) are left free, so the relation describes every output of every run. Groups are tagged by their $j$; a set of groups merges duplicate empty groups, which only lowers the count.
-- source:
--   Simchi-Levi–Zheng–Zhu, Offline Planning and Online Learning under Recovering Rewards, arXiv:2106.14813v2, §4.2, Algorithm 1, pp.12–13; Lemma 4, pp.12–13

import Mathlib
import Definitions.Def_RecoveringBandits_roundUp
import Definitions.Def_RecoveringBandits_PPP

namespace RecoveringBandits

/-- The rounded period `d_i` of (4) as a natural number (arXiv:2106.14813v2, §4.2, p.12).

**Formalization Note.** `roundUp a (x i) = ⊤` (the paper's `d_i = +∞`) is sent to `0`; `dnat` is
only read for arms in some `I_j`, whose period is finite and `≥ 1`. -/
noncomputable def dnat {N : ℕ} (a : ℕ) (x : Fin N → ℝ) (i : Fin N) : ℕ :=
  (roundUp a (x i)).untopD 0

open Classical in
/-- **`I_j = {i : d_i ∈ D_j}`** (arXiv:2106.14813v2, Lemma 4, p.12; Algorithm 1 line 8, p.13). -/
noncomputable def Ij {N : ℕ} (a : ℕ) (x : Fin N → ℝ) (j : ℕ) : Finset (Fin N) :=
  Finset.univ.filter (fun i => ∃ n : ℕ, roundUp a (x i) = (n : WithTop ℕ) ∧ n ∈ Dj j)

/-- **`K_j = ∑_{i ∈ I_j} 1/d_i`** (arXiv:2106.14813v2, Lemma 4, p.12). -/
noncomputable def Kj {N : ℕ} (a : ℕ) (x : Fin N → ℝ) (j : ℕ) : ℝ :=
  ∑ i ∈ Ij a x j, 1 / (dnat a x i : ℝ)

open Classical in
/-- **A 1-PPP on a set of arms `G`** with periods `d` and offsets `o`: every offset is in
`(−d_i, 0]` (Definition 1 (i), p.9) and no period `t ≥ 1` is a pull time of two arms of `G`
(Definition 2 with `K = 1`, p.9). -/
def IsOnePPPOn {N : ℕ} (d : Fin N → ℕ) (o : Fin N → ℤ) (G : Finset (Fin N)) : Prop :=
  (∀ i ∈ G, -(d i : ℤ) < o i ∧ o i ≤ 0) ∧
    ∀ t : ℕ, 1 ≤ t → (G.filter (fun i => (t : ℤ) ≡ o i [ZMOD (d i : ℤ)])).card ≤ 1

/-- **The grouping of Step 2 of R-S** (arXiv:2106.14813v2, §4.2, Step 2, pp.12–13; Lemma 4,
p.13; Algorithm 1 lines 7–9, p.13). For each `j ∈ [a]`, `𝒢 j` is a family of pairwise disjoint
sets whose union is `I_j`, with at most `s_j = ⌈K_j⌉` members (Lemma 4, first bullet, and line 8),
each with frequency sum `∑_{i ∈ G} 1/d_i ≤ 1` (Lemma 4, first bullet), and the offsets `o` make each
member a 1-PPP pulling arm `i` every `d_i` periods (Lemma 4, second bullet; line 9).

**Formalization Note.** The paper's procedure fixes one grouping (the greedy of the proof of
Lemma 4) and one choice of offsets; here any grouping and offsets with these properties are
allowed. A `Finset` of groups merges duplicate (empty) groups, which only lowers the count. -/
def IsRSGrouping {N : ℕ} (a : ℕ) (x : Fin N → ℝ) (𝒢 : ℕ → Finset (Finset (Fin N)))
    (o : Fin N → ℤ) : Prop :=
  ∀ j ∈ Finset.Icc 1 a,
    (↑(𝒢 j) : Set (Finset (Fin N))).PairwiseDisjoint id ∧
    (𝒢 j).sup id = Ij a x j ∧
    (𝒢 j).card ≤ ⌈Kj a x j⌉₊ ∧
    (∀ G ∈ 𝒢 j, ∑ i ∈ G, 1 / (dnat a x i : ℝ) ≤ 1) ∧
    (∀ G ∈ 𝒢 j, IsOnePPPOn (dnat a x) o G)

/-- All groups `{I_{j,s}}_{j,s}` of a grouping, tagged by `j ∈ [a]` (Algorithm 1, line 12). -/
def taggedGroups {N : ℕ} (a : ℕ) (𝒢 : ℕ → Finset (Finset (Fin N))) :
    Finset (ℕ × Finset (Fin N)) :=
  (Finset.Icc 1 a).biUnion (fun j => (𝒢 j).image (fun G => (j, G)))

/-- **The long-run average reward of a group**, `R(I_{j,s}) = ∑_{i ∈ I_{j,s}} R_i(d_i)/d_i`
(arXiv:2106.14813v2, Algorithm 1, line 10, p.13). -/
noncomputable def groupReward {N : ℕ} (R : Fin N → ℕ → ℝ) (a : ℕ) (x : Fin N → ℝ)
    (G : Finset (Fin N)) : ℝ :=
  ∑ i ∈ G, R i (dnat a x i) / (dnat a x i : ℝ)

/-- **`π` is an output of the procedure R-S(x, K, a)** (arXiv:2106.14813v2, Algorithm 1, p.13;
§4.2, pp.12–13). With `d_i` the rounding (4) of `x_i` and `I_j`, `K_j` as above, there are a
grouping `𝒢` with offsets `o` as in `IsRSGrouping`, and a selection `𝒮` of `min(K, K[a])` of the
tagged groups (all of them when there are at most `K`) whose total long-run average reward is
maximal among selections of that size ("Select `K` 1-PPPs from `{I_{j,s}}_{j,s}` that attain the
top `K` largest long-run average reward", line 12). Arms in a selected group have period `d_i` and
offset `o_i`; all other arms are never pulled (period `+∞`, offset `≤ 0`, Definition 1 (i)).

**Formalization Note.** The paper's procedure has internal choices (the grouping, the offsets,
ties in the top-`K` selection); this relation leaves every one of them free. The input
`x ∈ [0, 1]^N` is part of the relation (line 1). -/
def IsRSRun {N : ℕ} (R : Fin N → ℕ → ℝ) (K a : ℕ) (x : Fin N → ℝ) (π : PPP N) : Prop :=
  (∀ i, x i ∈ Set.Icc (0 : ℝ) 1) ∧
  ∃ (𝒢 : ℕ → Finset (Finset (Fin N))) (o : Fin N → ℤ), IsRSGrouping a x 𝒢 o ∧
    ∃ 𝒮 ⊆ taggedGroups a 𝒢,
      𝒮.card = min K (taggedGroups a 𝒢).card ∧
      (∀ 𝒮' ⊆ taggedGroups a 𝒢, 𝒮'.card = 𝒮.card →
        ∑ p ∈ 𝒮', groupReward R a x p.2 ≤ ∑ p ∈ 𝒮, groupReward R a x p.2) ∧
      ∀ i : Fin N,
        ((∃ p ∈ 𝒮, i ∈ p.2) →
          π.period i = ((dnat a x i : ℕ) : WithTop ℕ) ∧ π.offset i = o i) ∧
        ((¬ ∃ p ∈ 𝒮, i ∈ p.2) → π.period i = ⊤ ∧ π.offset i ≤ 0)

end RecoveringBandits


