-- Prove2me | Definitions.Def_NestedLogitVariants_PowersDelta_Levels
-- name    : NestedLogitVariants_PowersDelta_Levels
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T21:33:49.967279+00:00
-- url     : https://prove2.me/theorems/162e69e8-10f2-4458-b86b-03ba2d4471d9
-- title:
--   §6.2, pp. 27–28 — v^L_i, v^U_i, the levels l^L_i, l^U_i, problem (15), the assortments Ŝ_il and their candidate collection
-- statement:
--   Fix a constant $\delta > 1$. For nest $i$ let
--   $$v^L_i = v_{i0} + \min_{j \in N} v_{ij}, \qquad v^U_i = v_{i0} + \sum_{j \in N} v_{ij},$$
--   the smallest and the largest preference weight of a nonempty assortment of the nest, and let
--   $$l^L_i = \min\{l \in \mathbb Z : \delta^l \ge v^L_i\}, \qquad l^U_i = \min\{l \in \mathbb Z : \delta^l \ge v^U_i\},$$
--   so that $[v^L_i, v^U_i] \subset [\delta^{l^L_i - 1}, \delta^{l^U_i}]$. For an integer level $l$, an assortment $S \subseteq N$ is feasible for problem (15) when
--   $$\delta^{l-1} \le v_{i0} + \sum_{j \in S} v_{ij} \le \delta^l,$$
--   and $\hat G_{il}$ is the largest value of $\sum_{j \in S} r_{ij} v_{ij}$ over such $S$.
--
--   A family of assortments $\hat S_{il}$, one for each nest $i$ and level $l$, has the **powers-of-$\delta$ property** when, for every $l = l^L_i, \dots, l^U_i$ at which problem (15) has a feasible solution, $\hat S_{il}$ is feasible for (15) and
--   $$\delta \sum_{j \in \hat S_{il}} r_{ij} v_{ij} \ge \sum_{j \in S} r_{ij} v_{ij} \quad \text{for every } S \text{ feasible for (15)},$$
--   that is, $\delta \sum_{j \in \hat S_{il}} r_{ij} v_{ij} \ge \hat G_{il}$. The candidate collection of nest $i$ is $\{\hat S_{il} : l = l^L_i, \dots, l^U_i\} \cup \{\emptyset\}$.
--
--   These objects define the approximation scheme of §6.2: problem (4) is solved over the candidate collections, and Theorem 12 bounds the loss.
--
--   **Formalization Note** $l^L_i$ and $l^U_i$ are written $\lceil \log_\delta v^L_i \rceil$ and $\lceil \log_\delta v^U_i \rceil$, which equal the minima above whenever $\delta > 1$ and the weight is positive (proved in the sanity file). The minimum over products requires $n \ge 1$ (`[NeZero n]`). Powers $\delta^l$ with integer $l$ are integer powers. The property of $\hat S_{il}$ is stated as "at least every feasible value" rather than through a maximum, and a level at which (15) is infeasible imposes nothing on $\hat S_{il}$.
-- source:
--   Davis, Gallego, Topaloglu, Assortment optimization under variants of the nested logit model, revised manuscript of June 18, 2013 (published Oper. Res. 62(2), 2014, DOI 10.1287/opre.2014.1256), pp. 27–28, §6.2, display (15) and the paragraph after it

import Mathlib
import Definitions.Def_NestedLogitVariants_PowersDelta_Model

namespace NestedLogitVariants.PowersDelta

variable {ι : Type*} {n : ℕ}

/-- `v^L_i = v_{i0} + min_{j ∈ N} v_{ij}` (p. 27), the smallest preference weight of a nonempty
assortment in nest `i`. The minimum needs a product, hence `[NeZero n]`. -/
noncomputable def vL [NeZero n] (I : Instance ι n) (i : ι) : ℝ :=
  I.vnp i + Finset.univ.inf' Finset.univ_nonempty (I.v i)

/-- `v^U_i = v_{i0} + ∑_{j ∈ N} v_{ij}` (p. 27), the preference weight of the full assortment. -/
def vU (I : Instance ι n) (i : ι) : ℝ := V I i Finset.univ

/-- `l^L_i = min{l ∈ ℤ : δ^l ≥ v^L_i}` (p. 28), written as `⌈log_δ v^L_i⌉`, which is that minimum
whenever `δ > 1` and `v^L_i > 0`. -/
noncomputable def lL [NeZero n] (I : Instance ι n) (i : ι) (δ : ℝ) : ℤ := ⌈Real.logb δ (vL I i)⌉

/-- `l^U_i = min{l ∈ ℤ : δ^l ≥ v^U_i}` (p. 28), written as `⌈log_δ v^U_i⌉`. -/
noncomputable def lU (I : Instance ι n) (i : ι) (δ : ℝ) : ℤ := ⌈Real.logb δ (vU I i)⌉

/-- The constraint of problem (15) (p. 28): `δ^{l-1} ≤ v_{i0} + ∑_{j ∈ S} v_{ij} ≤ δ^l`
(integer powers). -/
def InLevel (I : Instance ι n) (i : ι) (δ : ℝ) (l : ℤ) (S : Finset (Fin n)) : Prop :=
  δ ^ (l - 1) ≤ V I i S ∧ V I i S ≤ δ ^ l

/-- The two properties p. 28 attributes to the assortments `Ŝ_il`, `l = l^L_i, …, l^U_i`: whenever
problem (15) is feasible, `Ŝ_il` is feasible for (15), and `δ ∑_{j ∈ Ŝ_il} r_{ij} v_{ij}` is at
least the objective value `∑_{j ∈ S} r_{ij} v_{ij}` of every feasible `S`, that is, at least
`Ĝ_il`. A level with no feasible assortment imposes nothing. -/
def IsPowersFamily [NeZero n] (I : Instance ι n) (δ : ℝ) (Sh : ι → ℤ → Finset (Fin n)) : Prop :=
  ∀ i, ∀ l, lL I i δ ≤ l → l ≤ lU I i δ → (∃ S, InLevel I i δ l S) →
    InLevel I i δ l (Sh i l) ∧
      ∀ S, InLevel I i δ l S → ∑ j ∈ S, I.r i j * I.v i j ≤ δ * ∑ j ∈ Sh i l, I.r i j * I.v i j

/-- The candidate collection `{Ŝ_il : l = l^L_i, …, l^U_i} ∪ {∅}` of nest `i` (p. 28). -/
def powersCandidates [NeZero n] (I : Instance ι n) (δ : ℝ) (Sh : ι → ℤ → Finset (Fin n)) (i : ι) :
    Set (Finset (Fin n)) :=
  {S | (∃ l : ℤ, lL I i δ ≤ l ∧ l ≤ lU I i δ ∧ S = Sh i l) ∨ S = ∅}

end NestedLogitVariants.PowersDelta


