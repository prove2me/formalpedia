-- Prove2me | Definitions.Def_LowDiameterNashWilliams_Main_Supplement_Promises
-- name    : LowDiameterNashWilliams_Main_Supplement_Promises
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T10:35:14.713577+00:00
-- url     : https://prove2.me/theorems/cf68ab09-d201-4cca-9a3f-4a6c4a5de0b5
-- title:
--   Exact YES and NO promises for the five hardness targets
-- statement:
--   For the diameter and internal-vertex ratio targets, graph validity means a simple graph with at least two vertices and a $k$-tree packing; the packing is a property of the input graph, with no certificate included. The rooted depth problem also retains the one-vertex graph, on which root depth is well-defined. It is YES when such a packing has every root depth at most two, and NO when this is impossible. The diameter problem uses exactly the bound $n/(2\delta(G))$, and NO is its complement within the same promise.
--
--   The internal-vertex gap is
--   $$\mathrm{YES}:\ \exists(T_i)_{i=1}^k\ \forall i,\ |\operatorname{int}(T_i)|<3n/\delta(G),\qquad
--   \mathrm{NO}:\ \forall T\text{ spanning},\ |\operatorname{int}(T)|>n\ln\delta(G)/(600\delta(G)).$$
--   Both sides retain the graph-packing promise. For minimum-frequency Set Cover the two cases are $\tau\le m/D$ and $\tau>(m/(100D))\ln D$, each with all validity and frequency constraints. For bounded Set Cover they are $\tau\le\beta$ and $\tau>(\beta/10)\ln B$, each with set sizes and frequencies at most $B$, valid nonempty data, and $0\le\beta\le m$.
--
--   The published operational definition of gap NP-hardness will be applied to these predicates and to the explicit encoders. These definitions assert neither hardness nor efficient reductions. Ratios are real and logarithms natural; nondegenerate promised graph inputs have positive minimum degree.
-- source:
--   Pin-Hsian Lee, Peng-Ting Lin, Meng-Tsung Tsai, Ting-An Wu, STOC 2027 submission #1510 (October 2026), Section 7, Lemma 7.3 and Theorems 5–7, pp. 26–28 (PDF pp. 27–29); Appendix A, Theorem 8, p. 33 (PDF p. 34)

import Mathlib
import Definitions.Def_LowDiameterNashWilliams_Main_Supplement_SetCover
import Definitions.Def_SetCoverThreshold_SetCover_Complexity

set_option autoImplicit false
open scoped ENNReal NNReal
open Classical
open LowDiameterNashWilliams.Main
open NashWilliams61.TreePacking

namespace LowDiameterNashWilliams.Main.Supplement

/-- Ordinary simple-graph packing promise; includes the rooted singleton case. -/
def SimplePackingPromise (k : ℕ) (G : GraphInput) : Prop :=
  Simple G.ends ∧ ∃ T : Trees k G.m, Packing G.ends T

/-- Nondegenerate domain of the minimum-degree ratios; no input certificate or edge partition. -/
def PackingPromise (k : ℕ) (G : GraphInput) : Prop :=
  2 ≤ G.n ∧ SimplePackingPromise k G

noncomputable def DepthYes (k : ℕ) (G : RootedInput) : Prop :=
  SimplePackingPromise k G.graph ∧ HasDepthPacking G.graph k G.root 2

noncomputable def DepthNo (k : ℕ) (G : RootedInput) : Prop :=
  SimplePackingPromise k G.graph ∧ ¬ HasDepthPacking G.graph k G.root 2

noncomputable def DiameterYes (k : ℕ) (G : GraphInput) : Prop :=
  PackingPromise k G ∧ HasDiameterPacking G k (ENNReal.ofReal ((G.n : ℝ) / (2 * minDegree G.ends)))

noncomputable def DiameterNo (k : ℕ) (G : GraphInput) : Prop :=
  PackingPromise k G ∧ ¬ HasDiameterPacking G k (ENNReal.ofReal ((G.n : ℝ) / (2 * minDegree G.ends)))

noncomputable def InternalYes (k : ℕ) (G : GraphInput) : Prop :=
  PackingPromise k G ∧ ∃ T : Trees k G.m, Packing G.ends T ∧
    ∀ i, ((internal G.ends (T i)).card : ℝ) < 3 * G.n / minDegree G.ends

noncomputable def InternalNo (k : ℕ) (G : GraphInput) : Prop :=
  PackingPromise k G ∧ ∀ T : Edges G.m, IsSpanningTree G.ends T →
    (G.n : ℝ) * Real.log (minDegree G.ends) / (600 * minDegree G.ends) <
      ((internal G.ends T).card : ℝ)

noncomputable def FrequentYes (D : ℕ) (I : SCInstance) : Prop :=
  FrequentCover I D ∧ (coverNumber I : ℝ) ≤ (I.sets.length : ℝ) / D

noncomputable def FrequentNo (D : ℕ) (I : SCInstance) : Prop :=
  FrequentCover I D ∧ (I.sets.length : ℝ) / (100 * D) * Real.log D < coverNumber I

noncomputable def BoundedYes (B : ℕ) (I : ThresholdInput) : Prop :=
  BoundedCover I.cover B ∧ I.beta ≤ I.cover.sets.length ∧ coverNumber I.cover ≤ I.beta

noncomputable def BoundedNo (B : ℕ) (I : ThresholdInput) : Prop :=
  BoundedCover I.cover B ∧ I.beta ≤ I.cover.sets.length ∧
    (I.beta : ℝ) / 10 * Real.log B < coverNumber I.cover

end LowDiameterNashWilliams.Main.Supplement


