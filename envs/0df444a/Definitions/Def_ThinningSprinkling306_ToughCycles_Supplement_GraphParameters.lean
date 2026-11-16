-- Prove2me | Definitions.Def_ThinningSprinkling306_ToughCycles_Supplement_GraphParameters
-- name    : ThinningSprinkling306_ToughCycles_Supplement_GraphParameters
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T17:41:39.232851+00:00
-- url     : https://prove2.me/theorems/347a3f8f-e54d-4620-9fd2-530827e91210
-- title:
--   Connectivity, regularity, degrees and external vertex expansion
-- statement:
--   Let $G$ be a finite simple undirected graph, and $W$ a vertex subset. Write $\kappa(G[W])$ for vertex connectivity, with $\kappa(K_s)=s-1$ for nonempty complete graphs and zero for empty, singleton or disconnected graphs. The real threshold $x$ is encoded by
--   $$
--   |W|\ge x+1,\qquad \kappa(G[W])\ge x.
--   $$
--   For $x\ge0$ this is the usual $\lceil x\rceil$ connectivity convention, including the cardinality clause. Regularity on $W$ means every vertex has exactly $d$ neighbors inside $W$. Minimum and maximum degrees are the actual extrema over all vertices, with zero on the empty graph.
--
--   External vertex expansion on $W$ means
--   $$
--   |N_G(U)\cap W|\ge\lambda|U|\quad(U\subseteq W,\ 2|U|\le|W|),
--   $$
--   where the neighborhood excludes $U$. These are reusable graph predicates, without connectivity, regularity or positivity bundled into expansion. The published connectivity and neighborhood definitions are imported; the original mission supplies its external-neighborhood convention.
-- source:
--   Micha Christoph, Zach Hunter, Benny Sudakov, STOC 2027 submission #306 (October 2026), p. 3, Theorems 1.1, 1.3–1.5; definition preceding Theorem 1.4 (PDF p. 5); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/306.pdf

import Definitions.Def_ThinningSprinkling306_ToughCycles_Cuts
import Definitions.Def_CharonChurn_Main_Connectivity

namespace ThinningSprinkling306.ToughCycles.Supplement

/-- Real connectivity thresholds use the ceiling integer; the cardinality clause
also excludes the empty graph at threshold zero. Positive thresholds use the
published vertex-cut connectivity, including κ(K_s)=s-1. -/
noncomputable def ConnectedAt {n : ℕ} (G : SimpleGraph (Fin n))
    (W : Finset (Fin n)) (x : ℝ) : Prop :=
  x + 1 ≤ (W.card : ℝ) ∧ x ≤ (CharonChurn.Main.kappa G W : ℝ)

/-- Degree inside an induced vertex set, without additional conditions. -/
noncomputable def RegularOn {n : ℕ} (G : SimpleGraph (Fin n))
    (W : Finset (Fin n)) (d : ℕ) : Prop :=
  ∀ v ∈ W, (CharonChurn.Main.nbrsIn G W v).card = d

/-- Actual minimum degree; Mathlib returns zero on the empty vertex type. -/
noncomputable def minimumDegree {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ := by
  classical
  exact G.minDegree

/-- Actual maximum degree; Mathlib returns zero on the empty vertex type. -/
noncomputable def maximumDegree {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ := by
  classical
  exact G.maxDegree

/-- External vertex expansion in G[W], with the paper's floor-half cutoff. -/
noncomputable def ExpandsOn {n : ℕ} (G : SimpleGraph (Fin n))
    (W : Finset (Fin n)) (lam : ℝ) : Prop :=
  ∀ U : Finset (Fin n), U ⊆ W → 2 * U.card ≤ W.card →
    lam * (U.card : ℝ) ≤ ((externalNeighbors G U ∩ W).card : ℝ)

end ThinningSprinkling306.ToughCycles.Supplement


