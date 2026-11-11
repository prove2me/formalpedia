-- Prove2me | Definitions.Def_ObliviousAdaptive172_Parallel_HistoryModel
-- name    : ObliviousAdaptive172_Parallel_HistoryModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:54:26.824818+00:00
-- url     : https://prove2.me/theorems/87f015a2-9bf6-4943-b889-08c9276a30c4
-- title:
--   Legal histories, monotone properties, and stable configurations
-- statement:
--   Let $U$ be an arbitrary update space. A history model specifies, for each finite history $h$ and proposed update $u$, whether $u$ is permitted. A history is legal when each update was permitted after its preceding prefix. A property $P$ is monotone when it persists under every legal extension. For a witness relation $\operatorname{valid}(h,w)$ and configuration $w\in W$, stability means
--
--   $$
--   \operatorname{Stable}(h,w)\quad\Longleftrightarrow\quad
--   \forall e\text{ with }h e\text{ legal},\ \operatorname{valid}(h e,w).
--   $$
--
--   The same configuration must work on every legal continuation. The model includes a specialization to insertion-only or deletion-only simple graphs on $\{0,\ldots,n-1\}$; the general interface also admits weighted or directed graphs, and states retaining update history. Graphs themselves reuse Mathlib's `SimpleGraph`. The optional first-hit time searches all prefixes, including the empty prefix at time zero; absence of a hit has no finite deadline. This layer supplies shared legality and monotonicity notions for both source results.
-- source:
--   Shiri Chechik, Inbal Hadad, From Oblivious to Adaptive Adversaries: Black-Box Reductions for Monotone Dynamic Problems with Applications to Cuts, Distances, and Clustering, STOC 2027 submission #172 (October 2026), pp. 1–2, Definition 1.1 (PDF pp. 3–4); p. 11, §3.3 (PDF p. 13)

import Mathlib
set_option autoImplicit false

namespace ObliviousAdaptive172.Parallel

/-- An online transition system. Histories retain the past, as needed for the synthetic
quantile property in §3.3. No information about the algorithm occurs in legality. -/
structure HistoryModel (U : Type) where
  permitted : List U → U → Prop

variable {U W : Type}

def HistoryModel.Legal (M : HistoryModel U) (h : List U) : Prop :=
  ∀ i (hi : i < h.length), M.permitted (h.take i) (h[i]'hi)

def HistoryModel.Monotone (M : HistoryModel U) (P : List U → Prop) : Prop :=
  ∀ h e, M.Legal (h ++ e) → P h → P (h ++ e)

def HistoryModel.Stable (M : HistoryModel U) (valid : List U → W → Prop)
    (h : List U) (w : W) : Prop :=
  ∀ e, M.Legal (h ++ e) → valid (h ++ e) w

/-- Specialization to ordinary legal insertions or deletions on a fixed vertex set.
The generic theorems also allow directed graphs, fixed weighted graphs, and history states. -/
inductive GraphMode
  | incremental | decremental

noncomputable def edgeUpdate {n : ℕ} (mode : GraphMode) (G : SimpleGraph (Fin n))
    (u : Fin n × Fin n) : SimpleGraph (Fin n) :=
  match mode with
  | .incremental => SimpleGraph.fromEdgeSet (insert (Sym2.mk u.1 u.2) G.edgeSet)
  | .decremental => SimpleGraph.fromEdgeSet (G.edgeSet \ {Sym2.mk u.1 u.2})

noncomputable def graphHistoryModel {n : ℕ} (mode : GraphMode)
    (G₀ : SimpleGraph (Fin n)) : HistoryModel (Fin n × Fin n) where
  permitted h u :=
    let G := h.foldl (edgeUpdate mode) G₀
    u.1 ≠ u.2 ∧ match mode with
      | .incremental => ¬ G.Adj u.1 u.2
      | .decremental => G.Adj u.1 u.2

/-- Optional deadline, including time zero. `none` means no hit in the finite run. -/
noncomputable def firstHit (P : List U → Prop) (h : List U) : Option ℕ := by
  classical
  exact (List.range (h.length + 1)).find? (fun t => P (h.take t))

end ObliviousAdaptive172.Parallel


