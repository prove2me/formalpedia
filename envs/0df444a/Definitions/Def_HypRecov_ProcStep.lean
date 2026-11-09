-- Prove2me | Definitions.Def_HypRecov_ProcStep
-- name    : HypRecov_ProcStep
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T16:37:26.977318+00:00
-- url     : https://prove2.me/theorems/f2502573-db0a-454e-98c3-5b4d5142fe69
-- title:
--   The layered completion process of Theorem 5.3
-- statement:
--   A state of the process consists of the deletion set $D$, the current partition $P$, $k$ connectivity layers $F_1,\dots,F_k$ (sets of edges), the number of acceptances and the number of strict merges. It starts with $D=\emptyset$, the base partition $P_0$ and empty layers. A step is one of:
--
--   1. **acceptance**: a residual edge $e\in E(H)\setminus D$ spanning current blocks is inserted into the first layer in which its vertices meet at least two components, and added to $D$;
--   2. **rejection**: if every layer already connects the vertices of such an $e$, the current blocks meeting $e$ are merged (a strict merge);
--   3. **safe merger**: the partition is replaced by any safe coarsening; this is a strict merge exactly when the number of blocks drops.
--
--   Connectivity in a layer is reachability in the two-section of its edges. The completion steps of Theorem 5.3 and the candidate processing of Theorem 6.4 (ProcessEdge) are acceptances or rejections; the separator contractions of §6.1 are safe mergers.
-- source:
--   Zhang, Chen, Shen, Hypergraph Recovery from Anonymous Projection Streams, STOC 2027 submission (manuscript sha256 719dcfff4dc2eba2d8c5a3c51679a08cfb11f076546dea963c6376a2b9da2c82), §5.2, p.11 (PDF p.12); Theorem 5.3, p.11; Theorem 6.4, p.16

import Mathlib
import Definitions.Def_HypRecov_twoSection
import Definitions.Def_HypRecov_Safe

namespace HypRecov

/-- **State of the layered completion process.** Zhang, Chen, Shen, *Hypergraph Recovery from
Anonymous Projection Streams*, STOC 2027 submission (manuscript sha256 719dcfff…), §5.2, p.11 (PDF
p.12): "we maintain k disjoint connectivity layers of recovered edges."

`D` is the deletion set, `P` the current block label, `layers i` the edges of layer `i`, `acc` the
number of acceptances and `mrg` the number of strict merges so far. -/
structure ProcState (n k : ℕ) where
  D : Finset (Finset (Fin n))
  P : Fin n → Fin n
  layers : Fin k → Finset (Finset (Fin n))
  acc : ℕ
  mrg : ℕ

/-- The starting state: empty deletion set, base partition `P₀`, empty layers. -/
def initState {n k : ℕ} (P₀ : Fin n → Fin n) : ProcState n k :=
  ⟨∅, P₀, fun _ => ∅, 0, 0⟩

/-- **One step of the process.** Ibid., §5.2, p.11: "Initially each layer is empty. Process a
recovered edge by inserting it into the first layer in which its vertices meet at least two
components, and then delete it from the residual J. The layer keeps the edge after this deletion. If
all layers already connect its vertices, merge their current blocks instead." Theorem 5.3, p.11:
"This phase, interleaved with any genuine candidate processing and safe mergers"; Theorem 6.4, p.16
(ProcessEdge).

A step is one of:
1. **acceptance**: a genuine residual edge `e ∈ E ∖ D` spanning current blocks is inserted into the
   first layer `i` whose components it meets at least twice, and added to `D`;
2. **rejection**: such an `e` whose vertices every layer already connects; the current blocks
   meeting `e` are merged (a strict merge);
3. **safe merger**: any coarsening `P'` of `P` that is safe; it counts as a strict merge exactly when
   the number of blocks drops.

**Formalization Note.** Connectivity in a layer is reachability in the two-section of its edges. The
process is a relation, so every order of steps and every interleaving is covered; the completion
steps of Theorem 5.3 are acceptances or rejections of qualifying edges. -/
inductive ProcStep {n : ℕ} (E : Finset (Finset (Fin n))) (k : ℕ) :
    ProcState n k → ProcState n k → Prop
  | accept (s : ProcState n k) (e : Finset (Fin n)) (i : Fin k) :
      e ∈ E → e ∉ s.D → Spans s.P e →
      (∃ u ∈ e, ∃ v ∈ e, ¬ (twoSection (s.layers i)).Reachable u v) →
      (∀ j : Fin k, j < i → ∀ u ∈ e, ∀ v ∈ e, (twoSection (s.layers j)).Reachable u v) →
      ProcStep E k s ⟨insert e s.D, s.P, Function.update s.layers i (insert e (s.layers i)),
        s.acc + 1, s.mrg⟩
  | reject (s : ProcState n k) (e : Finset (Fin n)) (P' : Fin n → Fin n) :
      e ∈ E → e ∉ s.D → Spans s.P e →
      (∀ j : Fin k, ∀ u ∈ e, ∀ v ∈ e, (twoSection (s.layers j)).Reachable u v) →
      IsMergeOf s.P e P' →
      ProcStep E k s ⟨s.D, P', s.layers, s.acc, s.mrg + 1⟩
  | merge (s : ProcState n k) (P' : Fin n → Fin n) :
      Coarsens s.P P' → Safe E k P' →
      ProcStep E k s ⟨s.D, P', s.layers, s.acc,
        s.mrg + (if numBlocks P' < numBlocks s.P then 1 else 0)⟩

end HypRecov


