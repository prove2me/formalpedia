-- Prove2me | Definitions.Def_GapCliqueLB_Clique_Construction
-- name    : GapCliqueLB_Clique_Construction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T09:50:08.406636+00:00
-- url     : https://prove2.me/theorems/d97a29b9-6780-49f9-af0e-8876915faab1
-- title:
--   The shared graph of local hypercliques
-- statement:
--   Let $H$ be a $k$-partite $r$-uniform hypergraph and let $T_i\subseteq[k]$. A vertex of part $i$ is a choice of one vertex from each class indexed by $T_i$ whose chosen set is a hyperclique. The choices are functions on $T_i$ itself, so unused coordinates do not create extra vertices. Empty choices and hypercliques of size below $r$ are retained.
--
--   Two vertices are adjacent exactly when they belong to different parts, choose the same vertex on each common class, and their union is a hyperclique. This defines one graph $G=\operatorname{gapGraph}(T,H)$, shared by both reductions. Its edge count counts each unordered edge once.
--
--   This construction specifies the full graph, including isolated vertices, independently of any proposed algorithm or running-time bound.
-- source:
--   Reina Itakura, Karthik C.S., Mayank Motwani, Gary Peng, STOC 2027 submission #232 (October 2026), Theorem 4.4, shared unchanged in Theorem 5.2, PDF p. 15 (printed p. 14), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/232.pdf

import Definitions.Def_GapCliqueLB_Clique_Inputs
import Definitions.Def_GapCliqueLB_Clique_Dispersers

namespace GapCliqueLB.Clique

abbrev Choice {k r : ℕ} (H : PartiteInput k r) (S : Finset (Fin k)) :=
  (a : S) → Fin (H.sizes a.val)

def selected {k r : ℕ} (H : PartiteInput k r) (S : Finset (Fin k))
    (c : Choice H S) : Finset H.Vertex :=
  S.attach.image (fun a => ⟨a.val, c a⟩)

abbrev LocalClique {k r : ℕ} (H : PartiteInput k r) (S : Finset (Fin k)) :=
  {c : Choice H S // IsHyperclique H.data.graph r (selected H S c)}

abbrev GapVertex {k ℓ r : ℕ} (T : Fin ℓ → Finset (Fin k)) (H : PartiteInput k r) :=
  Σ i : Fin ℓ, LocalClique H (T i)

noncomputable instance {k ℓ r : ℕ} (T : Fin ℓ → Finset (Fin k)) (H : PartiteInput k r) :
    Fintype (GapVertex T H) := by
  classical
  exact inferInstanceAs (Fintype (Σ i : Fin ℓ,
    {c : Choice H (T i) // IsHyperclique H.data.graph r (selected H (T i) c)}))

/-- Compatibility is stated on actual chosen vertices, so overlaps must agree. -/
def Compatible {k r : ℕ} {H : PartiteInput k r} (A B : Finset H.Vertex) : Prop :=
  ∀ u ∈ A, ∀ v ∈ B, u.1 = v.1 → u = v

/-- The shared construction in Theorems 4.4 and 5.2. -/
def gapGraph {k ℓ r : ℕ} (T : Fin ℓ → Finset (Fin k)) (H : PartiteInput k r) :
    SimpleGraph (GapVertex T H) where
  Adj x y := x.1 ≠ y.1 ∧
    Compatible (selected H (T x.1) x.2.val) (selected H (T y.1) y.2.val) ∧
    IsHyperclique H.data.graph r
      (selected H (T x.1) x.2.val ∪ selected H (T y.1) y.2.val)
  symm := ⟨by
    intro x y h
    refine ⟨Ne.symm h.1, ?_, ?_⟩
    · intro u hu v hv huv
      exact (h.2.1 v hv u hu huv.symm).symm
    · simpa [Finset.union_comm] using h.2.2⟩
  loopless := ⟨by intro x h; exact h.1 rfl⟩

/-- Unordered edges are counted once. -/
noncomputable def edgeCount {V : Type} [Fintype V] (G : SimpleGraph V) : ℕ := by
  classical
  exact G.edgeFinset.card

end GapCliqueLB.Clique


