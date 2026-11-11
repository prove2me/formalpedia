-- Prove2me | Definitions.Def_STCSublinear1377_Main_Quotient
-- name    : STCSublinear1377_Main_Quotient
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T03:37:51.692764+00:00
-- url     : https://prove2.me/theorems/a586f612-bd51-4a52-8b73-e91b03e2675e
-- title:
--   Named connected partitions, quotients and isolating cuts
-- statement:
--   A connected partition of a weighted graph assigns one nonempty connected bag to each quotient vertex. The bags are pairwise disjoint and cover the graph. Distinct quotient vertices are adjacent exactly when their bags have an original edge between them, and
--
--   $$\omega_{F/\mathcal P}(A,B)=\omega_F(A,B).$$
--
--   Loops disappear and parallel edges are aggregated by summing weights. Contracting a disjoint subcollection retains uncovered vertices as singleton bags. A selected isolating set $S_h$ meets a hub set $H$ in exactly $\{h\}$ and has boundary equal to the minimum $h$ versus $H\setminus\{h\}$ cut. Its contracted vertex retains the name $h$.
--
--   The bag maps support one-level lifting and repeated contraction without confusing a retained hub name with an original singleton. No preservation or congestion bound is part of the partition data.
-- source:
--   Sunny Atalig, Marek Chrobak, Petr Kolman, Hans Raj Tiwary, Sublinear Approximations for Spanning Tree Congestion, STOC 2027 submission #1377 (October 2026), pinned submission, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1377.pdf, §3 graph quotients and §3.1, PDF/printed pp.6–8, before Lemma 3.1

import Definitions.Def_STCSublinear1377_Main_Weighted
set_option autoImplicit false

namespace STCSublinear1377.Main

/-- A named connected partition. Labels live in the original name space; bags, not labels,
carry the mathematical vertices. No load or cut comparison is part of this interface. -/
structure BagPartition {n : ℕ} (f : WeightedGraph n) where
  names : Finset (Fin n)
  bag : Fin n → Finset (Fin n)
  connected : ∀ v ∈ names, f.connectedSet (bag v)
  disjoint : ∀ u ∈ names, ∀ v ∈ names, u ≠ v → Disjoint (bag u) (bag v)
  covers : names.biUnion bag = f.vertices

noncomputable def quotientRaw {n : ℕ} (f : WeightedGraph n)
    (names : Finset (Fin n)) (bag : Fin n → Finset (Fin n)) : WeightedGraph n := by
  classical
  exact ⟨names,
    fun u v => decide (u ∈ names ∧ v ∈ names ∧ u ≠ v ∧
      ∃ x ∈ bag u, ∃ y ∈ bag v, f.edges x y = true),
    fun u v => if u ∈ names ∧ v ∈ names ∧ u ≠ v then f.between (bag u) (bag v) else 0⟩

noncomputable def BagPartition.quotient {n : ℕ} {f : WeightedGraph n}
    (p : BagPartition f) : WeightedGraph n := quotientRaw f p.names p.bag

noncomputable def BagPartition.lift {n : ℕ} {f : WeightedGraph n}
    (p : BagPartition f) (s : Finset (Fin n)) : Finset (Fin n) := s.biUnion p.bag

/-- Contract the given disjoint sets, retaining the specified names; uncovered vertices
are singleton bags. The following functions have bodies even on malformed data. -/
noncomputable def contractionNames {n : ℕ} (f : WeightedGraph n)
    (hs : Finset (Fin n)) (sets : Fin n → Finset (Fin n)) : Finset (Fin n) :=
  (f.vertices \ hs.biUnion sets) ∪ hs

noncomputable def contractionBag {n : ℕ} (hs : Finset (Fin n))
    (sets : Fin n → Finset (Fin n)) (v : Fin n) : Finset (Fin n) := by
  classical
  exact if v ∈ hs then sets v else {v}

noncomputable def contract {n : ℕ} (f : WeightedGraph n)
    (hs : Finset (Fin n)) (sets : Fin n → Finset (Fin n)) : WeightedGraph n :=
  quotientRaw f (contractionNames f hs sets) (contractionBag hs sets)

/-- The actual minimum isolating-set specification. Connectedness is deliberately separate:
Lemma 3.1 itself only assumes disjoint isolating sets. -/
noncomputable def isolatingSets {n : ℕ} (f : WeightedGraph n)
    (h hs : Finset (Fin n)) (sets : Fin n → Finset (Fin n)) : Prop :=
  hs ⊆ h ∧ h ⊆ f.vertices ∧
  (∀ v ∈ hs, sets v ⊆ f.vertices ∧ sets v ∩ h = {v} ∧
    f.boundary (sets v) = f.mincut {v} (h.erase v)) ∧
  ∀ u ∈ hs, ∀ v ∈ hs, u ≠ v → Disjoint (sets u) (sets v)

end STCSublinear1377.Main


