-- Prove2me | solution 1 for AppliedComb.GraphAlg.dijkstra_monotone
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T17:19:41.213597+00:00
-- url     : https://prove2.me/submissions/16d04c54-6a67-49e4-9b47-13ecb9040b4d

import Definitions.Def_AppliedComb_GraphAlg_Dijkstra

set_option autoImplicit false


open AppliedComb.GraphAlg AppliedComb.GraphAlg.DijkstraState

namespace GraphAlgProof

variable {V : Type*} {G : WeightedDigraph V} {r : V} {s : DijkstraState V}

def Ordered (s : DijkstraState V) : Prop :=
  s.σ.Pairwise (fun u v => s.δ u ≤ s.δ v) ∧
  ∀ u ∈ s.σ, ∀ v, v ∉ s.σ → s.δ u ≤ s.δ v

theorem ordered_init (G : WeightedDigraph V) (r : V) : Ordered (init G r) := by
  classical
  constructor
  · simp [init]
  · intro u hu v hv
    simp only [init, List.mem_singleton] at hu
    subst u
    simp [init]

theorem ordered_permanent (hs : Ordered s) {x : V} (hx : s.IsMinTemp x) :
    Ordered (s.makePermanent x) := by
  constructor
  · simp only [makePermanent, List.pairwise_append, List.pairwise_singleton, true_and,
      and_true, List.mem_singleton]
    exact ⟨hs.1, fun u hu v hv => hv ▸ hs.2 u hu x hx.1⟩
  · intro u hu v hv
    simp only [makePermanent, List.mem_append, List.mem_singleton, not_or] at hu hv ⊢
    rcases hu with hu | rfl
    · exact hs.2 u hu v hv.1
    · exact hx.2 v hv.1

theorem ordered_last (hs : Ordered s) {v : V} (hv : s.σ.getLast? = some v)
    {u : V} (hu : u ∈ s.σ) : s.δ u ≤ s.δ v := by
  have h := hs.1.rel_getLast_of_rel_getLast_getLast hu (le_refl _)
  have he : s.σ.getLast (List.ne_nil_of_mem hu) = v := by
    simpa [List.getLast?_eq_getLast (List.ne_nil_of_mem hu)] using hv
  simpa [he] using h

theorem scan_perm {v u : V} (hu : u ∈ s.σ) : (scan G s v).δ u = s.δ u := by
  simp [scan,hu]

theorem ordered_scan (hs : Ordered s) {v : V} (hv : s.σ.getLast? = some v) :
    Ordered (scan G s v) := by
  classical
  have he : ∀ u ∈ s.σ, (scan G s v).δ u = s.δ u := fun u hu => scan_perm hu
  constructor
  · change s.σ.Pairwise _
    exact hs.1.imp_of_mem (fun {u v} hu hv huv => by simpa [he u hu,he v hv] using huv)
  · intro u hu x hx
    change u ∈ s.σ at hu
    change x ∉ s.σ at hx
    rw [he u hu]
    simp only [scan,hx,if_pos]
    exact le_min (hs.2 u hu x hx) ((ordered_last hs hv hu).trans (le_self_add))

theorem run_ordered [Fintype V] {i : ℕ} (hs : DijkstraRun G r i s) : Ordered s := by
  induction hs with
  | init => exact ordered_init _ _
  | first hx => exact ordered_permanent (ordered_init _ _) hx
  | step hrun hi hin hv hx ih => exact ordered_permanent (ordered_scan ih hv) hx

end GraphAlgProof


open AppliedComb.GraphAlg

theorem solution {V : Type*} [Fintype V] (G : WeightedDigraph V) (r : V)
    (s : DijkstraState V) (hs : DijkstraRun G r (Fintype.card V) s) :
    (s.σ.map s.δ).IsChain (· ≤ ·) := by
  rw [List.isChain_iff_pairwise, List.pairwise_map]
  exact (GraphAlgProof.run_ordered hs).1

#print axioms solution
