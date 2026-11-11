-- Prove2me | Definitions.Def_QMCSub_Edge
-- name    : QMCSub_Edge
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T09:17:49.022169+00:00
-- url     : https://prove2.me/theorems/6becd74a-8b96-4f10-8495-e580f270cf3b
-- title:
--   Reading the weight matrix off the canonical edge list
-- statement:
--   On the canonical edge list of an input graph, the program's weight lookup for a pair of vertices $(i,j)$ returns the entry $A_{ij}$ of the symmetric weight matrix, and the sum of the listed weights is the total weight $W$.
-- source:
--   Supporting library for QuantumMaxCutEnergy.agm_classical_sdp_lower_value_tm2 (Prove2me mission 'Quantum Max-Cut: 0.526 energy estimation'; Anshu, Gosset, Morenz, Beyond product state approximations for a quantum analogue of Max Cut, arXiv:2003.14394). Method: rounded dual subgradient iteration for the Max-Cut semidefinite relaxation with matrix-power approximate subgradients.

import Mathlib
import Definitions.Def_QuantumMaxCutFiniteNumericRuntime
import Definitions.Def_QMCSub_Prog
import Definitions.Def_QMCSub_Lap

/-!
The edge list of an input graph, read through the program's accessors.
-/

namespace QMCSub
open QuantumMaxCutEnergy QMCNumericRuntime
open scoped BigOperators

/-- A sum over the canonical edge list, as a double sum over ordered pairs. -/
theorem edge_list_sum {n : ℕ} (g : Edge n → ℚ) :
    ((graphEdgeList n).map g).sum =
      ∑ i : Fin n, ∑ j : Fin n, if h : i < j then g ⟨(i, j), h⟩ else 0 := by
  unfold graphEdgeList
  simp only [List.map_flatMap, QMCNumericRuntime.sum_flatMap, ← Fin.sum_univ_def]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> simp

/-- A sum over edges, as a double sum over ordered pairs. -/
theorem edge_univ_sum {n : ℕ} (g : Edge n → ℚ) :
    ∑ e, g e = ∑ i : Fin n, ∑ j : Fin n, if h : i < j then g ⟨(i, j), h⟩ else 0 := by
  classical
  let f : Fin n × Fin n → ℚ := fun p => if h : p.1 < p.2 then g ⟨p, h⟩ else 0
  have hf : (∑ p, f p) = ∑ e, g e := by
    apply Finset.sum_congr_set {p : Fin n × Fin n | p.1 < p.2} f g
    · intro p hp
      change p.1 < p.2 at hp
      simp only [f, dif_pos hp]
    · intro p hp
      change ¬p.1 < p.2 at hp
      simp only [f, dif_neg hp]
  rw [← hf, Fintype.sum_prod_type]

theorem edge_list_sum_univ {n : ℕ} (g : Edge n → ℚ) :
    ((graphEdgeList n).map g).sum = ∑ e, g e := by
  rw [edge_list_sum, edge_univ_sum]

/-- The program's weight lookup on the canonical edge list, as a sum over edges. -/
theorem edgeW_inputEdges_sum (G : Input) (a b : Fin G.n) :
    edgeW (inputEdges G) a.val b.val =
      ∑ e : Edge G.n, if (e.val.1 = a ∧ e.val.2 = b) ∨ (e.val.1 = b ∧ e.val.2 = a)
        then (G.weights e : ℚ) else 0 := by
  rw [← edge_list_sum_univ]
  unfold edgeW inputEdges
  rw [List.map_map]
  refine congrArg List.sum (List.map_congr_left fun e _ => ?_)
  simp only [Function.comp_apply, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
    Fin.val_inj]

/-- The program's weight lookup on the canonical edge list is the symmetric weight matrix. -/
theorem edgeW_inputEdges (G : Input) (i j : Fin G.n) :
    edgeW (inputEdges G) i.val j.val = Aq G i j := by
  classical
  rw [edgeW_inputEdges_sum]
  unfold Aq
  rcases lt_trichotomy i j with h | h | h
  · rw [dif_pos h]
    have hc : ∀ e : Edge G.n, ((e.val.1 = i ∧ e.val.2 = j) ∨ (e.val.1 = j ∧ e.val.2 = i)) ↔
        e = ⟨(i, j), h⟩ := by
      intro e
      constructor
      · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
        · exact Subtype.ext (Prod.ext h1 h2)
        · exact absurd e.2 (by rw [h1, h2]; exact not_lt.mpr h.le)
      · rintro rfl
        exact Or.inl ⟨rfl, rfl⟩
    simp only [hc, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  · subst h
    rw [dif_neg (lt_irrefl i), dif_neg (lt_irrefl i)]
    refine Finset.sum_eq_zero fun e _ => ?_
    rw [if_neg]
    rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact absurd e.2 (by rw [h1, h2]; exact lt_irrefl i)
    · exact absurd e.2 (by rw [h1, h2]; exact lt_irrefl i)
  · rw [dif_neg (not_lt.mpr h.le), dif_pos h]
    have hc : ∀ e : Edge G.n, ((e.val.1 = i ∧ e.val.2 = j) ∨ (e.val.1 = j ∧ e.val.2 = i)) ↔
        e = ⟨(j, i), h⟩ := by
      intro e
      constructor
      · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
        · exact absurd e.2 (by rw [h1, h2]; exact not_lt.mpr h.le)
        · exact Subtype.ext (Prod.ext h1 h2)
      · rintro rfl
        exact Or.inr ⟨rfl, rfl⟩
    simp only [hc, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem edgeWeightSum_inputEdges (G : Input) : edgeWeightSum (inputEdges G) = Wq G := by
  rw [inputEdges_weight_sum]
  rfl

end QMCSub


