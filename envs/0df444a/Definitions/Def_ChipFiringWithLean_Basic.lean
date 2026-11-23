-- Prove2me | Definitions.Def_ChipFiringWithLean_Basic
-- name    : ChipFiringWithLean_Basic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-23T21:41:32.106491+00:00
-- url     : https://prove2.me/theorems/50b9d72d-14b1-4487-a4ba-711255be3ec4
-- title:
--   Basic
-- statement:
--   Definitions and structural lemmas for Basic, from DhyeyMavani2003/chip-firing-with-lean contributors (see pinned LICENSE and source headers)'s pinned Chip-firing on multigraphs and Riemann-Roch for graphs development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/Basic.lean

module
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.Data.Matrix.Mul
set_option autoImplicit true
@[expose] public section
@[expose] public section
universe u
open Multiset Finset
structure CFGraph  where
  V : Type u
  [instDecidableEq : DecidableEq V]
  [instFintype : Fintype V]
  [instNonempty : Nonempty V]
  (edges : Multiset (V × V))
  (loopless : ∀ v, (v, v) ∉ edges)
attribute [instance] CFGraph.instDecidableEq CFGraph.instFintype CFGraph.instNonempty
def num_edges (G : CFGraph) (v w : G.V) : ℕ :=
  Multiset.card (G.edges.filter (λ e => e = (v, w) ∨ e = (w, v)))
def graph_connected (G : CFGraph) : Prop :=
  ∀ S : Finset G.V, (∃ (v w : G.V), v ∈ S ∧ w ∉ S) →
    (∃ v ∈ S, ∃ w ∉ S, num_edges G v w > 0)
def genus (G : CFGraph) : ℤ :=
  Multiset.card G.edges - Fintype.card G.V + 1
@[simp] lemma num_edges_self_zero (G : CFGraph) (v : G.V) :
  num_edges G v v = 0 := by
  rw [num_edges, Multiset.card_eq_zero]
  refine Multiset.filter_eq_nil.mpr ?_
  intro e h_inE h_eq
  rw [or_self] at h_eq
  rcases e with ⟨a, b⟩
  cases h_eq
  exact G.loopless v h_inE
def vertex_degree (G : CFGraph) (v : G.V) : ℤ :=
  ∑ u : G.V, (num_edges G v u : ℤ)
abbrev CFDiv (G : CFGraph) := G.V → ℤ
def one_chip {G : CFGraph} (v_chip : G.V) : CFDiv G :=
  fun v => if v = v_chip then 1 else 0
@[simp] lemma one_chip_apply_v {G : CFGraph} (v : G.V) : one_chip v v = 1 := by
  exact if_pos rfl
@[simp] lemma one_chip_apply_other {G : CFGraph} (v w : G.V) : v ≠ w → one_chip v w = 0 := by
  simp only [ne_eq, one_chip, ite_eq_right_iff, one_ne_zero, imp_false]
  intro h
  contrapose! h
  rw [h]
@[simp] lemma one_chip_apply_other' {G : CFGraph} (v w : G.V) : w ≠ v → one_chip v w = 0 := by
  simp only [ne_eq, one_chip, ite_eq_right_iff, one_ne_zero, imp_false, imp_self]
def firing_move (G : CFGraph) (D : CFDiv G) (v : G.V) : CFDiv G :=
  λ w => if w = v then D v - vertex_degree G v else D w + num_edges G v w
def borrowing_move (G : CFGraph) (D : CFDiv G) (v : G.V) : CFDiv G :=
  λ w => if w = v then D v + vertex_degree G v else D w - num_edges G v w
def outdeg_S (G : CFGraph) (S : Finset G.V) (v : G.V) : ℤ :=
  ∑ w ∈ (univ \ S), (num_edges G v w : ℤ)
@[simp] theorem outdeg_S_eq_sum_filter (G : CFGraph) (S : Finset G.V) (v : G.V) :
    outdeg_S G S v = ∑ w ∈ Finset.univ.filter (fun x => x ∉ S),
      (num_edges G v w : ℤ) := by
  refine Finset.sum_congr ?_ (fun _ _ => rfl)
  ext w
  simp
def set_firing (G : CFGraph) (D : CFDiv G) (S : Finset G.V) : CFDiv G :=
  λ w => if w ∈ S then D w - outdeg_S G S w else D w + outdeg_S G Sᶜ w
def firing_vector (G : CFGraph) (v : G.V) : CFDiv G :=
  λ w => if w = v then -vertex_degree G v else num_edges G v w
def principal_divisors (G : CFGraph) : AddSubgroup (CFDiv G) :=
  AddSubgroup.closure (Set.range (firing_vector G))
def linear_equiv (G : CFGraph) (D D' : CFDiv G) : Prop :=
  D' - D ∈ principal_divisors G
@[refl] lemma linear_equiv.refl (G : CFGraph) (D : CFDiv G) : linear_equiv G D D := by
  unfold linear_equiv
  simp only [sub_self, zero_mem]
@[symm] lemma linear_equiv.symm {G : CFGraph} {D D' : CFDiv G} :
  linear_equiv G D D' → linear_equiv G D' D := by
  intro h
  unfold linear_equiv at *
  simpa only [sub_eq_add_neg, neg_add_rev, neg_neg]
      using AddSubgroup.neg_mem (principal_divisors G) h
@[trans] lemma linear_equiv.trans {G : CFGraph} {D₁ D₂ D₃ : CFDiv G} :
  linear_equiv G D₁ D₂ → linear_equiv G D₂ D₃ → linear_equiv G D₁ D₃ := by
  intro h1 h2
  unfold linear_equiv at *
  simpa only [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, add_neg_cancel_comm_assoc] using
    AddSubgroup.add_mem (principal_divisors G) h2 h1
abbrev firing_script (G : CFGraph) := G.V → ℤ
def indicator_script (G : CFGraph) (S : Finset G.V) : firing_script G :=
  fun v => if v ∈ S then 1 else 0
def prin (G : CFGraph) : firing_script G →+ CFDiv G :=
  {
    toFun := fun σ v => ∑ u : G.V, (σ u - σ v) * (num_edges G v u),
    map_zero' := by
      funext v
      simp only [Pi.zero_apply, sub_self, zero_mul, sum_const_zero],
    map_add' := by
      intro σ₁ σ₂
      funext v
      dsimp only [Pi.add_apply]
      rw [← Finset.sum_add_distrib]
      apply sum_congr rfl
      intro u _
      ring,
  }
@[simp] theorem prin_apply (G : CFGraph) (σ : firing_script G) (v : G.V) :
    prin G σ v = ∑ u : G.V, (σ u - σ v) * (num_edges G v u : ℤ) := rfl
@[simp] theorem prin_const (G : CFGraph) (c : ℤ) :
    prin G (fun _ : G.V => c) = 0 := by
  funext v
  rw [prin_apply]
  simp
@[simp] theorem prin_sub_const (G : CFGraph) (σ : firing_script G) (c : ℤ) :
    prin G (fun v => σ v - c) = prin G σ := by
  funext v
  rw [prin_apply, prin_apply]
  apply Finset.sum_congr rfl
  intro u hu
  ring
def effective {G : CFGraph} (D : CFDiv G) : Prop :=
  ∀ v : G.V, D v ≥ 0
def Eff (G : CFGraph) : AddSubmonoid (CFDiv G) :=
  { carrier := {D : CFDiv G | effective D},
    zero_mem' := fun _ => le_refl 0
    add_mem' := fun {_D₁ _D₂} h_eff1 h_eff2 v => add_nonneg (h_eff1 v) (h_eff2 v) }
@[simp] lemma mem_Eff {G : CFGraph} {D : CFDiv G} : D ∈ Eff G ↔ effective D := Iff.rfl
def winnable (G : CFGraph) (D : CFDiv G) : Prop :=
  ∃ D' ∈ Eff G, linear_equiv G D D'
def deg {G : CFGraph} : CFDiv G →+ ℤ := {
  toFun := λ D => ∑ v, D v,
  map_zero' := by
    simp only [Pi.zero_apply, sum_const_zero],
  map_add' := by
    intro D₁ D₂
    simp only [Pi.add_apply, sum_add_distrib],
}
open Matrix
def laplacian_matrix (G : CFGraph) : Matrix G.V G.V ℤ :=
  λ i j => if i = j then vertex_degree G i else - (num_edges G i j)
def apply_laplacian (G : CFGraph) (σ : firing_script G) (D: CFDiv G) : CFDiv G :=
  fun v => (D v) - (laplacian_matrix G).mulVec σ v
def q_effective {G : CFGraph} (q : G.V) (D : CFDiv G) : Prop :=
  ∀ v : G.V, v ≠ q → D v ≥ 0
structure q_eff_div (G : CFGraph) (q : G.V) where
  (D : CFDiv G) (h_eff : q_effective q D)
def benevolent (G : CFGraph) (S : Finset G.V) : Prop :=
  ∀ (D : CFDiv G), ∃ (E : CFDiv G), linear_equiv G D E ∧ (∀ (v : G.V), E v < 0 → v ∈ S)
def q_reducer (G : CFGraph) (q : G.V) (σ : firing_script G) : Prop :=
  ∀ v : G.V, σ q ≤ σ v
def reduces_to (G : CFGraph) (q : G.V) (D₁ D₂: CFDiv G) : Prop :=
  ∃ σ : firing_script G, q_reducer G q σ ∧ D₂ = D₁ + prin G σ
def legal_set (G : CFGraph) (D : CFDiv G) (S : Finset G.V) : Prop :=
  ∀ v ∈ S, outdeg_S G S v ≤ D v
instance (G : CFGraph) (D : CFDiv G) (S : Finset G.V) :
    Decidable (legal_set G D S) := by
  unfold legal_set
  infer_instance
def q_reduced (G : CFGraph) (q : G.V) (D : CFDiv G) : Prop :=
  q_effective q D ∧
  ∀ S : Finset G.V, q ∉ S → S.Nonempty → ¬ legal_set G D S
def active (G : CFGraph) (q : G.V) (D : CFDiv G) (v : G.V) : Prop :=
  ∃ σ : firing_script G, q_reducer G q σ ∧ q_effective q (D + prin G σ) ∧ σ q < σ v
noncomputable def reduction_excess (G : CFGraph) (q : G.V) (D : CFDiv G) : ℤ := by
  classical
  exact (∑ v : G.V, if active G q D v then D v else 0)


