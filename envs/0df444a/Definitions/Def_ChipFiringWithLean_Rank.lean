-- Prove2me | Definitions.Def_ChipFiringWithLean_Rank
-- name    : ChipFiringWithLean_Rank
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-23T21:45:10.599404+00:00
-- url     : https://prove2.me/theorems/9031ad8c-8004-4f4e-a808-9e48160bfe3e
-- title:
--   Rank
-- statement:
--   Definitions and structural lemmas for Rank, from DhyeyMavani2003/chip-firing-with-lean contributors (see pinned LICENSE and source headers)'s pinned Chip-firing on multigraphs and Riemann-Roch for graphs development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/Rank.lean

module
public import Definitions.Def_ChipFiringWithLean_Basic
public import Theorems.Thm_deg_of_eff_nonneg
public import Theorems.Thm_deg_one_chip
public import Theorems.Thm_eff_one_chip
public import Theorems.Thm_legal_set_empty
public import Theorems.Thm_linear_equiv_preserves_deg
attribute [local simp] deg_one_chip
attribute [local simp] legal_set_empty


set_option autoImplicit true
@[expose] public section
@[expose] public section
set_option trace.split.failure true
open Multiset Finset
def maximal_unwinnable (G : CFGraph) (D : CFDiv G) : Prop :=
  ¬winnable G D ∧ ∀ v : G.V, winnable G (D + one_chip v)
def eff_of_degree (G : CFGraph) (k : ℤ) : Set (CFDiv G) :=
  {E | effective E ∧ deg E = k}
lemma eff_of_degree_nonempty (G : CFGraph) {k : ℤ} (h_nonneg : 0 ≤ k) :
  (eff_of_degree G k).Nonempty := by
  let v : G.V := Classical.arbitrary G.V
  refine ⟨k.toNat • one_chip v, ?_, ?_⟩
  · exact (Eff G).nsmul_mem (eff_one_chip v) k.toNat
  · simpa only [nsmul_eq_mul, deg_one_chip, Int.toNat_of_nonneg h_nonneg, mul_one] using
      (AddMonoidHom.map_nsmul deg k.toNat (one_chip v))
def rank_geq (G : CFGraph) (D : CFDiv G) (k : ℤ) : Prop :=
  ∀ E ∈ eff_of_degree G k, winnable G (D-E)
def rank_eq (G : CFGraph) (D : CFDiv G) (r : ℤ) : Prop :=
  rank_geq G D r ∧ ¬(rank_geq G D (r+1))
lemma rank_geq_neg (G : CFGraph) (D : CFDiv G) (k : ℤ): (k < 0) → rank_geq G D k := by
  intro k_neg E ⟨h_eff_E, h_deg_E⟩
  have := deg_of_eff_nonneg E h_eff_E
  linarith
lemma deg_winnable_nonneg (G : CFGraph) (D : CFDiv G) (h_winnable : winnable G D) : deg D ≥ 0 := by
  rcases h_winnable with ⟨D', h_D'_eff, h_lequiv⟩
  have same_deg: deg D = deg D' := linear_equiv_preserves_deg G D D' h_lequiv
  rw [same_deg]
  exact deg_of_eff_nonneg D' h_D'_eff
lemma rank_le_degree (G : CFGraph) (D : CFDiv G) : ∀ (r : ℤ), r ≥ 0 → rank_geq G D r → r ≤ deg D := by
  intro r r_nonneg h_rank
  contrapose! h_rank
  unfold rank_geq; push Not
  rcases eff_of_degree_nonempty G r_nonneg with ⟨E, h_E_eff, h_E_deg⟩
  use E
  constructor
  -- First conjunct: show that E is effecitive of the correct degree
  exact ⟨h_E_eff, h_E_deg⟩
  -- Second conjunct: show that D-E is not winnable
  contrapose! h_rank
  have deg_nonneg := deg_winnable_nonneg G (D-E) h_rank
  simp only [map_sub, Int.sub_nonneg] at deg_nonneg
  rw [h_E_deg] at deg_nonneg
  exact deg_nonneg
lemma rank_exists_helper (G : CFGraph) (D : CFDiv G) (m : ℕ):  ¬ (rank_geq G D m) → ∃ r < (m:ℤ), rank_eq G D r := by
  induction m with
  | zero =>
  · intro h_rank_geq
    exact ⟨-1, by norm_num, rank_geq_neg G D (-1) (by norm_num), h_rank_geq⟩
  | succ m ih =>
    intro h_rank_geq
    by_cases h_rank_m : rank_geq G D m
    · exact ⟨m, by norm_num, h_rank_m, h_rank_geq⟩
    ·
      specialize ih h_rank_m
      rcases ih with ⟨r, h_r_lt, h_rank_eq⟩
      have r_le : r < m + 1 := by
        linarith [h_r_lt]
      exact ⟨r, r_le, h_rank_eq⟩
lemma rank_exists (G : CFGraph) (D : CFDiv G) :
  ∃ r : ℤ, rank_eq G D r := by
  let m := (deg D).toNat + 1
  have h_not_geq : ¬(rank_geq G D m) := by
    intro h_rank_geq
    have h_le := rank_le_degree G D m (by linarith) h_rank_geq
    have m_ge : m ≥ deg D + 1:= by
      dsimp only [Int.natCast_add, Int.cast_ofNat_Int, m]
      simp only [Int.ofNat_toNat, ge_iff_le, add_le_add_iff_right, le_sup_left]
    linarith
  rcases rank_exists_helper G D m h_not_geq with ⟨r, _, h_rank_eq⟩
  exact ⟨r, h_rank_eq⟩
noncomputable def rank (G : CFGraph) (D : CFDiv G) : ℤ :=
  Classical.choose (rank_exists G D)


