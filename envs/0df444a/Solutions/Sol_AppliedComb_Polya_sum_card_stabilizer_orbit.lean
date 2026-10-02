-- Prove2me | solution 1 for AppliedComb.Polya.sum_card_stabilizer_orbit
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T11:15:22.765107+00:00
-- url     : https://prove2.me/submissions/d828f729-b28c-4c00-9495-984578b1d2ec

import Mathlib

open MulAction in
theorem stab_card_eq_749fe71b {G 𝒞 : Type*} [Group G] [Fintype G] [MulAction G 𝒞] (C : 𝒞) (π : G) :
    Nat.card (MulAction.stabilizer G (π • C)) = Nat.card (MulAction.stabilizer G C) := by
  rw [MulAction.stabilizer_smul_eq_stabilizer_map_conj]
  exact Nat.card_congr ((Subgroup.equivMapOfInjective _ _ (MulAut.conj π).injective).symm.toEquiv)

theorem solution {G 𝒞 : Type*} [Group G] [Fintype G] [Fintype 𝒞]
    [DecidableEq 𝒞] [MulAction G 𝒞] (C : 𝒞) :
    ∑ C' ∈ Finset.univ.filter (fun C' : 𝒞 => ∃ π : G, π • C = C'),
        Nat.card (MulAction.stabilizer G C') = Fintype.card G := by
  rw [Finset.sum_congr rfl (g := fun _ => Nat.card (MulAction.stabilizer G C)) (by
    intro C' hC'
    obtain ⟨π, rfl⟩ := (Finset.mem_filter.mp hC').2
    exact stab_card_eq_749fe71b C π)]
  rw [Finset.sum_const, smul_eq_mul]
  have hf : (Finset.univ.filter (fun C' : 𝒞 => ∃ π : G, π • C = C')).card
      = Nat.card (MulAction.orbit G C) := by
    rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
    rfl
  rw [hf, ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq, mul_comm, ← MulAction.index_stabilizer,
    Subgroup.card_mul_index]
