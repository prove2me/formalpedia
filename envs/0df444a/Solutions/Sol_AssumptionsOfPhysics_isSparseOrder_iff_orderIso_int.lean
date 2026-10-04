-- Prove2me | solution 1 for AssumptionsOfPhysics.isSparseOrder_iff_orderIso_int
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T04:20:04.695289+00:00
-- url     : https://prove2.me/submissions/aadc84a0-61f3-4664-bd0a-c6f959f7ee00

import Mathlib
import Definitions.Def_AoP_ExperimentalDomains
import Definitions.Def_AoP_PropertiesQuantities

set_option autoImplicit false

namespace P2M2270294e

open Order

theorem toZ_succ_le {ι : Type*} [LinearOrder ι] [SuccOrder ι] [IsSuccArchimedean ι]
    [PredOrder ι] (i0 i : ι) (hi : ¬ IsMax i) :
    toZ i0 (succ i) ≤ toZ i0 i + 1 := by
  rcases le_or_gt i0 i with h | h
  · have hn := iterate_succ_toZ (i0 := i0) i h
    have hnn : ((toZ i0 i).toNat : ℤ) = toZ i0 i := Int.toNat_of_nonneg (toZ_nonneg h)
    have h2 : succ^[(toZ i0 i).toNat + 1] i0 = succ i := by
      rw [Function.iterate_succ_apply', hn]
    have h3 := toZ_iterate_succ_le (i0 := i0) ((toZ i0 i).toNat + 1)
    rw [h2] at h3
    push_cast at h3
    omega
  · have hs : succ i ≤ i0 := Order.succ_le_of_lt h
    rcases hs.lt_or_eq with hs | hs
    · have hm := iterate_pred_toZ (i0 := i0) (succ i) hs
      have hneg := toZ_neg (i0 := i0) hs
      have hmm : ((-toZ i0 (succ i)).toNat : ℤ) = -toZ i0 (succ i) :=
        Int.toNat_of_nonneg (by omega)
      have h2 : pred^[(-toZ i0 (succ i)).toNat + 1] i0 = i := by
        rw [Function.iterate_succ_apply', hm, Order.pred_succ_of_not_isMax hi]
      have h3 := toZ_iterate_pred_ge (i0 := i0) ((-toZ i0 (succ i)).toNat + 1)
      rw [h2] at h3
      push_cast at h3
      omega
    · have h2 : pred^[1] i0 = i := by
        rw [Function.iterate_one, ← hs, Order.pred_succ_of_not_isMax hi]
      have h3 := toZ_iterate_pred_ge (i0 := i0) 1
      rw [h2] at h3
      rw [hs, toZ_of_eq]
      push_cast at h3
      omega

theorem range_toZ_ordConnected {ι : Type*} [LinearOrder ι] [SuccOrder ι] [IsSuccArchimedean ι]
    [PredOrder ι] (i0 : ι) : (Set.range (toZ i0)).OrdConnected := by
  refine ⟨?_⟩
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ c ⟨hc1, hc2⟩
  have key : ∀ k : ℕ, toZ i0 a + k ≤ toZ i0 b → toZ i0 a + k ∈ Set.range (toZ i0) := by
    intro k
    induction k with
    | zero => intro _; exact ⟨a, by simp⟩
    | succ k ih =>
      intro hk
      obtain ⟨p, hp⟩ := ih (by push_cast at hk; omega)
      have hpb : toZ i0 p < toZ i0 b := by push_cast at hk; omega
      have hpb' : p < b := toZ_lt_toZ.mp hpb
      have hpm : ¬ IsMax p := not_isMax_of_lt hpb'
      have h1 := toZ_succ_le i0 p hpm
      have h2 : toZ i0 p < toZ i0 (succ p) :=
        toZ_lt_toZ.mpr (Order.lt_succ_of_not_isMax hpm)
      refine ⟨succ p, ?_⟩
      push_cast
      omega
  have hk := key (c - toZ i0 a).toNat (by omega)
  have : toZ i0 a + ((c - toZ i0 a).toNat : ℤ) = c := by omega
  rwa [this] at hk

theorem exists_of_succPred {ι : Type*} [LinearOrder ι] [SuccOrder ι] [IsSuccArchimedean ι]
    [PredOrder ι] : ∃ S : Set ℤ, S.OrdConnected ∧ Nonempty (ι ≃o S) := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · refine ⟨∅, Set.ordConnected_empty, ⟨?_⟩⟩
    exact
      { toFun := fun x => (hι.false x).elim
        invFun := fun x => (x.2 : False).elim
        left_inv := fun x => (hι.false x).elim
        right_inv := fun x => (x.2 : False).elim
        map_rel_iff' := fun {a} => (hι.false a).elim }
  · exact ⟨_, range_toZ_ordConnected hι.some, ⟨orderIsoRangeToZOfLinearSuccPredArch⟩⟩

end P2M2270294e

open AssumptionsOfPhysics in
theorem solution (Q : Type*) [LinearOrder Q] :
    IsSparseOrder Q ↔ ∃ S : Set ℤ, S.OrdConnected ∧ Nonempty (Q ≃o S) := by
  constructor
  · intro h
    letI : LocallyFiniteOrder Q :=
      LocallyFiniteOrder.ofIcc Q (fun a b => (h a b).toFinset) (by intro a b x; simp)
    letI : SuccOrder Q := LinearLocallyFiniteOrder.succOrder Q
    letI : PredOrder Q := LinearLocallyFiniteOrder.predOrder Q
    exact P2M2270294e.exists_of_succPred
  · rintro ⟨S, -, ⟨e⟩⟩ a b
    let f : Q → ℤ := fun q => ((e q : S) : ℤ)
    have hf : Function.Injective f := fun x y hxy => e.injective (Subtype.ext hxy)
    refine ((Set.finite_Icc (f a) (f b)).preimage hf.injOn).subset ?_
    rintro x ⟨hx1, hx2⟩
    exact ⟨(e.monotone hx1 : e a ≤ e x), (e.monotone hx2 : e x ≤ e b)⟩
