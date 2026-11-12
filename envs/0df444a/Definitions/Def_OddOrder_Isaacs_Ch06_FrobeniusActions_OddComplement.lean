-- Prove2me | Definitions.Def_OddOrder_Isaacs_Ch06_FrobeniusActions_OddComplement
-- name    : OddOrder_Isaacs_Ch06_FrobeniusActions_OddComplement
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T05:45:06.4432+00:00
-- url     : https://prove2.me/theorems/b1d3fcf8-601e-49e8-a809-1be2b0b492b3
-- title:
--   Odd Frobenius complements: prime-order subgroups are normal (Huppert V.8.18 b)
-- statement:
--   Proves the structural fact used by Peterfalvi (13.17.c), Huppert, *Endliche Gruppen I*, Kapitel V, Satz 8.18 b): in a Frobenius complement of odd order, every subgroup of prime order is normal. The file works with the action-based form of a Frobenius complement, `IsFrobeniusAction A U`.
--
--   The bundle consists of lemmas only.
--
--   The bundle also proves 2 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Isaacs/Ch06_FrobeniusActions/OddComplement.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Isaacs/Ch06_FrobeniusActions/OddComplement.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Isaacs_Ch06_FrobeniusActions_Main
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_Main_CommutatorBasics
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_Main_ThreeSubgroupsCoprime
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_Main_BaerTrick
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_Main_ChainNilpotent
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_ForwardFromCh03
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_Main_ThreeSubgroups
import Definitions.Def_OddOrder_GroupTheory_ElementaryAbelian
import Mathlib.GroupTheory.SpecificGroups.ZGroup

namespace OddOrder.Isaacs.Ch06

open scoped IsMulCommutative

open scoped commutatorElement

open OddOrder.Isaacs.Ch04

/-- In a finite cyclic group, a subgroup of prime order is unique: two subgroups of the same
prime order `q` coincide.  (`H ⊔ K` is elementary abelian of exponent `q` and cyclic, hence of
order dividing `q`, forcing `H = H ⊔ K = K`.)  Local copy for use below `OddOrder.BG`. -/
theorem eq_of_card_eq_prime_of_isCyclic {C : Type*} [Group C] [Finite C] [IsCyclic C]
    {q : ℕ} (hq : q.Prime) {H K : Subgroup C}
    (hH : Nat.card ↥H = q) (hK : Nat.card ↥K = q) : H = K := by
  have : Fact q.Prime := ⟨hq⟩
  let : CommGroup C := IsCyclic.commGroup
  have hHel : H.IsElementaryAbelian q := Subgroup.IsElementaryAbelian.of_card_prime hH
  have hKel : K.IsElementaryAbelian q := Subgroup.IsElementaryAbelian.of_card_prime hK
  have hcent : H ≤ Subgroup.centralizer (K : Set C) := fun x _ =>
    Subgroup.mem_centralizer_iff.mpr (fun y _ => mul_comm y x)
  have hsupel : (H ⊔ K).IsElementaryAbelian q := hHel.sup_of_le_centralizer hKel hcent
  have : IsCyclic ↥(H ⊔ K) := inferInstance
  have hexp : Monoid.exponent ↥(H ⊔ K) ∣ q :=
    Monoid.exponent_dvd_of_forall_pow_eq_one (fun x => hsupel.2 x)
  have hcarddvd : Nat.card ↥(H ⊔ K) ∣ q := by rwa [IsCyclic.exponent_eq_card] at hexp
  have hcardle : Nat.card ↥(H ⊔ K) ≤ q := Nat.le_of_dvd hq.pos hcarddvd
  have hHK : H = H ⊔ K := Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [hH]; exact hcardle)
  have hKK : K = H ⊔ K := Subgroup.eq_of_le_of_card_ge le_sup_right (by rw [hK]; exact hcardle)
  exact hHK.trans hKK.symm

variable {A U : Type*} [Group A] [Finite A] [Group U] [Finite U] [Nontrivial U]
  [MulDistribMulAction A U]

/-- **Step 1.** A finite Frobenius complement of odd order is a Z-group: every Sylow subgroup
is cyclic.  Each Sylow `p`-subgroup has a unique subgroup of order `p` (Isaacs Cor 6.10,
`subgroups_card_prime_unique_of_frobeniusAction_sylow`) and `p` is odd, so it is cyclic
(Isaacs Thm 6.11, `isCyclic_of_subgroups_card_prime_unique_of_odd`). -/
theorem isZGroup_of_isFrobeniusAction_of_odd
    (hFrob : IsFrobeniusAction A U) (hodd : Odd (Nat.card A)) :
    IsZGroup A := by
  refine ⟨fun p hp P => ?_⟩
  have : Fact p.Prime := ⟨hp⟩
  by_cases hpA : p ∣ Nat.card A
  · -- `p` is an odd prime dividing `|A|`; the Sylow `p`-subgroup is cyclic.
    have hp_ne_two : p ≠ 2 := by
      rintro rfl
      obtain ⟨k, hk⟩ := hpA
      obtain ⟨m, hm⟩ := hodd
      omega
    have hp_odd : Odd p := hp.odd_of_ne_two hp_ne_two
    exact isCyclic_of_subgroups_card_prime_unique_of_odd P.isPGroup' hp_odd
      (subgroups_card_prime_unique_of_frobeniusAction_sylow hFrob P)
  · -- `p ∤ |A|` forces the Sylow `p`-subgroup to be trivial, hence cyclic.
    have hcard : Nat.card P = 1 := by
      rcases P.isPGroup'.card_eq_or_dvd with h1 | hd
      · exact h1
      · exact absurd (hd.trans (Subgroup.card_subgroup_dvd_card P.toSubgroup)) hpA
    have : Subsingleton P := (Nat.card_eq_one_iff_unique.mp hcard).1
    exact isCyclic_of_subsingleton

end OddOrder.Isaacs.Ch06


