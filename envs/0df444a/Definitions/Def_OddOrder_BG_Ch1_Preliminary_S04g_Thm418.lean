-- Prove2me | Definitions.Def_OddOrder_BG_Ch1_Preliminary_S04g_Thm418
-- name    : OddOrder_BG_Ch1_Preliminary_S04g_Thm418
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T06:17:57.583062+00:00
-- url     : https://prove2.me/theorems/9a3e18c7-2056-40ae-a62e-1f4f7dde6b7b
-- title:
--   BG §4H: Theorem 4.18, $p$-complement transfer and the characteristic Sylow series
-- statement:
--   The downstream supporting layer of Bender–Glauberman Theorem 4.18, supplying BG Theorem 4.20(c): transfer of $O_{r\ne p}$-cores of a normal $p$-complement, quotient transport lemmas and the characteristic Sylow series.
--
--   Main definitions: `quotient_oPiCore_mulEquiv_sylow_of_hasNormalPComplement` (the quotient by the canonical normal $p$-complement is isomorphic to a Sylow $p$-subgroup), `CharacteristicSylowLayer` and `CharacteristicSylowStep` (factors of the characteristic Sylow series of Theorem 4.20(c)), `top_of_hasNormalPComplement`, `lift_oPiCore_of_hasNormalPComplement_ne`, `upper` and `lower`.
--
--   The bundle also proves 34 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/Ch1_Preliminary/S04g_Thm418.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/BG/Ch1_Preliminary/S04g_Thm418.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_BG_Ch1_Preliminary_S04g_Thm418Core

namespace OddOrder.BG.Ch1.S04

open OddOrder.GroupTheory

open OddOrder.Isaacs

open scoped commutatorElement

section Thm418

variable {G : Type*} [Group G] [Finite G]

/-- A normal `p`-complement is the canonical `{r | r != p}`-core.

This is the bridge needed in BG Thm 4.20(c): once Thm 4.18(b) produces a normal
`p`-complement, the complement can be taken to be the characteristic subgroup
`O_{r | r != p}(G)`. -/
theorem normalPComplement_eq_oPiCore_compl {p : ℕ} [Fact p.Prime] {K : Subgroup G}
    [K.Normal] (hK : ∀ P : Sylow p G, Subgroup.IsComplement' K (P : Subgroup G)) :
    K = Ch03.oPiCore {r : ℕ | r ≠ p} G := by
  classical
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow p G))
  have hKP := hK P
  have hK_pi : Ch03.Subgroup.IsPiGroup {r : ℕ | r ≠ p} K := by
    intro q hq hq_eq
    have hq_dvd_K : q ∣ Nat.card ↥K := Nat.dvd_of_mem_primeFactors hq
    have hp_dvd_index : p ∣ (P : Subgroup G).index := by
      rw [hKP.index_eq_card, ← hq_eq]
      exact hq_dvd_K
    exact P.not_dvd_index hp_dvd_index
  have hK_le : K ≤ Ch03.oPiCore {r : ℕ | r ≠ p} G :=
    Ch03.Subgroup.IsPiGroup.le_oPiCore hK_pi
  have hK_hall : Ch03.IsHallSubgroup {r : ℕ | r ≠ p} K := by
    refine ⟨hK_pi, ?_⟩
    intro q hq hq_ne_p
    have hidx : K.index = Nat.card ↥(P : Subgroup G) := hKP.symm.index_eq_card
    have hqP : q ∈ (Nat.card ↥(P : Subgroup G)).primeFactors := by
      simpa [hidx] using hq
    have hPp : IsPGroup p ↥(P : Subgroup G) := P.isPGroup'
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hPp
    rw [hk, Nat.mem_primeFactors] at hqP
    have hq_eq_p : q = p :=
      (Nat.prime_dvd_prime_iff_eq hqP.1 (Fact.out : p.Prime)).mp
        (hqP.1.dvd_of_dvd_pow hqP.2.1)
    exact hq_ne_p hq_eq_p
  have hO_le : Ch03.oPiCore {r : ℕ | r ≠ p} G ≤ K :=
    Ch03.Subgroup.IsPiGroup.normal_le_hall
      (Ch03.oPiCore.isPiGroup {r : ℕ | r ≠ p}) hK_hall
  exact le_antisymm hK_le hO_le

/-- If `G` has a normal `p`-complement, then the canonical core is such a complement. -/
theorem oPiCore_isComplement_of_hasNormalPComplement {p : ℕ} [Fact p.Prime]
    (hG : Ch05.HasNormalPComplement p G) (P : Sylow p G) :
    Subgroup.IsComplement' (Ch03.oPiCore {r : ℕ | r ≠ p} G) (P : Subgroup G) := by
  rcases hG with ⟨K, hK_normal, hK_compl⟩
  have : K.Normal := hK_normal
  have hK_eq : K = Ch03.oPiCore {r : ℕ | r ≠ p} G :=
    normalPComplement_eq_oPiCore_compl (K := K) hK_compl
  rw [← hK_eq]
  exact hK_compl P

/-- The quotient by the canonical normal `p`-complement is isomorphic to any Sylow
`p`-subgroup. -/
noncomputable def quotient_oPiCore_mulEquiv_sylow_of_hasNormalPComplement {p : ℕ}
    [Fact p.Prime] (hG : Ch05.HasNormalPComplement p G) (P : Sylow p G) :
    G ⧸ Ch03.oPiCore {r : ℕ | r ≠ p} G ≃* (P : Subgroup G) :=
  (oPiCore_isComplement_of_hasNormalPComplement hG P).symm.QuotientMulEquiv

/-- If `G` has a normal `p`-complement, then quotienting by the canonical complement
leaves a `p`-group. -/
theorem isPGroup_quotient_oPiCore_of_hasNormalPComplement {p : ℕ} [Fact p.Prime]
    (hG : Ch05.HasNormalPComplement p G) :
    IsPGroup p (G ⧸ Ch03.oPiCore {r : ℕ | r ≠ p} G) := by
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow p G))
  exact P.isPGroup'.of_equiv
    (quotient_oPiCore_mulEquiv_sylow_of_hasNormalPComplement hG P).symm

/-- The canonical normal `p`-complement quotient has the same cardinality as a Sylow
`p`-subgroup. -/
theorem card_quotient_oPiCore_eq_card_sylow_of_hasNormalPComplement {p : ℕ}
    [Fact p.Prime] (hG : Ch05.HasNormalPComplement p G) (P : Sylow p G) :
    Nat.card (G ⧸ Ch03.oPiCore {r : ℕ | r ≠ p} G) = Nat.card ↥(P : Subgroup G) := by
  exact Nat.card_congr
    (quotient_oPiCore_mulEquiv_sylow_of_hasNormalPComplement hG P).toEquiv

/-- A normal `p`-free subgroup whose quotient is a `p`-group is a normal
`p`-complement.

This is the ambient lift used after applying BG Thm 4.20(c) inside a normal subgroup:
once the candidate kernel is normal in `G`, the remaining work is only to identify the
quotient as a `p`-group. -/
theorem hasNormalPComplement_of_normal_pPrime_of_quotient_isPGroup {p : ℕ}
    [Fact p.Prime] {N : Subgroup G} [N.Normal]
    (hNpPrime : ¬ p ∣ Nat.card ↥N) (hquot : IsPGroup p (G ⧸ N)) :
    Ch05.HasNormalPComplement p G := by
  classical
  obtain ⟨a, hquot_card⟩ := IsPGroup.iff_card.mp hquot
  have hquot_index : N.index = p ^ a := by
    rw [Subgroup.index_eq_card]
    exact hquot_card
  refine ⟨N, inferInstance, fun P => ?_⟩
  have h_fact_a : (Nat.card G).factorization p = a := by
    have hN_card_mul : Nat.card ↥N * N.index = Nat.card G :=
      Subgroup.card_mul_index N
    have h_total : Nat.card G = Nat.card ↥N * p ^ a := by
      rw [← hN_card_mul, hquot_index]
    have hN_card_ne : Nat.card ↥N ≠ 0 := ne_of_gt Nat.card_pos
    have hpa_ne : p ^ a ≠ 0 := ne_of_gt (pow_pos (Fact.out : p.Prime).pos a)
    rw [h_total, Nat.factorization_mul hN_card_ne hpa_ne, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hNpPrime,
      Nat.factorization_pow_self (Fact.out : p.Prime), zero_add]
  have hP_card : Nat.card ↥(P : Subgroup G) = p ^ a := by
    rw [P.card_eq_multiplicity, h_fact_a]
  have h_card_mul : Nat.card ↥N * Nat.card ↥(P : Subgroup G) = Nat.card G := by
    rw [hP_card, ← hquot_index]
    exact Subgroup.card_mul_index N
  have h_coprime : Nat.Coprime (Nat.card ↥N) (Nat.card ↥(P : Subgroup G)) := by
    rw [hP_card]
    exact (((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hNpPrime).symm).pow_right a
  exact Subgroup.isComplement'_of_coprime h_card_mul h_coprime

/-- Characteristic subgroup variant of
`hasNormalPComplement_of_normal_pPrime_of_quotient_isPGroup`.

If `K char H` and `H ⊴ G`, then the image of `K` in `G` is normal, so a `p`-group
quotient by that image gives a normal `p`-complement in `G`. -/
theorem hasNormalPComplement_of_characteristic_subgroup_quotient_isPGroup {p : ℕ}
    [Fact p.Prime] {H : Subgroup G} [H.Normal] {K : Subgroup H}
    (hK_char : K.Characteristic) (hKpPrime : ¬ p ∣ Nat.card ↥K)
    (hquot : IsPGroup p (G ⧸ K.map H.subtype)) :
    Ch05.HasNormalPComplement p G := by
  classical
  have : K.Characteristic := hK_char
  have : (K.map H.subtype).Normal := inferInstance
  refine hasNormalPComplement_of_normal_pPrime_of_quotient_isPGroup
    (N := K.map H.subtype) ?_ hquot
  rw [Subgroup.card_map_of_injective H.subtype_injective]
  exact hKpPrime

/-- If both quotient layers `H/K` and `G/H` are `p`-groups, then the ambient quotient by
the image of `K` is a `p`-group. -/
theorem isPGroup_quotient_map_subtype_of_isPGroup_quotient_of_isPGroup_quotient {p : ℕ}
    [Fact p.Prime] {H : Subgroup G} [H.Normal] {K : Subgroup H}
    [K.Normal] [(K.map H.subtype).Normal]
    (hHK : IsPGroup p (↥H ⧸ K)) (hGH : IsPGroup p (G ⧸ H)) :
    IsPGroup p (G ⧸ K.map H.subtype) := by
  classical
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hHK
  obtain ⟨b, hb⟩ := IsPGroup.iff_card.mp hGH
  refine IsPGroup.of_card (n := a + b) ?_
  rw [← Subgroup.index_eq_card, Subgroup.index_map_subtype,
    Subgroup.index_eq_card, Subgroup.index_eq_card, ha, hb, ← pow_add]

/-- Characteristic-subgroup version of the quotient-extension bridge for normal
`p`-complements. -/
theorem hasNormalPComplement_of_characteristic_subgroup_quotient_and_outer_quotient_isPGroup
    {p : ℕ} [Fact p.Prime] {H : Subgroup G} [H.Normal] {K : Subgroup H}
    [K.Normal] (hK_char : K.Characteristic) (hKpPrime : ¬ p ∣ Nat.card ↥K)
    (hHK : IsPGroup p (↥H ⧸ K)) (hGH : IsPGroup p (G ⧸ H)) :
    Ch05.HasNormalPComplement p G := by
  classical
  have : K.Characteristic := hK_char
  have : (K.map H.subtype).Normal := inferInstance
  exact hasNormalPComplement_of_characteristic_subgroup_quotient_isPGroup
    (H := H) (K := K) hK_char hKpPrime
    (isPGroup_quotient_map_subtype_of_isPGroup_quotient_of_isPGroup_quotient
      (p := p) (H := H) (K := K) hHK hGH)

/-- The `O_{r | r != p}` version of the quotient-extension bridge. -/
theorem hasNormalPComplement_of_oPiCore_quotient_and_outer_quotient_isPGroup {p : ℕ}
    [Fact p.Prime] {H : Subgroup G} [H.Normal]
    (hlocal : IsPGroup p (↥H ⧸ Ch03.oPiCore {r : ℕ | r ≠ p} ↥H))
    (houter : IsPGroup p (G ⧸ H)) :
    Ch05.HasNormalPComplement p G :=
  hasNormalPComplement_of_characteristic_subgroup_quotient_and_outer_quotient_isPGroup
    (H := H) (K := Ch03.oPiCore {r : ℕ | r ≠ p} ↥H)
    (Ch03.oPiCore.characteristic {r : ℕ | r ≠ p} ↥H)
    (not_dvd_card_oPiCore (G := ↥H) (p := p) (π := {r : ℕ | r ≠ p}) (by simp))
    hlocal houter

/-- If a normal subgroup has a normal `p`-complement and the outer quotient is a
`p`-group, then the ambient group has a normal `p`-complement. -/
theorem hasNormalPComplement_of_normal_subgroup_hasNormalPComplement_of_quotient_isPGroup
    {p : ℕ} [Fact p.Prime] {H : Subgroup G} [H.Normal]
    (hH : Ch05.HasNormalPComplement p ↥H) (houter : IsPGroup p (G ⧸ H)) :
    Ch05.HasNormalPComplement p G :=
  hasNormalPComplement_of_oPiCore_quotient_and_outer_quotient_isPGroup
    (H := H) (isPGroup_quotient_oPiCore_of_hasNormalPComplement hH) houter

/-- The canonical normal `p`-complement preserves the `q`-part of the group order
for `q != p`. -/
theorem factorization_card_oPiCore_eq_factorization_card_of_hasNormalPComplement_ne
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (hpq : q ≠ p)
    (hG : Ch05.HasNormalPComplement p G) :
    (Nat.card ↥(Ch03.oPiCore {r : ℕ | r ≠ p} G)).factorization q =
      (Nat.card G).factorization q := by
  classical
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow p G))
  have hcomp : Subgroup.IsComplement' (Ch03.oPiCore {r : ℕ | r ≠ p} G)
      (P : Subgroup G) := oPiCore_isComplement_of_hasNormalPComplement hG P
  have hmul : Nat.card ↥(Ch03.oPiCore {r : ℕ | r ≠ p} G) *
      Nat.card ↥(P : Subgroup G) = Nat.card G := hcomp.card_mul_card
  have hP_q_zero : (Nat.card ↥(P : Subgroup G)).factorization q = 0 := by
    rw [P.card_eq_multiplicity]
    refine Nat.factorization_eq_zero_of_not_dvd ?_
    intro hq_dvd
    have hq_eq_p : q = p :=
      (Nat.prime_dvd_prime_iff_eq (Fact.out : q.Prime) (Fact.out : p.Prime)).mp
        ((Fact.out : q.Prime).dvd_of_dvd_pow hq_dvd)
    exact hpq hq_eq_p
  have hfact : (Nat.card G).factorization q =
      (Nat.card ↥(Ch03.oPiCore {r : ℕ | r ≠ p} G)).factorization q := by
    rw [← hmul, Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne',
      Finsupp.add_apply, hP_q_zero, add_zero]
  exact hfact.symm

/-- The canonical normal `p`-complement preserves the Sylow cardinalities for primes
`q != p`. -/
theorem card_sylow_oPiCore_eq_card_sylow_of_hasNormalPComplement_ne {p q : ℕ}
    [Fact p.Prime] [Fact q.Prime] (hpq : q ≠ p)
    (hG : Ch05.HasNormalPComplement p G)
    (QK : Sylow q ↥(Ch03.oPiCore {r : ℕ | r ≠ p} G)) (QG : Sylow q G) :
    Nat.card ↥(QK : Subgroup ↥(Ch03.oPiCore {r : ℕ | r ≠ p} G)) =
      Nat.card ↥(QG : Subgroup G) := by
  classical
  have hfact :=
    factorization_card_oPiCore_eq_factorization_card_of_hasNormalPComplement_ne
      (G := G) hpq hG
  rw [QK.card_eq_multiplicity, QG.card_eq_multiplicity]
  exact congrArg (fun n => q ^ n) hfact

/-- A characteristic subgroup with Sylow `q`-cardinality supplies a normal Sylow
`q`-subgroup.  This is the packaged extraction form used after BG Theorem 4.20(c)
has produced the last characteristic layer. -/
theorem exists_normal_sylow_of_exists_characteristic_subgroup_card_sylow
    {q : ℕ} [Fact q.Prime]
    (hK :
      ∃ L : Subgroup G,
        L.Characteristic ∧ Nat.card ↥L = Nat.card ↥((default : Sylow q G) : Subgroup G)) :
    ∃ Q : Sylow q G, (Q : Subgroup G).Normal := by
  classical
  obtain ⟨L, hL_char, hL_card⟩ := hK
  exact Ch01.exists_normal_sylow_of_characteristic_card_eq_sylow hL_char
    (default : Sylow q G) hL_card

/-- If a characteristic subgroup has a bottom quotient with Sylow `q`-cardinality,
then it supplies a normal Sylow `q`-subgroup. -/
theorem exists_normal_sylow_of_characteristic_quotient_bot_card_eq_sylow
    {q : ℕ} [Fact q.Prime] {A : Subgroup G} (hA_char : A.Characteristic)
    (hcard :
      Nat.card (A ⧸ ((⊥ : Subgroup G).subgroupOf A)) =
        Nat.card ↥((default : Sylow q G) : Subgroup G)) :
    ∃ Q : Sylow q G, (Q : Subgroup G).Normal := by
  classical
  exact exists_normal_sylow_of_exists_characteristic_subgroup_card_sylow
    ⟨A, hA_char,
      (Subgroup.nat_card_quotient_bot_subgroupOf_eq (H := A)).symm.trans hcard⟩

/-- If a quotient layer inside the canonical normal `p`-complement has the
`q`-Sylow cardinality, then mapping the layer into the ambient group preserves
characteristic endpoints and the `q`-Sylow cardinality, for `q != p`.

This is the quotient-layer version of the BG Theorem 4.20(c) induction lift. -/
theorem characteristic_quotient_layer_lift_of_hasNormalPComplement_ne
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (hpq : q ≠ p)
    (hG : Ch05.HasNormalPComplement p G)
    {A B : Subgroup ↥(Ch03.oPiCore {r : ℕ | r ≠ p} G)}
    (hBA : B ≤ A) (hA_char : A.Characteristic) (hB_char : B.Characteristic)
    (hcard :
      Nat.card (A ⧸ B.subgroupOf A) =
        Nat.card ↥((default : Sylow q ↥(Ch03.oPiCore {r : ℕ | r ≠ p} G)) :
          Subgroup ↥(Ch03.oPiCore {r : ℕ | r ≠ p} G))) :
    (A.map (Ch03.oPiCore {r : ℕ | r ≠ p} G).subtype).Characteristic ∧
      (B.map (Ch03.oPiCore {r : ℕ | r ≠ p} G).subtype).Characteristic ∧
        Nat.card
            ((A.map (Ch03.oPiCore {r : ℕ | r ≠ p} G).subtype) ⧸
              ((B.map (Ch03.oPiCore {r : ℕ | r ≠ p} G).subtype).subgroupOf
                (A.map (Ch03.oPiCore {r : ℕ | r ≠ p} G).subtype))) =
          Nat.card ↥((default : Sylow q G) : Subgroup G) := by
  classical
  let O : Subgroup G := Ch03.oPiCore {r : ℕ | r ≠ p} G
  have : B.Characteristic := hB_char
  have : ((B.subgroupOf A) : Subgroup A).Normal :=
    (inferInstance : B.Normal).subgroupOf A
  refine ⟨?_, ?_, ?_⟩
  · exact OddOrder.GroupTheory.characteristic_map_subtype_of_characteristic
      (Ch03.oPiCore.characteristic {r : ℕ | r ≠ p} G) hA_char
  · exact OddOrder.GroupTheory.characteristic_map_subtype_of_characteristic
      (Ch03.oPiCore.characteristic {r : ℕ | r ≠ p} G) hB_char
  · calc
      Nat.card
          ((A.map (Ch03.oPiCore {r : ℕ | r ≠ p} G).subtype) ⧸
            ((B.map (Ch03.oPiCore {r : ℕ | r ≠ p} G).subtype).subgroupOf
              (A.map (Ch03.oPiCore {r : ℕ | r ≠ p} G).subtype))) =
          Nat.card (A ⧸ B.subgroupOf A) := by
        simpa [O] using Subgroup.nat_card_quotient_subgroupOf_map_subtype_eq
          (H := O) hBA
      _ = Nat.card ↥((default : Sylow q ↥(Ch03.oPiCore {r : ℕ | r ≠ p} G)) :
          Subgroup ↥(Ch03.oPiCore {r : ℕ | r ≠ p} G)) := hcard
      _ = Nat.card ↥((default : Sylow q G) : Subgroup G) :=
        card_sylow_oPiCore_eq_card_sylow_of_hasNormalPComplement_ne hpq hG
          (default : Sylow q ↥(Ch03.oPiCore {r : ℕ | r ≠ p} G))
          (default : Sylow q G)

/-- One factor of the characteristic Sylow series in BG Theorem 4.20(c).

The data records two characteristic subgroups `lower <= upper` whose quotient has
exactly the cardinality of a Sylow `q`-subgroup of the ambient group.  Keeping the
factor as data lets the 4.20(c) induction lift whole layers from the normal
`p`-complement before assembling the full series. -/
structure CharacteristicSylowLayer (G : Type*) [Group G] [Finite G]
    (q : ℕ) [Fact q.Prime] where
  upper : Subgroup G
  lower : Subgroup G
  lower_le_upper : lower ≤ upper
  upper_char : upper.Characteristic
  lower_char : lower.Characteristic
  card_quotient_eq_sylow :
    Nat.card (upper ⧸ lower.subgroupOf upper) =
      Nat.card ↥((default : Sylow q G) : Subgroup G)

namespace CharacteristicSylowLayer

/-- A bottom layer in the BG Theorem 4.20(c) characteristic Sylow series supplies
a normal Sylow subgroup. -/
theorem exists_normal_sylow_of_lower_eq_bot {q : ℕ} [Fact q.Prime]
    (L : CharacteristicSylowLayer G q) (hlower : L.lower = ⊥) :
    ∃ Q : Sylow q G, (Q : Subgroup G).Normal := by
  classical
  refine exists_normal_sylow_of_characteristic_quotient_bot_card_eq_sylow
    L.upper_char ?_
  simpa [hlower] using L.card_quotient_eq_sylow

/-- The top layer `G/O_{p-prime}` associated to a normal `p`-complement.

This is the layer attached at the front of the BG Theorem 4.20(c) induction
series after Theorem 4.18(b) replaces the chosen complement by the canonical
`O_{p-prime}`. -/
noncomputable def top_of_hasNormalPComplement
    {p : ℕ} [Fact p.Prime] (hG : Ch05.HasNormalPComplement p G) :
    CharacteristicSylowLayer G p := by
  classical
  let O : Subgroup G := Ch03.oPiCore {r : ℕ | r ≠ p} G
  haveI : O.Normal := by dsimp [O]; infer_instance
  haveI : (O.subgroupOf (⊤ : Subgroup G)).Normal :=
    (inferInstance : O.Normal).subgroupOf (⊤ : Subgroup G)
  have hquot_top :
      Nat.card ((⊤ : Subgroup G) ⧸ O.subgroupOf (⊤ : Subgroup G)) =
        Nat.card (G ⧸ O) := by
    let e : (⊤ : Subgroup G) ≃* G := Subgroup.topEquiv
    have hmap : (O.subgroupOf (⊤ : Subgroup G)).map e.toMonoidHom = O := by
      ext x
      constructor
      · rintro ⟨y, hyO, rfl⟩
        exact hyO
      · intro hx
        exact ⟨⟨x, trivial⟩, hx, rfl⟩
    exact Nat.card_congr
      (QuotientGroup.congr (O.subgroupOf (⊤ : Subgroup G)) O e hmap).toEquiv
  exact
    { upper := ⊤
      lower := O
      lower_le_upper := le_top
      upper_char := Subgroup.topCharacteristic
      lower_char := by
        dsimp [O]
        exact Ch03.oPiCore.characteristic {r : ℕ | r ≠ p} G
      card_quotient_eq_sylow := by
        calc
          Nat.card ((⊤ : Subgroup G) ⧸ O.subgroupOf (⊤ : Subgroup G)) =
              Nat.card (G ⧸ O) := hquot_top
          _ = Nat.card ↥((default : Sylow p G) : Subgroup G) := by
            simpa [O] using
              card_quotient_oPiCore_eq_card_sylow_of_hasNormalPComplement
                (G := G) hG (default : Sylow p G) }

@[simp] theorem top_of_hasNormalPComplement_upper
    {p : ℕ} [Fact p.Prime] (hG : Ch05.HasNormalPComplement p G) :
    (top_of_hasNormalPComplement (G := G) hG).upper = ⊤ := rfl

@[simp] theorem top_of_hasNormalPComplement_lower
    {p : ℕ} [Fact p.Prime] (hG : Ch05.HasNormalPComplement p G) :
    (top_of_hasNormalPComplement (G := G) hG).lower =
      Ch03.oPiCore {r : ℕ | r ≠ p} G := rfl

/-- Lift a characteristic Sylow layer from the canonical normal `p`-complement to
the ambient group, for `q != p`. -/
noncomputable def lift_oPiCore_of_hasNormalPComplement_ne
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (hpq : q ≠ p)
    (hG : Ch05.HasNormalPComplement p G)
    (L : CharacteristicSylowLayer
      ↥(Ch03.oPiCore {r : ℕ | r ≠ p} G) q) :
    CharacteristicSylowLayer G q :=
  let hlift := characteristic_quotient_layer_lift_of_hasNormalPComplement_ne
    (G := G) hpq hG L.lower_le_upper L.upper_char L.lower_char
    L.card_quotient_eq_sylow
  { upper := L.upper.map (Ch03.oPiCore {r : ℕ | r ≠ p} G).subtype
    lower := L.lower.map (Ch03.oPiCore {r : ℕ | r ≠ p} G).subtype
    lower_le_upper := Subgroup.map_mono L.lower_le_upper
    upper_char := hlift.1
    lower_char := hlift.2.1
    card_quotient_eq_sylow := hlift.2.2 }

end CharacteristicSylowLayer

/-- One labelled factor in the BG Theorem 4.20(c) characteristic Sylow series. -/
structure CharacteristicSylowStep (G : Type*) [Group G] [Finite G] where
  q : ℕ
  q_prime : Fact q.Prime
  layer : @CharacteristicSylowLayer G _ _ q q_prime

namespace CharacteristicSylowStep

/-- Upper endpoint of a labelled characteristic Sylow step. -/
def upper (S : CharacteristicSylowStep G) : Subgroup G :=
  @CharacteristicSylowLayer.upper G _ _ S.q S.q_prime S.layer

/-- Lower endpoint of a labelled characteristic Sylow step. -/
def lower (S : CharacteristicSylowStep G) : Subgroup G :=
  @CharacteristicSylowLayer.lower G _ _ S.q S.q_prime S.layer

/-- Regard an unlabelled characteristic Sylow layer as a labelled step. -/
def ofLayer {q : ℕ} [Fact q.Prime] (L : CharacteristicSylowLayer G q) :
    CharacteristicSylowStep G :=
  { q := q
    q_prime := inferInstance
    layer := L }

@[simp] theorem upper_ofLayer {q : ℕ} [Fact q.Prime]
    (L : CharacteristicSylowLayer G q) :
    (ofLayer L).upper = L.upper := rfl

@[simp] theorem lower_ofLayer {q : ℕ} [Fact q.Prime]
    (L : CharacteristicSylowLayer G q) :
    (ofLayer L).lower = L.lower := rfl

/-- A labelled step whose lower endpoint is bottom supplies a normal Sylow
subgroup for its label. -/
theorem exists_normal_sylow_of_lower_eq_bot (S : CharacteristicSylowStep G)
    (hlower : S.lower = ⊥) : ∃ Q : Sylow S.q G, (Q : Subgroup G).Normal := by
  have : Fact S.q.Prime := S.q_prime
  exact CharacteristicSylowLayer.exists_normal_sylow_of_lower_eq_bot S.layer
    (by simpa [lower] using hlower)

end CharacteristicSylowStep

/-- A finite characteristic Sylow series in the form used by BG Theorem 4.20(c).

The terms are indexed as `G_0, ..., G_n`, with each step carrying the existing
`CharacteristicSylowLayer` payload for the quotient `G_i/G_{i+1}`.  The labels
are part of the step data; later theorem statements can impose that they enumerate
`Nat.card G` prime factors in increasing order. -/
structure CharacteristicSylowSeries (G : Type*) [Group G] [Finite G] where
  length : ℕ
  term : Fin (length + 1) → Subgroup G
  top_eq : term 0 = ⊤
  bot_eq : term (Fin.last length) = ⊥
  step : Fin length → CharacteristicSylowStep G
  upper_eq : ∀ i : Fin length, (step i).upper = term (Fin.castSucc i)
  lower_eq : ∀ i : Fin length, (step i).lower = term i.succ

/-- The downstream-facing package supplied by BG Theorem 4.20(c).

The raw `CharacteristicSylowSeries` records the characteristic factor data.  Consumers such
as §9 also need the series to have a terminal step and need that terminal label to be an
actual prime divisor of the ambient group.  Keeping those as explicit fields avoids baking
strictness assumptions into the raw series representation. -/
structure CharacteristicSylowSeriesPackage (G : Type*) [Group G] [Finite G] where
  series : CharacteristicSylowSeries G
  length_pos : 0 < series.length
  terminal_mem :
    ∀ i : Fin series.length,
      i.succ = Fin.last series.length → (series.step i).q ∈ (Nat.card G).primeFactors

/-- A finite characteristic Sylow segment with arbitrary endpoints.

This is the ambient image of the induction series inside the canonical normal
`p`-complement before the top `G/O_{p-prime}` layer is attached. -/
structure CharacteristicSylowSegment (G : Type*) [Group G] [Finite G] where
  length : ℕ
  term : Fin (length + 1) → Subgroup G
  step : Fin length → CharacteristicSylowStep G
  upper_eq : ∀ i : Fin length, (step i).upper = term (Fin.castSucc i)
  lower_eq : ∀ i : Fin length, (step i).lower = term i.succ

namespace CharacteristicSylowStep

/-- Lift a labelled step from the canonical normal `p`-complement to the ambient
group. -/
noncomputable def lift_oPiCore_of_hasNormalPComplement_ne
    {p : ℕ} [Fact p.Prime] (hG : Ch05.HasNormalPComplement p G)
    (S : CharacteristicSylowStep ↥(Ch03.oPiCore {r : ℕ | r ≠ p} G))
    (hpq : S.q ≠ p) : CharacteristicSylowStep G :=
  { q := S.q
    q_prime := S.q_prime
    layer := @CharacteristicSylowLayer.lift_oPiCore_of_hasNormalPComplement_ne
      G _ _ p S.q _ S.q_prime hpq hG S.layer }

@[simp] theorem upper_lift_oPiCore_of_hasNormalPComplement_ne
    {p : ℕ} [Fact p.Prime] (hG : Ch05.HasNormalPComplement p G)
    (S : CharacteristicSylowStep ↥(Ch03.oPiCore {r : ℕ | r ≠ p} G))
    (hpq : S.q ≠ p) :
    (S.lift_oPiCore_of_hasNormalPComplement_ne (G := G) hG hpq).upper =
      S.upper.map (Ch03.oPiCore {r : ℕ | r ≠ p} G).subtype := by
  have : Fact S.q.Prime := S.q_prime
  unfold lift_oPiCore_of_hasNormalPComplement_ne upper
  unfold CharacteristicSylowLayer.lift_oPiCore_of_hasNormalPComplement_ne
  rcases characteristic_quotient_layer_lift_of_hasNormalPComplement_ne
      (G := G) hpq hG S.layer.lower_le_upper S.layer.upper_char
      S.layer.lower_char S.layer.card_quotient_eq_sylow with
    ⟨hupper, hlower, hcard⟩
  rfl

@[simp] theorem lower_lift_oPiCore_of_hasNormalPComplement_ne
    {p : ℕ} [Fact p.Prime] (hG : Ch05.HasNormalPComplement p G)
    (S : CharacteristicSylowStep ↥(Ch03.oPiCore {r : ℕ | r ≠ p} G))
    (hpq : S.q ≠ p) :
    (S.lift_oPiCore_of_hasNormalPComplement_ne (G := G) hG hpq).lower =
      S.lower.map (Ch03.oPiCore {r : ℕ | r ≠ p} G).subtype := by
  have : Fact S.q.Prime := S.q_prime
  unfold lift_oPiCore_of_hasNormalPComplement_ne lower
  unfold CharacteristicSylowLayer.lift_oPiCore_of_hasNormalPComplement_ne
  rcases characteristic_quotient_layer_lift_of_hasNormalPComplement_ne
      (G := G) hpq hG S.layer.lower_le_upper S.layer.upper_char
      S.layer.lower_char S.layer.card_quotient_eq_sylow with
    ⟨hupper, hlower, hcard⟩
  rfl

end CharacteristicSylowStep

namespace CharacteristicSylowSegment

/-- Attach a top characteristic Sylow layer to a segment whose top endpoint is
that layer's lower endpoint, producing a full characteristic Sylow series. -/
def consTop (seg : CharacteristicSylowSegment G) {q : ℕ} [Fact q.Prime]
    (topLayer : CharacteristicSylowLayer G q) (hupper : topLayer.upper = ⊤)
    (hlink : topLayer.lower = seg.term 0)
    (hbot : seg.term (Fin.last seg.length) = ⊥) : CharacteristicSylowSeries G :=
  { length := seg.length + 1
    term := Fin.cons (⊤ : Subgroup G) seg.term
    top_eq := by
      simp [Fin.cons_zero]
    bot_eq := by
      simpa [Fin.cons_last] using hbot
    step := Fin.cons (CharacteristicSylowStep.ofLayer topLayer) seg.step
    upper_eq := by
      intro i
      cases i using Fin.cases
      · simp [CharacteristicSylowStep.upper_ofLayer, hupper]
      · rename_i i
        have hidx : Fin.castSucc i.succ = (Fin.castSucc i).succ := by
          ext
          rfl
        rw [hidx, Fin.cons_succ]
        exact seg.upper_eq i
    lower_eq := by
      intro i
      cases i using Fin.cases
      · simp [CharacteristicSylowStep.lower_ofLayer, hlink]
      · rename_i i
        simpa [Fin.cons_succ] using seg.lower_eq i }

end CharacteristicSylowSegment

namespace CharacteristicSylowSeries

/-- Any step of a characteristic Sylow series whose lower endpoint is bottom
supplies a normal Sylow subgroup for that step's label. -/
theorem exists_normal_sylow_of_step_lower_eq_bot
    (S : CharacteristicSylowSeries G) (i : Fin S.length)
    (hlower : (S.step i).lower = ⊥) :
    ∃ Q : Sylow (S.step i).q G, (Q : Subgroup G).Normal :=
  CharacteristicSylowStep.exists_normal_sylow_of_lower_eq_bot (S.step i) hlower

/-- A step whose lower series term is bottom supplies a normal Sylow subgroup. -/
theorem exists_normal_sylow_of_step_term_eq_bot
    (S : CharacteristicSylowSeries G) (i : Fin S.length)
    (hterm : S.term i.succ = ⊥) :
    ∃ Q : Sylow (S.step i).q G, (Q : Subgroup G).Normal :=
  exists_normal_sylow_of_step_lower_eq_bot S i ((S.lower_eq i).trans hterm)

/-- The terminal step of a characteristic Sylow series supplies a normal Sylow
subgroup for its label. -/
theorem exists_normal_sylow_of_terminal_step
    (S : CharacteristicSylowSeries G) (i : Fin S.length)
    (hi : i.succ = Fin.last S.length) :
    ∃ Q : Sylow (S.step i).q G, (Q : Subgroup G).Normal :=
  exists_normal_sylow_of_step_term_eq_bot S i (by rw [hi, S.bot_eq])

/-- A positive-length characteristic Sylow series has a terminal step. -/
theorem exists_terminal_step_of_length_pos (S : CharacteristicSylowSeries G)
    (hpos : 0 < S.length) :
    ∃ i : Fin S.length, i.succ = Fin.last S.length := by
  obtain ⟨n, hlen⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hpos)
  refine ⟨Fin.cast hlen.symm (Fin.last n), ?_⟩
  apply Fin.ext
  simp [Fin.val_succ, Fin.val_last, hlen]

/-- A positive-length characteristic Sylow series supplies a normal Sylow subgroup
from its terminal step. -/
theorem exists_normal_sylow_of_length_pos (S : CharacteristicSylowSeries G)
    (hpos : 0 < S.length) :
    ∃ i : Fin S.length,
      i.succ = Fin.last S.length ∧
        ∃ Q : Sylow (S.step i).q G, (Q : Subgroup G).Normal := by
  obtain ⟨i, hi⟩ := exists_terminal_step_of_length_pos S hpos
  exact ⟨i, hi, exists_normal_sylow_of_terminal_step S i hi⟩

/-- Lift the induction series inside the canonical normal `p`-complement to an
ambient segment in `G`.  Its top endpoint is `O_{p-prime}(G)`, not `G`; the top
layer is attached separately by `CharacteristicSylowLayer.top_of_hasNormalPComplement`. -/
noncomputable def lift_oPiCore_segment_of_hasNormalPComplement_ne
    {p : ℕ} [Fact p.Prime] (hG : Ch05.HasNormalPComplement p G)
    (S : CharacteristicSylowSeries ↥(Ch03.oPiCore {r : ℕ | r ≠ p} G))
    (hpq : ∀ i : Fin S.length, (S.step i).q ≠ p) :
    CharacteristicSylowSegment G :=
  { length := S.length
    term := fun i => (S.term i).map (Ch03.oPiCore {r : ℕ | r ≠ p} G).subtype
    step := fun i => (S.step i).lift_oPiCore_of_hasNormalPComplement_ne (G := G) hG (hpq i)
    upper_eq := by
      intro i
      calc
        ((S.step i).lift_oPiCore_of_hasNormalPComplement_ne (G := G) hG (hpq i)).upper =
            (S.step i).upper.map (Ch03.oPiCore {r : ℕ | r ≠ p} G).subtype := by
          rw [CharacteristicSylowStep.upper_lift_oPiCore_of_hasNormalPComplement_ne]
        _ = (S.term (Fin.castSucc i)).map
              (Ch03.oPiCore {r : ℕ | r ≠ p} G).subtype := by
          rw [S.upper_eq i]
    lower_eq := by
      intro i
      calc
        ((S.step i).lift_oPiCore_of_hasNormalPComplement_ne (G := G) hG (hpq i)).lower =
            (S.step i).lower.map (Ch03.oPiCore {r : ℕ | r ≠ p} G).subtype := by
          rw [CharacteristicSylowStep.lower_lift_oPiCore_of_hasNormalPComplement_ne]
        _ = (S.term i.succ).map (Ch03.oPiCore {r : ℕ | r ≠ p} G).subtype := by
          rw [S.lower_eq i] }

/-- The lifted complement segment starts at the canonical normal `p`-complement. -/
theorem lift_oPiCore_segment_top_eq
    {p : ℕ} [Fact p.Prime] (hG : Ch05.HasNormalPComplement p G)
    (S : CharacteristicSylowSeries ↥(Ch03.oPiCore {r : ℕ | r ≠ p} G))
    (hpq : ∀ i : Fin S.length, (S.step i).q ≠ p) :
    (lift_oPiCore_segment_of_hasNormalPComplement_ne (G := G) hG S hpq).term 0 =
      Ch03.oPiCore {r : ℕ | r ≠ p} G := by
  classical
  let O : Subgroup G := Ch03.oPiCore {r : ℕ | r ≠ p} G
  change (S.term 0).map O.subtype = O
  rw [S.top_eq]
  ext x
  constructor
  · rintro ⟨y, _hy, rfl⟩
    exact y.2
  · intro hx
    exact ⟨⟨x, hx⟩, trivial, rfl⟩

/-- The lifted complement segment still ends at the ambient bottom subgroup. -/
theorem lift_oPiCore_segment_bot_eq
    {p : ℕ} [Fact p.Prime] (hG : Ch05.HasNormalPComplement p G)
    (S : CharacteristicSylowSeries ↥(Ch03.oPiCore {r : ℕ | r ≠ p} G))
    (hpq : ∀ i : Fin S.length, (S.step i).q ≠ p) :
    (lift_oPiCore_segment_of_hasNormalPComplement_ne (G := G) hG S hpq).term
        (Fin.last S.length) = ⊥ := by
  classical
  let O : Subgroup G := Ch03.oPiCore {r : ℕ | r ≠ p} G
  change (S.term (Fin.last S.length)).map O.subtype = ⊥
  rw [S.bot_eq]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [Subgroup.mem_bot] using congrArg O.subtype hy
  · intro hx
    rw [Subgroup.mem_bot] at hx
    subst x
    exact ⟨1, by simp, rfl⟩

/-- Lift the induction series inside the canonical normal `p`-complement and
attach the top `G/O_{p-prime}` layer, producing the ambient characteristic Sylow
series used in BG Theorem 4.20(c). -/
noncomputable def lift_oPiCore_series_of_hasNormalPComplement_ne
    {p : ℕ} [Fact p.Prime] (hG : Ch05.HasNormalPComplement p G)
    (S : CharacteristicSylowSeries ↥(Ch03.oPiCore {r : ℕ | r ≠ p} G))
    (hpq : ∀ i : Fin S.length, (S.step i).q ≠ p) :
    CharacteristicSylowSeries G :=
  (lift_oPiCore_segment_of_hasNormalPComplement_ne (G := G) hG S hpq).consTop
    (CharacteristicSylowLayer.top_of_hasNormalPComplement (G := G) hG)
    (by simp)
    (by
      rw [CharacteristicSylowLayer.top_of_hasNormalPComplement_lower]
      exact (lift_oPiCore_segment_top_eq (G := G) hG S hpq).symm)
    (lift_oPiCore_segment_bot_eq (G := G) hG S hpq)

@[simp] theorem lift_oPiCore_series_length_of_hasNormalPComplement_ne
    {p : ℕ} [Fact p.Prime] (hG : Ch05.HasNormalPComplement p G)
    (S : CharacteristicSylowSeries ↥(Ch03.oPiCore {r : ℕ | r ≠ p} G))
    (hpq : ∀ i : Fin S.length, (S.step i).q ≠ p) :
    (lift_oPiCore_series_of_hasNormalPComplement_ne (G := G) hG S hpq).length =
      S.length + 1 := rfl

end CharacteristicSylowSeries

namespace CharacteristicSylowSeriesPackage

/-- A packaged BG Theorem 4.20(c) characteristic Sylow series supplies the terminal
normal Sylow subgroup together with the fact that its label lies in `π(G)`. -/
theorem exists_terminal_normal_sylow (P : CharacteristicSylowSeriesPackage G) :
    ∃ i : Fin P.series.length,
      i.succ = Fin.last P.series.length ∧
        (P.series.step i).q ∈ (Nat.card G).primeFactors ∧
          ∃ Q : Sylow (P.series.step i).q G, (Q : Subgroup G).Normal := by
  obtain ⟨i, hi, hQ⟩ :=
    CharacteristicSylowSeries.exists_normal_sylow_of_length_pos P.series P.length_pos
  exact ⟨i, hi, P.terminal_mem i hi, hQ⟩

end CharacteristicSylowSeriesPackage

/-- For a finite group `B` whose elements pairwise commute (i.e. abelian), the quotient by its
`p'`-core `O_{p'}(B) = oPiCore {r ≠ p} B` is a `p`-group.

In an abelian — more generally nilpotent — group `B ≅ Sylow_p(B) × O_{p'}(B)`, so `B/O_{p'}(B)`
is the Sylow `p`-subgroup.  This is the BG Theorem 4.20(c) step "`G/F` is abelian, hence
`(G/F)/O_{p₁'}(G/F)` is a `p₁`-group". -/
theorem isPGroup_quotient_oPiCore_of_comm {B : Type*} [Group B] [Finite B] {p : ℕ}
    [Fact p.Prime] (hcomm : ∀ x y : B, x * y = y * x) :
    IsPGroup p (B ⧸ Ch03.oPiCore {r : ℕ | r ≠ p} B) := by
  classical
  set O : Subgroup B := Ch03.oPiCore {r : ℕ | r ≠ p} B with hOdef
  set C := B ⧸ O with hCdef
  -- the quotient is abelian and has trivial `p'`-core
  have hcommC : ∀ x y : C, x * y = y * x := by
    intro x y
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective O x
    obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective O y
    rw [← map_mul, ← map_mul, hcomm a b]
  have hcoreC : Ch03.oPiCore {r : ℕ | r ≠ p} C = ⊥ :=
    Ch03.oPiCore_quotient_self_eq_bot _
  -- every prime dividing `|C|` equals `p`
  have huniq : ∀ q : ℕ, q.Prime → q ∣ Nat.card C → q = p := by
    intro q hq hqdvd
    by_contra hqp
    have : Fact q.Prime := ⟨hq⟩
    obtain ⟨x, hx⟩ := Ch01.cauchy (G := C) hqdvd
    -- `⟨x⟩` is a normal `{r ≠ p}`-subgroup, hence trivial — contradicting `|⟨x⟩| = q > 1`.
    have hnorm : (Subgroup.zpowers x).Normal :=
      { conj_mem := fun n hn g => by
          have hgn : g * n * g⁻¹ = n := by
            rw [hcommC g n, mul_assoc, mul_inv_cancel, mul_one]
          rw [hgn]; exact hn }
    have hcard : Nat.card (Subgroup.zpowers x) = q := by
      rw [Nat.card_zpowers, hx]
    have hpi : Ch03.Subgroup.IsPiGroup {r : ℕ | r ≠ p} (Subgroup.zpowers x) := by
      intro q' hq'
      rw [hcard, hq.primeFactors, Finset.mem_singleton] at hq'
      change q' ≠ p
      rw [hq']; exact hqp
    have hbot : Subgroup.zpowers x = ⊥ :=
      Ch03.eq_bot_of_isPiGroup_of_oPiCore_eq_bot {r : ℕ | r ≠ p} hpi hcoreC
    have hx1 : x = 1 := Subgroup.zpowers_eq_bot.mp hbot
    rw [hx1, orderOf_one] at hx
    exact hq.ne_one hx.symm
  -- a number all of whose prime divisors equal `p` is a power of `p`
  have hcard_eq : Nat.card C = p ^ (Nat.card C).primeFactorsList.length :=
    Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne'
      (fun {d} hd hdvd => huniq d hd hdvd)
  exact IsPGroup.iff_card.mpr ⟨_, hcard_eq⟩

/-- If `X` has a nilpotent normal subgroup `M` whose index is coprime to `p` (so `M` contains a
full Sylow `p`-subgroup of `X`), then some Sylow `p`-subgroup of `X` lies in the Fitting subgroup
`F(X)`.

BG Theorem 4.20(c) applies this with `X = H`, `M = F(G)` viewed inside `H`: since `H/F` is a
`p₁'`-group, `p₁ ∤ [H:F]`, and `F ≤ F(H)` is nilpotent and normal. -/
theorem exists_sylow_le_fitting_of_nilpotent_normal_index_coprime
    {X : Type*} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]
    {M : Subgroup X} [M.Normal] [Group.IsNilpotent ↥M] (hidx : ¬ p ∣ M.index) :
    ∃ P : Sylow p X, (P : Subgroup X) ≤ Ch01.fitting X := by
  classical
  have hM_le : M ≤ Ch01.fitting X := Ch01.nilpotent_normal_le_fitting
  -- `p`-part of `|X|` equals `p`-part of `|M|`, since `p ∤ [X:M]`.
  have hfactX : (Nat.card X).factorization p = (Nat.card ↥M).factorization p := by
    have hmul : Nat.card ↥M * M.index = Nat.card X := Subgroup.card_mul_index M
    rw [← hmul, Nat.factorization_mul Nat.card_pos.ne' Subgroup.index_ne_zero_of_finite,
      Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hidx, add_zero]
  -- a Sylow `p` of `M`, pushed into `X`, has full `p`-order, hence is Sylow in `X`.
  obtain ⟨R⟩ := (inferInstance : Nonempty (Sylow p ↥M))
  set Rmap : Subgroup X := (R : Subgroup ↥M).map M.subtype with hRmap
  have hRmap_pg : IsPGroup p ↥Rmap := R.isPGroup'.map M.subtype
  have hRmap_le : Rmap ≤ Ch01.fitting X := (Subgroup.map_subtype_le _).trans hM_le
  have hRmap_card : Nat.card ↥Rmap = p ^ (Nat.card X).factorization p := by
    rw [hRmap, Subgroup.card_map_of_injective M.subtype_injective, R.card_eq_multiplicity,
      ← hfactX]
  obtain ⟨P, hP_le⟩ := IsPGroup.exists_le_sylow hRmap_pg
  have hRmap_eq : Rmap = (P : Subgroup X) :=
    Subgroup.eq_of_le_of_card_ge hP_le
      (le_of_eq (P.card_eq_multiplicity.trans hRmap_card.symm))
  exact ⟨P, hRmap_eq ▸ hRmap_le⟩

end Thm418

end OddOrder.BG.Ch1.S04


