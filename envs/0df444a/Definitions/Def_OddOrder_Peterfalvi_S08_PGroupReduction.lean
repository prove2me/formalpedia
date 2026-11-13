-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S08_PGroupReduction
-- name    : OddOrder_Peterfalvi_S08_PGroupReduction
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T07:26:08.940926+00:00
-- url     : https://prove2.me/theorems/cdd5bde8-2b63-4eb4-853f-cd6defa78206
-- title:
--   Peterfalvi (6.5): reduction to a non-abelian $p$-group, application of (6.8)
-- statement:
--   Peterfalvi, *Character Theory for the Odd Order Theorem*, §6, (6.5). The group-theoretic core of (6.5)(b), that a finite nilpotent group with a fixed-point-free action on its abelianization and the $\le4|\cdot|^2+1$ index bound is a $p$-group, is already formalized abstractly; this file applies the (6.8) coherence theorem to reach it.
--
--   The bundle includes `caseAB_split_of_c2` (the (6.8) case A/B split).
--
--   The bundle also proves 15 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S08_PGroupReduction.lean

/-
Copyright (c) 2026 The Odd Order Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S08_PGroupReduction.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S08_CaseBSeedGlue
import Definitions.Def_OddOrder_Peterfalvi_S08_CoherenceCore
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_Main_CommutatorBasics
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_Main_ThreeSubgroupsCoprime
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_Main_BaerTrick
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_Main_ChainNilpotent
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_ForwardFromCh03
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_Main_ThreeSubgroups
import Definitions.Def_OddOrder_Peterfalvi_S08_Theorem62_63_Standalone

namespace OddOrder.Peterfalvi.S08

open OddOrder.RepresentationTheory

variable {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]

variable {L : Subgroup G} [Fintype ↥L] [Invertible (Nat.card ↥L : ℂ)]

variable {H : Subgroup ↥L} [Invertible (Nat.card ↥H : ℂ)]

/-- Any natural dividing `|L|` is odd (since `|L|` is odd, Peterfalvi (6.4.a)). -/
theorem odd_of_dvd_card_L (hyp : SibleyDadeHypothesis G L H) {a : ℕ} (ha : a ∣ Nat.card ↥L) :
    Odd a := by
  rcases Nat.even_or_odd a with he | ho
  · obtain ⟨c, hc⟩ := ha
    exact absurd (hc ▸ he.mul_right c) (Nat.not_even_iff_odd.mpr hyp.card_L_odd)
  · exact ho

/-- `|W₁|` is odd. -/
theorem card_W1_odd (hyp : SibleyDadeHypothesis G L H) : Odd (Nat.card ↥hyp.W1) :=
  odd_of_dvd_card_L hyp (Subgroup.card_subgroup_dvd_card hyp.W1)

/-- `|Abelianization H| = |H : ⁅H,H⁆|` is odd (it divides `|H|`, which divides the odd `|L|`). -/
theorem card_abelianization_H_odd (hyp : SibleyDadeHypothesis G L H) :
    Odd (Nat.card (Abelianization ↥H)) :=
  odd_of_dvd_card_L hyp
    ((Subgroup.card_quotient_dvd_card (commutator ↥H)).trans (Subgroup.card_subgroup_dvd_card H))

/-- **Peterfalvi (6.5)(b) reduction — (6.8)(c2) certain-type case, in the Sibley context.**

In case (6.8)(c2) the complement `W₁` does *not* act fixed-point-freely on `H`, but the
`W₁`-conjugation fixed points lie in `⁅H,H⁆` (the certain-type centralizer condition `hfix`, phrased
via the explicit `L`-conjugation `w x w⁻¹ = x`).  Together with the Hall coprimality `hcop` and the
(6.2)/(6.3) index bound `hbound`, the nilpotent `H` is a `p`-group.

This wires `isPGroup_of_isNilpotent_of_coprime_fixedPoints_le_commutator` into the capstone via the
`W₁`-conjugation action, isolating `hfix` (the (4.6)/(6.4.c) fixed-point condition) and `hbound`
(the
contrapositive of Theorem (6.3)) as the residual obligations of the (6.8)(c2) `p`-group
reduction. -/
theorem exists_isPGroup_H_of_c2_of_card_le (hyp : SibleyDadeHypothesis G L H)
    (hcop : Nat.Coprime (Nat.card ↥H) (Nat.card ↥hyp.W1))
    (hfix : ∀ w : ↥hyp.W1, w ≠ 1 → ∀ x : ↥H,
      (w : ↥L) * (x : ↥L) * (w : ↥L)⁻¹ = (x : ↥L) → x ∈ commutator ↥H)
    (hbound : Nat.card (Abelianization ↥H) ≤ 4 * Nat.card ↥hyp.W1 ^ 2 + 1) :
    ∃ p : ℕ, Nat.Prime p ∧ IsPGroup p ↥H := by
  let : H.Normal := hyp.H_normal
  let : Group.IsNilpotent ↥H := hyp.H_nilpotent
  -- the `W₁`-conjugation action on `H`.
  let actH : MulDistribMulAction ↥hyp.W1 ↥H :=
    MulDistribMulAction.compHom H ((MulAut.conjNormal (H := H)).comp hyp.W1.subtype)
  have hsmulH : ∀ (a : ↥hyp.W1) (x : ↥H),
      ((a • x : ↥H) : ↥L) = (a : ↥L) * (x : ↥L) * (a : ↥L)⁻¹ := by
    intro a x
    have h1 : (a • x : ↥H) = (MulDistribMulAction.toMulAut ↥hyp.W1 ↥H a) x := by
      simp [MulDistribMulAction.toMulAut_apply]
    rw [h1]
    change ((MulAut.conjNormal (H := H) (hyp.W1.subtype a)) x : ↥L) = _
    rw [MulAut.conjNormal_apply]; rfl
  -- convert the explicit-conjugation `hfix` to the smul form the reduction lemma consumes.
  have hfix' : ∀ w : ↥hyp.W1, w ≠ 1 → ∀ x : ↥H, w • x = x → x ∈ commutator ↥H := by
    intro w hw x hwx
    refine hfix w hw x ?_
    have hb := hsmulH w x
    rw [hwx] at hb
    exact hb.symm
  exact isPGroup_of_isNilpotent_of_coprime_fixedPoints_le_commutator hcop.symm hfix'
    (card_abelianization_H_odd hyp) (card_W1_odd hyp) hbound

/-- A `p`-group factor of the odd group `H` (`p` prime, `H ≠ ⊥`) has `p ≥ 3`: `p ∣ |H| ∣ |L|` and
`|L|` is odd, so `p` is an odd prime. -/
theorem three_le_of_isPGroup_H (hyp : SibleyDadeHypothesis G L H)
    {p : ℕ} (hp : p.Prime) (hHp : IsPGroup p ↥H) : 3 ≤ p := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, hn⟩ := hHp.exists_card_eq
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hn
    exact (Finite.one_lt_card_iff_nontrivial.mpr
      ((Subgroup.nontrivial_iff_ne_bot H).mpr hyp.H_ne_bot)).ne' hn
  have hpH : p ∣ Nat.card ↥H := hn ▸ dvd_pow_self p hn0
  have hpL : p ∣ Nat.card ↥L := hpH.trans H.card_subgroup_dvd_card
  have hpodd : Odd p := hyp.card_L_odd.of_dvd_nat hpL
  have h2 : 2 ≤ p := hp.two_le
  rcases Nat.lt_or_ge p 3 with h | h
  · interval_cases p
    · exact absurd hpodd (by decide)
  · exact h

/-- **A finite `p`-group with cyclic abelianization is cyclic** (Burnside-basis, rank-1 case).
If `P ⧸ ⁅P,P⁆` is cyclic, a lift `x` of a generator satisfies `⟨x⟩ ⊔ ⁅P,P⁆ = ⊤`; since
`⁅P,P⁆ ≤ Φ(P)` (`commutator_le_frattini_of_pgroup`), the non-generating property
`frattini_nongenerating` upgrades this to `⟨x⟩ ⊔ Φ(P) = ⊤`, forcing `⟨x⟩ = ⊤`, i.e. `P` cyclic. -/
theorem isCyclic_of_isPGroup_of_isCyclic_quotient_commutator
    {P : Type*} [Group P] [Finite P] {p : ℕ} [Fact p.Prime] (hP : IsPGroup p P)
    (hcyc : IsCyclic (P ⧸ commutator P)) : IsCyclic P := by
  obtain ⟨q, hq⟩ := hcyc.exists_generator
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (commutator P) q
  -- `⟨x⟩ ⊔ ⁅P,P⁆ = ⊤`: every `g` is `x^k` times a commutator, using that `mk x` generates.
  have htop : Subgroup.zpowers x ⊔ commutator P = ⊤ := by
    rw [eq_top_iff]
    intro g _
    obtain ⟨k, hk⟩ := hq (QuotientGroup.mk' (commutator P) g)
    have heq : (QuotientGroup.mk (x ^ k) : P ⧸ commutator P) = QuotientGroup.mk g := by
      have h := (map_zpow (QuotientGroup.mk' (commutator P)) x k).trans hk
      simpa only [QuotientGroup.mk'_apply] using h
    have hmem : (x ^ k)⁻¹ * g ∈ commutator P := QuotientGroup.eq.mp heq
    have hg : g = x ^ k * ((x ^ k)⁻¹ * g) := by group
    rw [hg]
    exact mul_mem (Subgroup.mem_sup_left (Subgroup.mem_zpowers_iff.mpr ⟨k, rfl⟩))
      (Subgroup.mem_sup_right hmem)
  -- upgrade `⁅P,P⁆` to `Φ(P)` and use non-generation.
  have hfr : Subgroup.zpowers x ⊔ frattini P = ⊤ :=
    top_le_iff.mp (htop ▸ sup_le_sup_left
      (OddOrder.Isaacs.Ch04.commutator_le_frattini_of_pgroup hP) (Subgroup.zpowers x))
  have hxtop : Subgroup.zpowers x = ⊤ := frattini_nongenerating hfr
  have hgen : ∀ y : P, y ∈ Subgroup.zpowers x := fun y => by rw [hxtop]; exact Subgroup.mem_top y
  exact ⟨⟨x, hgen⟩⟩

/-- **A non-abelian finite `p`-group has `p² ≤ |P : P′|`** — the Burnside-basis input to
Peterfalvi (6.5)(c).  If `P` is a `p`-group that is not commutative, then `p² ≤ |Abelianization P|`.

`|Abelianization P|` is a power `pⁿ`; if it were `< p²` then `pⁿ ∣ p`, so the abelianization is
cyclic (`isCyclic_of_card_dvd_prime`), whence `P` is cyclic
(`isCyclic_of_isPGroup_of_isCyclic_quotient_commutator`) and therefore abelian — contradicting
non-commutativity. -/
theorem sq_le_card_abelianization_of_isPGroup_of_noncomm
    {P : Type*} [Group P] [Finite P] {p : ℕ} (hp : p.Prime) (hP : IsPGroup p P)
    (hnc : ¬ ∀ a b : P, a * b = b * a) :
    p ^ 2 ≤ Nat.card (Abelianization P) := by
  have : Fact p.Prime := ⟨hp⟩
  by_contra hlt
  rw [not_le] at hlt
  have hpg : IsPGroup p (Abelianization P) := hP.to_quotient (commutator P)
  obtain ⟨n, hn⟩ := hpg.exists_card_eq
  have hn2 : n < 2 := by
    by_contra h; rw [not_lt] at h
    exact absurd (hn.symm ▸ Nat.pow_le_pow_right hp.pos h) (not_le.mpr hlt)
  have : IsCyclic (Abelianization P) :=
    isCyclic_of_card_dvd_prime (p := p)
      (by rw [hn]; exact (pow_dvd_pow p (by omega : n ≤ 1)).trans (dvd_of_eq (pow_one p)))
  have hcyc : IsCyclic P :=
    isCyclic_of_isPGroup_of_isCyclic_quotient_commutator hP this
  obtain ⟨x, hx⟩ := hcyc.exists_generator
  refine hnc fun a b => ?_
  obtain ⟨m, hm⟩ := hx a
  obtain ⟨l, hl⟩ := hx b
  rw [← hm, ← hl, ← zpow_add, ← zpow_add, add_comm]

/-- **Peterfalvi (6.5)(c) coherence producer** (abstract (6.1)/(5.2) form, over the `S07` setup).

The (6.5)(c) conclusion "`S = SOf ⊥` is coherent" for a nilpotent **Frobenius kernel** `H` (kernel
of
`hF : IsFrobeniusGroup ↥L H C`) with the divisibility `|L:H| ∣ p − 1` for every `p ∣ |H|` (`hdvd`),
assembled over the abstract `S07` coherence setup (`τ`, `A0`, filtration `SOf`).  By contradiction:
if `SOf ⊥` is not coherent, then `six_three_of_six_two_oracle` (with `M = ⊥`, `H₁ = ⁅H,H⁆`, `K = H`)
forces `|H:H′| ≤ 4|L:H|² + 1` (else it would produce coherence).  The **(6.5.b) reduction** is done
*here*: from the Frobenius structure + that index bound, `isPGroup_of_isFrobeniusGroup_of_card_le`
produces the prime `p` with `IsPGroup p H`; a non-abelian `p`-group has `p² ≤ |H:H′|`
(`sq_le_card_abelianization_of_isPGroup_of_noncomm`), and `six_five_c_arith` turns `|L:H| ∣ p − 1`
into a contradiction.  (The caller supplies non-abelianness `hnonab`; the abelian case is handled
upstream — `H` abelian ⟹ `⁅H,H⁆ = ⊥` ⟹ `SOf ⁅H,H⁆ = SOf ⊥`, coherent by `hcoh`.)

This is the honest (6.5)(c) assembly engine: the genuine residual obligations are exactly the
parameters — the **(5.6) break-member oracle** `h56` (the remaining character-theoretic core), the
**`S(H′)` coherence** `hcoh` (constant-degree (5.7)), and the filtration `SOf`.  Everything numeric
—
the (6.3) descent, the (6.5.b) `p`-group reduction, the `p²`-index gap, and the (6.5.c) arithmetic —
is proved here.  Oddness side-conditions are discharged from `|L|` odd (`hLodd`). -/
theorem nonempty_coherent_SOf_bot_of_index_dvd [Finite ↥L] [Group.IsNilpotent ↥H]
    (hHnorm : H.Normal)
    (τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥L G) (A0 : Set ↥L)
    (SOf : Subgroup ↥L → Set (ClassFunction ↥L ℂ))
    {C : Subgroup ↥L} (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥L H C)
    (hnonab : ¬ ∀ a b : ↥H, a * b = b * a)
    (hLodd : Odd (Nat.card ↥L))
    (hdvd : ∀ p : ℕ, p.Prime → p ∣ Nat.card ↥H → H.index ∣ p - 1)
    (hH'lt : (⁅H, H⁆ : Subgroup ↥L) < H)
    (hcoh : Nonempty (OddOrder.Peterfalvi.S07.IsCoherent τ (SOf ⁅H, H⁆) A0))
    (h56 : ∀ (A B : Subgroup ↥L) [A.Normal] [B.Normal], B ≤ A → A ≤ ⁅H, H⁆ →
        (A.subgroupOf H).map (QuotientGroup.mk' (B.subgroupOf H)) ≤
          Subgroup.center (↥H ⧸ B.subgroupOf H) →
        Nonempty (OddOrder.Peterfalvi.S07.IsCoherent τ (SOf A) A0) →
        ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent τ (SOf B) A0) →
        ∃ θ : IrreducibleCharacter ↥H,
          (↑(B.subgroupOf H) : Set ↥H) ⊆ OddOrder.Peterfalvi.S03.characterKernel
              (θ : ClassFunction ↥H ℂ) ∧
          (Nat.card (↥H ⧸ A.subgroupOf H) : ℝ) - 1 ≤
              2 * (ClassFunction.induce H (θ : ClassFunction ↥H ℂ) 1).re) :
    Nonempty (OddOrder.Peterfalvi.S07.IsCoherent τ (SOf ⊥) A0) := by
  have := hHnorm
  by_contra hncoh
  -- If `|H:H′| > 4|L:H|² + 1`, the (6.3) oracle produces coherence — contradiction.
  have hle : Nat.card (↥H ⧸ (⁅H, H⁆ : Subgroup ↥L).subgroupOf H) ≤ 4 * H.index ^ 2 + 1 := by
    by_contra hgt
    rw [not_le] at hgt
    exact hncoh (six_three_of_six_two_oracle hHnorm bot_le hH'lt le_rfl τ A0 SOf h56 hcoh hgt)
  -- `|L:H| = |C|` (Frobenius complement); convert to the abelianization/complement bound.
  have hidxC : H.index = Nat.card ↥C := hF.isComplement.symm.index_eq_card
  have hbound : Nat.card (Abelianization ↥H) ≤ 4 * Nat.card ↥C ^ 2 + 1 := by
    have hle' := hle
    rwa [commutator_subgroupOf_self, hidxC] at hle'
  -- Odd orders, all from `|L|` odd.
  have hHabodd : Odd (Nat.card (Abelianization ↥H)) :=
    Odd.of_dvd_nat (Odd.of_dvd_nat hLodd H.card_subgroup_dvd_card)
      (Subgroup.card_quotient_dvd_card (_root_.commutator ↥H))
  have hCodd : Odd (Nat.card ↥C) := Odd.of_dvd_nat hLodd C.card_subgroup_dvd_card
  -- **(6.5)(b) reduction:** the nilpotent Frobenius kernel `H` is a `p`-group.
  obtain ⟨p, hp, hHp⟩ := isPGroup_of_isFrobeniusGroup_of_card_le hF hHabodd hCodd hbound
  have : Fact (Nat.Prime p) := ⟨hp⟩
  -- `p ∣ |H|` (nontrivial `p`-group), hence `p` odd and `|L:H| ∣ p − 1`.
  have : Nontrivial ↥H := by
    rcases subsingleton_or_nontrivial ↥H with h | h
    · exact absurd (fun a b => Subsingleton.elim (a * b) (b * a)) hnonab
    · exact h
  have hpdvd : p ∣ Nat.card ↥H := by
    obtain ⟨n, hn⟩ := hHp.exists_card_eq
    have h1 : 1 < Nat.card ↥H := Finite.one_lt_card_iff_nontrivial.mpr inferInstance
    rw [hn] at h1 ⊢
    exact dvd_pow_self p (by rintro rfl; simp at h1)
  have hodd_p : Odd p :=
    Odd.of_dvd_nat (Odd.of_dvd_nat hLodd H.card_subgroup_dvd_card) hpdvd
  have hodd_LH : Odd H.index := hidxC ▸ hCodd
  have hdvd' : H.index ∣ p - 1 := hdvd p hp hpdvd
  -- Non-abelian `p`-group ⟹ `p² ≤ |H:H′|`.
  have hsq : p ^ 2 ≤ Nat.card (↥H ⧸ (⁅H, H⁆ : Subgroup ↥L).subgroupOf H) := by
    rw [commutator_subgroupOf_self]
    exact sq_le_card_abelianization_of_isPGroup_of_noncomm hp hHp hnonab
  exact six_five_c_arith hp hodd_p hodd_LH hdvd' hsq hle

/-- **`H` is non-abelian** in the `X`-nonempty branch: `X(⁅H,H⁆) ≠ ∅` forces `⁅H,H⁆ ≠ ⊥`, hence
`commutator ↥H ≠ ⊥`.  (If `⁅H,H⁆ = ⊥` then `S(⁅H,H⁆) = S(⊥) = S`, so `X(⁅H,H⁆) = S − S = ∅`.) -/
theorem commutator_ne_bot_of_Xset_commutator_nonempty (hyp : SibleyDadeHypothesis G L H)
    (hXne : (hyp.Xset ⁅H, H⁆).Nonempty) : _root_.commutator ↥H ≠ ⊥ := by
  let : H.Normal := hyp.H_normal
  intro hbot
  rw [← commutator_subgroupOf_self] at hbot
  have hcommbot : (⁅H, H⁆ : Subgroup ↥L) = ⊥ :=
    (Subgroup.subgroupOf_eq_bot.mp hbot).eq_bot_of_le (Subgroup.commutator_le_left H H)
  have hXempty : hyp.Xset ⁅H, H⁆ = ∅ := by
    change hyp.S \ hyp.SsubFiltration ⁅H, H⁆ = ∅
    rw [hcommbot, hyp.SsubFiltration_bot, Set.sdiff_self]
  rw [hXempty] at hXne
  exact Set.not_nonempty_empty hXne

/-- **Peterfalvi (6.8) — Frobenius case (6.8)(c1): `S` is coherent.**  When `L` is a Frobenius group
with kernel `H` and complement `W₁`, and the `X`-set `X(⁅H,H⁆)` is nonempty (so `H` is non-abelian),
the Sibley set `S` is coherent.

This *fully closes* the (6.8)(c1) branch: by contradiction, if `S` is not coherent then the (6.5)
reduction `isPGroup_of_not_coherent` makes `H` a `p`-group; `p ≥ 3` (odd order) and `H` non-abelian
(`X`-nonempty) feed the case-(A) Frobenius coherence `nonempty_coherent_S_caseA_of_frobenius`,
contradicting non-coherence. -/
theorem nonempty_coherent_S_of_frobenius (hyp : SibleyDadeHypothesis G L H)
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    (hXne : (hyp.Xset ⁅H, H⁆).Nonempty) :
    Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.S
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)) := by
  let : H.Normal := hyp.H_normal
  by_contra hncoh
  obtain ⟨p, hp, hHp⟩ := hyp.isPGroup_of_not_coherent hF hncoh
  exact hncoh (hyp.nonempty_coherent_S_caseA_of_frobenius hF
    (commutator_ne_bot_of_Xset_commutator_nonempty hyp hXne) hp
    (three_le_of_isPGroup_H hyp hp hHp) hHp)

/-- **Peterfalvi (6.4.c) for case (6.8)(c2): the `W₁`-conjugation fixed points lie in `⁅H,H⁆`.**

The certain-type Hypothesis (4.2)(b) gives `C_K(w) = W₂` for every `w ∈ W₁^#` (`centralizer_W2`),
and case (c2) has `W₂ ⊆ ⁅H,H⁆`.  Hence any `x ∈ H` fixed by conjugation by a nonidentity
`w ∈ W₁` lies in `C_L(w) ⊓ K = W₂ ⊆ ⁅H,H⁆`, so `x ∈ ⁅H,H⁆.subgroupOf H = commutator ↥H`
(`commutator_subgroupOf_self`).  This is exactly the `hfix` hypothesis consumed by
`exists_isPGroup_H_of_c2_of_card_le`, mirroring the `caseB_W1_dvd_index_commutator` fixed-point
argument — the (6.4.c) Frobenius-action condition is a *consequence* of the certain-type centralizer
datum, not an extra input. -/
theorem fixedPoints_W1_subset_commutator_of_c2 (hyp : SibleyDadeHypothesis G L H)
    (cert : OddOrder.Peterfalvi.S06.CertainTypeHypothesis (sharpImage H) L)
    (hK : cert.K = H) (hW1 : cert.W1 = hyp.W1) (hW2 : cert.W2 ≤ ⁅H, H⁆) :
    ∀ w : ↥hyp.W1, w ≠ 1 → ∀ x : ↥H,
      (w : ↥L) * (x : ↥L) * (w : ↥L)⁻¹ = (x : ↥L) → x ∈ commutator ↥H := by
  intro w hw x hwx
  -- `(x:L)` commutes with `(w:L)` (from the conjugation-fixed hypothesis), so lies in `C_L(w)`.
  have hxcen : (x : ↥L) ∈ Subgroup.centralizer ({(w : ↥L)} : Set ↥L) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hwx).symm
  have hwW1 : (w : ↥L) ∈ cert.W1 := by rw [hW1]; exact w.2
  have hwne : (w : ↥L) ≠ 1 := fun h => hw (OneMemClass.coe_eq_one.mp h)
  -- `(x:L) ∈ C_L(w) ⊓ K = W₂` by the certain-type centralizer datum (4.2.b).
  have hxW2 : (x : ↥L) ∈ cert.W2 := by
    rw [← cert.centralizer_W2 (w : ↥L) hwW1 hwne]
    exact Subgroup.mem_inf.mpr ⟨hxcen, by rw [hK]; exact x.2⟩
  -- `W₂ ⊆ ⁅H,H⁆`, so `x ∈ ⁅H,H⁆.subgroupOf H = commutator ↥H`.
  rw [← commutator_subgroupOf_self]
  exact Subgroup.mem_subgroupOf.mpr (hW2 hxW2)

/-- **Peterfalvi (6.8) — certain-type case (6.8)(c2): `S` is coherent (dispatch skeleton).**

The (6.8)(c2) branch of `sibleySetup_is_coherent`, assembled from the certain-type data `h46` of
`hyp.cases.inr`.  By contradiction-free assembly: the (6.5) reduction
(`exists_isPGroup_H_of_c2_of_card_le`, fed `hfix` from `fixedPoints_W1_subset_commutator_of_c2` and
the (6.3) index bound `hbound`) makes `H` a `p`-group, then the math case split (6.8.A/B) on whether
`W₂ ⊆ Z(H)` routes to the case-A coherence producer (`Z(H) ∩ W₂ = 1`) or the case-B one
(`1 ≠ W₂ ⊆ Z(H)`, `nonempty_coherent_S_caseB_of_structure`, cont.¹³).

This is the [[gated-endpoint-skeleton]] form: the three genuine residual obligations are isolated as
named hypotheses — `hbound` (Theorem (6.3) c2, the main remaining work, via the reducible-break
norm-weighted (5.6) engine), `hcaseA` (the case-A `_of_c2_caseA` → `S` bootstrap), and `hcaseB` (the
case-B structure-data discharge feeding `nonempty_coherent_S_caseB_of_structure`).  The A/B split
itself (`hsplit`, prime-order `W₂.subgroupOf H` ⟹ `⊥` or all in `Z(H)`) is also named, to be
discharged separately.  Wiring this into `S08_CoherenceTheorems:59` (the c2 branch) follows once the
three obligations are filled. -/
theorem nonempty_coherent_S_of_c2_of_branches (hyp : SibleyDadeHypothesis G L H)
    [H.Normal] [Finite ↥H]
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L)
    (hHK : h46.K = H) (hW1 : h46.W1 = hyp.W1) (hW2comm : h46.W2 ≤ ⁅H, H⁆)
    (hcop : Nat.Coprime (Nat.card ↥H) (Nat.card hyp.W1))
    (hbound : Nat.card (Abelianization ↥H) ≤ 4 * Nat.card ↥hyp.W1 ^ 2 + 1)
    (hsplit : h46.W2.subgroupOf H ≤ Subgroup.center ↥H ∨
      Disjoint (h46.W2.subgroupOf H) (Subgroup.center ↥H))
    (hcaseA : ∀ {p : ℕ}, p.Prime → IsPGroup p ↥H →
      Disjoint (h46.W2.subgroupOf H) (Subgroup.center ↥H) →
      Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.S
        (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)))
    (hcaseB : ∀ {p : ℕ}, p.Prime → IsPGroup p ↥H →
      h46.W2.subgroupOf H ≤ Subgroup.center ↥H →
      Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.S
        (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))) :
    Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.S
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)) := by
  have hfix := fixedPoints_W1_subset_commutator_of_c2 hyp h46.toCertainTypeHypothesis hHK hW1
      hW2comm
  obtain ⟨p, hp, hHp⟩ := exists_isPGroup_H_of_c2_of_card_le hyp hcop hfix hbound
  rcases hsplit with hB | hA
  · exact hcaseB hp hHp hB
  · exact hcaseA hp hHp hA

omit [Invertible (Nat.card ↥H : ℂ)] in
/-- **(6.8) case A/B split** (discharges `hsplit` of `nonempty_coherent_S_of_c2_of_branches`).
Since `W₂ ≤ H` is of prime order, `W₂.subgroupOf H` has prime order too, so the subgroup
`(W₂.subgroupOf H) ⊓ Z(H)` is either trivial (case A: `Z(H) ∩ W₂ = 1`) or all of `W₂.subgroupOf H`
(case B: `1 ≠ W₂ ⊆ Z(H)`).  This is Peterfalvi (6.8)'s two-case dichotomy (04.8:152-154). -/
theorem caseAB_split_of_c2 [H.Normal] [Finite ↥H]
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L)
    (hW2H : h46.W2 ≤ H) (hprime : (Nat.card h46.W2).Prime) :
    h46.W2.subgroupOf H ≤ Subgroup.center ↥H ∨
    Disjoint (h46.W2.subgroupOf H) (Subgroup.center ↥H) := by
  by_cases hB : h46.W2.subgroupOf H ≤ Subgroup.center ↥H
  · exact Or.inl hB
  refine Or.inr (disjoint_iff.mpr ?_)
  have hWprime : (Nat.card ↥(h46.W2.subgroupOf H)).Prime := by
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW2H).toEquiv]
  have hdvd : Nat.card ↥(h46.W2.subgroupOf H ⊓ Subgroup.center ↥H) ∣
      Nat.card ↥(h46.W2.subgroupOf H) := Subgroup.card_dvd_of_le inf_le_left
  rcases (Nat.dvd_prime hWprime).mp hdvd with h1 | hfull
  · exact Subgroup.card_eq_one.mp h1
  · exact absurd (inf_eq_left.mp (Subgroup.eq_of_le_of_card_ge inf_le_left hfull.ge)) hB

/-- **(6.8) case-B: `W₂ ≤ Z(L)`** (helper for the case-B structure-data discharge).
In case (B), `W₂ ⊆ Z(H)` (`hcen`) so `W₂` commutes with all of `H`; and `W₂` commutes with `W₁` by
the certain-type centralizer datum (`commute_of_mem_W1_of_mem_W2`).  Since `L = H ⋊ W₁`
(`H ⊔ W₁ = ⊤`), `W₂` commutes with every element of `L` (by closure induction), i.e. `W₂ ≤ Z(L)`. -/
theorem caseB_W2_le_center_L (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L)
    (hW1 : h46.W1 = hyp.W1) (hW2H : h46.W2 ≤ H)
    (hcen : h46.W2.subgroupOf H ≤ Subgroup.center ↥H) :
    h46.W2 ≤ Subgroup.center ↥L := by
  intro w hw
  have hwZH : (⟨w, hW2H hw⟩ : ↥H) ∈ Subgroup.center ↥H :=
    hcen (Subgroup.mem_subgroupOf.mpr hw)
  rw [Subgroup.mem_center_iff] at hwZH
  rw [Subgroup.mem_center_iff]
  intro g
  have hg : g ∈ Subgroup.closure ((H : Set ↥L) ∪ (hyp.W1 : Set ↥L)) := by
    rw [Subgroup.closure_union, Subgroup.closure_eq, Subgroup.closure_eq, hyp.split.sup_eq_top]
    exact Subgroup.mem_top g
  have hcomm : Commute g w := by
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with hxH | hxW1
      · have h3 : ((⟨x, hxH⟩ * ⟨w, hW2H hw⟩ : ↥H) : ↥L) =
            ((⟨w, hW2H hw⟩ * ⟨x, hxH⟩ : ↥H) : ↥L) := congrArg _ (hwZH ⟨x, hxH⟩)
        rw [Subgroup.coe_mul, Subgroup.coe_mul] at h3
        exact h3
      · exact h46.commute_of_mem_W1_of_mem_W2 (by rw [hW1]; exact hxW1) hw
    | one => exact Commute.one_left w
    | mul x y _ _ ihx ihy => exact ihx.mul_left ihy
    | inv x _ ihx => exact ihx.inv_left
  exact hcomm

/-- **Peterfalvi (6.8) case-B coherence from c2 data** (discharges `hcaseB` of the dispatch
skeleton).
Given the case-B math condition `W₂ ⊆ Z(H)` (`hcen`) and the `p`-group structure, derive the
structural inputs `hderiv` (W₂ ⊆ commutator via `commutator_subgroupOf_self`), `hcZ` (`|W₂|` prime),
and `hW2cenL` (`caseB_W2_le_center_L`), then feed `nonempty_coherent_S_caseB_of_structure`
(cont.¹³).
The FPF index data (`hc2`/`hfpf`/`hFPF`) and the X/Y-cardinality conditions (`hYcard`/`hXne`) remain
as named hypotheses, to be discharged separately (`hfpf` via `caseB_fpf_bound`, the rest from the
final `S08:59` wiring). -/
theorem nonempty_coherent_S_caseB_of_c2_data (hyp : SibleyDadeHypothesis G L H)
    [H.Normal] [Finite ↥H]
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L) (hHK : h46.K = H)
    (hW1 : h46.W1 = hyp.W1)
    [NeZero (Nat.card h46.W1)] [Invertible (Nat.card ↥h46.K : ℂ)]
    [Finite ↥(h46.W1 ⊔ h46.W2)] [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    [Finite (OddOrder.Peterfalvi.S06.ticVdiff h46).W]
    [Invertible (Nat.card (OddOrder.Peterfalvi.S06.ticVdiff h46).W : ℂ)]
    [h46.W2.Normal] [Invertible (Nat.card ↥h46.W2 : ℂ)]
    [Finite ↥(h46.W2.subgroupOf H)] [Invertible (Nat.card ↥(h46.W2.subgroupOf H) : ℂ)]
    (hW2H : h46.W2 ≤ H) (hcop : Nat.Coprime (Nat.card ↥H) (Nat.card hyp.W1))
    {p : ℕ} (hp : p.Prime) (hHp : IsPGroup p ↥H)
    (hprime : (Nat.card h46.W2).Prime) (hW2comm : h46.W2 ≤ ⁅H, H⁆)
    (hcen : h46.W2.subgroupOf H ≤ Subgroup.center ↥H)
    (hc2 : 2 ≤ (h46.W2.subgroupOf H).index)
    (hfpf : (2 * Nat.card hyp.W1 + 1) ^ 2 ≤ Nat.card (↥H ⧸ h46.W2.subgroupOf H))
    (hFPF : (h46.W2.index : ℤ) < ((h46.W2.subgroupOf H).index : ℤ) ^ 2)
    (hXne : (hyp.Xset h46.W2).Nonempty) :
    Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.S
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)) := by
  have : Fintype ↥H := Fintype.ofFinite _
  have : Fintype ↥(h46.W1 ⊔ h46.W2) := Fintype.ofFinite _
  have : Fintype (OddOrder.Peterfalvi.S06.ticVdiff h46).W := Fintype.ofFinite _
  have : Fintype ↥(h46.W2.subgroupOf H) := Fintype.ofFinite _
  have hderiv : h46.W2.subgroupOf H ≤ commutator ↥H := by
    rw [← commutator_subgroupOf_self]
    exact fun x hx => Subgroup.mem_subgroupOf.mpr (hW2comm (Subgroup.mem_subgroupOf.mp hx))
  have hcZ : 2 ≤ Nat.card ↥(h46.W2.subgroupOf H) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW2H).toEquiv]; exact hprime.two_le
  have hW2cenL : h46.W2 ≤ Subgroup.center ↥L := caseB_W2_le_center_L hyp h46 hW1 hW2H hcen
  exact nonempty_coherent_S_caseB_of_structure hyp h46 hHK hW1 hW2H hcen hderiv hcop hp hHp
    hprime hW2comm hW2cenL hc2 hFPF hcZ hfpf hXne

/-- **Peterfalvi (6.8) case-B coherence — full c2 FPF/index structure-data discharge.**

Strengthens `nonempty_coherent_S_caseB_of_c2_data` by deriving the FPF/index structure data
(`hfpf`/`hc2`/`hFPF`) *internally* from the `p`-group + central-`W₂` context, so that only the
genuine (6.8.3) *case* conditions remain as named hypotheses:
* `hWMgt` — `W₂ ⊊ ⁅H,H⁆` (`1 < |⁅H,H⁆ : W₂|`), i.e. `Z = W₂ ≠ H' = ⁅H,H⁆`, the (6.8.3) nontrivial
  branch (when `Z = H'` we already have `S = X ∪ Y` coherent by (6.8.2));
* `hYcard` — `m = |Y| ≠ 2`, the (6.8.2) exceptional case;
* `hXne` — `X` nonempty.

The (6.8.3) FPF bound `hfpf : (2|W₁|+1)² ≤ |H:W₂|` comes from `caseB_fpf_bound` (`W₂ ≤ Z(L)` via
`caseB_W2_le_center_L`; `H` non-abelian via nilpotency — `⁅H,H⁆ ⊊ H` so `1 < |H:⁅H,H⁆|`).  The
remaining index data is arithmetic: `hc2` (`|H:W₂| ≥ 9 ≥ 2`) and `hFPF`
(`|W₂|_L = |H:W₂|·|W₁| < |H:W₂|²` since `|W₁| < |H:W₂|`, via `relIndex_mul_index` and
`index_H_eq_card_W1`).  This is the clean `hcaseB` producer feeding the dispatch skeleton
`nonempty_coherent_S_of_c2_of_branches`. -/
theorem nonempty_coherent_S_caseB_of_c2 (hyp : SibleyDadeHypothesis G L H)
    [H.Normal] [Finite ↥H]
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L) (hHK : h46.K = H)
    (hW1 : h46.W1 = hyp.W1)
    [NeZero (Nat.card h46.W1)] [Invertible (Nat.card ↥h46.K : ℂ)]
    [Finite ↥(h46.W1 ⊔ h46.W2)] [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    [Finite (OddOrder.Peterfalvi.S06.ticVdiff h46).W]
    [Invertible (Nat.card (OddOrder.Peterfalvi.S06.ticVdiff h46).W : ℂ)]
    [h46.W2.Normal] [Invertible (Nat.card ↥h46.W2 : ℂ)]
    [Finite ↥(h46.W2.subgroupOf H)] [Invertible (Nat.card ↥(h46.W2.subgroupOf H) : ℂ)]
    (hW2H : h46.W2 ≤ H) (hcop : Nat.Coprime (Nat.card ↥H) (Nat.card hyp.W1))
    {p : ℕ} (hp : p.Prime) (hHp : IsPGroup p ↥H)
    (hprime : (Nat.card h46.W2).Prime) (hW2comm : h46.W2 ≤ ⁅H, H⁆)
    (hcen : h46.W2.subgroupOf H ≤ Subgroup.center ↥H)
    (hWMgt : 1 < (h46.W2.subgroupOf H).relIndex (commutator ↥H))
    (hXne : (hyp.Xset h46.W2).Nonempty) :
    Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.S
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)) := by
  have : Fintype ↥H := Fintype.ofFinite _
  have : Fintype ↥(h46.W1 ⊔ h46.W2) := Fintype.ofFinite _
  have : Fintype (OddOrder.Peterfalvi.S06.ticVdiff h46).W := Fintype.ofFinite _
  have : Fintype ↥(h46.W2.subgroupOf H) := Fintype.ofFinite _
  let : Group.IsNilpotent ↥H := hyp.H_nilpotent
  have : Nontrivial ↥H := (Subgroup.nontrivial_iff_ne_bot H).mpr hyp.H_ne_bot
  -- `W₂ ≤ Z(L)` (case-B central datum).
  have hW2cenL : h46.W2 ≤ Subgroup.center ↥L := caseB_W2_le_center_L hyp h46 hW1 hW2H hcen
  -- `H` non-abelian: `⁅H,H⁆ ⊊ H`, so `1 < |H : ⁅H,H⁆|`.
  have hMgt : 1 < (commutator ↥H).index := by
    have hne : commutator ↥H ≠ ⊤ := (Group.IsSolvable.commutator_lt_top_of_nontrivial ↥H).ne
    have h0 : (commutator ↥H).index ≠ 0 := Subgroup.index_ne_zero_of_finite
    have h1 : (commutator ↥H).index ≠ 1 := fun h => hne (Subgroup.index_eq_one.mp h)
    omega
  -- the (6.8.3) FPF bound `(2|W₁|+1)² ≤ |H:W₂|`.
  have hfpf : (2 * Nat.card hyp.W1 + 1) ^ 2 ≤ Nat.card (↥H ⧸ h46.W2.subgroupOf H) :=
    caseB_fpf_bound hyp h46.toCertainTypeHypothesis hHK hW1 hW2comm hW2cenL hcop hMgt hWMgt
  have hw1pos : 1 ≤ Nat.card hyp.W1 := Nat.card_pos
  -- `|H:W₂| ≥ 2`.
  have hc2 : 2 ≤ (h46.W2.subgroupOf H).index :=
    le_trans (le_trans (by omega) (Nat.le_self_pow (by norm_num) (2 * Nat.card hyp.W1 + 1))) hfpf
  -- `|W₂|_L = |H:W₂|·|W₁| < |H:W₂|²`.
  have hFPF : (h46.W2.index : ℤ) < ((h46.W2.subgroupOf H).index : ℤ) ^ 2 := by
    have hidx : h46.W2.index = (h46.W2.subgroupOf H).index * Nat.card hyp.W1 := by
      have h := Subgroup.relIndex_mul_index hW2H
      rw [hyp.index_H_eq_card_W1] at h
      exact h.symm
    have hw1lt : Nat.card hyp.W1 < (h46.W2.subgroupOf H).index :=
      lt_of_lt_of_le
        (lt_of_lt_of_le (by omega) (Nat.le_self_pow (by norm_num) (2 * Nat.card hyp.W1 + 1))) hfpf
    have hw1ltZ : (Nat.card hyp.W1 : ℤ) < ((h46.W2.subgroupOf H).index : ℤ) := by
      exact_mod_cast hw1lt
    have hiposZ : (0 : ℤ) < ((h46.W2.subgroupOf H).index : ℤ) := by
      exact_mod_cast lt_of_le_of_lt (Nat.zero_le _) hw1lt
    rw [hidx]; push_cast; nlinarith [hw1ltZ, hiposZ]
  exact nonempty_coherent_S_caseB_of_c2_data hyp h46 hHK hW1 hW2H hcop hp hHp hprime hW2comm
    hcen hc2 hfpf hFPF hXne

end OddOrder.Peterfalvi.S08


