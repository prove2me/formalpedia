-- Prove2me | Definitions.Def_OddOrder_GroupTheory_IsExtraspecial
-- name    : OddOrder_GroupTheory_IsExtraspecial
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T04:47:49.45345+00:00
-- url     : https://prove2.me/theorems/691f163e-d609-471b-a6d9-6a1f30a55a76
-- title:
--   Extraspecial $p$-groups
-- statement:
--   Introduces extraspecial $p$-groups, absent from Mathlib, as needed for Bender–Glauberman §2 Thm 2.5 (faithful irreducible modules of extraspecial groups), BG §4 Lemma 4.15 (extraspecial commutator constraint) and Isaacs Ch. 6.
--
--   Main definitions: `IsExtraspecial p G` (a $p$-group with $Z(G)=[G,G]=\Phi(G)$ of order $p$), `IsSpecial` (special $p$-groups, Gorenstein *Finite Groups* §3) and `IsExpPExtraspecial` (extraspecial $p$-groups of exponent $p$).
--
--   The bundle also proves 8 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/GroupTheory/IsExtraspecial.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/GroupTheory/IsExtraspecial.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_GroupTheory_ElementaryAbelian
import Definitions.Def_OddOrder_GroupTheory_FrattiniPGroup
import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.Frattini
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.GroupTheory.SpecificGroups.Cyclic

open scoped commutatorElement

namespace OddOrder.GroupTheory

/-- **Extraspecial p-group**: `G` is a `p`-group with
`Z(G) = [G, G] = Φ(G)` and `|Z(G)| = p`.

これは Isaacs FGT Defn 6.6 / Aschbacher §23 の標準定義. `frattini = center`
は p-群 G で `Φ(G) = [G, G] ⊔ {g^p}_{g∈G}` を介して `∀ g, g^p ∈ Z(G)` と同値. -/
structure IsExtraspecial (p : ℕ) (G : Type*) [Group G] : Prop where
  /-- `G` is a `p`-group. -/
  isPGroup : IsPGroup p G
  /-- The commutator subgroup equals the center: `[G, G] = Z(G)`. -/
  commutator_eq_center : commutator G = Subgroup.center G
  /-- The Frattini subgroup equals the center: `Φ(G) = Z(G)`. -/
  frattini_eq_center : frattini G = Subgroup.center G
  /-- The center has order `p`. -/
  center_card : Nat.card (Subgroup.center G) = p

/-- **Special p-group** (Gorenstein, _Finite Groups_, §3, after Theorem 3.7): a `p`-group
`G` is *special* if it is either elementary abelian, or of class `2` with
`G' = Z(G) = Φ(G)` elementary abelian. (The class-`2` case with `|G'| = p` is exactly
extraspecial.) Equivalently `Φ(G) = G' ⊆ Z(G)` with `G/G'` and the common subgroup
elementary abelian.

Used in **BG §4 Lemma 4.13** (= **G** Theorem 4.15(ii), precursor 2, issue 0051): a minimal
`A`-invariant subgroup on which a nontrivial `p'`-automorphism acts is special of exponent
`p` (Gorenstein Theorems 3.7/3.8/3.10). -/
def IsSpecial (p : ℕ) (G : Type*) [Group G] : Prop :=
  IsPGroup p G ∧
    (IsElementaryAbelian p G ∨
      (commutator G = Subgroup.center G ∧ frattini G = Subgroup.center G ∧
        (Subgroup.center G).IsElementaryAbelian p))

namespace IsSpecial

variable {p : ℕ} {G : Type*} [Group G]

/-- **`IsSpecial` transports along group isomorphisms** (each ingredient — `p`-group,
elementary abelian, commutator, centre, Frattini — corresponds under `e`). -/
theorem of_mulEquiv {H : Type*} [Group H] (e : G ≃* H) (h : IsSpecial p G) : IsSpecial p H := by
  obtain ⟨hpg, hcase⟩ := h
  refine ⟨hpg.of_injective e.symm.toMonoidHom e.symm.injective, ?_⟩
  rcases hcase with hEA | ⟨hcomm, hfrat, hZEA⟩
  · exact Or.inl (IsElementaryAbelian.of_mulEquiv e hEA)
  refine Or.inr ?_
  have hcenter : (Subgroup.center G).map e.toMonoidHom = Subgroup.center H := by
    ext x
    simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom]
    constructor
    · rintro ⟨z, hz, rfl⟩
      rw [Subgroup.mem_center_iff] at hz ⊢
      intro g
      calc g * e z = e (e.symm g * z) := by rw [map_mul, e.apply_symm_apply]
        _ = e (z * e.symm g) := by rw [hz (e.symm g)]
        _ = e z * g := by rw [map_mul, e.apply_symm_apply]
    · intro hx
      refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
      rw [Subgroup.mem_center_iff] at hx ⊢
      intro g
      apply e.injective
      rw [map_mul, map_mul, e.apply_symm_apply]
      exact hx (e g)
  have hcommutator : (commutator G).map e.toMonoidHom = commutator H := by
    rw [commutator_def, commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ e.surjective]
  have hfrattini : (frattini G).map e.toMonoidHom = frattini H := by
    refine le_antisymm ?_ ?_
    · rw [Subgroup.map_le_iff_le_comap]
      exact frattini_le_comap_frattini_of_surjective e.surjective
    · have h2 := frattini_le_comap_frattini_of_surjective
        (φ := e.symm.toMonoidHom) e.symm.surjective
      rwa [Subgroup.map_equiv_eq_comap_symm']
  refine ⟨?_, ?_, ?_⟩
  · rw [← hcommutator, hcomm]
    exact hcenter
  · rw [← hfrattini, hfrat]
    exact hcenter
  · rw [← hcenter]
    exact Subgroup.IsElementaryAbelian.map e.injective hZEA

end IsSpecial

namespace IsExtraspecial

variable {p : ℕ} {G : Type*} [Group G]

/-- The commutator subgroup of an extraspecial group equals its Frattini subgroup. -/
theorem commutator_eq_frattini (h : IsExtraspecial p G) :
    commutator G = frattini G :=
  h.commutator_eq_center.trans h.frattini_eq_center.symm

/-- The commutator subgroup of an extraspecial group has cardinality `p`. -/
theorem commutator_card (h : IsExtraspecial p G) : Nat.card (commutator G) = p := by
  rw [h.commutator_eq_center]; exact h.center_card

/-- **A nonabelian group of order `p³` is extraspecial** (Coq mathcomp `p3group_extraspecial`).
A finite group `G` of order `p³` (`p` prime) that is nonabelian is extraspecial:
`Z(G) = [G, G] = Φ(G)` and `|Z(G)| = p`.

*Proof outline.* The centre has order `p^k`, `0 < k ≤ 3` (`card_center_eq_prime_pow`); `k = 3` makes
`Z = ⊤` (so `G` abelian) and `k = 2` makes `G/Z` cyclic (hence `G` abelian,
`MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center`), both excluded, so `|Z| = p`.
Then `G/Z` has order `p²`,
hence abelian, giving `[G, G] ≤ Z`; nontriviality of `[G, G]` (nonabelian) and `|Z| = p` prime force
`[G, G] = Z`.  Finally `Z = [G, G] ≤ Φ(G)` (`commutator_sup_pow_closure_le_frattini`), and `Φ(G)` is
proper (`frattini_le_coatom`); were `|Φ| = p²` then `|G/Φ| = p` so `G/Φ` is cyclic, forcing `G`
cyclic (`isCyclic_of_isCyclic_quotient_frattini`, Burnside basis) hence abelian — excluded.  So
`|Φ| = p = |Z|`, whence `Φ = Z`.

This is Coq `p3group_extraspecial`, used for BG Theorem 15.7(e) disjunct 3 (the `O_p(M_F)` of order
`p³` Singer/`SL₂(p)` case) and reusable for any nonabelian `p`-group of order `p³`. -/
theorem of_card_eq_prime_cube [Finite G] [Fact p.Prime]
    (hcard : Nat.card G = p ^ 3) (hnonab : ¬ ∀ a b : G, a * b = b * a) :
    IsExtraspecial p G := by
  have hp : p.Prime := Fact.out
  have hpg : IsPGroup p G := IsPGroup.of_card hcard
  have : Nontrivial G := by
    rcases subsingleton_or_nontrivial G with hs | hn
    · exact absurd (fun a b => Subsingleton.elim _ _) hnonab
    · exact hn
  -- Step 1: `|Z(G)| = p`.
  obtain ⟨k, hk0, hk⟩ := IsPGroup.card_center_eq_prime_pow hcard (by norm_num)
  have hk3 : k ≤ 3 := by
    have hle : Nat.card (Subgroup.center G) ≤ Nat.card G :=
      Nat.le_of_dvd Nat.card_pos (Subgroup.card_subgroup_dvd_card _)
    rw [hk, hcard] at hle
    exact (Nat.pow_le_pow_iff_right hp.one_lt).mp hle
  have hcardZ : Nat.card (Subgroup.center G) = p := by
    have hkne3 : k ≠ 3 := by
      rintro rfl
      have htop : Subgroup.center G = ⊤ := Subgroup.eq_top_of_card_eq _ (by rw [hk, hcard])
      exact hnonab fun a b => by
        have ha : a ∈ Subgroup.center G := htop ▸ Subgroup.mem_top a
        exact (Subgroup.mem_center_iff.mp ha b).symm
    have hkne2 : k ≠ 2 := by
      rintro rfl
      have hcardQ : Nat.card (G ⧸ Subgroup.center G) = p := by
        have heq := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center G)
        rw [hcard, hk] at heq
        have hmul : Nat.card (G ⧸ Subgroup.center G) * p ^ 2 = p * p ^ 2 := by rw [← heq]; ring
        exact Nat.eq_of_mul_eq_mul_right (pow_pos hp.pos 2) hmul
      have : IsCyclic (G ⧸ Subgroup.center G) := isCyclic_of_prime_card hcardQ
      exact hnonab ((MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center
        (QuotientGroup.mk' (Subgroup.center G)) (QuotientGroup.ker_mk' _).le).is_comm.comm)
    have hk1 : k = 1 := by omega
    rw [hk, hk1, pow_one]
  -- Step 2: `[G, G] = Z(G)`.
  have hcardQ2 : Nat.card (G ⧸ Subgroup.center G) = p ^ 2 := by
    have heq := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center G)
    rw [hcard, hcardZ] at heq
    have hmul : Nat.card (G ⧸ Subgroup.center G) * p = p ^ 2 * p := by rw [← heq]; ring
    exact Nat.eq_of_mul_eq_mul_right hp.pos hmul
  have hcomm_le_center : commutator G ≤ Subgroup.center G := by
    rw [commutator_def, Subgroup.commutator_le]
    intro x _ y _
    have hQcomm := IsPGroup.isMulCommutative_of_card_eq_prime_sq hcardQ2
    have hpi : (QuotientGroup.mk' (Subgroup.center G)) ⁅x, y⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_commute]
      exact (isMulCommutative_iff.mp hQcomm) _ _
    exact (QuotientGroup.eq_one_iff _).mp hpi
  have hcomm_ne_bot : commutator G ≠ ⊥ := by
    obtain ⟨a, b, hab⟩ : ∃ a b : G, a * b ≠ b * a := by
      by_contra hc
      refine hnonab fun a b => ?_
      by_contra h
      exact hc ⟨a, b, h⟩
    intro hbot
    refine hab (commutatorElement_eq_one_iff_commute.mp ?_)
    have hmem : ⁅a, b⁆ ∈ commutator G := by
      rw [commutator_def]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
    rwa [hbot, Subgroup.mem_bot] at hmem
  have hcomm_eq_center : commutator G = Subgroup.center G := by
    have hdvd : Nat.card (commutator G) ∣ Nat.card (Subgroup.center G) :=
      Subgroup.card_dvd_of_le hcomm_le_center
    rw [hcardZ] at hdvd
    have hne1 : Nat.card (commutator G) ≠ 1 := fun h1 =>
      hcomm_ne_bot (Subgroup.card_eq_one.mp h1)
    have hcardC : Nat.card (commutator G) = p := ((Nat.dvd_prime hp).mp hdvd).resolve_left hne1
    exact Subgroup.eq_of_le_of_card_ge hcomm_le_center (by rw [hcardZ, hcardC])
  -- Step 3: `Φ(G) = Z(G)`.
  have hZle : Subgroup.center G ≤ frattini G :=
    hcomm_eq_center ▸ le_sup_left.trans (IsPGroup.commutator_sup_pow_closure_le_frattini hpg)
  have hfr_ne_top : frattini G ≠ ⊤ := by
    obtain ⟨M, hM, _⟩ :=
      (IsCoatomic.eq_top_or_exists_le_coatom (⊥ : Subgroup G)).resolve_left bot_lt_top.ne
    exact fun htop => hM.1 (le_antisymm le_top (htop ▸ frattini_le_coatom hM))
  have hcardFr : Nat.card (frattini G) = p := by
    have hple : p ≤ Nat.card (frattini G) := by
      rw [← hcardZ]; exact Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_le hZle)
    have hdvd : Nat.card (frattini G) ∣ p ^ 3 := by
      rw [← hcard]; exact Subgroup.card_subgroup_dvd_card _
    obtain ⟨j, hj3, hj⟩ := (Nat.dvd_prime_pow hp).mp hdvd
    have hj0 : j ≠ 0 := by
      rintro rfl
      rw [hj, pow_zero] at hple
      have := hp.one_lt; omega
    have hjne3 : j ≠ 3 := fun h =>
      hfr_ne_top (Subgroup.eq_top_of_card_eq _ (by rw [hj, h, hcard]))
    have hjne2 : j ≠ 2 := by
      intro h
      have hcardQF : Nat.card (G ⧸ frattini G) = p := by
        have heq := Subgroup.card_eq_card_quotient_mul_card_subgroup (frattini G)
        rw [hcard, hj, h] at heq
        have hmul : Nat.card (G ⧸ frattini G) * p ^ 2 = p * p ^ 2 := by rw [← heq]; ring
        exact Nat.eq_of_mul_eq_mul_right (pow_pos hp.pos 2) hmul
      have : IsCyclic (G ⧸ frattini G) := isCyclic_of_prime_card hcardQF
      have : IsCyclic G := OddOrder.GroupTheory.isCyclic_of_isCyclic_quotient_frattini ‹_›
      obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
      refine hnonab fun a b => ?_
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg a)
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg b)
      rw [← zpow_add, ← zpow_add, add_comm]
    have : j = 1 := by omega
    rw [hj, this, pow_one]
  exact ⟨hpg, hcomm_eq_center,
    (Subgroup.eq_of_le_of_card_ge hZle (by rw [hcardZ, hcardFr])).symm, hcardZ⟩

/-- **A nonabelian special group with cyclic centre is extraspecial.**
A special `p`-group `G` (`IsSpecial p G`) that is *not* elementary abelian (equivalently,
nonabelian) and whose centre is cyclic is extraspecial: in the nonabelian branch of `IsSpecial`,
`Z(G) = [G, G] = Φ(G)` is elementary abelian, and being additionally cyclic forces `|Z(G)| = p`.

This is the closing structural step of **BG Theorem 3.4** (step 7): Gorenstein's Theorem 5.3.7
leaves `K` either elementary abelian or nonabelian special; the elementary abelian case is excluded
earlier, and `Z(K) ⊆ Z(G)` is cyclic, so `K` is extraspecial and Theorem 2.5 applies. -/
theorem of_isSpecial_of_isCyclic_center [Finite G] [Fact p.Prime]
    (hsp : IsSpecial p G) (hnonab : ¬ IsElementaryAbelian p G)
    (hcyc : IsCyclic (Subgroup.center G)) :
    IsExtraspecial p G := by
  obtain ⟨hpg, hdisj⟩ := hsp
  rcases hdisj with helem | ⟨hcomm, hfrat, hZelem⟩
  · exact absurd helem hnonab
  -- Nonabelian branch: `Z(G) = [G,G] = Φ(G)` elementary abelian.  `G` (hence `Z(G)`) is nontrivial.
  have : Nontrivial G := by
    by_contra hcon
    rw [not_nontrivial_iff_subsingleton] at hcon
    exact hnonab ⟨fun x y => Subsingleton.elim _ _, fun x => Subsingleton.elim _ _⟩
  have hZnt : Nontrivial (Subgroup.center G) := hpg.center_nontrivial
  have : IsCyclic (Subgroup.center G) := hcyc
  refine ⟨hpg, hcomm, hfrat, ?_⟩
  -- `Z(G)` cyclic + elementary abelian ⟹ `exponent = card` divides `p`; nontrivial ⟹ `card = p`.
  have hZea : IsElementaryAbelian p (Subgroup.center G) := hZelem
  have hdvd : Nat.card (Subgroup.center G) ∣ p := by
    rw [← IsCyclic.exponent_eq_card, Monoid.exponent_dvd_iff_forall_pow_eq_one]
    exact hZea.pow_eq_one
  have hgt : 1 < Nat.card (Subgroup.center G) := Finite.one_lt_card_iff_nontrivial.mpr hZnt
  rcases (Nat.dvd_prime (Fact.out : p.Prime)).mp hdvd with h1 | hp
  · omega
  · exact hp

end IsExtraspecial

/-- **Extraspecial p-group of exponent p**: an extraspecial `p`-group all of whose
elements satisfy `g ^ p = 1` (equivalently `Monoid.exponent G = p`).

これは **BG §4 Thm 4.16** condition (2) / **BG Cor 10.7(b)** で現れる中心積の
非可換因子 `R₁` (= Heisenberg 群 `M(p,1)`, 位数 `p³`) の構造を記述する再利用可能な
述語. Thm 4.16 の Case B-1 では `S = Ω₁(R)` が `r(R) = 2` から非可換 ⇒ extraspecial,
かつ Prop 4.8 から exponent `p` であることが示され, この述語の witness となる.

**重要**: 位数 `p³` はこの述語に **含めない**. Thm 4.16 の証明内部で `|Ω₁(R)| = p³`
として別途確立される (Prop 4.8) ため, ここでは exponent-`p` 部分のみを述語化する.

`p` prime 仮定は def 段階では不要 (`IsExtraspecial` と同様 mathlib 慣用). -/
def IsExpPExtraspecial (p : ℕ) (G : Type*) [Group G] : Prop :=
  IsExtraspecial p G ∧ Monoid.exponent G = p

namespace IsExpPExtraspecial

variable {p : ℕ} {G : Type*} [Group G]

/-- An exponent-`p` extraspecial group is extraspecial. -/
theorem isExtraspecial (h : IsExpPExtraspecial p G) : IsExtraspecial p G := h.1

/-- An exponent-`p` extraspecial group has `Monoid.exponent` equal to `p`. -/
theorem exponent_eq (h : IsExpPExtraspecial p G) : Monoid.exponent G = p := h.2

/-- Every element of an exponent-`p` extraspecial group satisfies `g ^ p = 1`.

This is the form consumed in BG §4 Thm 4.16 Case B-1, where `S = Ω₁(R)` has exponent
`p` and hence every element of `S` is killed by `p`-th power. -/
theorem pow_eq_one (h : IsExpPExtraspecial p G) (g : G) : g ^ p = 1 := by
  rw [← h.exponent_eq]; exact Monoid.pow_exponent_eq_one g

end IsExpPExtraspecial

end OddOrder.GroupTheory


