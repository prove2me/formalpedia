-- Prove2me | Definitions.Def_OddOrder_BG_Ch1_Preliminary_S02_FixedSubmodules
-- name    : OddOrder_BG_Ch1_Preliminary_S02_FixedSubmodules
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T05:37:23.323839+00:00
-- url     : https://prove2.me/theorems/6f8915f9-36ac-48bc-90f1-e8b94c315101
-- title:
--   Bender–Glauberman §2: fixed submodules
-- statement:
--   A part of the Bender–Glauberman §2 formalization (representations) on fixed submodules, preparing the proof of Theorem 2.6. Its docstring gives no further description, and the bundle contains no definitions of its own.
--
--   The bundle consists of lemmas only.
--
--   The bundle also proves 7 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/Ch1_Preliminary/S02_FixedSubmodules.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/BG/Ch1_Preliminary/S02_FixedSubmodules.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_BG_Ch1_Preliminary_S02_RepresentationsBasic
import Definitions.Def_OddOrder_BG_Ch1_Preliminary_S02_FixedQuotientMachinery

namespace OddOrder.BG.Ch1.S02

open scoped Pointwise

open OddOrder.RepresentationTheory (baseChangeRepresentation baseChangeRepresentation_apply_tmul
  baseChangeRepresentation_faithful)

/-- If the ambient group is abelian, then the Sylow conclusion of
BG Thm 2.6(b) is immediate. -/
theorem sylow_commutative_and_commutator_le_of_commutative
    {p : ℕ} {G : Type*} [Group G]
    (hGcomm : Std.Commutative (· * · : G → G → G))
    (P : Sylow p G) :
    Std.Commutative (· * · : P → P → P) ∧
      commutator G ≤ (P : Subgroup G) := by
  constructor
  · constructor
    intro x y
    exact Subtype.ext (hGcomm.comm x y)
  · intro g hg
    have hcomm_bot : commutator G = ⊥ := by
      rw [commutator_eq_bot_iff_center_eq_top, Subgroup.eq_top_iff']
      intro x
      rw [Subgroup.mem_center_iff]
      intro y
      exact hGcomm.comm y x
    rw [hcomm_bot] at hg
    have hg_one : g = 1 := by simpa using hg
    simp [hg_one]

/-- q = p endpoint phrased as the existence of a nontrivial normal p-subgroup.

This is the theorem-facing reduction left after the fixed-space helpers: the
full BG proof only has to produce such a subgroup, then this lemma supplies
the Sylow conclusion. -/
theorem sylow_commutative_and_commutator_le_of_exists_nontrivial_normal_pSubgroup
    {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [CharP F p]
    {G : Type*} [Group G] [Finite G] [Finite (Sylow p G)]
    {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]
    (ρ : Representation F G V) (hfaithful : Function.Injective ρ)
    (hdim : Module.finrank F V = 2)
    (hexists : ∃ K : Subgroup G, K.Normal ∧ IsPGroup p K ∧ K ≠ ⊥)
    (P : Sylow p G) :
    Std.Commutative (· * · : P → P → P) ∧
      commutator G ≤ (P : Subgroup G) := by
  rcases hexists with ⟨K, hKnormal, hK, hK_ne_bot⟩
  have : K.Normal := hKnormal
  exact sylow_commutative_and_commutator_le_of_nontrivial_normal_p_fixed_space
    K ρ hfaithful hK hdim hK_ne_bot P

/-- q = p endpoint when the determinant kernel `G*` is trivial.

This is the `G* = 1` branch in BG Thm 2.6: the determinant character embeds
`G` into `Fˣ`, so `G` is abelian and hence every Sylow subgroup is abelian and
contains `G'`. -/
theorem sylow_commutative_and_commutator_le_of_determinantKernel_eq_bot
    {p : ℕ} [Fact p.Prime] {F : Type*} [Field F]
    {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module F V]
    (ρ : Representation F G V) (hdet : determinantKernelSubgroup ρ = ⊥)
    (P : Sylow p G) :
    Std.Commutative (· * · : P → P → P) ∧
      commutator G ≤ (P : Subgroup G) := by
  exact sylow_commutative_and_commutator_le_of_commutative
    (commutative_of_determinantKernel_eq_bot ρ hdet) P

/-- q = p endpoint when the determinant kernel `G*` itself is a nontrivial
p-subgroup.

In this case `G*` is already the nontrivial normal p-subgroup needed by the
fixed-space reduction. -/
theorem sylow_commutative_and_commutator_le_of_nontrivial_determinantKernel_pGroup
    {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [CharP F p]
    {G : Type*} [Group G] [Finite G] [Finite (Sylow p G)]
    {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]
    (ρ : Representation F G V) (hfaithful : Function.Injective ρ)
    (hdim : Module.finrank F V = 2)
    (hdet_p : IsPGroup p (determinantKernelSubgroup ρ))
    (hdet_ne_bot : determinantKernelSubgroup ρ ≠ ⊥)
    (P : Sylow p G) :
    Std.Commutative (· * · : P → P → P) ∧
      commutator G ≤ (P : Subgroup G) := by
  have : (determinantKernelSubgroup ρ).Normal :=
    determinantKernelSubgroup_normal ρ
  exact sylow_commutative_and_commutator_le_of_nontrivial_normal_p_fixed_space
    (determinantKernelSubgroup ρ) ρ hfaithful hdet_p hdim hdet_ne_bot P

/-- A nontrivial normal `p`-subgroup forces the `p`-core to be nontrivial.

This is the small `O_p` bridge used twice in BG Thm 2.6: once for `O_p(G*)`,
and once inside the normalizer of a Sylow `q`-subgroup in the `q ≠ p` branch. -/
theorem opCore_ne_bot_of_nontrivial_normal_pSubgroup
    {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [Finite (Sylow p G)]
    {K : Subgroup G} [K.Normal] (hK : IsPGroup p K) (hK_ne_bot : K ≠ ⊥) :
    OddOrder.Isaacs.Ch01.opCore p G ≠ ⊥ := by
  intro hop_bot
  apply hK_ne_bot
  refine le_bot_iff.mp ?_
  intro x hx
  rw [← hop_bot]
  exact OddOrder.Isaacs.Ch01.normal_pgroup_le_opCore hK hx

/-- A finite nontrivial abelian group has a nontrivial prime core.

This is one half of the induction-output bridge for BG Thm 2.6: when an
inductive subgroup is abelian, any nontrivial Sylow subgroup is normal, hence it
lies in the corresponding `O_r`. -/
theorem exists_prime_opCore_ne_bot_of_commutative
    {G : Type*} [Group G] [Finite G] [Nontrivial G]
    (hGcomm : Std.Commutative (· * · : G → G → G)) :
    ∃ r : ℕ, r.Prime ∧ OddOrder.Isaacs.Ch01.opCore r G ≠ ⊥ := by
  have hcard_ne_one : Nat.card G ≠ 1 := (Finite.one_lt_card (α := G)).ne'
  obtain ⟨r, hr_prime, hr_dvd⟩ :=
    Nat.exists_prime_and_dvd hcard_ne_one
  have : Fact r.Prime := ⟨hr_prime⟩
  have : Finite (Sylow r G) := inferInstance
  obtain ⟨P⟩ := Sylow.nonempty (p := r) (G := G)
  have hP_ne_bot : (P : Subgroup G) ≠ ⊥ := P.ne_bot_of_dvd_card hr_dvd
  have hPnormal : (P : Subgroup G).Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [hGcomm.comm g x]
    simpa [mul_assoc] using hx
  have : (P : Subgroup G).Normal := hPnormal
  exact ⟨r, hr_prime,
    opCore_ne_bot_of_nontrivial_normal_pSubgroup
      (G := G) (K := (P : Subgroup G)) P.2 hP_ne_bot⟩

/-- A BG Thm 2.6(b)-style Sylow conclusion supplies a nontrivial prime core.

If `G'` is nontrivial then `G' ≤ P` makes the derived subgroup a nontrivial
normal `p`-subgroup.  If `G' = 1`, the group is abelian, so a nontrivial Sylow
subgroup gives a nontrivial prime core.  This is the form needed to turn the
induction theorem's Sylow conclusion back into the `hind` input used by the
determinant-kernel spine. -/
theorem exists_prime_opCore_ne_bot_of_commutator_le_sylow
    {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [Finite G] [Nontrivial G]
    [Finite (Sylow p G)] (P : Sylow p G)
    (hcomm_le : commutator G ≤ (P : Subgroup G)) :
    ∃ r : ℕ, r.Prime ∧ OddOrder.Isaacs.Ch01.opCore r G ≠ ⊥ := by
  by_cases hcomm_bot : commutator G = ⊥
  · apply exists_prime_opCore_ne_bot_of_commutative
    constructor
    intro x y
    have hxcenter : x ∈ Subgroup.center G := by
      rw [(commutator_eq_bot_iff_center_eq_top (G := G)).mp hcomm_bot]
      trivial
    exact (Subgroup.mem_center_iff.mp hxcenter y).symm
  · have : (commutator G).Normal :=
      Subgroup.Normal.of_commutator_le (G := G) (H := commutator G) le_rfl
    have hcomm_p : IsPGroup p (commutator G) := P.2.to_le hcomm_le
    exact ⟨p, Fact.out,
      opCore_ne_bot_of_nontrivial_normal_pSubgroup
        (G := G) (K := commutator G) hcomm_p hcomm_bot⟩

end OddOrder.BG.Ch1.S02


