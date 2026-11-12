-- Prove2me | Definitions.Def_OddOrder_BG_Ch1_Preliminary_S02_TwoDimInduction
-- name    : OddOrder_BG_Ch1_Preliminary_S02_TwoDimInduction
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T05:39:26.424946+00:00
-- url     : https://prove2.me/theorems/011d8ade-961a-4a5b-b075-909d5c5269a5
-- title:
--   Bender–Glauberman §2F: the odd two-dimensional induction machinery
-- statement:
--   The strong-induction web behind Bender–Glauberman Theorem 2.6 (`odd_two_dim_abelian`): the determinant-kernel spine, the $O_p$-core branches, and the base-change/algebraic-closure transport, up to the core-spine commutativity layer. The bundle consists of lemmas only.
--
--   The bundle also proves 33 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/Ch1_Preliminary/S02_TwoDimInduction.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/BG/Ch1_Preliminary/S02_TwoDimInduction.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_BG_Ch1_Preliminary_S02_FixedSubmodules

namespace OddOrder.BG.Ch1.S02

open scoped Pointwise

open OddOrder.RepresentationTheory (baseChangeRepresentation baseChangeRepresentation_apply_tmul
  baseChangeRepresentation_faithful)

/-- The combined BG Thm 2.6 induction outputs imply a nontrivial prime core.

For a smaller subgroup in the induction, either the ambient characteristic does
not divide its order and the abelian branch supplies a normal Sylow subgroup, or
the characteristic prime divides the order and the Sylow branch supplies
`G' ≤ P`.  Both cases produce some nontrivial `O_r(G)`. -/
private theorem exists_prime_opCore_ne_bot_of_odd_two_dim_outputs
    {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [hchar : CharP F p]
    {G : Type*} [Group G] [Finite G] [Nontrivial G]
    (hab : (∀ q : ℕ, q.Prime → q ∣ Nat.card G → ¬ CharP F q) →
      Std.Commutative (· * · : G → G → G))
    (hsyl : p ∣ Nat.card G → (P : Sylow p G) →
      Std.Commutative (· * · : P → P → P) ∧
        commutator G ≤ (P : Subgroup G)) :
    ∃ r : ℕ, r.Prime ∧ OddOrder.Isaacs.Ch01.opCore r G ≠ ⊥ := by
  by_cases hp_dvd : p ∣ Nat.card G
  · have : Finite (Sylow p G) := inferInstance
    obtain ⟨P⟩ := Sylow.nonempty (p := p) (G := G)
    exact exists_prime_opCore_ne_bot_of_commutator_le_sylow
      (p := p) P (hsyl hp_dvd P).2
  · apply exists_prime_opCore_ne_bot_of_commutative
    apply hab
    intro q _hq_prime hq_dvd hq_char
    exact hp_dvd ((CharP.eq F hq_char hchar) ▸ hq_dvd)

/-- Proper determinant-kernel subgroups receive the induction output in the
shape required by the core spine.

For a normal `N < G*`, the restricted representation is still faithful and `N`
has odd order.  Thus the two BG Thm 2.6 induction outputs for that restricted
representation give the nontrivial prime core required by the determinant-kernel
normal-complement spine. -/
theorem determinantKernel_hind_of_odd_two_dim_induction_outputs
    {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [CharP F p]
    {G : Type*} [Group G] [Finite G]
    {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]
    (ρ : Representation F G V) (hfaithful : Function.Injective ρ)
    (hodd : Odd (Nat.card G)) (hdim : Module.finrank F V = 2)
    (hab_ind : ∀ N : Subgroup (determinantKernelSubgroup ρ),
      N.Normal → N ≠ ⊥ → N ≠ ⊤ → Odd (Nat.card N) →
        (σ : Representation F N V) → Function.Injective σ →
        Module.finrank F V = 2 →
        (∀ q : ℕ, q.Prime → q ∣ Nat.card N → ¬ CharP F q) →
        Std.Commutative (· * · : N → N → N))
    (hsyl_ind : ∀ N : Subgroup (determinantKernelSubgroup ρ),
      N.Normal → N ≠ ⊥ → N ≠ ⊤ → Odd (Nat.card N) →
        (σ : Representation F N V) → Function.Injective σ →
        Module.finrank F V = 2 → p ∣ Nat.card N → (P : Sylow p N) →
        Std.Commutative (· * · : P → P → P) ∧
          commutator N ≤ (P : Subgroup N))
    (N : Subgroup (determinantKernelSubgroup ρ))
    (hNnormal : N.Normal) (hN_ne_bot : N ≠ ⊥) (hN_ne_top : N ≠ ⊤) :
    ∃ r : ℕ, r.Prime ∧ OddOrder.Isaacs.Ch01.opCore r N ≠ ⊥ := by
  let Gstar : Subgroup G := determinantKernelSubgroup ρ
  let ρN : Representation F N V := ρ.comp (Gstar.subtype.comp N.subtype)
  have : Nontrivial N := (Subgroup.nontrivial_iff_ne_bot N).mpr hN_ne_bot
  have hfaithfulN : Function.Injective ρN := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact hfaithful (by simpa [ρN, Gstar] using hxy)
  have hoddN : Odd (Nat.card N) := by
    have hN_dvd_Gstar : Nat.card N ∣ Nat.card Gstar :=
      Subgroup.card_subgroup_dvd_card N
    have hGstar_dvd_G : Nat.card Gstar ∣ Nat.card G :=
      Subgroup.card_subgroup_dvd_card Gstar
    exact hodd.of_dvd_nat (hN_dvd_Gstar.trans hGstar_dvd_G)
  exact exists_prime_opCore_ne_bot_of_odd_two_dim_outputs
    (p := p) (F := F) (G := N)
    (fun hcharN => hab_ind N hNnormal hN_ne_bot hN_ne_top hoddN
      ρN hfaithfulN hdim hcharN)
    (fun hpN P => hsyl_ind N hNnormal hN_ne_bot hN_ne_top hoddN
      ρN hfaithfulN hdim hpN P)

/-- A nontrivial `p`-core in a normal subgroup gives a nontrivial `p`-core
in the ambient group.

This is the ambient-lift needed after the induction step in BG Thm 2.6: if a
normal complement `N ⊴ G*` has `O_r(N) ≠ 1`, then `O_r(G*) ≠ 1`. -/
private theorem opCore_ne_bot_of_normal_subgroup_opCore_ne_bot
    {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [Finite (Sylow p G)]
    (N : Subgroup G) [N.Normal]
    (hNcore : OddOrder.Isaacs.Ch01.opCore p N ≠ ⊥) :
    OddOrder.Isaacs.Ch01.opCore p G ≠ ⊥ := by
  let K : Subgroup G := (OddOrder.Isaacs.Ch01.opCore p N).map N.subtype
  have : (OddOrder.Isaacs.Ch01.opCore p N).Characteristic :=
    OddOrder.Isaacs.Ch01.opCore.characteristic p N
  have hKnormal : K.Normal := by
    dsimp [K]
    infer_instance
  have hKp : IsPGroup p K := by
    dsimp [K]
    exact (OddOrder.Isaacs.Ch01.opCore_isPGroup p N).map N.subtype
  have hK_ne_bot : K ≠ ⊥ := by
    intro hK_bot
    apply hNcore
    have hmap :
        (OddOrder.Isaacs.Ch01.opCore p N).map N.subtype =
          (⊥ : Subgroup N).map N.subtype := by
      simpa [K] using hK_bot
    exact (Subgroup.map_subtype_inj (H := N)).mp hmap
  exact opCore_ne_bot_of_nontrivial_normal_pSubgroup
    (G := G) (K := K) hKp hK_ne_bot

/-- A nontrivial `q`-core contains a nontrivial abelian normal `q`-subgroup.

This is the group-theoretic precursor to BG's
`K = Ω₁(Z(O_q(G^*)))`: before introducing `Ω₁`, the center of `O_q(G)` already
gives a nontrivial abelian normal `q`-subgroup. -/
private theorem exists_nontrivial_normal_commutative_qSubgroup_of_opCore_ne_bot
    {q : ℕ} [Fact q.Prime] {G : Type*} [Group G] [Finite G] [Finite (Sylow q G)]
    (hcore_ne_bot : OddOrder.Isaacs.Ch01.opCore q G ≠ ⊥) :
    ∃ K : Subgroup G, K.Normal ∧ IsPGroup q K ∧ K ≠ ⊥ ∧
      Std.Commutative (· * · : K → K → K) := by
  set O : Subgroup G := OddOrder.Isaacs.Ch01.opCore q G with hO_def
  have hO_ne_bot : O ≠ ⊥ := by
    simpa [hO_def] using hcore_ne_bot
  have hO_p : IsPGroup q O := by
    rw [hO_def]
    exact OddOrder.Isaacs.Ch01.opCore_isPGroup q G
  have hO_nontrivial : Nontrivial O :=
    (Subgroup.nontrivial_iff_ne_bot O).mpr hO_ne_bot
  have : Nontrivial O := hO_nontrivial
  have hcenter_nontrivial : Nontrivial (Subgroup.center O) := by
    have htop_nontrivial : Nontrivial (⊤ : Subgroup O) :=
      (Subgroup.nontrivial_iff_ne_bot (⊤ : Subgroup O)).mpr top_ne_bot
    have h :=
      OddOrder.Isaacs.Ch01.IsPGroup.normal_inf_center_nontrivial
        (P := O) (p := q) (N := (⊤ : Subgroup O))
        hO_p htop_nontrivial
    simpa using h
  let Z : Subgroup G := (Subgroup.center O).map O.subtype
  have : O.Normal := by
    rw [hO_def]
    infer_instance
  have : (Subgroup.center O).Characteristic := Subgroup.centerCharacteristic
  have hZnormal : Z.Normal := by
    dsimp [Z]
    infer_instance
  have hZp : IsPGroup q Z := by
    dsimp [Z]
    exact (hO_p.to_subgroup (Subgroup.center O)).map O.subtype
  have hZ_ne_bot : Z ≠ ⊥ := by
    intro hZ_bot
    have hcenter_ne_bot : Subgroup.center O ≠ ⊥ :=
      (Subgroup.nontrivial_iff_ne_bot (Subgroup.center O)).mp hcenter_nontrivial
    apply hcenter_ne_bot
    have hmap :
        (Subgroup.center O).map O.subtype = (⊥ : Subgroup O).map O.subtype := by
      simpa [Z] using hZ_bot
    exact (Subgroup.map_subtype_inj (H := O)).mp hmap
  have hZcomm : Std.Commutative (· * · : Z → Z → Z) := by
    constructor
    intro x y
    apply Subtype.ext
    rcases x.property with ⟨xO, hxO_center, hx_eq⟩
    rcases y.property with ⟨yO, _hyO_center, hy_eq⟩
    change (x : G) * (y : G) = (y : G) * (x : G)
    rw [← hx_eq, ← hy_eq]
    simpa using (congr_arg Subtype.val
      (Subgroup.mem_center_iff.mp hxO_center yO)).symm
  exact ⟨Z, hZnormal, hZp, hZ_ne_bot, hZcomm⟩

/-- Determinant-kernel q-core bridge for BG Thm 2.6, q≠p.

From `O_q(G*) ≠ 1`, construct a nontrivial abelian normal q-subgroup of the
ambient group `G` that still lies in `G*`.  This is the formal counterpart of
BG's choice `K = Ω₁(Z(O_q(G*)))`, stopping just before the `Ω₁` refinement. -/
private theorem exists_ambient_normal_commutative_qSubgroup_le_determinantKernel_of_opCore_ne_bot
    {q : ℕ} [Fact q.Prime] {F : Type*} [Field F]
    {G : Type*} [Group G] [Finite G]
    {V : Type*} [AddCommGroup V] [Module F V]
    (ρ : Representation F G V)
    (hcore_ne_bot : OddOrder.Isaacs.Ch01.opCore q (determinantKernelSubgroup ρ) ≠ ⊥) :
    ∃ K : Subgroup G, K.Normal ∧ K ≤ determinantKernelSubgroup ρ ∧
      IsPGroup q K ∧ K ≠ ⊥ ∧ Std.Commutative (· * · : K → K → K) := by
  let Gstar : Subgroup G := determinantKernelSubgroup ρ
  let Ostar : Subgroup Gstar := OddOrder.Isaacs.Ch01.opCore q Gstar
  let Oamb : Subgroup G := Ostar.map Gstar.subtype
  have : Gstar.Normal := by
    dsimp [Gstar]
    exact determinantKernelSubgroup_normal ρ
  have : Ostar.Characteristic := by
    dsimp [Ostar]
    exact OddOrder.Isaacs.Ch01.opCore.characteristic q Gstar
  have hOamb_normal : Oamb.Normal := by
    dsimp [Oamb]
    infer_instance
  have hOamb_p : IsPGroup q Oamb := by
    dsimp [Oamb, Ostar]
    exact (OddOrder.Isaacs.Ch01.opCore_isPGroup q Gstar).map Gstar.subtype
  have hOamb_ne_bot : Oamb ≠ ⊥ := by
    intro hOamb_bot
    apply hcore_ne_bot
    have hmap :
        Ostar.map Gstar.subtype = (⊥ : Subgroup Gstar).map Gstar.subtype := by
      simpa [Oamb] using hOamb_bot
    exact (Subgroup.map_subtype_inj (H := Gstar)).mp hmap
  have hOamb_nontrivial : Nontrivial Oamb :=
    (Subgroup.nontrivial_iff_ne_bot Oamb).mpr hOamb_ne_bot
  have : Nontrivial Oamb := hOamb_nontrivial
  have hcenter_nontrivial : Nontrivial (Subgroup.center Oamb) := by
    have htop_nontrivial : Nontrivial (⊤ : Subgroup Oamb) :=
      (Subgroup.nontrivial_iff_ne_bot (⊤ : Subgroup Oamb)).mpr top_ne_bot
    have h :=
      OddOrder.Isaacs.Ch01.IsPGroup.normal_inf_center_nontrivial
        (P := Oamb) (p := q) (N := (⊤ : Subgroup Oamb))
        hOamb_p htop_nontrivial
    simpa using h
  let K : Subgroup G := (Subgroup.center Oamb).map Oamb.subtype
  have : Oamb.Normal := hOamb_normal
  have : (Subgroup.center Oamb).Characteristic := Subgroup.centerCharacteristic
  have hKnormal : K.Normal := by
    dsimp [K]
    infer_instance
  have hOamb_le_Gstar : Oamb ≤ Gstar := by
    intro x hx
    rcases hx with ⟨xstar, _hxstar, rfl⟩
    exact xstar.2
  have hK_le_Gstar : K ≤ Gstar := by
    intro x hx
    rcases hx with ⟨xO, _hxO_center, rfl⟩
    exact hOamb_le_Gstar xO.2
  have hKp : IsPGroup q K := by
    dsimp [K]
    exact (hOamb_p.to_subgroup (Subgroup.center Oamb)).map Oamb.subtype
  have hK_ne_bot : K ≠ ⊥ := by
    intro hK_bot
    have hcenter_ne_bot : Subgroup.center Oamb ≠ ⊥ :=
      (Subgroup.nontrivial_iff_ne_bot (Subgroup.center Oamb)).mp hcenter_nontrivial
    apply hcenter_ne_bot
    have hmap :
        (Subgroup.center Oamb).map Oamb.subtype =
          (⊥ : Subgroup Oamb).map Oamb.subtype := by
      simpa [K] using hK_bot
    exact (Subgroup.map_subtype_inj (H := Oamb)).mp hmap
  have hKcomm : Std.Commutative (· * · : K → K → K) := by
    constructor
    intro x y
    apply Subtype.ext
    rcases x.property with ⟨xO, hxO_center, hx_eq⟩
    rcases y.property with ⟨yO, _hyO_center, hy_eq⟩
    change (x : G) * (y : G) = (y : G) * (x : G)
    rw [← hx_eq, ← hy_eq]
    simpa using (congr_arg Subtype.val
      (Subgroup.mem_center_iff.mp hxO_center yO)).symm
  exact ⟨K, hKnormal, hK_le_Gstar, hKp, hK_ne_bot, hKcomm⟩

/-- q≠p core branch reduced to constructing complementary rank-one
`K`-submodules.

This is the action-free successor to
`commutative_of_determinantKernel_opCore_ne_bot_of_rankOneLinePair`: the
Maschke/algebraically-closed step only has to provide two complementary
rank-one subrepresentations for the normal abelian `q`-subgroup `K ≤ G*`.
The determinant-kernel uniqueness and odd-order no-swap arguments then make
the ambient group abelian. -/
theorem commutative_of_determinantKernel_opCore_ne_bot_of_rankOneKSubmodules
    {q : ℕ} [Fact q.Prime] {F : Type*} [Field F]
    {G : Type*} [Group G] [Finite G]
    {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]
    (ρ : Representation F G V) (hfaithful : Function.Injective ρ)
    (hodd : Odd (Nat.card G))
    (hcore_ne_bot : OddOrder.Isaacs.Ch01.opCore q (determinantKernelSubgroup ρ) ≠ ⊥)
    (hline : ∀ K : Subgroup G, K.Normal → K ≤ determinantKernelSubgroup ρ →
      IsPGroup q K → K ≠ ⊥ → Std.Commutative (· * · : K → K → K) →
      ∃ W : Subrepresentation (ρ.comp K.subtype),
      ∃ U : Subrepresentation (ρ.comp K.subtype),
        Nonempty (Module.Free F W.toSubmodule) ∧
        Nonempty (Module.Free F U.toSubmodule) ∧
        Nonempty (Module.Finite F W.toSubmodule) ∧
        Nonempty (Module.Finite F U.toSubmodule) ∧
        Nonempty (Module.Free F (V ⧸ W.toSubmodule)) ∧
        Nonempty (Module.Free F (V ⧸ U.toSubmodule)) ∧
        IsCompl W.toSubmodule U.toSubmodule ∧
        Module.finrank F W.toSubmodule = 1 ∧
        Module.finrank F U.toSubmodule = 1 ∧
        Module.finrank F (V ⧸ W.toSubmodule) = 1 ∧
        Module.finrank F (V ⧸ U.toSubmodule) = 1) :
    Std.Commutative (· * · : G → G → G) := by
  rcases exists_ambient_normal_commutative_qSubgroup_le_determinantKernel_of_opCore_ne_bot
      ρ hcore_ne_bot with
    ⟨K, hKnormal, hK_le_Gstar, hKq, hK_ne_bot, hKcomm⟩
  rcases hline K hKnormal hK_le_Gstar hKq hK_ne_bot hKcomm with
    ⟨W, U, hfreeW, hfreeU, hfiniteW, hfiniteU, hfreeQW, hfreeQU,
      hcompl, hdimW, hdimU, hdimQW, hdimQU⟩
  let : Module.Free F W.toSubmodule := hfreeW.some
  let : Module.Free F U.toSubmodule := hfreeU.some
  let : Module.Finite F W.toSubmodule := hfiniteW.some
  let : Module.Finite F U.toSubmodule := hfiniteU.some
  let : Module.Free F (V ⧸ W.toSubmodule) := hfreeQW.some
  let : Module.Free F (V ⧸ U.toSubmodule) := hfreeQU.some
  have : Nontrivial K := (Subgroup.nontrivial_iff_ne_bot K).mpr hK_ne_bot
  obtain ⟨x, hx_ne_one⟩ := exists_ne (1 : K)
  exact commutative_of_determinantKernel_subgroup_rank_one_complement
    ρ hfaithful hodd K hKnormal hK_le_Gstar W U hcompl
    hdimW hdimU hdimQW hdimQU hx_ne_one

/-- Algebraically closed characteristic-away determinant-core endpoint for
BG Thm 2.6(a).

If the characteristic of `F` is not any prime divisor of `|G|`, a nontrivial
`O_q(G*)` supplies an abelian normal q-subgroup `K ≤ G*` whose order is
nonzero in `F`; Maschke then gives the same rank-one data as in the q≠p
branch. -/
private theorem commutative_of_determinantKernel_opCore_ne_bot_of_isAlgClosed_charAway
    {q : ℕ} [Fact q.Prime]
    {F : Type*} [Field F] [IsAlgClosed F]
    {G : Type*} [Group G] [Finite G]
    {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]
    (ρ : Representation F G V) (hfaithful : Function.Injective ρ)
    (hodd : Odd (Nat.card G)) (hdim : Module.finrank F V = 2)
    (hchar : ∀ r : ℕ, r.Prime → r ∣ Nat.card G → ¬ CharP F r)
    (hcore_ne_bot : OddOrder.Isaacs.Ch01.opCore q (determinantKernelSubgroup ρ) ≠ ⊥) :
    Std.Commutative (· * · : G → G → G) :=
  commutative_of_determinantKernel_opCore_ne_bot_of_rankOneKSubmodules
    ρ hfaithful hodd hcore_ne_bot
    (fun K _hKnormal _hKle _hKq _hK_ne_bot hKcomm =>
      letI : NeZero (Nat.card K : F) :=
        neZero_nat_card_cast_of_subgroup_forall_prime_not_char hchar K
      exists_rank_one_KSubmodule_data_of_commutative_of_neZero_card
        ρ hdim K hKcomm)

/-- Algebraically closed q≠p endpoint when the determinant is already trivial.

This is the normalizer form of the q≠p branch: for subgroups lying inside
`G*`, the restricted representation has determinant kernel equal to the whole
group.  A nontrivial `O_q(G)` then supplies the abelian normal `q`-subgroup
needed by the same Maschke line argument. -/
private theorem commutative_of_opCore_ne_bot_of_isAlgClosed_of_determinantKernel_eq_top
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    {F : Type*} [Field F] [CharP F p] [IsAlgClosed F]
    {G : Type*} [Group G] [Finite G]
    {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]
    (ρ : Representation F G V) (hfaithful : Function.Injective ρ)
    (hodd : Odd (Nat.card G)) (hdim : Module.finrank F V = 2)
    (hq_ne_p : q ≠ p)
    (hdet_top : determinantKernelSubgroup ρ = ⊤)
    (hcore_ne_bot : OddOrder.Isaacs.Ch01.opCore q G ≠ ⊥) :
    Std.Commutative (· * · : G → G → G) := by
  have : Finite (Sylow q G) := inferInstance
  rcases exists_nontrivial_normal_commutative_qSubgroup_of_opCore_ne_bot
      (q := q) (G := G) hcore_ne_bot with
    ⟨K, hKnormal, hKq, hK_ne_bot, hKcomm⟩
  have hKle : K ≤ determinantKernelSubgroup ρ := by
    intro x _hx
    rw [hdet_top]
    trivial
  rcases exists_rank_one_KSubmodule_data_of_commutative_isPGroup_ne_char
      (p := p) (q := q) ρ hdim K hKq hq_ne_p hKcomm with
    ⟨W, U, hfreeW, hfreeU, hfiniteW, hfiniteU, hfreeQW, hfreeQU,
      hcompl, hdimW, hdimU, hdimQW, hdimQU⟩
  let : Module.Free F W.toSubmodule := hfreeW.some
  let : Module.Free F U.toSubmodule := hfreeU.some
  let : Module.Finite F W.toSubmodule := hfiniteW.some
  let : Module.Finite F U.toSubmodule := hfiniteU.some
  let : Module.Free F (V ⧸ W.toSubmodule) := hfreeQW.some
  let : Module.Free F (V ⧸ U.toSubmodule) := hfreeQU.some
  have : Nontrivial K := (Subgroup.nontrivial_iff_ne_bot K).mpr hK_ne_bot
  obtain ⟨x, hx_ne_one⟩ := exists_ne (1 : K)
  exact commutative_of_determinantKernel_subgroup_rank_one_complement
    ρ hfaithful hodd K hKnormal hKle W U hcompl
    hdimW hdimU hdimQW hdimQU hx_ne_one

/-- Algebraically closed characteristic-away endpoint when the determinant is
already trivial.

This is the determinant-trivial subgroup form needed by the normalizer branch
of BG Thm 2.6(a): `O_q(G) ≠ 1` supplies the abelian normal q-subgroup, while
the theorem-level `hchar` hypothesis supplies Maschke's `NeZero` premise. -/
private theorem commutative_of_opCore_ne_bot_of_isAlgClosed_charAway_of_determinantKernel_eq_top
    {q : ℕ} [Fact q.Prime]
    {F : Type*} [Field F] [IsAlgClosed F]
    {G : Type*} [Group G] [Finite G]
    {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]
    (ρ : Representation F G V) (hfaithful : Function.Injective ρ)
    (hodd : Odd (Nat.card G)) (hdim : Module.finrank F V = 2)
    (hchar : ∀ r : ℕ, r.Prime → r ∣ Nat.card G → ¬ CharP F r)
    (hdet_top : determinantKernelSubgroup ρ = ⊤)
    (hcore_ne_bot : OddOrder.Isaacs.Ch01.opCore q G ≠ ⊥) :
    Std.Commutative (· * · : G → G → G) := by
  have : Finite (Sylow q G) := inferInstance
  rcases exists_nontrivial_normal_commutative_qSubgroup_of_opCore_ne_bot
      (q := q) (G := G) hcore_ne_bot with
    ⟨K, hKnormal, _hKq, hK_ne_bot, hKcomm⟩
  have hKle : K ≤ determinantKernelSubgroup ρ := by
    intro x _hx
    rw [hdet_top]
    trivial
  have : NeZero (Nat.card K : F) :=
    neZero_nat_card_cast_of_subgroup_forall_prime_not_char hchar K
  rcases exists_rank_one_KSubmodule_data_of_commutative_of_neZero_card
      ρ hdim K hKcomm with
    ⟨W, U, hfreeW, hfreeU, hfiniteW, hfiniteU, hfreeQW, hfreeQU,
      hcompl, hdimW, hdimU, hdimQW, hdimQU⟩
  let : Module.Free F W.toSubmodule := hfreeW.some
  let : Module.Free F U.toSubmodule := hfreeU.some
  let : Module.Finite F W.toSubmodule := hfiniteW.some
  let : Module.Finite F U.toSubmodule := hfiniteU.some
  let : Module.Free F (V ⧸ W.toSubmodule) := hfreeQW.some
  let : Module.Free F (V ⧸ U.toSubmodule) := hfreeQU.some
  have : Nontrivial K := (Subgroup.nontrivial_iff_ne_bot K).mpr hK_ne_bot
  obtain ⟨x, hx_ne_one⟩ := exists_ne (1 : K)
  exact commutative_of_determinantKernel_subgroup_rank_one_complement
    ρ hfaithful hodd K hKnormal hKle W U hcompl
    hdimW hdimU hdimQW hdimQU hx_ne_one

/-- If `Q ∈ Syl_q(G)` is nontrivial, then `O_q(N_G(Q))` is nontrivial.

This isolates the group-theoretic part of BG Thm 2.6 where, after choosing
`q ≠ p` and a Sylow `q`-subgroup `Q ≤ G*`, one sets `H = N_{G*}(Q)` and needs
`O_q(H) ≠ 1`. -/
private theorem opCore_ne_bot_of_sylow_normalizer
    {q : ℕ} [Fact q.Prime] {G : Type*} [Group G] [Finite G] [Finite (Sylow q G)]
    (Q : Sylow q G) (hq_dvd : q ∣ Nat.card G) :
    OddOrder.Isaacs.Ch01.opCore q
      (Subgroup.normalizer (Q : Set G)) ≠ ⊥ := by
  let N : Subgroup G := Subgroup.normalizer (Q : Set G)
  let QN : Sylow q N := Q.subtype Q.le_normalizer
  have : Finite (Sylow q N) := inferInstance
  have : (QN : Subgroup N).Normal := by
    change ((Q : Subgroup G).subgroupOf N).Normal
    exact Subgroup.normal_subgroupOf_of_le_normalizer le_rfl
  have hQ_ne_bot : (Q : Subgroup G) ≠ ⊥ := Q.ne_bot_of_dvd_card hq_dvd
  have hQN_ne_bot : (QN : Subgroup N) ≠ ⊥ := by
    intro hbot
    apply hQ_ne_bot
    have hmap : ((QN : Subgroup N).map N.subtype) = (Q : Subgroup G) := by
      simp only [QN, Sylow.coe_subtype]
      exact Subgroup.map_subgroupOf_eq_of_le Q.le_normalizer
    rw [hbot, Subgroup.map_bot] at hmap
    exact hmap.symm
  exact opCore_ne_bot_of_nontrivial_normal_pSubgroup
    (G := N) (K := (QN : Subgroup N)) QN.2 hQN_ne_bot

/-- q≠p normalizer branch inside the determinant kernel.

For `Q ∈ Syl_q(G*)`, set `H = N_{G*}(Q)`.  Since `H ≤ G*`, the determinant of
the restricted representation on `H` is trivial.  Thus the algebraically
closed q≠p endpoint applies directly to `H` once `O_q(H) ≠ 1`. -/
private theorem determinantKernel_sylow_normalizer_commutative_of_isAlgClosed
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    {F : Type*} [Field F] [CharP F p] [IsAlgClosed F]
    {G : Type*} [Group G] [Finite G]
    {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]
    (ρ : Representation F G V) (hfaithful : Function.Injective ρ)
    (hodd : Odd (Nat.card G)) (hdim : Module.finrank F V = 2)
    (hq_ne_p : q ≠ p)
    (Q : Sylow q (determinantKernelSubgroup ρ))
    (hcore_ne_bot : OddOrder.Isaacs.Ch01.opCore q
      (Subgroup.normalizer ((Q : Subgroup (determinantKernelSubgroup ρ)) :
        Set (determinantKernelSubgroup ρ))) ≠ ⊥) :
    Std.Commutative
      (· * · :
        Subgroup.normalizer ((Q : Subgroup (determinantKernelSubgroup ρ)) :
          Set (determinantKernelSubgroup ρ)) →
        Subgroup.normalizer ((Q : Subgroup (determinantKernelSubgroup ρ)) :
          Set (determinantKernelSubgroup ρ)) →
        Subgroup.normalizer ((Q : Subgroup (determinantKernelSubgroup ρ)) :
          Set (determinantKernelSubgroup ρ))) := by
  let Gstar : Subgroup G := determinantKernelSubgroup ρ
  let H : Subgroup Gstar := Subgroup.normalizer ((Q : Subgroup Gstar) : Set Gstar)
  let ρH : Representation F H V := ρ.comp (Gstar.subtype.comp H.subtype)
  have hfaithfulH : Function.Injective ρH := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact hfaithful (by simpa [ρH] using hxy)
  have hoddH : Odd (Nat.card H) := by
    have hH_dvd_Gstar : Nat.card H ∣ Nat.card Gstar :=
      Subgroup.card_subgroup_dvd_card H
    have hGstar_dvd_G : Nat.card Gstar ∣ Nat.card G :=
      Subgroup.card_subgroup_dvd_card Gstar
    exact hodd.of_dvd_nat (hH_dvd_Gstar.trans hGstar_dvd_G)
  have hdet_top : determinantKernelSubgroup ρH = ⊤ := by
    ext x
    constructor
    · intro _hx
      trivial
    · intro _hx
      rw [mem_determinantKernelSubgroup]
      have hxdetG : (((x : H) : Gstar) : G) ∈ determinantKernelSubgroup ρ :=
        ((x : H) : Gstar).2
      rw [mem_determinantKernelSubgroup] at hxdetG
      simpa [ρH, determinantCharacterOfRepresentation,
        representationToGeneralLinearGroup] using hxdetG
  simpa [H] using
    commutative_of_opCore_ne_bot_of_isAlgClosed_of_determinantKernel_eq_top
      (p := p) (q := q) ρH hfaithfulH hoddH hdim hq_ne_p hdet_top
      hcore_ne_bot

/-- Characteristic-away normalizer branch inside the determinant kernel.

This is the BG Thm 2.6(a) analogue of
`determinantKernel_sylow_normalizer_commutative_of_isAlgClosed`: for
`H = N_{G*}(Q)`, the determinant is trivial on `H`, and the characteristic-away
hypothesis restricts from `G` to `H`. -/
private theorem determinantKernel_sylow_normalizer_commutative_of_isAlgClosed_charAway
    {q : ℕ} [Fact q.Prime]
    {F : Type*} [Field F] [IsAlgClosed F]
    {G : Type*} [Group G] [Finite G]
    {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]
    (ρ : Representation F G V) (hfaithful : Function.Injective ρ)
    (hodd : Odd (Nat.card G)) (hdim : Module.finrank F V = 2)
    (hchar : ∀ r : ℕ, r.Prime → r ∣ Nat.card G → ¬ CharP F r)
    (Q : Sylow q (determinantKernelSubgroup ρ))
    (hcore_ne_bot : OddOrder.Isaacs.Ch01.opCore q
      (Subgroup.normalizer ((Q : Subgroup (determinantKernelSubgroup ρ)) :
        Set (determinantKernelSubgroup ρ))) ≠ ⊥) :
    Std.Commutative
      (· * · :
        Subgroup.normalizer ((Q : Subgroup (determinantKernelSubgroup ρ)) :
          Set (determinantKernelSubgroup ρ)) →
        Subgroup.normalizer ((Q : Subgroup (determinantKernelSubgroup ρ)) :
          Set (determinantKernelSubgroup ρ)) →
        Subgroup.normalizer ((Q : Subgroup (determinantKernelSubgroup ρ)) :
          Set (determinantKernelSubgroup ρ))) := by
  let Gstar : Subgroup G := determinantKernelSubgroup ρ
  let H : Subgroup Gstar := Subgroup.normalizer ((Q : Subgroup Gstar) : Set Gstar)
  let ρH : Representation F H V := ρ.comp (Gstar.subtype.comp H.subtype)
  have hfaithfulH : Function.Injective ρH := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact hfaithful (by simpa [ρH] using hxy)
  have hH_dvd_Gstar : Nat.card H ∣ Nat.card Gstar :=
    Subgroup.card_subgroup_dvd_card H
  have hGstar_dvd_G : Nat.card Gstar ∣ Nat.card G :=
    Subgroup.card_subgroup_dvd_card Gstar
  have hoddH : Odd (Nat.card H) :=
    hodd.of_dvd_nat (hH_dvd_Gstar.trans hGstar_dvd_G)
  have hcharH :
      ∀ r : ℕ, r.Prime → r ∣ Nat.card H → ¬ CharP F r := by
    intro r hr_prime hr_dvd
    exact hchar r hr_prime (hr_dvd.trans (hH_dvd_Gstar.trans hGstar_dvd_G))
  have hdet_top : determinantKernelSubgroup ρH = ⊤ := by
    ext x
    constructor
    · intro _hx
      trivial
    · intro _hx
      rw [mem_determinantKernelSubgroup]
      have hxdetG : (((x : H) : Gstar) : G) ∈ determinantKernelSubgroup ρ :=
        ((x : H) : Gstar).2
      rw [mem_determinantKernelSubgroup] at hxdetG
      simpa [ρH, determinantCharacterOfRepresentation,
        representationToGeneralLinearGroup] using hxdetG
  simpa [H] using
    commutative_of_opCore_ne_bot_of_isAlgClosed_charAway_of_determinantKernel_eq_top
      (q := q) ρH hfaithfulH hoddH hdim hcharH hdet_top hcore_ne_bot

/-- A finite group that is not a `p`-group has a prime divisor different from `p`.

This is the arithmetic half of the `G*` dichotomy in BG Thm 2.6. -/
private theorem exists_prime_ne_dvd_card_of_not_isPGroup
    {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [Finite G]
    (hnot_pgroup : ¬ IsPGroup p G) :
    ∃ q : ℕ, q.Prime ∧ q ≠ p ∧ q ∣ Nat.card G := by
  by_contra hnone
  apply hnot_pgroup
  rw [IsPGroup.iff_card]
  refine ⟨(Nat.card G).primeFactorsList.length,
    Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' ?_⟩
  intro q hq_prime hq_dvd
  by_contra hq_ne_p
  exact hnone ⟨q, hq_prime, hq_ne_p, hq_dvd⟩

/-- If a finite group is not a `p`-group, one can choose `q ≠ p` and
`Q ∈ Syl_q(G)` with nontrivial `O_q(N_G(Q))`.

This packages the first two group-theoretic moves in the `q ≠ p` branch of
BG Thm 2.6 before the Burnside normal-complement/induction step. -/
private theorem exists_prime_ne_sylow_normalizer_opCore_ne_bot_of_not_isPGroup
    {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [Finite G]
    (hnot_pgroup : ¬ IsPGroup p G) :
    ∃ q : ℕ, q.Prime ∧ q ≠ p ∧ q ∣ Nat.card G ∧ ∃ Q : Sylow q G,
      OddOrder.Isaacs.Ch01.opCore q
        (Subgroup.normalizer (Q : Set G)) ≠ ⊥ := by
  rcases exists_prime_ne_dvd_card_of_not_isPGroup (p := p) (G := G) hnot_pgroup with
    ⟨q, hq_prime, hq_ne_p, hq_dvd⟩
  have : Fact q.Prime := ⟨hq_prime⟩
  have : Finite (Sylow q G) := inferInstance
  obtain ⟨Q⟩ := Sylow.nonempty (p := q) (G := G)
  exact ⟨q, hq_prime, hq_ne_p, hq_dvd, Q,
    opCore_ne_bot_of_sylow_normalizer Q hq_dvd⟩

/-- Burnside bridge for BG Thm 2.6: an abelian Sylow normalizer gives a normal
`p`-complement.

BG phrases the step as "`H = N_G(Q)` is abelian, so by Burnside ..."; Ch.5's
formal entry point expects `N_G(Q) ≤ C_G(Q)`. -/
private theorem hasNormalPComplement_of_sylow_normalizer_commutative
    {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [Finite G]
    (Q : Sylow p G)
    (hN_comm : Std.Commutative
      (· * · : Subgroup.normalizer (Q : Set G) →
        Subgroup.normalizer (Q : Set G) →
        Subgroup.normalizer (Q : Set G))) :
    OddOrder.Isaacs.Ch05.HasNormalPComplement p G := by
  refine OddOrder.Isaacs.Ch05.hasNormalPComplement_of_sylow_normalizer_le_centralizer
    Q ?_
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  exact (congr_arg Subtype.val
    (hN_comm.comm ⟨x, hx⟩ ⟨y, Q.le_normalizer hy⟩)).symm

/-- Burnside normal-complement branch for BG Thm 2.6.

If `G` has a normal `p`-complement and `p ∣ |G|`, then either the complement is
trivial, giving `O_p(G) ≠ 1`, or the induction result on the nontrivial normal
complement lifts back to `G`.  The hypothesis `hind` is exactly the induction
output used in the text for `N ≠ 1`. -/
private theorem exists_prime_opCore_ne_bot_of_hasNormalPComplement_induction
    {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [Finite G] [Finite (Sylow p G)]
    (hp_dvd : p ∣ Nat.card G)
    (hcomp : OddOrder.Isaacs.Ch05.HasNormalPComplement p G)
    (hind : ∀ N : Subgroup G, N.Normal → N ≠ ⊥ → N ≠ ⊤ →
      ∃ r : ℕ, r.Prime ∧ OddOrder.Isaacs.Ch01.opCore r N ≠ ⊥) :
    ∃ r : ℕ, r.Prime ∧ OddOrder.Isaacs.Ch01.opCore r G ≠ ⊥ := by
  rcases hcomp with ⟨N, hNnormal, hNcompl⟩
  by_cases hN_bot : N = ⊥
  · obtain ⟨P⟩ := Sylow.nonempty (p := p) (G := G)
    have hPtop : (P : Subgroup G) = ⊤ := by
      simpa [hN_bot] using hNcompl P
    have : (P : Subgroup G).Normal := by
      rw [hPtop]
      infer_instance
    exact ⟨p, Fact.out,
      opCore_ne_bot_of_nontrivial_normal_pSubgroup
        (G := G) (K := (P : Subgroup G)) P.2
        (P.ne_bot_of_dvd_card hp_dvd)⟩
  · have : N.Normal := hNnormal
    have hN_ne_top : N ≠ ⊤ := by
      intro hN_top
      obtain ⟨P⟩ := Sylow.nonempty (p := p) (G := G)
      have hP_ne_bot : (P : Subgroup G) ≠ ⊥ := P.ne_bot_of_dvd_card hp_dvd
      apply hP_ne_bot
      refine le_bot_iff.mp ?_
      have hP_le_N : (P : Subgroup G) ≤ N := by
        rw [hN_top]
        exact le_top
      have hP_le_inf : (P : Subgroup G) ≤ N ⊓ (P : Subgroup G) :=
        le_inf hP_le_N le_rfl
      simpa [(hNcompl P).isCompl.inf_eq_bot] using hP_le_inf
    rcases hind N hNnormal hN_bot hN_ne_top with ⟨r, hr_prime, hNcore_ne_bot⟩
    have : Fact r.Prime := ⟨hr_prime⟩
    have : Finite (Sylow r G) := inferInstance
    exact ⟨r, hr_prime,
      opCore_ne_bot_of_normal_subgroup_opCore_ne_bot
        (p := r) (G := G) N hNcore_ne_bot⟩

/-- BG Thm 2.6 step 5 as a group-theoretic spine.

When `G` is not a `p`-group, choose `q ≠ p` and `Q ∈ Syl_q(G)`, use the
previous `O_q(N_G(Q)) ≠ 1` branch to make `N_G(Q)` abelian, apply Burnside, and
then return the normal-complement induction output to `G`. -/
private theorem exists_prime_opCore_ne_bot_of_not_isPGroup_via_normalizers
    {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [Finite G]
    (hnot_pgroup : ¬ IsPGroup p G)
    (hnormalizer : ∀ {q : ℕ} [Fact q.Prime], q ≠ p → (Q : Sylow q G) →
      OddOrder.Isaacs.Ch01.opCore q
        (Subgroup.normalizer (Q : Set G)) ≠ ⊥ →
      Std.Commutative
        (· * · : Subgroup.normalizer (Q : Set G) →
          Subgroup.normalizer (Q : Set G) →
          Subgroup.normalizer (Q : Set G)))
    (hind : ∀ N : Subgroup G, N.Normal → N ≠ ⊥ → N ≠ ⊤ →
      ∃ r : ℕ, r.Prime ∧ OddOrder.Isaacs.Ch01.opCore r N ≠ ⊥) :
    ∃ r : ℕ, r.Prime ∧ OddOrder.Isaacs.Ch01.opCore r G ≠ ⊥ := by
  rcases exists_prime_ne_sylow_normalizer_opCore_ne_bot_of_not_isPGroup
      (p := p) (G := G) hnot_pgroup with
    ⟨q, hq_prime, hq_ne_p, hq_dvd, Q, hQcore_ne_bot⟩
  have : Fact q.Prime := ⟨hq_prime⟩
  have : Finite (Sylow q G) := inferInstance
  have hcomp : OddOrder.Isaacs.Ch05.HasNormalPComplement q G :=
    hasNormalPComplement_of_sylow_normalizer_commutative
      Q (hnormalizer hq_ne_p Q hQcore_ne_bot)
  exact exists_prime_opCore_ne_bot_of_hasNormalPComplement_induction
    (p := q) (G := G) hq_dvd hcomp hind

/-- BG Thm 2.6 step 5 specialized to the determinant kernel `G*`.

If `G*` is nontrivial, then either it is a `p`-group, giving
`O_p(G*) ≠ 1`, or the non-`p`-group normalizer spine supplies a prime `r` with
`O_r(G*) ≠ 1`.  The two hypotheses are precisely the remaining theorem-level
inputs from the text: the q≠p linear-algebra normalizer step and the induction
output on normal complements. -/
private theorem exists_prime_opCore_ne_bot_of_determinantKernel_ne_bot
    {p : ℕ} [Fact p.Prime] {F : Type*} [Field F]
    {G : Type*} [Group G] [Finite G]
    {V : Type*} [AddCommGroup V] [Module F V]
    (ρ : Representation F G V)
    (hdet_ne_bot : determinantKernelSubgroup ρ ≠ ⊥)
    (hnormalizer : ∀ {q : ℕ} [Fact q.Prime], q ≠ p →
      (Q : Sylow q (determinantKernelSubgroup ρ)) →
      OddOrder.Isaacs.Ch01.opCore q
        (Subgroup.normalizer ((Q : Subgroup (determinantKernelSubgroup ρ)) :
          Set (determinantKernelSubgroup ρ))) ≠ ⊥ →
      Std.Commutative
        (· * · :
          Subgroup.normalizer ((Q : Subgroup (determinantKernelSubgroup ρ)) :
            Set (determinantKernelSubgroup ρ)) →
          Subgroup.normalizer ((Q : Subgroup (determinantKernelSubgroup ρ)) :
            Set (determinantKernelSubgroup ρ)) →
          Subgroup.normalizer ((Q : Subgroup (determinantKernelSubgroup ρ)) :
            Set (determinantKernelSubgroup ρ))))
    (hind : ∀ N : Subgroup (determinantKernelSubgroup ρ), N.Normal → N ≠ ⊥ → N ≠ ⊤ →
      ∃ r : ℕ, r.Prime ∧ OddOrder.Isaacs.Ch01.opCore r N ≠ ⊥) :
    ∃ r : ℕ, r.Prime ∧
      OddOrder.Isaacs.Ch01.opCore r (determinantKernelSubgroup ρ) ≠ ⊥ := by
  let Gstar : Subgroup G := determinantKernelSubgroup ρ
  have hGstar_ne_bot : Gstar ≠ ⊥ := by
    simpa [Gstar] using hdet_ne_bot
  by_cases hGstar_p : IsPGroup p Gstar
  · have : Finite (Sylow p Gstar) := inferInstance
    have : Nontrivial Gstar :=
      (Subgroup.nontrivial_iff_ne_bot Gstar).mpr hGstar_ne_bot
    exact ⟨p, Fact.out,
      opCore_ne_bot_of_nontrivial_normal_pSubgroup
        (G := Gstar) (K := (⊤ : Subgroup Gstar))
        (hGstar_p.to_subgroup ⊤) top_ne_bot⟩
  · exact exists_prime_opCore_ne_bot_of_not_isPGroup_via_normalizers
      (p := p) (G := Gstar) hGstar_p
      (fun {q} hq_prime hq_ne_p Q hQcore =>
        hnormalizer (q := q) hq_ne_p Q hQcore)
      hind

/-- Characteristic-away determinant-kernel core spine.

This is the BG Thm 2.6(a) version of
`exists_prime_opCore_ne_bot_of_determinantKernel_ne_bot`: since there is no
distinguished field characteristic prime, we choose any prime divisor of
`|G*|` and reuse the p-parametrized normalizer spine. -/
private theorem exists_prime_opCore_ne_bot_of_determinantKernel_ne_bot_charAway
    {F : Type*} [Field F]
    {G : Type*} [Group G] [Finite G]
    {V : Type*} [AddCommGroup V] [Module F V]
    (ρ : Representation F G V)
    (hdet_ne_bot : determinantKernelSubgroup ρ ≠ ⊥)
    (hnormalizer : ∀ {q : ℕ} [Fact q.Prime],
      (Q : Sylow q (determinantKernelSubgroup ρ)) →
      OddOrder.Isaacs.Ch01.opCore q
        (Subgroup.normalizer ((Q : Subgroup (determinantKernelSubgroup ρ)) :
          Set (determinantKernelSubgroup ρ))) ≠ ⊥ →
      Std.Commutative
        (· * · :
          Subgroup.normalizer ((Q : Subgroup (determinantKernelSubgroup ρ)) :
            Set (determinantKernelSubgroup ρ)) →
          Subgroup.normalizer ((Q : Subgroup (determinantKernelSubgroup ρ)) :
            Set (determinantKernelSubgroup ρ)) →
          Subgroup.normalizer ((Q : Subgroup (determinantKernelSubgroup ρ)) :
            Set (determinantKernelSubgroup ρ))))
    (hind : ∀ N : Subgroup (determinantKernelSubgroup ρ), N.Normal → N ≠ ⊥ → N ≠ ⊤ →
      ∃ r : ℕ, r.Prime ∧ OddOrder.Isaacs.Ch01.opCore r N ≠ ⊥) :
    ∃ r : ℕ, r.Prime ∧
      OddOrder.Isaacs.Ch01.opCore r (determinantKernelSubgroup ρ) ≠ ⊥ := by
  let Gstar : Subgroup G := determinantKernelSubgroup ρ
  have hGstar_ne_bot : Gstar ≠ ⊥ := by
    simpa [Gstar] using hdet_ne_bot
  have : Nontrivial Gstar :=
    (Subgroup.nontrivial_iff_ne_bot Gstar).mpr hGstar_ne_bot
  obtain ⟨p, hp_prime, _hp_dvd⟩ :=
    Nat.exists_prime_and_dvd (Finite.one_lt_card (α := Gstar)).ne'
  have : Fact p.Prime := ⟨hp_prime⟩
  exact exists_prime_opCore_ne_bot_of_determinantKernel_ne_bot
    (p := p) ρ hdet_ne_bot
    (fun {q} _hq_prime _hq_ne_p Q hQcore =>
      hnormalizer (q := q) Q hQcore)
    hind

/-- q = p endpoint when `O_p(G*)` is nontrivial.

Here `G* = ker(det ∘ ρ)`.  The Ch.1 `opCore` is characteristic in `G*`; since
`G* ⊴ G`, its image in `G` is a nontrivial normal p-subgroup and can be fed to
the fixed-space reduction. -/
private theorem sylow_commutative_and_commutator_le_of_determinantKernel_opCore_ne_bot
    {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [CharP F p]
    {G : Type*} [Group G] [Finite G] [Finite (Sylow p G)]
    {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]
    (ρ : Representation F G V) (hfaithful : Function.Injective ρ)
    (hdim : Module.finrank F V = 2)
    (hop_ne_bot : OddOrder.Isaacs.Ch01.opCore p (determinantKernelSubgroup ρ) ≠ ⊥)
    (P : Sylow p G) :
    Std.Commutative (· * · : P → P → P) ∧
      commutator G ≤ (P : Subgroup G) := by
  let Gstar : Subgroup G := determinantKernelSubgroup ρ
  have : Gstar.Normal := by
    dsimp [Gstar]
    exact determinantKernelSubgroup_normal ρ
  have hGcore_ne_bot : OddOrder.Isaacs.Ch01.opCore p G ≠ ⊥ :=
    opCore_ne_bot_of_normal_subgroup_opCore_ne_bot
      (p := p) (G := G) Gstar hop_ne_bot
  exact sylow_commutative_and_commutator_le_of_exists_nontrivial_normal_pSubgroup
    ρ hfaithful hdim
    ⟨OddOrder.Isaacs.Ch01.opCore p G, inferInstance,
      OddOrder.Isaacs.Ch01.opCore_isPGroup p G, hGcore_ne_bot⟩ P

/-- Determinant-kernel core dispatch for the Sylow conclusion of BG Thm 2.6(b).

Once the group-theoretic spine has produced a nontrivial prime core in `G*`,
the `r = p` branch feeds the fixed-space endpoint.  The only remaining
theorem-specific input for `r ≠ p` is the linear-algebra branch from the text:
a nontrivial `q`-core in `G*`, with `q ≠ p`, makes the ambient group abelian. -/
private theorem sylow_commutative_and_commutator_le_of_determinantKernel_core_spine
    {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [CharP F p]
    {G : Type*} [Group G] [Finite G] [Finite (Sylow p G)]
    {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]
    (ρ : Representation F G V) (hfaithful : Function.Injective ρ)
    (hdim : Module.finrank F V = 2)
    (hdet_ne_bot : determinantKernelSubgroup ρ ≠ ⊥)
    (hnormalizer : ∀ {q : ℕ} [Fact q.Prime], q ≠ p →
      (Q : Sylow q (determinantKernelSubgroup ρ)) →
      OddOrder.Isaacs.Ch01.opCore q
        (Subgroup.normalizer ((Q : Subgroup (determinantKernelSubgroup ρ)) :
          Set (determinantKernelSubgroup ρ))) ≠ ⊥ →
      Std.Commutative
        (· * · :
          Subgroup.normalizer ((Q : Subgroup (determinantKernelSubgroup ρ)) :
            Set (determinantKernelSubgroup ρ)) →
          Subgroup.normalizer ((Q : Subgroup (determinantKernelSubgroup ρ)) :
            Set (determinantKernelSubgroup ρ)) →
          Subgroup.normalizer ((Q : Subgroup (determinantKernelSubgroup ρ)) :
            Set (determinantKernelSubgroup ρ))))
    (hind : ∀ N : Subgroup (determinantKernelSubgroup ρ), N.Normal → N ≠ ⊥ → N ≠ ⊤ →
      ∃ r : ℕ, r.Prime ∧ OddOrder.Isaacs.Ch01.opCore r N ≠ ⊥)
    (hcore_ne_p_comm : ∀ {q : ℕ} [Fact q.Prime], q ≠ p →
      OddOrder.Isaacs.Ch01.opCore q (determinantKernelSubgroup ρ) ≠ ⊥ →
      Std.Commutative (· * · : G → G → G))
    (P : Sylow p G) :
    Std.Commutative (· * · : P → P → P) ∧
      commutator G ≤ (P : Subgroup G) := by
  rcases exists_prime_opCore_ne_bot_of_determinantKernel_ne_bot
      (p := p) ρ hdet_ne_bot hnormalizer hind with
    ⟨r, hr_prime, hcore_ne_bot⟩
  by_cases hr_eq_p : r = p
  · subst r
    exact sylow_commutative_and_commutator_le_of_determinantKernel_opCore_ne_bot
      ρ hfaithful hdim hcore_ne_bot P
  · have : Fact r.Prime := ⟨hr_prime⟩
    exact sylow_commutative_and_commutator_le_of_commutative
      (hcore_ne_p_comm (q := r) hr_eq_p hcore_ne_bot) P

/-- Theorem-facing determinant-kernel reduction using `K`-submodule data.

This is the successor of
`sylow_commutative_and_commutator_le_of_determinantKernel_spine_rankOneLinePair`
after the q≠p branch has been moved below the permutation-action interface:
the only remaining linear-algebra input is the pair of complementary rank-one
`K`-submodules for every nontrivial `q`-core in `G*`. -/
private theorem
    sylow_commutative_and_commutator_le_of_determinantKernel_spine_rankOneKSubmodules
    {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [CharP F p]
    {G : Type*} [Group G] [Finite G] [Finite (Sylow p G)]
    {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]
    (ρ : Representation F G V) (hfaithful : Function.Injective ρ)
    (hodd : Odd (Nat.card G)) (hdim : Module.finrank F V = 2)
    (hnormalizer : ∀ {q : ℕ} [Fact q.Prime], q ≠ p →
      (Q : Sylow q (determinantKernelSubgroup ρ)) →
      OddOrder.Isaacs.Ch01.opCore q
        (Subgroup.normalizer ((Q : Subgroup (determinantKernelSubgroup ρ)) :
          Set (determinantKernelSubgroup ρ))) ≠ ⊥ →
      Std.Commutative
        (· * · :
          Subgroup.normalizer ((Q : Subgroup (determinantKernelSubgroup ρ)) :
            Set (determinantKernelSubgroup ρ)) →
          Subgroup.normalizer ((Q : Subgroup (determinantKernelSubgroup ρ)) :
            Set (determinantKernelSubgroup ρ)) →
          Subgroup.normalizer ((Q : Subgroup (determinantKernelSubgroup ρ)) :
            Set (determinantKernelSubgroup ρ))))
    (hind : ∀ N : Subgroup (determinantKernelSubgroup ρ), N.Normal → N ≠ ⊥ → N ≠ ⊤ →
      ∃ r : ℕ, r.Prime ∧ OddOrder.Isaacs.Ch01.opCore r N ≠ ⊥)
    (hline : ∀ {q : ℕ} [Fact q.Prime], q ≠ p →
      ∀ K : Subgroup G, K.Normal → K ≤ determinantKernelSubgroup ρ →
        IsPGroup q K → K ≠ ⊥ → Std.Commutative (· * · : K → K → K) →
        ∃ W : Subrepresentation (ρ.comp K.subtype),
        ∃ U : Subrepresentation (ρ.comp K.subtype),
          Nonempty (Module.Free F W.toSubmodule) ∧
          Nonempty (Module.Free F U.toSubmodule) ∧
          Nonempty (Module.Finite F W.toSubmodule) ∧
          Nonempty (Module.Finite F U.toSubmodule) ∧
          Nonempty (Module.Free F (V ⧸ W.toSubmodule)) ∧
          Nonempty (Module.Free F (V ⧸ U.toSubmodule)) ∧
          IsCompl W.toSubmodule U.toSubmodule ∧
          Module.finrank F W.toSubmodule = 1 ∧
          Module.finrank F U.toSubmodule = 1 ∧
          Module.finrank F (V ⧸ W.toSubmodule) = 1 ∧
          Module.finrank F (V ⧸ U.toSubmodule) = 1)
    (P : Sylow p G) :
    Std.Commutative (· * · : P → P → P) ∧
      commutator G ≤ (P : Subgroup G) := by
  by_cases hdet_bot : determinantKernelSubgroup ρ = ⊥
  · exact sylow_commutative_and_commutator_le_of_determinantKernel_eq_bot
      ρ hdet_bot P
  · exact sylow_commutative_and_commutator_le_of_determinantKernel_core_spine
      ρ hfaithful hdim hdet_bot hnormalizer hind
      (fun {q} _hq_prime hq_ne_p hcore_ne_bot =>
        commutative_of_determinantKernel_opCore_ne_bot_of_rankOneKSubmodules
          ρ hfaithful hodd hcore_ne_bot (hline (q := q) hq_ne_p))
      P

/-- Algebraically closed determinant-kernel spine for BG Thm 2.6(b).

Over an algebraically closed field, the q≠p Maschke branch supplies the
rank-one `K`-submodule input directly.  What remains outside this bridge is
the group-theoretic normalizer/induction spine inside `G*`. -/
private theorem
    sylow_commutative_and_commutator_le_of_determinantKernel_spine_isAlgClosed
    {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [CharP F p] [IsAlgClosed F]
    {G : Type*} [Group G] [Finite G] [Finite (Sylow p G)]
    {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]
    (ρ : Representation F G V) (hfaithful : Function.Injective ρ)
    (hodd : Odd (Nat.card G)) (hdim : Module.finrank F V = 2)
    (hnormalizer : ∀ {q : ℕ} [Fact q.Prime], q ≠ p →
      (Q : Sylow q (determinantKernelSubgroup ρ)) →
      OddOrder.Isaacs.Ch01.opCore q
        (Subgroup.normalizer ((Q : Subgroup (determinantKernelSubgroup ρ)) :
          Set (determinantKernelSubgroup ρ))) ≠ ⊥ →
      Std.Commutative
        (· * · :
          Subgroup.normalizer ((Q : Subgroup (determinantKernelSubgroup ρ)) :
            Set (determinantKernelSubgroup ρ)) →
          Subgroup.normalizer ((Q : Subgroup (determinantKernelSubgroup ρ)) :
            Set (determinantKernelSubgroup ρ)) →
          Subgroup.normalizer ((Q : Subgroup (determinantKernelSubgroup ρ)) :
            Set (determinantKernelSubgroup ρ))))
    (hind : ∀ N : Subgroup (determinantKernelSubgroup ρ), N.Normal → N ≠ ⊥ → N ≠ ⊤ →
      ∃ r : ℕ, r.Prime ∧ OddOrder.Isaacs.Ch01.opCore r N ≠ ⊥)
    (P : Sylow p G) :
    Std.Commutative (· * · : P → P → P) ∧
      commutator G ≤ (P : Subgroup G) :=
  sylow_commutative_and_commutator_le_of_determinantKernel_spine_rankOneKSubmodules
    ρ hfaithful hodd hdim hnormalizer hind
    (fun {q} _hq_prime hq_ne_p K _hKnormal _hKle hKq _hK_ne_bot hKcomm =>
      exists_rank_one_KSubmodule_data_of_commutative_isPGroup_ne_char
        (p := p) (q := q) ρ hdim K hKq hq_ne_p hKcomm)
    P

/-- Algebraically closed determinant-kernel spine with the normalizer branch closed.

The q≠p normalizer step is now supplied by restricting the representation to
`H = N_{G*}(Q)`, where the determinant is trivial because `H ≤ G*`.  The only
remaining theorem-level input in this algebraically closed reduction is the
induction output on nontrivial normal subgroups of `G*`. -/
private theorem
    sylow_commutative_and_commutator_le_of_determinantKernel_spine_isAlgClosed_induction
    {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [CharP F p] [IsAlgClosed F]
    {G : Type*} [Group G] [Finite G] [Finite (Sylow p G)]
    {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]
    (ρ : Representation F G V) (hfaithful : Function.Injective ρ)
    (hodd : Odd (Nat.card G)) (hdim : Module.finrank F V = 2)
    (hind : ∀ N : Subgroup (determinantKernelSubgroup ρ), N.Normal → N ≠ ⊥ → N ≠ ⊤ →
      ∃ r : ℕ, r.Prime ∧ OddOrder.Isaacs.Ch01.opCore r N ≠ ⊥)
    (P : Sylow p G) :
    Std.Commutative (· * · : P → P → P) ∧
      commutator G ≤ (P : Subgroup G) :=
  sylow_commutative_and_commutator_le_of_determinantKernel_spine_isAlgClosed
    ρ hfaithful hodd hdim
    (fun {q} _hq_prime hq_ne_p Q hQcore =>
      determinantKernel_sylow_normalizer_commutative_of_isAlgClosed
        (q := q) ρ hfaithful hodd hdim hq_ne_p Q hQcore)
    hind P

/-- Scalar extension preserves the determinant kernel.

This is the determinant compatibility needed to move the BG Thm 2.6(b) spine to
an algebraic closure: the base-changed determinant is the algebra-map image of
the original determinant, and field extensions have injective algebra maps. -/
private theorem determinantKernelSubgroup_baseChangeRepresentation
    {F : Type*} [Field F] (K : Type*) [Field K] [Algebra F K]
    {G : Type*} [Group G]
    {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]
    (ρ : Representation F G V) :
    determinantKernelSubgroup (baseChangeRepresentation K ρ) =
      determinantKernelSubgroup ρ := by
  ext g
  rw [mem_determinantKernelSubgroup, mem_determinantKernelSubgroup]
  constructor
  · intro hg
    apply Units.ext
    apply (algebraMap F K).injective
    have hdetF :
        ((determinantCharacterOfRepresentation ρ g : F) =
          LinearMap.det (ρ g)) := by
      simp [determinantCharacterOfRepresentation, representationToGeneralLinearGroup]
    have hdetK :
        ((determinantCharacterOfRepresentation (baseChangeRepresentation K ρ) g : K) =
          LinearMap.det ((baseChangeRepresentation K ρ) g)) := by
      simp [determinantCharacterOfRepresentation, representationToGeneralLinearGroup]
    have hgK :
        ((determinantCharacterOfRepresentation (baseChangeRepresentation K ρ) g : K) =
          1) := by
      simpa using congrArg Units.val hg
    calc
      algebraMap F K ((determinantCharacterOfRepresentation ρ g : F))
          = algebraMap F K (LinearMap.det (ρ g)) := by rw [hdetF]
      _ = LinearMap.det ((ρ g).baseChange K) := by rw [LinearMap.det_baseChange]
      _ = LinearMap.det ((baseChangeRepresentation K ρ) g) := rfl
      _ = (determinantCharacterOfRepresentation (baseChangeRepresentation K ρ) g : K) :=
        hdetK.symm
      _ = 1 := hgK
      _ = algebraMap F K (1 : F) := by simp
  · intro hg
    apply Units.ext
    have hdetF :
        ((determinantCharacterOfRepresentation ρ g : F) =
          LinearMap.det (ρ g)) := by
      simp [determinantCharacterOfRepresentation, representationToGeneralLinearGroup]
    have hdetK :
        ((determinantCharacterOfRepresentation (baseChangeRepresentation K ρ) g : K) =
          LinearMap.det ((baseChangeRepresentation K ρ) g)) := by
      simp [determinantCharacterOfRepresentation, representationToGeneralLinearGroup]
    have hgF : ((determinantCharacterOfRepresentation ρ g : F) = 1) := by
      simpa using congrArg Units.val hg
    calc
      (determinantCharacterOfRepresentation (baseChangeRepresentation K ρ) g : K)
          = LinearMap.det ((baseChangeRepresentation K ρ) g) := hdetK
      _ = LinearMap.det ((ρ g).baseChange K) := rfl
      _ = algebraMap F K (LinearMap.det (ρ g)) := by rw [LinearMap.det_baseChange]
      _ = algebraMap F K ((determinantCharacterOfRepresentation ρ g : F)) := by rw [hdetF]
      _ = 1 := by simp [hgF]

/-- A prime characteristic on the algebraic closure descends to the base field. -/
private theorem not_charP_algebraicClosure_of_not_charP
    {F : Type*} [Field F] {q : ℕ} (hchar : ¬ CharP F q) :
    ¬ CharP (AlgebraicClosure F) q := by
  intro hq
  exact hchar ((Algebra.charP_iff F (AlgebraicClosure F) q).mpr hq)

/-- The BG Thm 2.6(a) characteristic-away hypothesis survives algebraic closure. -/
private theorem charAway_algebraicClosure
    {F : Type*} [Field F] {G : Type*} [Group G] [Finite G]
    (hchar : ∀ q : ℕ, q.Prime → q ∣ Nat.card G → ¬ CharP F q) :
    ∀ q : ℕ, q.Prime → q ∣ Nat.card G → ¬ CharP (AlgebraicClosure F) q :=
  fun q hq_prime hq_dvd =>
    not_charP_algebraicClosure_of_not_charP (hchar q hq_prime hq_dvd)

/-- Algebraic-closure reduction for the characteristic-away determinant-core
endpoint.

This transports BG Thm 2.6(a)'s linear-algebra branch to `AlgebraicClosure F`
while keeping the determinant kernel, hence the nontrivial `O_q(G*)`, unchanged. -/
private theorem commutative_of_determinantKernel_opCore_ne_bot_of_algebraicClosure_charAway
    {q : ℕ} [Fact q.Prime]
    {F : Type*} [Field F]
    {G : Type*} [Group G] [Finite G]
    {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]
    (ρ : Representation F G V) (hfaithful : Function.Injective ρ)
    (hodd : Odd (Nat.card G)) (hdim : Module.finrank F V = 2)
    (hchar : ∀ r : ℕ, r.Prime → r ∣ Nat.card G → ¬ CharP F r)
    (hcore_ne_bot : OddOrder.Isaacs.Ch01.opCore q (determinantKernelSubgroup ρ) ≠ ⊥) :
    Std.Commutative (· * · : G → G → G) := by
  let ρK : Representation (AlgebraicClosure F) G
      (TensorProduct F (AlgebraicClosure F) V) :=
    baseChangeRepresentation (AlgebraicClosure F) ρ
  have hfaithfulK : Function.Injective ρK := by
    simpa [ρK] using
      baseChangeRepresentation_faithful (AlgebraicClosure F) ρ hfaithful
  have hdimK :
      Module.finrank (AlgebraicClosure F)
        (TensorProduct F (AlgebraicClosure F) V) = 2 := by
    exact
      (Module.finrank_baseChange (R := AlgebraicClosure F) (S := F) (M' := V)).trans hdim
  have hcoreK :
      OddOrder.Isaacs.Ch01.opCore q (determinantKernelSubgroup ρK) ≠ ⊥ := by
    change
      OddOrder.Isaacs.Ch01.opCore q
          (determinantKernelSubgroup (baseChangeRepresentation (AlgebraicClosure F) ρ)) ≠
        ⊥
    rw [determinantKernelSubgroup_baseChangeRepresentation (AlgebraicClosure F) ρ]
    exact hcore_ne_bot
  exact
    commutative_of_determinantKernel_opCore_ne_bot_of_isAlgClosed_charAway
      ρK hfaithfulK hodd hdimK (charAway_algebraicClosure hchar) hcoreK

/-- Characteristic-away dispatch once the determinant-kernel core spine has
produced a nontrivial prime core.

The resulting `O_r(G*) ≠ 1` is sent to the algebraic-closure Maschke endpoint,
which returns commutativity of the original group. -/
private theorem commutative_of_determinantKernel_core_spine_charAway
    {F : Type*} [Field F]
    {G : Type*} [Group G] [Finite G]
    {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]
    (ρ : Representation F G V) (hfaithful : Function.Injective ρ)
    (hodd : Odd (Nat.card G)) (hdim : Module.finrank F V = 2)
    (hchar : ∀ r : ℕ, r.Prime → r ∣ Nat.card G → ¬ CharP F r)
    (hdet_ne_bot : determinantKernelSubgroup ρ ≠ ⊥)
    (hnormalizer : ∀ {q : ℕ} [Fact q.Prime],
      (Q : Sylow q (determinantKernelSubgroup ρ)) →
      OddOrder.Isaacs.Ch01.opCore q
        (Subgroup.normalizer ((Q : Subgroup (determinantKernelSubgroup ρ)) :
          Set (determinantKernelSubgroup ρ))) ≠ ⊥ →
      Std.Commutative
        (· * · :
          Subgroup.normalizer ((Q : Subgroup (determinantKernelSubgroup ρ)) :
            Set (determinantKernelSubgroup ρ)) →
          Subgroup.normalizer ((Q : Subgroup (determinantKernelSubgroup ρ)) :
            Set (determinantKernelSubgroup ρ)) →
          Subgroup.normalizer ((Q : Subgroup (determinantKernelSubgroup ρ)) :
            Set (determinantKernelSubgroup ρ))))
    (hind : ∀ N : Subgroup (determinantKernelSubgroup ρ), N.Normal → N ≠ ⊥ → N ≠ ⊤ →
      ∃ r : ℕ, r.Prime ∧ OddOrder.Isaacs.Ch01.opCore r N ≠ ⊥) :
    Std.Commutative (· * · : G → G → G) := by
  rcases exists_prime_opCore_ne_bot_of_determinantKernel_ne_bot_charAway
      ρ hdet_ne_bot hnormalizer hind with
    ⟨r, hr_prime, hcore_ne_bot⟩
  have : Fact r.Prime := ⟨hr_prime⟩
  exact commutative_of_determinantKernel_opCore_ne_bot_of_algebraicClosure_charAway
    ρ hfaithful hodd hdim hchar hcore_ne_bot

/-- Algebraically closed characteristic-away determinant-kernel spine with the
normalizer branch closed.

The normalizer step is supplied by restricting the representation to
`N_{G*}(Q)`, where the determinant is trivial.  The remaining input is only the
proper-normal-subgroup induction output inside `G*`. -/
private theorem commutative_of_determinantKernel_core_spine_isAlgClosed_charAway
    {F : Type*} [Field F] [IsAlgClosed F]
    {G : Type*} [Group G] [Finite G]
    {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]
    (ρ : Representation F G V) (hfaithful : Function.Injective ρ)
    (hodd : Odd (Nat.card G)) (hdim : Module.finrank F V = 2)
    (hchar : ∀ r : ℕ, r.Prime → r ∣ Nat.card G → ¬ CharP F r)
    (hdet_ne_bot : determinantKernelSubgroup ρ ≠ ⊥)
    (hind : ∀ N : Subgroup (determinantKernelSubgroup ρ), N.Normal → N ≠ ⊥ → N ≠ ⊤ →
      ∃ r : ℕ, r.Prime ∧ OddOrder.Isaacs.Ch01.opCore r N ≠ ⊥) :
    Std.Commutative (· * · : G → G → G) :=
  commutative_of_determinantKernel_core_spine_charAway
    ρ hfaithful hodd hdim hchar hdet_ne_bot
    (fun {q} _hq_prime Q hQcore =>
      determinantKernel_sylow_normalizer_commutative_of_isAlgClosed_charAway
        (q := q) ρ hfaithful hodd hdim hchar Q hQcore)
    hind

/-- Algebraic-closure reduction for the characteristic-away determinant-kernel
spine, with the induction hypothesis stated on the original determinant kernel.

This is the theorem-facing bridge for BG Thm 2.6(a): scalar extension preserves
faithfulness, dimension, and the determinant kernel, so the algebraically closed
normalizer branch can be used without changing the group-theoretic spine. -/
theorem commutative_of_determinantKernel_core_spine_algebraicClosure_charAway
    {F : Type*} [Field F]
    {G : Type*} [Group G] [Finite G]
    {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]
    (ρ : Representation F G V) (hfaithful : Function.Injective ρ)
    (hodd : Odd (Nat.card G)) (hdim : Module.finrank F V = 2)
    (hchar : ∀ r : ℕ, r.Prime → r ∣ Nat.card G → ¬ CharP F r)
    (hdet_ne_bot : determinantKernelSubgroup ρ ≠ ⊥)
    (hind : ∀ N : Subgroup (determinantKernelSubgroup ρ), N.Normal → N ≠ ⊥ → N ≠ ⊤ →
      ∃ r : ℕ, r.Prime ∧ OddOrder.Isaacs.Ch01.opCore r N ≠ ⊥) :
    Std.Commutative (· * · : G → G → G) := by
  let ρK : Representation (AlgebraicClosure F) G
      (TensorProduct F (AlgebraicClosure F) V) :=
    baseChangeRepresentation (AlgebraicClosure F) ρ
  have hfaithfulK : Function.Injective ρK := by
    simpa [ρK] using
      baseChangeRepresentation_faithful (AlgebraicClosure F) ρ hfaithful
  have hdimK :
      Module.finrank (AlgebraicClosure F)
        (TensorProduct F (AlgebraicClosure F) V) = 2 := by
    exact
      (Module.finrank_baseChange (R := AlgebraicClosure F) (S := F) (M' := V)).trans hdim
  have hdetK_ne_bot : determinantKernelSubgroup ρK ≠ ⊥ := by
    change
      determinantKernelSubgroup (baseChangeRepresentation (AlgebraicClosure F) ρ) ≠ ⊥
    rw [determinantKernelSubgroup_baseChangeRepresentation (AlgebraicClosure F) ρ]
    exact hdet_ne_bot
  have hindK :
      ∀ N : Subgroup (determinantKernelSubgroup ρK),
        N.Normal → N ≠ ⊥ → N ≠ ⊤ →
          ∃ r : ℕ, r.Prime ∧ OddOrder.Isaacs.Ch01.opCore r N ≠ ⊥ := by
    change
      ∀ N : Subgroup
          (determinantKernelSubgroup
            (baseChangeRepresentation (AlgebraicClosure F) ρ)),
        N.Normal → N ≠ ⊥ → N ≠ ⊤ →
          ∃ r : ℕ, r.Prime ∧ OddOrder.Isaacs.Ch01.opCore r N ≠ ⊥
    rw [determinantKernelSubgroup_baseChangeRepresentation (AlgebraicClosure F) ρ]
    exact hind
  exact
    commutative_of_determinantKernel_core_spine_isAlgClosed_charAway
      ρK hfaithfulK hodd hdimK (charAway_algebraicClosure hchar)
      hdetK_ne_bot hindK

/-- Algebraic-closure reduction for the current BG Thm 2.6(b) spine.

This keeps the remaining induction hypothesis explicit but moves the field
from `F` to `AlgebraicClosure F`, where the q≠p Maschke/eigenline branch is
available.  The content is the faithful scalar-extension and dimension
transport, not a theorem rename. -/
private theorem
    sylow_commutative_and_commutator_le_of_algebraicClosure_induction
    {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [CharP F p]
    {G : Type*} [Group G] [Finite G] [Finite (Sylow p G)]
    {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]
    (ρ : Representation F G V) (hfaithful : Function.Injective ρ)
    (hodd : Odd (Nat.card G)) (hdim : Module.finrank F V = 2)
    (hind :
      ∀ N : Subgroup
          (determinantKernelSubgroup
            (baseChangeRepresentation (AlgebraicClosure F) ρ)),
        N.Normal → N ≠ ⊥ → N ≠ ⊤ →
        ∃ r : ℕ, r.Prime ∧ OddOrder.Isaacs.Ch01.opCore r N ≠ ⊥)
    (P : Sylow p G) :
    Std.Commutative (· * · : P → P → P) ∧
      commutator G ≤ (P : Subgroup G) := by
  let ρK : Representation (AlgebraicClosure F) G
      (TensorProduct F (AlgebraicClosure F) V) :=
    baseChangeRepresentation (AlgebraicClosure F) ρ
  have hfaithfulK : Function.Injective ρK := by
    simpa [ρK] using
      baseChangeRepresentation_faithful (AlgebraicClosure F) ρ hfaithful
  have hdimK :
      Module.finrank (AlgebraicClosure F)
        (TensorProduct F (AlgebraicClosure F) V) = 2 := by
    exact
      (Module.finrank_baseChange (R := AlgebraicClosure F) (S := F) (M' := V)).trans hdim
  exact
    sylow_commutative_and_commutator_le_of_determinantKernel_spine_isAlgClosed_induction
      ρK hfaithfulK hodd hdimK hind P

/-- Algebraic-closure reduction with the induction hypothesis stated on the
original determinant kernel.

The preceding determinant-kernel compatibility identifies the determinant
kernel after scalar extension with the original `G*`, so the theorem-facing
induction hypothesis no longer has to mention the base-changed representation. -/
theorem
    sylow_commutative_and_commutator_le_of_algebraicClosure_original_induction
    {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [CharP F p]
    {G : Type*} [Group G] [Finite G] [Finite (Sylow p G)]
    {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]
    (ρ : Representation F G V) (hfaithful : Function.Injective ρ)
    (hodd : Odd (Nat.card G)) (hdim : Module.finrank F V = 2)
    (hind : ∀ N : Subgroup (determinantKernelSubgroup ρ),
      N.Normal → N ≠ ⊥ → N ≠ ⊤ →
        ∃ r : ℕ, r.Prime ∧ OddOrder.Isaacs.Ch01.opCore r N ≠ ⊥)
    (P : Sylow p G) :
    Std.Commutative (· * · : P → P → P) ∧
      commutator G ≤ (P : Subgroup G) := by
  refine
    sylow_commutative_and_commutator_le_of_algebraicClosure_induction
      ρ hfaithful hodd hdim ?_ P
  rw [determinantKernelSubgroup_baseChangeRepresentation (AlgebraicClosure F) ρ]
  exact hind

end OddOrder.BG.Ch1.S02


