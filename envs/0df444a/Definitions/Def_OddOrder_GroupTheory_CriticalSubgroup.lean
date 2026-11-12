-- Prove2me | Definitions.Def_OddOrder_GroupTheory_CriticalSubgroup
-- name    : OddOrder_GroupTheory_CriticalSubgroup
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T05:26:12.698587+00:00
-- url     : https://prove2.me/theorems/041a19c4-0ad7-4f3a-8035-6ec3ebc3814f
-- title:
--   Critical subgroups (Gorenstein Thm 5.3.11 / 5.3.13)
-- statement:
--   Formalizes Thompson's critical subgroups, the foundation for Bender–Glauberman Theorem 1.13. BG delegates the proof to Gorenstein, *Finite Groups*, Thm 5.3.11 (existence of a critical subgroup) and Thm 5.3.13 (properties of $\Omega_1(C)$), since Isaacs has no corresponding theorem.
--
--   Main definitions: `IsCritical` (a subgroup $C\le G$ satisfying the conditions of Gorenstein 5.3.11), `centralizer_eq_self_of_maximal_abelian_normal` (Gorenstein Lemma 5.3.12), `omega1Center` ($\Omega_1(Z(P))$, shown characteristic in $P$), and `IsCharAbelian` (the predicate "characteristic abelian subgroup"), plus related center lemmas.
--
--   The bundle also proves 29 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/GroupTheory/CriticalSubgroup.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/GroupTheory/CriticalSubgroup.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_GroupTheory_OmegaSubgroup
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_Main_CommutatorBasics
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_Main_ThreeSubgroupsCoprime
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_Main_BaerTrick
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_Main_ChainNilpotent
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_ForwardFromCh03
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_Main_ThreeSubgroups
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic

namespace OddOrder.GroupTheory

variable {G : Type*} [Group G]

/-- **Gorenstein "Finite Groups" Thm 5.3.11** の条件を満たす部分群 `C ≤ G` =
`G` の **critical subgroup**:

* (char) `C` は `G` で characteristic;
* (i) `cl(C) ≤ 2`, すなわち `⁅C, C⁆ ≤ Z(C)`;
* (ii) `[G, C] ≤ Z(C)` (ambient `G` 側で, `Z(C)` は `C.subtype` 像);
* (iii) `C_G(C) = Z(C)` (self-centralizing).

Gorenstein の (i) に含まれる `C/Z(C)` elementary abelian は導出可能なので
def には入れない. -/
def IsCritical (C : Subgroup G) : Prop :=
  C.Characteristic
    ∧ _root_.commutator ↥C ≤ Subgroup.center ↥C
    ∧ ⁅(⊤ : Subgroup G), C⁆ ≤ (Subgroup.center ↥C).map C.subtype
    ∧ Subgroup.centralizer (C : Set G) = (Subgroup.center ↥C).map C.subtype

namespace IsCritical

variable {C : Subgroup G}

/-- critical ⇒ `C` characteristic. -/
theorem characteristic (hC : IsCritical C) : C.Characteristic := hC.1

/-- critical ⇒ `cl(C) ≤ 2` (`⁅C, C⁆ ≤ Z(C)`). -/
theorem commutator_le_center (hC : IsCritical C) :
    _root_.commutator ↥C ≤ Subgroup.center ↥C := hC.2.1

/-- critical ⇒ `[G, C] ≤ Z(C)` (ambient `G`). -/
theorem commutator_top_le_center (hC : IsCritical C) :
    ⁅(⊤ : Subgroup G), C⁆ ≤ (Subgroup.center ↥C).map C.subtype := hC.2.2.1

/-- critical ⇒ `C_G(C) = Z(C)` (self-centralizing). -/
theorem centralizer_eq (hC : IsCritical C) :
    Subgroup.centralizer (C : Set G) = (Subgroup.center ↥C).map C.subtype := hC.2.2.2

end IsCritical

section MaximalAbelianNormal

variable {P : Type*} [Group P]

/-- A nontrivial normal subgroup `K` of a finite `p`-group meets the center
nontrivially: there is a nonidentity element of `K` lying in `Z(P)`.

Proof mirrors `IsPGroup.center_nontrivial`: `ConjAct P` is a `p`-group acting on
`↥K` by conjugation (well-defined as `K` is normal); its fixed points are the
elements of `K` central in `P`. Fixed-point counting (`p ∣ |K|` since `K ≠ ⊥`,
and `1` is a fixed point) yields a second fixed point. -/
theorem exists_mem_center_of_normal_ne_bot {p : ℕ} [Fact p.Prime] [Finite P]
    (hP : IsPGroup p P) {K : Subgroup P} [K.Normal] (hK : K ≠ ⊥) :
    ∃ x : P, x ∈ K ∧ x ∈ Subgroup.center P ∧ x ≠ 1 := by
  -- `ConjAct P` is a `p`-group acting on `↥K`.
  have hConj : IsPGroup p (ConjAct P) := hP.of_equiv ConjAct.toConjAct
  -- `p ∣ |K|` since `K` is a nontrivial finite `p`-group.
  have hKp : IsPGroup p K := hP.to_subgroup K
  have : Nontrivial K := (Subgroup.nontrivial_iff_ne_bot K).mpr hK
  have hdvd : p ∣ Nat.card K := by
    obtain ⟨n, hn0, hn⟩ := hKp.nontrivial_iff_card.mp inferInstance
    exact hn.symm ▸ dvd_pow_self _ (ne_of_gt hn0)
  -- `1 : ↥K` is a fixed point of the conjugation action.
  have h1fix : (1 : K) ∈ MulAction.fixedPoints (ConjAct P) K := by
    rw [MulAction.mem_fixedPoints]
    intro g
    apply Subtype.ext
    rw [ConjAct.Subgroup.val_conj_smul]
    simp
  -- A second fixed point exists.
  obtain ⟨b, hb_fix, hb_ne⟩ :=
    hConj.exists_fixed_point_of_prime_dvd_card_of_fixed_point (α := K) hdvd h1fix
  refine ⟨(b : P), b.2, ?_, ?_⟩
  · -- A fixed point of conjugation is central in `P`.
    rw [Subgroup.mem_center_iff]
    intro g
    have hfix := (MulAction.mem_fixedPoints.mp hb_fix) (ConjAct.toConjAct g)
    have hval : ((ConjAct.toConjAct g • b : K) : P) = g * (b : P) * g⁻¹ := by
      rw [ConjAct.Subgroup.val_conj_smul, ConjAct.toConjAct_smul]
    rw [Subtype.ext_iff, hval] at hfix
    -- `g * b * g⁻¹ = b` ⟺ `g * b = b * g`.
    rwa [mul_inv_eq_iff_eq_mul] at hfix
  · -- `b ≠ 1` in `↥K` gives `(b : P) ≠ 1`.
    exact fun h => hb_ne (Subtype.ext (by simpa using h.symm))

variable [Finite P] {p : ℕ} [Fact p.Prime]

set_option backward.isDefEq.respectTransparency false in
/-- **Gorenstein "Finite Groups" Lemma 5.3.12.** If `M` is a normal subgroup of a
finite `p`-group `P` that is maximal subject to being abelian, then `M` is
self-centralizing: `C_P(M) = M`.

`hM_comm` witnesses that `M` is abelian, and `hM_max` its maximality among abelian
normal subgroups (any abelian normal `N ⊇ M` equals `M`).

Proof (Gorenstein): `M ≤ H := C_P(M)` since `M` is abelian. If `M < H`, pass to
`P̄ = P/M`; the image `H̄` is normal and nonzero, so it meets `Z(P̄)` in a
nonidentity central element `x̄`. The preimage `X` of `⟨x̄⟩` is normal in `P`,
contains `M`, has `M ≤ Z(X)` (as `X ≤ H` centralizes `M`), and `X/M ≅ ⟨x̄⟩` is
cyclic, hence `X` is abelian. Then `M < X` contradicts maximality of `M`. -/
theorem centralizer_eq_self_of_maximal_abelian_normal
    (hP : IsPGroup p P) {M : Subgroup P} [M.Normal]
    (hM_comm : ∀ x ∈ M, ∀ y ∈ M, x * y = y * x)
    (hM_max : ∀ N : Subgroup P, N.Normal → (∀ x ∈ N, ∀ y ∈ N, x * y = y * x) →
      M ≤ N → N = M) :
    Subgroup.centralizer (M : Set P) = M := by
  -- `M ≤ C_P(M)` because `M` is abelian.
  have hM_le : M ≤ Subgroup.centralizer (M : Set P) := by
    intro m hm
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact (hM_comm h hh m hm)
  refine le_antisymm ?_ hM_le
  -- Suppose `C_P(M) ⊄ M`; derive a contradiction.
  by_contra hnot
  -- Then `M < H := C_P(M)`.
  set H := Subgroup.centralizer (M : Set P) with hH_def
  have hMH : M < H := lt_of_le_of_ne hM_le (fun h => hnot (h ▸ le_refl _))
  -- `H` is normal in `P` (centralizer of a normal subgroup).
  have : H.Normal := inferInstance
  -- Image of `H` in `P̄ = P/M`.
  set q := QuotientGroup.mk' M with hq_def
  set Hbar := H.map q with hHbar_def
  have : Hbar.Normal := Subgroup.Normal.map inferInstance q (QuotientGroup.mk'_surjective M)
  -- `H̄ ≠ ⊥`: pick `h ∈ H \ M`, then `q h ≠ 1`.
  have hHbar_ne : Hbar ≠ ⊥ := by
    obtain ⟨h, hhH, hhM⟩ := SetLike.exists_of_lt hMH
    intro hbot
    apply hhM
    have : q h ∈ Hbar := Subgroup.mem_map_of_mem q hhH
    rw [hbot, Subgroup.mem_bot] at this
    exact (QuotientGroup.eq_one_iff h).mp this
  -- `P̄` is a `p`-group.
  have hPbar : IsPGroup p (P ⧸ M) := hP.to_quotient M
  -- A nonidentity central element of `H̄`.
  obtain ⟨xbar, hxbar_H, hxbar_center, hxbar_ne⟩ :=
    exists_mem_center_of_normal_ne_bot hPbar hHbar_ne
  -- `⟨x̄⟩` is central, hence normal; its preimage `X` is normal in `P`.
  have hzp_le_center : Subgroup.zpowers xbar ≤ Subgroup.center (P ⧸ M) :=
    Subgroup.zpowers_le.mpr hxbar_center
  have hzp_normal : (Subgroup.zpowers xbar).Normal :=
    { conj_mem := fun n hn g => by
        rw [Subgroup.mem_center_iff.mp (hzp_le_center hn) g, mul_assoc,
          mul_inv_cancel, mul_one]
        exact hn }
  -- The preimage `X` of `⟨x̄⟩` in `P`; it is normal in `P`.
  set X := (Subgroup.zpowers xbar).comap q with hX_def
  have : X.Normal := inferInstance
  -- `M ≤ X` (since `q` sends `M` to `1 ∈ ⟨x̄⟩`).
  have hMX : M ≤ X := by
    intro m hm
    rw [hX_def, Subgroup.mem_comap, hq_def, QuotientGroup.mk'_apply,
      (QuotientGroup.eq_one_iff m).mpr hm]
    exact one_mem _
  -- `X ≤ H`: `X ≤ comap q H̄ = H ⊔ M = H`.
  have hXH : X ≤ H := by
    have h1 : X ≤ Hbar.comap q :=
      Subgroup.comap_mono (Subgroup.zpowers_le.mpr hxbar_H)
    have h2 : Hbar.comap q = M ⊔ H := by
      rw [hHbar_def, hq_def, QuotientGroup.comap_map_mk']
    rw [h2, sup_eq_right.mpr hMH.le] at h1
    exact h1
  -- `f : ↥X →* ⟨x̄⟩`, the quotient map restricted to `X`.
  have hf_mem : ∀ g : X, q (g : P) ∈ Subgroup.zpowers xbar := fun g => g.2
  set f : X →* Subgroup.zpowers xbar :=
    (q.comp X.subtype).codRestrict (Subgroup.zpowers xbar) hf_mem with hf_def
  -- `ker f ≤ Z(X)`: `f g = 1 ⟹ g ∈ M`, and `X ≤ H = C_P(M)` centralizes `M`.
  have hker : f.ker ≤ Subgroup.center X := by
    intro g hg
    rw [MonoidHom.mem_ker, hf_def] at hg
    have hgM : (g : P) ∈ M := by
      have : q (g : P) = 1 := by
        have := congrArg (Subtype.val) hg
        simpa [MonoidHom.codRestrict_apply] using this
      exact (QuotientGroup.eq_one_iff (g : P)).mp this
    rw [Subgroup.mem_center_iff]
    intro h
    apply Subtype.ext
    -- `h ∈ X ≤ H = C_P(M)` commutes with `g ∈ M`.
    have hhH : (h : P) ∈ Subgroup.centralizer (M : Set P) := hXH h.2
    have := Subgroup.mem_centralizer_iff.mp hhH (g : P) hgM
    simpa using this.symm
  -- `X` is abelian (cyclic quotient by central kernel).
  have hX_comm : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x := by
    intro x hx y hy
    have := (f.isMulCommutative_of_isCyclic_of_ker_le_center hker).is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩
    exact congrArg Subtype.val this
  -- `X = M` by maximality, but `x ∈ X \ M` — contradiction.
  obtain ⟨x, hx_eq⟩ := QuotientGroup.mk'_surjective M xbar
  have hxX : x ∈ X := by
    rw [hX_def, Subgroup.mem_comap, hq_def, hx_eq]
    exact Subgroup.mem_zpowers xbar
  have hxM : x ∉ M := by
    intro hmem
    apply hxbar_ne
    rw [← hx_eq, QuotientGroup.mk'_apply]
    exact (QuotientGroup.eq_one_iff x).mpr hmem
  have hXeqM : X = M := hM_max X inferInstance hX_comm hMX
  exact hxM (hXeqM ▸ hxX)

/-- **Gorenstein "Finite Groups" Theorem 2.6.4 (`Ω₁(Z(P))` form).** A nontrivial
normal subgroup `N` of a finite `p`-group `P` meets `Ω₁(Z(P))` nontrivially: there
is `x ∈ N ∩ Z(P)` with `x ≠ 1` and `x ^ p = 1`.

Proof: `exists_mem_center_of_normal_ne_bot` gives a nonidentity `y ∈ N ∩ Z(P)`.
As `P` is a `p`-group, `orderOf y = p ^ k` with `k ≥ 1`; then `x = y ^ (p ^ (k-1))`
has order `p`, lies in `N` and in `Z(P)`, and satisfies `x ^ p = 1`. -/
theorem exists_mem_omega1_center_of_normal_ne_bot
    (hP : IsPGroup p P) {N : Subgroup P} [N.Normal] (hN : N ≠ ⊥) :
    ∃ x : P, x ∈ N ∧ x ∈ Subgroup.center P ∧ x ≠ 1 ∧ x ^ p = 1 := by
  obtain ⟨y, hyN, hyZ, hy1⟩ := exists_mem_center_of_normal_ne_bot hP hN
  -- `orderOf y = p ^ k` with `k ≥ 1`.
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hP) y
  have hkpos : 0 < k := by
    rcases Nat.eq_zero_or_pos k with hk0 | hk0
    · exact absurd (orderOf_eq_one_iff.mp (by rw [hk, hk0, pow_zero])) hy1
    · exact hk0
  -- `x = y ^ (p ^ (k-1))` has order `p`.
  refine ⟨y ^ (p ^ (k - 1)), N.pow_mem hyN _, (Subgroup.center P).pow_mem hyZ _, ?_, ?_⟩
  · -- `x ≠ 1` because `orderOf x = p ≠ 1`.
    have hp1 : (1 : ℕ) < p := (Fact.out (p := p.Prime)).one_lt
    have hox : orderOf (y ^ (p ^ (k - 1))) = p := by
      rw [orderOf_pow_of_dvd (by positivity) (hk ▸ pow_dvd_pow p (Nat.sub_le k 1)), hk,
        Nat.div_eq_iff_eq_mul_left (by positivity) (pow_dvd_pow p (Nat.sub_le k 1)),
        ← pow_succ', Nat.sub_add_cancel hkpos]
    intro hx1
    rw [hx1, orderOf_one] at hox
    exact hp1.ne hox
  · -- `x ^ p = y ^ (p ^ k) = 1`.
    rw [← pow_mul, ← pow_succ, Nat.sub_add_cancel hkpos, ← hk, pow_orderOf_eq_one]

end MaximalAbelianNormal

section Omega1Center

variable {P : Type*} [Group P] {p : ℕ}

/-- `Ω₁(Z(P)) = {g ∈ Z(P) | g ^ p = 1}` packaged as a subgroup of `P` via
`omega1OfAbelian` (the center is abelian). -/
private def omega1Center (P : Type*) [Group P] (p : ℕ) : Subgroup P :=
  omega1OfAbelian P (Subgroup.center P) p
    (fun _ hx y _ => (Subgroup.mem_center_iff.mp hx y).symm)

private theorem mem_omega1Center {g : P} :
    g ∈ omega1Center P p ↔ g ∈ Subgroup.center P ∧ g ^ p = 1 := Iff.rfl

private theorem omega1Center_le_center : omega1Center P p ≤ Subgroup.center P :=
  fun _ hg => hg.1

/-- `Ω₁(Z(P))` is characteristic in `P`: any `φ : P ≃* P` preserves `Z(P)` and
`g ^ p = 1`. -/
private instance omega1Center.characteristic : (omega1Center P p).Characteristic := by
  rw [Subgroup.characteristic_iff_comap_eq]
  intro φ
  -- `φ g ∈ Z(P) ↔ g ∈ Z(P)` from `centerCharacteristic`.
  have hcZ : ∀ g : P, φ g ∈ Subgroup.center P ↔ g ∈ Subgroup.center P := by
    intro g
    rw [Subgroup.mem_center_iff, Subgroup.mem_center_iff]
    constructor
    · intro h h'
      have := h (φ h')
      rwa [← map_mul, ← map_mul, φ.injective.eq_iff] at this
    · intro h h'
      obtain ⟨h'', rfl⟩ := φ.surjective h'
      rw [← map_mul, ← map_mul, φ.injective.eq_iff]
      exact h h''
  ext g
  simp only [Subgroup.mem_comap, mem_omega1Center, MulEquiv.coe_toMonoidHom]
  rw [hcZ g]
  refine and_congr_right fun _ => ?_
  constructor
  · intro hpow
    have := congrArg φ.symm hpow
    rwa [map_pow, φ.symm_apply_apply, map_one] at this
  · intro hpow
    rw [← map_pow, hpow, map_one]

end Omega1Center

section Existence

open scoped commutatorElement

variable {P : Type*} [Group P] [Finite P] {p : ℕ} [Fact p.Prime]

/-- A characteristic subgroup of a characteristic subgroup is characteristic in
the ambient group (char-in-char transitivity). Needed to identify `Z(C)` as a
characteristic abelian subgroup of `P` when `C` is characteristic. -/
theorem characteristic_map_subtype_of_characteristic
    {G : Type*} [Group G] {H : Subgroup G} {K : Subgroup H}
    (hH : H.Characteristic) (hK : K.Characteristic) :
    (K.map H.subtype).Characteristic := by
  rw [Subgroup.characteristic_iff_map_le]
  intro φ y hy
  rw [Subgroup.mem_map] at hy ⊢
  obtain ⟨x, hxK, rfl⟩ := hy
  rw [Subgroup.mem_map] at hxK
  obtain ⟨k, hkK, rfl⟩ := hxK
  -- `φ` restricts to `H ≃* H` since `H` is characteristic.
  have hHfix : H.map φ.toMonoidHom = H := Subgroup.characteristic_iff_map_eq.mp hH φ
  let φH : H ≃* H := (MulEquiv.subgroupMap φ H).trans (MulEquiv.subgroupCongr hHfix)
  have hφH_coe : ∀ h : H, (φH h : G) = φ (h : G) := fun h => rfl
  -- `K` is characteristic in `H`, so `φH k ∈ K`.
  have hk_image : φH k ∈ K :=
    (Subgroup.characteristic_iff_map_le.mp hK φH) (Subgroup.mem_map_of_mem φH.toMonoidHom hkK)
  exact ⟨φH k, hk_image, hφH_coe k⟩

/-- The predicate "`N` is a characteristic abelian subgroup" used to extract a
maximal one. -/
private def IsCharAbelian (N : Subgroup P) : Prop :=
  N.Characteristic ∧ ∀ x ∈ N, ∀ y ∈ N, x * y = y * x

/-- A finite group has a maximal characteristic abelian subgroup (the trivial
subgroup is one, and the subgroup lattice is finite hence well-founded). -/
private theorem exists_maximal_charAbelian :
    ∃ D : Subgroup P, Maximal (IsCharAbelian (P := P)) D := by
  have : Finite (Subgroup P) := Finite.of_injective _ (SetLike.coe_injective (A := Subgroup P))
  have : WellFoundedGT (Subgroup P) := Finite.to_wellFoundedGT
  obtain ⟨D, _, hD⟩ := exists_maximal_ge_of_wellFoundedGT (IsCharAbelian (P := P)) ⊥
    ⟨Subgroup.botCharacteristic, by simp⟩
  exact ⟨D, hD⟩

omit [Finite P] in
/-- If `C` is characteristic, then `Z(C)` (as an ambient subgroup) is a
characteristic abelian subgroup of `P`. -/
private theorem center_map_subtype_isCharAbelian {C : Subgroup P} (hC : C.Characteristic) :
    IsCharAbelian ((Subgroup.center ↥C).map C.subtype) := by
  refine ⟨characteristic_map_subtype_of_characteristic hC Subgroup.centerCharacteristic, ?_⟩
  rintro x ⟨x', hx', rfl⟩ y ⟨y', hy', rfl⟩
  rw [← map_mul, ← map_mul]
  exact congrArg C.subtype ((Subgroup.mem_center_iff.mp hx' y').symm)

/-- **Gorenstein "Finite Groups" Theorem 5.3.11** (J. G. Thompson). Every finite
`p`-group `P` possesses a **critical subgroup** `C`: a characteristic subgroup with
`cl(C) ≤ 2`, `[P, C] ⊆ Z(C)`, and `C_P(C) = Z(C)` (self-centralizing).

This is the existence half of the definition; the derived faithfulness property
(every nontrivial `p'`-automorphism acts nontrivially) is `IsCritical`-downstream.
`S2` of `notes/bg/thm113_design.md`.

Proof (Gorenstein, two cases). Let `D` be a maximal characteristic abelian
subgroup and `H = C_P(D)`.

* If `H = D`, then `C = D` is critical: `D` is abelian (`cl = 1`), characteristic,
  `[P, D] ⊆ D = Z(D)`, and `C_P(D) = D = Z(D)`.
* If `D < H`, pass to `P̄ = P/D`. The image `H̄` of `H` is a nontrivial normal
  subgroup, so it meets `Ω₁(Z(P̄))`. Let `C` be the preimage of
  `C̄ = H̄ ∩ Ω₁(Z(P̄))`. Then `C = H ∩ K` (with `K` the preimage of `Ω₁(Z(P̄))`,
  characteristic by `Characteristic.comap_quotient_mk`) is characteristic;
  `D ⊆ Z(C)` (as `C ⊆ H` centralizes `D`); `Z(C) = D` by maximality of `D`;
  `C/Z(C) = C̄` is elementary abelian (so `cl(C) ≤ 2`); `[P, C] ⊆ D = Z(C)`
  (as `C̄ ⊆ Z(P̄)`); and `C_P(C) = Z(C)` via the second-center theorem applied to
  `C_P(C)/D`. -/
theorem isCritical_exists (hG : IsPGroup p P) : ∃ C : Subgroup P, IsCritical C := by
  obtain ⟨D, hD_max⟩ := exists_maximal_charAbelian (P := P)
  obtain ⟨hD_char, hD_ab⟩ := hD_max.prop
  have : D.Characteristic := hD_char
  -- `H = C_P(D)`, characteristic, and `D ≤ H` since `D` is abelian.
  set H := Subgroup.centralizer (D : Set P) with hH_def
  have hH_char : H.Characteristic := Subgroup.characteristic_centralizer
  have hDH : D ≤ H := by
    intro d hd
    rw [hH_def, Subgroup.mem_centralizer_iff]
    exact fun g hg => hD_ab g hg d hd
  -- Case split on whether `D` is self-centralizing.
  -- `D` abelian ⇒ `Z(D) = ⊤`, so `(Z(D)).map subtype = D`.
  have hcenterD : Subgroup.center ↥D = ⊤ := by
    rw [Subgroup.center_eq_top_iff, isMulCommutative_iff]
    exact fun x y => Subtype.ext (hD_ab x x.2 y y.2)
  have hZD : (Subgroup.center ↥D).map D.subtype = D := by
    rw [hcenterD, ← MonoidHom.range_eq_map, D.range_subtype]
  by_cases hcase : H ≤ D
  · -- **Case A**: `C_P(D) = D`. Take `C = D`.
    have hHD : H = D := le_antisymm hcase hDH
    have : D.Normal := inferInstance
    refine ⟨D, hD_char, ?_, ?_, ?_⟩
    · -- `commutator ↥D ≤ center ↥D = ⊤`.
      rw [hcenterD]; exact le_top
    · -- `[P, D] ⊆ Z(D).map subtype = D`.
      rw [hZD]; exact Subgroup.commutator_le_right _ _
    · -- `C_P(D) = Z(D).map subtype = D`.
      rw [hZD, ← hH_def, hHD]
  · -- **Case B**: `D < H`.
    have hDH_lt : D < H := lt_of_le_of_ne hDH (fun h => hcase (h ▸ le_rfl))
    -- Pass to `P̄ = P / D`.
    set q := QuotientGroup.mk' D with hq_def
    have hPbar : IsPGroup p (P ⧸ D) := hG.to_quotient D
    -- `K = preimage of Ω₁(Z(P̄))`, characteristic in `P`.
    set K := (omega1Center (P ⧸ D) p).comap q with hK_def
    have hK_char : K.Characteristic :=
      Subgroup.Characteristic.comap_quotient_mk omega1Center.characteristic
    -- `C = H ⊓ K`.
    set C := H ⊓ K with hC_def
    -- `C` is characteristic (`H`, `K` both characteristic).
    have hC_char : C.Characteristic := by
      rw [hC_def, Subgroup.characteristic_iff_comap_eq]
      intro φ
      rw [Subgroup.comap_inf, Subgroup.characteristic_iff_comap_eq.mp hH_char φ,
        Subgroup.characteristic_iff_comap_eq.mp hK_char φ]
    -- `q x = 1 ↔ x ∈ D`.
    have hker : ∀ x : P, q x = 1 ↔ x ∈ D := fun x => by
      rw [hq_def, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    -- `D ≤ K` (kernel maps to `1 ∈ Ω₁(Z(P̄))`).
    have hDK : D ≤ K := by
      intro d hd
      rw [hK_def, Subgroup.mem_comap, (hker d).mpr hd]
      exact one_mem _
    -- `D ≤ C`.
    have hDC : D ≤ C := le_inf hDH hDK
    -- For `c ∈ C`, `q c ∈ Z(P̄)`.
    have hqc_center : ∀ c ∈ C, q c ∈ Subgroup.center (P ⧸ D) := by
      intro c hc
      exact omega1Center_le_center (Subgroup.mem_comap.mp hc.2)
    -- (F-CD) `D` is central in `C`: every `c ∈ C ⊆ H = C_P(D)` centralizes `D`.
    have hDcentralC : ∀ d ∈ D, ∀ c ∈ C, d * c = c * d := by
      intro d hd c hc
      have : c ∈ Subgroup.centralizer (D : Set P) := hc.1
      exact Subgroup.mem_centralizer_iff.mp this d hd
    -- Membership bridge: `x ∈ C` centralizing all of `C` lies in `Z(C)`-image.
    have hmem_ZC : ∀ x : P, x ∈ C → (∀ c ∈ C, x * c = c * x) →
        x ∈ (Subgroup.center ↥C).map C.subtype := by
      intro x hxC hxcent
      have hcent : (⟨x, hxC⟩ : ↥C) ∈ Subgroup.center ↥C := by
        rw [Subgroup.mem_center_iff]
        intro c
        exact Subtype.ext (hxcent c c.2).symm
      exact Subgroup.mem_map_of_mem C.subtype hcent
    -- `(center ↥C).map subtype = D` (bridge), via maximality of `D`.
    have hD_le_ZC : D ≤ (Subgroup.center ↥C).map C.subtype :=
      fun d hd => hmem_ZC d (hDC hd) (fun c hc => hDcentralC d hd c hc)
    have hZC : (Subgroup.center ↥C).map C.subtype = D := by
      refine le_antisymm ?_ hD_le_ZC
      exact hD_max.le_of_ge (center_map_subtype_isCharAbelian hC_char) hD_le_ZC
    refine ⟨C, hC_char, ?_, ?_, ?_⟩
    · -- (i) `commutator ↥C ≤ center ↥C`: `[c, c'] ∈ D` since `q c, q c'` central.
      rw [_root_.commutator_def, Subgroup.commutator_le]
      intro a _ b _
      rw [← Subgroup.mem_map_iff_mem C.subtype_injective, hZC, map_commutatorElement]
      have hcomm : q ⁅C.subtype a, C.subtype b⁆ = 1 := by
        rw [map_commutatorElement]
        exact Commute.commutator_eq
          (Subgroup.mem_center_iff.mp (hqc_center a a.2) (q (C.subtype b))).symm
      exact (hker _).mp hcomm
    · -- (ii) `⁅⊤, C⁆ ≤ (center ↥C).map subtype = D`.
      rw [hZC, Subgroup.commutator_le]
      intro g _ c hc
      have hcomm : q ⁅g, c⁆ = 1 := by
        rw [map_commutatorElement]
        exact Commute.commutator_eq
          (Subgroup.mem_center_iff.mp (hqc_center c hc) (q g))
      exact (hker _).mp hcomm
    · -- (iii) `C_P(C) = (center ↥C).map subtype = D`.
      rw [hZC]
      refine le_antisymm ?_ ?_
      · -- `C_P(C) ≤ D`: any element centralizing `C` lies in `C` (second center), then in `D`.
        -- First, `Q := C_P(C)` is contained in `H = C_P(D)` (it centralizes `D ⊆ C`).
        have hQH : Subgroup.centralizer (C : Set P) ≤ H := by
          intro x hx
          rw [hH_def, Subgroup.mem_centralizer_iff]
          intro d hd
          exact (Subgroup.mem_centralizer_iff.mp hx d (hDC hd))
        -- `Q ≤ C`.
        have hQC : Subgroup.centralizer (C : Set P) ≤ C := by
          by_contra hQnotC
          rw [SetLike.not_le_iff_exists] at hQnotC
          obtain ⟨q₀, hq₀Q, hq₀C⟩ := hQnotC
          -- `Q̄ := Q.map q` is normal and nontrivial.
          have hQchar : (Subgroup.centralizer (C : Set P)).Characteristic :=
            Subgroup.characteristic_centralizer (H := C) (hH := hC_char)
          set Qbar := (Subgroup.centralizer (C : Set P)).map q with hQbar_def
          have : Qbar.Normal :=
            Subgroup.Normal.map inferInstance q (QuotientGroup.mk'_surjective D)
          have hQbar_ne : Qbar ≠ ⊥ := by
            intro hbot
            apply hq₀C
            have hmem : q q₀ ∈ Qbar := Subgroup.mem_map_of_mem q hq₀Q
            rw [hbot, Subgroup.mem_bot] at hmem
            exact hDC ((hker q₀).mp hmem)
          -- Second center: `Q̄ ∩ Ω₁(Z(P̄)) ≠ 1`.
          obtain ⟨xbar, hxbarQ, hxbarZ, hxbar_ne, hxbar_p⟩ :=
            exists_mem_omega1_center_of_normal_ne_bot hPbar hQbar_ne
          -- Lift `xbar` to `q'' ∈ Q`.
          rw [hQbar_def, Subgroup.mem_map] at hxbarQ
          obtain ⟨q'', hq''Q, hq''eq⟩ := hxbarQ
          -- `q'' ∈ H` (since `Q ≤ H`) and `q q'' ∈ Ω₁(Z(P̄))`, so `q'' ∈ K`, hence `q'' ∈ C`.
          have hq''K : q'' ∈ K := by
            rw [hK_def, Subgroup.mem_comap, hq''eq, mem_omega1Center]
            exact ⟨hxbarZ, hxbar_p⟩
          have hq''C : q'' ∈ C := Subgroup.mem_inf.mpr ⟨hQH hq''Q, hq''K⟩
          -- `q''` centralizes `C` and lies in `C`, so `q'' ∈ Z(C)`-image `= D`, giving `q q'' = 1`.
          have hq''ZC : q'' ∈ (Subgroup.center ↥C).map C.subtype :=
            hmem_ZC q'' hq''C (fun c hc =>
              (Subgroup.mem_centralizer_iff.mp hq''Q c hc).symm)
          rw [hZC] at hq''ZC
          have : q q'' = 1 := (hker q'').mpr hq''ZC
          rw [hq''eq] at this
          exact hxbar_ne this
        -- Now `Q ≤ C` and `Q` centralizes `C`, so `Q ⊆ Z(C)`-image `= D`.
        intro x hx
        have hxC : x ∈ C := hQC hx
        have := hmem_ZC x hxC (fun c hc => (Subgroup.mem_centralizer_iff.mp hx c hc).symm)
        rwa [hZC] at this
      · -- `D ≤ C_P(C)`: `D` centralizes `C` (F-CD).
        intro d hd
        rw [Subgroup.mem_centralizer_iff]
        intro c hc
        exact (hDcentralC d hd c hc).symm

end Existence

section ClassTwoExponent

variable {K : Type*} [Group K]

open scoped commutatorElement

/-- Triangular-number Pascal step: `(k+1) * (k+1-1) / 2 = k * (k-1) / 2 + k`.
Phrased via `Nat.choose 2` (`= n*(n-1)/2`) and `Nat.choose_succ_succ'`. -/
private theorem succ_choose_two (k : ℕ) :
    (k + 1) * (k + 1 - 1) / 2 = k * (k - 1) / 2 + k := by
  have h := Nat.choose_succ_succ' k 1
  rw [Nat.choose_two_right, Nat.choose_two_right, Nat.choose_one_right] at h
  -- `(k+1).choose 2 = k.choose 1 + k.choose 2 = k + k.choose 2`.
  omega

/-- For `z := ⁅y, x⁆` central, `y ^ n * x = z ^ n * x * y ^ n`. Iterating the basic
relation `y * x = ⁅y, x⁆ * x * y` (which holds by definition of `⁅y, x⁆`). -/
private theorem pow_mul_eq_of_commutator_central (x y : K)
    (hz : ⁅y, x⁆ ∈ Subgroup.center K) (n : ℕ) :
    y ^ n * x = ⁅y, x⁆ ^ n * x * y ^ n := by
  -- `z` commutes with everything (`mem_center_iff` gives `g * z = z * g`).
  have hzc : ∀ g : K, ⁅y, x⁆ * g = g * ⁅y, x⁆ :=
    fun g => (Subgroup.mem_center_iff.mp hz g).symm
  -- Base relation: `y * x = z * x * y`.
  have hbase : y * x = ⁅y, x⁆ * x * y := by
    rw [commutatorElement_def]; group
  -- `y` commutes with `z^k`.
  have hycomm : ∀ j : ℕ, y * ⁅y, x⁆ ^ j = ⁅y, x⁆ ^ j * y :=
    fun j => (Commute.pow_right (show Commute y ⁅y, x⁆ from (hzc y).symm) j).eq
  induction n with
  | zero => simp
  | succ k ih =>
    calc y ^ (k + 1) * x
        = y * (y ^ k * x) := by rw [pow_succ']; group
      _ = y * (⁅y, x⁆ ^ k * x * y ^ k) := by rw [ih]
      _ = (y * ⁅y, x⁆ ^ k) * x * y ^ k := by group
      _ = (⁅y, x⁆ ^ k * y) * x * y ^ k := by rw [hycomm]
      _ = ⁅y, x⁆ ^ k * (y * x) * y ^ k := by group
      _ = ⁅y, x⁆ ^ k * (⁅y, x⁆ * x * y) * y ^ k := by rw [hbase]
      _ = ⁅y, x⁆ ^ (k + 1) * x * (y ^ (k + 1)) := by
          rw [pow_succ ⁅y, x⁆ k, pow_succ' y k]; simp only [mul_assoc]

/-- **Gorenstein "Finite Groups" Lemma 5.3.9, eq. (3.1).** In a group of class
`≤ 2` (`⁅K, K⁆ ≤ Z(K)`), for all `x y : K` and `n : ℕ`,
`(x * y) ^ n = ⁅y, x⁆ ^ (n * (n - 1) / 2) * x ^ n * y ^ n`.

Special case of the Hall–Petrescu collection formula. Proof by induction on `n`,
moving the central commutator `z = ⁅y, x⁆` past powers using
`pow_mul_eq_of_commutator_central`; the exponent accumulates as
`n(n-1)/2 + n = (n+1)n/2`. -/
theorem mul_pow_eq_commutator_pow_mul_of_class_le_two
    (hcl : _root_.commutator K ≤ Subgroup.center K) (x y : K) (n : ℕ) :
    (x * y) ^ n = ⁅y, x⁆ ^ (n * (n - 1) / 2) * x ^ n * y ^ n := by
  -- `z := ⁅y, x⁆` is central.
  have hz : ⁅y, x⁆ ∈ Subgroup.center K :=
    hcl (Subgroup.commutator_mem_commutator (Subgroup.mem_top y) (Subgroup.mem_top x))
  have hzc : ∀ g : K, ⁅y, x⁆ * g = g * ⁅y, x⁆ :=
    fun g => (Subgroup.mem_center_iff.mp hz g).symm
  -- `z^j` commutes with every element.
  have hzpow : ∀ (j : ℕ) (g : K), Commute (⁅y, x⁆ ^ j) g :=
    fun j g => Commute.pow_left (hzc g) j
  induction n with
  | zero => simp
  | succ k ih =>
    -- Target exponent: `(k+1) * (k+1-1) / 2 = k*(k-1)/2 + k`.
    have hexp : (k + 1) * (k + 1 - 1) / 2 = k * (k - 1) / 2 + k := succ_choose_two k
    calc (x * y) ^ (k + 1)
        = ⁅y, x⁆ ^ (k * (k - 1) / 2) * x ^ k * y ^ k * (x * y) := by rw [pow_succ, ih]
      _ = ⁅y, x⁆ ^ (k * (k - 1) / 2) * x ^ k * (y ^ k * x) * y := by group
      _ = ⁅y, x⁆ ^ (k * (k - 1) / 2) * x ^ k * (⁅y, x⁆ ^ k * x * y ^ k) * y := by
          rw [pow_mul_eq_of_commutator_central x y hz k]
      _ = ⁅y, x⁆ ^ (k * (k - 1) / 2) * (x ^ k * ⁅y, x⁆ ^ k) * x * (y ^ k * y) := by group
      _ = ⁅y, x⁆ ^ (k * (k - 1) / 2) * (⁅y, x⁆ ^ k * x ^ k) * x * (y ^ k * y) := by
          rw [(hzpow k (x ^ k)).eq]
      _ = ⁅y, x⁆ ^ (k * (k - 1) / 2 + k) * (x ^ k * x) * (y ^ k * y) := by
          rw [pow_add]; group
      _ = ⁅y, x⁆ ^ ((k + 1) * (k + 1 - 1) / 2) * x ^ (k + 1) * y ^ (k + 1) := by
          rw [hexp, pow_succ x, pow_succ y]

/-- **Gorenstein "Finite Groups" Lemma 5.3.9(i)** (key step). In a group of class
`≤ 2` with `p` odd, the product of two elements of order dividing `p` again has
order dividing `p`: if `x ^ p = 1` and `y ^ p = 1` then `(x * y) ^ p = 1`.

Proof: in `(x * y) ^ p = ⁅y, x⁆ ^ (p (p-1) / 2) · x ^ p · y ^ p`, the last two
factors are `1`. Also `⁅y, x⁆ ^ p = ⁅y ^ p, x⁆ = ⁅1, x⁆ = 1`, and for odd `p`,
`p ∣ p (p-1) / 2`, so `⁅y, x⁆ ^ (p (p-1) / 2) = 1`. -/
theorem mul_pow_prime_eq_one_of_class_le_two {p : ℕ} (hp_odd : Odd p)
    (hcl : _root_.commutator K ≤ Subgroup.center K) {x y : K}
    (hx : x ^ p = 1) (hy : y ^ p = 1) : (x * y) ^ p = 1 := by
  have hz : ⁅y, x⁆ ∈ Subgroup.center K :=
    hcl (Subgroup.commutator_mem_commutator (Subgroup.mem_top y) (Subgroup.mem_top x))
  -- `z ^ p = 1`: move `p` inside the left slot of the commutator using `pow_mul_eq_…`.
  have hzp : ⁅y, x⁆ ^ p = 1 := by
    have h := pow_mul_eq_of_commutator_central x y hz p
    rw [hy, one_mul, mul_one] at h
    -- `x = z^p * x`, so `z^p = 1`.
    nth_rewrite 1 [← one_mul x] at h
    exact (mul_right_cancel h).symm
  -- `p ∣ p (p-1) / 2`.
  have hdvd : p ∣ p * (p - 1) / 2 := by
    obtain ⟨k, rfl⟩ := hp_odd
    -- `(2k+1) * (2k) / 2 = (2k+1) * ((2k)/2) = (2k+1) * k`.
    rw [show 2 * k + 1 - 1 = 2 * k by omega,
      Nat.mul_div_assoc _ (Dvd.intro k rfl : 2 ∣ 2 * k), Nat.mul_div_cancel_left k two_pos]
    exact Dvd.intro k rfl
  obtain ⟨m, hm⟩ := hdvd
  rw [mul_pow_eq_commutator_pow_mul_of_class_le_two hcl, hx, hy, mul_one, mul_one, hm,
    pow_mul, hzp, one_pow]

end ClassTwoExponent

section Omega1ClassTwo

variable {K : Type*} [Group K] {p : ℕ}

/-- For odd `p` and class `≤ 2`, the set `{g : K | g ^ p = 1}` is a subgroup. -/
private def omega1OfClassLeTwo (K : Type*) [Group K] (p : ℕ) (hp_odd : Odd p)
    (hcl : _root_.commutator K ≤ Subgroup.center K) : Subgroup K where
  carrier := {g : K | g ^ p = 1}
  mul_mem' := fun {x y} hx hy => mul_pow_prime_eq_one_of_class_le_two hp_odd hcl hx hy
  one_mem' := one_pow p
  inv_mem' := fun {x} hx => by rw [Set.mem_ofPred_eq, inv_pow, hx, inv_one]

/-- **Gorenstein "Finite Groups" Lemma 5.3.9(i).** In a group `K` of class `≤ 2`
with `p` odd, every element of `Ω₁(K) = Omega K p 1` has `p`-th power `1`.

This is the load-bearing form: `Ω₁` has exponent dividing `p`. The set
`{g | g ^ p = 1}` is already a subgroup (`mul_pow_prime_eq_one_of_class_le_two`),
so it contains the closure `Omega K p 1`. -/
theorem Omega.pow_eq_one_of_class_le_two (hp_odd : Odd p)
    (hcl : _root_.commutator K ≤ Subgroup.center K) {g : K}
    (hg : g ∈ Omega K p 1) : g ^ p = 1 := by
  -- `Omega K p 1 = closure {g | g^(p^1) = 1} ≤ {g | g^p = 1}` (the latter is a subgroup).
  have hle : Omega K p 1 ≤ omega1OfClassLeTwo K p hp_odd hcl := by
    rw [Omega, Subgroup.closure_le]
    intro x hx
    change x ^ p = 1
    exact pow_one p ▸ hx
  simpa [omega1OfClassLeTwo] using hle hg

/-- **Gorenstein "Finite Groups" Lemma 5.3.9(i)** (exponent form). For odd `p` and
a class-`≤ 2` group `K`, `Ω₁(K)` has exponent `p`, provided `Ω₁(K)` is nontrivial.

`Monoid.exponent (Omega K p 1) = p`: every nonidentity element has order exactly
`p` (`p` prime ⇒ order dividing `p` is `1` or `p`; nonidentity ⇒ not `1`). -/
theorem Omega.exponent_eq_of_class_le_two [Fact p.Prime] (hp_odd : Odd p)
    (hcl : _root_.commutator K ≤ Subgroup.center K)
    [Nontrivial (Omega K p 1)] :
    Monoid.exponent (Omega K p 1) = p := by
  rw [Monoid.exponent_eq_prime_iff (Fact.out (p := p.Prime))]
  intro g hg
  -- `g ^ p = 1`, so `orderOf g ∣ p`; `g ≠ 1` rules out `orderOf g = 1`.
  have hgp : (g : K) ^ p = 1 := Omega.pow_eq_one_of_class_le_two hp_odd hcl g.2
  have hgp' : g ^ p = 1 := by
    apply Subtype.ext; rw [SubmonoidClass.coe_pow]; simpa using hgp
  have hdvd : orderOf g ∣ p := orderOf_dvd_of_pow_eq_one hgp'
  rcases ((Fact.out (p := p.Prime)).eq_one_or_self_of_dvd _ hdvd) with h1 | hp
  · exact absurd (orderOf_eq_one_iff.mp h1) hg
  · exact hp

end Omega1ClassTwo

section Faithful

open OddOrder.Isaacs.Ch04

open scoped commutatorElement

variable {P : Type*} [Group P] [Finite P] {p : ℕ} [Fact p.Prime]

variable {A : Type*} [Group A] [Finite A]

omit [Finite P] in
omit [Finite A] in
/-- If `A` acts trivially on a characteristic self-centralizing subgroup `C`
(`C ≤ C_P(C)`-image suffices via `IsCritical`), then `[P, A] = actionCommutator φ`
centralizes `C`, i.e. `actionCommutator φ ≤ C_P(C)`.

This is the three-subgroup-lemma core of Gorenstein 5.3.11 (iii)⇒(iv), carried out
in `Γ = P ⋊[φ] A` exactly as in `actionCommutator_commutator_eq_bot_of_acts_trivially`. -/
theorem actionCommutator_le_centralizer_of_acts_trivially_of_characteristic
    {φ : A →* MulAut P} {C : Subgroup P} (hC_char : C.Characteristic)
    (h_triv : (C : Set P) ⊆ Subgroup.fixedPointsOfMulAut φ) :
    actionCommutator φ ≤ Subgroup.centralizer (C : Set P) := by
  have : C.Characteristic := hC_char
  have : C.Normal := inferInstance
  -- Work in `Γ = P ⋊[φ] A`.
  set XG : Subgroup (P ⋊[φ] A) := (SemidirectProduct.inl : P →* P ⋊[φ] A).range with hXG
  set YA : Subgroup (P ⋊[φ] A) := (SemidirectProduct.inr : A →* P ⋊[φ] A).range with hYA
  set XC : Subgroup (P ⋊[φ] A) := C.map (SemidirectProduct.inl : P →* P ⋊[φ] A) with hXC
  set H_Γ : Subgroup (P ⋊[φ] A) := ⁅XG, YA⁆ with hHΓ_def
  have h_HΓ_eq : (actionCommutator φ).map SemidirectProduct.inl = H_Γ :=
    actionCommutator_map_inl φ
  -- Step 1: `⁅XC, YA⁆ = ⊥` (A acts trivially on C).
  have h_step1 : ⁅XC, YA⁆ = ⊥ := by
    rw [hXC, eq_bot_iff, Subgroup.commutator_le]
    rintro _ ⟨c, hc, rfl⟩ _ ⟨a, rfl⟩
    rw [SemidirectProduct.commutator_inl_inr, Subgroup.mem_bot]
    have h_fix : (φ a) c = c := h_triv hc a
    rw [show (φ a) c⁻¹ = ((φ a) c)⁻¹ from map_inv (φ a) c, h_fix, mul_inv_cancel]
    exact map_one _
  -- `⁅XG, XC⁆ ≤ XC`: `[P, C] ⊆ C` (C normal), pushed by `inl`.
  have h_GC_le : ⁅XG, XC⁆ ≤ XC := by
    rw [hXG, hXC, show (SemidirectProduct.inl : P →* P ⋊[φ] A).range
        = (⊤ : Subgroup P).map SemidirectProduct.inl from
        (MonoidHom.range_eq_map _), ← Subgroup.map_commutator]
    exact Subgroup.map_mono (Subgroup.commutator_le_right _ _)
  -- Step 2: `⁅⁅XG, XC⁆, YA⁆ = ⊥`.
  have h_step2 : ⁅⁅XG, XC⁆, YA⁆ = ⊥ :=
    le_bot_iff.mp <| le_trans (Subgroup.commutator_mono h_GC_le le_rfl) h_step1.le
  -- Three-subgroups (H₁ = YA, H₂ = XG, H₃ = XC): conclude `⁅⁅YA, XG⁆, XC⁆ = ⊥`.
  have h_three : ⁅⁅YA, XG⁆, XC⁆ = ⊥ := by
    have h_a : ⁅⁅XG, XC⁆, YA⁆ = ⊥ := h_step2
    have h_b : ⁅⁅XC, YA⁆, XG⁆ = ⊥ := by rw [h_step1, Subgroup.commutator_bot_left]
    exact Subgroup.commutator_commutator_eq_bot_of_rotate h_a h_b
  -- `⁅YA, XG⁆ = ⁅XG, YA⁆ = H_Γ`, so `⁅H_Γ, XC⁆ = ⊥`.
  have h_HΓ_XC : ⁅H_Γ, XC⁆ = ⊥ := by
    rwa [Subgroup.commutator_comm YA XG, ← hHΓ_def] at h_three
  -- Pull back via `inl`: `⁅actionCommutator φ, C⁆ = ⊥` in `P`.
  have h_pull : ⁅actionCommutator φ, C⁆ = ⊥ := by
    apply Subgroup.map_injective (f := (SemidirectProduct.inl : P →* P ⋊[φ] A))
      SemidirectProduct.inl_injective
    rw [Subgroup.map_commutator, h_HΓ_eq, Subgroup.map_bot]
    exact h_HΓ_XC
  rw [← Subgroup.commutator_eq_bot_iff_le_centralizer]
  exact h_pull

/-- **Gorenstein "Finite Groups" Theorem 5.3.11, (iii) ⇒ (iv)** (`S3`). A
`p'`-automorphism group `A` of a `p`-group `P` (`p` odd) acting trivially on a
critical subgroup `C` acts trivially on all of `P`: `actionCommutator φ = ⊥`.

More precisely only the characteristic and self-centralizing properties of `C` are
used (`IsCritical.characteristic` and `IsCritical.centralizer_eq`).

Proof: by `actionCommutator_le_centralizer_of_acts_trivially_of_characteristic`,
`actionCommutator φ ≤ C_P(C)`; by self-centrality `C_P(C) = Z(C)`-image `⊆ C`, so
`A` fixes `actionCommutator φ` pointwise (as it fixes `C`). Coprimality (`A` is
`p'`, `P` is a `p`-group) and solvability of `P` (`p`-group ⇒ nilpotent ⇒ solvable)
give `actionCommutator φ = ⊥` by the coprime collapse Lem 4.28 corollary. -/
theorem IsCritical.actionCommutator_eq_bot_of_acts_trivially
    {φ : A →* MulAut P} (_hp_odd : p ≠ 2) (hP : IsPGroup p P)
    (hA_p' : ¬ p ∣ Nat.card A) {C : Subgroup P} (hC : IsCritical C)
    (h_triv : (C : Set P) ⊆ Subgroup.fixedPointsOfMulAut φ) :
    actionCommutator φ = ⊥ := by
  have : C.Characteristic := hC.characteristic
  -- `actionCommutator φ ≤ C_P(C) = Z(C)-image ⊆ C`.
  have h_le_cent : actionCommutator φ ≤ Subgroup.centralizer (C : Set P) :=
    actionCommutator_le_centralizer_of_acts_trivially_of_characteristic hC.characteristic h_triv
  have h_cent_le_C : Subgroup.centralizer (C : Set P) ≤ C := by
    rw [hC.centralizer_eq]
    rintro _ ⟨z, _, rfl⟩
    exact z.2
  have h_ac_le_C : actionCommutator φ ≤ C := le_trans h_le_cent h_cent_le_C
  -- `A` fixes `actionCommutator φ` pointwise (it fixes `C ⊇ actionCommutator φ`).
  have h_triv_ac : ∀ a : A, ∀ h ∈ actionCommutator φ, (φ a) h = h := by
    intro a h hh
    exact h_triv (h_ac_le_C hh) a
  -- Coprimality of `|A|` and `|P|` (`P` is a `p`-group, `p ∤ |A|`).
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := p) (G := P)).mp hP
  have hCop : Nat.Coprime (Nat.card A) (Nat.card P) := by
    rw [hk]
    exact (Nat.Coprime.pow_right k
      ((Fact.out (p := p.Prime)).coprime_iff_not_dvd.mpr hA_p').symm)
  -- `P` is solvable (`p`-group ⇒ nilpotent ⇒ solvable).
  have : Group.IsNilpotent P := hP.isNilpotent
  have : Group.IsSolvable P := inferInstance
  exact actionCommutator_eq_bot_of_acts_trivially_on_self_of_coprime hCop (Or.inr inferInstance)
    h_triv_ac

end Faithful

section AutFixer

open OddOrder.Isaacs.Ch04

variable {P : Type*} [Group P] [Finite P] {p : ℕ} [Fact p.Prime]

/-- The subgroup of `MulAut P` consisting of automorphisms that fix every element
of order dividing `p` (equivalently every element of `Ω₁(P)` in the abelian case).
For a critical subgroup `C`, the relevant fixers of `Ω₁(C)` embed here via the
faithfulness property. -/
def autFixerOfOrderP (P : Type*) [Group P] (p : ℕ) : Subgroup (MulAut P) where
  carrier := {ψ : MulAut P | ∀ g : P, g ^ p = 1 → ψ g = g}
  one_mem' := fun _ _ => rfl
  mul_mem' := fun {ψ χ} hψ hχ g hg => by
    change ψ (χ g) = g
    rw [hχ g hg, hψ g hg]
  inv_mem' := fun {ψ} hψ g hg => by
    -- `ψ⁻¹ g = g` since `ψ g = g`: apply `ψ⁻¹` to `ψ g = g`.
    have h := hψ g hg
    have h2 := congrArg (ψ⁻¹ : MulAut P) h
    rw [MulAut.inv_apply_self P ψ g] at h2
    exact h2.symm

omit [Finite P] [Fact p.Prime] in
@[simp]
theorem mem_autFixerOfOrderP {ψ : MulAut P} :
    ψ ∈ autFixerOfOrderP P p ↔ ∀ g : P, g ^ p = 1 → ψ g = g := Iff.rfl

/-- A finite subgroup `A` of `autFixerOfOrderP P p` whose order is prime to `p`
acts trivially, hence is the trivial subgroup. This is the contrapositive of
Gorenstein 5.3.10 restricted to a single subgroup, powered by
`isaacs_thm_4_36`. -/
theorem autFixerOfOrderP.eq_bot_of_not_dvd_card (hp_odd : p ≠ 2) (hP : IsPGroup p P)
    {A : Subgroup (MulAut P)} [Finite A] (hA_le : A ≤ autFixerOfOrderP P p)
    (hA_p' : ¬ p ∣ Nat.card A) : A = ⊥ := by
  -- `φ : A →* MulAut P` is the inclusion. Each `a : A` fixes every order-`p` element.
  set φ : A →* MulAut P := A.subtype with hφ_def
  have h_fix : ∀ g : P, g ^ p = 1 → ∀ a : A, (φ a) g = g := by
    intro g hg a
    exact hA_le a.2 g hg
  -- Engine: `isaacs_thm_4_36` gives `actionCommutator φ = ⊥`, i.e. `A` acts trivially.
  have h_triv := actionCommutator_eq_bot_iff_acts_trivially φ
    |>.mp (isaacs_thm_4_36 hp_odd φ hP hA_p' h_fix)
  -- Each `a ∈ A` acts as the identity automorphism, hence `a = 1`.
  rw [eq_bot_iff]
  intro a ha
  rw [Subgroup.mem_bot]
  refine MulEquiv.ext fun g => ?_
  -- `(φ ⟨a, ha⟩) g = a g` and `h_triv` gives `a g = g = (1 : MulAut P) g`.
  rw [MulAut.one_apply]
  exact h_triv ⟨a, ha⟩ g

/-- **Gorenstein "Finite Groups" Theorem 5.3.10** (packaged, `S7`). For `p` odd,
the group of automorphisms of a `p`-group `P` fixing every order-`p` element is a
`p`-group: `autFixerOfOrderP P p` is a `p`-group.

Equivalently, every `p'`-automorphism of `P` acting trivially on the elements of
order dividing `p` is trivial. This is the source of property (d) of a critical
subgroup once combined with the faithfulness property `S3`.

Proof: were a prime `q ≠ p` to divide the order, Cauchy would give an order-`q`
element `ψ`; then `A = ⟨ψ⟩` has order `q` prime to `p`, so `A = ⊥` by
`eq_bot_of_not_dvd_card`, contradicting `ψ ≠ 1`. Hence the order is a `p`-power. -/
theorem isPGroup_autFixerOfOrderP (hp_odd : p ≠ 2) (hP : IsPGroup p P) :
    IsPGroup p (autFixerOfOrderP P p) := by
  -- Suffices: every element has `p`-power order (`IsPGroup.iff_orderOf`).
  rw [IsPGroup.iff_orderOf]
  intro ψ
  -- Let `n = orderOf ψ`; show `n` is a `p`-power by ruling out other prime divisors.
  by_contra hψ
  simp only [not_exists] at hψ
  -- `n ≠ 0` and `n` is not a `p`-power; so some prime `q ≠ p` divides `n`.
  have hn0 : orderOf ψ ≠ 0 := by
    intro h0
    -- `orderOf = 0` impossible in a finite group.
    have : Finite (autFixerOfOrderP P p) := Subtype.finite
    exact (orderOf_pos ψ).ne' h0
  -- The `p'`-part `b := ordCompl[p] (orderOf ψ)` is `> 1` (else `n` is a `p`-power).
  set n := orderOf ψ with hn_def
  set b := ordCompl[p] n with hb_def
  have hb_pos : 0 < b := Nat.ordCompl_pos p hn0
  have hb_cop : ¬ p ∣ b := Nat.not_dvd_ordCompl (Fact.out (p := p.Prime)) hn0
  have hb_ne_one : b ≠ 1 := by
    intro hb1
    -- `n = p ^ (n.factorization p) * b = p ^ _ * 1`, a `p`-power.
    have hnpow : n = p ^ (n.factorization p) := by
      conv_lhs => rw [← Nat.ordProj_mul_ordCompl_eq_self n p, ← hb_def, hb1, mul_one]
    exact hψ (n.factorization p) hnpow
  -- `σ := ψ ^ (ordProj[p] n)` has order `b` (the `p'`-part).
  set σ : autFixerOfOrderP P p := ψ ^ (ordProj[p] n) with hσ_def
  have hσ_ord : orderOf σ = b := by
    rw [hσ_def, hb_def, orderOf_pow_of_dvd (Nat.ordProj_pos n p).ne' (Nat.ordProj_dvd n p)]
  -- `A := zpowers σ` has card `b`, coprime to `p`, and lies in the fixer.
  set A : Subgroup (autFixerOfOrderP P p) := Subgroup.zpowers σ with hA_def
  have : Finite A := Subtype.finite
  have hAcard : Nat.card A = b := by rw [hA_def, Nat.card_zpowers, hσ_ord]
  -- Map `A` into `MulAut P` via the fixer's `subtype`; the image lies in the fixer.
  set Aimg : Subgroup (MulAut P) := A.map (autFixerOfOrderP P p).subtype with hAimg_def
  have hAimg_le : Aimg ≤ autFixerOfOrderP P p := by
    rw [hAimg_def]
    rintro _ ⟨x, _, rfl⟩
    exact x.property
  have : Finite Aimg := Subtype.finite
  have hAimg_card : Nat.card Aimg = b := by
    rw [hAimg_def, Nat.card_congr (Subgroup.equivMapOfInjective A _
      (autFixerOfOrderP P p).subtype_injective).symm.toEquiv, hAcard]
  -- `Aimg = ⊥` by the helper (order `b` prime to `p`).
  have hAimg_bot : Aimg = ⊥ :=
    autFixerOfOrderP.eq_bot_of_not_dvd_card hp_odd hP hAimg_le (hAimg_card ▸ hb_cop)
  -- But `σ ≠ 1` (order `b > 1`), and `(subtype σ) ∈ Aimg`, contradiction.
  have hσ_ne : σ ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hσ_ord
    exact hb_ne_one hσ_ord.symm
  have hmem : ((autFixerOfOrderP P p).subtype σ) ∈ Aimg :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_zpowers σ)
  rw [hAimg_bot, Subgroup.mem_bot] at hmem
  exact hσ_ne ((autFixerOfOrderP P p).subtype_injective (by
    rw [hmem]; rfl))

end AutFixer

section Omega1Critical

open scoped commutatorElement

variable {P : Type*} [Group P]

/-- **Class `≤ 2` is inherited by subgroups.** If `K ≤ L` are subgroups of `P` and
`L` has class `≤ 2` (`⁅L, L⁆ ≤ Z(L)`, i.e. `commutator ↥L ≤ center ↥L`), then so
does `K`. Used for `S5` with `K = Ω₁(C) ≤ C = L`.

Proof: in `P`, `Z(L)`-image centralizes `L`, so `⁅L, L⁆` centralizes `L ⊇ K`;
hence `⁅K, K⁆ ≤ ⁅L, L⁆` centralizes `K`, i.e. `commutator ↥K ≤ center ↥K`. -/
theorem commutator_le_center_of_le_of_class_le_two {K L : Subgroup P} (hKL : K ≤ L)
    (hL : _root_.commutator ↥L ≤ Subgroup.center ↥L) :
    _root_.commutator ↥K ≤ Subgroup.center ↥K := by
  -- `⁅L, L⁆ ≤ centralizer L` (central elements of `L` commute with `L`).
  have hLL_cent : ⁅L, L⁆ ≤ Subgroup.centralizer (L : Set P) := by
    rw [← L.map_subtype_commutator]
    rintro _ ⟨c, hc, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro x hx
    -- `c ∈ center ↥L` commutes with `⟨x, hx⟩ : ↥L`.
    have := Subgroup.mem_center_iff.mp (hL hc) ⟨x, hx⟩
    exact congrArg Subtype.val this
  -- `⁅K, K⁆ ≤ centralizer K`.
  have hKK_cent : ⁅K, K⁆ ≤ Subgroup.centralizer (K : Set P) := by
    refine le_trans (Subgroup.commutator_mono hKL hKL) ?_
    refine le_trans hLL_cent ?_
    exact Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hKL)
  -- Translate back to `center ↥K`: every element of `⁅K, K⁆` is in `K` and central in `K`.
  rw [← K.map_subtype_le_map_subtype, K.map_subtype_commutator]
  intro x hx
  have hxK : x ∈ K := K.commutator_le_self hx
  rw [Subgroup.mem_map]
  refine ⟨⟨x, hxK⟩, ?_, rfl⟩
  rw [Subgroup.mem_center_iff]
  intro k
  apply Subtype.ext
  -- `x` centralizes `K ∋ k`: goal reduces to `↑k * x = x * ↑k`.
  rw [Subgroup.coe_mul, Subgroup.coe_mul]
  exact Subgroup.mem_centralizer_iff.mp (hKK_cent hx) (k : P) k.2

variable {p : ℕ}

/-- `H = Ω₁(C)` as an ambient subgroup of `P`: the image of `Omega ↥C p 1` under
`C.subtype`. -/
def omega1Map (C : Subgroup P) (p : ℕ) : Subgroup P :=
  (Omega ↥C p 1).map C.subtype

theorem omega1Map_le {C : Subgroup P} : omega1Map C p ≤ C := by
  rw [omega1Map]; exact Subgroup.map_subtype_le _

/-- **`S4`**: `H = Ω₁(C)` is characteristic in `P` (char-in-char: `Ω₁(C)` char `C`,
`C` char `P`). -/
theorem IsCritical.omega1Map_characteristic {C : Subgroup P} (hC : IsCritical C) :
    (omega1Map C p).Characteristic :=
  characteristic_map_subtype_of_characteristic hC.characteristic Omega.characteristic

/-- **`S5`**: `H = Ω₁(C)` has class `≤ 2` (inherited from `C`). -/
theorem IsCritical.omega1Map_class_le_two {C : Subgroup P} (hC : IsCritical C) :
    _root_.commutator ↥(omega1Map C p) ≤ Subgroup.center ↥(omega1Map C p) :=
  commutator_le_center_of_le_of_class_le_two omega1Map_le hC.commutator_le_center

/-- **`S8`** (BG Theorem 1.13, property (a)). `[P, H] ⊆ Z(H)` for `H = Ω₁(C)`.

Proof (BG, mmd L468): `⁅⊤, H⁆ ⊆ ⁅⊤, C⁆ ∩ H ⊆ Z(C) ∩ H ⊆ Z(H)`. Concretely, any
`⁅g, h⁆` with `h ∈ H ⊆ C` lies in `H` (normality of `H`) and is central in `C`
(`hC.commutator_top_le_center`); an element of `H` central in `C ⊇ H` is central
in `H`. -/
theorem IsCritical.commutator_top_le_center_omega1Map {C : Subgroup P} (hC : IsCritical C) :
    ⁅(⊤ : Subgroup P), omega1Map C p⁆ ≤
      (Subgroup.center ↥(omega1Map C p)).map (omega1Map C p).subtype := by
  have : (omega1Map C p).Characteristic := hC.omega1Map_characteristic
  set H := omega1Map C p with hH_def
  -- `⁅⊤, H⁆ ≤ H` (H normal) and `⁅⊤, H⁆ ≤ ⁅⊤, C⁆`.
  have hCH_H : ⁅(⊤ : Subgroup P), H⁆ ≤ H := Subgroup.commutator_le_right _ _
  have hCH_C : ⁅(⊤ : Subgroup P), H⁆ ≤ ⁅(⊤ : Subgroup P), C⁆ :=
    Subgroup.commutator_mono le_rfl omega1Map_le
  -- Each element of `⁅⊤, H⁆` is in `H` and central in `C` (hence in `H`).
  intro x hx
  have hxH : x ∈ H := hCH_H hx
  -- `x ∈ ⁅⊤, C⁆ ≤ (center ↥C).map C.subtype`, so `x` is central in `C`.
  have hxZC : x ∈ (Subgroup.center ↥C).map C.subtype := hC.commutator_top_le_center (hCH_C hx)
  rw [Subgroup.mem_map] at hxZC
  obtain ⟨z, hz_center, hz_eq⟩ := hxZC
  simp only [Subgroup.coe_subtype] at hz_eq
  -- `x` commutes with all of `C ⊇ H`.
  have hx_comm : ∀ c ∈ C, x * c = c * x := by
    intro c hc
    have := Subgroup.mem_center_iff.mp hz_center ⟨c, hc⟩
    have := congrArg (Subtype.val) this
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hz_eq] at this
    exact this.symm
  -- Hence `x` is central in `H`.
  rw [Subgroup.mem_map]
  refine ⟨⟨x, hxH⟩, ?_, rfl⟩
  rw [Subgroup.mem_center_iff]
  intro k
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul]
  exact (hx_comm (k : P) (omega1Map_le k.2)).symm

variable [Finite P] [Fact p.Prime]

omit [Finite P] in
/-- A critical subgroup of a nontrivial `p`-group is itself nontrivial: if `C = ⊥`
then `C_P(C) = ⊤` but self-centrality forces `C_P(C) = Z(⊥)`-image `= ⊥`, so
`⊤ = ⊥`, contradicting `Nontrivial P`. -/
theorem IsCritical.ne_bot [Nontrivial P] {C : Subgroup P} (hC : IsCritical C) : C ≠ ⊥ := by
  intro hbot
  -- `centralizer ⊥ = ⊤`, but `hC.centralizer_eq` makes it `(center ↥⊥).map subtype = ⊥`.
  have h1 : Subgroup.centralizer (C : Set P) = ⊤ := by
    rw [hbot]; simp [Subgroup.centralizer_eq_top_iff_subset]
  have h2 : Subgroup.centralizer (C : Set P) = ⊥ := by
    rw [hC.centralizer_eq, hbot]
    rw [eq_bot_iff]
    rintro _ ⟨z, _, rfl⟩
    have : (z : (⊥ : Subgroup P)) = 1 := Subsingleton.elim _ _
    simp [this]
  rw [h1] at h2
  exact (bot_ne_top h2.symm)

/-- `Ω₁(C)` is nontrivial for a critical subgroup `C` of a nontrivial finite
`p`-group: `C` is a nontrivial `p`-group, so by Cauchy it has an order-`p` element,
which lies in `Omega ↥C p 1`. -/
theorem IsCritical.omega1_nontrivial [Nontrivial P] {C : Subgroup P}
    (hG : IsPGroup p P) (hC : IsCritical C) : Nontrivial ↥(Omega ↥C p 1) := by
  have : Nontrivial ↥C := (Subgroup.nontrivial_iff_ne_bot C).mpr hC.ne_bot
  have hCp : IsPGroup p ↥C := hG.to_subgroup C
  -- `p ∣ |↥C|`.
  obtain ⟨n, hn0, hn⟩ := hCp.nontrivial_iff_card.mp inferInstance
  have hdvd : p ∣ Nat.card ↥C := hn ▸ dvd_pow_self p hn0.ne'
  -- Cauchy: an order-`p` element of `↥C`.
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := ↥C) p hdvd
  have hg1 : g ^ p = 1 := by rw [← hg]; exact pow_orderOf_eq_one g
  have hg_ne : g ≠ 1 := by
    intro h; rw [h, orderOf_one] at hg; exact (Fact.out (p := p.Prime)).one_lt.ne hg
  -- `g ∈ Omega ↥C p 1`.
  have hg_mem : g ∈ Omega ↥C p 1 := Omega.mem_of_pow_eq_one (by rw [pow_one]; exact hg1)
  exact ⟨⟨⟨g, hg_mem⟩, 1, fun h => hg_ne (by simpa using congrArg Subtype.val h)⟩⟩

/-- **`S6`** (BG Theorem 1.13, property (c)). `H = Ω₁(C)` has exponent `p` (for `p`
odd). Transfers `Omega.exponent_eq_of_class_le_two` along the iso
`↥(omega1Map C p) ≃* Omega ↥C p 1`. -/
theorem IsCritical.exponent_omega1Map [Nontrivial P] (hp_odd : p ≠ 2)
    (hG : IsPGroup p P) {C : Subgroup P} (hC : IsCritical C) :
    Monoid.exponent ↥(omega1Map C p) = p := by
  have : Nontrivial ↥(Omega ↥C p 1) := hC.omega1_nontrivial hG
  -- exponent of `Omega ↥C p 1` is `p`.
  have hexp : Monoid.exponent ↥(Omega ↥C p 1) = p :=
    Omega.exponent_eq_of_class_le_two (Nat.Prime.odd_of_ne_two (Fact.out (p := p.Prime)) hp_odd)
      hC.commutator_le_center
  -- transfer along the iso `↥(omega1Map C p) ≃* Omega ↥C p 1`.
  rw [omega1Map, Monoid.exponent_eq_of_mulEquiv
    (Subgroup.equivMapOfInjective (Omega ↥C p 1) C.subtype C.subtype_injective).symm]
  exact hexp

open OddOrder.Isaacs.Ch04

/-- `C_{Aut P}(H)`: the automorphisms of `P` fixing every element of `H` pointwise. -/
def autCentralizer (H : Subgroup P) : Subgroup (MulAut P) where
  carrier := {ψ : MulAut P | ∀ h ∈ H, ψ h = h}
  one_mem' := fun _ _ => rfl
  mul_mem' := fun {ψ χ} hψ hχ h hh => by
    change ψ (χ h) = h
    rw [hχ h hh, hψ h hh]
  inv_mem' := fun {ψ} hψ h hh => by
    have hh' := hψ h hh
    have h2 := congrArg (ψ⁻¹ : MulAut P) hh'
    rw [MulAut.inv_apply_self P ψ h] at h2
    exact h2.symm

omit [Finite P] in
@[simp]
theorem mem_autCentralizer {H : Subgroup P} {ψ : MulAut P} :
    ψ ∈ autCentralizer H ↔ ∀ h ∈ H, ψ h = h := Iff.rfl

/-- A finite subgroup `A` of `C_{Aut P}(Ω₁(C))` with order prime to `p` acts
trivially on `P`, hence is the trivial subgroup. Chain: `A` fixes `Ω₁(C)` ⇒ `A`
fixes every order-`p` element of `C` ⇒ (`isaacs_thm_4_36`) `A` acts trivially on
`C` ⇒ (faithfulness `S3`) `A` acts trivially on `P` ⇒ `A = ⊥`. -/
theorem autCentralizer.eq_bot_of_not_dvd_card (hp_odd : p ≠ 2) (hG : IsPGroup p P)
    {C : Subgroup P} (hC : IsCritical C)
    {A : Subgroup (MulAut P)} [Finite A] (hA_le : A ≤ autCentralizer (omega1Map C p))
    (hA_p' : ¬ p ∣ Nat.card A) : A = ⊥ := by
  have : C.Characteristic := hC.characteristic
  set φ : A →* MulAut P := A.subtype with hφ_def
  -- `C` is `A`-invariant (characteristic), so restrict the action to `↥C`.
  have hC_inv : OddOrder.Isaacs.Ch03.IsAInvariant φ C :=
    OddOrder.Isaacs.Ch03.IsAInvariant.of_characteristic φ
  set φC : A →* MulAut ↥C := hC_inv.restrict with hφC_def
  have hCp : IsPGroup p ↥C := hG.to_subgroup C
  -- `A` fixes every order-`p` element of `↥C` (such elements map into `Ω₁(C) = H`).
  have h_fix_C : ∀ g : ↥C, g ^ p = 1 → ∀ a : A, (φC a) g = g := by
    intro g hgp a
    -- `(g : P) ∈ omega1Map C p` since `g ^ p = 1` (so `g ∈ Omega ↥C p 1`).
    have hg_omega : g ∈ Omega ↥C p 1 := Omega.mem_of_pow_eq_one (by rw [pow_one]; exact hgp)
    have hgP_mem : (g : P) ∈ omega1Map C p :=
      Subgroup.mem_map_of_mem C.subtype hg_omega
    -- `a` fixes `(g : P)`.
    have h_fix : (φ a) (g : P) = (g : P) := hA_le a.2 (g : P) hgP_mem
    -- transfer to `↥C`.
    apply Subtype.ext
    rw [hC_inv.restrict_apply_val a g]
    exact h_fix
  -- `isaacs_thm_4_36`: `A` acts trivially on `↥C`.
  have h_triv_C_act : actionCommutator φC = ⊥ := isaacs_thm_4_36 hp_odd φC hCp hA_p' h_fix_C
  have h_triv_C : ∀ a : A, ∀ g : ↥C, (φC a) g = g :=
    (actionCommutator_eq_bot_iff_acts_trivially φC).mp h_triv_C_act
  -- `A` fixes `C` pointwise (as a subset of `P`).
  have h_triv_C_set : (C : Set P) ⊆ Subgroup.fixedPointsOfMulAut φ := by
    intro x hx a
    have := h_triv_C a ⟨x, hx⟩
    have := congrArg (Subtype.val) this
    rwa [hC_inv.restrict_apply_val a ⟨x, hx⟩] at this
  -- Faithfulness (`S3`): `A` acts trivially on `P`.
  have h_triv_P : actionCommutator φ = ⊥ :=
    hC.actionCommutator_eq_bot_of_acts_trivially hp_odd hG hA_p' h_triv_C_set
  have h_triv_P' : ∀ a : A, ∀ g : P, (φ a) g = g :=
    (actionCommutator_eq_bot_iff_acts_trivially φ).mp h_triv_P
  -- Each `a ∈ A` is the identity automorphism, so `A = ⊥`.
  rw [eq_bot_iff]
  intro a ha
  rw [Subgroup.mem_bot]
  refine MulEquiv.ext fun g => ?_
  rw [MulAut.one_apply]
  exact h_triv_P' ⟨a, ha⟩ g

/-- **BG Theorem 1.13, property (d)** (Gorenstein 5.3.13). For `p` odd and `C` a
critical subgroup of a finite `p`-group `P`, `C_{Aut P}(Ω₁(C))` is a `p`-group.

Proof (mirrors `isPGroup_autFixerOfOrderP`): if a prime `q ≠ p` divided the order,
Cauchy would give an order-`q` element `ψ`; its cyclic `p'`-part `A` would satisfy
`A = ⊥` by `eq_bot_of_not_dvd_card`, contradicting `ψ ≠ 1`. -/
theorem IsCritical.isPGroup_autCentralizer_omega1Map (hp_odd : p ≠ 2) (hG : IsPGroup p P)
    {C : Subgroup P} (hC : IsCritical C) :
    IsPGroup p (autCentralizer (omega1Map C p)) := by
  rw [IsPGroup.iff_orderOf]
  intro ψ
  by_contra hψ
  simp only [not_exists] at hψ
  have hn0 : orderOf ψ ≠ 0 := by
    intro h0
    have : Finite (autCentralizer (omega1Map C p)) := Subtype.finite
    exact (orderOf_pos ψ).ne' h0
  set n := orderOf ψ with hn_def
  set b := ordCompl[p] n with hb_def
  have hb_pos : 0 < b := Nat.ordCompl_pos p hn0
  have hb_cop : ¬ p ∣ b := Nat.not_dvd_ordCompl (Fact.out (p := p.Prime)) hn0
  have hb_ne_one : b ≠ 1 := by
    intro hb1
    have hnpow : n = p ^ (n.factorization p) := by
      conv_lhs => rw [← Nat.ordProj_mul_ordCompl_eq_self n p, ← hb_def, hb1, mul_one]
    exact hψ (n.factorization p) hnpow
  set σ : autCentralizer (omega1Map C p) := ψ ^ (ordProj[p] n) with hσ_def
  have hσ_ord : orderOf σ = b := by
    rw [hσ_def, hb_def, orderOf_pow_of_dvd (Nat.ordProj_pos n p).ne' (Nat.ordProj_dvd n p)]
  set A : Subgroup (autCentralizer (omega1Map C p)) := Subgroup.zpowers σ with hA_def
  have : Finite A := Subtype.finite
  have hAcard : Nat.card A = b := by rw [hA_def, Nat.card_zpowers, hσ_ord]
  set Aimg : Subgroup (MulAut P) := A.map (autCentralizer (omega1Map C p)).subtype with hAimg_def
  have hAimg_le : Aimg ≤ autCentralizer (omega1Map C p) := by
    rw [hAimg_def]
    rintro _ ⟨x, _, rfl⟩
    exact x.property
  have : Finite Aimg := Subtype.finite
  have hAimg_card : Nat.card Aimg = b := by
    rw [hAimg_def, Nat.card_congr (Subgroup.equivMapOfInjective A _
      (autCentralizer (omega1Map C p)).subtype_injective).symm.toEquiv, hAcard]
  have hAimg_bot : Aimg = ⊥ :=
    autCentralizer.eq_bot_of_not_dvd_card hp_odd hG hC hAimg_le (hAimg_card ▸ hb_cop)
  have hσ_ne : σ ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hσ_ord
    exact hb_ne_one hσ_ord.symm
  have hmem : ((autCentralizer (omega1Map C p)).subtype σ) ∈ Aimg :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_zpowers σ)
  rw [hAimg_bot, Subgroup.mem_bot] at hmem
  exact hσ_ne ((autCentralizer (omega1Map C p)).subtype_injective (by
    rw [hmem]; rfl))

end Omega1Critical

end OddOrder.GroupTheory


