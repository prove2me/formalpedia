-- Prove2me | Definitions.Def_OddOrder_BG_Ch2_Uniqueness_S08_FittingInGBasic
-- name    : OddOrder_BG_Ch2_Uniqueness_S08_FittingInGBasic
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T06:16:22.908645+00:00
-- url     : https://prove2.me/theorems/2245bc8d-9e0b-4b05-b95a-37229a9a61af
-- title:
--   BG §8: `fittingInG` and `cFittingInG`, definitions and basic API
-- statement:
--   The Fitting subgroup of a maximal subgroup $M$ viewed in $G$, the relative centralizer, their characteristic/normality transport, the conjugation action on `fittingInG`, and the first comparison lemmas (Bender–Glauberman §8).
--
--   Main definitions: `fittingInG` ($F(M)$ realized as a subgroup of $G$), `cFittingInG` (the relative centralizer $C_{F(M)}(A_0)$) and `conjActionOnFittingInG` (the conjugation action of $\langle x\rangle$ on $F(M)$ for $x\in M$).
--
--   The bundle also proves 18 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/Ch2_Uniqueness/S08_FittingInGBasic.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/BG/Ch2_Uniqueness/S08_FittingInGBasic.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_BG_Ch2_Uniqueness_Setup
import Definitions.Def_OddOrder_BG_Ch2_Uniqueness_S07_Transitivity
import Definitions.Def_OddOrder_BG_AppB_Thm62
import Definitions.Def_OddOrder_GroupTheory_SubgroupInAmbient
import Definitions.Def_OddOrder_GroupTheory_MaximalSubgroup
import Definitions.Def_OddOrder_GroupTheory_SCN
import Definitions.Def_OddOrder_GroupTheory_PRank
import Definitions.Def_OddOrder_GroupTheory_ElementaryAbelian
import Definitions.Def_OddOrder_Isaacs_Ch01_Sylow_Main

namespace OddOrder.BG.Ch2.S08

open OddOrder.GroupTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

/-- `F(M)` (maximal subgroup `M` の Fitting 部分群) を `G` 内の部分群として実現したもの。 -/
def fittingInG (M : Subgroup G) : Subgroup G :=
  (Ch01.fitting ↥M).map M.subtype

/-- `F(M)`, realized in `G`, lies inside `M`. -/
theorem fittingInG_le (M : Subgroup G) : fittingInG M ≤ M :=
  Subgroup.map_subtype_le _

/-- The ambient q-core `O_q(M)` lies inside `F(M)`. -/
theorem opiCoreInG_singleton_le_fittingInG [Finite G] {q : ℕ} [Fact q.Prime]
    (M : Subgroup G) :
    opiCoreInG ({q} : Set ℕ) M ≤ fittingInG M := by
  rw [opiCoreInG, fittingInG]
  refine Subgroup.map_mono ?_
  rw [OddOrder.Isaacs.Ch04.oPiCore_singleton_eq_opCore (G := ↥M) q]
  exact Ch01.opCore_le_fitting ⟨q, Fact.out⟩ ↥M

/-- A normal ambient q-subgroup of `M` lies inside `F(M)`. -/
theorem le_fittingInG_of_normal_isPiSubgroup_singleton [Finite G]
    {q : ℕ} [Fact q.Prime] {M Q : Subgroup G}
    (hQM : Q ≤ M) (hQnorm : (Q.subgroupOf M).Normal)
    (hQpi : Subgroup.IsPiSubgroup ({q} : Set ℕ) Q) :
    Q ≤ fittingInG M :=
  (le_opiCoreInG_of_normal_of_isPiSubgroup hQM hQnorm hQpi).trans
    (opiCoreInG_singleton_le_fittingInG M)

/-- The relative centralizer C_{F(M)}(A0), realized in the ambient group G. -/
def cFittingInG (M A0 : Subgroup G) : Subgroup G :=
  Subgroup.centralizer (A0 : Set G) ⊓ fittingInG M

/-- Realizing `F(M)` in `G` and then restricting back to `M` recovers the original
Fitting subgroup of the group `↥M`. -/
theorem fittingInG_subgroupOf_eq (M : Subgroup G) :
    (fittingInG M).subgroupOf M = Ch01.fitting ↥M := by
  ext x
  rw [Subgroup.mem_subgroupOf, fittingInG, Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, hy_eq⟩
    have hyx : y = x := Subtype.ext hy_eq
    rwa [← hyx]
  · intro hx
    exact ⟨x, hx, rfl⟩

/-- Ambient form of BG Proposition 1.3 for a subgroup M: elements of M centralizing
F(M) lie in F(M). -/
theorem mem_fittingInG_of_mem_centralizer_fittingInG [Finite G] {M : Subgroup G}
    [Group.IsSolvable ↥M] {x : G} (hxM : x ∈ M)
    (hxC : x ∈ Subgroup.centralizer (fittingInG M : Set G)) :
    x ∈ fittingInG M := by
  have hxC_M : (⟨x, hxM⟩ : ↥M) ∈
      Subgroup.centralizer ((Ch01.fitting ↥M : Subgroup ↥M) : Set ↥M) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    apply Subtype.ext
    have hyF : (y : G) ∈ fittingInG M := by
      have hySub : y ∈ (fittingInG M).subgroupOf M := by
        rwa [fittingInG_subgroupOf_eq M]
      exact Subgroup.mem_subgroupOf.mp hySub
    exact Subgroup.mem_centralizer_iff.mp hxC (y : G) hyF
  have hxF_M : (⟨x, hxM⟩ : ↥M) ∈ Ch01.fitting ↥M :=
    OddOrder.GroupTheory.centralizer_fitting_le_fitting hxC_M
  have hxSub : (⟨x, hxM⟩ : ↥M) ∈ (fittingInG M).subgroupOf M := by
    rwa [fittingInG_subgroupOf_eq M]
  exact Subgroup.mem_subgroupOf.mp hxSub

/-- Subgroup form of the ambient self-centralizing property for F(M). -/
theorem centralizer_fittingInG_inf_le_fittingInG [Finite G] {M : Subgroup G}
    [Group.IsSolvable ↥M] :
    Subgroup.centralizer (fittingInG M : Set G) ⊓ M ≤ fittingInG M := by
  intro x hx
  exact mem_fittingInG_of_mem_centralizer_fittingInG hx.2 hx.1

/-- If x lies in F(M) and generates a pi(F(M))-complement subgroup, then x is trivial. -/
theorem eq_one_of_mem_fittingInG_of_zpowers_isPiSubgroup_primesOf_compl [Finite G]
    {M : Subgroup G} {x : G} (hxF : x ∈ fittingInG M)
    (hxpi : Subgroup.IsPiSubgroup (OddOrder.BG.Ch2.S07.primesOf (fittingInG M))ᶜ
      (Subgroup.zpowers x)) :
    x = 1 :=
  eq_one_of_mem_of_isPiSubgroup_of_zpowers_isPiSubgroup_compl
    (π := OddOrder.BG.Ch2.S07.primesOf (fittingInG M)) (H := fittingInG M)
    (fun r hr => by simpa [OddOrder.BG.Ch2.S07.primesOf] using hr) hxF hxpi

/-- `F(M)`, viewed as a subgroup of `M`, is characteristic. -/
theorem fittingInG_subgroupOf_characteristic (M : Subgroup G) :
    ((fittingInG M).subgroupOf M).Characteristic := by
  rw [fittingInG_subgroupOf_eq]
  exact Ch01.fitting.characteristic ↥M

/-- `F(M)`, viewed as a subgroup of `M`, is normal. -/
theorem fittingInG_subgroupOf_normal (M : Subgroup G) :
    ((fittingInG M).subgroupOf M).Normal := by
  rw [fittingInG_subgroupOf_eq]
  exact Ch01.fitting.normal ↥M

/-- Any element of M normalizes F(M), viewed in the ambient group G. -/
theorem mem_normalizer_fittingInG_of_mem {M : Subgroup G} {x : G} (hxM : x ∈ M) :
    x ∈ Subgroup.normalizer (fittingInG M : Set G) := by
  have hM_norm_F : M ≤ Subgroup.normalizer (fittingInG M : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (fittingInG_le M)).mp
      (fittingInG_subgroupOf_normal M)
  exact hM_norm_F hxM

/-- The cyclic subgroup generated by an element of M normalizes F(M). -/
theorem zpowers_le_normalizer_fittingInG_of_mem {M : Subgroup G} {x : G} (hxM : x ∈ M) :
    Subgroup.zpowers x ≤ Subgroup.normalizer (fittingInG M : Set G) :=
  Subgroup.zpowers_le.mpr (mem_normalizer_fittingInG_of_mem hxM)

/-- Conjugation action of the cyclic subgroup generated by x on F(M), for x in M. -/
def conjActionOnFittingInG {M : Subgroup G} {x : G} (hxM : x ∈ M) :
    ↥(Subgroup.zpowers x) →* MulAut ↥(fittingInG M) :=
  (fittingInG M).normalizerMonoidHom.comp
    (Subgroup.inclusion (zpowers_le_normalizer_fittingInG_of_mem hxM))

/-- The action on F(M) above is ambient conjugation. -/
theorem conjActionOnFittingInG_apply {M : Subgroup G} {x : G} (hxM : x ∈ M)
    (a : ↥(Subgroup.zpowers x)) (f : ↥(fittingInG M)) :
    ((conjActionOnFittingInG hxM a) f : G) = (a : G) * (f : G) * (a : G)⁻¹ := by
  rw [conjActionOnFittingInG]
  rfl

/-- Fixed points of the cyclic conjugation action on F(M) are the elements of F(M)
centralizing the cyclic subgroup. -/
theorem fixedPoints_conjActionOnFittingInG_eq {M : Subgroup G} {x : G} (hxM : x ∈ M) :
    Subgroup.fixedPointsOfMulAut (conjActionOnFittingInG hxM) =
      (Subgroup.centralizer (Subgroup.zpowers x : Set G) ⊓ fittingInG M).subgroupOf
        (fittingInG M) := by
  ext f
  constructor
  · intro hf
    rw [Subgroup.mem_subgroupOf]
    refine ⟨?_, f.2⟩
    refine Subgroup.mem_centralizer_iff.mpr ?_
    intro y hy
    have hfix := Subgroup.mem_fixedPointsOfMulAut.mp hf ⟨y, hy⟩
    have hfixG := congrArg Subtype.val hfix
    rw [conjActionOnFittingInG_apply] at hfixG
    calc y * (f : G) = (y * (f : G) * y⁻¹) * y := by group
      _ = (f : G) * y := by rw [hfixG]
  · intro hf
    rw [Subgroup.mem_fixedPointsOfMulAut]
    intro a
    apply Subtype.ext
    rw [conjActionOnFittingInG_apply]
    have hfcent : (f : G) ∈ Subgroup.centralizer (Subgroup.zpowers x : Set G) :=
      (Subgroup.mem_subgroupOf.mp hf).1
    have hcomm : (a : G) * (f : G) = (f : G) * (a : G) :=
      Subgroup.mem_centralizer_iff.mp hfcent (a : G) a.2
    calc (a : G) * (f : G) * (a : G)⁻¹ = (f : G) * (a : G) * (a : G)⁻¹ := by rw [hcomm]
      _ = (f : G) := by group

/-- Ambient form of BG Proposition 1.4: if a coprime subgroup `B` normalizes a
finite solvable subgroup `N` and centralizes `F(N)`, then `B` centralizes `N`. -/
theorem le_centralizer_of_coprime_normalizes_of_le_centralizer_fittingInG
    [Finite G] {B N : Subgroup G} [Group.IsSolvable ↥N]
    (hBN : B ≤ Subgroup.normalizer (N : Set G))
    (hCop : Nat.Coprime (Nat.card ↥B) (Nat.card ↥N))
    (hBF : B ≤ Subgroup.centralizer (fittingInG N : Set G)) :
    B ≤ Subgroup.centralizer (N : Set G) := by
  let φ : ↥B →* MulAut ↥N :=
    N.normalizerMonoidHom.comp (Subgroup.inclusion hBN)
  have hφcoe : ∀ (b : ↥B) (n : ↥N),
      ((φ b) n : G) = (b : G) * (n : G) * (b : G)⁻¹ := by
    intro b n
    dsimp [φ]
    rfl
  have hF_le_fixed : Ch01.fitting ↥N ≤ Subgroup.fixedPointsOfMulAut φ := by
    intro f hf
    rw [Subgroup.mem_fixedPointsOfMulAut]
    intro b
    refine Subtype.ext ?_
    rw [hφcoe]
    have hfG : (f : G) ∈ fittingInG N := by
      have hfSub : f ∈ (fittingInG N).subgroupOf N := by
        rwa [fittingInG_subgroupOf_eq N]
      exact Subgroup.mem_subgroupOf.mp hfSub
    have hcomm : Commute (f : G) (b : G) :=
      Subgroup.mem_centralizer_iff.mp (hBF b.2) (f : G) hfG
    rw [hcomm.symm.eq, mul_assoc, mul_inv_cancel, mul_one]
  have hAC_bot : OddOrder.Isaacs.Ch04.actionCommutator φ = ⊥ :=
    OddOrder.BG.Ch1.S01.actionCommutator_eq_bot_of_fitting_le_fixedPoints
      hCop hF_le_fixed
  have htriv : ∀ b : ↥B, ∀ n : ↥N, (φ b) n = n :=
    (OddOrder.Isaacs.Ch04.actionCommutator_eq_bot_iff_acts_trivially φ).mp hAC_bot
  intro b hb
  rw [Subgroup.mem_centralizer_iff]
  intro n hn
  have hval := congrArg Subtype.val (htriv ⟨b, hb⟩ ⟨n, hn⟩)
  rw [hφcoe] at hval
  exact (mul_inv_eq_iff_eq_mul.mp hval).symm

/-- Fitting M, realized in G, is nilpotent. -/
theorem fittingInG_isNilpotent [Finite G] (M : Subgroup G) :
    Group.IsNilpotent ↥(fittingInG M) := by
  rw [fittingInG]
  have : Group.IsNilpotent ↥(Ch01.fitting ↥M) := Ch01.fitting.isNilpotent
  exact Group.nilpotent_of_mulEquiv (Subgroup.equivMapOfInjective (Ch01.fitting ↥M)
    M.subtype M.subtype_injective)

/-- An element normalizing `N` also normalizes the ambient realization of `F(N)`. -/
theorem mem_normalizer_fittingInG_of_mem_normalizer {N : Subgroup G} {x : G}
    (hxN : x ∈ Subgroup.normalizer (N : Set G)) :
    x ∈ Subgroup.normalizer (fittingInG N : Set G) := by
  have hforward : ∀ {z : G}, z ∈ Subgroup.normalizer (N : Set G) →
      ∀ y : G, y ∈ fittingInG N → z * y * z⁻¹ ∈ fittingInG N := by
    intro z hz y hy
    have hyN : y ∈ N := fittingInG_le N hy
    let φ : MulAut ↥N := N.normalizerMonoidHom ⟨z, hz⟩
    have hchar : ((fittingInG N).subgroupOf N).map (φ : ↥N →* ↥N) =
        (fittingInG N).subgroupOf N :=
      Subgroup.characteristic_iff_map_eq.mp (fittingInG_subgroupOf_characteristic N) φ
    have hySub : (⟨y, hyN⟩ : ↥N) ∈ (fittingInG N).subgroupOf N := by
      simpa [Subgroup.mem_subgroupOf] using hy
    have hmap : φ ⟨y, hyN⟩ ∈ ((fittingInG N).subgroupOf N).map (φ : ↥N →* ↥N) := by
      rw [Subgroup.mem_map]
      exact ⟨⟨y, hyN⟩, hySub, rfl⟩
    rw [hchar] at hmap
    have hmem : ((φ ⟨y, hyN⟩ : ↥N) : G) ∈ fittingInG N := by
      exact Subgroup.mem_subgroupOf.mp hmap
    simpa [φ] using hmem
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · exact hforward hxN y
  · intro hy
    have hxN_inv : x⁻¹ ∈ Subgroup.normalizer (N : Set G) :=
      (Subgroup.normalizer (N : Set G)).inv_mem hxN
    have hback : x⁻¹ * (x * y * x⁻¹) * (x⁻¹)⁻¹ ∈ fittingInG N :=
      hforward hxN_inv (x * y * x⁻¹) hy
    have hEq : x⁻¹ * (x * y * x⁻¹) * x = y := by group
    simpa [hEq] using hback

/-- If `N ≤ H` and `H` normalizes `N`, then the ambient realization of `F(N)`
lies in the ambient realization of `F(H)`. -/
theorem fittingInG_le_fittingInG_of_le_normalizer [Finite G] {N H : Subgroup G}
    (hNH : N ≤ H) (hHN : H ≤ Subgroup.normalizer (N : Set G)) :
    fittingInG N ≤ fittingInG H := by
  have hFN_H : fittingInG N ≤ H := (fittingInG_le N).trans hNH
  have hFN_norm_H : ((fittingInG N).subgroupOf H).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hFN_H]
    intro x hx
    exact mem_normalizer_fittingInG_of_mem_normalizer (hHN hx)
  have hFN_nilp_H : Group.IsNilpotent ↥((fittingInG N).subgroupOf H) := by
    have : Group.IsNilpotent ↥(fittingInG N) := fittingInG_isNilpotent N
    exact Group.nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hFN_H).symm
  have hSub_le_fitH : (fittingInG N).subgroupOf H ≤ Ch01.fitting ↥H := by
    have : ((fittingInG N).subgroupOf H).Normal := hFN_norm_H
    have : Group.IsNilpotent ↥((fittingInG N).subgroupOf H) := hFN_nilp_H
    exact Ch01.nilpotent_normal_le_fitting
  calc fittingInG N = ((fittingInG N).subgroupOf H).map H.subtype :=
        (Subgroup.map_subgroupOf_eq_of_le hFN_H).symm
    _ ≤ (Ch01.fitting ↥H).map H.subtype := Subgroup.map_mono hSub_le_fitH
    _ = fittingInG H := rfl

/-- BG (8.7) Fitting-core bridge: `F(O_{p'}(H))` lies in `O_{p'}(F(H))`. -/
theorem fittingInG_opiCoreInG_singleton_compl_le_opiCoreInG_singleton_compl_fittingInG
    [Finite G] {p : ℕ} [Fact p.Prime] (H : Subgroup G) :
    fittingInG (opiCoreInG ({p} : Set ℕ)ᶜ H) ≤
      opiCoreInG ({p} : Set ℕ)ᶜ (fittingInG H) := by
  let N : Subgroup G := opiCoreInG ({p} : Set ℕ)ᶜ H
  change fittingInG N ≤ opiCoreInG ({p} : Set ℕ)ᶜ (fittingInG H)
  have hN_H : N ≤ H := by
    dsimp [N]
    exact opiCoreInG_le ({p} : Set ℕ)ᶜ H
  have hH_norm_N : H ≤ Subgroup.normalizer (N : Set G) := by
    dsimp [N]
    exact le_normalizer_opiCoreInG ({p} : Set ℕ)ᶜ H
  have hFN_FH : fittingInG N ≤ fittingInG H :=
    fittingInG_le_fittingInG_of_le_normalizer hN_H hH_norm_N
  have hFN_norm_FH : ((fittingInG N).subgroupOf (fittingInG H)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hFN_FH]
    intro x hx
    have hxH : x ∈ H := fittingInG_le H hx
    exact mem_normalizer_fittingInG_of_mem_normalizer (hH_norm_N hxH)
  have hFN_pi : Subgroup.IsPiSubgroup ({p} : Set ℕ)ᶜ (fittingInG N) := by
    intro r hr
    exact isPiSubgroup_opiCoreInG ({p} : Set ℕ)ᶜ H r
      (Nat.primeFactors_mono (Subgroup.card_dvd_of_le (fittingInG_le N))
        Nat.card_pos.ne' hr)
  exact le_opiCoreInG_of_normal_of_isPiSubgroup hFN_FH hFN_norm_FH hFN_pi

end OddOrder.BG.Ch2.S08


