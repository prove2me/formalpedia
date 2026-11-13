-- Prove2me | Definitions.Def_OddOrder_BG_Ch2_Uniqueness_S08_CenterFittingOpcore
-- name    : OddOrder_BG_Ch2_Uniqueness_S08_CenterFittingOpcore
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T06:18:37.716196+00:00
-- url     : https://prove2.me/theorems/03c30069-2640-4d9f-aab4-35f61aa16241
-- title:
--   BG §8: center, Fitting subgroup and $O$-core of a maximal subgroup
-- statement:
--   Part of the Bender–Glauberman §8 development on the Fitting subgroup of a maximal subgroup.
--
--   Main definitions: `centerFittingInG` (the center of $F(M)$ in $G$), `centerFittingOpCoreInG` (the $q$-core of $Z(F(M))$) and `isMaxElemAbelianIn` (membership in $\mathcal{E}_p^*(H)$, a maximal $p$-elementary abelian subgroup of $H$).
--
--   The bundle also proves 72 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/Ch2_Uniqueness/S08_CenterFittingOpcore.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/BG/Ch2_Uniqueness/S08_CenterFittingOpcore.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_BG_Ch2_Uniqueness_S08_FittingInGBasic
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

/-- For a finite solvable subgroup `H`, its `π(F(H))`-complement core is trivial.

This is the ambient form of the BG §8 step `O_{σ'}(H)=1`, where `σ=π(F(H))`.
If the core were nontrivial, the Fitting subgroup of that normal solvable subgroup would
map to a nontrivial subgroup of both `F(H)` and the `σ`-complement core. -/
theorem opiCoreInG_primesOf_fittingInG_compl_eq_bot [Finite G]
    {H : Subgroup G} [Group.IsSolvable ↥H] :
    opiCoreInG (OddOrder.BG.Ch2.S07.primesOf (fittingInG H))ᶜ H = ⊥ := by
  classical
  let σ : Set ℕ := OddOrder.BG.Ch2.S07.primesOf (fittingInG H)
  let N : Subgroup G := opiCoreInG σᶜ H
  suffices N = ⊥ by simpa [N, σ]
  by_contra hN_ne_bot
  have hNH : N ≤ H := by
    dsimp [N]
    exact opiCoreInG_le σᶜ H
  let NH : Subgroup H := N.subgroupOf H
  have hNH_normal : NH.Normal := by
    dsimp [NH]
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hNH).mpr (by
      dsimp [N]
      exact le_normalizer_opiCoreInG σᶜ H)
  have hNH_ne_bot : NH ≠ ⊥ := by
    intro hbot
    apply hN_ne_bot
    have hmap : NH.map H.subtype = N := by
      dsimp [NH]
      exact Subgroup.map_subgroupOf_eq_of_le hNH
    rw [← hmap, hbot, Subgroup.map_bot]
  have hNH_nontrivial : Nontrivial ↥NH :=
    (Subgroup.nontrivial_iff_ne_bot NH).mpr hNH_ne_bot
  have hFNH_ne_bot : Ch01.fitting ↥NH ≠ ⊥ :=
    Ch01.fitting_ne_bot_of_isSolvable_nontrivial ↥NH
  let FNH : Subgroup H := (Ch01.fitting ↥NH).map NH.subtype
  have hFNH_ne_bot : FNH ≠ ⊥ := by
    intro hbot
    apply hFNH_ne_bot
    exact (Subgroup.map_eq_bot_iff_of_injective (Ch01.fitting ↥NH)
      NH.subtype_injective).mp hbot
  let B : Subgroup G := FNH.map H.subtype
  have hB_ne_bot : B ≠ ⊥ := by
    intro hbot
    apply hFNH_ne_bot
    exact (Subgroup.map_eq_bot_iff_of_injective FNH H.subtype_injective).mp hbot
  have hFNH_le_fittingH : FNH ≤ Ch01.fitting ↥H := by
    dsimp [FNH]
    exact Ch01.fitting_map_subtype_le_fitting
  have hB_le_fittingH : B ≤ fittingInG H := by
    dsimp [B, fittingInG]
    exact Subgroup.map_mono hFNH_le_fittingH
  have hFNH_le_NH : FNH ≤ NH := by
    dsimp [FNH]
    exact Subgroup.map_subtype_le _
  have hB_le_N : B ≤ N := by
    dsimp [B]
    calc FNH.map H.subtype
        ≤ NH.map H.subtype := Subgroup.map_mono hFNH_le_NH
      _ = N := by
        dsimp [NH]
        exact Subgroup.map_subgroupOf_eq_of_le hNH
  have hN_pi_compl : Subgroup.IsPiSubgroup σᶜ N := by
    dsimp [N]
    exact isPiSubgroup_opiCoreInG σᶜ H
  have hB_pi_compl : Subgroup.IsPiSubgroup σᶜ B := by
    intro r hr
    exact hN_pi_compl r
      (Nat.primeFactors_mono (Subgroup.card_dvd_of_le hB_le_N) Nat.card_pos.ne' hr)
  have hFittingH_pi : Subgroup.IsPiSubgroup σ (fittingInG H) := by
    intro r hr
    simpa [σ, OddOrder.BG.Ch2.S07.primesOf] using hr
  have hB_bot : B = ⊥ :=
    eq_bot_of_le_of_isPiSubgroup_of_isPiSubgroup_compl hB_le_fittingH hFittingH_pi
      hB_pi_compl
  exact hB_ne_bot hB_bot

/-- Ambient core commutation: `O_π(H)` centralizes `O_{π'}(H)` inside `H`.
This is the core form of the `[O_q(H), O_{q'}(H)] = 1` step used in BG (8.7). -/
theorem opiCoreInG_commutator_compl_eq_bot [Finite G]
    (π : Set ℕ) (H : Subgroup G) :
    ⁅opiCoreInG π H, opiCoreInG πᶜ H⁆ = ⊥ := by
  have hleft : ⁅opiCoreInG π H, opiCoreInG πᶜ H⁆ ≤ opiCoreInG π H :=
    OddOrder.Isaacs.Ch04.commutator_le_of_le_normalizer
      ((opiCoreInG_le πᶜ H).trans (le_normalizer_opiCoreInG π H))
  have hright : ⁅opiCoreInG π H, opiCoreInG πᶜ H⁆ ≤ opiCoreInG πᶜ H := by
    rw [Subgroup.commutator_comm]
    exact OddOrder.Isaacs.Ch04.commutator_le_of_le_normalizer
      ((opiCoreInG_le π H).trans (le_normalizer_opiCoreInG πᶜ H))
  have hinf : opiCoreInG π H ⊓ opiCoreInG πᶜ H = ⊥ :=
    inf_eq_bot_of_isPiSubgroup_of_isPiSubgroup_compl
      (isPiSubgroup_opiCoreInG π H)
      (isPiSubgroup_opiCoreInG πᶜ H)
  exact le_bot_iff.mp (by
    rw [← hinf]
    exact le_inf hleft hright)

/-- The `π`-core of `F(H)`, viewed as a subgroup of `H`, is normal. -/
theorem opiCoreInG_fittingInG_subgroupOf_normal [Finite G]
    (π : Set ℕ) (H : Subgroup G) :
    ((opiCoreInG π (fittingInG H)).subgroupOf H).Normal := by
  have hNH : opiCoreInG π (fittingInG H) ≤ H :=
    (opiCoreInG_le π (fittingInG H)).trans (fittingInG_le H)
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer hNH]
  have hH_norm_F : H ≤ Subgroup.normalizer (fittingInG H : Set G) := by
    intro x hx
    exact mem_normalizer_fittingInG_of_mem hx
  exact le_normalizer_opiCoreInG_of_le_normalizer π hH_norm_F

/-- The `π`-core of `F(H)` is absorbed by the `π`-core of `H`.
This is the formal `D_q ≤ O_q(H)` bridge for BG (8.7), with `D = F(H)`. -/
theorem opiCoreInG_fittingInG_le_opiCoreInG [Finite G]
    (π : Set ℕ) (H : Subgroup G) :
    opiCoreInG π (fittingInG H) ≤ opiCoreInG π H := by
  have hNH : opiCoreInG π (fittingInG H) ≤ H :=
    (opiCoreInG_le π (fittingInG H)).trans (fittingInG_le H)
  exact le_opiCoreInG_of_normal_of_isPiSubgroup hNH
    (opiCoreInG_fittingInG_subgroupOf_normal π H)
    (isPiSubgroup_opiCoreInG π (fittingInG H))

/-- Monotonicity of the ambient `π`-core in the set of primes. -/
theorem opiCoreInG_mono [Finite G] {π ρ : Set ℕ}
    (hπρ : π ⊆ ρ) (H : Subgroup G) :
    opiCoreInG π H ≤ opiCoreInG ρ H := by
  rw [opiCoreInG, opiCoreInG]
  exact Subgroup.map_mono (Ch03.oPiCore_mono hπρ ↥H)

/-- In a finite nilpotent subgroup `K`, every ambient p-subgroup of `K` lies in
`O_p(K)`. -/
theorem le_opiCoreInG_singleton_of_isPGroup_of_le_nilpotent [Finite G]
    {p : ℕ} [Fact p.Prime] {K P : Subgroup G}
    (hKnilp : Group.IsNilpotent ↥K)
    (hPK : P ≤ K) (hPp : IsPGroup p ↥P) :
    P ≤ opiCoreInG ({p} : Set ℕ) K := by
  have : Group.IsNilpotent ↥K := hKnilp
  have hPsub_p : IsPGroup p ↥(P.subgroupOf K) := by
    obtain ⟨n, hn⟩ := hPp.exists_card_eq
    exact IsPGroup.of_card (by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPK).toEquiv]
      exact hn)
  obtain ⟨S, hPS⟩ := hPsub_p.exists_le_sylow
  have hSnormal : (S : Subgroup ↥K).Normal := Ch01.Sylow.normal_of_isNilpotent S
  have hSpi : Ch03.Subgroup.IsPiGroup ({p} : Set ℕ) (S : Subgroup ↥K) := by
    intro r hr
    exact (isPiSubgroup_singleton_of_isPGroup (G := ↥K) S.isPGroup') r hr
  have hSleCore : (S : Subgroup ↥K) ≤ Ch03.oPiCore ({p} : Set ℕ) ↥K :=
    hSpi.le_oPiCore
  calc P = (P.subgroupOf K).map K.subtype :=
        (Subgroup.map_subgroupOf_eq_of_le hPK).symm
    _ ≤ (S : Subgroup ↥K).map K.subtype := Subgroup.map_mono hPS
    _ ≤ opiCoreInG ({p} : Set ℕ) K := Subgroup.map_mono hSleCore

/-- A finite nilpotent ambient subgroup is generated by the images of its default
Sylow subgroups. This packages the Ch. 1 Sylow-generation theorem in the form
needed for subgroup containments in `G`. -/
theorem le_of_sylow_le_of_nilpotent [Finite G] {K X : Subgroup G}
    (hKnilp : Group.IsNilpotent ↥K)
    (hSyl : ∀ r : (Nat.card ↥K).primeFactors,
      ((default : Sylow (r : ℕ) ↥K) : Subgroup ↥K).map K.subtype ≤ X) :
    K ≤ X := by
  have : Group.IsNilpotent ↥K := hKnilp
  have htop_map : (⊤ : Subgroup ↥K).map K.subtype = K := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rw [← htop_map, ← Ch01.iSup_default_sylow_eq_top_of_nilpotent ↥K, Subgroup.map_iSup]
  exact iSup_le hSyl

/-- The r-core of `C_F(M)(A0)` lies in the r-core of `F(M)`. -/
theorem opiCoreInG_singleton_cFittingInG_le_opiCoreInG_fittingInG [Finite G]
    {q : ℕ} [Fact q.Prime] {M A0 : Subgroup G} :
    opiCoreInG ({q} : Set ℕ) (cFittingInG M A0) ≤
      opiCoreInG ({q} : Set ℕ) (fittingInG M) := by
  have hcore_le_F : opiCoreInG ({q} : Set ℕ) (cFittingInG M A0) ≤ fittingInG M :=
    (opiCoreInG_le ({q} : Set ℕ) (cFittingInG M A0)).trans (by
      dsimp [cFittingInG]
      exact inf_le_right)
  exact le_opiCoreInG_singleton_of_isPGroup_of_le_nilpotent
    (fittingInG_isNilpotent M) hcore_le_F
    (isPGroup_opiCoreInG_singleton (cFittingInG M A0))

/-- If `r ≠ q`, then the r-core of `C_F(M)(A0)` lies in `O_{q'}(M)`. -/
theorem opiCoreInG_singleton_cFittingInG_le_opiCoreInG_singleton_compl_maximal_of_ne
    [Finite G] {q r : ℕ} [Fact q.Prime] [Fact r.Prime] {M A0 : Subgroup G}
    (hqr : q ≠ r) :
    opiCoreInG ({r} : Set ℕ) (cFittingInG M A0) ≤ opiCoreInG ({q} : Set ℕ)ᶜ M := by
  have hArF : opiCoreInG ({r} : Set ℕ) (cFittingInG M A0) ≤
      opiCoreInG ({r} : Set ℕ) (fittingInG M) :=
    opiCoreInG_singleton_cFittingInG_le_opiCoreInG_fittingInG
  have hArM : opiCoreInG ({r} : Set ℕ) (cFittingInG M A0) ≤
      opiCoreInG ({r} : Set ℕ) M :=
    hArF.trans (opiCoreInG_fittingInG_le_opiCoreInG ({r} : Set ℕ) M)
  have hsubset : ({r} : Set ℕ) ⊆ ({q} : Set ℕ)ᶜ := by
    intro s hs hsq
    rw [Set.mem_singleton_iff] at hs hsq
    exact hqr (hsq.symm.trans hs)
  exact hArM.trans (opiCoreInG_mono hsubset M)

/-- The `π`-core of `F(H)` centralizes the `π`-complement core of `H`.

This is the `D_q` versus `O_{q'}(H)` commutation part of BG (8.7), with
`D = F(H)`. -/
theorem opiCoreInG_fittingInG_commutator_compl_eq_bot [Finite G]
    (π : Set ℕ) (H : Subgroup G) :
    ⁅opiCoreInG π (fittingInG H), opiCoreInG πᶜ H⁆ = ⊥ := by
  have hD_le : opiCoreInG π (fittingInG H) ≤ opiCoreInG π H :=
    opiCoreInG_fittingInG_le_opiCoreInG π H
  have hbig_bot : ⁅opiCoreInG π H, opiCoreInG πᶜ H⁆ ≤ ⊥ := by
    rw [opiCoreInG_commutator_compl_eq_bot π H]
  exact le_bot_iff.mp ((Subgroup.commutator_mono hD_le le_rfl).trans hbig_bot)

/-- If a subgroup lies in `O_{π'}(H)`, then `O_π(F(H))` centralizes it. -/
theorem opiCoreInG_fittingInG_le_centralizer_of_le_opiCoreInG_compl [Finite G]
    (π : Set ℕ) {H K : Subgroup G}
    (hK : K ≤ opiCoreInG πᶜ H) :
    opiCoreInG π (fittingInG H) ≤ Subgroup.centralizer (K : Set G) := by
  rw [← Subgroup.commutator_eq_bot_iff_le_centralizer]
  have hcomm_le :
      ⁅opiCoreInG π (fittingInG H), K⁆ ≤
        ⁅opiCoreInG π (fittingInG H), opiCoreInG πᶜ H⁆ :=
    Subgroup.commutator_mono le_rfl hK
  have hbig_bot :
      ⁅opiCoreInG π (fittingInG H), opiCoreInG πᶜ H⁆ ≤ ⊥ := by
    rw [opiCoreInG_fittingInG_commutator_compl_eq_bot π H]
  exact le_bot_iff.mp (hcomm_le.trans hbig_bot)

/-- BG Proposition 1.10, packaged for the cyclic conjugation action on `F(M)`.

If the fixed subgroup `C_{F(M)}(<x>)` is self-centralizing in `F(M)` and `<x>` has
order coprime to `|F(M)|`, then `<x>` acts trivially on `F(M)`. -/
theorem zpowers_acts_trivially_on_fittingInG_of_centralizer_self [Finite G]
    {M : Subgroup G} {x : G} (hxM : x ∈ M)
    (hcop : Nat.Coprime (Nat.card ↥(Subgroup.zpowers x)) (Nat.card ↥(fittingInG M)))
    (hCC :
      Subgroup.centralizer
        ((Subgroup.centralizer (Subgroup.zpowers x : Set G) ⊓ fittingInG M).subgroupOf
          (fittingInG M) : Set ↥(fittingInG M))
        ≤ (Subgroup.centralizer (Subgroup.zpowers x : Set G) ⊓ fittingInG M).subgroupOf
          (fittingInG M)) :
    ∀ a : ↥(Subgroup.zpowers x), ∀ f : ↥(fittingInG M),
      (conjActionOnFittingInG hxM a) f = f := by
  have : Group.IsNilpotent ↥(fittingInG M) := fittingInG_isNilpotent M
  have hCC_fixed : Subgroup.centralizer
      (Subgroup.fixedPointsOfMulAut (conjActionOnFittingInG hxM) : Set ↥(fittingInG M))
      ≤ Subgroup.fixedPointsOfMulAut (conjActionOnFittingInG hxM) := by
    rw [fixedPoints_conjActionOnFittingInG_eq hxM]
    exact hCC
  exact OddOrder.BG.Ch1.S01.coprime_nilpotent_acts_trivially_of_centralizer_self
    (A := ↥(Subgroup.zpowers x)) (G := ↥(fittingInG M))
    (φ := conjActionOnFittingInG hxM) hcop hCC_fixed

/-- If `<x>` acts trivially on `F(M)`, then its generator centralizes `F(M)`. -/
theorem mem_centralizer_fittingInG_of_zpowers_action_trivial {M : Subgroup G} {x : G}
    (hxM : x ∈ M)
    (htriv : ∀ a : ↥(Subgroup.zpowers x), ∀ f : ↥(fittingInG M),
      (conjActionOnFittingInG hxM a) f = f) :
    x ∈ Subgroup.centralizer (fittingInG M : Set G) := by
  refine Subgroup.mem_centralizer_iff.mpr ?_
  intro y hy
  let a : ↥(Subgroup.zpowers x) := ⟨x, Subgroup.mem_zpowers x⟩
  let f : ↥(fittingInG M) := ⟨y, hy⟩
  have hfix := htriv a f
  have hfixG := congrArg Subtype.val hfix
  rw [conjActionOnFittingInG_apply] at hfixG
  have hcomm : x * y = y * x := by
    calc x * y = (x * y * x⁻¹) * x := by group
      _ = y * x := by rw [hfixG]
  exact hcomm.symm

/-- The Prop 1.10 bridge in the form used in BG (8.3): the generator of a cyclic
subgroup satisfying the self-centralizer condition centralizes `F(M)`. -/
theorem mem_centralizer_fittingInG_of_centralizer_self_zpowers [Finite G]
    {M : Subgroup G} {x : G} (hxM : x ∈ M)
    (hcop : Nat.Coprime (Nat.card ↥(Subgroup.zpowers x)) (Nat.card ↥(fittingInG M)))
    (hCC :
      Subgroup.centralizer
        ((Subgroup.centralizer (Subgroup.zpowers x : Set G) ⊓ fittingInG M).subgroupOf
          (fittingInG M) : Set ↥(fittingInG M))
        ≤ (Subgroup.centralizer (Subgroup.zpowers x : Set G) ⊓ fittingInG M).subgroupOf
          (fittingInG M)) :
    x ∈ Subgroup.centralizer (fittingInG M : Set G) :=
  mem_centralizer_fittingInG_of_zpowers_action_trivial hxM
    (zpowers_acts_trivially_on_fittingInG_of_centralizer_self hxM hcop hCC)

/-- With solvability of `M`, the same Prop 1.10 bridge places the generator inside
`F(M)` by the ambient self-centralizer of the Fitting subgroup. -/
theorem mem_fittingInG_of_centralizer_self_zpowers [Finite G]
    {M : Subgroup G} [Group.IsSolvable ↥M] {x : G} (hxM : x ∈ M)
    (hcop : Nat.Coprime (Nat.card ↥(Subgroup.zpowers x)) (Nat.card ↥(fittingInG M)))
    (hCC :
      Subgroup.centralizer
        ((Subgroup.centralizer (Subgroup.zpowers x : Set G) ⊓ fittingInG M).subgroupOf
          (fittingInG M) : Set ↥(fittingInG M))
        ≤ (Subgroup.centralizer (Subgroup.zpowers x : Set G) ⊓ fittingInG M).subgroupOf
          (fittingInG M)) :
    x ∈ fittingInG M := by
  exact mem_fittingInG_of_mem_centralizer_fittingInG hxM
    (mem_centralizer_fittingInG_of_centralizer_self_zpowers hxM hcop hCC)

/-- A cyclic `π(F(M))`-complement subgroup has order coprime to `|F(M)|`. -/
theorem coprime_card_zpowers_fittingInG_of_isPiSubgroup_primesOf_compl [Finite G]
    {M : Subgroup G} {x : G}
    (hxpi : Subgroup.IsPiSubgroup (OddOrder.BG.Ch2.S07.primesOf (fittingInG M))ᶜ
      (Subgroup.zpowers x)) :
    Nat.Coprime (Nat.card ↥(Subgroup.zpowers x)) (Nat.card ↥(fittingInG M)) :=
  (coprime_card_of_isPiSubgroup_of_isPiSubgroup_compl
    (π := OddOrder.BG.Ch2.S07.primesOf (fittingInG M)) (H := fittingInG M)
    (K := Subgroup.zpowers x)
    (fun r hr => by simpa [OddOrder.BG.Ch2.S07.primesOf] using hr) hxpi).symm

/-- BG (8.3) endpoint for a cyclic pi-complement element: under the Prop 1.10
self-centralizer condition, such an element is trivial. -/
theorem eq_one_of_centralizer_self_zpowers_of_isPiSubgroup_primesOf_compl [Finite G]
    {M : Subgroup G} [Group.IsSolvable ↥M] {x : G} (hxM : x ∈ M)
    (hCC :
      Subgroup.centralizer
        ((Subgroup.centralizer (Subgroup.zpowers x : Set G) ⊓ fittingInG M).subgroupOf
          (fittingInG M) : Set ↥(fittingInG M))
        ≤ (Subgroup.centralizer (Subgroup.zpowers x : Set G) ⊓ fittingInG M).subgroupOf
          (fittingInG M))
    (hxpi : Subgroup.IsPiSubgroup (OddOrder.BG.Ch2.S07.primesOf (fittingInG M))ᶜ
      (Subgroup.zpowers x)) :
    x = 1 :=
  eq_one_of_mem_fittingInG_of_zpowers_isPiSubgroup_primesOf_compl
    (mem_fittingInG_of_centralizer_self_zpowers hxM
      (coprime_card_zpowers_fittingInG_of_isPiSubgroup_primesOf_compl hxpi) hCC) hxpi

/-- BG (8.3) criterion: if every cyclic pi-complement element in the ambient centralizer
satisfies the Prop 1.10 self-centralizer hypothesis, then the centralizer is a
`π(F(M))`-subgroup. -/
theorem centralizer_cFitting_isPiSubgroup_of_zpowers_centralizer_self [Finite G]
    {M A0 : Subgroup G} [Group.IsSolvable ↥M]
    (hCentM : Subgroup.centralizer (cFittingInG M A0 : Set G) ≤ M)
    (hCC : ∀ {x : G}, x ∈ Subgroup.centralizer (cFittingInG M A0 : Set G) →
      Subgroup.IsPiSubgroup (OddOrder.BG.Ch2.S07.primesOf (fittingInG M))ᶜ
        (Subgroup.zpowers x) →
      Subgroup.centralizer
        ((Subgroup.centralizer (Subgroup.zpowers x : Set G) ⊓ fittingInG M).subgroupOf
          (fittingInG M) : Set ↥(fittingInG M))
        ≤ (Subgroup.centralizer (Subgroup.zpowers x : Set G) ⊓ fittingInG M).subgroupOf
          (fittingInG M)) :
    Subgroup.IsPiSubgroup (OddOrder.BG.Ch2.S07.primesOf (fittingInG M))
      (Subgroup.centralizer (cFittingInG M A0 : Set G)) := by
  refine isPiSubgroup_of_forall_zpowers_isPiSubgroup_compl_eq_one ?_
  intro x hxC hxpi
  exact eq_one_of_centralizer_self_zpowers_of_isPiSubgroup_primesOf_compl
    (hCentM hxC) (hCC hxC hxpi) hxpi

/-- The center of `F(M)`, realized as a subgroup of the ambient group `G`. -/
def centerFittingInG (M : Subgroup G) : Subgroup G :=
  (Subgroup.center ↥(fittingInG M)).map (fittingInG M).subtype

/-- `Z(F(M))`, realized in `G`, lies inside `F(M)`. -/
theorem centerFittingInG_le_fittingInG (M : Subgroup G) :
    centerFittingInG M ≤ fittingInG M :=
  Subgroup.map_subtype_le _

/-- `Z(F(M))`, realized in `G`, lies inside `M`. -/
theorem centerFittingInG_le (M : Subgroup G) :
    centerFittingInG M ≤ M :=
  (centerFittingInG_le_fittingInG M).trans (fittingInG_le M)

/-- Elements of `F(M)` centralize the ambient center `Z(F(M))`. -/
theorem fittingInG_le_centralizer_centerFittingInG (M : Subgroup G) :
    fittingInG M ≤ Subgroup.centralizer (centerFittingInG M : Set G) := by
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  obtain ⟨zc, hzc, hzc_eq⟩ := hz
  have hzc_eqG : (zc : G) = z := hzc_eq
  have hcomm :=
    congrArg Subtype.val (Subgroup.mem_center_iff.mp hzc ⟨x, hx⟩)
  simpa [hzc_eqG] using hcomm.symm

/-- The ambient realization of Z(F(M)) is commutative. -/
theorem centerFittingInG_isMulCommutative (M : Subgroup G) :
    IsMulCommutative ↥(centerFittingInG M) := by
  rw [centerFittingInG]
  exact Subgroup.map_isMulCommutative (Subgroup.center ↥(fittingInG M))
    (fittingInG M).subtype

/-- Every prime divisor of Fitting M divides the center of Fitting M. -/
theorem mem_primeFactors_centerFittingInG_of_mem_primeFactors_fittingInG [Finite G]
    {q : ℕ} [Fact q.Prime] {M : Subgroup G}
    (hq : q ∈ (Nat.card ↥(fittingInG M)).primeFactors) :
    q ∈ (Nat.card ↥(centerFittingInG M)).primeFactors := by
  have : Group.IsNilpotent ↥(fittingInG M) := fittingInG_isNilpotent M
  rw [centerFittingInG, Subgroup.card_map_of_injective (fittingInG M).subtype_injective]
  exact Ch01.mem_primeFactors_center_of_isNilpotent hq

/-- The center of `F(M)`, viewed as a subgroup of `M`, is normal in `M`.

This is the ambient form of the elementary fact that the center of a normal subgroup is
normal.  It is used in BG (8.2), where nontrivial characteristic subgroups of `Z(F(M))`
have normalizer exactly `M`. -/
theorem centerFittingInG_subgroupOf_normal (M : Subgroup G) :
    ((centerFittingInG M).subgroupOf M).Normal := by
  let F : Subgroup G := fittingInG M
  let Z : Subgroup G := centerFittingInG M
  have hZF : Z ≤ F := by
    dsimp [Z]
    exact centerFittingInG_le_fittingInG M
  have hZM : Z ≤ M := by
    dsimp [Z]
    exact centerFittingInG_le M
  have hF_norm_M : M ≤ Subgroup.normalizer (F : Set G) := by
    dsimp [F]
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer (fittingInG_le M)).mp
      (fittingInG_subgroupOf_normal M)
  have hconj_mem : ∀ m ∈ M, ∀ z ∈ Z, m * z * m⁻¹ ∈ Z := by
    intro m hm z hz
    have hzF : z ∈ F := hZF hz
    have hconjF : m * z * m⁻¹ ∈ F :=
      (Subgroup.mem_normalizer_iff.mp (hF_norm_M hm) z).mp hzF
    obtain ⟨zc, hzc, hzc_eq⟩ := hz
    have hzc_eqG : (zc : G) = z := hzc_eq
    refine ⟨⟨m * z * m⁻¹, hconjF⟩, ?_, rfl⟩
    refine Subgroup.mem_center_iff.mpr ?_
    intro y
    apply Subtype.ext
    have hyF : (y : G) ∈ F := y.2
    have hyPrimeF : m⁻¹ * (y : G) * m ∈ F := by
      have hm_inv : m⁻¹ ∈ M := M.inv_mem hm
      simpa using (Subgroup.mem_normalizer_iff.mp (hF_norm_M hm_inv) (y : G)).mp hyF
    have hcomm :
        (m⁻¹ * (y : G) * m) * z = z * (m⁻¹ * (y : G) * m) := by
      have hcommPrime :
          (m⁻¹ * (y : G) * m) * (zc : G) =
            (zc : G) * (m⁻¹ * (y : G) * m) := by
        simpa using
          congrArg Subtype.val
            (Subgroup.mem_center_iff.mp hzc ⟨m⁻¹ * (y : G) * m, hyPrimeF⟩)
      simpa [hzc_eqG] using hcommPrime
    calc
      (y : G) * (m * z * m⁻¹) = m * ((m⁻¹ * (y : G) * m) * z) * m⁻¹ := by
        group
      _ = m * (z * (m⁻¹ * (y : G) * m)) * m⁻¹ := by rw [hcomm]
      _ = m * z * m⁻¹ * (y : G) := by group
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer hZM]
  intro m hm
  rw [Subgroup.mem_normalizer_iff]
  intro z
  constructor
  · exact hconj_mem m hm z
  · intro hz
    have hback := hconj_mem m⁻¹ (M.inv_mem hm) (m * z * m⁻¹) hz
    have heq : m⁻¹ * (m * z * m⁻¹) * m⁻¹⁻¹ = z := by group
    rwa [heq] at hback

/-- The `q`-core of `Z(F(M))`, realized as a subgroup of the ambient group `G`. -/
def centerFittingOpCoreInG (q : ℕ) (M : Subgroup G) : Subgroup G :=
  opiCoreInG ({q} : Set ℕ) (centerFittingInG M)

/-- `O_q(Z(F(M)))`, realized in `G`, lies inside `Z(F(M))`. -/
theorem centerFittingOpCoreInG_le_centerFittingInG (q : ℕ) (M : Subgroup G) :
    centerFittingOpCoreInG q M ≤ centerFittingInG M :=
  opiCoreInG_le ({q} : Set ℕ) (centerFittingInG M)

/-- `O_q(Z(F(M)))`, realized in `G`, lies inside `M`. -/
theorem centerFittingOpCoreInG_le (q : ℕ) (M : Subgroup G) :
    centerFittingOpCoreInG q M ≤ M :=
  (centerFittingOpCoreInG_le_centerFittingInG q M).trans (centerFittingInG_le M)

/-- `O_q(Z(F(M)))`, viewed as a subgroup of `M`, is normal in `M`. -/
theorem centerFittingOpCoreInG_subgroupOf_normal (q : ℕ) (M : Subgroup G) :
    ((centerFittingOpCoreInG q M).subgroupOf M).Normal := by
  have hOM : centerFittingOpCoreInG q M ≤ M := centerFittingOpCoreInG_le q M
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer hOM]
  have hMZ : M ≤ Subgroup.normalizer (centerFittingInG M : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (centerFittingInG_le M)).mp
      (centerFittingInG_subgroupOf_normal M)
  exact le_normalizer_opiCoreInG_of_le_normalizer ({q} : Set ℕ) hMZ

/-- If q divides the order of Z(F(M)), then O_q(Z(F(M))) is nontrivial. -/
theorem centerFittingOpCoreInG_ne_bot_of_mem_primeFactors_center [Finite G]
    {q : ℕ} [Fact q.Prime] {M : Subgroup G}
    (hq : q ∈ (Nat.card ↥(centerFittingInG M)).primeFactors) :
    centerFittingOpCoreInG q M ≠ ⊥ := by
  let Z : Subgroup G := centerFittingInG M
  let P : Sylow q ↥Z := default
  let N : Subgroup G := (P : Subgroup ↥Z).map Z.subtype
  have hq_dvd : q ∣ Nat.card ↥Z := (Nat.mem_primeFactors.mp hq).2.1
  have hP_ne : (P : Subgroup ↥Z) ≠ ⊥ := P.ne_bot_of_dvd_card hq_dvd
  have hN_ne : N ≠ ⊥ := by
    intro hN_bot
    exact hP_ne ((Subgroup.map_eq_bot_iff_of_injective (P : Subgroup ↥Z)
      Z.subtype_injective).mp hN_bot)
  have hZ_comm : IsMulCommutative ↥Z := by
    dsimp [Z]
    exact centerFittingInG_isMulCommutative M
  have hNZ : N ≤ Z := by
    dsimp [N]
    exact Subgroup.map_subtype_le _
  have hNnorm : (N.subgroupOf Z).Normal :=
    Subgroup.normal_of_isMulCommutative (N.subgroupOf Z)
  have hNpi : Subgroup.IsPiSubgroup ({q} : Set ℕ) N := by
    dsimp [N]
    exact isPiSubgroup_singleton_of_isPGroup (P.isPGroup'.map Z.subtype)
  have hNle : N ≤ centerFittingOpCoreInG q M := by
    dsimp [centerFittingOpCoreInG, Z]
    exact le_opiCoreInG_of_normal_of_isPiSubgroup hNZ hNnorm hNpi
  intro hcore_bot
  apply hN_ne
  exact le_bot_iff.mp (by rw [← hcore_bot]; exact hNle)

/-- If q divides the order of Fitting M, then the q-core of its center is nontrivial. -/
theorem centerFittingOpCoreInG_ne_bot_of_mem_primeFactors_fittingInG [Finite G]
    {q : ℕ} [Fact q.Prime] {M : Subgroup G}
    (hq : q ∈ (Nat.card ↥(fittingInG M)).primeFactors) :
    centerFittingOpCoreInG q M ≠ ⊥ :=
  centerFittingOpCoreInG_ne_bot_of_mem_primeFactors_center
    (mem_primeFactors_centerFittingInG_of_mem_primeFactors_fittingInG hq)

/-- **BG (8.1), left inclusion**: `Z(F(M))` centralizes every subgroup contained in
`F(M)`, hence lies in the relative centralizer `C_{F(M)}(A₀)`. -/
theorem centerFittingInG_le_centralizer_inf {M A₀ : Subgroup G}
    (hA₀F : A₀ ≤ fittingInG M) :
    centerFittingInG M ≤ Subgroup.centralizer (A₀ : Set G) ⊓ fittingInG M := by
  refine le_inf ?_ (centerFittingInG_le_fittingInG M)
  intro z hz
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  obtain ⟨zc, hzc, hzc_eq⟩ := hz
  have hzc_eqG : (zc : G) = z := hzc_eq
  have hcomm :=
    congrArg Subtype.val (Subgroup.mem_center_iff.mp hzc ⟨y, hA₀F hy⟩)
  simpa [hzc_eqG] using hcomm

/-- **BG (8.1), prime-support form**: `C_F(M)(A₀)` and `F(M)` have the same
prime divisors when `A₀ ≤ F(M)`. -/
theorem mem_primeFactors_cFitting_iff_mem_primeFactors_fittingInG [Finite G]
    {M A₀ : Subgroup G} (hA₀F : A₀ ≤ fittingInG M) {q : ℕ} :
    q ∈ (Nat.card ↥(Subgroup.centralizer (A₀ : Set G) ⊓ fittingInG M)).primeFactors ↔
      q ∈ (Nat.card ↥(fittingInG M)).primeFactors := by
  constructor
  · intro hq
    exact Nat.primeFactors_mono
      (Subgroup.card_dvd_of_le
        (inf_le_right : Subgroup.centralizer (A₀ : Set G) ⊓ fittingInG M ≤ fittingInG M))
      Nat.card_pos.ne' hq
  · intro hqF
    have : Fact q.Prime := ⟨Nat.prime_of_mem_primeFactors hqF⟩
    have hqZ : q ∈ (Nat.card ↥(centerFittingInG M)).primeFactors :=
      mem_primeFactors_centerFittingInG_of_mem_primeFactors_fittingInG hqF
    exact Nat.primeFactors_mono
      (Subgroup.card_dvd_of_le (centerFittingInG_le_centralizer_inf hA₀F))
      Nat.card_pos.ne' hqZ

/-- **BG (8.1), `π`-notation form**: `π(C_F(M)(A₀)) = π(F(M))`. -/
theorem primesOf_cFitting_eq_primesOf_fittingInG [Finite G]
    {M A₀ : Subgroup G} (hA₀F : A₀ ≤ fittingInG M) :
    OddOrder.BG.Ch2.S07.primesOf
        (Subgroup.centralizer (A₀ : Set G) ⊓ fittingInG M) =
      OddOrder.BG.Ch2.S07.primesOf (fittingInG M) := by
  ext q
  exact mem_primeFactors_cFitting_iff_mem_primeFactors_fittingInG hA₀F

/-- **`ℰ_p^*(H)` membership**: `A₀` は `H` の中で極大な `p`-elementary abelian 部分群
(`A₀ ≤ H` elem-ab で、`H` 内の elem-ab `B ⊇ A₀` は `A₀` に戻る)。 -/
def isMaxElemAbelianIn (p : ℕ) (A₀ H : Subgroup G) : Prop :=
  A₀.IsElementaryAbelian p ∧ A₀ ≤ H ∧
    ∀ B : Subgroup G, B.IsElementaryAbelian p → B ≤ H → A₀ ≤ B → B = A₀

/-- A maximal elementary abelian subgroup is elementary abelian. -/
theorem isMaxElemAbelianIn_isElementaryAbelian {p : ℕ} {A₀ H : Subgroup G}
    (hA₀ : isMaxElemAbelianIn p A₀ H) :
    A₀.IsElementaryAbelian p :=
  hA₀.1

/-- A maximal elementary abelian subgroup of `H` lies in `H`. -/
theorem isMaxElemAbelianIn_le {p : ℕ} {A₀ H : Subgroup G}
    (hA₀ : isMaxElemAbelianIn p A₀ H) :
    A₀ ≤ H :=
  hA₀.2.1

/-- A maximal elementary abelian subgroup of `F(M)` lies in its own centralizer inside
`F(M)`.  This is the formal start of BG (8.1). -/
theorem isMaxElemAbelianIn_le_centralizer_inf {p : ℕ} {M A₀ : Subgroup G}
    (hA₀ : isMaxElemAbelianIn p A₀ (fittingInG M)) :
    A₀ ≤ Subgroup.centralizer (A₀ : Set G) ⊓ fittingInG M := by
  refine le_inf ?_ (isMaxElemAbelianIn_le hA₀)
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  exact congrArg Subtype.val (hA₀.1.comm ⟨y, hy⟩ ⟨x, hx⟩)

/-- The `p`-complement core of `F(M)` is absorbed by the `p`-complement core of
`A = C_F(M)(A0)`. This is the formal `O_{p'}(F) ≤ O_{p'}(A)` part of BG (8.8). -/
theorem opiCoreInG_singleton_compl_fittingInG_le_opiCoreInG_singleton_compl_cFittingInG
    [Finite G] {p : ℕ} [Fact p.Prime] {M A0 : Subgroup G}
    (hA0 : isMaxElemAbelianIn p A0 (fittingInG M)) :
    opiCoreInG ({p} : Set ℕ)ᶜ (fittingInG M) ≤
      opiCoreInG ({p} : Set ℕ)ᶜ (cFittingInG M A0) := by
  let K : Subgroup G := opiCoreInG ({p} : Set ℕ)ᶜ (fittingInG M)
  change K ≤ opiCoreInG ({p} : Set ℕ)ᶜ (cFittingInG M A0)
  have hA0_le_OpF : A0 ≤ opiCoreInG ({p} : Set ℕ) (fittingInG M) :=
    le_opiCoreInG_singleton_of_isPGroup_of_le_nilpotent
      (fittingInG_isNilpotent M) (isMaxElemAbelianIn_le hA0)
      hA0.1.isPGroup
  have hOpF_cent_K : opiCoreInG ({p} : Set ℕ) (fittingInG M) ≤
      Subgroup.centralizer (K : Set G) := by
    dsimp [K]
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact opiCoreInG_commutator_compl_eq_bot ({p} : Set ℕ) (fittingInG M)
  have hK_cent_A0 : K ≤ Subgroup.centralizer (A0 : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact (Subgroup.mem_centralizer_iff.mp (hOpF_cent_K (hA0_le_OpF ha)) x hx).symm
  have hK_A : K ≤ cFittingInG M A0 := by
    refine le_inf hK_cent_A0 ?_
    dsimp [K]
    exact opiCoreInG_le ({p} : Set ℕ)ᶜ (fittingInG M)
  have hK_norm_A : (K.subgroupOf (cFittingInG M A0)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hK_A]
    have hA_le_F : cFittingInG M A0 ≤ fittingInG M := by
      dsimp [cFittingInG]
      exact inf_le_right
    have hF_norm_K : fittingInG M ≤ Subgroup.normalizer (K : Set G) := by
      dsimp [K]
      exact le_normalizer_opiCoreInG ({p} : Set ℕ)ᶜ (fittingInG M)
    exact hA_le_F.trans hF_norm_K
  have hK_pi : Subgroup.IsPiSubgroup ({p} : Set ℕ)ᶜ K := by
    dsimp [K]
    exact isPiSubgroup_opiCoreInG ({p} : Set ℕ)ᶜ (fittingInG M)
  exact le_opiCoreInG_of_normal_of_isPiSubgroup hK_A hK_norm_A hK_pi

/-- If `x` centralizes `C_F(M)(A0)`, then `C_F(M)(A0)` lies in
`C_F(M)(<x>)`. -/
theorem cFitting_le_centralizer_zpowers_inf_fittingInG_of_mem_centralizer
    {M A0 : Subgroup G} {x : G}
    (hxC : x ∈ Subgroup.centralizer (cFittingInG M A0 : Set G)) :
    cFittingInG M A0 ≤ Subgroup.centralizer (Subgroup.zpowers x : Set G) ⊓ fittingInG M := by
  intro a haA
  have haA_saved : a ∈ cFittingInG M A0 := haA
  rw [cFittingInG, Subgroup.mem_inf] at haA
  refine ⟨?_, haA.2⟩
  refine Subgroup.mem_centralizer_iff.mpr ?_
  intro y hy
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  have hcomm_eq : (a : G) * x = x * (a : G) :=
    Subgroup.mem_centralizer_iff.mp hxC (a : G) haA_saved
  have hcomm : Commute (a : G) x := hcomm_eq
  exact (hcomm.symm.zpow_left n).eq

/-- BG (8.3) self-centralizer bridge: for `A = C_F(M)(A0)`, an element of `C_G(A)`
satisfies the `C_F(C_F(<x>)) ≤ C_F(<x>)` input needed for Proposition 1.10. -/
theorem centralizer_zpowers_inf_fittingInG_self_of_mem_centralizer_cFitting
    {p : ℕ} {M A0 : Subgroup G} {x : G}
    (hA0 : isMaxElemAbelianIn p A0 (fittingInG M))
    (hxC : x ∈ Subgroup.centralizer (cFittingInG M A0 : Set G)) :
    Subgroup.centralizer
        ((Subgroup.centralizer (Subgroup.zpowers x : Set G) ⊓ fittingInG M).subgroupOf
          (fittingInG M) : Set ↥(fittingInG M))
      ≤ (Subgroup.centralizer (Subgroup.zpowers x : Set G) ⊓ fittingInG M).subgroupOf
          (fittingInG M) := by
  let C : Subgroup G := Subgroup.centralizer (Subgroup.zpowers x : Set G) ⊓ fittingInG M
  have hA_le_C : cFittingInG M A0 ≤ C := by
    dsimp [C]
    exact cFitting_le_centralizer_zpowers_inf_fittingInG_of_mem_centralizer hxC
  have hA0A : A0 ≤ Subgroup.centralizer (A0 : Set G) ⊓ fittingInG M :=
    isMaxElemAbelianIn_le_centralizer_inf hA0
  intro y hy
  rw [Subgroup.mem_subgroupOf]
  have hyA : (y : G) ∈ cFittingInG M A0 := by
    rw [cFittingInG, Subgroup.mem_inf]
    refine ⟨?_, y.2⟩
    refine Subgroup.mem_centralizer_iff.mpr ?_
    intro a0 ha0
    let a0F : ↥(fittingInG M) := ⟨a0, (hA0A ha0).2⟩
    have ha0C : a0F ∈ C.subgroupOf (fittingInG M) := by
      rw [Subgroup.mem_subgroupOf]
      exact hA_le_C (by simpa [cFittingInG] using (hA0A ha0).1)
    have hcommF := Subgroup.mem_centralizer_iff.mp hy a0F ha0C
    exact congrArg Subtype.val hcommF
  exact hA_le_C hyA

/-- BG (8.3) packaged with the self-centralizer bridge for
`A = C_F(M)(A0)`: once the ambient centralizer is known to lie in `M`, it is a
`π(F(M))`-subgroup. -/
theorem centralizer_cFitting_isPiSubgroup_primesOf_fittingInG_of_le_maximal [Finite G]
    {p : ℕ} {M A0 : Subgroup G} [Group.IsSolvable ↥M]
    (hA0 : isMaxElemAbelianIn p A0 (fittingInG M))
    (hCentM : Subgroup.centralizer (cFittingInG M A0 : Set G) ≤ M) :
    Subgroup.IsPiSubgroup (OddOrder.BG.Ch2.S07.primesOf (fittingInG M))
      (Subgroup.centralizer (cFittingInG M A0 : Set G)) :=
  centralizer_cFitting_isPiSubgroup_of_zpowers_centralizer_self hCentM
    (fun hxC _hxpi =>
      centralizer_zpowers_inf_fittingInG_self_of_mem_centralizer_cFitting hA0 hxC)

/-- Maximality clause for `isMaxElemAbelianIn`. -/
theorem isMaxElemAbelianIn_eq_of_isElementaryAbelian_of_le {p : ℕ} {A₀ H B : Subgroup G}
    (hA₀ : isMaxElemAbelianIn p A₀ H) (hB : B.IsElementaryAbelian p) (hBH : B ≤ H)
    (hA₀B : A₀ ≤ B) :
    B = A₀ :=
  hA₀.2.2 B hB hBH hA₀B

/-- A maximal elementary abelian subgroup of `F(M)` is nontrivial when `p` divides
`|F(M)|`. -/
theorem isMaxElemAbelianIn_ne_bot_of_mem_primeFactors_fittingInG [Finite G]
    {p : ℕ} [Fact p.Prime] {M A₀ : Subgroup G}
    (hp : p ∈ (Nat.card ↥(fittingInG M)).primeFactors)
    (hA₀ : isMaxElemAbelianIn p A₀ (fittingInG M)) :
    A₀ ≠ ⊥ := by
  intro hA₀_bot
  have hp_dvd : p ∣ Nat.card ↥(fittingInG M) := (Nat.mem_primeFactors.mp hp).2.1
  obtain ⟨x, hx_order⟩ :=
    exists_prime_orderOf_dvd_card' (G := ↥(fittingInG M)) p hp_dvd
  let B₀ : Subgroup ↥(fittingInG M) := Subgroup.zpowers x
  let B : Subgroup G := B₀.map (fittingInG M).subtype
  have hB_card : Nat.card B = p := by
    rw [show B = B₀.map (fittingInG M).subtype from rfl,
      Subgroup.card_map_of_injective (fittingInG M).subtype_injective,
      show B₀ = Subgroup.zpowers x from rfl, Nat.card_zpowers, hx_order]
  have hB_elem : B.IsElementaryAbelian p := Subgroup.IsElementaryAbelian.of_card_prime hB_card
  have hB_le_F : B ≤ fittingInG M := by
    exact Subgroup.map_subtype_le B₀
  have hA₀_le_B : A₀ ≤ B := by
    rw [hA₀_bot]
    exact bot_le
  have hB_eq_A₀ : B = A₀ :=
    isMaxElemAbelianIn_eq_of_isElementaryAbelian_of_le hA₀ hB_elem hB_le_F hA₀_le_B
  have hB_ne_bot : B ≠ ⊥ := by
    intro hB_bot
    have hp_one : p = 1 := by
      rw [hB_bot, Subgroup.card_bot] at hB_card
      exact hB_card.symm
    exact (Fact.out : p.Prime).ne_one hp_one
  exact hB_ne_bot (hB_eq_A₀.trans hA₀_bot)

/-- The relative centralizer `C_F(M)(A₀)` is nontrivial under the hypotheses of BG (8.1). -/
theorem cFitting_ne_bot_of_isMaxElemAbelianIn [Finite G]
    {p : ℕ} [Fact p.Prime] {M A₀ : Subgroup G}
    (hp : p ∈ (Nat.card ↥(fittingInG M)).primeFactors)
    (hA₀ : isMaxElemAbelianIn p A₀ (fittingInG M)) :
    Subgroup.centralizer (A₀ : Set G) ⊓ fittingInG M ≠ ⊥ := by
  have hA₀_ne : A₀ ≠ ⊥ :=
    isMaxElemAbelianIn_ne_bot_of_mem_primeFactors_fittingInG hp hA₀
  have hA₀_le :
      A₀ ≤ Subgroup.centralizer (A₀ : Set G) ⊓ fittingInG M :=
    isMaxElemAbelianIn_le_centralizer_inf hA₀
  intro hbot
  apply hA₀_ne
  exact le_bot_iff.mp (by simpa [hbot] using hA₀_le)

/-- The subgroup A0, restricted to C_F(M)(A0), lies in that relative centralizer's center. -/
theorem subgroupOf_cFitting_le_center (M A0 : Subgroup G) :
    A0.subgroupOf (Subgroup.centralizer (A0 : Set G) ⊓ fittingInG M) ≤
      Subgroup.center ↥(Subgroup.centralizer (A0 : Set G) ⊓ fittingInG M) := by
  let A : Subgroup G := Subgroup.centralizer (A0 : Set G) ⊓ fittingInG M
  change A0.subgroupOf A ≤ Subgroup.center ↥A
  intro x hx
  rw [Subgroup.mem_center_iff]
  intro y
  apply Subtype.ext
  rw [Subgroup.mem_subgroupOf] at hx
  have hycent : (y : G) ∈ Subgroup.centralizer (A0 : Set G) := y.2.1
  exact (Subgroup.mem_centralizer_iff.mp hycent (x : G) hx).symm

/-- If m(A0) >= 3, then m(Z(C_F(M)(A0))) >= 3. -/
theorem three_le_rank_center_cFitting_of_isMaxElemAbelianIn [Finite G]
    {p : ℕ} {M A0 : Subgroup G}
    (hA0 : isMaxElemAbelianIn p A0 (fittingInG M))
    (hm : 3 ≤ rank ↥A0) :
    3 ≤ rank ↥(Subgroup.center ↥(Subgroup.centralizer (A0 : Set G) ⊓ fittingInG M)) := by
  let A : Subgroup G := Subgroup.centralizer (A0 : Set G) ⊓ fittingInG M
  have hA0A : A0 ≤ A := by
    dsimp [A]
    exact isMaxElemAbelianIn_le_centralizer_inf hA0
  have hA0sub_le_center : A0.subgroupOf A ≤ Subgroup.center ↥A := by
    dsimp [A]
    exact subgroupOf_cFitting_le_center M A0
  have hsub_rank : rank ↥(A0.subgroupOf A) ≤ rank ↥(Subgroup.center ↥A) :=
    rank_le_of_injective (Subgroup.inclusion_injective hA0sub_le_center)
  have hA0_rank_le_sub : rank ↥A0 ≤ rank ↥(A0.subgroupOf A) :=
    rank_le_of_injective
      (f := (Subgroup.subgroupOfEquivOfLe hA0A).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hA0A).symm.injective
  exact hm.trans (hA0_rank_le_sub.trans hsub_rank)

/-- **Simplicity normalizer fact**: in a minimal simple odd group, the normalizer of a nonidentity
subgroup `L` that is normal in a maximal subgroup `M` (and contained in `M`) is exactly `M`.  If
`N_G(L) = G` then `L ⊴ G`, contradicting simplicity (`L ≠ ⊥`, `L ≤ M < ⊤`); else `N_G(L)` lies in a
maximal, which must be `M` since `M ≤ N_G(L)`. -/
theorem normalizer_eq_of_normal_of_mem_maximal [Finite G] (hG : IsMinimalSimpleOdd G)
    {M L : Subgroup G} (hM : M ∈ maximalSubgroups G) (hLM : (L.subgroupOf M).Normal)
    (hLne : L ≠ ⊥) (hLleM : L ≤ M) :
    Subgroup.normalizer (L : Set G) = M := by
  have : IsSimpleGroup G := hG.simple
  have hMco : IsCoatom M := mem_maximalSubgroups.mp hM
  have hMleN : M ≤ Subgroup.normalizer (L : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLleM).mp hLM
  have hNne : Subgroup.normalizer (L : Set G) ≠ ⊤ := by
    intro hNtop
    have hLnormal : L.Normal := Subgroup.normalizer_eq_top_iff.mp hNtop
    rcases hLnormal.eq_bot_or_eq_top with hLbot | hLtop
    · exact hLne hLbot
    · have htop_le_M : ⊤ ≤ M := by
        rw [← hLtop]
        exact hLleM
      exact hMco.lt_top.ne (eq_top_iff.mpr htop_le_M)
  have hNleM : Subgroup.normalizer (L : Set G) ≤ M :=
    (isCoatom_iff_ge_of_le.mp hMco).2 _ hNne hMleN
  exact le_antisymm hNleM hMleN

/-- If a maximal subgroup `M` normalizes a nontrivial q-subgroup `Q`, then `Q` lies
inside `M`. -/
theorem le_maximal_of_le_normalizer_of_ne_bot_isPiSubgroup_singleton [Finite G]
    (hG : IsMinimalSimpleOdd G) {q : ℕ} [Fact q.Prime]
    {M Q : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hMQ : M ≤ Subgroup.normalizer (Q : Set G))
    (hQne : Q ≠ ⊥) (hQpi : Subgroup.IsPiSubgroup ({q} : Set ℕ) Q) :
    Q ≤ M := by
  by_contra hQnot_le
  have hMco : IsCoatom M := mem_maximalSubgroups.mp hM
  have hMQtop : M ⊔ Q = ⊤ := by
    rcases hMco.le_iff.mp (le_sup_left : M ≤ M ⊔ Q) with htop | hsup_eq
    · exact htop
    · exfalso
      apply hQnot_le
      rw [← hsup_eq]
      exact le_sup_right
  have hsup_le_NQ : M ⊔ Q ≤ Subgroup.normalizer (Q : Set G) :=
    sup_le hMQ Subgroup.le_normalizer
  have hNQtop : Subgroup.normalizer (Q : Set G) = ⊤ := by
    refine eq_top_iff.mpr ?_
    rw [← hMQtop]
    exact hsup_le_NQ
  have : Q.Normal := Subgroup.normalizer_eq_top_iff.mp hNQtop
  rcases hG.simple.eq_bot_or_eq_top_of_normal Q inferInstance with hQbot | hQtop
  · exact hQne hQbot
  · have hQp : IsPGroup q ↥Q :=
      OddOrder.GroupTheory.isPGroup_of_isPiSubgroup_singleton hQpi
    have hGp : IsPGroup q G :=
      (hQtop ▸ hQp : IsPGroup q ↥(⊤ : Subgroup G)).of_surjective
        (Subgroup.topEquiv : (⊤ : Subgroup G) ≃* G).toMonoidHom
        Subgroup.topEquiv.surjective
    have : Group.IsNilpotent G := hGp.isNilpotent
    exact hG.notSolvable inferInstance

/-- **BG (8.2) normalizer localization**: if `O_q(Z(F(M)))` is nontrivial, then its
normalizer in the ambient minimal simple group is exactly the maximal subgroup `M`. -/
theorem normalizer_centerFittingOpCoreInG_eq_of_ne_bot [Finite G]
    (hG : IsMinimalSimpleOdd G) {q : ℕ} {M : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hO_ne : centerFittingOpCoreInG q M ≠ ⊥) :
    Subgroup.normalizer (centerFittingOpCoreInG q M : Set G) = M :=
  normalizer_eq_of_normal_of_mem_maximal hG hM
    (centerFittingOpCoreInG_subgroupOf_normal q M) hO_ne (centerFittingOpCoreInG_le q M)

/-- BG (8.2), general centralizer localization: any subgroup containing a nontrivial
`O_q(Z(F(M)))` has ambient centralizer contained in `M`. -/
theorem centralizer_le_maximal_of_centerFittingOpCoreInG_le [Finite G]
    (hG : IsMinimalSimpleOdd G) {q : ℕ} {M B : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hO_ne : centerFittingOpCoreInG q M ≠ ⊥)
    (hOB : centerFittingOpCoreInG q M ≤ B) :
    Subgroup.centralizer (B : Set G) ≤ M := by
  have hcent_le_norm :
      Subgroup.centralizer (B : Set G) ≤
        Subgroup.normalizer (centerFittingOpCoreInG q M : Set G) :=
    (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hOB)).trans
      (Subgroup.centralizer_le_normalizer (centerFittingOpCoreInG q M : Set G))
  simpa [normalizer_centerFittingOpCoreInG_eq_of_ne_bot hG hM hO_ne]
    using hcent_le_norm

/-- BG (8.2), prime-factor form of the general centralizer localization. -/
theorem centralizer_le_maximal_of_centerFittingOpCoreInG_le_fitting_primeFactor [Finite G]
    (hG : IsMinimalSimpleOdd G) {q : ℕ} [Fact q.Prime] {M B : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hq : q ∈ (Nat.card ↥(fittingInG M)).primeFactors)
    (hOB : centerFittingOpCoreInG q M ≤ B) :
    Subgroup.centralizer (B : Set G) ≤ M :=
  centralizer_le_maximal_of_centerFittingOpCoreInG_le hG hM
    (centerFittingOpCoreInG_ne_bot_of_mem_primeFactors_fittingInG hq) hOB

/-- **BG (8.2), centralizer localization form**: if `O_q(Z(F(M)))` is nontrivial,
then the ambient centralizer of `C_{F(M)}(A₀)` lies in `M`. -/
theorem centralizer_cFitting_le_maximal_of_centerFittingOpCore_ne [Finite G]
    (hG : IsMinimalSimpleOdd G) {q : ℕ} {M A₀ : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hA₀F : A₀ ≤ fittingInG M)
    (hO_ne : centerFittingOpCoreInG q M ≠ ⊥) :
    Subgroup.centralizer ((Subgroup.centralizer (A₀ : Set G) ⊓ fittingInG M : Subgroup G) : Set G)
      ≤ M := by
  let A : Subgroup G := Subgroup.centralizer (A₀ : Set G) ⊓ fittingInG M
  have hO_le_A : centerFittingOpCoreInG q M ≤ A :=
    (centerFittingOpCoreInG_le_centerFittingInG q M).trans
      (centerFittingInG_le_centralizer_inf hA₀F)
  have hcent_le_norm :
      Subgroup.centralizer (A : Set G) ≤
        Subgroup.normalizer (centerFittingOpCoreInG q M : Set G) := by
    exact (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hO_le_A)).trans
      (Subgroup.centralizer_le_normalizer (centerFittingOpCoreInG q M : Set G))
  simpa [A, normalizer_centerFittingOpCoreInG_eq_of_ne_bot hG hM hO_ne]
    using hcent_le_norm

/-- BG (8.2), prime-factor form: if q divides |Z(F(M))|, then the ambient
centralizer of C_F(M)(A0) lies in M. -/
theorem centralizer_cFitting_le_maximal_of_centerFitting_primeFactor [Finite G]
    (hG : IsMinimalSimpleOdd G) {q : ℕ} [Fact q.Prime] {M A0 : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hA0F : A0 ≤ fittingInG M)
    (hq : q ∈ (Nat.card ↥(centerFittingInG M)).primeFactors) :
    Subgroup.centralizer ((Subgroup.centralizer (A0 : Set G) ⊓ fittingInG M : Subgroup G) : Set G)
      ≤ M :=
  centralizer_cFitting_le_maximal_of_centerFittingOpCore_ne hG hM hA0F
    (centerFittingOpCoreInG_ne_bot_of_mem_primeFactors_center hq)

/-- BG (8.2), Fitting-prime-factor form. -/
theorem centralizer_cFitting_le_maximal_of_fitting_primeFactor [Finite G]
    (hG : IsMinimalSimpleOdd G) {q : ℕ} [Fact q.Prime] {M A0 : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hA0F : A0 ≤ fittingInG M)
    (hq : q ∈ (Nat.card ↥(fittingInG M)).primeFactors) :
    Subgroup.centralizer ((Subgroup.centralizer (A0 : Set G) ⊓ fittingInG M : Subgroup G) : Set G)
      ≤ M :=
  centralizer_cFitting_le_maximal_of_centerFitting_primeFactor hG hM hA0F
    (mem_primeFactors_centerFittingInG_of_mem_primeFactors_fittingInG hq)

private theorem exists_primeFactor_ne_of_not_isPGroup {H : Type*} [Group H] [Finite H]
    {p : ℕ} [Fact p.Prime] (hHnot : ¬ IsPGroup p H) :
    ∃ q, q ∈ (Nat.card H).primeFactors ∧ q ≠ p := by
  by_contra h
  apply hHnot
  rw [IsPGroup.iff_card]
  refine ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' ?_⟩
  intro q hq_prime hq_dvd
  by_contra hq_ne
  exact h ⟨q, Nat.mem_primeFactors.mpr ⟨hq_prime, hq_dvd, Nat.card_pos.ne'⟩, hq_ne⟩

theorem exists_primeFactor_ne_of_mem_primeFactor_not_isPGroup {H : Type*}
    [Group H] [Finite H] {p : ℕ} [Fact p.Prime]
    (hp : p ∈ (Nat.card H).primeFactors) (hHnot : ¬ IsPGroup p H) (q : ℕ) :
    ∃ r, r ∈ (Nat.card H).primeFactors ∧ r ≠ q := by
  by_cases hqp : q = p
  · obtain ⟨r, hr, hrp⟩ := exists_primeFactor_ne_of_not_isPGroup hHnot
    exact ⟨r, hr, fun hrq => hrp (hrq.trans hqp)⟩
  · exact ⟨p, hp, fun hpq => hqp hpq.symm⟩

/-- If Fitting M is not a p-group, BG (8.2) supplies a prime q whose center-core
localizes the ambient centralizer of C_F(M)(A0) inside M. -/
theorem centralizer_cFitting_le_maximal_of_not_isPGroup [Finite G]
    (hG : IsMinimalSimpleOdd G) {p : ℕ} [Fact p.Prime] {M A0 : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hA0F : A0 ≤ fittingInG M)
    (hFnp : ¬ IsPGroup p ↥(fittingInG M)) :
    Subgroup.centralizer ((Subgroup.centralizer (A0 : Set G) ⊓ fittingInG M : Subgroup G) : Set G)
      ≤ M := by
  obtain ⟨q, hqF, _⟩ := exists_primeFactor_ne_of_not_isPGroup hFnp
  have : Fact q.Prime := ⟨Nat.prime_of_mem_primeFactors hqF⟩
  exact centralizer_cFitting_le_maximal_of_fitting_primeFactor hG hM hA0F hqF

/-- BG (8.3) under the hypotheses used in Theorem 8.1(a): in the non-`p`-group case,
the ambient centralizer of `C_F(M)(A0)` is a `π(C_F(M)(A0))`-subgroup. -/
theorem centralizer_cFitting_isPiSubgroup_of_not_pGroup [Finite G]
    (hG : IsMinimalSimpleOdd G) {p : ℕ} [Fact p.Prime] {M A0 : Subgroup G}
    (hM : M ∈ maximalSubgroups G)
    (hA0 : isMaxElemAbelianIn p A0 (fittingInG M))
    (hFnp : ¬ IsPGroup p ↥(fittingInG M)) :
    Subgroup.IsPiSubgroup (OddOrder.BG.Ch2.S07.primesOf (cFittingInG M A0))
      (Subgroup.centralizer (cFittingInG M A0 : Set G)) := by
  have : Group.IsSolvable ↥M := hG.isSolvable_of_mem_maximalSubgroups hM
  have hA0F : A0 ≤ fittingInG M := isMaxElemAbelianIn_le hA0
  have hPrimes :
      OddOrder.BG.Ch2.S07.primesOf (cFittingInG M A0) =
        OddOrder.BG.Ch2.S07.primesOf (fittingInG M) := by
    dsimp [cFittingInG]
    exact primesOf_cFitting_eq_primesOf_fittingInG hA0F
  have hCentM : Subgroup.centralizer (cFittingInG M A0 : Set G) ≤ M :=
    centralizer_cFitting_le_maximal_of_not_isPGroup hG hM hA0F hFnp
  rw [hPrimes]
  exact centralizer_cFitting_isPiSubgroup_primesOf_fittingInG_of_le_maximal hA0 hCentM

/-- BG (8.3) in `K`-notation: in the non-`p`-group case, the complement core
`O_{π(A)^c}(C_G(A))` is trivial for `A = C_F(M)(A0)`. -/
theorem kSubgroup_cFittingInG_eq_bot_of_not_pGroup [Finite G]
    (hG : IsMinimalSimpleOdd G) {p : ℕ} [Fact p.Prime] {M A0 : Subgroup G}
    (hM : M ∈ maximalSubgroups G)
    (hA0 : isMaxElemAbelianIn p A0 (fittingInG M))
    (hFnp : ¬ IsPGroup p ↥(fittingInG M)) :
    OddOrder.BG.Ch2.S07.kSubgroup (cFittingInG M A0) = ⊥ :=
  OddOrder.BG.Ch2.S07.kSubgroup_eq_bot_of_centralizer_isPiSubgroup
    (centralizer_cFitting_isPiSubgroup_of_not_pGroup hG hM hA0 hFnp)

/-- If `H` is a `π`-subgroup, then every member of `ℋ_X(A;π-complement)`
meets `H` trivially. -/
theorem hInvariant_inf_eq_bot_of_isPiSubgroup [Finite G] {π : Set ℕ}
    {A H X Y : Subgroup G} (hHpi : Subgroup.IsPiSubgroup π H)
    (hY : Y ∈ hInvariant X A πᶜ) :
    Y ⊓ H = ⊥ := by
  have hHY : H ⊓ Y = ⊥ :=
    inf_eq_bot_of_isPiSubgroup_of_isPiSubgroup_compl hHpi (hInvariant_isPiSubgroup hY)
  simpa [inf_comm] using hHY

/-- If `C_G(A)` is a `π(A)`-subgroup, then every member of `ℋ_X(A;π(A)-complement)`
meets `C_G(A)` trivially. -/
theorem hInvariant_inf_centralizer_eq_bot_of_centralizer_isPiSubgroup [Finite G]
    {A X Y : Subgroup G}
    (hCpi : Subgroup.IsPiSubgroup (OddOrder.BG.Ch2.S07.primesOf A)
      (Subgroup.centralizer (A : Set G)))
    (hY : Y ∈ hInvariant X A (OddOrder.BG.Ch2.S07.primesOf A)ᶜ) :
    Y ⊓ Subgroup.centralizer (A : Set G) = ⊥ :=
  hInvariant_inf_eq_bot_of_isPiSubgroup hCpi hY

/-- BG (8.4), first intersection form: in the non-p-group case, every
`A = C_F(M)(A0)`-invariant `π(A)`-complement subgroup has trivial intersection with `C_G(A)`. -/
theorem hInvariant_inf_centralizer_cFittingInG_eq_bot_of_not_pGroup [Finite G]
    (hG : IsMinimalSimpleOdd G) {p : ℕ} [Fact p.Prime] {M A0 X Y : Subgroup G}
    (hM : M ∈ maximalSubgroups G)
    (hA0 : isMaxElemAbelianIn p A0 (fittingInG M))
    (hFnp : ¬ IsPGroup p ↥(fittingInG M))
    (hY : Y ∈ hInvariant X (cFittingInG M A0)
      (OddOrder.BG.Ch2.S07.primesOf (cFittingInG M A0))ᶜ) :
    Y ⊓ Subgroup.centralizer (cFittingInG M A0 : Set G) = ⊥ :=
  hInvariant_inf_centralizer_eq_bot_of_centralizer_isPiSubgroup
    (centralizer_cFitting_isPiSubgroup_of_not_pGroup hG hM hA0 hFnp) hY

/-- BG (8.4), Fitting intersection form: every `A = C_F(M)(A0)`-invariant
`π(A)`-complement subgroup has trivial intersection with `F(M)`. -/
theorem hInvariant_inf_fittingInG_cFittingInG_eq_bot [Finite G]
    {p : ℕ} {M A0 X Y : Subgroup G}
    (hA0 : isMaxElemAbelianIn p A0 (fittingInG M))
    (hY : Y ∈ hInvariant X (cFittingInG M A0)
      (OddOrder.BG.Ch2.S07.primesOf (cFittingInG M A0))ᶜ) :
    Y ⊓ fittingInG M = ⊥ := by
  have hA0F : A0 ≤ fittingInG M := isMaxElemAbelianIn_le hA0
  have hPrimes :
      OddOrder.BG.Ch2.S07.primesOf (cFittingInG M A0) =
        OddOrder.BG.Ch2.S07.primesOf (fittingInG M) := by
    dsimp [cFittingInG]
    exact primesOf_cFitting_eq_primesOf_fittingInG hA0F
  have hFpi : Subgroup.IsPiSubgroup
      (OddOrder.BG.Ch2.S07.primesOf (cFittingInG M A0)) (fittingInG M) := by
    rw [hPrimes]
    intro r hr
    simpa [OddOrder.BG.Ch2.S07.primesOf] using hr
  exact hInvariant_inf_eq_bot_of_isPiSubgroup hFpi hY

/-- BG (8.4), centralizer step: for `q ∈ π(F(M))`, the subgroup
`C_Y(O_q(Z(F(M))))` centralizes `A = C_F(M)(A0)` for every `A`-invariant
`π(A)`-complement subgroup `Y`. -/
theorem centralizer_centerFittingOpCoreInG_inf_hInvariant_le_centralizer_cFittingInG
    [Finite G] (hG : IsMinimalSimpleOdd G) {p q : ℕ} [Fact q.Prime]
    {M A0 X Y : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hA0 : isMaxElemAbelianIn p A0 (fittingInG M))
    (hq : q ∈ (Nat.card ↥(fittingInG M)).primeFactors)
    (hY : Y ∈ hInvariant X (cFittingInG M A0)
      (OddOrder.BG.Ch2.S07.primesOf (cFittingInG M A0))ᶜ) :
    Subgroup.centralizer (centerFittingOpCoreInG q M : Set G) ⊓ Y ≤
      Subgroup.centralizer (cFittingInG M A0 : Set G) := by
  let A : Subgroup G := cFittingInG M A0
  let C : Subgroup G := Subgroup.centralizer (centerFittingOpCoreInG q M : Set G) ⊓ Y
  change C ≤ Subgroup.centralizer (A : Set G)
  rw [← Subgroup.commutator_eq_bot_iff_le_centralizer]
  have hC_le_M : C ≤ M := by
    dsimp [C]
    exact inf_le_left.trans
      (centralizer_le_maximal_of_centerFittingOpCoreInG_le_fitting_primeFactor
        hG hM hq le_rfl)
  have hA_le_F : A ≤ fittingInG M := by
    dsimp [A, cFittingInG]
    exact inf_le_right
  have hM_norm_F : M ≤ Subgroup.normalizer (fittingInG M : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (fittingInG_le M)).mp
      (fittingInG_subgroupOf_normal M)
  have hC_norm_F : C ≤ Subgroup.normalizer (fittingInG M : Set G) :=
    hC_le_M.trans hM_norm_F
  have hcomm_le_Y : ⁅C, A⁆ ≤ Y := by
    have hYA : ⁅Y, A⁆ ≤ Y :=
      OddOrder.Isaacs.Ch04.commutator_le_of_le_normalizer (hInvariant_le_normalizer hY)
    exact (Subgroup.commutator_mono (by dsimp [C]; exact inf_le_right) le_rfl).trans hYA
  have hcomm_le_F : ⁅C, A⁆ ≤ fittingInG M := by
    rw [Subgroup.commutator_comm C A]
    exact (Subgroup.commutator_mono hA_le_F le_rfl).trans
      (OddOrder.Isaacs.Ch04.commutator_le_of_le_normalizer hC_norm_F)
  have hcomm_le_YF : ⁅C, A⁆ ≤ Y ⊓ fittingInG M := by
    intro x hx
    exact ⟨hcomm_le_Y hx, hcomm_le_F hx⟩
  exact le_bot_iff.mp (by
    rw [← hInvariant_inf_fittingInG_cFittingInG_eq_bot hA0 hY]
    exact hcomm_le_YF)

/-- BG (8.4), centralizer vanishing in the non-p-group case: for `q ∈ π(F(M))`,
`C_Y(O_q(Z(F(M)))) = 1`. -/
theorem centralizer_centerFittingOpCoreInG_inf_hInvariant_eq_bot_of_not_pGroup
    [Finite G] (hG : IsMinimalSimpleOdd G) {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    {M A0 X Y : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hA0 : isMaxElemAbelianIn p A0 (fittingInG M))
    (hFnp : ¬ IsPGroup p ↥(fittingInG M))
    (hq : q ∈ (Nat.card ↥(fittingInG M)).primeFactors)
    (hY : Y ∈ hInvariant X (cFittingInG M A0)
      (OddOrder.BG.Ch2.S07.primesOf (cFittingInG M A0))ᶜ) :
    Subgroup.centralizer (centerFittingOpCoreInG q M : Set G) ⊓ Y = ⊥ := by
  have hC_le_cent :=
    centralizer_centerFittingOpCoreInG_inf_hInvariant_le_centralizer_cFittingInG
      hG hM hA0 hq hY
  have hY_cent_bot :=
    hInvariant_inf_centralizer_cFittingInG_eq_bot_of_not_pGroup hG hM hA0 hFnp hY
  exact le_bot_iff.mp (by
    rw [← hY_cent_bot]
    exact le_inf inf_le_right hC_le_cent)

/-- Coprime fixed-point decomposition in ambient subgroup form: if `B` normalizes `Y`,
acts coprimely on it, and has no nontrivial fixed point in `Y`, then
`Y <= ⁅B, Y⁆`. This is the subgroup version of BG Prop. 1.6(a) used in BG (8.4). -/
theorem le_commutator_of_coprime_inf_centralizer_eq_bot [Finite G]
    {B Y : Subgroup G} [Group.IsSolvable ↥B] (hBY : B ≤ Subgroup.normalizer Y)
    (hcop : Nat.Coprime (Nat.card ↥B) (Nat.card ↥Y))
    (hfixed : Y ⊓ Subgroup.centralizer (B : Set G) = ⊥) :
    Y ≤ ⁅B, Y⁆ := by
  classical
  have hY_inv : Ch03.IsAInvariant (OddOrder.BG.Ch2.S07.conjAction B) Y :=
    OddOrder.BG.Ch2.S07.isAInvariant_conjAction_iff.mpr hBY
  have htop := OddOrder.Isaacs.Ch04.fixedPoints_sup_actionCommutator_eq_top
    (φ := hY_inv.restrict) hcop (Or.inl inferInstance)
  rw [← Subgroup.subgroupOf_eq_top, eq_top_iff, ← htop, sup_le_iff]
  refine ⟨?_, ?_⟩
  · intro x hx
    rw [Subgroup.mem_subgroupOf]
    have hx_fixed : (x : G) ∈ Y ⊓ Subgroup.centralizer (B : Set G) := by
      refine Subgroup.mem_inf.mpr ⟨x.2, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      have hval := congrArg Subtype.val
        (Subgroup.mem_fixedPointsOfMulAut.mp hx ⟨b, hb⟩)
      rw [Ch03.IsAInvariant.restrict_apply_val] at hval
      simp only [OddOrder.BG.Ch2.S07.conjAction, MonoidHom.comp_apply,
        Subgroup.coe_subtype, MulAut.conj_apply] at hval
      exact mul_inv_eq_iff_eq_mul.mp hval
    have hx_one : (x : G) = 1 := by
      simpa [hfixed] using hx_fixed
    rw [hx_one]
    exact Subgroup.one_mem _
  · rw [OddOrder.Isaacs.Ch04.actionCommutator_le_iff]
    intro a g
    rw [Subgroup.mem_subgroupOf]
    have hgen : (((hY_inv.restrict a) g * g⁻¹ : ↥Y) : G)
        = (a : G) * (g : G) * (a : G)⁻¹ * (g : G)⁻¹ := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, Ch03.IsAInvariant.restrict_apply_val]
      simp only [OddOrder.BG.Ch2.S07.conjAction, MonoidHom.comp_apply,
        Subgroup.coe_subtype, MulAut.conj_apply]
    rw [hgen]
    exact Subgroup.commutator_mem_commutator a.2 g.2

/-- The central q-core `O_q(Z(F(M)))` is solvable, since it lies in the center of `F(M)`. -/
theorem centerFittingOpCoreInG_isSolvable (q : ℕ) (M : Subgroup G) :
    Group.IsSolvable ↥(centerFittingOpCoreInG q M) := by
  have : IsMulCommutative ↥(centerFittingInG M) := centerFittingInG_isMulCommutative M
  exact Group.isSolvable_of_comm fun a b => by
    apply Subtype.ext
    exact setLike_mul_comm
      (centerFittingOpCoreInG_le_centerFittingInG q M a.2)
      (centerFittingOpCoreInG_le_centerFittingInG q M b.2)

/-- `O_q(Z(F(M)))` lies in `C_F(M)(A0)` whenever `A0 ≤ F(M)`. -/
theorem centerFittingOpCoreInG_le_cFittingInG {p q : ℕ} {M A0 : Subgroup G}
    (hA0 : isMaxElemAbelianIn p A0 (fittingInG M)) :
    centerFittingOpCoreInG q M ≤ cFittingInG M A0 :=
  (centerFittingOpCoreInG_le_centerFittingInG q M).trans
    (centerFittingInG_le_centralizer_inf (isMaxElemAbelianIn_le hA0))

/-- `O_q(Z(F(M)))` lies in the q-core of `C_F(M)(A0)`. -/
theorem centerFittingOpCoreInG_le_opiCoreInG_cFittingInG_singleton
    [Finite G] {p q : ℕ} {M A0 : Subgroup G}
    (hA0 : isMaxElemAbelianIn p A0 (fittingInG M)) :
    centerFittingOpCoreInG q M ≤ opiCoreInG ({q} : Set ℕ) (cFittingInG M A0) := by
  have hBA : centerFittingOpCoreInG q M ≤ cFittingInG M A0 :=
    centerFittingOpCoreInG_le_cFittingInG (q := q) hA0
  have hBnorm : ((centerFittingOpCoreInG q M).subgroupOf (cFittingInG M A0)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hBA]
    have hA_le_M : cFittingInG M A0 ≤ M := by
      dsimp [cFittingInG]
      exact inf_le_right.trans (fittingInG_le M)
    have hM_norm_B : M ≤ Subgroup.normalizer (centerFittingOpCoreInG q M : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer (centerFittingOpCoreInG_le q M)).mp
        (centerFittingOpCoreInG_subgroupOf_normal q M)
    exact hA_le_M.trans hM_norm_B
  have hBpi_q : Subgroup.IsPiSubgroup ({q} : Set ℕ) (centerFittingOpCoreInG q M) := by
    dsimp [centerFittingOpCoreInG]
    exact isPiSubgroup_opiCoreInG ({q} : Set ℕ) (centerFittingInG M)
  exact le_opiCoreInG_of_normal_of_isPiSubgroup hBA hBnorm hBpi_q

/-- If `r ≠ q`, then the central `r`-core of `F(M)` lies in the `q`-complement
core of `C_F(M)(A0)`. This is the `A_r ≤ O_{q'}(A)` input for BG (8.7). -/
theorem centerFittingOpCoreInG_le_opiCoreInG_cFittingInG_singleton_compl_of_ne
    [Finite G] {p q r : ℕ} {M A0 : Subgroup G}
    (hA0 : isMaxElemAbelianIn p A0 (fittingInG M)) (hqr : q ≠ r) :
    centerFittingOpCoreInG r M ≤ opiCoreInG ({q} : Set ℕ)ᶜ (cFittingInG M A0) := by
  have hBA : centerFittingOpCoreInG r M ≤ cFittingInG M A0 :=
    centerFittingOpCoreInG_le_cFittingInG (q := r) hA0
  have hBnorm : ((centerFittingOpCoreInG r M).subgroupOf (cFittingInG M A0)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hBA]
    have hA_le_M : cFittingInG M A0 ≤ M := by
      dsimp [cFittingInG]
      exact inf_le_right.trans (fittingInG_le M)
    have hM_norm_B : M ≤ Subgroup.normalizer (centerFittingOpCoreInG r M : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer (centerFittingOpCoreInG_le r M)).mp
        (centerFittingOpCoreInG_subgroupOf_normal r M)
    exact hA_le_M.trans hM_norm_B
  have hBpi_r : Subgroup.IsPiSubgroup ({r} : Set ℕ) (centerFittingOpCoreInG r M) := by
    dsimp [centerFittingOpCoreInG]
    exact isPiSubgroup_opiCoreInG ({r} : Set ℕ) (centerFittingInG M)
  have hBpi_qcompl : Subgroup.IsPiSubgroup ({q} : Set ℕ)ᶜ (centerFittingOpCoreInG r M) := by
    refine hBpi_r.mono ?_
    intro s hs hsq
    rw [Set.mem_singleton_iff] at hs hsq
    exact hqr (hsq.symm.trans hs)
  exact le_opiCoreInG_of_normal_of_isPiSubgroup hBA hBnorm hBpi_qcompl

/-- BG (8.2) applied to `O_{q'}(C_F(M)(A0))`: if `r ≠ q` is another Fitting
prime, then the centralizer of this `q`-complement core lies in `M`. -/
theorem centralizer_opiCoreInG_cFittingInG_singleton_compl_le_maximal_of_ne
    [Finite G] (hG : IsMinimalSimpleOdd G) {p q r : ℕ} {M A0 : Subgroup G}
    (hM : M ∈ maximalSubgroups G)
    (hA0 : isMaxElemAbelianIn p A0 (fittingInG M))
    (hr : r ∈ (Nat.card ↥(fittingInG M)).primeFactors) (hqr : q ≠ r) :
    Subgroup.centralizer (opiCoreInG ({q} : Set ℕ)ᶜ (cFittingInG M A0) : Set G) ≤ M := by
  have : Fact r.Prime := ⟨Nat.prime_of_mem_primeFactors hr⟩
  exact centralizer_le_maximal_of_centerFittingOpCoreInG_le hG hM
    (centerFittingOpCoreInG_ne_bot_of_mem_primeFactors_fittingInG hr)
    (centerFittingOpCoreInG_le_opiCoreInG_cFittingInG_singleton_compl_of_ne hA0 hqr)

/-- BG (8.2) applied to `O_{q'}(C_F(M)(A0))` in the non-`p`-group case. -/
theorem centralizer_opiCoreInG_cFittingInG_singleton_compl_le_maximal_of_not_pGroup
    [Finite G] (hG : IsMinimalSimpleOdd G) {p q : ℕ} [Fact p.Prime]
    {M A0 : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hp : p ∈ (Nat.card ↥(fittingInG M)).primeFactors)
    (hA0 : isMaxElemAbelianIn p A0 (fittingInG M))
    (hFnp : ¬ IsPGroup p ↥(fittingInG M))
    (_hq : q ∈ (Nat.card ↥(fittingInG M)).primeFactors) :
    Subgroup.centralizer (opiCoreInG ({q} : Set ℕ)ᶜ (cFittingInG M A0) : Set G) ≤ M := by
  obtain ⟨r, hr, hrq⟩ :=
    exists_primeFactor_ne_of_mem_primeFactor_not_isPGroup
      (H := ↥(fittingInG M)) hp hFnp q
  exact centralizer_opiCoreInG_cFittingInG_singleton_compl_le_maximal_of_ne
    hG hM hA0 hr (fun hqr => hrq hqr.symm)

/-- BG (8.7), conditional endpoint: once `O_{q'}(C_F(M)(A0))` is absorbed by
`O_{q'}(H)`, the q-core of `F(H)` lies in the original maximal subgroup `M`. -/
theorem opiCoreInG_fittingInG_singleton_le_maximal_of_cFittingInG_compl_le_opiCoreInG_compl
    [Finite G] (hG : IsMinimalSimpleOdd G) {p q : ℕ} [Fact p.Prime]
    {M A0 H : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hp : p ∈ (Nat.card ↥(fittingInG M)).primeFactors)
    (hA0 : isMaxElemAbelianIn p A0 (fittingInG M))
    (hFnp : ¬ IsPGroup p ↥(fittingInG M))
    (hq : q ∈ (Nat.card ↥(fittingInG M)).primeFactors)
    (hcore : opiCoreInG ({q} : Set ℕ)ᶜ (cFittingInG M A0) ≤
      opiCoreInG ({q} : Set ℕ)ᶜ H) :
    opiCoreInG ({q} : Set ℕ) (fittingInG H) ≤ M := by
  have hcent :
      opiCoreInG ({q} : Set ℕ) (fittingInG H) ≤
        Subgroup.centralizer
          (opiCoreInG ({q} : Set ℕ)ᶜ (cFittingInG M A0) : Set G) :=
    opiCoreInG_fittingInG_le_centralizer_of_le_opiCoreInG_compl ({q} : Set ℕ) hcore
  exact hcent.trans
    (centralizer_opiCoreInG_cFittingInG_singleton_compl_le_maximal_of_not_pGroup
      hG hM hp hA0 hFnp hq)

/-- Members of `ℋ_X(C_F(M)(A0); π(C_F(M)(A0))^c)` are normalized by
`O_q(Z(F(M)))`. -/
theorem centerFittingOpCoreInG_le_normalizer_of_hInvariant
    {p q : ℕ} {M A0 X Y : Subgroup G}
    (hA0 : isMaxElemAbelianIn p A0 (fittingInG M))
    (hY : Y ∈ hInvariant X (cFittingInG M A0)
      (OddOrder.BG.Ch2.S07.primesOf (cFittingInG M A0))ᶜ) :
    centerFittingOpCoreInG q M ≤ Subgroup.normalizer Y :=
  (centerFittingOpCoreInG_le_cFittingInG (q := q) hA0).trans
    (hInvariant_le_normalizer hY)

end OddOrder.BG.Ch2.S08


