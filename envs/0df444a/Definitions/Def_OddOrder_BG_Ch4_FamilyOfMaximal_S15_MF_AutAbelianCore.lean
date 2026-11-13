-- Prove2me | Definitions.Def_OddOrder_BG_Ch4_FamilyOfMaximal_S15_MF_AutAbelianCore
-- name    : OddOrder_BG_Ch4_FamilyOfMaximal_S15_MF_AutAbelianCore
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T09:49:27.422946+00:00
-- url     : https://prove2.me/theorems/41352679-d12a-4222-bd18-8941a3b30141
-- title:
--   BG §15: notation and the Aut-abelian core
-- statement:
--   The §15 notation layer of Bender–Glauberman, *Local Analysis for the Odd Order Theorem* and the reusable Aut-abelian core independent of §14. It introduces $M_F$ (the maximal nilpotent normal Hall subgroup of $M$), the Fitting subgroup of $M$ in the ambient group, its nonidentity part, and the hypothesis that $F(M)$ is a TI-subgroup of $G$, together with the core fact that $H'\le C_H(N)$ when $N\trianglelefteq H$ is cyclic.
--
--   Main declarations: `MF` (BG `M_F`: the maximal nilpotent normal Hall subgroup of `M`); `fittingInAmbient` (The Fitting subgroup of `M`, viewed in the ambient group as in BG §8/§15); `fittingSharp` (The nonidentity part of the ambient Fitting subgroup of `M`); `FittingIsTI` (The BG §15 hypothesis that `F(M)` is a TI-subgroup of `G`); and 3 more.
--
--   The bundle also proves 16 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/Ch4_FamilyOfMaximal/S15_MF/AutAbelianCore.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/BG/Ch4_FamilyOfMaximal/S15_MF/AutAbelianCore.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_BG_Ch4_FamilyOfMaximal_S14_TypePCounting_Basics
import Definitions.Def_OddOrder_BG_Ch4_FamilyOfMaximal_S14_TypePCounting_LocalStructure
import Definitions.Def_OddOrder_BG_Ch4_FamilyOfMaximal_S14_TypePCounting_SigmaLengthOne
import Definitions.Def_OddOrder_BG_Ch4_FamilyOfMaximal_S14_TypePCounting_TypePDuality
import Definitions.Def_OddOrder_BG_Ch4_FamilyOfMaximal_S14_TypePCounting_GlobalCounting
import Definitions.Def_OddOrder_BG_Ch1_Preliminary_S03h_Thm38
import Definitions.Def_OddOrder_BG_Ch1_Preliminary_S03g_Thm310ElemAbelian
import Definitions.Def_OddOrder_BG_Ch1_Preliminary_S05_NarrowCharacterization
import Definitions.Def_OddOrder_Mathlib_Subgroup

namespace OddOrder.BG.Ch4.S15

open OddOrder.GroupTheory

open OddOrder.Isaacs

open OddOrder.BG.Ch3.S12

open OddOrder.BG.Ch4.S14

open scoped Pointwise

open scoped IsMulCommutative

open scoped commutatorElement

variable {G : Type*} [Group G]

/-- **BG `M_F`**: the maximal nilpotent normal Hall subgroup of `M`. -/
noncomputable abbrev MF (M : Subgroup G) : Subgroup G :=
  maxNilpotentNormalHall M

/-- `M_F ≤ M`: basic containment, directly from the `sSup` construction.  (The §15
well-definedness that the `sSup` is again Hall is `maxNilpotentNormalHall_isHall` below; this
containment is the more elementary half.) -/
theorem maxNilpotentNormalHall_le (M : Subgroup G) : maxNilpotentNormalHall M ≤ M :=
  sSup_le fun _ hN => hN.1

set_option backward.isDefEq.respectTransparency false in
/-- `M` normalizes `M_F` (so `(M_F).subgroupOf M ⊴ M`): the `sSup` of `M`-normal
candidates is again `M`-normal.  Like `maxNilpotentNormalHall_le`, this is part of the
`§14`-independent §15 well-definedness (the Hall property is `maxNilpotentNormalHall_isHall`);
each candidate `N` is fixed by conjugation by `m ∈ M` because `(N.subgroupOf M).Normal`. -/
theorem maxNilpotentNormalHall_le_normalizer (M : Subgroup G) :
    M ≤ Subgroup.normalizer (maxNilpotentNormalHall M) := by
  intro m hm
  refine mem_normalizer_of_conj_smul_eq_self ?_
  unfold maxNilpotentNormalHall
  rw [Subgroup.pointwise_smul_def, (Subgroup.gc_map_comap _).l_sSup, sSup_eq_iSup]
  refine iSup_congr fun N => iSup_congr fun hN => ?_
  rw [← Subgroup.pointwise_smul_def]
  obtain ⟨hNM, hNnorm, -, -⟩ := hN
  exact conj_smul_eq_self_of_mem_normalizer
    (((Subgroup.normal_subgroupOf_iff_le_normalizer hNM).mp hNnorm) hm)

/-- `M_F ⊴ M` in the relative sense `(M_F).subgroupOf M`: the directly usable form of
`maxNilpotentNormalHall_le_normalizer`, matching the normality clause in the defining
predicate of `M_F`. -/
theorem maxNilpotentNormalHall_subgroupOf_normal (M : Subgroup G) :
    ((maxNilpotentNormalHall M).subgroupOf M).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (maxNilpotentNormalHall_le M)).mpr
    (maxNilpotentNormalHall_le_normalizer M)

/-- `M_F ≤ F(M)`: the maximal nilpotent normal Hall subgroup lies inside the Fitting subgroup
`F(M)` (`OddOrder.BG.Ch2.S08.fittingInG`, defeq `(Ch01.fitting ↥M).map M.subtype`), because each
candidate `N` is nilpotent and normal in `M` (so `N.subgroupOf M ≤ fitting ↥M`).  `§14`-independent;
the structural bridge between `M_F` and `F(M)` used throughout §15/§16. -/
theorem maxNilpotentNormalHall_le_fittingInG [Finite G] (M : Subgroup G) :
    maxNilpotentNormalHall M ≤ OddOrder.BG.Ch2.S08.fittingInG M := by
  refine sSup_le fun N hN => ?_
  obtain ⟨hNM, hNnorm, hNnil, -⟩ := hN
  have := hNnorm
  have := hNnil
  calc N = (N.subgroupOf M).map M.subtype := (Subgroup.map_subgroupOf_eq_of_le hNM).symm
    _ ≤ OddOrder.BG.Ch2.S08.fittingInG M :=
        Subgroup.map_mono OddOrder.Isaacs.Ch01.nilpotent_normal_le_fitting

/-- **`M_F` is nilpotent** — the §15 well-definedness piece that the defining `sSup` is again
nilpotent.  `M_F ≤ F(M)` (`maxNilpotentNormalHall_le_fittingInG`) and `F(M)` is nilpotent
(image of the nilpotent `fitting ↥M` under the injective `M.subtype`).  `§14`-independent. -/
theorem maxNilpotentNormalHall_isNilpotent [Finite G] (M : Subgroup G) :
    Group.IsNilpotent ↥(maxNilpotentNormalHall M) := by
  have : Group.IsNilpotent ↥(OddOrder.Isaacs.Ch01.fitting (↥M)) :=
    OddOrder.Isaacs.Ch01.fitting.isNilpotent
  have : Group.IsNilpotent ↥(OddOrder.BG.Ch2.S08.fittingInG M) :=
    Group.nilpotent_of_mulEquiv
      (Subgroup.equivMapOfInjective (OddOrder.Isaacs.Ch01.fitting (↥M)) M.subtype
        M.subtype_injective)
  exact Group.nilpotent_of_mulEquiv
    (Subgroup.subgroupOfEquivOfLe (maxNilpotentNormalHall_le_fittingInG M))

/-- **`M_F` absorbs every nilpotent normal Hall subgroup** (`§14`-independent): a subgroup `N ≤ M`
that is `M`-normal (`(N.subgroupOf M).Normal`), nilpotent, and a Hall `π(N)`-subgroup of `M`
(`IsHallSubgroup (Nat.card ↥N).primeFactors (N.subgroupOf M)`) is one of the candidates in the
`sSup` defining `M_F = maxNilpotentNormalHall M`, hence `≤ M_F`.  This is the `le_sSup` half of the
`M_F` characterization (the converse `M_F ≤ M_σ` is `maxNilpotentNormalHall_le_Msigma`); it supplies
`Q ≤ M_F` in Theorem 15.2 once `Q = O_q(M)` is shown to be such a subgroup. -/
theorem le_maxNilpotentNormalHall {M N : Subgroup G} (hNM : N ≤ M)
    (hNnorm : (N.subgroupOf M).Normal) (hNnil : Group.IsNilpotent ↥(N.subgroupOf M))
    (hNhall : OddOrder.Isaacs.Ch03.IsHallSubgroup (Nat.card ↥N).primeFactors (N.subgroupOf M)) :
    N ≤ maxNilpotentNormalHall M :=
  le_sSup ⟨hNM, hNnorm, hNnil, hNhall⟩

/-- If `M_σ` is nilpotent, then `M_σ ≤ M_F`: `M_σ` is then a nilpotent normal Hall subgroup of
`M` (normal `σ`-core, `σ`-Hall by `Msigma_isHall`, nilpotent by hypothesis), hence one of the
candidates in the `sSup` defining `M_F`.  `§14`-independent.  Combined with the (gated)
`M_F ≤ M_σ` of Theorem A this gives `M_F = M_σ ⟺ M_σ` nilpotent (recall `M_F` is always
nilpotent, `maxNilpotentNormalHall_isNilpotent`). -/
theorem Msigma_le_maxNilpotentNormalHall_of_nilpotent [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hnil : Group.IsNilpotent ↥(OddOrder.BG.Ch3.S10.Msigma M)) :
    OddOrder.BG.Ch3.S10.Msigma M ≤ maxNilpotentNormalHall M := by
  have := hnil
  have hle := OddOrder.BG.Ch3.S10.Msigma_le M
  have hcard : Nat.card ↥((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M) =
      Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma M) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
  apply le_sSup
  refine ⟨hle, ?_, ?_, ?_⟩
  · rw [OddOrder.BG.Ch3.S10.Msigma_subgroupOf]; infer_instance
  · exact Group.nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hle).symm
  · obtain ⟨hHcard, hHidx⟩ := OddOrder.BG.Ch3.S10.Msigma_isHall hG hM
    refine ⟨fun q hq => by rwa [hcard] at hq, fun q hq hqπ => ?_⟩
    obtain ⟨hqp, hqd, -⟩ := Nat.mem_primeFactors.mp hq
    have hdvd : ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M).index ∣
        (OddOrder.BG.Ch3.S10.Msigma M).index :=
      Subgroup.relIndex_dvd_index_of_le hle
    exact hHidx q
      (Nat.mem_primeFactors.mpr ⟨hqp, hqd.trans hdvd, Subgroup.index_ne_zero_of_finite⟩)
      (hHcard q hqπ)

/-- **`M_F ≤ M_σ`** (BG §15, mmd L4116 "it is easy to see ... `M_F` ... lies in `M_σ`").
Every nilpotent normal Hall subgroup `N` of `M` is a `σ(M)`-group: for a prime `p ∣ |N|`, the
Sylow `p`-subgroup of `N` is characteristic in `N` (nilpotent) hence normal in `M`, and a full
Sylow `p`-subgroup of `M` (`N` Hall), so it maps to `O_p(M)`; minimality of `M` and simplicity
of `G` give `N_G(O_p(M)) ≤ M`, i.e. `p ∈ σ(M)`.  Then `N ≤ O_{σ(M)}(M) = M_σ` by maximality of
the `σ(M)`-core.  `§14`-independent. -/
theorem maxNilpotentNormalHall_le_Msigma [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G) :
    maxNilpotentNormalHall M ≤ OddOrder.BG.Ch3.S10.Msigma M := by
  refine sSup_le fun N hN => ?_
  obtain ⟨hNM, hNnorm, hNnil, hNHall⟩ := hN
  have := hNnorm
  have := hNnil
  set N' : Subgroup ↥M := N.subgroupOf M with hN'def
  have hcardN' : Nat.card ↥N' = Nat.card ↥N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNM).toEquiv
  -- `N'` is a `σ(M)`-group: every prime divisor of `|N|` lies in `σ(M)`.
  have hpi : OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup (OddOrder.BG.Ch3.S10.sigma M) N' := by
    intro p hp
    have hpN : p ∈ (Nat.card ↥N).primeFactors := by rwa [hcardN'] at hp
    have : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors hp⟩
    have hpM : p ∈ (Nat.card ↥M).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨‹Fact p.Prime›.1,
        (Nat.dvd_of_mem_primeFactors hpN).trans
          (hcardN' ▸ Subgroup.card_subgroup_dvd_card N'), Nat.card_pos.ne'⟩
    -- `p ∤ [M : N']` (Hall), so the `p`-part of `|M|` is concentrated in `N'`.
    have hpidx : ¬ p ∣ N'.index := fun hdvd =>
      hNHall.2 p (Nat.mem_primeFactors.mpr
        ⟨‹Fact p.Prime›.1, hdvd, Subgroup.index_ne_zero_of_finite⟩) hpN
    have hfact : (Nat.card ↥M).factorization p = (Nat.card ↥N').factorization p := by
      conv_lhs => rw [← Subgroup.card_mul_index N']
      rw [Nat.factorization_mul Nat.card_pos.ne' Subgroup.index_ne_zero_of_finite,
        Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hpidx, add_zero]
    -- The Sylow `p`-subgroup of the nilpotent `N'` is characteristic, hence normal in `M`,
    -- and (Hall) a full Sylow `p`-subgroup of `M`.
    obtain ⟨SN⟩ := (inferInstance : Nonempty (Sylow p ↥N'))
    have hSNnorm : (SN : Subgroup ↥N').Normal :=
      OddOrder.Isaacs.Ch01.Sylow.normal_of_isNilpotent SN
    have hSNchar : (SN : Subgroup ↥N').Characteristic :=
      Sylow.characteristic_of_normal SN hSNnorm
    have hScard : Nat.card ↥((SN : Subgroup ↥N').map N'.subtype) =
        p ^ (Nat.card ↥M).factorization p := by
      rw [Subgroup.card_map_of_injective N'.subtype_injective, SN.card_eq_multiplicity, hfact]
    have hmapnorm : ((SN : Subgroup ↥N').map N'.subtype).Normal := inferInstance
    let P : Sylow p ↥M := Sylow.ofCard ((SN : Subgroup ↥N').map N'.subtype) hScard
    have hPnorm : (P : Subgroup ↥M).Normal := hmapnorm
    have hPmap : (P : Subgroup ↥M).map M.subtype = OddOrder.GroupTheory.opiCoreInG {p} M :=
      OddOrder.BG.Ch3.S10.sylowMap_eq_opiCoreInG_singleton_of_normal P hPnorm
    have hPne : OddOrder.GroupTheory.opiCoreInG {p} M ≠ ⊥ :=
      OddOrder.BG.Ch3.S10.opiCoreInG_singleton_ne_bot_of_sylowMap_eq hpM P hPmap
    rw [OddOrder.BG.Ch3.S10.mem_sigma_iff]
    refine ⟨hpM, P, ?_⟩
    rw [hPmap]
    exact OddOrder.BG.Ch2.S09.normalizer_opiCoreInG_singleton_le_maximal_of_ne_bot hG hM hPne
  calc N = N'.map M.subtype := (Subgroup.map_subgroupOf_eq_of_le hNM).symm
    _ ≤ (OddOrder.Isaacs.Ch03.oPiCore (OddOrder.BG.Ch3.S10.sigma M) ↥M).map M.subtype :=
        Subgroup.map_mono hpi.le_oPiCore
    _ = OddOrder.BG.Ch3.S10.Msigma M := rfl

/-- **`M_F = M_σ ⟺ M_σ` is nilpotent** (`§14`-independent).  Forward: `M_F` is always nilpotent
(`maxNilpotentNormalHall_isNilpotent`).  Backward: `maxNilpotentNormalHall_le_Msigma` (always)
and `Msigma_le_maxNilpotentNormalHall_of_nilpotent` give equality by antisymmetry. -/
theorem maxNilpotentNormalHall_eq_Msigma_iff_isNilpotent [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G) :
    maxNilpotentNormalHall M = OddOrder.BG.Ch3.S10.Msigma M ↔
      Group.IsNilpotent ↥(OddOrder.BG.Ch3.S10.Msigma M) := by
  refine ⟨fun h => h ▸ maxNilpotentNormalHall_isNilpotent M, fun hnil => ?_⟩
  exact le_antisymm (maxNilpotentNormalHall_le_Msigma hG hM)
    (Msigma_le_maxNilpotentNormalHall_of_nilpotent hG hM hnil)

/-- **`M_F ≤ M'`** (the `H ⊆ M'` part of BG Corollary 15.5(c), `H = M_F`): the containment chain
`M_F ≤ M_σ ≤ M' ≤ M` via `maxNilpotentNormalHall_le_Msigma` and `Msigma_le_derived`.
`§14`-independent.  ⚠ The other half of 15.5(c), "`M'/M_F` is nilpotent", is **proved** as
`S16.derivedInG_quotient_maxNilpotentNormalHall_isNilpotent` (downstream, so it cannot appear in
a §15 statement without an import cycle).  The old "remains deferred — quotient API" note was
stale; corrected in the issue 0177 §15 audit (2026-08-08). -/
theorem maxNilpotentNormalHall_le_derived [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G) :
    maxNilpotentNormalHall M ≤ derivedInG M :=
  (maxNilpotentNormalHall_le_Msigma hG hM).trans (OddOrder.BG.Ch3.S10.Msigma_le_derived hG hM)

/-- **General helper (§14-independent, reusable).**  In a finite group, the `sSup` of a set `s`
of normal `π`-subgroups is again a `π`-subgroup.  (Mirrors the `Finset.sup_induction` argument of
`Ch03.oPiCore.isPiGroup`, but for an arbitrary set rather than the defining family of `oPiCore`.)
Used for the §15 well-definedness "`M_F` is Hall": the supremum defining `M_F` collapses to a join
of normal subgroups, whose order has no new prime factors. -/
theorem isPiGroup_sSup_of_forall_normal {H : Type*} [Group H] [Finite H] (π : Set ℕ)
    (s : Set (Subgroup H)) (hnorm : ∀ N ∈ s, N.Normal)
    (hpi : ∀ N ∈ s, Ch03.Subgroup.IsPiGroup π N) :
    Ch03.Subgroup.IsPiGroup π (sSup s) := by
  classical
  have hSubF : Fintype {N : Subgroup H // N ∈ s} := Fintype.ofFinite _
  -- Carry both normality and the `π`-group property through the induction.
  set q : Subgroup H → Prop := fun K => K.Normal ∧ Ch03.Subgroup.IsPiGroup π K with hq_def
  suffices hgoal : q (sSup s) by exact hgoal.2
  -- Rewrite the `sSup` as a `Finset.sup` over the (finite) subtype `{N // N ∈ s}`.
  have hsup : sSup s =
      (Finset.univ : Finset {N : Subgroup H // N ∈ s}).sup (fun N => (N.val : Subgroup H)) := by
    rw [Finset.sup_eq_iSup]
    simp only [iSup_pos, Finset.mem_univ]
    rw [← sSup_eq_iSup']
  rw [hsup]
  refine Finset.sup_induction (p := q) ?_ ?_ ?_
  · -- `⊥` is a normal `π`-group (no prime factors).
    refine ⟨inferInstance, ?_⟩
    intro r hr
    simp only [Subgroup.card_bot, Nat.primeFactors_one, Finset.notMem_empty] at hr
  · -- closure under join of two normal `π`-subgroups.
    rintro a₁ ⟨ha₁N, ha₁Pi⟩ a₂ ⟨ha₂N, ha₂Pi⟩
    have := ha₁N
    have := ha₂N
    exact ⟨inferInstance, Ch03.Subgroup.IsPiGroup.sup_of_normal ha₁Pi ha₂Pi⟩
  · -- each generator is a normal `π`-group by hypothesis.
    intro b _
    exact ⟨hnorm b.val b.2, hpi b.val b.2⟩

/-- **BG §15 well-definedness: `M_F` is a Hall subgroup of `M`** (general finite-group fact,
§14-independent; no minimal-simple hypothesis needed).  `M_F = maxNilpotentNormalHall M` is, as a
relative subgroup `(M_F).subgroupOf M ⊴ M`, a `π(M_F)`-Hall subgroup of `M`, where
`π(M_F) = (Nat.card ↥(M_F)).primeFactors`.

Proof: `(M_F).subgroupOf M` is the join (in `↥M`) of the normal subgroups `N.subgroupOf M`
ranging over the candidates `N` of the `sSup` defining `M_F`; this join has no prime factor beyond
those of the candidates (`isPiGroup_sSup_of_forall_normal`).  Hence every prime `p ∣ |M_F|` divides
some candidate `|N₀|`, and that candidate is `π(N₀)`-Hall in `↥M` with `p ∈ π(N₀)`, so
`p ∤ [M : N₀.subgroupOf M]`; since `N₀.subgroupOf M ≤ (M_F).subgroupOf M`, also `p ∤ [M : M_F]`.
The index of `(M_F).subgroupOf M` therefore shares no prime with `|M_F|`, i.e. `M_F` is Hall. -/
theorem maxNilpotentNormalHall_isHall [Finite G] (M : Subgroup G) :
    Ch03.IsHallSubgroup (Nat.card ↥(maxNilpotentNormalHall M)).primeFactors
      ((maxNilpotentNormalHall M).subgroupOf M) := by
  classical
  set H : Subgroup G := maxNilpotentNormalHall M with hHdef
  set Hbar : Subgroup ↥M := H.subgroupOf M with hHbar
  -- The defining set of `M_F`, and its image in `↥M`.
  set S : Set (Subgroup G) := {N : Subgroup G | N ≤ M ∧ (N.subgroupOf M).Normal ∧
      Group.IsNilpotent ↥(N.subgroupOf M) ∧
      Ch03.IsHallSubgroup (Nat.card ↥N).primeFactors (N.subgroupOf M)} with hSdef
  have hHsSup : H = sSup S := rfl
  set T : Set (Subgroup ↥M) := (fun N => N.subgroupOf M) '' S with hTdef
  -- `card Hbar = card H` (since `H ≤ M`).
  have hHle : H ≤ M := maxNilpotentNormalHall_le M
  have hcardHbar : Nat.card ↥Hbar = Nat.card ↥H :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHle).toEquiv
  -- `⨆ x ∈ T, map x = ⨆ N ∈ S, N`, since `map (N.subgroupOf M) = N` for `N ≤ M ∈ S`.
  have hiSup : (⨆ x ∈ T, x.map M.subtype) = ⨆ N ∈ S, N := by
    rw [hTdef, iSup_image]
    refine iSup_congr fun N => iSup_congr fun hN => ?_
    exact Subgroup.map_subgroupOf_eq_of_le hN.1
  -- Key identification: `Hbar = sSup T`.
  have hHbar_eq : Hbar = sSup T := by
    apply Subgroup.map_injective M.subtype_injective
    rw [hHbar, Subgroup.map_subgroupOf_eq_of_le hHle, hHsSup,
      (Subgroup.gc_map_comap M.subtype).l_sSup, hiSup, ← sSup_eq_iSup]
  -- Every element of `T` is normal in `↥M` and a `Pri`-group, where `Pri` is the set of primes
  -- occurring in some candidate's order.
  set Pri : Set ℕ := {p | ∃ N ∈ S, p ∈ (Nat.card ↥N).primeFactors} with hPridef
  have hTnorm : ∀ x ∈ T, x.Normal := by
    rintro x ⟨N, hN, rfl⟩; exact hN.2.1
  have hTpi : ∀ x ∈ T, Ch03.Subgroup.IsPiGroup Pri x := by
    rintro x ⟨N, hN, rfl⟩
    intro p hp
    -- `card (N.subgroupOf M) = card N`, so a prime factor of it is one of `N`.
    have hcardN : Nat.card ↥(N.subgroupOf M) = Nat.card ↥N :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hN.1).toEquiv
    exact ⟨N, hN, by rwa [hcardN] at hp⟩
  -- Hence `Hbar` is a `Pri`-group.
  have hHbarpi : Ch03.Subgroup.IsPiGroup Pri Hbar := by
    rw [hHbar_eq]; exact isPiGroup_sSup_of_forall_normal Pri T hTnorm hTpi
  -- Assemble the Hall property.
  refine ⟨fun p hp => ?_, fun p hp hpπ => ?_⟩
  · -- Prime factors of `|Hbar| = |H|` are exactly `π(M_F)`.
    rwa [hcardHbar] at hp
  · -- `p ∈ π(M_F)` and `p ∣ [M : Hbar]`: derive a contradiction.
    have : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors hp⟩
    -- `p ∈ π(M_F)`, so `p ∣ |Hbar|`, so `p ∈ Π`: pick a candidate `N₀` with `p ∣ |N₀|`.
    have hpHbar : p ∈ (Nat.card ↥Hbar).primeFactors := by
      rw [hcardHbar]; exact hpπ
    obtain ⟨N₀, hN₀, hpN₀⟩ := hHbarpi p hpHbar
    -- `N₀.subgroupOf M` is `π(N₀)`-Hall with `p ∈ π(N₀)`, so `p ∤ [M : N₀.subgroupOf M]`.
    have hpN₀Hall : ¬ p ∣ (N₀.subgroupOf M).index := by
      intro hdvd
      exact hN₀.2.2.2.2 p
        (Nat.mem_primeFactors.mpr ⟨Fact.out, hdvd, Subgroup.index_ne_zero_of_finite⟩) hpN₀
    -- `N₀.subgroupOf M ≤ Hbar`, so `[M : Hbar] ∣ [M : N₀.subgroupOf M]`, so `p ∤ [M : Hbar]`.
    have hN₀_le_H : N₀ ≤ H := hHsSup ▸ le_sSup hN₀
    have hle : N₀.subgroupOf M ≤ Hbar := by
      rw [hHbar]; exact Subgroup.subgroupOf_mono M hN₀_le_H
    exact hpN₀Hall ((Nat.mem_primeFactors.mp hp).2.1.trans (Subgroup.index_dvd_of_le hle))

/-- The Fitting subgroup of `M`, viewed in the ambient group as in BG §8/§15. -/
noncomputable abbrev fittingInAmbient (M : Subgroup G) : Subgroup G :=
  OddOrder.BG.Ch2.S08.fittingInG M

/-- **`F(H) = H` for a nilpotent subgroup `H`** (`§14`-independent, reusable): the Fitting
subgroup of a nilpotent group is the whole group (`fitting ↥H = ⊤`), so its ambient realization
`fittingInAmbient H` is just `H`.  Used by Corollary 15.5 (the `M_F = M_σ` case, where `M_σ` is
nilpotent so `F(M_σ) = M_σ = M_F`) and the `M_F` cyclic ⟹ `F(M)` cyclic step of Corollary 15.6. -/
theorem fittingInAmbient_eq_self_of_isNilpotent [Finite G] {H : Subgroup G}
    [Group.IsNilpotent ↥H] : fittingInAmbient H = H := by
  have : Group.IsNilpotent ↥(⊤ : Subgroup ↥H) :=
    Group.nilpotent_of_mulEquiv Subgroup.topEquiv.symm
  have htop : OddOrder.Isaacs.Ch01.fitting ↥H = ⊤ :=
    top_le_iff.mp OddOrder.Isaacs.Ch01.nilpotent_normal_le_fitting
  change (OddOrder.Isaacs.Ch01.fitting ↥H).map H.subtype = H
  rw [htop, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

/-- **Converse of `fittingInAmbient_eq_self_of_isNilpotent`** (`§14`-independent, reusable): if the
ambient realization of the Fitting subgroup is all of `H` (`fittingInAmbient H = H`), then `H` is
nilpotent.  Together with the forward direction this is `IsNilpotent ↥H ↔ fittingInAmbient H = H`.

Used in Theorem 15.2's step 2 (the contrapositive of Theorem 3.8): from `⁅M_σ, K⁆ = M_σ ⊆ F(M_σ)`
one gets `F(M_σ) = M_σ`, hence `M_σ` nilpotent — contradicting `M_F ≠ M_σ`. -/
theorem isNilpotent_of_fittingInAmbient_eq_self [Finite G] {H : Subgroup G}
    (h : fittingInAmbient H = H) : Group.IsNilpotent ↥H := by
  have htop : OddOrder.Isaacs.Ch01.fitting ↥H = ⊤ := by
    apply Subgroup.map_injective H.subtype_injective
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    exact h
  have hnil : Group.IsNilpotent ↥(OddOrder.Isaacs.Ch01.fitting ↥H) :=
    OddOrder.Isaacs.Ch01.fitting.isNilpotent
  rw [htop] at hnil
  have := hnil
  exact Group.nilpotent_of_mulEquiv Subgroup.topEquiv

/-- The conjugation action commutator of `H` on itself is the ordinary derived subgroup:
`actionCommutator (MulAut.conj) = commutator H`.  (Both are the closure of the commutator
elements `g * (a g⁻¹ a⁻¹) = ⁅g, a⁆`.) -/
private theorem actionCommutator_conj_eq_commutator {H : Type*} [Group H] :
    OddOrder.Isaacs.Ch04.actionCommutator (MulAut.conj : H →* MulAut H) = commutator H := by
  rw [commutator_eq_closure]
  unfold OddOrder.Isaacs.Ch04.actionCommutator
  congr 1
  ext x
  simp only [Set.mem_ofPred_eq, commutatorSet_def]
  constructor
  · rintro ⟨g, a, rfl⟩
    exact ⟨g, a, by rw [commutatorElement_def, MulAut.conj_apply]; group⟩
  · rintro ⟨g₁, g₂, rfl⟩
    exact ⟨g₁, g₂, by rw [commutatorElement_def, MulAut.conj_apply]; group⟩

open OddOrder.BG.Ch1.OperatorQuotientAction in
/-- **Aut-abelian core**: if `N ⊴ H` is cyclic, then `H' ≤ C_H(N)`.  Conjugation gives a
homomorphism `H → Aut(↥N)` with kernel `C_H(N)`; `↥N` cyclic makes `Aut(↥N)` abelian, so the
derived subgroup `H'` lands in the kernel.  Reuses the BG Thm 4.12 machinery
(`actionCommutator_le_centralizer_of_isCyclic_isAInvariant`) with `φ = MulAut.conj`. -/
theorem commutator_le_centralizer_of_normal_isCyclic {H : Type*} [Group H]
    {N : Subgroup H} [IsCyclic ↥N] (hN : N.Normal) :
    commutator H ≤ Subgroup.centralizer (N : Set H) := by
  have hinv : OddOrder.Isaacs.Ch03.IsAInvariant (MulAut.conj : H →* MulAut H) N := by
    rw [OddOrder.Isaacs.Ch03.isAInvariant_iff_smul_mem]
    intro a g hg
    rw [MulAut.conj_apply]
    exact hN.conj_mem g hg a
  have h := actionCommutator_le_centralizer_of_isCyclic_isAInvariant
    (φ := (MulAut.conj : H →* MulAut H)) (S := N) hN hinv
  rwa [actionCommutator_conj_eq_commutator] at h

/-- **BG §15, `F(M)` cyclic ⟹ `M'' = 1`** (`§14`-independent).  If the ambient Fitting subgroup
`F(M)` is cyclic then `M' ≤ C_M(F(M)) ≤ F(M)` (Aut-abelian core + Fitting self-centralizing),
so `M'` is abelian and `M'' = 1`.  This is the engine of Corollary 15.6's "`M_F` not cyclic"
clause. -/
theorem fittingInAmbient_cyclic_imp_derivedDerived_eq_bot [Finite G] {M : Subgroup G}
    [Group.IsSolvable ↥M] (hcyc : IsCyclic ↥(fittingInAmbient M)) :
    derivedInG (derivedInG M) = ⊥ := by
  -- `fitting ↥M` is cyclic (transport of `hcyc` along `fittingInAmbient M ≅ fitting ↥M`)
  have hfitcyc : IsCyclic ↥(OddOrder.Isaacs.Ch01.fitting ↥M) := by
    have e : ↥(OddOrder.Isaacs.Ch01.fitting ↥M) ≃* ↥(fittingInAmbient M) :=
      Subgroup.equivMapOfInjective (OddOrder.Isaacs.Ch01.fitting ↥M) M.subtype M.subtype_injective
    exact isCyclic_of_surjective e.symm e.symm.surjective
  -- `commutator ↥M ≤ centralizer (fitting ↥M) ≤ fitting ↥M`
  have hcomm_le : commutator ↥M ≤ OddOrder.Isaacs.Ch01.fitting ↥M :=
    (commutator_le_centralizer_of_normal_isCyclic
      (inferInstance : (OddOrder.Isaacs.Ch01.fitting ↥M).Normal)).trans
      OddOrder.GroupTheory.centralizer_fitting_le_fitting
  -- push to the ambient group: `M' = ⁅M, M⁆ ≤ F(M)`
  have hderiv_le : derivedInG M ≤ fittingInAmbient M := Subgroup.map_mono hcomm_le
  -- `F(M)` cyclic ⟹ abelian ⟹ `F(M) ≤ C_G(F(M))`
  have hself : (fittingInAmbient M : Subgroup G) ≤ Subgroup.centralizer (fittingInAmbient M) := by
    have := hcyc
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have h : (⟨y, hy⟩ : ↥(fittingInAmbient M)) * ⟨x, hx⟩ = ⟨x, hx⟩ * ⟨y, hy⟩ := mul_comm' _ _
    calc y * x = ↑((⟨y, hy⟩ : ↥(fittingInAmbient M)) * ⟨x, hx⟩) := by rw [Subgroup.coe_mul]
      _ = ↑((⟨x, hx⟩ : ↥(fittingInAmbient M)) * ⟨y, hy⟩) := by rw [h]
      _ = x * y := by rw [Subgroup.coe_mul]
  -- `M'' = ⁅M', M'⁆ ≤ ⁅F(M), F(M)⁆ = 1`
  rw [show derivedInG (derivedInG M) = ⁅derivedInG M, derivedInG M⁆ from
        Subgroup.map_subtype_commutator (derivedInG M)]
  refine le_bot_iff.mp (le_trans (Subgroup.commutator_mono hderiv_le hderiv_le) ?_)
  exact le_of_eq (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hself)

/-- **§14-independent engine for BG Corollary 15.6's `K* ⊆ M''` clause.**  Given the type-`P`
complement structure `M = K M'` with `K ∩ M' = 1` (BG Theorem 14.7(h), here as the relative-
complement hypothesis `hcompl` inside `↥M`) and the coprimality of `|M'|` and `|K|`, Lemma 6.3
(`centralizer_inf_le_derivedInG_of_isComplement'`, proved) yields `C_{M'}(K) ⊆ M''`; since
`K* = C_{M_σ}(K) = M_σ ⊓ C_G(K) ⊆ C_{M'}(K)` (because `M_σ ⊆ M'`), this gives `K* ⊆ M''`.

The complement/coprimality data are the only `§14` inputs; everything else is unconditional, so
Corollary 15.6 reduces its `K* ⊆ M''` clause to a single citation once Theorem 14.7(h) (or the
`IsComplement' (derivedInG M) K` strengthening of Lemma 15.1) lands.  Mirrors the Lemma 6.3
transport in `S12_E.Msigma_E_relations`, with `M'` in place of `M_σ` and `K` in place of `E`. -/
theorem Msigma_inf_centralizer_le_derivedDerived_of_isComplement' [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M K : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hcompl : Subgroup.IsComplement' ((derivedInG M).subgroupOf M) (K.subgroupOf M))
    (hcop : Nat.Coprime (Nat.card ↥((derivedInG M).subgroupOf M))
      (Nat.card ↥(K.subgroupOf M))) :
    OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G) ≤
      derivedInG (derivedInG M) := by
  classical
  have : Group.IsSolvable ↥M := hG.isSolvable_of_mem_maximalSubgroups hM
  have hMσM : OddOrder.BG.Ch3.S10.Msigma M ≤ M := OddOrder.BG.Ch3.S10.Msigma_le M
  have hMσ_le_deriv : OddOrder.BG.Ch3.S10.Msigma M ≤ derivedInG M :=
    OddOrder.BG.Ch3.S10.Msigma_le_derived hG hM
  have hderivM : derivedInG M ≤ M := Subgroup.map_subtype_le _
  -- `H := (derivedInG M).subgroupOf M = commutator ↥M`, normal in `↥M`.
  have hid : (derivedInG M).subgroupOf M = commutator ↥M :=
    Subgroup.comap_map_eq_self_of_injective M.subtype_injective (commutator ↥M)
  have hHnorm : ((derivedInG M).subgroupOf M).Normal := by rw [hid]; infer_instance
  have hH_le : (derivedInG M).subgroupOf M ≤ commutator ↥M := le_of_eq hid
  -- Lemma 6.3 inside `↥M`:  `C_{↥M}(K') ⊓ H ≤ derivedInG H`.
  have h632 := OddOrder.BG.Ch1.S06.centralizer_inf_le_derivedInG_of_isComplement'
    (G := ↥M) hcompl hH_le hcop
  -- Transport identity:  `(derivedInG H).map M.subtype = derivedInG (derivedInG M)`.
  have hderiv_transport :
      (derivedInG ((derivedInG M).subgroupOf M)).map M.subtype =
        derivedInG (derivedInG M) := by
    rw [show derivedInG ((derivedInG M).subgroupOf M)
          = ⁅(derivedInG M).subgroupOf M, (derivedInG M).subgroupOf M⁆
          from Subgroup.map_subtype_commutator _,
      Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hderivM,
      show ⁅(derivedInG M : Subgroup G), derivedInG M⁆ = derivedInG (derivedInG M)
          from (Subgroup.map_subtype_commutator _).symm]
  -- Pointwise: every `x ∈ M_σ ⊓ C_G(K)` lands in `derivedInG (derivedInG M)`.
  intro x hx
  obtain ⟨hxMσ, hxC⟩ := hx
  have hxM : x ∈ M := hMσM hxMσ
  have hxmem : (⟨x, hxM⟩ : ↥M) ∈
      Subgroup.centralizer ((K.subgroupOf M : Subgroup ↥M) : Set ↥M)
        ⊓ (derivedInG M).subgroupOf M := by
    refine ⟨Subgroup.mem_centralizer_iff.mpr ?_, ?_⟩
    · intro k' hk'
      have hkK : ((k' : ↥M) : G) ∈ K := Subgroup.mem_subgroupOf.mp hk'
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hxC (k' : G) hkK)
    · exact Subgroup.mem_subgroupOf.mpr (hMσ_le_deriv hxMσ)
  have hmapped := Subgroup.mem_map_of_mem M.subtype (h632 hxmem)
  rwa [hderiv_transport] at hmapped

/-- The nonidentity part of the ambient Fitting subgroup of `M`. -/
def fittingSharp (M : Subgroup G) : Set G :=
  sharpSubgroup (fittingInAmbient M)

/-- The BG §15 hypothesis that `F(M)` is a TI-subgroup of `G`. -/
def FittingIsTI (M : Subgroup G) : Prop :=
  IsTISubset (fittingSharp M) (Subgroup.normalizer ((fittingInAmbient M : Subgroup G) : Set G))

/-- The subgroup generated by the centralizers in `U` of nonidentity elements of
`M_sigma`; this packages BG Lemma 15.1(d). -/
noncomputable def centralizerGeneratedBySigma (M U : Subgroup G) : Subgroup G :=
  sSup {C : Subgroup G | ∃ x ∈ sigmaSharp M,
    C = U ⊓ Subgroup.centralizer ({x} : Set G)}

end OddOrder.BG.Ch4.S15


