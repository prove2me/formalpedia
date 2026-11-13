-- Prove2me | Definitions.Def_OddOrder_FeitThompsonSection16Core
-- name    : OddOrder_FeitThompsonSection16Core
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T17:39:16.090907+00:00
-- url     : https://prove2.me/theorems/e4223a0d-8bd0-4ecb-94fe-0697b69a70b2
-- title:
--   Feit–Thompson Section 16: carriers and type $P$ setup
-- statement:
--   Formalizes carriers for Section 16 of the Feit–Thompson proof and the type $P$ setup from $\kappa$-Hall pairing data.
--
--   Main declarations: `typePData_of_kappaHall_hallComplement` (`TypePData M` from a `K`-invariant `(κ∪σ)′`-Hall complement `U`); `certainTypeHypothesis_of_typeP_kappaHall` (Certain-type §6 hypothesis from κ-Hall pairing data); `Section16MaximalPair.certainTypeS` (The S-side §6 certain-type Hypothesis); `Section16MaximalPair.certainTypeT` (The T-side §6 certain-type Hypothesis).
--
--   The bundle also proves 5 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/FeitThompsonSection16Core.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/FeitThompsonSection16Core.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_BG_AppC_LemmaC3_Step4Capstone
import Definitions.Def_OddOrder_BG_AppC_FrobeniusClassSum
import Definitions.Def_OddOrder_Peterfalvi_S16_NonExistenceG_SubgroupL
import Definitions.Def_OddOrder_Peterfalvi_S16_NonExistenceG_TSideTypeP
import Definitions.Def_OddOrder_Peterfalvi_S15_SAndT_Setup_HypothesisBasics
import Definitions.Def_OddOrder_Peterfalvi_S15_SAndT_Setup_HypothesisSwap
import Definitions.Def_OddOrder_Peterfalvi_S15_SAndT_Setup_DegreesFirstSplit
import Definitions.Def_OddOrder_Peterfalvi_S15_SAndT_Setup_PairStructure
import Definitions.Def_OddOrder_Peterfalvi_S15_SAndT_Setup_CountingLayer
import Definitions.Def_OddOrder_Peterfalvi_S15_SAndT_Setup_Canonicalization
import Definitions.Def_OddOrder_Peterfalvi_S13_ElementaryAbelianKernel
import Definitions.Def_OddOrder_BG_Ch2_Uniqueness_S07_Theorem74
import Definitions.Def_OddOrder_Peterfalvi_S15_SAndT_Setup_TSideDegrees
import Definitions.Def_OddOrder_Peterfalvi_S12_MaximalIII_IV_V_Core_Hypothesis
import Definitions.Def_OddOrder_Peterfalvi_S12_MaximalIII_IV_V_Core_CharacterParameters
import Definitions.Def_OddOrder_Peterfalvi_S12_MaximalIII_IV_V_Core_DadeCalculations
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_PrimeTIResidue
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_InducedIrreducible
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_ColumnOrthogonality
import Definitions.Def_OddOrder_Peterfalvi_S13_Orthogonality
import Definitions.Def_OddOrder_Peterfalvi_S16_GridExpansion
import Definitions.Def_OddOrder_Peterfalvi_S15_CharacterDegreeEnginesSSide
import Definitions.Def_OddOrder_Peterfalvi_S15_CharacterDegreeEngines
import Definitions.Def_OddOrder_Peterfalvi_S15_CharacterDegreeSupply
import Definitions.Def_OddOrder_Peterfalvi_S16_NonExistenceG_CoherentProjectionRigidity
import Definitions.Def_OddOrder_Peterfalvi_S16_CoreLemmas
import Definitions.Def_OddOrder_Peterfalvi_S16_NonExistenceG_SubgroupM
import Definitions.Def_OddOrder_Peterfalvi_S16_NonExistenceG_BetaVanishing
import Definitions.Def_OddOrder_BG_Ch4_FamilyOfMaximal_S14_TypePCounting_Basics
import Definitions.Def_OddOrder_BG_Ch4_FamilyOfMaximal_S14_TypePCounting_LocalStructure
import Definitions.Def_OddOrder_BG_Ch4_FamilyOfMaximal_S14_TypePCounting_SigmaLengthOne
import Definitions.Def_OddOrder_BG_Ch4_FamilyOfMaximal_S14_TypePCounting_TypePDuality
import Definitions.Def_OddOrder_BG_Ch4_FamilyOfMaximal_S14_TypePCounting_GlobalCounting
import Definitions.Def_OddOrder_BG_Ch4_FamilyOfMaximal_S15_MF_SetupLemma151
import Definitions.Def_OddOrder_BG_Ch4_FamilyOfMaximal_S15_MF_Theorem152Helpers
import Definitions.Def_OddOrder_BG_Ch4_FamilyOfMaximal_S15_MF_Corollary155
import Definitions.Def_OddOrder_BG_Ch4_FamilyOfMaximal_S15_MF_TIFailure
import Definitions.Def_OddOrder_BG_Ch4_FamilyOfMaximal_S15_MF_WitnessPGroup
import Definitions.Def_OddOrder_GroupTheory_AInvariantComplement
import Definitions.Def_OddOrder_Peterfalvi_S06_CertainTypeCharacters
import Definitions.Def_OddOrder_Peterfalvi_S13_CoreStructure
import Definitions.Def_OddOrder_Peterfalvi_S13_Section16PairData

namespace OddOrder

open OddOrder.BG

open OddOrder.GroupTheory

open OddOrder.Isaacs

open OddOrder.RepresentationTheory

open scoped Pointwise

universe u

section

open scoped OddOrder.Peterfalvi.S15.FiniteInduce

open scoped IsMulCommutative in
/-- **`TypePData M` from a `K`-invariant `(κ∪σ)′`-Hall complement `U`** (`sorry`-free engine;
POLE-1 carrier, issue 4008).

Given a type-`P` maximal subgroup `M`, its cyclic κ-Hall `K`, and a `(κ∪σ)′`-Hall complement `U`
normalised by `K` (`hKnorm`), this assembles the Peterfalvi type-`P` datum `TypePData M` with the
chosen factors `data.W₁ = K`, `data.U = U` (definitionally: `…_W1`/`…_U`).  This is the
complement-specified constructor that `typePData_of_isTypeNonI` cannot provide (it builds its own
`U`), so it lets the §16 `Section16TypePStructure` carry a `TypePData` whose `W₁`/`U` agree with the
maximal-pair factors, unblocking Peterfalvi `basic_structure` (13.2).

All structural fields are discharged through BG §14/15/16 machinery (sorry-free, cited):
`typeP2_mf_internal_fitting_decomposition` (the deep `M′`-complement/Fitting fields) and
`typeP_hall_derived_eq_and_abelian` (`U` abelian, hence nilpotent), fed to
`typePData_of_isTypeP_of_inputs`.  The two structural hypotheses, `K ≤ N_G(U)` and that `U` is the
`(κ∪σ)′`-Hall, are the residual obligations discharged for the canonical pair by
`exists_kappaHall_invariant_complement_to_MF` (`K ≤ N_G(U)`) and
`Peterfalvi.S10Interface.isHall_kappaSigmaCompl_of_isTypeP2_complement` (the `(κ∪σ)′`-Hall
property),
bundled in `exists_typePData_W1_eq_of_isTypeP2`. -/
noncomputable def typePData_of_kappaHall_hallComplement {G : Type*} [Group G] [Finite G]
    (hG : IsMinimalSimpleOdd G) {M K U : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hP2 : BG.Ch4.S14.IsTypeP2 M) (hKM : K ≤ M) (hKne : K ≠ ⊥)
    (hK : Ch03.IsHallSubgroup (BG.Ch4.S14.kappa M) (K.subgroupOf M)) (hUM : U ≤ M)
    (hUhall : Ch03.IsHallSubgroup ((BG.Ch4.S14.kappa M ∪ BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    (hKnorm : K ≤ Subgroup.normalizer (U : Set G)) :
    TypePData M :=
  -- Term-mode (no `obtain`/`have` casesOn) so the `.W₁ = K`/`.U = U` projections reduce
  -- definitionally past lane-f's tactic-built `typePData_of_isTypeP_of_inputs`
  -- (memory: coupled engine fields + beta).
  let hdec := BG.Ch4.S15.typeP2_mf_internal_fitting_decomposition hG hM hP2 hKM hUM hKne hK hUhall
  let hM'ab := BG.Ch4.S15.typeP_hall_derived_eq_and_abelian hG hM hKM hUM hKne hK hUhall
  BG.Ch4.S16.typePData_of_isTypeP_of_inputs hG hM hP2.1 hKM hKne hK
    (le_sup_left.trans_eq hM'ab.1.symm) hKnorm
    (haveI := hM'ab.2; (inferInstance : Group.IsNilpotent ↥U))
    hdec.1 hdec.2.1 hdec.2.2

/-- **Certain-type §6 hypothesis from κ-Hall pairing data** — *lane-b* (cd producer building block).

For a type-`P` maximal `M` with cyclic κ-Hall `K` and the dual factor `K* = M_σ ⊓ C(K)` (cyclic,
nontrivial), builds the Peterfalvi §6 certain-type Hypothesis (4.2) with `W₁ = K`, `W₂ = K*`,
`K(§6) = M' = [M,M]`, all transported into `↥M`.  Structural fields are discharged from the
BG §14/§16 type-`P` theory: `M = M' ⋊ K` (`typeP_derivedInG_isComplement_kappaHall`, BG 14.7(h)),
the (4.2.b) centralizer law `C_{M'}(k) = K*` for `k ∈ K#`
(`typeP_derivedInG_inf_centralizer_kappaElement_eq`, BG Thm C / Pf (8.4)), Hall coprimality
(`IsHallSubgroup.coprime_index` with `[M:M'] = |K|`), and `K* ≤ M_σ ≤ M'`.

Unlike `typePData_toS06Hypothesis` (which uses a `TypePData`'s *canonical* `W₁`), this builds the
hypothesis with `W₁ = K` the *chosen pairing factor*, so the resulting `ω`/`μ`-grids are indexed by
`tp.W₁ = mp.K`, `tp.W₂ = mp.Kstar` — exactly the indexing `Section16CharacterData` needs (no
cross-construction `W`-identification).  Applied to `(mp.S; mp.K, mp.Kstar)` and the swapped
`(mp.T; mp.Kstar, mp.K)`, it gives the two members' certain-type machinery for the cd producer. -/
noncomputable def certainTypeHypothesis_of_typeP_kappaHall {G : Type*} [Group G] [Finite G]
    (hG : IsMinimalSimpleOdd G) {M K Kstar : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hP : BG.Ch4.S14.IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (BG.Ch4.S14.kappa M) (K.subgroupOf M))
    (hKstar : Kstar = BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hKcyc : IsCyclic ↥K) (hKstarcyc : IsCyclic ↥Kstar) (hKstarne : Kstar ≠ ⊥) :
    OddOrder.Peterfalvi.S06.Hypothesis ↥M := by
  haveI := hKcyc
  haveI := hKstarcyc
  have hM'le : derivedInG M ≤ M := Subgroup.map_subtype_le _
  have hKstarM' : Kstar ≤ derivedInG M := by
    rw [hKstar]; exact inf_le_left.trans (BG.Ch3.S10.Msigma_le_derived hG hM)
  have hKstarM : Kstar ≤ M := hKstarM'.trans hM'le
  have hcompl := BG.Ch4.S14.typeP_derivedInG_isComplement_kappaHall hG hM hP hKM hK
  have hidx : (K.subgroupOf M).index = Nat.card ↥(derivedInG M) := by
    rw [hcompl.index_eq_card]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hM'le).toEquiv
  have hCop : Nat.Coprime (Nat.card ↥K) (Nat.card ↥(derivedInG M)) := by
    have hco := hK.coprime_index
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKM).toEquiv, hidx] at hco
  exact
    { K := (derivedInG M).subgroupOf M
      W1 := K.subgroupOf M
      W2 := Kstar.subgroupOf M
      K_normal := by
        rw [show (derivedInG M).subgroupOf M = commutator ↥M by
          rw [derivedInG, Subgroup.subgroupOf,
            Subgroup.comap_map_eq_self_of_injective M.subtype_injective]]
        infer_instance
      isComplement := hcompl
      W1_nontrivial := by
        rw [ne_eq, Subgroup.subgroupOf_eq_bot]
        intro hdisj
        exact BG.Ch4.S14.card_kappaHall_ne_one hP hKM hK
          (Subgroup.card_eq_one.mpr (disjoint_self.mp (hdisj.mono_right hKM)))
      W1_cyclic := isCyclic_of_injective (Subgroup.subgroupOfEquivOfLe hKM).toMonoidHom
        (Subgroup.subgroupOfEquivOfLe hKM).injective
      card_coprime := by
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hM'le).toEquiv,
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKM).toEquiv]
        exact hCop.symm
      W2_nontrivial := by
        rw [ne_eq, Subgroup.subgroupOf_eq_bot]
        exact fun hdisj => hKstarne (disjoint_self.mp (hdisj.mono_right hKstarM))
      W2_cyclic := isCyclic_of_injective (Subgroup.subgroupOfEquivOfLe hKstarM).toMonoidHom
        (Subgroup.subgroupOfEquivOfLe hKstarM).injective
      W2_le_K := Subgroup.comap_mono hKstarM'
      centralizer_W2 := by
        intro x hx1 hx2
        have hxW1 : (x : G) ∈ K := Subgroup.mem_subgroupOf.mp hx1
        have hxne : (x : G) ≠ 1 := fun h => hx2 (Subtype.ext h)
        have hamb : Subgroup.centralizer ({(x : G)} : Set G) ⊓ derivedInG M = Kstar := by
          rw [inf_comm]
          exact BG.Ch4.S16.typeP_derivedInG_inf_centralizer_kappaElement_eq hG hM hP hKM hK hKstar
            (x : G) hxW1 hxne
        rw [OddOrder.BG.Ch1.S03h.centralizer_subgroupOf, Set.image_singleton]
        simp only [Subgroup.subgroupOf, ← Subgroup.comap_inf, Subgroup.coe_subtype, hamb]
      W_odd := by
        rw [← Subgroup.subgroupOf_sup hKM hKstarM,
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe (sup_le hKM hKstarM)).toEquiv]
        exact hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card (K ⊔ Kstar)) }

/-- **The S-side §6 certain-type Hypothesis** (cd producer building block): `mp.S` with `W₁ = mp.K`,
`W₂ = mp.Kstar`.  Wires `certainTypeHypothesis_of_typeP_kappaHall` to `mp`'s κ-Hall data
(`mp.K_hall`, `mp.Kstar_eq`); the dual `mp.Kstar ≠ 1` is the κ-Hall nontriviality of `mp.T`. -/
noncomputable def Section16MaximalPair.certainTypeS {G : Type*} [Group G] [Finite G]
    (hG : IsMinimalSimpleOdd G) (mp : Section16MaximalPair G) :
    OddOrder.Peterfalvi.S06.Hypothesis ↥mp.S :=
  haveI := mp.isCyclic_K
  haveI := mp.isCyclic_Kstar
  certainTypeHypothesis_of_typeP_kappaHall hG mp.S_maximal mp.S_typeP mp.K_le_S mp.K_hall
    mp.Kstar_eq inferInstance inferInstance (fun hbot =>
      BG.Ch4.S14.card_kappaHall_ne_one mp.T_typeP mp.Kstar_le_T mp.Kstar_hall
        (Subgroup.card_eq_one.mpr hbot))

/-- **The T-side §6 certain-type Hypothesis** (cd producer building block): `mp.T` with
`W₁ = mp.Kstar`,
`W₂ = mp.K` (the roles of the two factors swap for the partner).  The pairing relation `mp.K =
M_σ(T) ⊓ C(mp.Kstar)` is `mp.K_eq`. -/
noncomputable def Section16MaximalPair.certainTypeT {G : Type*} [Group G] [Finite G]
    (hG : IsMinimalSimpleOdd G) (mp : Section16MaximalPair G) :
    OddOrder.Peterfalvi.S06.Hypothesis ↥mp.T :=
  haveI := mp.isCyclic_K
  haveI := mp.isCyclic_Kstar
  certainTypeHypothesis_of_typeP_kappaHall hG mp.T_maximal mp.T_typeP mp.Kstar_le_T mp.Kstar_hall
    mp.K_eq inferInstance inferInstance (fun hbot =>
      BG.Ch4.S14.card_kappaHall_ne_one mp.S_typeP mp.K_le_S mp.K_hall
        (Subgroup.card_eq_one.mpr hbot))

/-- **W-structure of the canonical maximal pair** (BG Theorem 14.7, via `typeP_pair_W_structure`):
`S ∩ T = K ⊔ K*` is cyclic, `K ⊓ K* = ⊥`, and `K`, `K*` commute.  A Hall `(κ ∪ σ)'`-subgroup of
`S` (needed only to invoke the lemma) comes from Hall's theorem on the solvable `S`. -/
theorem Section16MaximalPair.W_structure {G : Type*} [Group G] [Finite G]
    (hG : IsMinimalSimpleOdd G) (mp : Section16MaximalPair G) :
    mp.S ⊓ mp.T = mp.K ⊔ mp.Kstar ∧ IsCyclic ↥(mp.S ⊓ mp.T) ∧
      mp.K ⊓ mp.Kstar = ⊥ ∧ (∀ x ∈ mp.K, ∀ y ∈ mp.Kstar, Commute x y) := by
  have : Group.IsSolvable ↥mp.S := hG.isSolvable_of_mem_maximalSubgroups mp.S_maximal
  have hUex : ∃ U₀ : Subgroup G,
      Ch03.IsHallSubgroup ((BG.Ch4.S14.kappa mp.S ∪ BG.Ch3.S10.sigma mp.S)ᶜ)
        (U₀.subgroupOf mp.S) := by
    obtain ⟨U', hU'⟩ := Ch03.hall_E_exists (G := ↥mp.S)
      ((BG.Ch4.S14.kappa mp.S ∪ BG.Ch3.S10.sigma mp.S)ᶜ)
    exact ⟨U'.map mp.S.subtype, by
      rw [show (U'.map mp.S.subtype).subgroupOf mp.S = U' from
        Subgroup.comap_map_eq_self_of_injective mp.S.subtype_injective U']
      exact hU'⟩
  exact BG.Ch4.S16.typeP_pair_W_structure hG mp.S_maximal mp.S_typeP mp.K_le_S mp.K_hall
    mp.Kstar_eq hUex.choose_spec mp.T_maximal mp.T_typeP mp.S_T_not_conj mp.Kstar_le_T
    mp.Kstar_hall mp.Z_cyclic mp.K_eq

/-- **The type-`P` pairing factors are the maximal-pair κ-Hall factors** (`W₁ = mp.K`,
`W₂ = mp.Kstar`) — the cd-grid indexing alignment (HUB 1011, resolved lane-b-internally; no
producer reduction needed).  Both `W₁`/`K` are the unique order-`q` subgroup, and `W₂`/`K*` the
unique order-`p` subgroup, of the cyclic `W = K ⊔ K*` (`eq_of_card_eq_prime_of_isCyclic`); the
orderings `q < p` (`q_lt_p`) and `|K| < |K*|` (`K_lt_Kstar`) match the two labellings. -/
theorem Section16TypePStructure.W1_eq_K_and_W2_eq_Kstar {G : Type*} [Group G] [Finite G]
    (hG : IsMinimalSimpleOdd G) {mp : Section16MaximalPair G}
    (tp : Section16TypePStructure mp) :
    tp.W1 = mp.K ∧ tp.W2 = mp.Kstar := by
  obtain ⟨hWjoin, _, hKbot, _⟩ := mp.W_structure hG
  have hWeq : tp.W = mp.K ⊔ mp.Kstar := tp.W_eq_inter.trans hWjoin
  have : IsCyclic ↥tp.W := tp.W_cyclic
  have hKle : mp.K ≤ tp.W := hWeq ▸ le_sup_left
  have hKstarle : mp.Kstar ≤ tp.W := hWeq ▸ le_sup_right
  have hW1le : tp.W1 ≤ tp.W := tp.W_eq_join ▸ le_sup_left
  have hW2le : tp.W2 ≤ tp.W := tp.W_eq_join ▸ le_sup_right
  have hcardW : tp.q * tp.p = Nat.card ↥tp.W := by
    rw [tp.q_eq_card_W1, tp.p_eq_card_W2]
    exact card_mul_eq_of_disjoint_sup_le_isCyclic tp.W_cyclic hW1le hW2le tp.W_eq_join.symm
      tp.W1_inf_W2_eq_bot
  have hcardK : Nat.card ↥mp.K * Nat.card ↥mp.Kstar = Nat.card ↥tp.W :=
    card_mul_eq_of_disjoint_sup_le_isCyclic tp.W_cyclic hKle hKstarle hWeq.symm hKbot
  have hprod : Nat.card ↥mp.K * Nat.card ↥mp.Kstar = tp.q * tp.p := by rw [hcardK, ← hcardW]
  have hKpos : 1 < Nat.card ↥mp.K := by
    have hne := BG.Ch4.S14.card_kappaHall_ne_one mp.S_typeP mp.K_le_S mp.K_hall
    have h0 := Nat.card_pos (α := ↥mp.K)
    omega
  -- arithmetic: `|K|·|K*| = q·p`, `|K| < |K*|`, `q < p` prime, `|K| > 1` give `|K| = q`, `|K*| = p`
  have hcardKeq : Nat.card ↥mp.K = tp.q := by
    have hlt : Nat.card ↥mp.K < Nat.card ↥mp.Kstar := mp.K_lt_Kstar
    have hpdvd : tp.p ∣ Nat.card ↥mp.K * Nat.card ↥mp.Kstar := ⟨tp.q, by rw [hprod]; ring⟩
    rcases (tp.p_prime.dvd_mul).mp hpdvd with hpa | hpb
    · exfalso
      have hple : tp.p ≤ Nat.card ↥mp.K := Nat.le_of_dvd (by omega) hpa
      nlinarith [hprod, hlt, hple, tp.q_prime.two_le, tp.q_lt_p]
    · obtain ⟨b'', hb''⟩ := hpb
      have hKb : Nat.card ↥mp.K * b'' = tp.q := by
        have h2 : (Nat.card ↥mp.K * b'') * tp.p = tp.q * tp.p := by
          rw [mul_assoc, mul_comm b'' tp.p, ← hb'', hprod]
        exact Nat.eq_of_mul_eq_mul_right tp.p_prime.pos h2
      rcases (tp.q_prime.eq_one_or_self_of_dvd _ ⟨b'', hKb.symm⟩) with h1 | hq
      · omega
      · exact hq
  have hcardKstareq : Nat.card ↥mp.Kstar = tp.p := by
    have h2 : tp.q * Nat.card ↥mp.Kstar = tp.q * tp.p :=
      calc tp.q * Nat.card ↥mp.Kstar = Nat.card ↥mp.K * Nat.card ↥mp.Kstar := by rw [hcardKeq]
        _ = tp.q * tp.p := hprod
    exact Nat.eq_of_mul_eq_mul_left tp.q_prime.pos h2
  refine ⟨?_, ?_⟩
  · have hW1card : Nat.card ↥(tp.W1.subgroupOf tp.W) = tp.q := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW1le).toEquiv, ← tp.q_eq_card_W1]
    have hKcard : Nat.card ↥(mp.K.subgroupOf tp.W) = tp.q := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKle).toEquiv, hcardKeq]
    have hinf := Subgroup.subgroupOf_inj.1
      (Ch06.eq_of_card_eq_prime_of_isCyclic tp.q_prime hW1card hKcard)
    rwa [inf_of_le_left hW1le, inf_of_le_left hKle] at hinf
  · have hW2card : Nat.card ↥(tp.W2.subgroupOf tp.W) = tp.p := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW2le).toEquiv, ← tp.p_eq_card_W2]
    have hKstarcard : Nat.card ↥(mp.Kstar.subgroupOf tp.W) = tp.p := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKstarle).toEquiv, hcardKstareq]
    have hinf := Subgroup.subgroupOf_inj.1
      (Ch06.eq_of_card_eq_prime_of_isCyclic tp.p_prime hW2card hKstarcard)
    rwa [inf_of_le_left hW2le, inf_of_le_left hKstarle] at hinf

/-- `W₁ = mp.K` (cd-grid `W₁`-index alignment; HUB 1011). -/
theorem Section16TypePStructure.W1_eq_K {G : Type*} [Group G] [Finite G]
    (hG : IsMinimalSimpleOdd G) {mp : Section16MaximalPair G}
    (tp : Section16TypePStructure mp) : tp.W1 = mp.K :=
  (tp.W1_eq_K_and_W2_eq_Kstar hG).1

/-- `W₂ = mp.Kstar` (cd-grid `W₂`-index alignment; HUB 1011). -/
theorem Section16TypePStructure.W2_eq_Kstar {G : Type*} [Group G] [Finite G]
    (hG : IsMinimalSimpleOdd G) {mp : Section16MaximalPair G}
    (tp : Section16TypePStructure mp) : tp.W2 = mp.Kstar :=
  (tp.W1_eq_K_and_W2_eq_Kstar hG).2

/-- `W = mp.K ⊔ mp.Kstar` — the cd-grid `ω`-codomain identification. -/
theorem Section16TypePStructure.W_eq_kappa_join {G : Type*} [Group G] [Finite G]
    (hG : IsMinimalSimpleOdd G) {mp : Section16MaximalPair G}
    (tp : Section16TypePStructure mp) : tp.W = mp.K ⊔ mp.Kstar :=
  tp.W_eq_inter.trans (mp.W_structure hG).1

end

end OddOrder


