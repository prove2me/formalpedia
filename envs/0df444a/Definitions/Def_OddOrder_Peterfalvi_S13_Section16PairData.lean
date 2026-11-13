-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S13_Section16PairData
-- name    : OddOrder_Peterfalvi_S13_Section16PairData
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T14:11:24.620029+00:00
-- url     : https://prove2.me/theorems/cc5eb03d-2254-4dce-9df7-c3e646b337ba
-- title:
--   Section 16 maximal-pair and type $P$ pairing data structures
-- statement:
--   Defines the data structures for the maximal pair and type $P$ pairing of Section 16 (Bender–Glauberman style type classification), together with cyclic-factor helper lemmas.
--
--   Main declarations: `Section16MaximalPairCore` (BG §16 maximal-pair / type-classification output); `Section16MaximalPair` (The κ-ordered maximal pair); `Section16TypePStructure` (BG §14 type-P duality / cyclic-counting output).
--
--   The bundle also proves 5 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S13_Section16PairData.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S13_Section16PairData.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S13_CoreStructure
import Definitions.Def_OddOrder_Peterfalvi_S13_Orthogonality
import Definitions.Def_OddOrder_Peterfalvi_S06_CertainTypeCharacters
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

namespace OddOrder

open OddOrder.BG

open OddOrder.GroupTheory

open OddOrder.Isaacs

open OddOrder.RepresentationTheory

open scoped Pointwise

/-- **BG §16 maximal-pair / type-classification output** — *owned by lane-g*.

The maximal pair `S, T`, their (non-)types, the "at least one Type II" disjunction,
and the case-(b) trichotomy of (8.8).  These are the fields of `Section16Inputs`
that mention only `S, T`. Producer: `section16MaximalPair_of_isMinimalSimpleOdd` (in
`S13_TypeDetermination`, below the unconditional (10.10))
(BG §16 main results). -/
structure Section16MaximalPairCore (G : Type*) [Group G] [Finite G] where
  S : Subgroup G
  T : Subgroup G
  S_maximal : S ∈ maximalSubgroups G
  T_maximal : T ∈ maximalSubgroups G
  S_ne_T : S ≠ T
  S_nonI : IsTypeNonI S
  T_nonI : IsTypeNonI T
  one_typeII : IsTypeII S ∨ IsTypeII T
  theorem88_caseB :
    ∀ M : Subgroup G, M ∈ maximalSubgroups G →
      IsTypeI M ∨ (∃ g : G, MulAut.conj g • M = S) ∨
        (∃ g : G, MulAut.conj g • M = T)
  /-- The κ-Hall factor `K` of `S` and its dual `K* = C_{S_σ}(K)`. -/
  K : Subgroup G
  Kstar : Subgroup G
  /-- **Canonical partner witness** (BG Theorem 14.7 / `typeP_duality`): `T` is the *canonical*
  type-`P` partner of `S`, not merely some maximal in its conjugacy class.  These fields pin the
  pairing `S ∩ T = K ⊔ K*` (the `theorem88_caseB` covering alone fixes the partner only up to
  conjugacy, which would leave `Section16TypePStructure` an empty type).  Supplied by
  `exists_section16MaximalPair_data`. -/
  K_le_S : K ≤ S
  K_hall : Ch03.IsHallSubgroup (BG.Ch4.S14.kappa S) (K.subgroupOf S)
  Kstar_eq : Kstar = BG.Ch3.S10.Msigma S ⊓ Subgroup.centralizer (K : Set G)
  S_typeP : BG.Ch4.S14.IsTypeP S
  T_typeP : BG.Ch4.S14.IsTypeP T
  S_T_not_conj : ¬ BG.Ch4.S14.IsConjugateSubgroup S T
  Kstar_le_T : Kstar ≤ T
  Kstar_hall : Ch03.IsHallSubgroup (BG.Ch4.S14.kappa T) (Kstar.subgroupOf T)
  K_eq : K = BG.Ch3.S10.Msigma T ⊓ Subgroup.centralizer (Kstar : Set G)
  Z_cyclic : IsCyclic ↥(K ⊔ Kstar)
  /-- **Peterfalvi (13.2.a)**: the `S`-member of the pair is of type `P₂` (Type II).  In the
  canonical producer this is pinned via `isTypeP2_of_typeP_kappaHall_lt` (`S13_TypeDetermination`)
  on the smaller-κ
  labelling; in the `M`-seeded producer it is the clean resolution of the `typeP_duality`
  disjunction against `¬ IsTypeP2 M` (no (13.2.a) content; issue 1020 Phase 1a). -/
  S_typeP2 : BG.Ch4.S14.IsTypeP2 S

/-- **The κ-ordered maximal pair**: `Section16MaximalPairCore` together with the ordering
`|K| < |K*|`.  The ordering is genuinely Peterfalvi-(13.2.a)-deep (its available proofs route
through (10.10) ← (10.8)), so the (10.7)/(10.8) chain must consume only the order-free
`Core` (issue 1020, the (13.2.a) circle); the `q < p`-pinned §15/§16 packaging keeps the
full structure. -/
structure Section16MaximalPair (G : Type*) [Group G] [Finite G]
    extends Section16MaximalPairCore G where
  /-- **Ordering** `|K| < |K*|`: the pair is labelled so that the κ-Hall factor of `S` is the
  smaller of the two coprime factors of `W = K × K*`.  Established by relabelling `S ↔ T` in
  `exists_section16MaximalPair_data` (`card_kappaHall_ne_card_Kstar` makes the two orders distinct,
  so one of the two labellings has `|K| < |K*|`).  This pins the otherwise-ambiguous `q < p`. -/
  K_lt_Kstar : Nat.card ↥toSection16MaximalPairCore.K < Nat.card ↥toSection16MaximalPairCore.Kstar

/-- **BG §14 type-P duality / cyclic-counting output** — *owned by lane-f*.

The cyclic structure `W = W₁W₂`, the complements `U, V`, the primes `p, q`, and the
counting parameters `u, v, c, d` with their identities.  Sibling references to the
maximal pair are taken from `mp`.  Producer:
`section16TypePStructure_of_isMinimalSimpleOdd` (BG §14 `typeP_duality`). -/
structure Section16TypePStructure {G : Type*} [Group G] [Finite G]
    (mp : Section16MaximalPair G) where
  W1 : Subgroup G
  W2 : Subgroup G
  W : Subgroup G
  U : Subgroup G
  V : Subgroup G
  W_eq_inter : W = mp.S ⊓ mp.T
  W_eq_join : W = W1 ⊔ W2
  W1_inf_W2_eq_bot : W1 ⊓ W2 = ⊥
  W1_commutes_W2 : ∀ x ∈ W1, ∀ y ∈ W2, Commute x y
  W_cyclic : IsCyclic ↥W
  S_deriv_eq_PU : derivedInG mp.S = maxNilpotentNormalHall mp.S ⊔ U
  T_deriv_eq_QV : derivedInG mp.T = maxNilpotentNormalHall mp.T ⊔ V
  /-- `Q ⊓ V = ⊥`: the invariant complement `V` genuinely complements `Q = T_F` in `T'` (from
  `exists_kappaHall_invariant_complement_to_MF`, ungated by (14.9)); threaded into `S15.Hypothesis`
  as `Q_inf_V_eq_bot`. -/
  V_inf_Q_eq_bot : maxNilpotentNormalHall mp.T ⊓ V = ⊥
  /-- `T = T' ⋊ W₂`: `W₂` complements `T'` in `T` (from `typeP_derivedInG_isComplement_kappaHall`,
  ungated by (14.9)); threaded into `S15.Hypothesis` as `W2_isComplement_T_deriv`. -/
  W2_isComplement_T_deriv :
    Subgroup.IsComplement' ((derivedInG mp.T).subgroupOf mp.T) (W2.subgroupOf mp.T)
  W1_normalizes_U : W1 ≤ Subgroup.normalizer (U : Set G)
  W2_normalizes_V : W2 ≤ Subgroup.normalizer (V : Set G)
  q : ℕ
  p : ℕ
  q_prime : q.Prime
  p_prime : p.Prime
  q_eq_card_W1 : q = Nat.card ↥W1
  p_eq_card_W2 : p = Nat.card ↥W2
  u : ℕ
  v : ℕ
  c : ℕ
  d : ℕ
  c_eq_card_C : c = Nat.card ↥(U ⊓ Subgroup.centralizer (maxNilpotentNormalHall mp.S : Set G))
  d_eq_card_D : d = Nat.card ↥(V ⊓ Subgroup.centralizer (maxNilpotentNormalHall mp.T : Set G))
  card_U_eq_uc : Nat.card ↥U = u * c
  card_V_eq_vd : Nat.card ↥V = v * d
  q_lt_p : q < p
  /-- **Peterfalvi (13.1.b) carrier (S-side)**: the type-`P` structure data of the smaller-κ,
  type-`P₂` member `S` (`S = (P ⋊ U) ⋊ W₁`, `P = S_F`), with its complement `U` and cyclic factor
  `W₁` reconciled (`Sdata_U_eq`/`Sdata_W1_eq`) to the structure's `U`/`W1`.  Built from
  `mp.S_typeP2`
  (Pf (13.2.a)) via `typePData_of_kappaHall_hallComplement`; it supplies the U-side facts
  (`U` complements `M_F = P`, `W₁ ≤ N_G(U)`, `U` nilpotent) that Peterfalvi §15 reads off `S`
  (`basic_structure` U-side, `exists_typeI_maximal_overNormalizer_U`).  Only `S` is determinate —
  `T` (the larger-κ member) need not be type-`P₂`, so no symmetric `Tdata`. -/
  Sdata : TypePData mp.S
  Sdata_U_eq : Sdata.U = U
  Sdata_W1_eq : Sdata.W1 = W1
  /-- **Peterfalvi (13.2.a) U-side**: `U` abelian (BG Lemma 15.1(b), `U` the `(κ∪σ)'`-Hall). -/
  S_U_commutative : IsMulCommutative ↥U
  /-- **W₂-reconciliation**: intrinsic `Sdata.W2 = C_{S'}(W₁#)` equals abstract `W₂` (= `K*`). -/
  Sdata_W2_eq : Sdata.W2 = W2

/-- The cyclic factors `mp.K`, `mp.Kstar` are cyclic (subgroups of the cyclic `Z = K ⊔ K*`). -/
theorem Section16MaximalPairCore.isCyclic_K {G : Type*} [Group G] [Finite G]
    (mp : Section16MaximalPairCore G) : IsCyclic ↥mp.K :=
  haveI : IsCyclic ↥(mp.K ⊔ mp.Kstar) := mp.Z_cyclic
  isCyclic_of_injective (Subgroup.inclusion (le_sup_left : mp.K ≤ mp.K ⊔ mp.Kstar))
    (Subgroup.inclusion_injective _)

theorem Section16MaximalPair.isCyclic_K {G : Type*} [Group G] [Finite G]
    (mp : Section16MaximalPair G) : IsCyclic ↥mp.K :=
  mp.toSection16MaximalPairCore.isCyclic_K

/-- The cyclic factors `mp.K`, `mp.Kstar` are cyclic (subgroups of the cyclic `Z = K ⊔ K*`). -/
theorem Section16MaximalPairCore.isCyclic_Kstar {G : Type*} [Group G] [Finite G]
    (mp : Section16MaximalPairCore G) : IsCyclic ↥mp.Kstar :=
  haveI : IsCyclic ↥(mp.K ⊔ mp.Kstar) := mp.Z_cyclic
  isCyclic_of_injective (Subgroup.inclusion (le_sup_right : mp.Kstar ≤ mp.K ⊔ mp.Kstar))
    (Subgroup.inclusion_injective _)

theorem Section16MaximalPair.isCyclic_Kstar {G : Type*} [Group G] [Finite G]
    (mp : Section16MaximalPair G) : IsCyclic ↥mp.Kstar :=
  mp.toSection16MaximalPairCore.isCyclic_Kstar

/-- Helper: in a finite group, two complementary subgroups `A`, `B` of a cyclic subgroup `W`
(`A ⊔ B = W`, `A ⊓ B = ⊥`) have `|A|·|B| = |W|`. -/
theorem card_mul_eq_of_disjoint_sup_le_isCyclic {G : Type*} [Group G] [Finite G]
    {W A B : Subgroup G} (hWcyc : IsCyclic ↥W) (hAW : A ≤ W) (hBW : B ≤ W)
    (hsup : A ⊔ B = W) (hinf : A ⊓ B = ⊥) :
    Nat.card ↥A * Nat.card ↥B = Nat.card ↥W := by
  have := hWcyc
  let : CommGroup ↥W := IsCyclic.commGroup
  have : (A.subgroupOf W).Normal := inferInstance
  have hinf' : (A.subgroupOf W) ⊓ (B.subgroupOf W) = ⊥ := by
    rw [eq_bot_iff]; intro x hx
    obtain ⟨hxA, hxB⟩ := Subgroup.mem_inf.mp hx
    rw [Subgroup.mem_subgroupOf] at hxA hxB
    have hxAB : (x : G) ∈ A ⊓ B := ⟨hxA, hxB⟩
    rw [hinf, Subgroup.mem_bot] at hxAB
    rw [Subgroup.mem_bot]; exact Subtype.ext hxAB
  have hsup' : (A.subgroupOf W) ⊔ (B.subgroupOf W) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hAW hBW, hsup, Subgroup.subgroupOf_self]
  have h := Subgroup.card_mul_card_of_complement_normal hinf' hsup'
  rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAW).toEquiv,
       Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBW).toEquiv] at h

end OddOrder


