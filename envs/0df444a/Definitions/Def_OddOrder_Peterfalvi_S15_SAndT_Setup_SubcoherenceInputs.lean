-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S15_SAndT_Setup_SubcoherenceInputs
-- name    : OddOrder_Peterfalvi_S15_SAndT_Setup_SubcoherenceInputs
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T15:33:01.698308+00:00
-- url     : https://prove2.me/theorems/d34ad1c3-d3b9-4607-bfb8-92d5fd23d599
-- title:
--   Peterfalvi §13: subcoherence inputs for the $(S,T)$ setup
-- statement:
--   Formalizes subcoherence inputs for the hypothesis of Peterfalvi §13 on the pair $(S,T)$, along with general finite-set and cardinality helper definitions.
--
--   Main declarations: `finNeg` (Negation `i ↦ -i ≡ (n − i) (mod n)` on `Fin n`, for `0 < n`); `Hypothesis` (Peterfalvi (13.1)); `H` (Peterfalvi's `H = P C` in (13.5)--(13.10)); `K` (Peterfalvi's `K = Q D`, used symmetrically for `T`).
--
--   The bundle also proves 12 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S15_SAndT_Setup/SubcoherenceInputs.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S15_SAndT_Setup/SubcoherenceInputs.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S14_MaximalI_Hypothesis
import Definitions.Def_OddOrder_Peterfalvi_S14_MaximalI_RhoConstancy
import Definitions.Def_OddOrder_Peterfalvi_S14_MaximalI_PairCoherence
import Definitions.Def_OddOrder_Peterfalvi_S14_MaximalI_FrobeniusStructure
import Definitions.Def_OddOrder_Peterfalvi_S14_MaximalI_MinimalCounterexample
import Definitions.Def_OddOrder_Peterfalvi_S14_MaximalI_DadeContradiction
import Definitions.Def_OddOrder_Peterfalvi_S14_MaximalI_RhoMEvaluation
import Definitions.Def_OddOrder_Peterfalvi_S14_MaximalI_NormPackage
import Definitions.Def_OddOrder_Peterfalvi_S14_MaximalI_TypeICovering
import Definitions.Def_OddOrder_Peterfalvi_S07_Subcoherent
import Definitions.Def_OddOrder_Peterfalvi_S10_CoherenceWiring
import Definitions.Def_OddOrder_Peterfalvi_S09_CertificateDischarge
import Definitions.Def_OddOrder_Isaacs_Ch06_FrobeniusActions_OddComplement
import Definitions.Def_OddOrder_GroupTheory_MaximalSubgroupTypeConj
import Definitions.Def_OddOrder_GroupTheory_WielandtFixedPoint
import Definitions.Def_OddOrder_Algebra_GaloisRationalInteger
import Definitions.Def_OddOrder_GroupTheory_TISubset
import Definitions.Def_OddOrder_GroupTheory_ConjClassSet
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_InducedCharacter
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Index
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots

namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

/-- Negation `i ↦ -i ≡ (n − i) (mod n)` on `Fin n`, for `0 < n`.  This is the index map
realizing the conjugation pairing `(i,j) ↦ (−i,−j)` of the Dade `η`-grid in Peterfalvi
(3.9.a)/(14.11.3).  Defined identically to the (downstream) `S16.finNeg`, so the two are
definitionally equal — the `(3.9.a)` field `eta_pair_of_coprime` below (stated with this
`finNeg`) is thus citeable to fill `S16.EtaGenericData.eta_pair` (stated with `S16.finNeg`). -/
def finNeg {n : ℕ} (hn : 0 < n) (i : Fin n) : Fin n :=
  ⟨(n - i.val) % n, Nat.mod_lt _ hn⟩

namespace FiniteInduce

noncomputable scoped instance finiteSubFintype [Finite G] (H : Subgroup G) :
    Fintype ↥H := Fintype.ofFinite _

noncomputable scoped instance natCardInvC [Finite G] (H : Subgroup G) :
    Invertible (Nat.card H : ℂ) :=
  invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')

noncomputable scoped instance ambientFintype [Finite G] : Fintype G :=
  Fintype.ofFinite _

noncomputable scoped instance ambientNatCardInvC [Finite G] :
    Invertible (Nat.card G : ℂ) :=
  invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')

end FiniteInduce

open scoped FiniteInduce in
/-- **Peterfalvi (13.1)**: the main setup for the two maximal subgroups `S` and
`T` in case (b) of Theorem (8.8).

`G` is finite (carried as the instance field `finiteG`, so consumers need not
re-assume `[Finite G]`); this finiteness is what makes the canonical inductions
`Ind_W^S`/`Ind_W^T` in `mu_definition`/`nu_definition` well-defined. -/
structure Hypothesis where
  [finiteG : Finite G]
  S : Subgroup G
  T : Subgroup G
  W1 : Subgroup G
  W2 : Subgroup G
  W : Subgroup G
  P : Subgroup G
  Q : Subgroup G
  U : Subgroup G
  V : Subgroup G
  C : Subgroup G
  D : Subgroup G
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
  W_eq_inter : W = S ⊓ T
  W_eq_join : W = W1 ⊔ W2
  W1_inf_W2_eq_bot : W1 ⊓ W2 = ⊥
  W1_commutes_W2 : ∀ x ∈ W1, ∀ y ∈ W2, Commute x y
  W_cyclic : IsCyclic ↥W
  P_eq_SF : P = maxNilpotentNormalHall S
  Q_eq_TF : Q = maxNilpotentNormalHall T
  S_deriv_eq_PU : derivedInG S = P ⊔ U
  T_deriv_eq_QV : derivedInG T = Q ⊔ V
  /-- **Peterfalvi (13.1.b)/(13.2), T-side complement disjointness**: `Q ⊓ V = ⊥`.  The κ-Hall
  invariant complement `V` to `Q = T_F` in `T'` genuinely *complements* `Q` — a fact available
  ungated at the §16 construction (`exists_kappaHall_invariant_complement_to_MF` returns
  `M_F ⊓ U = ⊥` from `T`'s type-`P` structure, i.e. from `T_nonI`, **not** requiring
  (14.9)/`IsTypeP2 T`),
  but dropped by the abstract `T_deriv_eq_QV` (`T' = Q ⊔ V`, which alone does not force
  disjointness).
  Threading it exposes the T-side linchpin used by every V-side coprimality/complement argument
  (`isMulCommutative_V`, `coprime_card_V_card_Q_of_disjoint`, …), previously routed circularly
  through
  the then-sorried `reconciled_typePData_T` (`Q_inf_V_eq_bot_of_reconciled`). -/
  Q_inf_V_eq_bot : Q ⊓ V = ⊥
  /-- **Peterfalvi (13.1.b), T-side semidirect complement `T = T' ⋊ W₂`**: the cyclic factor `W₂`
  complements the derived subgroup `T'` in `T`.  Available ungated at the §16 construction from
  `typeP_derivedInG_isComplement_kappaHall` (BG 14.7(h), via `T`'s type-`P` structure `T_nonI`,
  **not** (14.9)); the abstract Hypothesis otherwise omits it.  Discharges the `M_complement` field
  of `reconciled_typePData_T` and lets the ungated `coprime_card_Q_card_VW2` build honestly. -/
  W2_isComplement_T_deriv :
    Subgroup.IsComplement' ((derivedInG T).subgroupOf T) (W2.subgroupOf T)
  C_eq : C = U ⊓ Subgroup.centralizer (P : Set G)
  D_eq : D = V ⊓ Subgroup.centralizer (Q : Set G)
  W1_normalizes_U : W1 ≤ Subgroup.normalizer (U : Set G)
  W2_normalizes_V : W2 ≤ Subgroup.normalizer (V : Set G)
  q : ℕ
  p : ℕ
  q_prime : q.Prime
  p_prime : p.Prime
  q_odd : Odd q
  p_odd : Odd p
  q_eq_card_W1 : q = Nat.card ↥W1
  p_eq_card_W2 : p = Nat.card ↥W2
  u : ℕ
  v : ℕ
  c : ℕ
  d : ℕ
  c_eq_card_C : c = Nat.card ↥C
  d_eq_card_D : d = Nat.card ↥D
  card_U_eq_uc : Nat.card ↥U = u * c
  card_V_eq_vd : Nat.card ↥V = v * d
  Sset : Set (ClassFunction ↥S ℂ)
  Tset : Set (ClassFunction ↥T ℂ)
  A0S : Set ↥S
  A0T : Set ↥T
  tauS : OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥S G
  tauT : OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥T G
  omega : Fin q → Fin p → ClassFunction ↥W ℂ
  eta : Fin q → Fin p → ClassFunction G ℂ
  mu : Fin q → Fin p → ClassFunction ↥S ℂ
  nu : Fin q → Fin p → ClassFunction ↥T ℂ
  delta : Fin p → ℤ
  deltaPrime : Fin q → ℤ
  /-- **Peterfalvi (13.1.e)**: the signs `δ_j`, `δ'_i` are `±1` (the (4.3.b) `sign_eq`). -/
  delta_pm_one : (∀ j : Fin p, delta j = 1 ∨ delta j = -1) ∧
    (∀ i : Fin q, deltaPrime i = 1 ∨ deltaPrime i = -1)
  /-- **Peterfalvi (4.3.d)**: the degree congruence `μ_{ij}(1) ≡ δ_j (mod q)`
  (`μ_{ij}(1) = δ_j + q·a` for an integer `a`, the `Res_{W₁}` value identity). -/
  mu_degree_modEq_delta : ∀ (i : Fin q) (j : Fin p), ∃ a : ℤ,
    mu i j 1 = (delta j : ℂ) + (q : ℂ) * (a : ℂ)
  /-- **Peterfalvi (4.4), the `S`-side base sign**: `δ_0 = 1` (`μ_{00} = 1_S`, the trivial
  column's `σ`-anchor). -/
  delta_zero_eq_one : delta ⟨0, p_prime.pos⟩ = 1
  /-- The Peterfalvi (3.2)/(3.3) transfer map `τ`, typed as an integral
  (virtual-character) map via the same `IntegralCharacterMap` convention as
  `tauS`/`tauT` — faithful to `τ` being defined on the `ℤ`-lattice of virtual
  characters.  Pinning `tau3` to the *concrete* (3.2) Dade isometry (built from a
  `S05.TICyclicHypothesis` for `W` through `S04.dadeIntegralCharacterMap`, with the
  `ω`-grid materialized as the (3.3) characters) is a dedicated §3/§5 construction;
  `eta_eq_tau_omega` already forces the `η`-grid to be the integral-linear image of
  the `ω`-grid. -/
  tau3 : OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥W G
  /-- **Peterfalvi (13.1.d)**: `η_{ij} = ω_{ij}^τ`. -/
  eta_eq_tau_omega : ∀ (i : Fin q) (j : Fin p), eta i j = tau3 (omega i j)
  /-- **Peterfalvi (13.1.e)**: `Ind_W^S (ω_{ij} − ω_{0j}) = δ_j (μ_{ij} − μ_{0j})`,
  where the induction is the canonical `Ind_W^S = ClassFunction.induce (W.subgroupOf S)`
  (transporting the `W`-grid into `S` via `W ≤ S`) and `δ_j = ±1` is `delta`. -/
  mu_definition : ∀ (i : Fin q) (j : Fin p),
    ClassFunction.induce (W.subgroupOf S)
        (ClassFunction.compHom
          (Subgroup.subgroupOfEquivOfLe
            ((le_of_eq W_eq_inter).trans inf_le_left)).toMonoidHom
          (omega i j - omega ⟨0, q_prime.pos⟩ j))
      = (delta j : ℂ) • (mu i j - mu ⟨0, q_prime.pos⟩ j)
  /-- **Peterfalvi (13.1.e), irreducibility**: each `μ_{ij}` is an irreducible character of `S`
  (the (1.4)/(4.3.b) column families consist of irreducibles; threaded from the
  `SignedIrreducibleDifferenceFamily` producer, issue 2035 μ-linkage). -/
  mu_irreducible : ∀ (i : Fin q) (j : Fin p),
    OddOrder.RepresentationTheory.IsIrreducibleCharacter (mu i j)
  /-- **Peterfalvi (13.1.e), column distinctness**: within a column `j` the `μ_{ij}` are
  pairwise distinct (the (1.4) family `injective` field).  Makes the column sums
  `μ_j = ∑_i μ_{ij}` sums of `q ≥ 2` distinct irreducibles — hence reducible, the (13.3.a)
  entry condition. -/
  mu_col_injective : ∀ j : Fin p, Function.Injective (fun i : Fin q => mu i j)
  /-- **Peterfalvi (4.3.b), full-grid orthonormality** (issues 9076/9014, the `(13.18)`
  grounding): the `μ_{ij}` are pairwise-distinct irreducibles across the *whole* grid,
  `⟨μ_{ij}, μ_{kl}⟩ = [(i,j) = (k,l)]`.  Within a column this refines `mu_irreducible` +
  `mu_col_injective`; the cross-column part is the prime-TI residue-grid fact
  (S06 `columnFamily_mu_ne` / `PrimeTIResidueData.mu2_orthonormal`), supplied by the
  producer from `Section16CharacterData.muS_orthonormal`.  Discharges the `(13.18)` pin
  `mu_row0_ne` (row-`0` cross-column distinctness, `S15_HonestTypeP2A0`). -/
  mu_orthonormal : ∀ (i k : Fin q) (j l : Fin p),
    OddOrder.RepresentationTheory.ClassFunction.inner (mu i j) (mu k l)
      = if i = k ∧ j = l then 1 else 0
  /-- **Peterfalvi (4.5.a) for the `S`-grid** (issue 2035 μ-linkage): each `μ`-column sum is
  induced from an irreducible character of `S' = [S,S]` — the §4 certain-type identity
  `μ_j = Ind_{S'}^S χ_j` (`induce_restrict_certainType_eq`), the constructive membership
  shape behind (13.3.a)'s `μ_j ∈ 𝒮(H₀)`. -/
  mu_colSum_eq_induce : ∀ j : Fin p,
    ∃ ψ : ClassFunction ↥((derivedInG S).subgroupOf S) ℂ,
      OddOrder.RepresentationTheory.IsIrreducibleCharacter ψ ∧
      (∑ i : Fin q, mu i j) = ClassFunction.induce ((derivedInG S).subgroupOf S) ψ ∧
      (j ≠ ⟨0, p_prime.pos⟩ →
        ¬ (((W2.subgroupOf S).subgroupOf ((derivedInG S).subgroupOf S) :
            Set ↥((derivedInG S).subgroupOf S)) ⊆
          OddOrder.Peterfalvi.S03.characterKernel ψ))
  /-- **Peterfalvi (9.8)/(9.11) reverse dichotomy (S-side R-family gate)** (issue 9092): a
  *reducible* member of the general kernel-filter family `S(X)` over `S' = derivedInG S` (any
  kernel demand `X`) is a nonzero `μ`-column sum `∑ᵢ μ_{ij}`, `j ≠ 0`.  This is the S-side
  analogue of the M-side `reducible_mem_inducedKernelFamily_eq_muGrid_columnSum` (`S12_HcBound`);
  it is *supplied by the producer* from the §6 certain-type identity
  `μ = certainTypeS.columnFamily.mu` (the abstract `Hypothesis` cannot see this identification,
  so the reverse dispatch is threaded as a field).  It is consumed by the (Clifford-case-agnostic)
  per-member `R`-family (`sSet_memberRFamily`): a reducible `η ∈ 𝒮` bridges into `S(⊥)` — the `𝒳`
  condition `¬(H ⊆ Ker)` forces `η`'s source nontrivial — and is dispatched to its μ-column `j`,
  whose §6 `certainTypeR` image family is the (5.2.d) `R`-datum. -/
  mu_reducible_dichotomy : ∀ {X : Subgroup ↥S} {ψ : ClassFunction ↥S ℂ},
    ψ ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily ((derivedInG S).subgroupOf S) X →
    ¬ OddOrder.RepresentationTheory.IsIrreducibleCharacter ψ →
    ∃ j : Fin p, j ≠ ⟨0, p_prime.pos⟩ ∧ ψ = ∑ i : Fin q, mu i j
  /-- **Peterfalvi (13.1.e)**: `Ind_W^T (ω_{ij} − ω_{i0}) = δ'_i (ν_{ij} − ν_{i0})`,
  with the canonical `Ind_W^T = ClassFunction.induce (W.subgroupOf T)` and
  `δ'_i = ±1` is `deltaPrime`. -/
  nu_definition : ∀ (i : Fin q) (j : Fin p),
    ClassFunction.induce (W.subgroupOf T)
        (ClassFunction.compHom
          (Subgroup.subgroupOfEquivOfLe
            ((le_of_eq W_eq_inter).trans inf_le_right)).toMonoidHom
          (omega i j - omega i ⟨0, p_prime.pos⟩))
      = (deltaPrime i : ℂ) • (nu i j - nu i ⟨0, p_prime.pos⟩)
  m : ℚ
  m_eq : m = 1 - 1 / ((q : ℚ) - 1) - ((q : ℚ) - 1) / (q : ℚ) ^ p +
    1 / (((q : ℚ) - 1) * (q : ℚ) ^ p)
  /-- **Peterfalvi (13.1.b) carrier (S-side)**: the type-`P` structure data of `S`
  (`S = (P ⋊ U) ⋊ W₁`), with its complement `U` and cyclic factor `W₁` reconciled to the
  hypothesis's `U`/`W1` (`Sdata_U_eq`/`Sdata_W1_eq`).  This is the §16-construction witness
  (`Section16TypePStructure.Sdata`, built from `mp.S_typeP2` = Pf (13.2.a)) that pins the otherwise
  unconstrained relationship between the abstract `Hypothesis` fields `U`/`W1`/`P` and the intrinsic
  type-`P` decomposition of `S`.  It supplies the U-side structural facts (`U` complements
  `M_F = P`, `W₁ ≤ N_G(U)`, `U` nilpotent) that Peterfalvi §15 reads off `S`. -/
  Sdata : TypePData S
  Sdata_U_eq : Sdata.U = U
  Sdata_W1_eq : Sdata.W1 = W1
  /-- **Peterfalvi (13.2.a), U-side**: the complement `U` is abelian.  Supplied at construction from
  BG Lemma 15.1(b) (`typeP_hall_derived_eq_and_abelian`, with `U` the `(κ∪σ)'`-Hall of `S`), so §15
  need not re-derive it; discharges the `U_commutative` field of `basic_structure_gated`. -/
  S_U_commutative : IsMulCommutative ↥U
  /-- **Reconciliation (W₂-side)**: the intrinsic dual factor `Sdata.W2 = C_{S'}(W₁#)` equals the
  abstract `W₂` (complement of `W₁` in the cyclic `W = S ∩ T`).  Supplied at construction as
  `Sdata.W2 = K*` (`typePData_of_kappaHall_hallComplement_W2`); discharges `card_P_eq` and hence
  `basic_structure_gated.P_order` (issue 3001/4014). -/
  Sdata_W2_eq : Sdata.W2 = W2
  /-- **Peterfalvi (4.8), `μ`-column-difference support** (issues 9076/9014, the `(13.18)`
  support grounding; Coq `prDade_sub_TIirr_on`): for nontrivial equal-degree columns
  `j, k ≠ 0`, the difference `μ_{ij} − μ_{ik}` is supported in `A₀(S) = A(S) ∪ V^S`.
  Supplied by the producer from `Section16CharacterData.muS_diff_support` (the §6 support
  engine `certainType_diff_supp_subset_A0` at the `muS`-instance `Hypothesis46` `hyp46Smp`).
  Discharges the `(13.18)` support pin `tauS_mu_row0_diff_support` (`S15_HonestTypeP2A0`). -/
  mu_diff_support : ∀ (i : Fin q) {j k : Fin p},
    j ≠ ⟨0, p_prime.pos⟩ → k ≠ ⟨0, p_prime.pos⟩ →
    mu i j 1 = mu i k 1 →
    (mu i j - mu i k).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (S10.typePACore0 S Sdata) S
  /-- **Peterfalvi (4.3.c), value identity** (Coq `prTIirr_id`, `PFsection4.v:403`; issues
  9076/9014, the `(13.18)` V-value grounding): on `W ∖ W₂` the `μ`-grid is the signed
  `ω`-grid, `μ_{ij}(w) = δ_j·ω_{ij}(w)`.  Supplied by the producer from the §6 value
  identity `certainType_apply_eq_of_mem_V` (the (1.3)/(4.3.c) value-match of the
  certain-type construction — Dade-free, base `S06.Hypothesis` level).  With `δ_j = 1`
  (`delta_eq_one_S`, Pf (13.3.c)) this becomes the prime-TI restriction identity
  (`μ_{0j}|_{W∖W₂} = ω`-value) feeding the `(13.18)` V-value pin
  `tauS_mu_row0_vanish_on_V`. -/
  mu_apply_of_not_mem_W2 : ∀ (i : Fin q) (j : Fin p) (w : G) (hwW : w ∈ W)
    (hwS : w ∈ S), w ∉ (W2 : Set G) →
    mu i j ⟨w, hwS⟩ = (delta j : ℂ) * omega i j ⟨w, hwW⟩
  /-- **Peterfalvi (4.9)(a), CF-level conjugation symmetry of the `μ`-grid** (Coq
  `prTIirr_aut`; the full-CF strengthening of the generic-element `eta_pair_of_coprime`
  pattern): `μ̄_{ij} = μ_{−i,−j}`.  Supplied by the producer from `muS_conj`
  (the §6 conjugation bridge `certainType_mu_conj_eq` with the power-enumeration index
  bridges).  Feeds the (13.18.c) reality of `Γ` (`gammaGrid_real`). -/
  mu_conj : ∀ (i : Fin q) (j : Fin p),
    (mu i j).conj = mu (finNeg q_prime.pos i) (finNeg p_prime.pos j)
  /-- **Peterfalvi (3.9.a), CF-level conjugation symmetry of the `η`-grid** (Coq
  `cfAut_cycTIiso`): `η̄_{ij} = η_{−i,−j}`.  Supplied by the producer from
  `tau3W_omegaS_conj` (`σ` Galois-intertwining `sigma_mapRingEquiv_comm` + linear-character
  inversion `galoisMap_conj_omega`, through the power enumerations).  Feeds the (13.18.c)
  reality of `Γ` (`gammaGrid_real`). -/
  eta_conj : ∀ (i : Fin q) (j : Fin p),
    (eta i j).conj = eta (finNeg q_prime.pos i) (finNeg p_prime.pos j)
  /- ### Grid property fields (issue 3002)

  The (3.2)/(3.3)/(3.4) character-theoretic content of the Dade grid carriers `tau3`/`omega`,
  which the §15 norm cascade ((13.5)–(13.10)) consumes.  All are supplied at construction from
  the honest spine grid (`Section16CharacterData.omegaS`/`tau3W` in `FeitThompson.lean`):
  ω-orthonormality via `S05.TICyclicHypothesis.omega_inner`, the τ₃ facts via the (3.2)
  σ-isometry package (`S05.TICyclicHypothesis.sigmaIntegral_*`). -/
  /-- **Peterfalvi (3.2), isometry part**: `τ₃` preserves the class-function inner product. -/
  tau3_isometry : OddOrder.Peterfalvi.S07.IsIntegralIsometry tau3
  /-- **Peterfalvi (3.2)**: `τ₃` sends the trivial character to the trivial character. -/
  tau3_trivial : tau3 (trivialClassFunction ↥W) = trivialClassFunction G
  /-- **Peterfalvi (3.2.c)**: on the regular set `W ∖ (W₁ ∪ W₂)` the map `τ₃` is the
  identity: `(α^{τ₃})(w) = α(w)` for regular `w`. -/
  tau3_apply_of_regular : ∀ (α : ClassFunction ↥W ℂ) (w : G) (hwW : w ∈ W),
    w ∉ (W1 : Set G) ∪ (W2 : Set G) → tau3 α w = α ⟨w, hwW⟩
  /-- **Peterfalvi (3.2)**: `τ₃` sends virtual characters to virtual characters. -/
  tau3_mem_ZIrr : ∀ z ∈ ZIrr ↥W, tau3 z ∈ ZIrr G
  /-- **Peterfalvi (3.3)/(3.4)**: the `ω`-grid is orthonormal. -/
  omega_orthonormal : ∀ (i k : Fin q) (j l : Fin p),
    ClassFunction.inner (omega i j) (omega k l) = if i = k ∧ j = l then 1 else 0
  /-- The `ω_{ij}` are linear characters: `ω_{ij}(1) = 1`. -/
  omega_apply_one : ∀ (i : Fin q) (j : Fin p), omega i j 1 = 1
  /-- Each `ω_{ij}` is a virtual character (in fact an irreducible character of `W`). -/
  omega_mem_ZIrr : ∀ (i : Fin q) (j : Fin p), omega i j ∈ ZIrr ↥W
  /-- **Peterfalvi (3.3)** (issue 2033): each `ω_{ij}` is multiplicative — a linear character. -/
  omega_mul : ∀ (i : Fin q) (j : Fin p) (w w' : ↥W),
    omega i j (w * w') = omega i j w * omega i j w'
  /-- **Peterfalvi (3.3)** (issue 2033): the column-`0` characters `ω_{i0}` are trivial on `W₂`. -/
  omega_col_zero_apply_of_mem_W2 : ∀ (i : Fin q) (w : ↥W), (w : G) ∈ W2 →
    omega i ⟨0, p_prime.pos⟩ w = 1
  /-- **Peterfalvi (3.3)** (issue 2033): the row-`0` characters `ω_{0j}` are trivial on `W₁`. -/
  omega_row_zero_apply_of_mem_W1 : ∀ (j : Fin p) (w : ↥W), (w : G) ∈ W1 →
    omega ⟨0, q_prime.pos⟩ j w = 1
  /-- **Peterfalvi (3.3)** (issue 2033): on `W₁` the grid values are `q`-th roots of unity. -/
  omega_pow_q_of_mem_W1 : ∀ (i : Fin q) (j : Fin p) (w : ↥W), (w : G) ∈ W1 →
    omega i j w ^ q = 1
  /-- **Peterfalvi (3.3)** (issue 2033): on `W₂` the grid values are `p`-th roots of unity. -/
  omega_pow_p_of_mem_W2 : ∀ (i : Fin q) (j : Fin p) (w : ↥W), (w : G) ∈ W2 →
    omega i j w ^ p = 1
  /-- **Peterfalvi (3.2.d)** (issue 2034): a class function of `G` orthogonal to the whole
  `τ₃ω`-grid vanishes on the regular set `Ŵ = W ∖ (W₁ ∪ W₂)` — the grid enumerates the
  `σ`-image, and every irreducible off the image vanishes on `Ŵ`. -/
  eta_complete_vanish : ∀ χ : ClassFunction G ℂ,
    (∀ (i : Fin q) (j : Fin p), ClassFunction.inner (tau3 (omega i j)) χ = 0) →
    ∀ w : G, w ∈ W → w ∉ (W1 : Set G) ∪ (W2 : Set G) → χ w = 0
  /-- **Peterfalvi (3.4)/(3.5), the four-corner vanishing** (issue 2036): off the conjugacy
  saturation of the regular set `Ŵ = W ∖ (W₁ ∪ W₂)`, the `(3.5)` relation collapses to
  `1 − (τ₃ω)_{i0}(x) − (τ₃ω)_{0j}(x) + (τ₃ω)_{ij}(x) = 0` for nonzero row/column indices. -/
  eta_fourcorner_vanish : ∀ (i : Fin q) (j : Fin p), i ≠ ⟨0, q_prime.pos⟩ →
    j ≠ ⟨0, p_prime.pos⟩ → ∀ x : G,
    x ∉ OddOrder.GroupTheory.conjClassSet ((W : Set G) \ ((W1 : Set G) ∪ (W2 : Set G))) →
    (1 : ℂ) - tau3 (omega i ⟨0, p_prime.pos⟩) x - tau3 (omega ⟨0, q_prime.pos⟩ j) x
      + tau3 (omega i j) x = 0
  /-- **Peterfalvi (3.9.b), row-vanishing transport** (issue 2036): if `(τ₃ω)₁₀` vanishes at
  `x`, so do all `(τ₃ω)_{i0}` with `i ≠ 0` — the nontrivial row characters are Galois-conjugate
  powers of `ω₁₀`, and the twist fixes the vanishing value. -/
  eta_row_vanish_of_one_zero : ∀ x : G,
    tau3 (omega ⟨1, q_prime.one_lt⟩ ⟨0, p_prime.pos⟩) x = 0 →
    ∀ i : Fin q, i ≠ ⟨0, q_prime.pos⟩ → tau3 (omega i ⟨0, p_prime.pos⟩) x = 0
  /-- **Peterfalvi (3.9.b), full row-axis Galois orbit.** -/
  eta_row_galois_orbit : ∀ i : Fin q, i ≠ ⟨0, q_prime.pos⟩ →
    ∃ u : ℂ ≃+* ℂ,
      ClassFunction.mapRingEquiv u (tau3 (omega ⟨1, q_prime.one_lt⟩ ⟨0, p_prime.pos⟩)) =
        tau3 (omega i ⟨0, p_prime.pos⟩)
  /-- **Peterfalvi (3.9.b), full column-axis Galois orbit.** -/
  eta_column_galois_orbit : ∀ j : Fin p, j ≠ ⟨0, p_prime.pos⟩ →
    ∃ u : ℂ ≃+* ℂ,
      ClassFunction.mapRingEquiv u (tau3 (omega ⟨0, q_prime.pos⟩ ⟨1, p_prime.one_lt⟩)) =
        tau3 (omega ⟨0, q_prime.pos⟩ j)
  /-- **Peterfalvi (3.9.c), the `η`-grid integrality on generic elements** (issue-3002
  keystone): for `g` of order prime to `pq`, each grid value `η_{ij}(g) = (τ₃ω)_{ij}(g)` is a
  rational integer.  The genuine §3/§5 Dade-Galois fact (`σ` intertwines the cyclotomic Galois
  action, so a value at `g` of order prime to the character order `|ξ_{ij}| ∣ pq` is fixed by
  every ring automorphism of `ℂ`, hence rational; a rational algebraic integer is an integer).
  Supplied from the honest spine grid (`Section16CharacterData.omegaS`/`tau3W`, whose value is
  `σ(ω(ξ_{ij}))(g)`) through `S05.exists_intCast_sigma_omega_apply`.  The c-side (`S16`) cites
  this after `MHypothesis.G0_orderOf_coprime` to fill `EtaGenericData.eta_int`. -/
  eta_intCast_of_coprime : ∀ (g : G), Nat.Coprime (orderOf g) (p * q) →
    ∀ (i : Fin q) (j : Fin p), ∃ m : ℤ, eta i j g = (m : ℂ)
  /-- **Peterfalvi (3.9.a), the conjugate-pair symmetry of the `η`-grid on generic elements**
  (issue-3002 keystone): for `g` of order prime to `pq`, the grid pairs under the index
  negation `(i,j) ↦ (−i,−j)` (`finNeg`), `η_{−i,−j}(g) = η_{ij}(g)`.  Peterfalvi's (3.9.a):
  the complex conjugate of `η_{ij}` is the grid character at the conjugate index, and the value at
  `g` (a rational integer by (3.9.c), hence real) equals its conjugate.  Stated with
  `S15.finNeg` (defeq to `S16.finNeg`) so the c-side (`S16`) cites it to fill
  `EtaGenericData.eta_pair`. -/
  eta_pair_of_coprime : ∀ (g : G), Nat.Coprime (orderOf g) (p * q) →
    ∀ (i : Fin q) (j : Fin p),
      eta (finNeg q_prime.pos i) (finNeg p_prime.pos j) g = eta i j g
  /-- **Peterfalvi (3.9), the principal grid value on generic elements** (issue-3002 keystone):
  for `g` of order prime to `pq` (in fact for every `g`), the principal entry is `η₀₀(g) = 1`.
  Since `ω₀₀ = 1_W` is the trivial character and `τ₃(1_W) = 1_G` (`tau3_trivial`), the value
  is `1`.  The c-side (`S16`) cites this to fill `EtaGenericData.eta_principal`. -/
  eta_principal_of_coprime : ∀ (g : G), Nat.Coprime (orderOf g) (p * q) →
    eta ⟨0, q_prime.pos⟩ ⟨0, p_prime.pos⟩ g = 1

namespace Hypothesis

/-- Peterfalvi's `H = P C` in (13.5)--(13.10). -/
def H (hyp : Hypothesis (G := G)) : Subgroup G :=
  hyp.P ⊔ hyp.C

/-- Peterfalvi's `K = Q D`, used symmetrically for `T`. -/
def K (hyp : Hypothesis (G := G)) : Subgroup G :=
  hyp.Q ⊔ hyp.D

/-- `H = PC ≤ S`: `P = S_F ≤ S` and `C = U ∩ C_G(P) ≤ U ≤ S' ≤ S`. -/
theorem H_le_S [Finite G] (hyp : Hypothesis (G := G)) : hyp.H ≤ hyp.S := by
  have hUS : hyp.U ≤ hyp.S := by
    have h1 : hyp.U ≤ derivedInG hyp.S := by rw [hyp.S_deriv_eq_PU]; exact le_sup_right
    exact le_trans h1 (Subgroup.map_subtype_le _)
  change hyp.P ⊔ hyp.C ≤ hyp.S
  refine sup_le ?_ ?_
  · rw [hyp.P_eq_SF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le hyp.S
  · rw [hyp.C_eq]; exact le_trans inf_le_left hUS

/-- The generic set `G_0 = G# - ((H#)^G union (Q#)^G)` from (13.9). -/
def G0 (hyp : Hypothesis (G := G)) : Set G :=
  sharpSubgroup (⊤ : Subgroup G) \
    (conjClassSet (sharpSubgroup hyp.H) ∪
      conjClassSet (sharpSubgroup hyp.Q))

/-- Under **Peterfalvi (13.1)**, the prime `q` is odd, hence not `2`. -/
theorem q_ne_two (hyp : Hypothesis (G := G)) : hyp.q ≠ 2 := by
  intro hq2
  have hodd : Odd 2 := by simpa [hq2] using hyp.q_odd
  rcases hodd with ⟨k, hk⟩
  omega

/-- Under **Peterfalvi (13.1)**, the prime `p` is odd, hence not `2`. -/
theorem p_ne_two (hyp : Hypothesis (G := G)) : hyp.p ≠ 2 := by
  intro hp2
  have hodd : Odd 2 := by simpa [hp2] using hyp.p_odd
  rcases hodd with ⟨k, hk⟩
  omega

/-- Under **Peterfalvi (13.1)**, `q` is at least `3`. -/
theorem three_le_q (hyp : Hypothesis (G := G)) : 3 ≤ hyp.q := by
  have htwo : 2 ≤ hyp.q := hyp.q_prime.two_le
  have hne : hyp.q ≠ 2 := hyp.q_ne_two
  omega

/-- Under **Peterfalvi (13.1)**, `p` is at least `3`. -/
theorem three_le_p (hyp : Hypothesis (G := G)) : 3 ≤ hyp.p := by
  have htwo : 2 ≤ hyp.p := hyp.p_prime.two_le
  have hne : hyp.p ≠ 2 := hyp.p_ne_two
  omega

end Hypothesis

/-- Carrier for the basic structural conclusions of Peterfalvi (13.2). -/
structure BasicStructureData (hyp : Hypothesis (G := G)) where
  S_typeII_or_typeIII : IsTypeII hyp.S ∨ IsTypeIII hyp.S
  q_lt_p_forces_typeII : hyp.q < hyp.p → IsTypeII hyp.S
  U_commutative : IsMulCommutative ↥hyp.U
  UW1_frobenius : OddOrder.Isaacs.Ch06.IsFrobeniusGroup
    ↥(hyp.U ⊔ hyp.W1) (hyp.U.subgroupOf (hyp.U ⊔ hyp.W1))
      (hyp.W1.subgroupOf (hyp.U ⊔ hyp.W1))
  P_elementaryAbelian : IsElementaryAbelian hyp.p ↥hyp.P
  P_order : Nat.card ↥hyp.P = hyp.p ^ hyp.q
  u_bound : hyp.u ≤ (hyp.p ^ hyp.q - 1) / (hyp.p - 1)
  A0S_TI : Prop
  A0S_TI_holds : A0S_TI
  tauS_eq_induction : Prop
  tauS_eq_induction_holds : tauS_eq_induction

/-- **`S` is of type `P`**: the carried `S_nonI` taxonomy alternative lies in the BG type-`P`
class.  This is the common structural input for the `S`-side Dade support constructions and is
faithful to the symmetric (13.1) carrier. -/
theorem Hypothesis.S_isTypeP [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G)) :
    OddOrder.BG.Ch4.S14.IsTypeP hyp.S :=
  OddOrder.BG.Ch4.S16.isTypeP_of_isTypeNonI hG hyp.S_maximal hyp.S_nonI

/-- **The §9 type-II/type-III setup on `S`** (Peterfalvi (13.2.a) → (9.2)): the
`TypesIIIIIIVSetup` carrier for `S`, from the honest taxonomy alternative supplied by `S_nonI`.
`maximal`/`typeP` are the carried `S_maximal`/`Sdata`; the nontrivial core is witness-independent
and transported to `Sdata`; `type_alt` retains the actual type-II/type-III branch.  Note the §9
machinery's `H` is `Sdata.H = S_F = P`, so the
§9 inertia subgroup `HC` is `PC = hyp.H` — the (13.3.a) `Ind_{PC}(linear)` shape.  Opens the §9
Clifford/degree machinery ((9.7)–(9.9), the `hcPsi`-induction analysis) on `S`. -/
noncomputable def Hypothesis.toTypesIIIIIIVSetupS [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G)) :
    OddOrder.Peterfalvi.S11.TypesIIIIIIVSetup hyp.S := by
  have htype : IsTypeII hyp.S ∨ IsTypeIII hyp.S :=
    OddOrder.Peterfalvi.S13.isTypeII_or_isTypeIII_of_isTypeNonI
      hG hyp.S_maximal hyp.S_nonI
  exact { maximal := hyp.S_maximal
          typeP := hyp.Sdata
          nontrivial := by
            rcases htype with hII | hIII
            · exact hII.some.common.transfer hyp.Sdata
            · exact hIII.some.common.transfer hyp.Sdata
          type_alt := htype.elim Or.inl (fun hIII => Or.inr (Or.inl hIII)) }

open OddOrder.Isaacs.Ch03.IsAInvariant (quotientMulAutHom) in
/-- **§9 character data on `S`** (S12-mk mirror; degree-only placeholders): `u = |Ū|` is
rfl-pinned to the `U`-action image; `tau := hyp.tauS`, `H0CprimeSupport := ∅` and
`quotientSemidirectFrobenius := True` are the documented count/degree-only placeholders (as in
`S12.Hypothesis.mkSection11CharacterData` — NOT for (9.11)-coherence consumption; the honest
support/tau construction is issue 2035 step 1b).  Opens `caseB_degree_qu`, the (9.9) counts and
the (9.9.c) `hcPsi`-induction exhaustion on `S` for the (13.3) μ-column facts. -/
noncomputable def Hypothesis.mkSection11CharacterDataS [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG)) :
    OddOrder.Peterfalvi.S11.Section11CharacterData (hyp.toTypesIIIIIIVSetupS hG) chief where
  u := Nat.card ↥(((quotientMulAutHom (N := chief.N) chief.N_aInvariant).comp
      ((hyp.toTypesIIIIIIVSetupS hG).typeP.U.subgroupOf
        ((hyp.toTypesIIIIIIVSetupS hG).typeP.U
          ⊔ (hyp.toTypesIIIIIIVSetupS hG).typeP.W1)).subtype).range)
  u_eq_card_quotient := rfl
  H0CprimeSupport := ∅
  tau := hyp.tauS
  quotientSemidirectFrobenius := True

open scoped FiniteInduce in
/-- **`Ind_S^G` as a `ℂ`-linear map** `CF(S) →ₗ[ℂ] CF(G)` (issue 2035 step 1).  The
canonical class-function induction `ClassFunction.induce hyp.S`, bundled as a linear map;
linearity is `ClassFunction.induce_add` / `ClassFunction.induce_smul`.  This is the concrete
Peterfalvi (13.2.e)/(7.2) Dade isometry `τ = Ind_S^G` (the `(S, H^#)` isometry coincides with
induction), used as the honest `tau` of the §9 character data on `S`. -/
noncomputable def Hypothesis.indSLinearC [Finite G] (hyp : Hypothesis (G := G)) :
    ClassFunction ↥hyp.S ℂ →ₗ[ℂ] ClassFunction G ℂ where
  toFun := ClassFunction.induce hyp.S
  map_add' := ClassFunction.induce_add hyp.S
  map_smul' c θ := ClassFunction.induce_smul hyp.S c θ

open scoped FiniteInduce in
@[simp] theorem Hypothesis.indSLinearC_apply [Finite G] (hyp : Hypothesis (G := G))
    (θ : ClassFunction ↥hyp.S ℂ) :
    hyp.indSLinearC θ = ClassFunction.induce hyp.S θ := rfl

open scoped FiniteInduce in
/-- **`Ind_S^G` as an `IntegralCharacterMap ↥S G`** (issue 2035 step 1): the `ℤ`-linear
`Ind_S^G`, obtained by restricting scalars of the `ℂ`-linear `indSLinearC`.  This is the honest
`τ` value the §9 coherence (`coherent_H0C_commutator`) consumes for the (13.3) `S`-instance —
Peterfalvi's `τ = Ind_S^G` (13.2.e). -/
noncomputable def Hypothesis.indS [Finite G] (hyp : Hypothesis (G := G)) :
    OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥hyp.S G :=
  (hyp.indSLinearC).restrictScalars ℤ

open scoped FiniteInduce in
@[simp] theorem Hypothesis.indS_apply [Finite G] (hyp : Hypothesis (G := G))
    (θ : ClassFunction ↥hyp.S ℂ) :
    hyp.indS θ = ClassFunction.induce hyp.S θ := rfl

open scoped FiniteInduce in
/-- **`Ind_T^G` as an `IntegralCharacterMap ↥T G`** — the `T`-side mirror of `Hypothesis.indS`.
Used as the (unconstrained) `tau1T` of the λ-free core until the ν-side (13.2.e)-T coherence
lands (`nuGridSupply`, gated on the a-owned FT-layer carrier threading), and as the re-grounded
target of the caseA-`T` (9.11) base coherence (`sSetIrrDegT_coherent_indT`). -/
noncomputable def Hypothesis.indT [Finite G] (hyp : Hypothesis (G := G)) :
    OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥hyp.T G :=
  LinearMap.restrictScalars ℤ
    ({ toFun := ClassFunction.induce hyp.T
       map_add' := ClassFunction.induce_add hyp.T
       map_smul' := fun c θ => ClassFunction.induce_smul hyp.T c θ } :
      ClassFunction ↥hyp.T ℂ →ₗ[ℂ] ClassFunction G ℂ)

open scoped FiniteInduce in
@[simp] theorem Hypothesis.indT_apply [Finite G] (hyp : Hypothesis (G := G))
    (θ : ClassFunction ↥hyp.T ℂ) :
    hyp.indT θ = ClassFunction.induce hyp.T θ := rfl

/-- **`C' = [C, C]` as a subgroup** (Peterfalvi (9.5), `S`-instance): the derived subgroup of
`C = C_U(P)`.  Definitionally matches the §9 `cprimeSub` (`= derivedInG (cSub …)`) once the
`S`-instance kernel `cSub = C` identification (`toTypesIIIIIIVSetupS_cSub_eq_C`) is applied. -/
def Hypothesis.Cprime (hyp : Hypothesis (G := G)) : Subgroup G := derivedInG hyp.C

/-- **(13.2.e) `normedTI` core — no `A(S)`-point escapes** (Coq `FTtypeP_facts` (e) escaping
exclusion, PFsection13.v:224-238): on a type-`P₂` maximal subgroup, every `a ∈ A(M)` has
`C_G(a) ≤ M`.

Suppose `a ∈ A(M)` escapes.  Then `a ∈ M_σ^#` ((8.13.b),
`S10.escaping_typePACore_mem_sigmaSharp`), and BG Theorem D(4)
(`exists_RData_escape_structure`) attaches the unique maximal `N ⊇ C_G(a)`, of type `F` or
`P₂`, with `a ∈ Â_σ(N) ∖ N_σ` and `N_F = N_σ`:

* **`N` of type `P₂`** (Coq `Ltype2` branch, `typePF_exclusion`): the `P₂`-escape package
  (BG Cor 15.9, `centralizer_escape_final_local`, via the D(4) tail) makes `M` type `F` —
  contradicting `M` type `P₂` (`not_isTypeP_and_isTypeF`).
* **`N` of type `F`** (Coq `Ltype1` branch, `FTtype1_Frobenius`): `N` is of Peterfalvi type I
  (Prop 16.1, `isTypeI_iff_isTypeF`), so Peterfalvi (12.7) (`typeI_frobenius`) makes `N`
  Frobenius with kernel `N_F = N_σ`; `a ∈ Â_σ(N)` centralizes some `1 ≠ z ∈ N_σ`, and
  Frobenius-kernel regularity (Isaacs Thm 6.4, `centralizer_kernel_le`) pulls `a` into the
  kernel `N_σ` — contradicting `a ∉ N_σ`. -/
theorem escaping_typePACore_eq_empty [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hTP : OddOrder.BG.Ch4.S14.IsTypeP M) :
    OddOrder.GroupTheory.escapingCentralizerSet M (S10.typePACore M) = ∅ := by
  classical
  rw [Set.eq_empty_iff_forall_notMem]
  rintro a ⟨haA, haesc⟩
  -- the matched `κ`-Hall / `(κ∪σ)′`-Hall pair, for the `σ`-sharp confinement (8.13.b)
  obtain ⟨K₀, U₀, hKM, hUM, hKne, hK, hU⟩ :=
    S10.typeP_exists_kappa_hall_pair hG hM hTP
  have haσ : a ∈ OddOrder.BG.Ch4.S14.sigmaSharp M :=
    S10.escaping_typePACore_mem_sigmaSharp hG hM hKM hUM hKne hK hU ⟨haA, haesc⟩
  -- BG Theorem D(4): the unique neighbour `N ⊇ C_G(a)` with the escape structure
  obtain ⟨R, -, N, ⟨hNmem, -, hMFN, hxAN, hNtype, -, hP2imp⟩, -⟩ :=
    OddOrder.BG.Ch4.S16.exists_RData_escape_structure hG hM haσ haesc
  rcases hNtype with hNF | hNP2
  · -- `N` type `F`: Frobenius-kernel regularity forces `a ∈ N_σ`, contradiction.
    have hNmax : N ∈ maximalSubgroups G := hNmem.1
    have hNI : OddOrder.GroupTheory.IsTypeI N :=
      (OddOrder.Peterfalvi.S10Interface.isTypeI_iff_isTypeF hG hNmax).mpr hNF
    obtain ⟨fdata, -⟩ := OddOrder.Peterfalvi.S14.typeI_frobenius hG hnoV hNmax hNI
    -- the Frobenius kernel is `N_F = N_σ` (the D(4) `S15.MF N = Msigma N` conjunct)
    have hker : fdata.typeI.typeF.H = OddOrder.BG.Ch3.S10.Msigma N := by
      rw [fdata.typeI.typeF.H_eq]; exact hMFN
    -- `a ∈ Â_σ(N)`: some `1 ≠ z ∈ N_σ` commutes with `a`
    obtain ⟨haN, hne⟩ : a ∈ OddOrder.BG.Ch4.S16.hatMsigma N := hxAN.1.1
    obtain ⟨z, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
    obtain ⟨hzMσ, hzC⟩ := Subgroup.mem_inf.mp z.2
    have hzN : (z : G) ∈ N := OddOrder.BG.Ch3.S10.Msigma_le N hzMσ
    have hzG1 : (z : G) ≠ 1 := fun h => hz1 (Subtype.ext h)
    -- `a` centralizes `z` inside `↥N`; kernel regularity pulls `a` into the kernel
    have haker : (⟨a, haN⟩ : ↥N) ∈ fdata.typeI.typeF.H.subgroupOf N := by
      refine fdata.frobenius.centralizer_kernel_le ⟨(z : G), hzN⟩
        (Subgroup.mem_subgroupOf.mpr (by rw [hker]; exact hzMσ))
        (fun h => hzG1 (congrArg Subtype.val h)) ?_
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hzC).symm
    exact hxAN.2 (SetLike.mem_coe.mpr
      (by rw [← hker]; exact Subgroup.mem_subgroupOf.mp haker))
  · -- `N` type `P₂`: the escape package makes `M` type `F`, contradicting type `P`.
    obtain ⟨hFM, -⟩ := hP2imp hNP2
    exact OddOrder.BG.Ch4.S14.not_isTypeP_and_isTypeF ⟨hTP, hFM⟩

/-- **(13.2.e) `S`-instance Dade hypothesis** (issue 1017 update #10, step 1): the
`Hypothesis`-level
instantiation of `S10.dadeSupportHypothesisData_typePACore` at the type-`P` maximal `S`
(via `hyp.S_maximal`/`hyp.S_isTypeP`), packaging the honest §16 support
`A(S) = ⋃_{x∈S_σ#} C_{S'}(x)#` (`S10.typePACore hyp.S`) as an `S04.Hypothesis`. This is the
concrete
`S04` Dade datum for `S` (previously only available as the standalone theorem taking `hM`/`hP2`);
its
`.fullDadeIsometryData` (given the support's `HConjInvariant`) materialises the Dade isometry
`τ = Ind_S^G` on the `ℤ`-lattice of virtual characters — the (13.2.e) foundation the §9 subcoherence
assembly (`S07.irrSubcoherent`) consumes to re-ground `coherent_H0Cprime_S` off the unsound
`sibleyTarget_H0C`.  (Sorry-provenance parity with `S10.dadeSupportHypothesisData_typePACore`: the
inherited shared BG §16 Theorem-II pins, at exact parity with the accepted on-path
`dadeSupportHypotheses_typeI`; no lane-`b` sorry introduced.) -/
noncomputable def Hypothesis.dadeHypS [Fintype G] [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G)) :
    OddOrder.Peterfalvi.S04.Hypothesis G (S10.typePACore hyp.S) hyp.S :=
  (S10.dadeSupportHypothesisData_typePACore hG hyp.S_maximal (hyp.S_isTypeP hG)).some.dade

open scoped FiniteInduce in
/-- **(13.2.e) `S`-instance `dade = Ind` bridge** (issue 1017): for the honest type-`P₂` maximal
`S`,
on a class function `f` supported in a trivial-`H` sub-support `A₁ ⊆ A(S)` (an `S`-invariant subset
on which the `S`-instance Dade stabilizers vanish), the honest (13.2.e) Dade isometry
`τ = dadeIntegralCharacterMap (dadeHypS hG) …` acts as plain induction `Ind_S^G`.  This is the exact
`S`-instance analogue of the type-I bridge `S14.typeI_tau_eq_induce_of_supported_trivial_H`,
instantiating the general step-3 bridge `S14.dadeMap_eq_induce_of_supported_on_trivial_H` at the
`S`-instance Dade map `dadeHypS hG` (via `dadeIntegralCharacterMap_apply_of_support`, which rewrites
the lifted integral map as the §4 `dadeMap` on the supported carrier; `inclusion` widens the support
from `A₁` to `A(S)`).  The trivial-`H` sub-support facts (`hA₁A`, `hA₁norm`, `hH₁`, `hf`) are taken
as hypotheses, exactly as the type-I version defers them to the caller.  This is the `dade = Ind`
identity the (13.2.e)/(7.2) coherence route (`τ = Ind_S^G`, Peterfalvi (13.2.e)) rests on, matching
the honest `indS` value. -/
theorem Hypothesis.sInstance_dade_eq_induce_of_supported_trivial_H [Fintype G] [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    {A₁ : Set G} (hA₁A : A₁ ⊆ S10.typePACore hyp.S)
    (hA₁norm : ∀ (l : ↥hyp.S) ⦃a : G⦄, a ∈ A₁ → (l : G) * a * (l : G)⁻¹ ∈ A₁)
    (hH₁ : ∀ a, ((hyp.dadeHypS hG).restrict hA₁A hA₁norm).H a = ⊥)
    {f : ClassFunction ↥hyp.S ℂ}
    (hf : f.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup A₁ hyp.S) :
    OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS hG)
        ((hyp.dadeHypS hG).fullDadeIsometryData) f
      = ClassFunction.induce hyp.S f := by
  have hfA : f.support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (S10.typePACore hyp.S) hyp.S :=
    hf.trans (OddOrder.Peterfalvi.S04.supportInSubgroup_mono hA₁A)
  have h1 : OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS hG)
        ((hyp.dadeHypS hG).fullDadeIsometryData) f
      = (hyp.dadeHypS hG).dadeMap (k := ℂ)
        ⟨f, (ClassFunction.mem_supportedSubmodule).mpr hfA⟩ :=
    OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_apply_of_support (hyp.dadeHypS hG)
      ((hyp.dadeHypS hG).fullDadeIsometryData) hfA
  rw [h1]
  -- `⟨f, hfA⟩` is defeq to `inclusion hA₁A ⟨f, hf⟩` (same carrier `f`), so step 3 applies directly.
  exact OddOrder.Peterfalvi.S14.dadeMap_eq_induce_of_supported_on_trivial_H (hyp.dadeHypS hG)
    hA₁A hA₁norm hH₁ ⟨f, (ClassFunction.mem_supportedSubmodule).mpr hf⟩

/-- **(Rung B, reduction step 1) `dadeHypS.H a = ftSupportKernel S (A(S)) a`.**  The `S`-instance
Dade
stabilizer at a support point `a` is the faithful per-`x` (8.14) signalizer kernel
`R(a) = ftSupportKernel S (A(S)) a`, read off the `H_eq_ftSupportKernel` field of the underlying
`DadeSupportHypothesisData` (the very `.some` witness `dadeHypS` is projected from).  This is the
concrete formula `H(a) = R(a)` of Peterfalvi (8.15)/(8.14), specialised to the honest type-`P₂`
support `A(S)`. -/
theorem Hypothesis.dadeHypS_H_eq_ftSupportKernel [Fintype G] [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (a : {a : G // a ∈ S10.typePACore hyp.S}) :
    (hyp.dadeHypS hG).H a =
      OddOrder.Peterfalvi.S10.ftSupportKernel hyp.S (S10.typePACore hyp.S) a.1 :=
  (OddOrder.Peterfalvi.S10.dadeSupportHypothesisData_typePACore hG hyp.S_maximal
    (hyp.S_isTypeP hG)).some.H_eq_ftSupportKernel a

/-- **(Rung B, reduction) No escaping `A(S)`-points ⟹ all `S`-instance Dade stabilizers vanish.**
For the honest type-`P₂` support, `dadeHypS.H a = ftSupportKernel S (A(S)) a`
(`dadeHypS_H_eq_ftSupportKernel`), and the faithful kernel is `⊥` off the escaping set
(`ftSupportKernel_eq_bot_of_not_escaping`).  So if `A(S)` has no escaping point
(`∀ a ∈ A(S), a ∉ escapingCentralizerSet S (A(S))`, the Coq `FTtypeP_facts` (e) `normedTI` core,
Rung C), then `∀ a, dadeHypS.H a = ⊥` — the exact input `S04.isDadeMap_induce_of_forall_H_eq_bot` /
`sInstance_dade_eq_induce_of_supported_trivial_H` need to run `τ = Ind_S^G` on the *full* `A(S)`. -/
theorem Hypothesis.forall_dadeHypS_H_eq_bot_of_not_escaping [Fintype G] [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hno : ∀ a ∈ S10.typePACore hyp.S,
      a ∉ OddOrder.GroupTheory.escapingCentralizerSet hyp.S (S10.typePACore hyp.S)) :
    ∀ a : {a : G // a ∈ S10.typePACore hyp.S}, (hyp.dadeHypS hG).H a = ⊥ := by
  intro a
  rw [hyp.dadeHypS_H_eq_ftSupportKernel hG a]
  exact OddOrder.Peterfalvi.S10.ftSupportKernel_eq_bot_of_not_escaping (hno a.1 a.2)

/-- **(Rung C at `Hypothesis` level): no `A(S)`-point escapes `S`.**  The general type-`P`
escaping exclusion `escaping_typePACore_eq_empty` instantiated at the carrier's `S`
(`hyp.S_maximal`, `hyp.S_isTypeP`) — the single input Rung B was reduced to. -/
theorem Hypothesis.no_escaping_typePACore [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G)) :
    ∀ a ∈ S10.typePACore hyp.S,
      a ∉ OddOrder.GroupTheory.escapingCentralizerSet hyp.S (S10.typePACore hyp.S) := by
  intro a _ ha
  rw [escaping_typePACore_eq_empty hG hnoV hyp.S_maximal (hyp.S_isTypeP hG)] at ha
  exact Set.notMem_empty a ha

/-- **(13.2.e) for the `S`-instance, stabilizer form: every `S`-instance Dade stabilizer is
trivial.**  Rung B + Rung C: no `A(S)`-point escapes (`no_escaping_typePACore`), so every
`dadeHypS` stabilizer `H a = R(a)` vanishes (`forall_dadeHypS_H_eq_bot_of_not_escaping`). -/
theorem Hypothesis.forall_dadeHypS_H_eq_bot [Fintype G] [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G)) :
    ∀ a : {a : G // a ∈ S10.typePACore hyp.S}, (hyp.dadeHypS hG).H a = ⊥ :=
  hyp.forall_dadeHypS_H_eq_bot_of_not_escaping hG (hyp.no_escaping_typePACore hG hnoV)

open scoped FiniteInduce in
/-- **(13.2.e) `normedTI`, isometry half — `τ = Ind_S^G` on all of `A(S)`** (Coq
`FTtypeP_facts` (e), `{in 'CF(S, 'A0(S)), tau =1 'Ind}`): the `S`-instance Dade isometry agrees
with plain induction on every `A(S)`-supported class function.  This is
`sInstance_dade_eq_induce_of_supported_trivial_H` at the full support `A₁ = A(S)`, whose
trivial-stabilizer input is discharged by Rung C (`forall_dadeHypS_H_eq_bot`) — the honest
`dade = Ind` identity the (13.3) `tau1S_apply_induce_sub` route consumes. -/
theorem Hypothesis.sInstance_dade_eq_induce [Fintype G] [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G))
    {f : ClassFunction ↥hyp.S ℂ}
    (hf : f.support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (S10.typePACore hyp.S) hyp.S) :
    OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS hG)
        ((hyp.dadeHypS hG).fullDadeIsometryData) f
      = ClassFunction.induce hyp.S f :=
  hyp.sInstance_dade_eq_induce_of_supported_trivial_H hG (subset_refl _)
    (fun l _ ha => S10.typePACore_conj_mem l.2 ha)
    (fun a => hyp.forall_dadeHypS_H_eq_bot hG hnoV ⟨a.1, a.2⟩) hf

/-- **The honest `(H₀ ⊔ C')^#`-support for the `S`-instance, `= (C')^#`** (issue 2035 step 2).
For the `S`-instance the chief kernel is trivial (`toTypesIIIIIIVSetupS_chief_N_eq_bot`, giving
`H₀ = ⊥`), so the §9 `H₀C'`-support degenerates to `(C')^#` — the non-identity elements of
`C' = [C, C]`, viewed inside `↥S` via `C' ≤ C ≤ U ≤ S`.  This is the genuine `H0CprimeSupport`
of the honest §9 character data on `S`, replacing the `∅`-placeholder of
`mkSection11CharacterDataS`. -/
def Hypothesis.cprimeSharpS (hyp : Hypothesis (G := G)) : Set ↥hyp.S :=
  OddOrder.Peterfalvi.S04.sharp ((hyp.Cprime).subgroupOf hyp.S : Set ↥hyp.S)

@[simp] theorem Hypothesis.mem_cprimeSharpS (hyp : Hypothesis (G := G)) {x : ↥hyp.S} :
    x ∈ hyp.cprimeSharpS ↔ (x : G) ∈ hyp.Cprime ∧ x ≠ 1 := by
  simp only [Hypothesis.cprimeSharpS, OddOrder.Peterfalvi.S04.mem_sharp, SetLike.mem_coe,
    Subgroup.mem_subgroupOf]

open OddOrder.Peterfalvi.S11 in
open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (4.7), `S`-instance induced support**: `Supp Ind_{HU}^S ξ ⊆ A(S) ∪ {1}` for every
`ξ ∈ 𝒳` (Peterfalvi (9.5)'s family, `H ⊄ Ker ξ`), where `A(S) = ⋃_{x∈S_σ#} C_{S'}(x)#` is the honest
type-`P₂` Dade support (`S10.typePACore hyp.S`).

This is the honest §9 instance of the (4.7) support fact underlying the (5.3.a) R-datum's
`hdiffsupp`
input (the family differences of `𝒮` must vanish off `A(S)`).  The proof **mirrors** the S06 (4.7)
induced-support lemma `S06.induce_apply_eq_zero_of_not_mem_union_of_not_subset_characterKernel`
(the S06 statement is bound to the `Hypothesis46` structure and cannot be instantiated for the §9
`TypesIIIIIIVSetup`, so we replay its three steps directly in the `↥S` ambient):

* `support_induce_subset_conjugatesIntoSet`: a nonvanishing point `x` of `Ind_{HU}^S ξ` is
  `S`-conjugate to a point `w ∈ HU` of `Supp ξ`;
* the (4.7) **core** (Peterfalvi (1.2),
`irreducibleCharacter_apply_eq_zero_of_centralizerInSubgroup_eq_bot`
  contrapositive) forces a nontrivial `d ∈ H = P = S_F ≤ S_σ` centralizing `w`, and the covering
  condition puts `w ∈ A(S)` (via `S10.mem_typePACore`: `w ∈ S' = M'`, `w ≠ 1`, `w` centralizes
  `d ∈ S_σ#`);
* `S10.typePACore_conj_mem` ((4.7)'s `L_normalizes_A` replacement): `A(S)` is `S`-conjugation
  invariant, so the image of `x` lies in `A(S) ∪ {1}` too.

The inclusion `P = S_F ≤ S_σ` is the general `maxNilpotentNormalHall_le_Msigma` theorem, so this
support argument is uniform across the type-II/type-III alternative. -/
theorem Hypothesis.sSet_member_support_subset_A [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    {ξ : OddOrder.RepresentationTheory.IrreducibleCharacter ↥(huSub (hyp.toTypesIIIIIIVSetupS hG))}
    (hξ : ξ ∈ xiSet (hyp.toTypesIIIIIIVSetupS hG)) :
    (induceHU (hyp.toTypesIIIIIIVSetupS hG)
        (ξ : ClassFunction ↥(huSub (hyp.toTypesIIIIIIVSetupS hG)) ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (S10.typePACore hyp.S) hyp.S ∪ {1} := by
  classical
  -- `H = P = S_F ≤ S_σ`.
  have hHP : (hyp.toTypesIIIIIIVSetupS hG).H = hyp.P := by
    change hyp.Sdata.H = hyp.P
    rw [hyp.Sdata.H_eq, hyp.P_eq_SF]
  have hPle : hyp.P ≤ OddOrder.BG.Ch3.S10.Msigma hyp.S := by
    rw [hyp.P_eq_SF]
    exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_Msigma hG hyp.S_maximal
  -- the (4.7) core: a nonvanishing `w ∈ HU` with `(w:S) ≠ 1` maps into `A(S)`.
  have hcore : ∀ w : ↥(huSub (hyp.toTypesIIIIIIVSetupS hG)),
      (ξ : ClassFunction ↥(huSub (hyp.toTypesIIIIIIVSetupS hG)) ℂ) w ≠ 0 →
      ((w : ↥hyp.S) : G) ≠ 1 →
      ((w : ↥hyp.S) : G) ∈ S10.typePACore hyp.S := by
    intro w hwval hwne
    -- (1.2) contrapositive: `C_{hInHu}(w) ≠ ⊥`.
    have := hInHu_normal (hyp.toTypesIIIIIIVSetupS hG)
    have hCne : OddOrder.Peterfalvi.S03.centralizerInSubgroup
        (hInHu (hyp.toTypesIIIIIIVSetupS hG)) w ≠ ⊥ := fun hbot =>
      hwval
        (OddOrder.Peterfalvi.S03.irreducibleCharacter_apply_eq_zero_of_centralizerInSubgroup_eq_bot
          ξ hξ hbot)
    -- extract a nontrivial `d ∈ hInHu` centralizing `w`.
    obtain ⟨d, hd_mem, hd_ne⟩ := (Subgroup.bot_or_exists_ne_one _).resolve_left hCne
    rw [OddOrder.Peterfalvi.S03.mem_centralizerInSubgroup] at hd_mem
    obtain ⟨hd_H, hd_comm⟩ := hd_mem
    -- `d`'s ambient image lies in `H = P` and is nontrivial; it commutes with `w`.
    have hdS_H : (d : ↥hyp.S) ∈ (hyp.toTypesIIIIIIVSetupS hG).H.subgroupOf hyp.S :=
      (Subgroup.mem_subgroupOf).mp hd_H
    have hdH_G : ((d : ↥hyp.S) : G) ∈ (hyp.toTypesIIIIIIVSetupS hG).H :=
      (Subgroup.mem_subgroupOf).mp hdS_H
    have hdG_ne : ((d : ↥hyp.S) : G) ≠ 1 := fun he => hd_ne (by
      apply Subtype.ext; apply Subtype.ext; exact he)
    have hcommG : ((d : ↥hyp.S) : G) * ((w : ↥hyp.S) : G)
        = ((w : ↥hyp.S) : G) * ((d : ↥hyp.S) : G) := by
      have := congrArg (fun t : ↥hyp.S => (t : G)) (Subtype.ext_iff.mp hd_comm)
      simpa using this
    -- covering condition: `(w:S) ∈ A(S)` via `S10.mem_typePACore` with witness `d ∈ S_σ#`.
    rw [S10.mem_typePACore]
    refine ⟨?_, hwne, ((d : ↥hyp.S) : G), ?_, ?_⟩
    · -- `w ∈ S' = M'` since `w ∈ HU = (derivedInG S).subgroupOf S`.
      have hwHU : (w : ↥hyp.S) ∈ (derivedInG hyp.S).subgroupOf hyp.S := by
        rw [← huSub_eq_derivedInG_subgroupOf]; exact w.2
      exact (Subgroup.mem_subgroupOf).mp hwHU
    · -- `d ∈ S_σ# = (Msigma S)#`.
      refine (Set.mem_sdiff _).mpr ⟨?_, fun he => hdG_ne (Set.mem_singleton_iff.mp he)⟩
      have hdP : ((d : ↥hyp.S) : G) ∈ hyp.P := hHP ▸ hdH_G
      exact SetLike.mem_coe.mpr (hPle hdP)
    · -- `w` centralizes `d`.
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hcommG.symm
  -- assemble via `support_induce_subset_conjugatesIntoSet` + conjugation invariance.
  intro x hx
  rw [Set.mem_union, Set.mem_singleton_iff]
  by_cases hx1 : x = 1
  · exact Or.inr hx1
  -- `x` is `S`-conjugate into `Supp ξ`.
  have hxsupp : (induceHU (hyp.toTypesIIIIIIVSetupS hG)
      (ξ : ClassFunction ↥(huSub (hyp.toTypesIIIIIIVSetupS hG)) ℂ)) x ≠ 0 :=
    ClassFunction.mem_support.mp hx
  have hx_conj : x ∈ ClassFunction.conjugatesIntoSet (huSub (hyp.toTypesIIIIIIVSetupS hG))
      ((ξ : ClassFunction ↥(huSub (hyp.toTypesIIIIIIVSetupS hG)) ℂ)).support := by
    have hind : induceHU (hyp.toTypesIIIIIIVSetupS hG)
          (ξ : ClassFunction ↥(huSub (hyp.toTypesIIIIIIVSetupS hG)) ℂ)
        = ClassFunction.induce (huSub (hyp.toTypesIIIIIIVSetupS hG))
          (ξ : ClassFunction ↥(huSub (hyp.toTypesIIIIIIVSetupS hG)) ℂ) := rfl
    refine ClassFunction.support_induce_subset_conjugatesIntoSet (subset_refl _) ?_
    rw [← hind]; exact hxsupp
  rw [ClassFunction.mem_conjugatesIntoSet] at hx_conj
  obtain ⟨c, hc, hcsupp⟩ := hx_conj
  set w : ↥(huSub (hyp.toTypesIIIIIIVSetupS hG)) := ⟨c⁻¹ * x * c, hc⟩ with hw_def
  have hw_val : (ξ : ClassFunction ↥(huSub (hyp.toTypesIIIIIIVSetupS hG)) ℂ) w ≠ 0 :=
    ClassFunction.mem_support.mp hcsupp
  -- `(w:S) = c⁻¹ x c`; `x = c (w:S) c⁻¹` with `c ∈ S`.
  have hwS_eq : ((w : ↥hyp.S) : G) = (c : G)⁻¹ * (x : G) * (c : G) := rfl
  have hxeq : (x : G) = (c : G) * ((w : ↥hyp.S) : G) * (c : G)⁻¹ := by
    rw [hwS_eq]; group
  have hwne : ((w : ↥hyp.S) : G) ≠ 1 := by
    intro he
    apply hx1
    have hxG : (x : G) = 1 := by rw [hxeq, he]; group
    exact Subtype.ext hxG
  have hwA : ((w : ↥hyp.S) : G) ∈ S10.typePACore hyp.S := hcore w hw_val hwne
  -- conjugate back: `A(S)` is `S`-conjugation invariant.
  refine Or.inl ?_
  rw [OddOrder.Peterfalvi.S04.mem_supportInSubgroup, hxeq]
  exact S10.typePACore_conj_mem c.2 hwA

open OddOrder.Peterfalvi.S11 in
open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **(5.3.a) per-member difference support** (issue 1017): the Dade-image support hypothesis
`((Ind ξ)̄ − Ind ξ).support ⊆ A(S)` (as an `S`-support) that
`S07.dadeCharacterDifferenceImageOfDiff`
consumes to build the `CharacterDifferenceImage` of an irreducible §9 member.  From
`sSet_member_support_subset_A` (support `⊆ A(S) ∪ {1}`), removing the identity: the difference
`(Ind ξ)̄ − Ind ξ` vanishes at `1` (the degree `Ind ξ(1) = q·ξ(1)` is a positive real,
self-conjugate).
This is the `hdiffsupp` half of the R-datum — the S-instance `R1_diffsupp` (Peterfalvi §12/§5). -/
theorem Hypothesis.sSet_member_diffsupp [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    {ξ : OddOrder.RepresentationTheory.IrreducibleCharacter ↥(huSub (hyp.toTypesIIIIIIVSetupS hG))}
    (hξ : ξ ∈ xiSet (hyp.toTypesIIIIIIVSetupS hG)) :
    ((induceHU (hyp.toTypesIIIIIIVSetupS hG)
          (ξ : ClassFunction ↥(huSub (hyp.toTypesIIIIIIVSetupS hG)) ℂ)).conj
        - induceHU (hyp.toTypesIIIIIIVSetupS hG)
          (ξ : ClassFunction ↥(huSub (hyp.toTypesIIIIIIVSetupS hG)) ℂ)).support
      ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (S10.typePACore hyp.S) hyp.S := by
  set φ : ClassFunction ↥hyp.S ℂ :=
    induceHU (hyp.toTypesIIIIIIVSetupS hG)
      (ξ : ClassFunction ↥(huSub (hyp.toTypesIIIIIIVSetupS hG)) ℂ) with hφ
  have hsupp_eq : φ.conj.support = φ.support := by
    ext y
    simp only [ClassFunction.mem_support, ne_eq, ClassFunction.conj_apply, star_eq_zero]
  intro x hx
  have hx0 : (φ.conj - φ) x ≠ 0 := hx
  have hxsupp : x ∈ φ.support := by
    have hxU := ClassFunction.support_sub_subset _ _ hx
    rwa [hsupp_eq, Set.union_self] at hxU
  rcases hyp.sSet_member_support_subset_A hG hξ (hφ ▸ hxsupp) with h | h
  · exact h
  · exfalso
    rw [Set.mem_singleton_iff] at h
    subst h
    obtain ⟨d, _, hd⟩ :=
      OddOrder.RepresentationTheory.irreducibleCharacter_apply_one_eq_pos_natCast ξ
    apply hx0
    rw [ClassFunction.sub_apply, ClassFunction.conj_apply, hφ, induceHU_apply_one_eq_q_mul, hd,
      star_mul', star_natCast, star_natCast, sub_self]

end OddOrder.Peterfalvi.S15


