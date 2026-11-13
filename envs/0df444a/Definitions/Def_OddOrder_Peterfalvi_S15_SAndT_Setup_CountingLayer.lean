-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S15_SAndT_Setup_CountingLayer
-- name    : OddOrder_Peterfalvi_S15_SAndT_Setup_CountingLayer
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T15:50:26.457549+00:00
-- url     : https://prove2.me/theorems/5044735e-ee0d-49ac-a961-71847114be41
-- title:
--   Peterfalvi (13.5)–(13.10): counting layer
-- statement:
--   Formalizes the counting layer of Peterfalvi (13.5)–(13.10) for the pair $(S,T)$, including the §9 setup and character data on $T$ and the degrees of the $\mu$-column sums of (13.3.a).
--
--   Main declarations: `Hypothesis.toTypesIIIIIIVSetupT` (The §9 setup on `T`); `Hypothesis.mkSection11CharacterDataT` (§9 character data on `T`); `Hypothesis.mu_j_degree` (Peterfalvi (13.3.a), degree); `Hypothesis.mu_apply_one_column_const` (Column-constant degree).
--
--   The bundle also proves 14 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S15_SAndT_Setup/CountingLayer.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S15_SAndT_Setup/CountingLayer.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S15_SAndT_Setup_PairStructure

namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

section CountingLayer

open OddOrder.GroupTheory

open scoped Classical in
/-- **The §9 setup on `T`** (the (13.4) gate-3 router, issue 9013): the `TypesIIIIIIVSetup T`
carrier assembled from the **reconciled** type-`P` datum (`reconciled_typePData_T`), so its
`U`/`W1`/`W2` are the hypothesis's `V`/`W₂`/`W₁` (companions `toTypesIIIIIIVSetupT_U_eq` etc.)
and its kernel is `H = T_F = Q` (`toTypesIIIIIIVSetupT_H_eq`).  Nontriviality: `U = V ≠ ⊥` from
`|V| = v·d ≠ 1`; `|W1| = |W₂| = p` prime; the `M_F`-TI component of `TypePNontrivialCore` is
datum-independent, read off any non-V type witness (`T_typeII_or_III_or_IV`).  Opens the §9
machinery ((9.7)–(9.9), `typeII_III_IV_order_relations`, the `hcPsi` degree analysis) on `T` —
the (13.3.b)-on-`T` route of the (13.4) θ-package.  Mirrors `toTypesIIIIIIVSetupS`; extracts the
chief-factor setup later used by the unconditional `Q_elementaryAbelian`. -/
noncomputable def Hypothesis.toTypesIIIIIIVSetupT [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hvd : hyp.v * hyp.d ≠ 1) :
    OddOrder.Peterfalvi.S11.TypesIIIIIIVSetup hyp.T where
  maximal := hyp.T_maximal
  typeP := (reconciled_typePData_T hG hyp).choose
  nontrivial := by
    obtain ⟨hU, hW1, -⟩ := (reconciled_typePData_T hG hyp).choose_spec
    refine ⟨?_, ?_, ?_⟩
    · rw [hU]
      intro hbot
      apply hvd
      rw [← hyp.card_V_eq_vd, hbot, Subgroup.card_bot]
    · rw [hW1, ← hyp.p_eq_card_W2]
      exact hyp.p_prime
    · rcases hyp.T_typeII_or_III_or_IV hG hvd with h | h | h
      · exact h.some.common.2.2
      · exact h.some.common.2.2
      · exact h.some.common.2.2
  type_alt := hyp.T_typeII_or_III_or_IV hG hvd

theorem Hypothesis.toTypesIIIIIIVSetupT_U_eq [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hvd : hyp.v * hyp.d ≠ 1) :
    (hyp.toTypesIIIIIIVSetupT hG hvd).U = hyp.V :=
  (reconciled_typePData_T hG hyp).choose_spec.1

theorem Hypothesis.toTypesIIIIIIVSetupT_W1_eq [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hvd : hyp.v * hyp.d ≠ 1) :
    (hyp.toTypesIIIIIIVSetupT hG hvd).W1 = hyp.W2 :=
  (reconciled_typePData_T hG hyp).choose_spec.2.1

theorem Hypothesis.toTypesIIIIIIVSetupT_H_eq [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hvd : hyp.v * hyp.d ≠ 1) :
    ((hyp.toTypesIIIIIIVSetupT hG hvd).H : Subgroup G) = hyp.Q := by
  change (reconciled_typePData_T hG hyp).choose.H = hyp.Q
  rw [(reconciled_typePData_T hG hyp).choose.H_eq, hyp.Q_eq_TF]

open OddOrder.Isaacs.Ch03.IsAInvariant (quotientMulAutHom) in
/-- **§9 character data on `T`** (the T-mirror of `mkSection11CharacterDataS`, over the
`toTypesIIIIIIVSetupT` router; issue 9013 gate 3): `u = |V̄|` is rfl-pinned to the `V`-action
image on the chief factor of `Q`; `tau := hyp.tauT`; `H0CprimeSupport := ∅` and
`quotientSemidirectFrobenius := True` are the same documented count/degree-only placeholders as
the `S`-instance (NOT for coherence consumption).  Opens the §9 (9.8)/(9.9) counts — in
particular the (13.3.b) dichotomy glue `caseB_of_no_irreducible_sOf_H0Cprime` — on `T`. -/
noncomputable def Hypothesis.mkSection11CharacterDataT [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hvd : hyp.v * hyp.d ≠ 1)
    (chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetupT hG hvd)) :
    OddOrder.Peterfalvi.S11.Section11CharacterData (hyp.toTypesIIIIIIVSetupT hG hvd) chief where
  u := Nat.card ↥(((quotientMulAutHom (N := chief.N) chief.N_aInvariant).comp
      (((hyp.toTypesIIIIIIVSetupT hG hvd).typeP.U.subgroupOf
        ((hyp.toTypesIIIIIIVSetupT hG hvd).typeP.U
          ⊔ (hyp.toTypesIIIIIIVSetupT hG hvd).typeP.W1)).subtype)).range)
  u_eq_card_quotient := rfl
  H0CprimeSupport := ∅
  tau := hyp.tauT
  quotientSemidirectFrobenius := True

/-- `|S'| = |P|·|U|` — the (13.1.b) `S' = P ⋊ U` order decomposition
(`Sdata.derived_complement`). -/
theorem Hypothesis.card_deriv_S_eq [Finite G] (hyp : Hypothesis (G := G)) :
    Nat.card ↥(derivedInG hyp.S) = Nat.card ↥hyp.P * Nat.card ↥hyp.U := by
  have h := hyp.Sdata.derived_complement.card_mul_card
  have hPeq : hyp.Sdata.H = hyp.P := by rw [hyp.Sdata.H_eq, hyp.P_eq_SF]
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hyp.Sdata.H_le).toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hyp.Sdata.U_le).toEquiv, hPeq,
    hyp.Sdata_U_eq] at h
  exact h.symm

/-- `|S| = |S'|·q` — the (13.1.b) `S = S' ⋊ W₁` order decomposition (`Sdata.M_complement`). -/
theorem Hypothesis.card_S_eq_deriv_mul_q [Finite G] (hyp : Hypothesis (G := G)) :
    Nat.card ↥hyp.S = Nat.card ↥(derivedInG hyp.S) * hyp.q := by
  have hle : derivedInG hyp.S ≤ hyp.S := Subgroup.map_subtype_le _
  have h := hyp.Sdata.M_complement.card_mul_card
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hyp.Sdata.W1_le).toEquiv,
    hyp.Sdata_W1_eq, ← hyp.q_eq_card_W1] at h
  exact h.symm

/-- **`|S| = p^q·(uc)·q`** — the (13.2)-level order value of `S`, assembling
`card_S_eq_deriv_mul_q`, `card_deriv_S_eq`, `card_P_eq` (`|P| = p^q`), and `|U| = uc`. -/
theorem Hypothesis.card_S_val [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    Nat.card ↥hyp.S = hyp.p ^ hyp.q * (hyp.u * hyp.c) * hyp.q := by
  rw [hyp.card_S_eq_deriv_mul_q, hyp.card_deriv_S_eq, hyp.card_P_eq hG hyp.Sdata_W2_eq,
    hyp.card_U_eq_uc]

/-- **`|H| = p^q · c`** (Peterfalvi (13.2)): `H = PC` with `P = S_F` elementary abelian of order
`p^q` and `C = C_U(P)` of order `c`, and `P ⊓ C = ⊥` (`P` a `p`-group, `C ≤ U` with `|U| = uc`
coprime to `p` by the Hall property of `P` in `S`).  So `|PC| = |P|·|C| = p^q·c` (the complement
`card_mul_card_of_complement_normal`, `P ◁ H`).  Feeds `[S:H] = uq` (`mu_j_isIndPC` degree) and the
(13.5) counting value `|H^#|/|S| = uq/(cp^q)`. -/
theorem Hypothesis.card_H_eq [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    Nat.card ↥hyp.H = hyp.p ^ hyp.q * hyp.c := by
  have hP_le_S : hyp.P ≤ hyp.S := by
    rw [hyp.P_eq_SF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le hyp.S
  have hC_le_S : hyp.C ≤ hyp.S := by
    have hUS : hyp.U ≤ hyp.S := by
      have h1 : hyp.U ≤ derivedInG hyp.S := by rw [hyp.S_deriv_eq_PU]; exact le_sup_right
      exact le_trans h1 (Subgroup.map_subtype_le _)
    exact le_trans (hyp.C_eq ▸ inf_le_left) hUS
  have hPH : hyp.P ≤ hyp.H := le_sup_left
  have hCH : hyp.C ≤ hyp.H := le_sup_right
  have hPcard : Nat.card ↥hyp.P = hyp.p ^ hyp.q := hyp.card_P_eq hG hyp.Sdata_W2_eq
  -- `p ∤ c`: `P` Hall in `S`, `[S:P] = ucq`
  have hPScard : Nat.card ↥(hyp.P.subgroupOf hyp.S) = Nat.card ↥hyp.P :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP_le_S).toEquiv
  have hcop : Nat.Coprime (hyp.p ^ hyp.q) ((hyp.P.subgroupOf hyp.S).index) := by
    have hHall := OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_isHall hyp.S
    rw [← hyp.P_eq_SF] at hHall
    have h0 := Ch03.IsHallSubgroup.coprime_index hHall
    rw [hPScard, hPcard] at h0
    exact h0
  have hSPidx : (hyp.P.subgroupOf hyp.S).index = hyp.u * hyp.c * hyp.q := by
    have hm := Subgroup.card_mul_index (hyp.P.subgroupOf hyp.S)
    rw [hPScard, hPcard, hyp.card_S_val hG] at hm
    have hpq : (0 : ℕ) < hyp.p ^ hyp.q := pow_pos hyp.p_prime.pos hyp.q
    have hmm : hyp.p ^ hyp.q * (hyp.P.subgroupOf hyp.S).index
        = hyp.p ^ hyp.q * (hyp.u * hyp.c * hyp.q) := by rw [hm]; ring
    exact Nat.eq_of_mul_eq_mul_left hpq hmm
  have hpc : Nat.Coprime (hyp.p ^ hyp.q) hyp.c := by
    have hcdvd : hyp.c ∣ (hyp.P.subgroupOf hyp.S).index := by
      rw [hSPidx]; exact ⟨hyp.u * hyp.q, by ring⟩
    exact Nat.Coprime.coprime_dvd_right hcdvd hcop
  have hpc' : Nat.gcd (hyp.p ^ hyp.q) hyp.c = 1 := hpc
  -- `P ⊓ C = ⊥` from coprime orders
  have hdisj : hyp.P ⊓ hyp.C = ⊥ := by
    rw [← Subgroup.card_eq_one]
    have hd1 : Nat.card ↥(hyp.P ⊓ hyp.C) ∣ hyp.p ^ hyp.q :=
      hPcard ▸ Subgroup.card_dvd_of_le inf_le_left
    have hd2 : Nat.card ↥(hyp.P ⊓ hyp.C) ∣ hyp.c :=
      hyp.c_eq_card_C ▸ Subgroup.card_dvd_of_le inf_le_right
    exact Nat.dvd_one.mp (hpc' ▸ Nat.dvd_gcd hd1 hd2)
  -- `|H| = |P|·|C|` (complement `P ◁ H`)
  have hPnormalH : (hyp.P.subgroupOf hyp.H).Normal := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer hPH).mpr ?_
    have hSnorm : hyp.S ≤ Subgroup.normalizer (hyp.P : Set G) := by
      rw [hyp.P_eq_SF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer hyp.S
    exact le_trans (hyp.H_le_S) hSnorm
  have hinf : hyp.P.subgroupOf hyp.H ⊓ hyp.C.subgroupOf hyp.H = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxP, hxC⟩ := Subgroup.mem_inf.mp hx
    have hmem : ((x : ↥hyp.H) : G) ∈ hyp.P ⊓ hyp.C :=
      ⟨Subgroup.mem_subgroupOf.mp hxP, Subgroup.mem_subgroupOf.mp hxC⟩
    rw [hdisj, Subgroup.mem_bot] at hmem
    rw [Subgroup.mem_bot]; exact Subtype.ext hmem
  have hsup : hyp.P.subgroupOf hyp.H ⊔ hyp.C.subgroupOf hyp.H = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hPH hCH]
    exact Subgroup.subgroupOf_self hyp.H
  have hcompl : Subgroup.IsComplement' (hyp.P.subgroupOf hyp.H) (hyp.C.subgroupOf hyp.H) :=
    Subgroup.isComplement'_of_disjoint_and_mul_eq_univ (disjoint_iff.mpr hinf)
      (by rw [← Subgroup.normal_mul, hsup, Subgroup.coe_top])
  have hmul := hcompl.card_mul_card
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPH).toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCH).toEquiv, hPcard,
    ← hyp.c_eq_card_C] at hmul
  exact hmul.symm

/-- **`[S : H] = uq`** (Peterfalvi (13.2)): the index of `H = PC` in `S`.  From
`|S| = p^q·(uc)·q` (`card_S_val`) and `|H| = p^q·c` (`card_H_eq`), `[S:H] = |S|/|H| = uq`.  The
degree index of `mu_j_isIndPC` (`μ_j(1) = [S:H]·θ(1) = uq`). -/
theorem Hypothesis.H_index_eq_uq [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    (hyp.H.subgroupOf hyp.S).index = hyp.u * hyp.q := by
  have hm := Subgroup.card_mul_index (hyp.H.subgroupOf hyp.S)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hyp.H_le_S)).toEquiv, hyp.card_H_eq hG,
    hyp.card_S_val hG] at hm
  have hpos : (0 : ℕ) < hyp.p ^ hyp.q * hyp.c :=
    Nat.mul_pos (pow_pos hyp.p_prime.pos hyp.q) (hyp.c_eq_card_C ▸ Nat.card_pos)
  have hmm : hyp.p ^ hyp.q * hyp.c * (hyp.H.subgroupOf hyp.S).index
      = hyp.p ^ hyp.q * hyp.c * (hyp.u * hyp.q) := by rw [hm]; ring
  exact Nat.eq_of_mul_eq_mul_left hpos hmm

open scoped FiniteInduce in
/-- **Peterfalvi (13.3.a), degree**: each nonzero `μ`-column sum has degree `uq`.  Immediate from
`mu_j_isIndPC` (`μ_j = Ind_{PC} θ`, `θ` linear) and `H_index_eq_uq` (`[S:H] = uq`):
`μ_j(1) = [S:H]·θ(1) = uq·1 = uq`. -/
theorem Hypothesis.mu_j_degree [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (j : Fin hyp.p) (hj : j ≠ ⟨0, hyp.p_prime.pos⟩) :
    (∑ i : Fin hyp.q, hyp.mu i j) (1 : ↥hyp.S) = ((hyp.u * hyp.q : ℕ) : ℂ) := by
  have := hyp.finiteG
  obtain ⟨θ, hθirr, hθ1, hθeq⟩ := hyp.mu_j_isIndPC hG j hj
  rw [hθeq, ClassFunction.induce_apply_one, hθ1, mul_one, hyp.H_index_eq_uq hG]

open scoped FiniteInduce in
/-- **Column-constant degree** (Peterfalvi (13.1.e)/(4.3.c)): within a column `j`, all
`μ_{ij}(1)` are equal.  From `mu_definition` at `1`: the LHS `Ind_W^S(ω_{ij} − ω_{0j})(1)` is
`[S:W]·(ω_{ij}(1) − ω_{0j}(1)) = 0` (`omega_apply_one`: `ω`-grid linear), so the RHS
`δ_j·(μ_{ij}(1) − μ_{0j}(1)) = 0`, and `δ_j = ±1 ≠ 0` (`delta_pm_one`) gives the equality. -/
theorem Hypothesis.mu_apply_one_column_const [Finite G] (hyp : Hypothesis (G := G))
    (i : Fin hyp.q) (j : Fin hyp.p) :
    hyp.mu i j (1 : ↥hyp.S) = hyp.mu ⟨0, hyp.q_prime.pos⟩ j (1 : ↥hyp.S) := by
  have := hyp.finiteG
  have hdef := hyp.mu_definition i j
  have h1 := congrArg (fun f : ClassFunction ↥hyp.S ℂ => f (1 : ↥hyp.S)) hdef
  -- LHS(1) = 0
  rw [ClassFunction.induce_apply_one] at h1
  have homega0 : (ClassFunction.compHom
      (Subgroup.subgroupOfEquivOfLe ((le_of_eq hyp.W_eq_inter).trans inf_le_left)).toMonoidHom
        (hyp.omega i j - hyp.omega ⟨0, hyp.q_prime.pos⟩ j))
      (1 : ↥(hyp.W.subgroupOf hyp.S)) = 0 := by
    rw [ClassFunction.compHom_apply, map_one, ClassFunction.sub_apply,
      hyp.omega_apply_one, hyp.omega_apply_one, sub_self]
  rw [homega0, mul_zero] at h1
  -- RHS(1) = δ_j·(μ_{ij}(1) − μ_{0j}(1)) = 0, with δ_j ≠ 0
  have hδ : (hyp.delta j : ℂ) ≠ 0 := by
    rcases (hyp.delta_pm_one.1 j) with h | h <;> rw [h] <;> norm_num
  have hsub : hyp.mu i j (1 : ↥hyp.S) - hyp.mu ⟨0, hyp.q_prime.pos⟩ j (1 : ↥hyp.S) = 0 :=
    (mul_eq_zero.mp h1.symm).resolve_left hδ
  exact sub_eq_zero.mp hsub

open scoped FiniteInduce in
/-- **Peterfalvi (13.3.a), per-entry degree**: `μ_{ij}(1) = u` for `j ≥ 1`.  The column is
degree-constant (`mu_apply_one_column_const`), so the column sum `μ_j(1) = q·μ_{0j}(1)`; with
`μ_j(1) = uq` (`mu_j_degree`) and `q ≠ 0`, `μ_{0j}(1) = u`.  The `μ_{ij}(1) = u` that Peterfalvi
(13.3.c) feeds into the `(4.3.d)` congruence `u ≡ δ_j (mod q)` for `δ_j = 1`. -/
theorem Hypothesis.mu_apply_one_eq_u [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (i : Fin hyp.q) (j : Fin hyp.p)
    (hj : j ≠ ⟨0, hyp.p_prime.pos⟩) :
    hyp.mu i j (1 : ↥hyp.S) = ((hyp.u : ℕ) : ℂ) := by
  have := hyp.finiteG
  -- `∑ᵢ μ_{ij}(1) = q·μ_{0j}(1)` and `= uq`
  have hsum := hyp.mu_j_degree hG j hj
  rw [ClassFunction.finset_sum_apply] at hsum
  have hconst : ∑ k : Fin hyp.q, hyp.mu k j (1 : ↥hyp.S)
      = (hyp.q : ℂ) * hyp.mu ⟨0, hyp.q_prime.pos⟩ j (1 : ↥hyp.S) := by
    rw [Finset.sum_congr rfl (fun k _ => hyp.mu_apply_one_column_const k j),
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [hconst] at hsum
  have hq0 : (hyp.q : ℂ) ≠ 0 := by
    rw [Nat.cast_ne_zero]; exact hyp.q_prime.pos.ne'
  have h0j : hyp.mu ⟨0, hyp.q_prime.pos⟩ j (1 : ↥hyp.S) = ((hyp.u : ℕ) : ℂ) := by
    have : (hyp.q : ℂ) * hyp.mu ⟨0, hyp.q_prime.pos⟩ j (1 : ↥hyp.S)
        = (hyp.q : ℂ) * ((hyp.u : ℕ) : ℂ) := by rw [hsum]; push_cast; ring
    exact mul_left_cancel₀ hq0 this
  rw [hyp.mu_apply_one_column_const i j, h0j]

/-- **Peterfalvi `u ≡ 1 (mod q)`** (the (13.3.c) crux, (11.8.1) `|Ū| ≡ 1 mod q`).  The `S`-side
`U W₁` is a Frobenius group (`typeP_uW1_frobenius`), so for the conjugation homomorphism
`φ : U W₁ →* Aut(P)` the kernel-image `φ(U) = U/C_U(P) = Ū` satisfies `|Ū| ≡ 1 (mod |W₁|)`
(`IsFrobeniusGroup.card_range_comp_subtype_modEq_one`, Isaacs Lemma 6.1); with `|Ū| = u`
(`card_U_eq_uc`, `C = U ⊓ C_G(P)`) and `|W₁| = q` this is `u ≡ 1 (mod q)`.  Crucially **ungated**:
uses only the (proven) `U W₁` Frobenius structure, not the case-(b) Singer field model. -/
theorem Hypothesis.u_modEq_one [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) : hyp.u ≡ 1 [MOD hyp.q] := by
  have := hyp.finiteG
  let setup := hyp.toTypesIIIIIIVSetupS hG
  have hSdataUne := setup.nontrivial.1
  change hyp.Sdata.U ≠ ⊥ at hSdataUne
  have hfrob := OddOrder.Peterfalvi.S11.typeP_uW1_frobenius hyp.Sdata hSdataUne
  have hUW1leS : hyp.Sdata.U ⊔ hyp.Sdata.W1 ≤ hyp.S :=
    sup_le (hyp.Sdata.U_le.trans (Subgroup.map_subtype_le _)) hyp.Sdata.W1_le
  have hSnormP : hyp.S ≤ Subgroup.normalizer hyp.P := by
    rw [hyp.P_eq_SF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer hyp.S
  have hUW1normP : hyp.Sdata.U ⊔ hyp.Sdata.W1 ≤ Subgroup.normalizer hyp.P :=
    le_trans hUW1leS hSnormP
  let : MulDistribMulAction ↥(hyp.Sdata.U ⊔ hyp.Sdata.W1) ↥hyp.P :=
    MulDistribMulAction.compHom (M := ↥(Subgroup.normalizer hyp.P)) ↥hyp.P
      (Subgroup.inclusion hUW1normP)
  set φ : ↥(hyp.Sdata.U ⊔ hyp.Sdata.W1) →* MulAut ↥hyp.P :=
    MulDistribMulAction.toMulAut ↥(hyp.Sdata.U ⊔ hyp.Sdata.W1) ↥hyp.P with hφ
  have hmod := hfrob.card_range_comp_subtype_modEq_one φ
  have hAcard : Nat.card ↥(hyp.Sdata.W1.subgroupOf (hyp.Sdata.U ⊔ hyp.Sdata.W1)) = hyp.q := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right :
      hyp.Sdata.W1 ≤ hyp.Sdata.U ⊔ hyp.Sdata.W1)).toEquiv, hyp.Sdata_W1_eq, ← hyp.q_eq_card_W1]
  have hφapply : ∀ (a : ↥(hyp.Sdata.U ⊔ hyp.Sdata.W1)) (p : ↥hyp.P),
      ((φ a p : ↥hyp.P) : G) = (a : G) * (p : G) * (a : G)⁻¹ := fun a p => rfl
  have hker_iff : ∀ a : ↥(hyp.Sdata.U ⊔ hyp.Sdata.W1),
      φ a = 1 ↔ (a : G) ∈ Subgroup.centralizer (hyp.P : Set G) := by
    intro a
    rw [Subgroup.mem_centralizer_iff]
    constructor
    · intro h1 p hp
      have hcg := congrArg (fun e : MulAut ↥hyp.P => ((e ⟨p, hp⟩ : ↥hyp.P) : G)) h1
      simp only [hφapply, MulAut.one_apply] at hcg
      exact (mul_inv_eq_iff_eq_mul.mp hcg).symm
    · intro hc
      ext p
      simp only [hφapply, MulAut.one_apply]
      have hpc := hc (p : G) p.2
      rw [← hpc]; group
  set N := hyp.Sdata.U.subgroupOf (hyp.Sdata.U ⊔ hyp.Sdata.W1) with hN
  set ψ : ↥N →* MulAut ↥hyp.P := φ.comp N.subtype with hψ
  set ρ : ↥N →* G := (hyp.Sdata.U ⊔ hyp.Sdata.W1).subtype.comp N.subtype with hρ
  have hρinj : Function.Injective ρ :=
    (hyp.Sdata.U ⊔ hyp.Sdata.W1).subtype_injective.comp N.subtype_injective
  have hkermap : (ψ.ker).map ρ = hyp.C := by
    ext g
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨n, hn, rfl⟩
      rw [MonoidHom.mem_ker, hψ, MonoidHom.comp_apply] at hn
      have hgC : (ρ n : G) ∈ Subgroup.centralizer (hyp.P : Set G) := (hker_iff _).mp hn
      have hgU : (ρ n : G) ∈ hyp.Sdata.U := Subgroup.mem_subgroupOf.mp n.2
      have hgU' : (ρ n : G) ∈ hyp.U := by rw [← hyp.Sdata_U_eq]; exact hgU
      rw [hyp.C_eq]
      exact ⟨hgU', hgC⟩
    · intro hgC
      rw [hyp.C_eq, Subgroup.mem_inf] at hgC
      obtain ⟨hgU, hgc⟩ := hgC
      have hgUS : g ∈ hyp.Sdata.U := by rw [hyp.Sdata_U_eq]; exact hgU
      have hgUW1 : g ∈ hyp.Sdata.U ⊔ hyp.Sdata.W1 :=
        (le_sup_left : hyp.Sdata.U ≤ _) hgUS
      have hgN : (⟨g, hgUW1⟩ : ↥(hyp.Sdata.U ⊔ hyp.Sdata.W1)) ∈ N :=
        Subgroup.mem_subgroupOf.mpr hgUS
      refine ⟨⟨⟨g, hgUW1⟩, hgN⟩, ?_, rfl⟩
      rw [MonoidHom.mem_ker, hψ, MonoidHom.comp_apply]
      exact (hker_iff _).mpr hgc
  have hkercard : Nat.card ↥(ψ.ker) = hyp.c := by
    rw [hyp.c_eq_card_C, ← hkermap]
    exact Nat.card_congr (Subgroup.equivMapOfInjective _ ρ hρinj).toEquiv
  have hNcard : Nat.card ↥N = hyp.u * hyp.c := by
    rw [hN, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_left :
      hyp.Sdata.U ≤ hyp.Sdata.U ⊔ hyp.Sdata.W1)).toEquiv, hyp.Sdata_U_eq, hyp.card_U_eq_uc]
  have hrangecard : Nat.card ↥(ψ.range) = hyp.u := by
    have hsplit := Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv, hkercard, hNcard] at hsplit
    have hc0 : 0 < hyp.c := hyp.c_eq_card_C ▸ Nat.card_pos
    exact (Nat.eq_of_mul_eq_mul_right hc0 hsplit).symm
  have hru : Nat.card ↥((φ.comp N.subtype).range) = hyp.u := hrangecard
  rw [hru, hAcard] at hmod
  exact hmod

/-- **Peterfalvi (13.3.c), the `S`-side signs are `1`**: `δ_j = 1` for `j ≥ 1`.  The (4.3.d)
congruence `μ_{0j}(1) = δ_j + q·a` (`mu_degree_modEq_delta`) with `μ_{0j}(1) = u`
(`mu_apply_one_eq_u`) and `u ≡ 1 (mod q)` (`u_modEq_one`) gives `q ∣ δ_j − 1`; since `δ_j = ±1`
(`delta_pm_one`) and `q ≥ 3`, `δ_j = -1` would force `q ∣ 2`, so `δ_j = 1`. -/
theorem Hypothesis.delta_eq_one_of_ne_zero [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (j : Fin hyp.p) (hj : j ≠ ⟨0, hyp.p_prime.pos⟩) :
    hyp.delta j = 1 := by
  obtain ⟨a, ha⟩ := hyp.mu_degree_modEq_delta ⟨0, hyp.q_prime.pos⟩ j
  rw [hyp.mu_apply_one_eq_u hG ⟨0, hyp.q_prime.pos⟩ j hj] at ha
  have haZ : (hyp.u : ℤ) = hyp.delta j + (hyp.q : ℤ) * a := by exact_mod_cast ha
  have hqu : (hyp.q : ℤ) ∣ (hyp.u : ℤ) - 1 := by
    have h := (Nat.modEq_iff_dvd.mp (hyp.u_modEq_one hG))
    simpa using (dvd_neg.mpr h)
  have hqδ : (hyp.q : ℤ) ∣ hyp.delta j - 1 := by
    have hsub : hyp.delta j - 1 = ((hyp.u : ℤ) - 1) - (hyp.q : ℤ) * a := by
      rw [haZ]; ring
    rw [hsub]
    exact dvd_sub hqu (Dvd.intro a rfl)
  rcases hyp.delta_pm_one.1 j with h1 | hm1
  · exact h1
  · exfalso
    rw [hm1] at hqδ
    have hq2 : (hyp.q : ℤ) ∣ 2 := dvd_neg.mp (by simpa using hqδ)
    have hqle : hyp.q ≤ 2 := Nat.le_of_dvd (by norm_num) (by exact_mod_cast hq2)
    have h2le := hyp.q_prime.two_le
    have hodd := Nat.odd_iff.mp hyp.q_odd
    omega

/-- **Peterfalvi (13.3.c), the `S`-side signs are all `1`**: `δ_j = 1` for every `j`.  The
base `δ_0 = 1` is the (4.4) trivial-column anchor (`delta_zero_eq_one`); for `j ≥ 1` it is
`delta_eq_one_of_ne_zero` (the `u ≡ 1 (mod q)` route).  This supplies the `S`-side
`CharacterDegreeCore.delta_eq_one` field directly. -/
theorem Hypothesis.delta_eq_one_S [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (j : Fin hyp.p) : hyp.delta j = 1 := by
  by_cases hj : j = ⟨0, hyp.p_prime.pos⟩
  · rw [hj]; exact hyp.delta_zero_eq_one
  · exact hyp.delta_eq_one_of_ne_zero hG j hj

/-- `|T| = |T'|·p` — the `T`-side mirror of `card_S_eq_deriv_mul_q`
(`M_complement` of the reconciled type-`P` datum + `|W₂| = p`). -/
theorem Hypothesis.card_T_eq_deriv_mul_p [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    Nat.card ↥hyp.T = Nat.card ↥(derivedInG hyp.T) * hyp.p := by
  obtain ⟨tpd, -, hW1, -⟩ := reconciled_typePData_T hG hyp
  have hle : derivedInG hyp.T ≤ hyp.T := Subgroup.map_subtype_le _
  have h := tpd.M_complement.card_mul_card
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe tpd.W1_le).toEquiv,
    hW1, ← hyp.p_eq_card_W2] at h
  exact h.symm

/-- **`T` normalizes `Q^#`** — the `T`-side mirror of `S_normalizes_H_sharp`, via
`normalizer_Q_eq_T`. -/
theorem T_normalizes_Q_sharp [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    ∀ (l : hyp.T) ⦃a : G⦄, a ∈ OddOrder.Peterfalvi.S04.sharp (hyp.Q : Set G) →
      (l : G) * a * (l : G)⁻¹ ∈ OddOrder.Peterfalvi.S04.sharp (hyp.Q : Set G) := by
  have hnorm : Subgroup.normalizer (hyp.Q : Set G) = hyp.T := normalizer_Q_eq_T hG hyp
  intro l a ha
  rw [OddOrder.Peterfalvi.S04.mem_sharp] at ha ⊢
  obtain ⟨haQ, ha1⟩ := ha
  have hlnorm : (l : G) ∈ Subgroup.normalizer (hyp.Q : Set G) := by
    rw [hnorm]; exact l.2
  refine ⟨(Subgroup.mem_set_normalizer_iff.mp hlnorm a).mp haQ, ?_⟩
  intro heq
  refine ha1 ?_
  calc a = (l : G)⁻¹ * ((l : G) * a * (l : G)⁻¹) * (l : G) := by group
    _ = 1 := by rw [heq]; group

/-- **The (13.8)-for-`T` Dade hypothesis for the TI-subset `(T, Q^#)`** — the `T`-side mirror of
`H_sharp_dadeHypothesis`, from the proven `Q_sharp_isTISubset` (type V excluded by `vd ≠ 1`).
The foundation of the `T`-side (13.5) ρ-machinery consumed by `exists_caseB_data_eta10_T`. -/
noncomputable def Q_sharp_dadeHypothesis [Fintype G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (hvd : hyp.v * hyp.d ≠ 1) :
    OddOrder.Peterfalvi.S04.Hypothesis G (OddOrder.Peterfalvi.S04.sharp (hyp.Q : Set G)) hyp.T := by
  have hQT : hyp.Q ≤ hyp.T := by
    rw [hyp.Q_eq_TF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le hyp.T
  refine OddOrder.Peterfalvi.S04.Hypothesis.of_isTISubset ?_ ?_ (T_normalizes_Q_sharp hG hyp)
    (Q_sharp_isTISubset hG hyp hvd)
  · intro x hx
    exact OddOrder.Peterfalvi.S04.mem_sharp.mpr
      ⟨Set.mem_univ x, (OddOrder.Peterfalvi.S04.mem_sharp.mp hx).2⟩
  · intro x hx
    exact hQT (OddOrder.Peterfalvi.S04.mem_sharp.mp hx).1

open scoped OddOrder.Peterfalvi.S15.FiniteInduce in
/-- The (7.1) ρ-hypothesis for `(T, Q^#)` — mirror of `H_sharp_hypothesis71`. -/
noncomputable def Q_sharp_hypothesis71 [Fintype G] [Invertible (Nat.card G : ℂ)]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (hvd : hyp.v * hyp.d ≠ 1) :
    OddOrder.Peterfalvi.S09.Hypothesis71 G (OddOrder.Peterfalvi.S04.sharp (hyp.Q : Set G)) hyp.T :=
  { hyp := Q_sharp_dadeHypothesis hG hyp hvd
    τ := ((Q_sharp_dadeHypothesis hG hyp hvd).fullDadeIsometryData).toDadeIsometryData.toDadeMap
    isDadeMap := ((Q_sharp_dadeHypothesis hG hyp
        hvd).fullDadeIsometryData).toDadeIsometryData.isDadeMap }

/-- `|T'| = |Q|·(vd)` — the `T`-side derived-subgroup order decomposition
(`derived_complement` of the reconciled type-`P` datum). -/
theorem Hypothesis.card_deriv_T_eq [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    Nat.card ↥(derivedInG hyp.T) = Nat.card ↥hyp.Q * (hyp.v * hyp.d) := by
  obtain ⟨tpd, hU, -, -⟩ := reconciled_typePData_T hG hyp
  have h2 := tpd.derived_complement.card_mul_card
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe tpd.H_le).toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe tpd.U_le).toEquiv, tpd.H_eq, ← hyp.Q_eq_TF,
    hU, hyp.card_V_eq_vd] at h2
  exact h2.symm

end CountingLayer

end OddOrder.Peterfalvi.S15


