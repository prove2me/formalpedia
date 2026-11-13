-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S15_SAndT_Setup_TSideDegrees
-- name    : OddOrder_Peterfalvi_S15_SAndT_Setup_TSideDegrees
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T15:53:30.985918+00:00
-- url     : https://prove2.me/theorems/9971becb-3d45-4c6c-ab34-e237896eb02f
-- title:
--   Peterfalvi (13.3.a,c): $T$-side degree arithmetic
-- statement:
--   Formalizes the $T$-side mirrors of the $S$-side (13.3) degree and counting layer (Peterfalvi, pp. 76-77), giving the $\delta'$-half of (13.3.c) and the $\nu$-row degree facts.
--
--   Main declarations: `Hypothesis.toTypesIIIIIIVSetupT_cSub_eq_D` (`C_V(Q̄) = D`); `Hypothesis.nu_apply_one_row_const` (Row-constant degree); `Hypothesis.nu_rowSum_not_irreducible` (The `ν`-row sums are reducible); `Hypothesis.nu_rowSum_mem_sOf_H0_T` (The `ν`-row sums lie in the §9-on-`T` family `𝒮_T(H₀)`).
--
--   The bundle also proves 14 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S15_SAndT_Setup/TSideDegrees.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S15_SAndT_Setup/TSideDegrees.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S13_CoreStructure
import Definitions.Def_OddOrder_Peterfalvi_S13_NonGaloisExclusion
import Definitions.Def_OddOrder_Peterfalvi_S13_TypeDetermination
import Definitions.Def_OddOrder_Peterfalvi_S15_SAndT_Setup_CountingLayer
import Definitions.Def_OddOrder_Peterfalvi_S15_SAndT_Setup_HypothesisSwap

namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

variable {G : Type*} [Group G]

/-- `K = QD ≤ T`: `Q = T_F ≤ T` and `D = V ∩ C_G(Q) ≤ V ≤ T' ≤ T`.  Mirror of `H_le_S`. -/
theorem Hypothesis.K_le_T [Finite G] (hyp : Hypothesis (G := G)) : hyp.K ≤ hyp.T := by
  have hVT : hyp.V ≤ hyp.T := by
    have h1 : hyp.V ≤ derivedInG hyp.T := by rw [hyp.T_deriv_eq_QV]; exact le_sup_right
    exact le_trans h1 (Subgroup.map_subtype_le _)
  have hQT : hyp.Q ≤ hyp.T := by
    rw [hyp.Q_eq_TF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le hyp.T
  exact sup_le hQT (le_trans (hyp.D_eq ▸ inf_le_left) hVT)

/-- **`|K| = |Q|·d`** (Peterfalvi (13.2), `T`-side): `K = QD` with `Q ⊓ D = ⊥` (`D ≤ V` and
`Q ⊓ V = ⊥`) and `Q ◁ K`.  Mirror of `card_H_eq` — but *without* evaluating `|Q|`
(the type-uniform `S`-side evaluation and its `T`-analogue are separate results, while the
downstream index `[T:K] = v·p` cancels `|Q|` anyway). -/
theorem Hypothesis.card_K_val [Finite G] (hyp : Hypothesis (G := G)) :
    Nat.card ↥hyp.K = Nat.card ↥hyp.Q * hyp.d := by
  have := hyp.finiteG
  have hQK : hyp.Q ≤ hyp.K := le_sup_left
  have hDK : hyp.D ≤ hyp.K := le_sup_right
  have hK_le_T : hyp.K ≤ hyp.T := hyp.K_le_T
  have hT_le_NQ : hyp.T ≤ Subgroup.normalizer hyp.Q := by
    rw [hyp.Q_eq_TF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer hyp.T
  have hQn : (hyp.Q.subgroupOf hyp.K).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQK).mpr (hK_le_T.trans hT_le_NQ)
  have hinf : hyp.Q.subgroupOf hyp.K ⊓ hyp.D.subgroupOf hyp.K = ⊥ := by
    ext ⟨x, hx⟩
    simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf, Subgroup.mem_bot, Subtype.ext_iff,
      OneMemClass.coe_one]
    refine ⟨fun ⟨hxQ, hxD⟩ => ?_, fun h => by simp [h]⟩
    have hxQV : x ∈ (hyp.Q ⊓ hyp.V : Subgroup G) :=
      ⟨hxQ, (hyp.D_eq ▸ inf_le_left : hyp.D ≤ hyp.V) hxD⟩
    rwa [hyp.Q_inf_V_eq_bot, Subgroup.mem_bot] at hxQV
  have hsup : hyp.Q.subgroupOf hyp.K ⊔ hyp.D.subgroupOf hyp.K = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hQK hDK]
    exact Subgroup.subgroupOf_self hyp.K
  have hcompl : Subgroup.IsComplement' (hyp.Q.subgroupOf hyp.K) (hyp.D.subgroupOf hyp.K) :=
    Subgroup.isComplement'_of_disjoint_and_mul_eq_univ (disjoint_iff.mpr hinf)
      (by rw [← Subgroup.normal_mul, hsup, Subgroup.coe_top])
  have hmul := hcompl.card_mul_card
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQK).toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDK).toEquiv, ← hyp.d_eq_card_D] at hmul
  exact hmul.symm

/-- **`[T : K] = v·p`** (Peterfalvi (13.2), `T`-side): the index of `K = QD` in `T`.  From
`|T| = |Q|·(v·d)·p` (`card_T_eq_deriv_mul_p` + `card_deriv_T_eq` + `card_V_eq_vd`) and
`|K| = |Q|·d` (`card_K_val`) — the Fitting order `|Q|` cancels.  Mirror of `H_index_eq_uq`;
the degree index of the (13.3.a)-at-`T` `ν_i = Ind_{QD}^T (linear)`. -/
theorem Hypothesis.K_index_eq_vp [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    (hyp.K.subgroupOf hyp.T).index = hyp.v * hyp.p := by
  have hm := Subgroup.card_mul_index (hyp.K.subgroupOf hyp.T)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hyp.K_le_T).toEquiv, hyp.card_K_val,
    hyp.card_T_eq_deriv_mul_p hG, hyp.card_deriv_T_eq hG] at hm
  have hpos : (0 : ℕ) < Nat.card ↥hyp.Q * hyp.d :=
    Nat.mul_pos Nat.card_pos (hyp.d_eq_card_D ▸ Nat.card_pos)
  have hmm : Nat.card ↥hyp.Q * hyp.d * (hyp.K.subgroupOf hyp.T).index
      = Nat.card ↥hyp.Q * hyp.d * (hyp.v * hyp.p) := by rw [hm]; ring
  exact Nat.eq_of_mul_eq_mul_left hpos hmm

/-- **`v·d = |V| ≠ 1`**: `T` is type non-I; a type-II/III/IV witness has a nontrivial
complement whose order is `|V|` (witness-independence `card_U_eq_index`), and type V is
excluded unconditionally by Peterfalvi Theorem (10.10) (`no_typeV_maximal_unconditional`).
This discharges the `hvd` nontriviality input of `toTypesIIIIIIVSetupT` with no extra
hypothesis. -/
theorem Hypothesis.vd_ne_one [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) : hyp.v * hyp.d ≠ 1 := by
  intro h1
  obtain ⟨tpd, hU, -, -⟩ := reconciled_typePData_T hG hyp
  rcases hyp.T_nonI with h | h | h | h
  · obtain ⟨w⟩ := h
    have hc : Nat.card ↥tpd.U = Nat.card ↥w.typeP.U := by
      rw [tpd.card_U_eq_index, w.typeP.card_U_eq_index]
    rw [hU, hyp.card_V_eq_vd, h1] at hc
    exact w.common.1 (Subgroup.card_eq_one.mp hc.symm)
  · obtain ⟨w⟩ := h
    have hc : Nat.card ↥tpd.U = Nat.card ↥w.typeP.U := by
      rw [tpd.card_U_eq_index, w.typeP.card_U_eq_index]
    rw [hU, hyp.card_V_eq_vd, h1] at hc
    exact w.common.1 (Subgroup.card_eq_one.mp hc.symm)
  · obtain ⟨w⟩ := h
    have hc : Nat.card ↥tpd.U = Nat.card ↥w.typeP.U := by
      rw [tpd.card_U_eq_index, w.typeP.card_U_eq_index]
    rw [hU, hyp.card_V_eq_vd, h1] at hc
    exact w.common.1 (Subgroup.card_eq_one.mp hc.symm)
  · exact OddOrder.Peterfalvi.S12.no_typeV_maximal_unconditional hG
      ⟨hyp.T, hyp.T_maximal, h⟩

/-- **Peterfalvi `v ≡ 1 (mod p)`** (the (13.3.c) `δ'`-crux): the `T`-side `V W₂` is a
Frobenius group (`typeP_uW1_frobenius` on the reconciled type-`P` datum of `T`), so for the
conjugation homomorphism `φ : V W₂ →* Aut(Q)` the kernel-image `φ(V) = V/C_V(Q) = V̄`
satisfies `|V̄| ≡ 1 (mod |W₂|)` (`IsFrobeniusGroup.card_range_comp_subtype_modEq_one`,
Isaacs Lemma 6.1); with `|V| = v·d` (`card_V_eq_vd`, `D = V ⊓ C_G(Q)`) and `|W₂| = p` this
is `v ≡ 1 (mod p)`.  Mirror of `u_modEq_one`; crucially **ungated** — uses only the
reconciled `V W₂` Frobenius structure, with nontriviality from `vd_ne_one`. -/
theorem Hypothesis.v_modEq_one [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) : hyp.v ≡ 1 [MOD hyp.p] := by
  have := hyp.finiteG
  obtain ⟨tpd, hU, hW1, -⟩ := reconciled_typePData_T hG hyp
  have hUne : tpd.U ≠ ⊥ := by
    intro hbot
    apply hyp.vd_ne_one hG
    rw [← hyp.card_V_eq_vd, ← hU, hbot, Subgroup.card_bot]
  have hfrob := OddOrder.Peterfalvi.S11.typeP_uW1_frobenius tpd hUne
  have hUW1leT : tpd.U ⊔ tpd.W1 ≤ hyp.T :=
    sup_le (tpd.U_le.trans (Subgroup.map_subtype_le _)) tpd.W1_le
  have hTnormQ : hyp.T ≤ Subgroup.normalizer hyp.Q := by
    rw [hyp.Q_eq_TF]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer hyp.T
  have hUW1normQ : tpd.U ⊔ tpd.W1 ≤ Subgroup.normalizer hyp.Q :=
    le_trans hUW1leT hTnormQ
  let : MulDistribMulAction ↥(tpd.U ⊔ tpd.W1) ↥hyp.Q :=
    MulDistribMulAction.compHom (M := ↥(Subgroup.normalizer hyp.Q)) ↥hyp.Q
      (Subgroup.inclusion hUW1normQ)
  set φ : ↥(tpd.U ⊔ tpd.W1) →* MulAut ↥hyp.Q :=
    MulDistribMulAction.toMulAut ↥(tpd.U ⊔ tpd.W1) ↥hyp.Q with hφ
  have hmod := hfrob.card_range_comp_subtype_modEq_one φ
  have hAcard : Nat.card ↥(tpd.W1.subgroupOf (tpd.U ⊔ tpd.W1)) = hyp.p := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right :
      tpd.W1 ≤ tpd.U ⊔ tpd.W1)).toEquiv, hW1, ← hyp.p_eq_card_W2]
  have hφapply : ∀ (a : ↥(tpd.U ⊔ tpd.W1)) (x : ↥hyp.Q),
      ((φ a x : ↥hyp.Q) : G) = (a : G) * (x : G) * (a : G)⁻¹ := fun a x => rfl
  have hker_iff : ∀ a : ↥(tpd.U ⊔ tpd.W1),
      φ a = 1 ↔ (a : G) ∈ Subgroup.centralizer (hyp.Q : Set G) := by
    intro a
    rw [Subgroup.mem_centralizer_iff]
    constructor
    · intro h1 x hx
      have hcg := congrArg (fun e : MulAut ↥hyp.Q => ((e ⟨x, hx⟩ : ↥hyp.Q) : G)) h1
      simp only [hφapply, MulAut.one_apply] at hcg
      exact (mul_inv_eq_iff_eq_mul.mp hcg).symm
    · intro hc
      ext x
      simp only [hφapply, MulAut.one_apply]
      have hxc := hc (x : G) x.2
      rw [← hxc]; group
  set N := tpd.U.subgroupOf (tpd.U ⊔ tpd.W1) with hN
  set ψ : ↥N →* MulAut ↥hyp.Q := φ.comp N.subtype with hψ
  set ρ : ↥N →* G := (tpd.U ⊔ tpd.W1).subtype.comp N.subtype with hρ
  have hρinj : Function.Injective ρ :=
    (tpd.U ⊔ tpd.W1).subtype_injective.comp N.subtype_injective
  have hkermap : (ψ.ker).map ρ = hyp.D := by
    ext g
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨n, hn, rfl⟩
      rw [MonoidHom.mem_ker, hψ, MonoidHom.comp_apply] at hn
      have hgC : (ρ n : G) ∈ Subgroup.centralizer (hyp.Q : Set G) := (hker_iff _).mp hn
      have hgU : (ρ n : G) ∈ tpd.U := Subgroup.mem_subgroupOf.mp n.2
      have hgV : (ρ n : G) ∈ hyp.V := by rw [← hU]; exact hgU
      rw [hyp.D_eq]
      exact ⟨hgV, hgC⟩
    · intro hgD
      rw [hyp.D_eq, Subgroup.mem_inf] at hgD
      obtain ⟨hgV, hgc⟩ := hgD
      have hgUd : g ∈ tpd.U := by rw [hU]; exact hgV
      have hgUW1 : g ∈ tpd.U ⊔ tpd.W1 := (le_sup_left : tpd.U ≤ _) hgUd
      have hgN : (⟨g, hgUW1⟩ : ↥(tpd.U ⊔ tpd.W1)) ∈ N :=
        Subgroup.mem_subgroupOf.mpr hgUd
      refine ⟨⟨⟨g, hgUW1⟩, hgN⟩, ?_, rfl⟩
      rw [MonoidHom.mem_ker, hψ, MonoidHom.comp_apply]
      exact (hker_iff _).mpr hgc
  have hkercard : Nat.card ↥(ψ.ker) = hyp.d := by
    rw [hyp.d_eq_card_D, ← hkermap]
    exact Nat.card_congr (Subgroup.equivMapOfInjective _ ρ hρinj).toEquiv
  have hNcard : Nat.card ↥N = hyp.v * hyp.d := by
    rw [hN, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_left :
      tpd.U ≤ tpd.U ⊔ tpd.W1)).toEquiv, hU, hyp.card_V_eq_vd]
  have hrangecard : Nat.card ↥(ψ.range) = hyp.v := by
    have hsplit := Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv, hkercard, hNcard] at hsplit
    have hd0 : 0 < hyp.d := hyp.d_eq_card_D ▸ Nat.card_pos
    exact (Nat.eq_of_mul_eq_mul_right hd0 hsplit).symm
  have hrv : Nat.card ↥((φ.comp N.subtype).range) = hyp.v := hrangecard
  rw [hrv, hAcard] at hmod
  exact hmod

/-- **Peterfalvi (13.2.b) at `T`, order part — unconditional**: `|Q| = |T_F| = q^p`.

The `T`-analogue of `card_P_eq` with **no type-II carrier**: the four `T_nonI` branches are
each closed —

* **type II**: the (9.3) Wielandt order relation (`typeII_III_IV_order_relations`, first
  clause) on the reconciled type-`P` datum, exactly as `card_Q_eq` (S15_Gate3) runs it from
  the (14.9) `IsTypeII T` — here the branch hypothesis supplies it directly;
* **types III/IV**: the §11 chain — Peterfalvi (11.7) `|H| = p^q` is **proven
  unconditionally** for type-III/IV maximals (`card_H_eq_of_base` +
  `S_H0C_not_coherent_unconditional`, the honest (11.3)-on-(10.8) route), and the local
  `w₁`/`w₂` reconcile to the abstract `p`/`q` via the derived index
  (`card_W1_eq_derived_index` + `W2_isComplement_T_deriv`) and the κ-Hall dual-factor bridge
  (`card_Msigma_inf_centralizer_eq_card_W2` + `W1_eq_Msigma_T_inf_centralizer_W2`);
* **type V**: excluded by the unconditional Theorem (10.10)
  (`no_typeV_maximal_unconditional`).

This is exactly Peterfalvi's "(13.2.b) holds for `T` as well as `S`" ((13.1) makes `S` and
`T` play the same role): both sides now run the honest type-II/type-III classification.  It
un-gates the §9-on-`T` chief-kernel triviality (the
`nu_apply_one_eq_v` gate). -/
theorem Hypothesis.card_Q_eq_qp [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) :
    Nat.card ↥hyp.Q = hyp.q ^ hyp.p := by
  have := hyp.finiteG
  obtain ⟨tpd, hU, htpdW1, htpdW2⟩ := reconciled_typePData_T hG hyp
  have hW2T : hyp.W2 ≤ hyp.T :=
    (by rw [hyp.W_eq_join]; exact le_sup_right : hyp.W2 ≤ hyp.W).trans
      (by rw [hyp.W_eq_inter]; exact inf_le_right)
  -- The type-III/IV branch, shared by both disjuncts.
  have hIIIIV : (IsTypeIII hyp.T ∨ IsTypeIV hyp.T) → Nat.card ↥hyp.Q = hyp.q ^ hyp.p := by
    intro htype
    obtain ⟨base12⟩ := OddOrder.Peterfalvi.S12.exists_hypothesis_of_typeIIIorIVorV hG
      hyp.T_maximal (htype.imp id Or.inl)
    have hcard := OddOrder.Peterfalvi.S13.card_H_eq_of_base hG base12 htype
      (fun s13 => OddOrder.Peterfalvi.S13.S_H0C_not_coherent_unconditional hG s13)
    -- `base12.typeP.H = Q` (`H = M_F` is intrinsic)
    have hHQ : base12.typeP.H = hyp.Q := by rw [base12.typeP.H_eq, hyp.Q_eq_TF]
    -- `w₁ = p`: both `typeP.W1` and `W₂` complement `T'` in `T`, so both have the derived index
    have hw1 : base12.w1 = hyp.p := by
      change Nat.card ↥base12.typeP.W1 = hyp.p
      rw [base12.typeP.card_W1_eq_derived_index,
        hyp.W2_isComplement_T_deriv.symm.index_eq_card,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW2T).toEquiv, ← hyp.p_eq_card_W2]
    -- `w₂ = q`: the dual-factor bridge `|M_σ(T) ⊓ C(W₂)| = |typeP.W2|` against
    -- `W₁ = M_σ(T) ⊓ C(W₂)`
    have hw2 : base12.w2 = hyp.q := by
      change Nat.card ↥base12.typeP.W2 = hyp.q
      have : IsCyclic ↥hyp.W2 := by
        have := hyp.W_cyclic
        exact isCyclic_of_surjective _ (Subgroup.subgroupOfEquivOfLe
          (by rw [hyp.W_eq_join]; exact le_sup_right : hyp.W2 ≤ hyp.W)).surjective
      have hbridge := OddOrder.Peterfalvi.S10.card_Msigma_inf_centralizer_eq_card_W2 hG
        hyp.T_maximal (OddOrder.BG.Ch4.S16.isTypeP_of_isTypeNonI hG hyp.T_maximal hyp.T_nonI)
        hW2T (hyp.W2_isKappaHall_T hG) base12.typeP
      rw [← hbridge, ← hyp.W1_eq_Msigma_T_inf_centralizer_W2 hG, ← hyp.q_eq_card_W1]
    rw [hHQ, hw1, hw2] at hcard
    exact hcard
  rcases hyp.T_nonI with h | h | h | h
  · -- **type II**: the (9.3) Wielandt order relation on the reconciled datum.
    have w := h.some
    have hUne : tpd.U ≠ ⊥ := by
      intro hbot
      have h1 : Nat.card ↥tpd.U = Nat.card ↥w.typeP.U := by
        rw [tpd.card_U_eq_index, w.typeP.card_U_eq_index]
      rw [hbot, Subgroup.card_bot] at h1
      exact w.common.1 (Subgroup.card_eq_one.mp h1.symm)
    have hW1prime : (Nat.card ↥tpd.W1).Prime := by
      rw [htpdW1, ← hyp.p_eq_card_W2]; exact hyp.p_prime
    have hord := (OddOrder.Peterfalvi.S11.typeII_III_IV_order_relations hG
      { maximal := hyp.T_maximal
        typeP := tpd
        nontrivial := ⟨hUne, hW1prime, w.common.2.2⟩
        type_alt := Or.inl h }).1 h
    have hord2 : Nat.card ↥tpd.H = Nat.card ↥tpd.W2 ^ Nat.card ↥tpd.W1 := hord.2
    have hW2card : Nat.card ↥tpd.W2 = hyp.q := by
      rw [htpdW2, ← hyp.q_eq_card_W1]
    rw [tpd.H_eq, ← hyp.Q_eq_TF, hW2card, htpdW1, ← hyp.p_eq_card_W2] at hord2
    exact hord2
  · exact hIIIIV (Or.inl h)
  · exact hIIIIV (Or.inr h)
  · exact absurd ⟨hyp.T, hyp.T_maximal, h⟩
      (OddOrder.Peterfalvi.S12.no_typeV_maximal_unconditional hG)

/-- **The `T`-instance chief kernel `N` is trivial**: `Q = T_F` has order `q^p`
(`card_Q_eq_qp`, unconditional), and the chief factor `Q̄ = Q/H₀ ≅ ↥Q ⧸ N` already has order
`(chief.p)^p` (`chiefFactor_quotient_card`), so `chief.p = q` and `|N| = 1`.  Mirror of
`toTypesIIIIIIVSetupS_chief_N_eq_bot`; `card_Q_eq_qp` supplies the `T`-side order through the
same honest type classification used on the `S` side. -/
theorem Hypothesis.toTypesIIIIIIVSetupT_chief_N_eq_bot [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hvd : hyp.v * hyp.d ≠ 1)
    (chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetupT hG hvd)) :
    chief.N = ⊥ := by
  have := chief.N_normal
  have hq : (hyp.toTypesIIIIIIVSetupT hG hvd).q = hyp.p := by
    change Nat.card ↥(hyp.toTypesIIIIIIVSetupT hG hvd).W1 = hyp.p
    rw [hyp.toTypesIIIIIIVSetupT_W1_eq hG hvd, ← hyp.p_eq_card_W2]
  have hcardH : Nat.card ↥(hyp.toTypesIIIIIIVSetupT hG hvd).H = hyp.q ^ hyp.p := by
    rw [show ((hyp.toTypesIIIIIIVSetupT hG hvd).H : Subgroup G) = hyp.Q from
      hyp.toTypesIIIIIIVSetupT_H_eq hG hvd]
    exact hyp.card_Q_eq_qp hG
  have hquot := OddOrder.Peterfalvi.S11.chiefFactor_quotient_card chief
  rw [hq] at hquot
  have hsplit := Subgroup.card_eq_card_quotient_mul_card_subgroup chief.N
  rw [hquot, hcardH] at hsplit
  have hdvd : chief.p ∣ hyp.q ^ hyp.p := by
    refine dvd_trans (dvd_pow_self chief.p hyp.p_prime.pos.ne') ?_
    exact hsplit ▸ Dvd.intro _ rfl
  have hpp : chief.p = hyp.q :=
    (Nat.prime_dvd_prime_iff_eq chief.p_prime hyp.q_prime).mp
      (chief.p_prime.dvd_of_dvd_pow hdvd)
  rw [hpp] at hsplit
  have hN1 : Nat.card ↥chief.N = 1 := by
    have := hsplit.symm
    nlinarith [Nat.card_pos (α := ↥chief.N), pow_pos hyp.q_prime.pos hyp.p]
  exact Subgroup.card_eq_one.mp hN1

/-- **The `T`-instance chief `H₀` is trivial**: `H₀ = N.map subtype = ⊥`.  Mirror of
`toTypesIIIIIIVSetupS_chief_H0_eq_bot`; makes the (13.3.a)-at-`T` kernel condition
`H₀ ⊆ Ker` automatic. -/
theorem Hypothesis.toTypesIIIIIIVSetupT_chief_H0_eq_bot [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hvd : hyp.v * hyp.d ≠ 1)
    (chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetupT hG hvd)) :
    chief.H0 = ⊥ := by
  rw [chief.H0_eq, hyp.toTypesIIIIIIVSetupT_chief_N_eq_bot hG hvd chief]
  exact Subgroup.map_bot _

open OddOrder.Isaacs.Ch03.IsAInvariant (quotientMulAutHom) in
/-- **`C_V(Q̄) = D`** for the `T`-instance: the §9 kernel `cSub` (`= C_V(Q̄)`) equals
Peterfalvi's `D = C_V(Q) = V ⊓ C_G(Q)`.  Mirror of `toTypesIIIIIIVSetupS_cSub_eq_C`, using the
`T`-instance `H₀ = ⊥` (`toTypesIIIIIIVSetupT_chief_H0_eq_bot`).  The last spelling piece of
the (13.3.a)-at-`T` `ν_i = Ind_{QD}(linear)`: `KD-realized = Q·cSub`. -/
theorem Hypothesis.toTypesIIIIIIVSetupT_cSub_eq_D [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hvd : hyp.v * hyp.d ≠ 1)
    (chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetupT hG hvd)) :
    OddOrder.Peterfalvi.S11.cSub (hyp.toTypesIIIIIIVSetupT hG hvd) chief = hyp.D := by
  have := hyp.finiteG
  have := chief.N_normal
  have hUeq : (hyp.toTypesIIIIIIVSetupT hG hvd).U = hyp.V :=
    hyp.toTypesIIIIIIVSetupT_U_eq hG hvd
  have hHeq : ((hyp.toTypesIIIIIIVSetupT hG hvd).H : Subgroup G) = hyp.Q :=
    hyp.toTypesIIIIIIVSetupT_H_eq hG hvd
  apply le_antisymm
  · -- forward: `cSub ≤ V ⊓ C_G(Q)`
    rw [hyp.D_eq]
    intro g hg
    refine Subgroup.mem_inf.mpr
      ⟨hUeq ▸ OddOrder.Peterfalvi.S11.cSub_le_U _ chief hg, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hcomm : ⁅OddOrder.Peterfalvi.S11.cSub (hyp.toTypesIIIIIIVSetupT hG hvd) chief,
        (hyp.toTypesIIIIIIVSetupT hG hvd).H⁆ ≤ ⊥ := by
      rw [← hyp.toTypesIIIIIIVSetupT_chief_H0_eq_bot hG hvd chief]
      exact OddOrder.Peterfalvi.S11.commutator_cSub_H_le_H0 _ chief
    have hxH : x ∈ (hyp.toTypesIIIIIIVSetupT hG hvd).H := hHeq ▸ hx
    have hcm := hcomm (Subgroup.commutator_mem_commutator hg hxH)
    rw [Subgroup.mem_bot, commutatorElement_def] at hcm
    have hxg : g * x * g⁻¹ = x := by
      have h1 : g * x * g⁻¹ * x⁻¹ * x = x := by rw [hcm, one_mul]
      rwa [inv_mul_cancel_right] at h1
    have hgx : g * x = x * g := by
      have h2 : g * x * g⁻¹ * g = x * g := by rw [hxg]
      rwa [inv_mul_cancel_right] at h2
    exact hgx.symm
  · -- reverse: `V ⊓ C_G(Q) ≤ cSub`
    rw [hyp.D_eq]
    intro g hg
    obtain ⟨hgV, hgC⟩ := Subgroup.mem_inf.mp hg
    have hgUdata : g ∈ (hyp.toTypesIIIIIIVSetupT hG hvd).U := hUeq ▸ hgV
    have hgUW1 : g ∈ (hyp.toTypesIIIIIIVSetupT hG hvd).typeP.U ⊔
        (hyp.toTypesIIIIIIVSetupT hG hvd).typeP.W1 :=
      (le_sup_left : (hyp.toTypesIIIIIIVSetupT hG hvd).typeP.U ≤ _) hgUdata
    set bUW1 : ↥((hyp.toTypesIIIIIIVSetupT hG hvd).typeP.U ⊔
        (hyp.toTypesIIIIIIVSetupT hG hvd).typeP.W1) := ⟨g, hgUW1⟩ with hbUW1def
    have hbUW1mem : bUW1 ∈ ((hyp.toTypesIIIIIIVSetupT hG hvd).typeP.U).subgroupOf
        ((hyp.toTypesIIIIIIVSetupT hG hvd).typeP.U ⊔
          (hyp.toTypesIIIIIIVSetupT hG hvd).typeP.W1) :=
      Subgroup.mem_subgroupOf.mpr hgUdata
    have haut : quotientMulAutHom chief.N_aInvariant bUW1 = 1 := by
      ext x
      refine QuotientGroup.induction_on x ?_
      intro y
      rw [OddOrder.Isaacs.Ch03.IsAInvariant.quotientMulAutHom_apply
        chief.N_aInvariant bUW1 y, MulAut.one_apply]
      congr 1
      apply Subtype.ext
      rw [OddOrder.Peterfalvi.S11.typeP_conjAction_apply]
      have hyQ : ((y : G)) ∈ hyp.Q := hHeq ▸ y.2
      have hcy : g * (y : G) = (y : G) * g :=
        (Subgroup.mem_centralizer_iff.mp hgC (y : G) hyQ).symm
      change (bUW1 : G) * (y : G) * (bUW1 : G)⁻¹ = (y : G)
      rw [hbUW1def]
      change g * (y : G) * g⁻¹ = (y : G)
      rw [hcy]; group
    have hbker : (⟨bUW1, hbUW1mem⟩ :
        ↥(((hyp.toTypesIIIIIIVSetupT hG hvd).typeP.U).subgroupOf
          ((hyp.toTypesIIIIIIVSetupT hG hvd).typeP.U ⊔
            (hyp.toTypesIIIIIIVSetupT hG hvd).typeP.W1)))
        ∈ (OddOrder.Peterfalvi.S11.uActionHom (hyp.toTypesIIIIIIVSetupT hG hvd) chief).ker := by
      rw [MonoidHom.mem_ker, OddOrder.Peterfalvi.S11.uActionHom, MonoidHom.comp_apply]
      exact haut
    simp only [OddOrder.Peterfalvi.S11.cSub, Subgroup.mem_map]
    exact ⟨bUW1, ⟨⟨bUW1, hbUW1mem⟩, hbker, rfl⟩, rfl⟩

open scoped FiniteInduce in
/-- **Row-constant degree** (Peterfalvi (13.1.e)/(4.3.c), `T`-side): within a row `i`, all
`ν_{ij}(1)` are equal.  From `nu_definition` at `1`: the LHS `Ind_W^T(ω_{ij} − ω_{i0})(1)` is
`[T:W]·(ω_{ij}(1) − ω_{i0}(1)) = 0` (`omega_apply_one`), so the RHS
`δ'_i·(ν_{ij}(1) − ν_{i0}(1)) = 0`, and `δ'_i = ±1 ≠ 0` (`delta_pm_one.2`).  Mirror of
`mu_apply_one_column_const`. -/
theorem Hypothesis.nu_apply_one_row_const [Finite G] (hyp : Hypothesis (G := G))
    (i : Fin hyp.q) (j : Fin hyp.p) :
    hyp.nu i j (1 : ↥hyp.T) = hyp.nu i ⟨0, hyp.p_prime.pos⟩ (1 : ↥hyp.T) := by
  have := hyp.finiteG
  have hdef := hyp.nu_definition i j
  have h1 := congrArg (fun f : ClassFunction ↥hyp.T ℂ => f (1 : ↥hyp.T)) hdef
  rw [ClassFunction.induce_apply_one] at h1
  have homega0 : (ClassFunction.compHom
      (Subgroup.subgroupOfEquivOfLe ((le_of_eq hyp.W_eq_inter).trans inf_le_right)).toMonoidHom
        (hyp.omega i j - hyp.omega i ⟨0, hyp.p_prime.pos⟩))
      (1 : ↥(hyp.W.subgroupOf hyp.T)) = 0 := by
    rw [ClassFunction.compHom_apply, map_one, ClassFunction.sub_apply,
      hyp.omega_apply_one, hyp.omega_apply_one, sub_self]
  rw [homega0, mul_zero] at h1
  have hδ : (hyp.deltaPrime i : ℂ) ≠ 0 := by
    rcases (hyp.delta_pm_one.2 i) with h | h <;> rw [h] <;> norm_num
  have hsub : hyp.nu i j (1 : ↥hyp.T) - hyp.nu i ⟨0, hyp.p_prime.pos⟩ (1 : ↥hyp.T) = 0 :=
    (mul_eq_zero.mp h1.symm).resolve_left hδ
  exact sub_eq_zero.mp hsub

open scoped Classical in
/-- **The `ν`-row sums are reducible** ((13.3.a)-at-`T` entry condition): `ν_i = ∑_j ν_{ij}`
is a sum of `p ≥ 2` *distinct* irreducible characters (`nu_irreducible`,
`nu_row_injective`), so its norm is `p ≠ 1`.  Mirror of `mu_colSum_not_irreducible`,
parametric in the ν-grid supply. -/
theorem Hypothesis.nu_rowSum_not_irreducible [Finite G] (hyp : Hypothesis (G := G))
    (pins : NuGridSupplyData hyp) (i : Fin hyp.q) :
    ¬ OddOrder.RepresentationTheory.IsIrreducibleCharacter (∑ j : Fin hyp.p, hyp.nu i j) := by
  classical
  have := hyp.finiteG
  let : Fintype ↥hyp.T := Fintype.ofFinite _
  let : Invertible (Nat.card ↥hyp.T : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  intro hirr
  set a : Fin hyp.p → OddOrder.RepresentationTheory.IrreducibleCharacter ↥hyp.T :=
    fun j => ⟨hyp.nu i j, pins.nu_irreducible i j⟩ with ha
  have hcond : ∀ j j' : Fin hyp.p, a j = a j' ↔ j = j' := by
    intro j j'
    constructor
    · intro h
      exact pins.nu_row_injective i (congrArg
        (fun χ : OddOrder.RepresentationTheory.IrreducibleCharacter ↥hyp.T =>
          (χ : ClassFunction ↥hyp.T ℂ)) h)
    · rintro rfl
      rfl
  have hinner : ClassFunction.inner (∑ j : Fin hyp.p, hyp.nu i j)
      (∑ j : Fin hyp.p, hyp.nu i j) = (hyp.p : ℂ) := by
    rw [OddOrder.RepresentationTheory.inner_sum_left]
    calc ∑ j : Fin hyp.p, ClassFunction.inner (hyp.nu i j) (∑ j' : Fin hyp.p, hyp.nu i j')
        = ∑ j : Fin hyp.p, ∑ j' : Fin hyp.p, ClassFunction.inner (hyp.nu i j) (hyp.nu i j') := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [OddOrder.RepresentationTheory.inner_sum_right]
      _ = ∑ j : Fin hyp.p, ∑ j' : Fin hyp.p, if j = j' then (1 : ℂ) else 0 := by
          refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun j' _ => ?_
          rw [pins.nu_orthonormal i i j j']
          exact if_congr (by simp) rfl rfl
      _ = ∑ _j : Fin hyp.p, (1 : ℂ) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          simp
      _ = (hyp.p : ℂ) := by simp
  have h1 : ClassFunction.inner (∑ j : Fin hyp.p, hyp.nu i j)
      (∑ j : Fin hyp.p, hyp.nu i j) = 1 := by
    have hite := OddOrder.RepresentationTheory.irreducibleCharacter_inner_eq_ite
      (⟨∑ j : Fin hyp.p, hyp.nu i j, hirr⟩ :
        OddOrder.RepresentationTheory.IrreducibleCharacter ↥hyp.T)
      (⟨∑ j : Fin hyp.p, hyp.nu i j, hirr⟩ :
        OddOrder.RepresentationTheory.IrreducibleCharacter ↥hyp.T)
    simpa using hite
  rw [hinner] at h1
  have : hyp.p = 1 := by exact_mod_cast h1
  exact hyp.p_prime.one_lt.ne' this

open scoped FiniteInduce in
/-- **The `ν`-row sums lie in the §9-on-`T` family `𝒮_T(H₀)`** ((13.3.a)-at-`T` membership):
`ν_i = ∑_j ν_{ij} = Ind_{T'}^T ψ` with `ψ` irreducible not containing `W₁` in its kernel
(`nu_rowSum_eq_induce`), `Q ⊄ Ker` via `W₁ ≤ Q` (the reconciled pairing residual), and
`H₀ = ⊥ ⊆ Ker` (`toTypesIIIIIIVSetupT_chief_H0_eq_bot`).  Mirror of
`mu_colSum_mem_sOf_H0`. -/
theorem Hypothesis.nu_rowSum_mem_sOf_H0_T [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (pins : NuGridSupplyData hyp) (hvd : hyp.v * hyp.d ≠ 1)
    (chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetupT hG hvd))
    (i : Fin hyp.q) (hi : i ≠ ⟨0, hyp.q_prime.pos⟩) :
    (∑ j : Fin hyp.p, hyp.nu i j)
      ∈ OddOrder.Peterfalvi.S11.sOf (hyp.toTypesIIIIIIVSetupT hG hvd) chief.H0 := by
  classical
  have := hyp.finiteG
  let : Fintype ↥hyp.T := Fintype.ofFinite _
  let : Fintype ↥(OddOrder.Peterfalvi.S11.huSub (hyp.toTypesIIIIIIVSetupT hG hvd)) :=
    Fintype.ofFinite _
  let : Fintype ↥((derivedInG hyp.T).subgroupOf hyp.T) := Fintype.ofFinite _
  let : Invertible
      (Nat.card ↥(OddOrder.Peterfalvi.S11.huSub (hyp.toTypesIIIIIIVSetupT hG hvd)) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  let : Invertible (Nat.card ↥((derivedInG hyp.T).subgroupOf hyp.T) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  -- `W₁ ≤ Q` (the reconciled pairing residual, first component)
  have hW1Q : hyp.W1 ≤ hyp.Q :=
    ((hyp.reconciled_residuals_of_pairing_facts hG (hyp.W2_isKappaHall_T hG)
      (hyp.W1_eq_Msigma_T_inf_centralizer_W2 hG)).1).trans inf_le_left
  obtain ⟨ψ, hψirr, hψeq, hψker⟩ := pins.nu_rowSum_eq_induce i
  have hKeq : OddOrder.Peterfalvi.S11.huSub (hyp.toTypesIIIIIIVSetupT hG hvd)
      = (derivedInG hyp.T).subgroupOf hyp.T :=
    OddOrder.Peterfalvi.S11.huSub_eq_derivedInG_subgroupOf _
  set χ : ClassFunction
      ↥(OddOrder.Peterfalvi.S11.huSub (hyp.toTypesIIIIIIVSetupT hG hvd)) ℂ :=
    ClassFunction.compHom (MulEquiv.subgroupCongr hKeq).toMonoidHom ψ with hχdef
  have hχirr : OddOrder.RepresentationTheory.IsIrreducibleCharacter χ :=
    OddOrder.RepresentationTheory.IsIrreducibleCharacter.compHom_of_surjective
      (MulEquiv.subgroupCongr hKeq).surjective hψirr
  rw [OddOrder.Peterfalvi.S11.mem_sOf]
  refine ⟨⟨χ, hχirr⟩, ?_, ?_⟩
  · rw [OddOrder.Peterfalvi.S11.mem_xiOf]
    constructor
    · -- `H ⊄ Ker χ`: a kernel containment would violate the `W₁`-nonkernel conjunct
      intro hsub
      apply hψker hi
      intro c hc
      have hcW1 : ((c : ↥hyp.T) : G) ∈ hyp.W1 :=
        Subgroup.mem_subgroupOf.mp (Subgroup.mem_subgroupOf.mp (SetLike.mem_coe.mp hc))
      set x : ↥(OddOrder.Peterfalvi.S11.huSub (hyp.toTypesIIIIIIVSetupT hG hvd)) :=
        (MulEquiv.subgroupCongr hKeq).symm c with hxdef
      have hxval : ((x : ↥hyp.T) : G) = ((c : ↥hyp.T) : G) := by
        rw [hxdef]
        exact congrArg Subtype.val (MulEquiv.subgroupCongr_symm_apply hKeq c)
      have hxhInHu : x ∈ OddOrder.Peterfalvi.S11.hInHu (hyp.toTypesIIIIIIVSetupT hG hvd) := by
        refine Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mpr ?_)
        show ((x : ↥hyp.T) : G) ∈ ((hyp.toTypesIIIIIIVSetupT hG hvd).H : Subgroup G)
        rw [hxval, hyp.toTypesIIIIIIVSetupT_H_eq hG hvd]
        exact hW1Q hcW1
      have hxker := hsub (SetLike.mem_coe.mpr hxhInHu)
      rw [OddOrder.Peterfalvi.S03.mem_characterKernel,
        OddOrder.Peterfalvi.S03.characterDegree_def] at hxker
      rw [OddOrder.Peterfalvi.S03.mem_characterKernel,
        OddOrder.Peterfalvi.S03.characterDegree_def]
      have hxker' : χ x = χ 1 := hxker
      rw [hχdef, ClassFunction.compHom_apply, ClassFunction.compHom_apply, hxdef,
        MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply, map_one] at hxker'
      exact hxker'
    · -- `H₀ = ⊥ ⊆ Ker χ`
      rw [hyp.toTypesIIIIIIVSetupT_chief_H0_eq_bot hG hvd chief]
      intro x hx
      have hx1 : x = 1 := by
        have h2 := Subgroup.mem_subgroupOf.mp (Subgroup.mem_subgroupOf.mp
          (SetLike.mem_coe.mp hx))
        rw [Subgroup.mem_bot] at h2
        exact Subtype.ext (Subtype.ext h2)
      rw [hx1, OddOrder.Peterfalvi.S03.mem_characterKernel,
        OddOrder.Peterfalvi.S03.characterDegree_def]
  · -- `∑ ν_{ij} = Ind χ`
    rw [hψeq]
    have h1 : OddOrder.Peterfalvi.S11.induceHU (hyp.toTypesIIIIIIVSetupT hG hvd) χ
        = ClassFunction.induce
            (OddOrder.Peterfalvi.S11.huSub (hyp.toTypesIIIIIIVSetupT hG hvd)) χ := by
      unfold OddOrder.Peterfalvi.S11.induceHU
      congr!
    have h2 : ClassFunction.induce ((derivedInG hyp.T).subgroupOf hyp.T) ψ
        = OddOrder.Peterfalvi.S11.induceHU (hyp.toTypesIIIIIIVSetupT hG hvd) χ := by
      rw [h1, hχdef]
      exact (OddOrder.RepresentationTheory.induce_compHom_subgroupCongr hKeq ψ).symm
    exact h2

set_option maxHeartbeats 1600000 in
-- raised heartbeat budget for the heavy elaboration below
open scoped Classical FiniteInduce in
/-- **Peterfalvi (13.3.a) at `T`**: each nonzero `ν`-row sum `ν_i = ∑_j ν_{ij}` is induced
from a *linear* (degree-one) irreducible character of `K = QD`.  Mirror of `mu_j_isIndPC`:
`ν_i` lies in the §9-on-`T` family `𝒮_T(H₀)` (`nu_rowSum_mem_sOf_H0_T`) and is reducible
(`nu_rowSum_not_irreducible`), so the case-agnostic §9 `isIndHC`
(`reducible_sOf_H0_isIndHC`) gives `ν_i = Ind_{KD-realized}(ψ)` with `ψ` linear; the
`M`-level `HC` is `(Q ⊔ D).subgroupOf T = K.subgroupOf T` (`hcRealized_map_subtype_eq`,
`toTypesIIIIIIVSetupT_cSub_eq_D`), through which `ψ` transports to the required `θ`. -/
theorem Hypothesis.nu_i_isIndQD [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (pins : NuGridSupplyData hyp)
    (i : Fin hyp.q) (hi : i ≠ ⟨0, hyp.q_prime.pos⟩) :
    ∃ θ : ClassFunction ↥(hyp.K.subgroupOf hyp.T) ℂ,
      OddOrder.RepresentationTheory.IsIrreducibleCharacter θ ∧ θ 1 = 1 ∧
        (∑ j : Fin hyp.p, hyp.nu i j)
          = ClassFunction.induce (hyp.K.subgroupOf hyp.T) θ := by
  classical
  have := hyp.finiteG
  have hvd : hyp.v * hyp.d ≠ 1 := hyp.vd_ne_one hG
  obtain ⟨chief, -⟩ := OddOrder.Peterfalvi.S11.exists_chiefFactorData hG
    (hyp.toTypesIIIIIIVSetupT hG hvd)
  let : Fintype ↥(OddOrder.Peterfalvi.S11.huSub (hyp.toTypesIIIIIIVSetupT hG hvd)) :=
    Fintype.ofFinite _
  let : Fintype ↥(OddOrder.Peterfalvi.S11.hInHu (hyp.toTypesIIIIIIVSetupT hG hvd) ⊔
      ((chief.H0 ⊔ OddOrder.Peterfalvi.S11.cSub (hyp.toTypesIIIIIIVSetupT hG hvd)
        chief).subgroupOf hyp.T).subgroupOf
        (OddOrder.Peterfalvi.S11.huSub (hyp.toTypesIIIIIIVSetupT hG hvd))) :=
    Fintype.ofFinite _
  let : Fintype ↥((OddOrder.Peterfalvi.S11.hInHu (hyp.toTypesIIIIIIVSetupT hG hvd) ⊔
      ((chief.H0 ⊔ OddOrder.Peterfalvi.S11.cSub (hyp.toTypesIIIIIIVSetupT hG hvd)
        chief).subgroupOf hyp.T).subgroupOf
        (OddOrder.Peterfalvi.S11.huSub (hyp.toTypesIIIIIIVSetupT hG hvd))).map
      (OddOrder.Peterfalvi.S11.huSub (hyp.toTypesIIIIIIVSetupT hG hvd)).subtype) :=
    Fintype.ofFinite _
  let : Invertible (Nat.card
      ↥(OddOrder.Peterfalvi.S11.hInHu (hyp.toTypesIIIIIIVSetupT hG hvd) ⊔
        ((chief.H0 ⊔ OddOrder.Peterfalvi.S11.cSub (hyp.toTypesIIIIIIVSetupT hG hvd)
          chief).subgroupOf hyp.T).subgroupOf
          (OddOrder.Peterfalvi.S11.huSub (hyp.toTypesIIIIIIVSetupT hG hvd))) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  let : Invertible (Nat.card
      ↥((OddOrder.Peterfalvi.S11.hInHu (hyp.toTypesIIIIIIVSetupT hG hvd) ⊔
        ((chief.H0 ⊔ OddOrder.Peterfalvi.S11.cSub (hyp.toTypesIIIIIIVSetupT hG hvd)
          chief).subgroupOf hyp.T).subgroupOf
          (OddOrder.Peterfalvi.S11.huSub (hyp.toTypesIIIIIIVSetupT hG hvd))).map
        (OddOrder.Peterfalvi.S11.huSub (hyp.toTypesIIIIIIVSetupT hG hvd)).subtype) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  -- `ν_i ∈ 𝒮_T(H₀)`, reducible → `isIndHC`
  have hmem := hyp.nu_rowSum_mem_sOf_H0_T hG pins hvd chief i hi
  have hred := hyp.nu_rowSum_not_irreducible pins i
  obtain ⟨ψ, hψirr, hψone, hψeq⟩ :=
    OddOrder.Peterfalvi.S11.reducible_sOf_H0_isIndHC hG
      (hyp.mkSection11CharacterDataT hG hvd chief) hmem hred
  -- `HC.map subtype = (Q ⊔ D).subgroupOf T = hyp.K.subgroupOf T`
  have hsupeq : ((hyp.toTypesIIIIIIVSetupT hG hvd).H : Subgroup G)
      ⊔ OddOrder.Peterfalvi.S11.cSub (hyp.toTypesIIIIIIVSetupT hG hvd) chief = hyp.K := by
    rw [hyp.toTypesIIIIIIVSetupT_H_eq hG hvd,
      hyp.toTypesIIIIIIVSetupT_cSub_eq_D hG hvd chief]
    rfl
  have hHC : (OddOrder.Peterfalvi.S11.hInHu (hyp.toTypesIIIIIIVSetupT hG hvd) ⊔
      ((chief.H0 ⊔ OddOrder.Peterfalvi.S11.cSub (hyp.toTypesIIIIIIVSetupT hG hvd)
        chief).subgroupOf hyp.T).subgroupOf
        (OddOrder.Peterfalvi.S11.huSub (hyp.toTypesIIIIIIVSetupT hG hvd))).map
      (OddOrder.Peterfalvi.S11.huSub (hyp.toTypesIIIIIIVSetupT hG hvd)).subtype
      = hyp.K.subgroupOf hyp.T := by
    rw [OddOrder.Peterfalvi.S11.hcRealized_map_subtype_eq chief, hsupeq]
  set θ := ClassFunction.compHom (MulEquiv.subgroupCongr hHC.symm).toMonoidHom ψ with hθdef
  refine ⟨θ, ?_, ?_, ?_⟩
  · exact OddOrder.RepresentationTheory.IsIrreducibleCharacter.compHom_of_surjective
      (MulEquiv.subgroupCongr hHC.symm).surjective hψirr
  · rw [hθdef, ClassFunction.compHom_apply, map_one, hψone]
  · rw [hψeq, hθdef,
      OddOrder.RepresentationTheory.induce_compHom_subgroupCongr hHC.symm ψ]

open scoped FiniteInduce in
/-- **Peterfalvi (13.3.a) at `T`, per-entry degree**: `ν_{ij}(1) = v` for `i ≥ 1`.  The row
is degree-constant (`nu_apply_one_row_const`), and the row sum has degree
`ν_i(1) = [T:K]·θ(1) = v·p` (`nu_i_isIndQD` + `K_index_eq_vp`); with `p ≠ 0`,
`ν_{i0}(1) = v`.  Mirror of `mu_apply_one_eq_u` — the `ν_{ij}(1) = v` that Peterfalvi
(13.3.c) feeds into the (4.3.d) congruence `v ≡ δ'_i (mod p)` for `δ'_i = 1`. -/
theorem Hypothesis.nu_apply_one_eq_v [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G)) (pins : NuGridSupplyData hyp)
    (i : Fin hyp.q) (j : Fin hyp.p) (hi : i ≠ ⟨0, hyp.q_prime.pos⟩) :
    hyp.nu i j (1 : ↥hyp.T) = ((hyp.v : ℕ) : ℂ) := by
  have := hyp.finiteG
  obtain ⟨θ, hθirr, hθ1, hθeq⟩ := hyp.nu_i_isIndQD hG pins i hi
  have hsum : (∑ j' : Fin hyp.p, hyp.nu i j') (1 : ↥hyp.T) = ((hyp.v * hyp.p : ℕ) : ℂ) := by
    rw [hθeq, ClassFunction.induce_apply_one, hθ1, mul_one, hyp.K_index_eq_vp hG]
  rw [ClassFunction.finset_sum_apply] at hsum
  have hconst : ∑ j' : Fin hyp.p, hyp.nu i j' (1 : ↥hyp.T)
      = (hyp.p : ℂ) * hyp.nu i ⟨0, hyp.p_prime.pos⟩ (1 : ↥hyp.T) := by
    rw [Finset.sum_congr rfl (fun j' _ => hyp.nu_apply_one_row_const i j'),
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [hconst] at hsum
  have hp0 : (hyp.p : ℂ) ≠ 0 := by
    rw [Nat.cast_ne_zero]; exact hyp.p_prime.pos.ne'
  have h0i : hyp.nu i ⟨0, hyp.p_prime.pos⟩ (1 : ↥hyp.T) = ((hyp.v : ℕ) : ℂ) := by
    have : (hyp.p : ℂ) * hyp.nu i ⟨0, hyp.p_prime.pos⟩ (1 : ↥hyp.T)
        = (hyp.p : ℂ) * ((hyp.v : ℕ) : ℂ) := by rw [hsum]; push_cast; ring
    exact mul_left_cancel₀ hp0 this
  rw [hyp.nu_apply_one_row_const i j, h0i]

/-- **Peterfalvi (13.3.c), the `T`-side signs are `1` off the anchor row**: `δ'_i = 1` for
`i ≥ 1`.  The (4.3.d)-at-`T` congruence `ν_{i0}(1) = δ'_i + p·a`
(`nu_degree_modEq_deltaPrime`) with `ν_{i0}(1) = v` (`nu_apply_one_eq_v`) and `v ≡ 1 (mod p)`
(`v_modEq_one`) gives `p ∣ δ'_i − 1`; since `δ'_i = ±1` (`delta_pm_one.2`) and `p ≥ 3` odd,
`δ'_i = -1` would force `p ∣ 2`, so `δ'_i = 1`.  Mirror of `delta_eq_one_of_ne_zero`. -/
theorem Hypothesis.deltaPrime_eq_one_of_ne_zero_T [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (pins : NuGridSupplyData hyp) (i : Fin hyp.q) (hi : i ≠ ⟨0, hyp.q_prime.pos⟩) :
    hyp.deltaPrime i = 1 := by
  obtain ⟨a, ha⟩ := pins.nu_degree_modEq_deltaPrime i ⟨0, hyp.p_prime.pos⟩
  rw [hyp.nu_apply_one_eq_v hG pins i ⟨0, hyp.p_prime.pos⟩ hi] at ha
  have haZ : (hyp.v : ℤ) = hyp.deltaPrime i + (hyp.p : ℤ) * a := by exact_mod_cast ha
  have hpv : (hyp.p : ℤ) ∣ (hyp.v : ℤ) - 1 := by
    have h := (Nat.modEq_iff_dvd.mp (hyp.v_modEq_one hG))
    simpa using (dvd_neg.mpr h)
  have hpδ : (hyp.p : ℤ) ∣ hyp.deltaPrime i - 1 := by
    have hsub : hyp.deltaPrime i - 1 = ((hyp.v : ℤ) - 1) - (hyp.p : ℤ) * a := by
      rw [haZ]; ring
    rw [hsub]
    exact dvd_sub hpv (Dvd.intro a rfl)
  rcases hyp.delta_pm_one.2 i with h1 | hm1
  · exact h1
  · exfalso
    rw [hm1] at hpδ
    have hp2 : (hyp.p : ℤ) ∣ 2 := dvd_neg.mp (by simpa using hpδ)
    have hple : hyp.p ≤ 2 := Nat.le_of_dvd (by norm_num) (by exact_mod_cast hp2)
    have h2le := hyp.p_prime.two_le
    have hodd := Nat.odd_iff.mp hyp.p_odd
    omega

/-- **Peterfalvi (13.3.c), all `T`-side signs are `1`** (pins-parametric form): `δ'_i = 1` for
every `i` — the anchor row is the (4.4) base sign, the rest is
`deltaPrime_eq_one_of_ne_zero_T`. -/
theorem Hypothesis.deltaPrime_eq_one_pins [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (pins : NuGridSupplyData hyp) (i : Fin hyp.q) : hyp.deltaPrime i = 1 := by
  by_cases hi : i = ⟨0, hyp.q_prime.pos⟩
  · rw [hi]; exact pins.deltaPrime_zero_eq_one
  · exact hyp.deltaPrime_eq_one_of_ne_zero_T hG pins i hi

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **Reducible `𝒯`-members are nonzero ν-row sums** (Peterfalvi (9.8)/(9.11) reverse
dichotomy, `T`-instance; mirror of `sSet_reducible_eq_muColumnSum`).  A reducible member
`η ∈ 𝒯 = sSet(setupT)` bridges into the general kernel-filter family `S(⊥)` over
`T' = derivedInG T`, where the ν-side reverse dichotomy (`nu_reducible_dichotomy`, a pure
grid field of the ν-supply) dispatches it to its ν-row `∃ i ≠ 0, η = ∑_j ν_{ij}`. -/
theorem Hypothesis.sSet_reducible_eq_nuRowSum [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (pins : NuGridSupplyData hyp) (hvd : hyp.v * hyp.d ≠ 1)
    {η : ClassFunction ↥hyp.T ℂ} (hη : η ∈ sSet (hyp.toTypesIIIIIIVSetupT hG hvd))
    (hirr : ¬ OddOrder.RepresentationTheory.IsIrreducibleCharacter η) :
    ∃ i : Fin hyp.q, i ≠ ⟨0, hyp.q_prime.pos⟩ ∧ η = ∑ j : Fin hyp.p, hyp.nu i j := by
  classical
  have := hyp.finiteG
  obtain ⟨ξ, hξ, rfl⟩ := hη
  have hξne : ξ ≠ trivialIrreducibleCharacter
      ↥(huSub (hyp.toTypesIIIIIIVSetupT hG hvd)) := by
    intro htriv
    apply hξ
    rw [htriv]
    simp only [IrreducibleCharacter.coe_trivialIrreducibleCharacter,
      OddOrder.Peterfalvi.S03.characterKernel_trivialClassFunction]
    exact Set.subset_univ _
  have hmemHU : induceHU (hyp.toTypesIIIIIIVSetupT hG hvd)
        (ξ : ClassFunction ↥(huSub (hyp.toTypesIIIIIIVSetupT hG hvd)) ℂ)
      ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily
        (huSub (hyp.toTypesIIIIIIVSetupT hG hvd)) (⊥ : Subgroup ↥hyp.T) := by
    refine ⟨ξ, hξne, ?_, (induceHU_eq_induce (hyp.toTypesIIIIIIVSetupT hG hvd) _)⟩
    intro x hx
    have hx1 : x = 1 := by
      have h2 := Subgroup.mem_subgroupOf.mp (SetLike.mem_coe.mp hx)
      rw [Subgroup.mem_bot] at h2; exact Subtype.ext h2
    rw [hx1]
    exact OddOrder.Peterfalvi.S03.one_mem_characterKernel _
  have hKeq : huSub (hyp.toTypesIIIIIIVSetupT hG hvd)
      = (derivedInG hyp.T).subgroupOf hyp.T :=
    huSub_eq_derivedInG_subgroupOf _
  have hmem : induceHU (hyp.toTypesIIIIIIVSetupT hG hvd)
        (ξ : ClassFunction ↥(huSub (hyp.toTypesIIIIIIVSetupT hG hvd)) ℂ)
      ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily
        ((derivedInG hyp.T).subgroupOf hyp.T) (⊥ : Subgroup ↥hyp.T) := hKeq ▸ hmemHU
  exact pins.nu_reducible_dichotomy hmem hirr

/-- **Peterfalvi (13.2.a) at `T`, `V`-side — unconditional**: the complement `V` is abelian,
with **no** (14.9) input.  The `T_nonI` classification: a type-II or type-III witness carries
`U_commutative`, transported to the reconciled complement `V` by the Schur–Zassenhaus
conjugacy transfer (`isMulCommutative_typePData_U_of_typePData_U`); type IV is excluded
unconditionally by Peterfalvi (11.9.c) (`not_isTypeIV_of_mem_maximalSubgroups`,
`S13_NonGaloisExclusion` — sorry-free); type V by (10.10).

This supersedes the (14.9)-gated route (`isMulCommutative_V`, which consumes `IsTypeII T`):
the (11.9.c) chain landing makes the `V`-side (13.2.a) an unconditional §13 fact.  It is the
`D`-abelian input of the caseB-`T` coherence (`Cprime-T = derivedInG D = ⊥`) and an
unconditional supply for `Hypothesis.swap`'s `hV`. -/
theorem Hypothesis.isMulCommutative_V_unconditional [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G)) :
    IsMulCommutative ↥hyp.V := by
  obtain ⟨tpd, hU, -, -⟩ := reconciled_typePData_T hG hyp
  rw [← hU]
  rcases hyp.T_nonI with h | h | h | h
  · obtain ⟨w⟩ := h
    exact OddOrder.Peterfalvi.S13.isMulCommutative_typePData_U_of_typePData_U hG
      hyp.T_maximal w.typeP tpd w.U_commutative
  · obtain ⟨w⟩ := h
    exact OddOrder.Peterfalvi.S13.isMulCommutative_typePData_U_of_typePData_U hG
      hyp.T_maximal w.typeP tpd w.U_commutative
  · exact absurd h
      (OddOrder.Peterfalvi.S13.not_isTypeIV_of_mem_maximalSubgroups hG hyp.T_maximal)
  · exact absurd ⟨hyp.T, hyp.T_maximal, h⟩
      (OddOrder.Peterfalvi.S12.no_typeV_maximal_unconditional hG)

open OddOrder.Peterfalvi.S11 in
open scoped commutatorElement in
open scoped FiniteInduce in
/-- **(9.9.a) uniform degree of the `T`-instance §9 family in the Galois case** (mirror of
`sSet_caseB_apply_one_eq_qu`; the `hdeg` input of the caseB (5.7) uniform-degree coherence
engine on `T`): in Clifford case (b) every member of `𝒯 = sSet(setupT)` has degree
`setupT.q · chars.u` (= `p·v` after the identifications).  The kernel data degenerates —
`chief.H₀ = ⊥` (`toTypesIIIIIIVSetupT_chief_H0_eq_bot`) and `C′ = derivedInG (cSub) = ⊥`
(`cSub ≤ V` abelian by the **unconditional** `isMulCommutative_V_unconditional`) — so
`𝒮(H₀C′) = 𝒮(⊥) = 𝒯` and `caseB_degree_qu` applies to every member. -/
theorem Hypothesis.sSet_caseB_apply_one_eq_vp [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hvd : hyp.v * hyp.d ≠ 1)
    {chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetupT hG hvd)}
    (caseB : OddOrder.Peterfalvi.S11.CliffordCaseBData
      (hyp.mkSection11CharacterDataT hG hvd chief))
    {φ : ClassFunction ↥hyp.T ℂ} (hφ : φ ∈ sSet (hyp.toTypesIIIIIIVSetupT hG hvd)) :
    (φ : ↥hyp.T → ℂ) 1
      = (((hyp.toTypesIIIIIIVSetupT hG hvd).q
          * (hyp.mkSection11CharacterDataT hG hvd chief).u : ℕ) : ℂ) := by
  classical
  have := hyp.finiteG
  have hH0 : chief.H0 = ⊥ := hyp.toTypesIIIIIIVSetupT_chief_H0_eq_bot hG hvd chief
  have hCp : (hyp.mkSection11CharacterDataT hG hvd chief).Cprime = ⊥ := by
    change cprimeSub (hyp.toTypesIIIIIIVSetupT hG hvd) chief = ⊥
    have hCV : cSub (hyp.toTypesIIIIIIVSetupT hG hvd) chief ≤ hyp.V :=
      (cSub_le_U _ _).trans (le_of_eq (hyp.toTypesIIIIIIVSetupT_U_eq hG hvd))
    have hVab : IsMulCommutative ↥hyp.V := hyp.isMulCommutative_V_unconditional hG
    have hCab : IsMulCommutative
        ↥(cSub (hyp.toTypesIIIIIIVSetupT hG hvd) chief) :=
      ⟨⟨fun a b => Subtype.ext (by
        have h := hVab.is_comm.comm
          (⟨(a : G), hCV a.2⟩ : ↥hyp.V) ⟨(b : G), hCV b.2⟩
        simpa using congrArg Subtype.val h)⟩⟩
    have hcomm : commutator
        ↥(cSub (hyp.toTypesIIIIIIVSetupT hG hvd) chief) = ⊥ := by
      rw [eq_bot_iff]
      refine (Subgroup.commutator_le (H₁ := ⊤) (H₂ := ⊤) (H₃ := ⊥)).mpr (fun a _ b _ => ?_)
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_commute]
      exact hCab.is_comm.comm a b
    change derivedInG (cSub (hyp.toTypesIIIIIIVSetupT hG hvd) chief) = ⊥
    rw [derivedInG, hcomm, Subgroup.map_bot]
  have hmem : φ ∈ (hyp.mkSection11CharacterDataT hG hvd chief).SOf
      (chief.H0 ⊔ (hyp.mkSection11CharacterDataT hG hvd chief).Cprime) := by
    rw [Section11CharacterData.SOf_eq, hH0, hCp, sup_bot_eq]
    obtain ⟨χ, hχ, rfl⟩ := hφ
    refine ⟨χ, ?_, rfl⟩
    rw [mem_xiOf]
    refine ⟨hχ, ?_⟩
    intro x hx
    have hx1 : x = 1 := by
      have h2 := Subgroup.mem_subgroupOf.mp (Subgroup.mem_subgroupOf.mp
        (SetLike.mem_coe.mp hx))
      rw [Subgroup.mem_bot] at h2
      exact Subtype.ext (Subtype.ext h2)
    rw [hx1, OddOrder.Peterfalvi.S03.mem_characterKernel,
      OddOrder.Peterfalvi.S03.characterDegree_def]
  exact caseB_degree_qu hG (hyp.mkSection11CharacterDataT hG hvd chief) caseB φ hmem

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **(4.7)-at-`T` member support**: every `𝒯`-member source `Ind_{HU}^T ξ` (`ξ ∈ 𝒳`) is
supported in `A(T) ∪ {1}`.  Mirror of `sSet_member_support_subset_A` — the S-side type-II
identification `P = M_σ(S)` is only used for a *membership*, so the `T`-side needs just
`Q ≤ M_σ(T)` (`maxNilpotentNormalHall_le_Msigma`, valid for every maximal subgroup, type III
included); every other ingredient (`support_induce_subset_conjugatesIntoSet`, the (1.2) core,
`S10.typePACore_conj_mem`) is `M`-generic. -/
theorem Hypothesis.sSet_member_support_subset_A_T [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hvd : hyp.v * hyp.d ≠ 1)
    {ξ : OddOrder.RepresentationTheory.IrreducibleCharacter
      ↥(huSub (hyp.toTypesIIIIIIVSetupT hG hvd))}
    (hξ : ξ ∈ xiSet (hyp.toTypesIIIIIIVSetupT hG hvd)) :
    (induceHU (hyp.toTypesIIIIIIVSetupT hG hvd)
        (ξ : ClassFunction ↥(huSub (hyp.toTypesIIIIIIVSetupT hG hvd)) ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (S10.typePACore hyp.T) hyp.T ∪ {1} := by
  have : Fintype G := Fintype.ofFinite G
  classical
  have hHQ : ((hyp.toTypesIIIIIIVSetupT hG hvd).H : Subgroup G) = hyp.Q :=
    hyp.toTypesIIIIIIVSetupT_H_eq hG hvd
  have hQle : hyp.Q ≤ OddOrder.BG.Ch3.S10.Msigma hyp.T := by
    rw [hyp.Q_eq_TF]
    exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_Msigma hG hyp.T_maximal
  have hcore : ∀ w : ↥(huSub (hyp.toTypesIIIIIIVSetupT hG hvd)),
      (ξ : ClassFunction ↥(huSub (hyp.toTypesIIIIIIVSetupT hG hvd)) ℂ) w ≠ 0 →
      ((w : ↥hyp.T) : G) ≠ 1 →
      ((w : ↥hyp.T) : G) ∈ S10.typePACore hyp.T := by
    intro w hwval hwne
    have := hInHu_normal (hyp.toTypesIIIIIIVSetupT hG hvd)
    have hCne : OddOrder.Peterfalvi.S03.centralizerInSubgroup
        (hInHu (hyp.toTypesIIIIIIVSetupT hG hvd)) w ≠ ⊥ := fun hbot =>
      hwval
        (OddOrder.Peterfalvi.S03.irreducibleCharacter_apply_eq_zero_of_centralizerInSubgroup_eq_bot
          ξ hξ hbot)
    obtain ⟨d, hd_mem, hd_ne⟩ := (Subgroup.bot_or_exists_ne_one _).resolve_left hCne
    rw [OddOrder.Peterfalvi.S03.mem_centralizerInSubgroup] at hd_mem
    obtain ⟨hd_H, hd_comm⟩ := hd_mem
    have hdS_H : (d : ↥hyp.T) ∈ (hyp.toTypesIIIIIIVSetupT hG hvd).H.subgroupOf hyp.T :=
      (Subgroup.mem_subgroupOf).mp hd_H
    have hdH_G : ((d : ↥hyp.T) : G) ∈ (hyp.toTypesIIIIIIVSetupT hG hvd).H :=
      (Subgroup.mem_subgroupOf).mp hdS_H
    have hdG_ne : ((d : ↥hyp.T) : G) ≠ 1 := fun he => hd_ne (by
      apply Subtype.ext; apply Subtype.ext; exact he)
    have hcommG : ((d : ↥hyp.T) : G) * ((w : ↥hyp.T) : G)
        = ((w : ↥hyp.T) : G) * ((d : ↥hyp.T) : G) := by
      have := congrArg (fun t : ↥hyp.T => (t : G)) (Subtype.ext_iff.mp hd_comm)
      simpa using this
    rw [S10.mem_typePACore]
    refine ⟨?_, hwne, ((d : ↥hyp.T) : G), ?_, ?_⟩
    · have hwHU : (w : ↥hyp.T) ∈ (derivedInG hyp.T).subgroupOf hyp.T := by
        rw [← huSub_eq_derivedInG_subgroupOf]; exact w.2
      exact (Subgroup.mem_subgroupOf).mp hwHU
    · refine (Set.mem_sdiff _).mpr ⟨?_, fun he => hdG_ne (Set.mem_singleton_iff.mp he)⟩
      have hdQ : ((d : ↥hyp.T) : G) ∈ hyp.Q := hHQ ▸ hdH_G
      exact SetLike.mem_coe.mpr (hQle hdQ)
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact hcommG.symm
  intro x hx
  rw [Set.mem_union, Set.mem_singleton_iff]
  by_cases hx1 : x = 1
  · exact Or.inr hx1
  have hxsupp : (induceHU (hyp.toTypesIIIIIIVSetupT hG hvd)
      (ξ : ClassFunction ↥(huSub (hyp.toTypesIIIIIIVSetupT hG hvd)) ℂ)) x ≠ 0 :=
    ClassFunction.mem_support.mp hx
  have hx_conj : x ∈ ClassFunction.conjugatesIntoSet (huSub (hyp.toTypesIIIIIIVSetupT hG hvd))
      ((ξ : ClassFunction ↥(huSub (hyp.toTypesIIIIIIVSetupT hG hvd)) ℂ)).support := by
    have hind : induceHU (hyp.toTypesIIIIIIVSetupT hG hvd)
          (ξ : ClassFunction ↥(huSub (hyp.toTypesIIIIIIVSetupT hG hvd)) ℂ)
        = ClassFunction.induce (huSub (hyp.toTypesIIIIIIVSetupT hG hvd))
          (ξ : ClassFunction ↥(huSub (hyp.toTypesIIIIIIVSetupT hG hvd)) ℂ) := rfl
    refine ClassFunction.support_induce_subset_conjugatesIntoSet (subset_refl _) ?_
    rw [← hind]; exact hxsupp
  rw [ClassFunction.mem_conjugatesIntoSet] at hx_conj
  obtain ⟨c, hc, hcsupp⟩ := hx_conj
  set w : ↥(huSub (hyp.toTypesIIIIIIVSetupT hG hvd)) := ⟨c⁻¹ * x * c, hc⟩ with hw_def
  have hw_val : (ξ : ClassFunction ↥(huSub (hyp.toTypesIIIIIIVSetupT hG hvd)) ℂ) w ≠ 0 :=
    ClassFunction.mem_support.mp hcsupp
  have hwS_eq : ((w : ↥hyp.T) : G) = (c : G)⁻¹ * (x : G) * (c : G) := rfl
  have hxeq : (x : G) = (c : G) * ((w : ↥hyp.T) : G) * (c : G)⁻¹ := by
    rw [hwS_eq]; group
  have hwne : ((w : ↥hyp.T) : G) ≠ 1 := by
    intro he
    apply hx1
    have hxG : (x : G) = 1 := by rw [hxeq, he]; group
    exact Subtype.ext hxG
  have hwA : ((w : ↥hyp.T) : G) ∈ S10.typePACore hyp.T := hcore w hw_val hwne
  refine Or.inl ?_
  rw [OddOrder.Peterfalvi.S04.mem_supportInSubgroup, hxeq]
  exact S10.typePACore_conj_mem c.2 hwA

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **`𝒯`-members are supported in `A(T) ∪ {1}`** (full-family form; mirror of
`sSet_member_support_subset`). -/
theorem Hypothesis.sSet_member_support_subset_T [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hvd : hyp.v * hyp.d ≠ 1)
    {φ : ClassFunction ↥hyp.T ℂ} (hφ : φ ∈ sSet (hyp.toTypesIIIIIIVSetupT hG hvd)) :
    φ.support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (S10.typePACore hyp.T) hyp.T ∪ {1} := by
  have : Fintype G := Fintype.ofFinite G
  obtain ⟨ξ, hξ, rfl⟩ := hφ
  exact hyp.sSet_member_support_subset_A_T hG hvd hξ

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **`𝒯`-member differences are `A(T)`-supported in the Galois case** (mirror of
`sSet_caseB_member_diff_supported`; the `hsuppdiff` input of the caseB (5.7) coherence engine
on `T`): both members have the uniform degree `p·v` (`sSet_caseB_apply_one_eq_vp`), so the
difference vanishes at `1` and its support lands in `A(T)`. -/
theorem Hypothesis.sSet_caseB_member_diff_supported_T [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hvd : hyp.v * hyp.d ≠ 1)
    {chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetupT hG hvd)}
    (caseB : OddOrder.Peterfalvi.S11.CliffordCaseBData
      (hyp.mkSection11CharacterDataT hG hvd chief))
    {x : ClassFunction ↥hyp.T ℂ} (hx : x ∈ sSet (hyp.toTypesIIIIIIVSetupT hG hvd))
    {y : ClassFunction ↥hyp.T ℂ} (hy : y ∈ sSet (hyp.toTypesIIIIIIVSetupT hG hvd)) :
    (x - y).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (S10.typePACore hyp.T) hyp.T := by
  have : Fintype G := Fintype.ofFinite G
  intro z hz
  have hz0 : (x - y) z ≠ 0 := hz
  have hdeg : (x : ↥hyp.T → ℂ) 1 = (y : ↥hyp.T → ℂ) 1 := by
    rw [hyp.sSet_caseB_apply_one_eq_vp hG hvd caseB hx,
      hyp.sSet_caseB_apply_one_eq_vp hG hvd caseB hy]
  rcases ClassFunction.support_sub_subset x y hz with h | h
  · rcases hyp.sSet_member_support_subset_T hG hvd hx h with h' | h'
    · exact h'
    · exfalso; rw [Set.mem_singleton_iff] at h'; subst h'
      exact hz0 (by rw [ClassFunction.sub_apply, hdeg, sub_self])
  · rcases hyp.sSet_member_support_subset_T hG hvd hy h with h' | h'
    · exact h'
    · exfalso; rw [Set.mem_singleton_iff] at h'; subst h'
      exact hz0 (by rw [ClassFunction.sub_apply, hdeg, sub_self])

/-- **`Odd |T|`** (mirror of `oddCardS`): the subcoherence realness input for the `T`-instance
§9 family. -/
theorem Hypothesis.oddCardT [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G)) :
    Odd (Nat.card ↥hyp.T) := by
  rcases hG.odd with ⟨k, hk⟩
  have hdvd : Nat.card ↥hyp.T ∣ Nat.card G := Subgroup.card_subgroup_dvd_card hyp.T
  rcases Nat.even_or_odd (Nat.card ↥hyp.T) with heven | hodd
  · exfalso
    have h2 : (2 : ℕ) ∣ Nat.card G := (even_iff_two_dvd.mp heven).trans hdvd
    rw [hk] at h2
    omega
  · exact hodd

/-- **`T` is of type `P`** (issue 2035 #85, the 0116 (i) ungated producer): `T` is non-type-I
(`T_nonI`), and every branch of the Peterfalvi taxonomy (II/III/IV/V) is a BG type-`P` class
(`proposition_type_classification`: II ↔ `P₂`, III∨IV / V ↔ `P₁`-side).  This is the
general type-`P` input used by the `τ₁T`/Dade supply chain and by the symmetric §13 swap. -/
theorem Hypothesis.T_isTypeP [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G)) :
    OddOrder.BG.Ch4.S14.IsTypeP hyp.T := by
  have hcls := OddOrder.BG.Ch4.S16.proposition_type_classification hG hyp.T_maximal
  rcases hyp.T_nonI with h | h | h | h
  · exact (hcls.2.1.mp h).1
  · exact (hcls.2.2.1.mp (Or.inl h)).1.1
  · exact (hcls.2.2.1.mp (Or.inr h)).1.1
  · exact (hcls.2.2.2.1.mp h).1.1

/-- **(13.2.e) `T`-instance Dade hypothesis** (mirror of `dadeHypS`; the `A(T)`-Dade datum for
the caseB-`T` (5.7) coherence).  Runs at general type `P` (issue 2035 #85): the underlying
construction is `S10.dadeSupportHypothesisData_typePACore`, weakened to `IsTypeP` — supplied
ungated by `T_isTypeP`. -/
noncomputable def Hypothesis.dadeHypT [Fintype G] [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hTP : OddOrder.BG.Ch4.S14.IsTypeP hyp.T) :
    OddOrder.Peterfalvi.S04.Hypothesis G (S10.typePACore hyp.T) hyp.T :=
  (OddOrder.Peterfalvi.S10.dadeSupportHypothesisData_typePACore hG hyp.T_maximal hTP).some.dade

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **(5.3.a)-at-`T` per-member difference support** (mirror of `sSet_member_diffsupp`): for a
`𝒯`-member source `Ind_{HU}^T ξ`, the conjugate difference is `A(T)`-supported — the support
lands in `A(T) ∪ {1}` (`sSet_member_support_subset_A_T`) and the value at `1` is the real
positive degree, so `1` drops out.  The `hdiffsupp` half of the irreducible `R`-datum. -/
theorem Hypothesis.sSet_member_diffsupp_T [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hvd : hyp.v * hyp.d ≠ 1)
    {ξ : OddOrder.RepresentationTheory.IrreducibleCharacter
      ↥(huSub (hyp.toTypesIIIIIIVSetupT hG hvd))}
    (hξ : ξ ∈ xiSet (hyp.toTypesIIIIIIVSetupT hG hvd)) :
    ((induceHU (hyp.toTypesIIIIIIVSetupT hG hvd)
          (ξ : ClassFunction ↥(huSub (hyp.toTypesIIIIIIVSetupT hG hvd)) ℂ)).conj
        - induceHU (hyp.toTypesIIIIIIVSetupT hG hvd)
          (ξ : ClassFunction ↥(huSub (hyp.toTypesIIIIIIVSetupT hG hvd)) ℂ)).support
      ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (S10.typePACore hyp.T) hyp.T := by
  have : Fintype G := Fintype.ofFinite G
  set φ : ClassFunction ↥hyp.T ℂ :=
    induceHU (hyp.toTypesIIIIIIVSetupT hG hvd)
      (ξ : ClassFunction ↥(huSub (hyp.toTypesIIIIIIVSetupT hG hvd)) ℂ) with hφ
  have hsupp_eq : φ.conj.support = φ.support := by
    ext y
    simp only [ClassFunction.mem_support, ne_eq, ClassFunction.conj_apply, star_eq_zero]
  intro x hx
  have hx0 : (φ.conj - φ) x ≠ 0 := hx
  have hxsupp : x ∈ φ.support := by
    have hxU := ClassFunction.support_sub_subset _ _ hx
    rwa [hsupp_eq, Set.union_self] at hxU
  rcases hyp.sSet_member_support_subset_A_T hG hvd hξ (hφ ▸ hxsupp) with h | h
  · exact h
  · exfalso
    rw [Set.mem_singleton_iff] at h
    subst h
    obtain ⟨d, _, hd⟩ :=
      OddOrder.RepresentationTheory.irreducibleCharacter_apply_one_eq_pos_natCast ξ
    apply hx0
    rw [ClassFunction.sub_apply, ClassFunction.conj_apply, hφ, induceHU_apply_one_eq_q_mul, hd,
      star_mul', star_natCast, star_natCast, sub_self]

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **Conjugate-difference support for `𝒯`-members** (mirror of
`sSet_member_conjDiff_supported`): case-agnostic — a member and its conjugate share the real
positive degree, so `(η̄ − η).support ⊆ A(T)`.  The diff-support input of the irreducible
`R`-family, serving both Clifford cases. -/
theorem Hypothesis.sSet_member_conjDiff_supported_T [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hvd : hyp.v * hyp.d ≠ 1)
    {η : ClassFunction ↥hyp.T ℂ} (hη : η ∈ sSet (hyp.toTypesIIIIIIVSetupT hG hvd)) :
    ((η : ClassFunction ↥hyp.T ℂ).conj - η).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (S10.typePACore hyp.T) hyp.T := by
  have := hyp.finiteG
  let : Fintype G := Fintype.ofFinite G
  obtain ⟨ξ, hξ, rfl⟩ := hη
  exact hyp.sSet_member_diffsupp_T hG hvd hξ

/-- **The conjugate of a reducible `𝒯`-member is reducible** (mirror of
`sSet_reducible_conj_not_irr`). -/
theorem Hypothesis.sSet_reducible_conj_not_irr_T [Finite G] (hyp : Hypothesis (G := G))
    {η : ClassFunction ↥hyp.T ℂ}
    (hirr : ¬ OddOrder.RepresentationTheory.IsIrreducibleCharacter η) :
    ¬ OddOrder.RepresentationTheory.IsIrreducibleCharacter
      (η : ClassFunction ↥hyp.T ℂ).conj := by
  have := hyp.finiteG
  intro h
  apply hirr
  rw [← ClassFunction.conj_conj η]
  exact h.conj

open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in
/-- **The two ν-rows of a reducible `𝒯`-member are distinct** (mirror of
`sSet_reducible_columns_ne`): row`(η) ≠ ` row`(η̄)`, else `η` would be real, contradicting
`sSet_hasNoRealCharacters` (via `oddCardT`). -/
theorem Hypothesis.sSet_reducible_rows_ne [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (pins : NuGridSupplyData hyp) (hvd : hyp.v * hyp.d ≠ 1)
    {η : ClassFunction ↥hyp.T ℂ} (hη : η ∈ sSet (hyp.toTypesIIIIIIVSetupT hG hvd))
    (hirr : ¬ OddOrder.RepresentationTheory.IsIrreducibleCharacter η) :
    (hyp.sSet_reducible_eq_nuRowSum hG pins hvd hη hirr).choose ≠
      (hyp.sSet_reducible_eq_nuRowSum hG pins hvd
        (sSet_closedUnderConjugate (hyp.toTypesIIIIIIVSetupT hG hvd) hη)
        (hyp.sSet_reducible_conj_not_irr_T hirr)).choose := by
  intro he
  have hnonreal : ¬ ClassFunction.IsReal η :=
    sSet_hasNoRealCharacters (hyp.toTypesIIIIIIVSetupT hG hvd) (hyp.oddCardT hG) hη
  apply hnonreal
  have hjeq := (hyp.sSet_reducible_eq_nuRowSum hG pins hvd hη hirr).choose_spec.2
  have hkeq := (hyp.sSet_reducible_eq_nuRowSum hG pins hvd
    (sSet_closedUnderConjugate (hyp.toTypesIIIIIIVSetupT hG hvd) hη)
    (hyp.sSet_reducible_conj_not_irr_T hirr)).choose_spec.2
  change (η : ClassFunction ↥hyp.T ℂ).conj = η
  rw [hkeq, ← he, ← hjeq]

end OddOrder.Peterfalvi.S15


