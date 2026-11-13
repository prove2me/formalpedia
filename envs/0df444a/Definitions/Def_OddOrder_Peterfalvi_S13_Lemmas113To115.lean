-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S13_Lemmas113To115
-- name    : OddOrder_Peterfalvi_S13_Lemmas113To115
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T13:39:22.274268+00:00
-- url     : https://prove2.me/theorems/35246c02-9bd4-431d-a249-f07d9d7ebe3e
-- title:
--   Peterfalvi (9.11)/(10.10): Lemmas (11.3)–(11.5) and type V case (a) coherence
-- statement:
--   Formalizes the monotonicity of coherence for subfamilies, the subset step of the (9.11) coherence route, and the type V case (a) coherence of Peterfalvi (10.10).
--
--   Main declarations: `isCoherent_of_subset` (Coherence restricts to a subfamily); `coherent_sOf_H0C_of_coherent_sOf_H0Cprime` ((9.11) `hY`-route subset step); `typeV_caseA_coherence` (Peterfalvi (10.10), case (a) of Definition (8.7)).
--
--   The bundle also proves 10 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S13_Lemmas113To115.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S13_Lemmas113To115.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S13_MaximalIII_IVBasic
import Definitions.Def_OddOrder_Peterfalvi_S12_TypeVSibley
import Definitions.Def_OddOrder_Peterfalvi_S13_SixTwoImageData

namespace OddOrder.Peterfalvi.S13

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

open scoped OddOrder.Peterfalvi.S12.FiniteInduce

variable {G : Type*} [Group G]

/-- **Peterfalvi (11.3), the Theorem (6.3) coherence-extension input** (§13 instance): if the
sub-family `S(H₀C)` is coherent, then so is the full family `S`.

This is Peterfalvi's Theorem (6.3) applied with `(L, K, M, H, H₁) = (M, M', 1, HC, H₀C)`; its
hypotheses hold in the §13 setup ((6.3.a) `HC` nilpotent — `H = M_F` nilpotent and `C = C_U(H)`
centralizes `H`; (6.3.b) from the coherence of `S(H₀C)`; (6.3.c) from (9.6)/(11.1)).

Discharged through the **oracle-free** (6.3) `S12.Hypothesis.sixThree_of_hypothesis`
(`S13_SixTwoImageData`, issue 0153): the (6.2) break-member bound is *proved* from Hypothesis
(5.2)'s difference-image families (`inducedFamilyImageData`, i.e. Peterfalvi (5.3.b): the
two-element Dade family on irreducible members, `R(μ_j)` of Theorem (4.9) on the reducible
μ-columns), so this cite needs neither the break oracle nor the §11 dichotomy producer. -/
theorem coherent_S_of_coherent_SH0C [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hyp : Hypothesis M) (htype : IsTypeIII M ∨ IsTypeIV M)
    (_hcoh : Nonempty (OddOrder.Peterfalvi.S07.IsCoherent
      hyp.base.tau (hyp.SOf hyp.H0C) hyp.base.A0)) :
    Nonempty (OddOrder.Peterfalvi.S07.IsCoherent
      hyp.base.tau hyp.base.Sset hyp.base.A0) := by
  classical
  -- the (6.3) data: `(K, H, M, H₁) = (M', HC, ⊥, H₀C)`-traces inside `↥M`
  have hHCleM : hyp.HC ≤ M := hyp.HC_le_derived.trans (Subgroup.map_subtype_le _)
  have hH0CleM : hyp.H0C ≤ M := hyp.H0C_le_derived.trans (Subgroup.map_subtype_le _)
  have hH0CleHC : hyp.H0C ≤ hyp.HC :=
    sup_le (hyp.H0_lt_H.le.trans le_sup_left) le_sup_right
  -- instances for the oracle
  have : Group.IsSolvable ↥M :=
    _hG.isSolvable_of_lt_top M (lt_top_iff_ne_top.mpr hyp.base.maximal.1)
  have : Group.IsSolvable ↥((derivedInG M).subgroupOf M) := inferInstance
  have hHCnil : Group.IsNilpotent ↥(hyp.HC.subgroupOf M) := by
    have := hyp.HC_isNilpotent
    exact Group.nilpotent_of_surjective
      (Subgroup.subgroupOfEquivOfLe hHCleM).symm.toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hHCleM).symm.surjective
  have hH₁n : (hyp.H0C.subgroupOf M).Normal := hyp.H0C_subgroupOf_normal
  have hHnorm : (hyp.HC.subgroupOf M).Normal := hyp.HC_subgroupOf_normal
  -- strictness `H₀C-trace < HC-trace`
  have hH₁H : hyp.H0C.subgroupOf M < hyp.HC.subgroupOf M := by
    refine lt_of_le_of_ne (Subgroup.subgroupOf_mono M hH0CleHC) ?_
    intro heq
    have hamb : hyp.H0C = hyp.HC := by
      have h1 := congrArg (Subgroup.map M.subtype) heq
      rwa [Subgroup.map_subgroupOf_eq_of_le hH0CleM,
        Subgroup.map_subgroupOf_eq_of_le hHCleM] at h1
    exact hyp.H_not_le_H0C (hamb ▸ (le_sup_left : hyp.base.typeP.H ≤ hyp.HC))
  have hHK : hyp.HC.subgroupOf M ≤ (derivedInG M).subgroupOf M :=
    Subgroup.subgroupOf_mono M hyp.HC_le_derived
  -- numerical bound (6.3.c): `4q² + 1 < p^q`
  have hbound : 4 * ((derivedInG M).subgroupOf M).index ^ 2 + 1
      < Nat.card (↥(hyp.HC.subgroupOf M)
          ⧸ (hyp.H0C.subgroupOf M).subgroupOf (hyp.HC.subgroupOf M)) := by
    have hidx : ((derivedInG M).subgroupOf M).index = hyp.q :=
      hyp.base.typeP.card_W1_eq_derived_index.symm
    have hcardq : Nat.card (↥(hyp.HC.subgroupOf M)
        ⧸ (hyp.H0C.subgroupOf M).subgroupOf (hyp.HC.subgroupOf M))
        = hyp.p ^ hyp.q := by
      rw [← Subgroup.index_eq_card,
        show ((hyp.H0C.subgroupOf M).subgroupOf (hyp.HC.subgroupOf M)).index
          = (hyp.H0C.subgroupOf M).relIndex (hyp.HC.subgroupOf M) from rfl,
        Subgroup.relIndex_subgroupOf hHCleM]
      exact hyp.H0C_relIndex_HC _hG htype
    rw [hidx, hcardq]
    obtain ⟨hp', hq', hpo, hqo, hne⟩ := hyp.p_q_distinct_odd_primes _hG htype
    exact prime_pow_gt_four_mul_sq_add_one hp' hq' hpo hqo hne
  -- assemble via the **oracle-free** (6.3) (`S12.Hypothesis.sixThree_of_hypothesis`,
  -- `S13_SixTwoImageData`): the (6.2) break bound is proved from Hypothesis (5.2)'s image
  -- families, so neither the break-member oracle nor the §11 dichotomy producer (with its
  -- `ChiefFactorData` / `TypePNontrivialCore` inputs) is needed here.
  have hmain := hyp.base.sixThree_of_hypothesis _hG
    (hyp.params_mu_eq _hG _hG.odd) hyp.params_delta_pm
    (hyp.params_delta_sign _hG _hG.odd) hyp.params_zeta_mem hyp.params_zeta_degree
    (H := hyp.HC.subgroupOf M) (N := ⊥) (H₁ := hyp.H0C.subgroupOf M)
    hHnorm bot_le hH₁H hHK
    (by
      show Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.base.tau
        (OddOrder.Peterfalvi.S08.inducedKernelFamily ((derivedInG M).subgroupOf M)
          (hyp.H0C.subgroupOf M)) hyp.base.A0)
      rw [← hyp.SOf_eq]
      exact _hcoh) hbound
  have hSset : hyp.base.Sset
      = OddOrder.Peterfalvi.S08.inducedKernelFamily
          ((derivedInG M).subgroupOf M) (⊥ : Subgroup ↥M) := by
    unfold OddOrder.Peterfalvi.S12.Hypothesis.Sset
    exact OddOrder.Peterfalvi.S12.inducedFamily_eq_inducedKernelFamily_bot
  rw [hSset]
  exact hmain

/-- **Peterfalvi (11.4), parametrized on the (11.3) non-coherence** (issue 1025): if `S(H_1)`
is coherent for a normal subgroup `H_1 < M'`, then `|M'/H_1| - 1 ≤ 2 q |U/C|` (the quotient
bound from Theorem (6.2)), stated in the subtraction-free form `|M' : H_1| ≤ 2 q |U : C| + 1`.
The (11.3) non-coherence `hnc` of `𝒮(H₀C)` is taken as a hypothesis (rather than cited from the
legacy sorried `S_H0C_not_coherent`) so a caller who has an *axiom-clean* (11.3) — the spine's
`S_H0C_not_coherent_unconditional`, threaded through `exists_zeta_residual_..._of_refuter`'s
`hrefute` — gets an axiom-clean bound.  (The former legacy wrapper `coherent_quotient_bound`
at the sorried (11.3) is retired; the axiom-clean (11.3) is `S_H0C_not_coherent_unconditional`,
`S13_TypeDetermination`.  Issue 9087.) -/
theorem coherent_quotient_bound_of_noncoherent [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) {M H1 : Subgroup G}
    (hyp : Hypothesis M) (hH1_norm : M ≤ Subgroup.normalizer (H1 : Set G))
    (hH1_lt : H1 < derivedInG M)
    (hcoh : Nonempty (OddOrder.Peterfalvi.S07.IsCoherent
      hyp.base.tau (hyp.SOf H1) hyp.base.A0))
    (hnc : ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent
      hyp.base.tau (hyp.SOf hyp.H0C) hyp.base.A0)) :
    H1.relIndex (derivedInG M) ≤ 2 * hyp.q * hyp.C.relIndex hyp.U + 1 := by
  classical
  -- normality instances for the section subgroups and their traces
  have hA'n : ((H1.subgroupOf M)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer
      (hH1_lt.le.trans (Subgroup.map_subtype_le _))).mpr hH1_norm
  have hBn : ((hyp.H0C.subgroupOf M)).Normal := hyp.H0C_subgroupOf_normal
  have : ((H1.subgroupOf M).subgroupOf ((derivedInG M).subgroupOf M)).Normal :=
    hA'n.subgroupOf _
  have : ((hyp.H0C.subgroupOf M).subgroupOf ((derivedInG M).subgroupOf M)).Normal :=
    hBn.subgroupOf _
  have : ((hyp.H0C.subgroupOf M).subgroupOf (hyp.HC.subgroupOf M)).Normal :=
    hBn.subgroupOf _
  -- coherence dichotomy at the pinned family (`SOf_eq`; `tau`/`A0` are definitional)
  have hAcoh : Nonempty (OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp.base.dadeData.dade
        (hyp.base.dadeData.dade.fullDadeIsometryData))
      (OddOrder.Peterfalvi.S08.inducedKernelFamily ((derivedInG M).subgroupOf M)
        (H1.subgroupOf M)) hyp.base.A0) := by
    have h := hcoh
    rw [hyp.SOf_eq] at h
    exact h
  have hBncoh : ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp.base.dadeData.dade
        (hyp.base.dadeData.dade.fullDadeIsometryData))
      (OddOrder.Peterfalvi.S08.inducedKernelFamily ((derivedInG M).subgroupOf M)
        (hyp.H0C.subgroupOf M)) hyp.base.A0) := by
    have h := hnc
    rw [hyp.SOf_eq] at h
    exact h
  -- the two proper traces, in the `< M'`-form the oracle-free (6.2) takes (`A.subgroupOf B = ⊤ ↔
  -- B ≤ A`, so `≠ ⊤` upgrades `≤` to `<`)
  have hH0CleHC : hyp.H0C ≤ hyp.HC := sup_le (hyp.H0_lt_H.le.trans le_sup_left) le_sup_right
  have hA'lt : H1.subgroupOf M < (derivedInG M).subgroupOf M :=
    lt_of_le_not_ge (Subgroup.subgroupOf_mono M hH1_lt.le)
      (fun hle => Hypothesis.trace_ne_top_of_lt_derived hH1_lt
        (Subgroup.subgroupOf_eq_top.mpr hle))
  have hBlt : hyp.H0C.subgroupOf M < (derivedInG M).subgroupOf M :=
    lt_of_le_not_ge (Subgroup.subgroupOf_mono M (hH0CleHC.trans hyp.HC_le_derived))
      (fun hle => hyp.H0C_trace_ne_top (Subgroup.subgroupOf_eq_top.mpr hle))
  -- the (6.2) bound at `(C, D) = (HC, HC)`-traces, through the **oracle-free** (6.2)
  -- (`S12.Hypothesis.sixTwo_of_hypothesis`, `S13_SixTwoImageData`): the break bound is proved
  -- from Hypothesis (5.2)'s image families, so the §11 dichotomy producer — and with it the
  -- `ChiefFactorData` / `TypePNontrivialCore` inputs — is no longer needed (cf. (11.3) above).
  have hbound := hyp.base.sixTwo_of_hypothesis _hG
    (hyp.params_mu_eq _hG _hG.odd) hyp.params_delta_pm
    (hyp.params_delta_sign _hG _hG.odd) hyp.params_zeta_mem hyp.params_zeta_degree
    (A' := H1.subgroupOf M) (B := hyp.H0C.subgroupOf M)
    (C := hyp.HC.subgroupOf M) (D := hyp.HC.subgroupOf M)
    hA'lt hBlt (Subgroup.subgroupOf_mono M hH0CleHC)
    (Subgroup.subgroupOf_mono M hyp.HC_le_derived)
    hyp.HC_central_condition hAcoh hBncoh
  -- the square-root factor is `√1 = 1`
  have hsq : Nat.card (↥(hyp.HC.subgroupOf M) ⧸
      (hyp.HC.subgroupOf M).subgroupOf (hyp.HC.subgroupOf M)) = 1 := by
    rw [Subgroup.subgroupOf_self]
    have : Subsingleton (↥(hyp.HC.subgroupOf M) ⧸ (⊤ : Subgroup ↥(hyp.HC.subgroupOf M))) :=
      QuotientGroup.subsingleton_quotient_top
    exact Nat.card_unique
  rw [hsq] at hbound
  simp only [Nat.cast_one, Real.sqrt_one, mul_one] at hbound
  -- the left side is the relative index `|M' : H₁|`
  have hL : Nat.card (↥((derivedInG M).subgroupOf M) ⧸
      (H1.subgroupOf M).subgroupOf ((derivedInG M).subgroupOf M))
      = H1.relIndex (derivedInG M) := by
    have h1 : Nat.card (↥((derivedInG M).subgroupOf M) ⧸
        (H1.subgroupOf M).subgroupOf ((derivedInG M).subgroupOf M))
        = (H1.subgroupOf M).relIndex ((derivedInG M).subgroupOf M) := rfl
    rw [h1]
    exact Subgroup.relIndex_subgroupOf (show derivedInG M ≤ M from Subgroup.map_subtype_le _)
  rw [hL] at hbound
  -- the index factor is `q·|U:C|`
  have hidx : ((hyp.HC.subgroupOf M).index : ℝ)
      = (hyp.base.w1 * hyp.C.relIndex hyp.U : ℕ) := by
    rw [hyp.HC_trace_index]
  rw [hidx] at hbound
  -- conclude over `ℕ`
  have hfinal : (H1.relIndex (derivedInG M) : ℝ)
      ≤ 2 * (hyp.base.w1 * hyp.C.relIndex hyp.U : ℕ) + 1 := by linarith
  have : H1.relIndex (derivedInG M) ≤ 2 * (hyp.base.w1 * hyp.C.relIndex hyp.U) + 1 := by
    exact_mod_cast hfinal
  calc H1.relIndex (derivedInG M) ≤ 2 * (hyp.base.w1 * hyp.C.relIndex hyp.U) + 1 := this
    _ = 2 * hyp.q * hyp.C.relIndex hyp.U + 1 := by
        change 2 * (hyp.base.w1 * hyp.C.relIndex hyp.U) + 1
          = 2 * hyp.base.w1 * hyp.C.relIndex hyp.U + 1
        ring

/-- **`HC < M'`** (sorry-free): if `HC = M'` then `U ≤ HC = H·C`; decomposing `u = a·b`
(`a ∈ H`, `b ∈ C`) along the normal `H`-factor forces `a ∈ H ∩ U = ⊥`, so `u = b ∈ C`,
contradicting `C ⊊ U` (`C_lt_U`).  The strict inclusion feeds the (11.4)/(11.5) quotient bound
and the `𝒮(HC)`-nonemptiness (`coherent_SOf_HC`). -/
theorem HC_lt_derived [Finite G] {M : Subgroup G} (hyp : Hypothesis M) :
    hyp.HC < derivedInG M := by
  refine lt_of_le_of_ne hyp.HC_le_derived ?_
  intro hEq
  refine (hyp.C_lt_U).not_ge ?_
  intro u hu
  have huHC : u ∈ hyp.HC := by rw [hEq]; exact hyp.base.typeP.U_le hu
  -- decompose `u = h·c` along the normal `H`-factor inside `↥M`
  have hHle : hyp.base.typeP.H ≤ M := hyp.base.typeP.H_le.trans (Subgroup.map_subtype_le _)
  have hCle : hyp.C ≤ M := (hyp.C_le_U.trans hyp.base.typeP.U_le).trans
    (Subgroup.map_subtype_le _)
  have hHn : ((hyp.base.typeP.H).subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hHle).mpr hyp.H_normalized_by_M
  have huM : u ∈ M := (hyp.HC_le_derived.trans (Subgroup.map_subtype_le _)) huHC
  have hmem : (⟨u, huM⟩ : ↥M) ∈
      (hyp.base.typeP.H).subgroupOf M ⊔ hyp.C.subgroupOf M := by
    rw [← Subgroup.subgroupOf_sup hHle hCle]
    exact Subgroup.mem_subgroupOf.mpr huHC
  rw [← SetLike.mem_coe, Subgroup.normal_mul, Set.mem_mul] at hmem
  obtain ⟨a, ha, b, hb, hab⟩ := hmem
  have haH : ((a : ↥M) : G) ∈ hyp.base.typeP.H := Subgroup.mem_subgroupOf.mp ha
  have hbC : ((b : ↥M) : G) ∈ hyp.C := Subgroup.mem_subgroupOf.mp hb
  -- `a = u·b⁻¹ ∈ H ∩ U = ⊥`, so `u = b ∈ C`
  have haU : ((a : ↥M) : G) ∈ hyp.base.typeP.U := by
    have haeq : (a : ↥M) = ⟨u, huM⟩ * (b : ↥M)⁻¹ := by rw [← hab]; group
    have hcoe : ((a : ↥M) : G) = u * ((b : ↥M) : G)⁻¹ := by rw [haeq]; rfl
    rw [hcoe]
    exact Subgroup.mul_mem _ hu (Subgroup.inv_mem _ (hyp.C_le_U hbC))
  have ha1 : ((a : ↥M) : G) = 1 := by
    have := hyp.H_inf_U_eq_bot.le ⟨haH, haU⟩
    rwa [Subgroup.mem_bot] at this
  have hueq : u = ((b : ↥M) : G) := by
    have h1 : (⟨u, huM⟩ : ↥M) = a * b := hab.symm
    have h2 : u = ((a * b : ↥M) : G) := congrArg Subtype.val h1
    rw [h2]
    change ((a : ↥M) : G) * ((b : ↥M) : G) = ((b : ↥M) : G)
    rw [ha1, one_mul]
  rw [hueq]
  exact hbC

/-- **Coherence restricts to a subfamily** (Peterfalvi (5.2) monotonicity).  If `S` is coherent and
`S' ⊆ S` carries a nonzero `A`-supported witness, then `S'` is coherent with the *same* coherent
extension: the isometry (`extension_inner_eq`), `τ`-agreement (`extends_on_supported`) and
`ZIrr`-codomain (`extension_mem_ZIrr`) laws all transport along the `zSpan` / `zSupportedSpan`
monotonicity (`Submodule.span_mono` / `zSupportedSpan_mono_left`); only the `nonzero` witness must
be
re-supplied for `S'`.  This extracts the restriction pattern shared by `coherent_SOf_HC` (`S(HC) ⊆
S(M'')`) and the world-bridge `𝒮(H₀C)`-coherence subset step (`sOf(H₀C) ⊆ sOf(H₀C')`, the (9.11)
`hY` route). -/
noncomputable def isCoherent_of_subset {L : Type*} [Group L] [Fintype L] [Fintype G]
    [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]
    {τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap L G}
    {S S' : Set (ClassFunction L ℂ)} {A : Set L}
    (h : OddOrder.Peterfalvi.S07.IsCoherent τ S A) (hsub : S' ⊆ S)
    (hwit : ∃ φ : ClassFunction L ℂ,
      φ ∈ OddOrder.Peterfalvi.S07.zSupportedSpan (L := L) S' A ∧ φ ≠ 0) :
    OddOrder.Peterfalvi.S07.IsCoherent τ S' A where
  nonzero := hwit
  extension := h.extension
  extension_inner_eq := fun a b ha hb =>
    h.extension_inner_eq a b (Submodule.span_mono hsub ha) (Submodule.span_mono hsub hb)
  extends_on_supported := fun a ha =>
    h.extends_on_supported a (OddOrder.Peterfalvi.S07.zSupportedSpan_mono_left hsub ha)
  extension_mem_ZIrr := fun a ha =>
    h.extension_mem_ZIrr a (Submodule.span_mono hsub ha)

/-- **Peterfalvi (11.8): `S(HC)` is coherent** (sorry-free).  `S(HC) = SOf HC` is the subfamily of
the degree-`w₁` family `S(M'')` cut out by the *larger* kernel condition (`M'' ≤ HC`,
`secondDerived_le_HC`, so `S(HC) ⊆ S(M'')` by kernel-antitonicity), so it inherits the coherent
extension of `S(M'')` (`secondDerived_coherent`) verbatim — the
isometry/`τ`-agreement/`ZIrr`-codomain
laws transport along `zSpan`/`zSupportedSpan` monotonicity.  The one genuinely new input is the
`nonzero` supported witness `ζ̄ − ζ` for a member `ζ ∈ S(HC)`: existence of `ζ` from
`inducedKernelFamily_nonempty_of_commutator_ne_top` at the proper trace `HC ⊊ M'` (`HC_lt_derived`),
its conjugate difference being `A₀`-supported (`mderivSharp_subset_A0`) and nonzero (odd order has
no
real characters, `inducedKernelFamily_hasNoRealCharacters`).  This is the `S(HC)`-coherence input of
the (11.8.6) world-bridge capstone (glued with the `𝒮(H₀C)`-coherence along
`SOf_H0C_eq_SOf_HC_union_sOf`). -/
theorem coherent_SOf_HC [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hyp : Hypothesis M) :
    Nonempty (OddOrder.Peterfalvi.S07.IsCoherent
      hyp.base.tau (hyp.SOf hyp.HC) hyp.base.A0) := by
  classical
  -- coherence of the larger degree-`w₁` family `S(M'')` (5.7)
  obtain ⟨hM''coh⟩ := hyp.secondDerived_coherent hG
  -- `S(HC) ⊆ S(M'')`  (`M'' ≤ HC`, kernel antitone)
  have hsub : hyp.SOf hyp.HC ⊆ hyp.SOf (secondDerivedInAmbient M) := by
    rw [hyp.SOf_eq, hyp.SOf_eq]
    exact OddOrder.Peterfalvi.S08.inducedKernelFamily_antitone
      (Subgroup.subgroupOf_mono M hyp.secondDerived_le_HC)
  -- a genuine member `ζ ∈ S(HC)` from the proper trace `HC ⊊ M'`
  have hHCKnorm : ((hyp.HC.subgroupOf M).subgroupOf ((derivedInG M).subgroupOf M)).Normal :=
    hyp.HC_subgroupOf_normal.subgroupOf _
  have hne : (hyp.HC.subgroupOf M).subgroupOf ((derivedInG M).subgroupOf M) ≠ ⊤ := by
    rw [Ne, Subgroup.subgroupOf_eq_top]
    intro hle
    have hdle : derivedInG M ≤ M := Subgroup.map_subtype_le _
    have hMle : derivedInG M ≤ hyp.HC := fun x hx =>
      Subgroup.mem_subgroupOf.mp
        (hle (show (⟨x, hdle hx⟩ : ↥M) ∈ (derivedInG M).subgroupOf M from hx))
    exact (HC_lt_derived hyp).ne (le_antisymm hyp.HC_le_derived hMle)
  obtain ⟨ζ, hζ⟩ : (hyp.SOf hyp.HC).Nonempty := by
    rw [hyp.SOf_eq]
    exact OddOrder.Peterfalvi.S08.inducedKernelFamily_nonempty_of_commutator_ne_top
      (hyp.base.commutator_quotient_ne_top hG hne)
  rw [hyp.SOf_eq] at hζ
  have hζc := OddOrder.Peterfalvi.S08.inducedKernelFamily_closedUnderConjugate _ hζ
  -- assemble the restricted coherence, reusing `S(M'')`'s coherent extension
  -- (`isCoherent_of_subset`)
  refine ⟨isCoherent_of_subset hM''coh hsub ⟨ζ.conj - ζ, ⟨?_, ?_⟩, ?_⟩⟩
  · -- `ζ̄ − ζ ∈ ℤ[S(HC)]`
    rw [hyp.SOf_eq]
    exact Submodule.sub_mem _ (Submodule.subset_span hζc) (Submodule.subset_span hζ)
  · -- `ζ̄ − ζ` is `A₀`-supported
    exact OddOrder.Peterfalvi.S08.inducedKernelFamily_conjDiff_support
      hyp.base.mderivSharp_subset_A0 hζ
  · -- `ζ̄ − ζ ≠ 0` (odd order ⇒ no real characters)
    intro h
    exact OddOrder.Peterfalvi.S08.inducedKernelFamily_hasNoRealCharacters
      (hyp.base.card_odd_of_isMinimalSimpleOdd hG) _ hζ (sub_eq_zero.mp h)

/-- **(9.11) `hY`-route subset step**: the capstone's `𝒮(H₀C)`-coherence input (`hY`) follows from
a supplied (9.11) coherence datum for the smaller-kernel family `𝒮(H₀C')` (the honest Coq
`Ptype_core_coherence` induction target) by `isCoherent_of_subset` along `𝒮(H₀C) ⊆
𝒮(H₀C')`, once a nonzero `A₀`-supported `𝒮(H₀C)` witness is supplied.  This wires the (9.11) result
to the world-bridge capstone `coherent_SOf_H0C_of_glued`'s `hY` parameter.

Two named obligations remain: `hcoh` = coherent(`𝒮(H₀C')`) (the (9.11) induction port over the
sorry-free S07/S08 engines — `coherent_subset_of_constant_degree` base + `coherentPairChain` /
`xAdjoinStepW` extension), and `hwit` = a nonzero `𝒮(H₀C)` witness (nonemptiness via
`S11.caseA_exists_irreducible_sOf_H0C` + a Clifford case split).  See issue 1019 update⁴⁵/⁴⁶. -/
noncomputable def coherent_sOf_H0C_of_coherent_sOf_H0Cprime [Finite G] {M : Subgroup G}
    (hyp : Hypothesis M)
    (hcoh : OddOrder.Peterfalvi.S07.IsCoherent hyp.base.tau
      (OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime) hyp.base.A0)
    (hwit : ∃ φ : ClassFunction ↥M ℂ,
      φ ∈ OddOrder.Peterfalvi.S07.zSupportedSpan
        (OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0C) hyp.base.A0 ∧ φ ≠ 0) :
    OddOrder.Peterfalvi.S07.IsCoherent hyp.base.tau
      (OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0C) hyp.base.A0 :=
  isCoherent_of_subset hcoh hyp.sOf_H0C_subset_sOf_H0Cprime hwit

/-- **`S(HC)` is a subfamily of `SHCSet = S(M'')` = the degree-`w₁` irreducibles** (world-bridge
`S₁`-identification): every member of `S(HC)` kills `HC ⊇ M''`, so it kills `M''` and lies in
`S(M'')`, which is exactly the degree-`w₁` irreducible family `SHCSet` (`SOf_secondDerived_eq`).
Concretely `S(HC) ⊆ S(M'')` (kernel-antitone, `M'' ≤ HC`) and `S(M'') = SHCSet`.  This exhibits the
world-bridge `S₁ = S(HC)` as the uniform-degree-`q` part and lets the (11.8.6) capstone reuse the
`SHCSet` orthogonality/generation infrastructure on `S(HC)`. -/
theorem SOf_HC_subset_SHCSet [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hyp : Hypothesis M) :
    hyp.SOf hyp.HC ⊆ hyp.base.SHCSet := by
  have hsub : hyp.SOf hyp.HC ⊆ hyp.SOf (secondDerivedInAmbient M) := by
    rw [hyp.SOf_eq, hyp.SOf_eq]
    exact OddOrder.Peterfalvi.S08.inducedKernelFamily_antitone
      (Subgroup.subgroupOf_mono M hyp.secondDerived_le_HC)
  rwa [hyp.SOf_secondDerived_eq hG] at hsub

/-- **World-bridge source orthogonality (pairwise)**: a member of `S(HC)` is orthogonal to a member
of `𝒮(H₀C) = sOf`.  Both are `Ind_{HU}`-members of the pairwise-orthogonal §10 family
`inducedKernelFamily HU` (`sOf ⊆ SOf` via `sOf_subset_SOf`), and they are **distinct**: an
`S(HC)`-source `θ` kills `H` (`H ≤ HC ≤ Ker θ`), while an `𝒮(H₀C)`-source `χ'` lies in `𝒳`
(`H ⊄ Ker χ'`).  If `Ind θ = Ind χ'` then `θ, χ'` are `M`-conjugate (`induce_eq_induce_iff_conj`),
and `H ⊴ M` conjugation-invariance (`subsetCharacterKernel_conjBy_of_invariant`, via
`hSubgroupOfM_normal`) transports `H ≤ Ker θ` to `H ≤ Ker χ'` — contradicting `χ' ∈ 𝒳`.  This is the
`hsrc_ortho` input of the (11.8.6) world-bridge union-glue engine. -/
theorem SOf_HC_inner_sOf_H0C_eq_zero [Finite G] {M : Subgroup G} (hyp : Hypothesis M)
    {x y : ClassFunction ↥M ℂ} (hx : x ∈ hyp.SOf hyp.HC)
    (hy : y ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0C) :
    ClassFunction.inner x y = 0 := by
  classical
  have hHU : OddOrder.Peterfalvi.S11.huSub hyp.s11Setup = (derivedInG M).subgroupOf M :=
    OddOrder.Peterfalvi.S11.huSub_eq_derivedInG_subgroupOf hyp.s11Setup
  -- both sit in the pairwise-orthogonal `inducedKernelFamily HU`
  have hxIKF : x ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily
      (OddOrder.Peterfalvi.S11.huSub hyp.s11Setup) (hyp.HC.subgroupOf M) := by
    have h := hx; rw [hyp.SOf_eq, ← hHU] at h; exact h
  have hyIKF : y ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily
      (OddOrder.Peterfalvi.S11.huSub hyp.s11Setup) (hyp.H0C.subgroupOf M) := by
    have h := hyp.sOf_subset_SOf hyp.H0C hy; rw [hyp.SOf_eq, ← hHU] at h; exact h
  refine OddOrder.Peterfalvi.S08.inducedKernelFamily_pairwise_orthogonal hxIKF hyIKF ?_
  -- distinctness `x ≠ y`
  intro hxy
  -- `H` realized inside `HU`
  have hhin : OddOrder.Peterfalvi.S11.hInHu hyp.s11Setup
      = (hyp.H.subgroupOf M).subgroupOf (OddOrder.Peterfalvi.S11.huSub hyp.s11Setup) := by
    change (hyp.s11Setup.typeP.H.subgroupOf M).subgroupOf _
        = (hyp.base.typeP.H.subgroupOf M).subgroupOf _
    rw [hyp.setup_typeP_eq]
  -- `x`-source `θ` kills `hInHu` (`H ≤ HC`)
  obtain ⟨θ, hθne, hθker, hxeq⟩ := hxIKF
  have hHθ : (OddOrder.Peterfalvi.S11.hInHu hyp.s11Setup :
      Set ↥(OddOrder.Peterfalvi.S11.huSub hyp.s11Setup)) ⊆
      OddOrder.Peterfalvi.S03.characterKernel
        (θ : ClassFunction ↥(OddOrder.Peterfalvi.S11.huSub hyp.s11Setup) ℂ) := by
    rw [hhin]
    refine subset_trans (SetLike.coe_subset_coe.mpr (Subgroup.subgroupOf_mono _
      (Subgroup.subgroupOf_mono M (le_sup_left : hyp.H ≤ hyp.HC)))) hθker
  -- `y`-source `χ'` lies in `𝒳`: `¬ hInHu ⊆ Ker χ'`
  obtain ⟨χ', hχ'xiOf, hyeq⟩ := hy
  have hχ'xi : ¬ ((OddOrder.Peterfalvi.S11.hInHu hyp.s11Setup :
      Set ↥(OddOrder.Peterfalvi.S11.huSub hyp.s11Setup)) ⊆
      OddOrder.Peterfalvi.S03.characterKernel
        (χ' : ClassFunction ↥(OddOrder.Peterfalvi.S11.huSub hyp.s11Setup) ℂ)) := hχ'xiOf.1
  -- `Ind θ = Ind χ'`, so the sources are `M`-conjugate
  rw [OddOrder.Peterfalvi.S11.induceHU_eq_induce] at hyeq
  have heqInd := hxeq.symm.trans (hxy.trans hyeq)
  obtain ⟨g, hg⟩ := (induce_eq_induce_iff_conj θ χ').mp heqInd
  -- `hInHu` is `M`-conjugation-invariant (`H ⊴ M`)
  have hAinv : ∀ a ∈ (OddOrder.Peterfalvi.S11.hInHu hyp.s11Setup :
      Set ↥(OddOrder.Peterfalvi.S11.huSub hyp.s11Setup)),
      ClassFunction.conjByMulEquiv g a ∈
        (OddOrder.Peterfalvi.S11.hInHu hyp.s11Setup :
          Set ↥(OddOrder.Peterfalvi.S11.huSub hyp.s11Setup)) := by
    intro a ha
    simp only [SetLike.mem_coe] at ha ⊢
    rw [OddOrder.Peterfalvi.S11.hInHu, Subgroup.mem_subgroupOf] at ha ⊢
    rw [ClassFunction.conjByMulEquiv_apply]
    exact (OddOrder.Peterfalvi.S11.hSubgroupOfM_normal hyp.s11Setup).conj_mem _ ha g
  -- transport `hInHu ⊆ Ker θ` to `hInHu ⊆ Ker (conjBy g θ) = Ker χ'`
  have hHχ' : (OddOrder.Peterfalvi.S11.hInHu hyp.s11Setup :
      Set ↥(OddOrder.Peterfalvi.S11.huSub hyp.s11Setup)) ⊆
      OddOrder.Peterfalvi.S03.characterKernel
        (ClassFunction.conjBy g
          (θ : ClassFunction ↥(OddOrder.Peterfalvi.S11.huSub hyp.s11Setup) ℂ)) :=
    OddOrder.Peterfalvi.S11.subsetCharacterKernel_conjBy_of_invariant g _ _ hAinv hHθ
  rw [← IrreducibleCharacter.coe_conjBy, hg] at hHχ'
  exact hχ'xi hHχ'

/-- **World-bridge source orthogonality (span level)** — the `hsrc_ortho` input of the (11.8.6)
union-glue engine `coherentUnion_of_glued_of_generator_mixed_inner_eq_withDiagonal`:
`ℤ[S(HC)] ⊥ ℤ[𝒮(H₀C)]`.  Bilinear extension of the pairwise `SOf_HC_inner_sOf_H0C_eq_zero`
(double `span_induction`, additivity + `ℤ`-linearity of the inner product). -/
theorem span_inner_SOf_HC_sOf_H0C_eq_zero [Finite G] {M : Subgroup G} (hyp : Hypothesis M)
    {u v : ClassFunction ↥M ℂ}
    (hu : u ∈ Submodule.span ℤ (hyp.SOf hyp.HC))
    (hv : v ∈ Submodule.span ℤ (OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0C)) :
    ClassFunction.inner u v = 0 := by
  classical
  have hright : ∀ x ∈ hyp.SOf hyp.HC,
      ∀ w ∈ Submodule.span ℤ (OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0C),
      ClassFunction.inner x w = 0 := by
    intro x hx w hw
    induction hw using Submodule.span_induction with
    | mem y hy => exact SOf_HC_inner_sOf_H0C_eq_zero hyp hx hy
    | zero => rw [ClassFunction.inner_zero_right]
    | add y z _ _ ihy ihz => rw [ClassFunction.inner_add_right, ihy, ihz, add_zero]
    | smul a y _ ih =>
        rw [← Int.cast_smul_eq_zsmul ℂ a y,
          OddOrder.RepresentationTheory.inner_smul_right, ih, mul_zero]
  induction hu using Submodule.span_induction with
  | mem x hx => exact hright x hx v hv
  | zero => rw [ClassFunction.inner_zero_left]
  | add x z _ _ ihx ihz => rw [ClassFunction.inner_add_left, ihx, ihz, add_zero]
  | smul a x _ ih =>
      rw [← Int.cast_smul_eq_zsmul ℂ a x, ClassFunction.inner_smul_left, ih, mul_zero]

/-- **Peterfalvi (11.5), reverse inclusion `HC ⊆ M''`, parametrized on the (11.3) non-coherence**
(issue 1025): the coherence content of (11.5).  Since `M'/M''` is abelian, `S(M'')` is coherent by
(5.7); the quotient bound (11.4) together with (11.1)/(9.6) then forces `M'' = HC`.  The (11.3)
non-coherence `hnc` of `𝒮(H₀C)` is a hypothesis (see `coherent_quotient_bound_of_noncoherent`;
the former legacy wrapper `HC_le_secondDerived` at the sorried (11.3) is retired, issue 9087). -/
theorem HC_le_secondDerived_of_noncoherent [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hyp : Hypothesis M)
    (hnc : ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent
      hyp.base.tau (hyp.SOf hyp.H0C) hyp.base.A0))
    (htype : IsTypeIII M ∨ IsTypeIV M) :
    hyp.HC ≤ secondDerivedInAmbient M := by
  classical
  rw [← Subgroup.relIndex_eq_one]
  -- `HC < M'` (else `U ≤ HC` forces `U ≤ C`, contradicting `C ⊊ U`)
  have hHCltM' : hyp.HC < derivedInG M := HC_lt_derived hyp
  -- `(11.4)` at `H₁ := M''` with `(5.7)`
  have hM''lt : secondDerivedInAmbient M < derivedInG M :=
    lt_of_le_of_lt hyp.secondDerived_le_HC hHCltM'
  have h114 := coherent_quotient_bound_of_noncoherent _hG hyp le_normalizer_secondDerived hM''lt
    (hyp.secondDerived_coherent _hG) hnc
  -- tower `|M':M''| = X·|U:C|`
  set X := (secondDerivedInAmbient M).relIndex hyp.HC with hX
  set v := hyp.C.relIndex hyp.U with hv
  have htower : (secondDerivedInAmbient M).relIndex (derivedInG M) = X * v := by
    rw [hX, hv, ← hyp.HC_relIndex_derived]
    exact (Subgroup.relIndex_mul_relIndex (secondDerivedInAmbient M) hyp.HC (derivedInG M)
      hyp.secondDerived_le_HC hyp.HC_le_derived).symm
  rw [htower] at h114
  -- `v ≥ 2` from `C ⊊ U`
  have hvpos : v ≠ 0 := by
    intro h0
    have h2 : Nat.card ↥hyp.C * v = Nat.card ↥hyp.U := by
      have := Subgroup.card_mul_index (hyp.C.subgroupOf hyp.U)
      rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (show hyp.C ≤ hyp.U from hyp.C_le_U)).toEquiv] at this
    rw [h0, Nat.mul_zero] at h2
    exact (Nat.card_pos (α := ↥hyp.U)).ne' h2.symm
  have hvne1 : v ≠ 1 := by
    intro h1
    rw [hv, Subgroup.relIndex_eq_one] at h1
    exact hyp.C_lt_U.not_ge h1
  have hv2 : 2 ≤ v := by omega
  -- `X ≤ 2q`
  have hX2q : X ≤ 2 * hyp.q := by
    by_contra hgt
    push Not at hgt
    have hge : 2 * hyp.q + 1 ≤ X := hgt
    have h1 : (2 * hyp.q + 1) * v ≤ X * v := Nat.mul_le_mul_right v hge
    have h2 : 2 * hyp.q * v + v ≤ 2 * hyp.q * v + 1 := by
      calc 2 * hyp.q * v + v = (2 * hyp.q + 1) * v := by ring
        _ ≤ X * v := h1
        _ ≤ 2 * hyp.q * v + 1 := h114
    omega
  -- `q ∣ X − 1`, `X` and `q` odd ⟹ `X = 1`
  have hdvd : hyp.q ∣ X - 1 := hyp.q_dvd_secondDerived_relIndex_HC_sub_one _hG htype
  have hXodd : Odd X := by
    refine _hG.odd.of_dvd_nat ?_
    calc X ∣ Nat.card ↥hyp.HC := Subgroup.relIndex_dvd_card _ _
      _ ∣ Nat.card G := Subgroup.card_subgroup_dvd_card hyp.HC
  have hqodd : Odd hyp.q := by
    refine _hG.odd.of_dvd_nat ?_
    calc hyp.q = Nat.card ↥hyp.base.typeP.W1 := rfl
      _ ∣ Nat.card G := Subgroup.card_subgroup_dvd_card hyp.base.typeP.W1
  have hqpos : 0 < hyp.q := hqodd.pos
  obtain ⟨k, hk⟩ := hdvd
  have hXpos : 0 < X := hXodd.pos
  rw [Nat.odd_iff] at hXodd hqodd
  rcases Nat.lt_or_ge k 2 with hk2 | hk2
  · interval_cases k
    · omega
    · rw [Nat.mul_one] at hk
      omega
  · exfalso
    have h3 : hyp.q * 2 ≤ hyp.q * k := Nat.mul_le_mul_left hyp.q hk2
    have h4 : 2 * hyp.q ≤ X - 1 := by
      rw [hk]
      omega
    omega

/-- **Peterfalvi (11.5), parametrized on (11.3) non-coherence** (issue 1025): `M'' = HC` from the
reverse `HC_le_secondDerived_of_noncoherent hnc` and the unconditional `secondDerived_le_HC`. -/
theorem secondDerived_eq_HC_of_noncoherent [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hyp : Hypothesis M)
    (hnc : ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent
      hyp.base.tau (hyp.SOf hyp.H0C) hyp.base.A0))
    (htype : IsTypeIII M ∨ IsTypeIV M) :
    secondDerivedInAmbient M = hyp.HC :=
  le_antisymm hyp.secondDerived_le_HC (HC_le_secondDerived_of_noncoherent _hG hyp hnc htype)

/-- **Peterfalvi (11.6), `C = U'`, parametrized on the (11.3) non-coherence** (issue 9087):
`U' ≤ C` is (8.5.b) (`derivedU_le_C`); conversely `C ≤ HC = M'' ≤ H ⊔ U'` ((11.5) +
`secondDerived_le_H_sup_derivedU`), and an `H ⊔ U'`-element of `U` splits as `h·u'` with
`h ∈ H ⊓ U = ⊥`, so `C ≤ U'`.  The (11.3) non-coherence `hnc` and the type disjunction
`htype` are explicit hypotheses (instantiate with `S_H0C_not_coherent_unconditional` /
`isTypeIIIorIV_unconditional` downstream). -/
theorem C_eq_derivedU [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hyp : Hypothesis M)
    (hnc : ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent
      hyp.base.tau (hyp.SOf hyp.H0C) hyp.base.A0))
    (htype : IsTypeIII M ∨ IsTypeIV M) :
    hyp.C = derivedInG hyp.base.typeP.U := by
  refine le_antisymm ?_ hyp.derivedU_le_C
  intro c hc
  have hcM'' : c ∈ secondDerivedInAmbient M := by
    rw [secondDerived_eq_HC_of_noncoherent hG hyp hnc htype]
    exact Subgroup.mem_sup_right hc
  have hcHU' : c ∈ hyp.base.typeP.H ⊔ derivedInG hyp.base.typeP.U :=
    hyp.secondDerived_le_H_sup_derivedU hcM''
  -- split `c = h·u'` and cancel the `H`-part inside `U`
  have hHle : hyp.base.typeP.H ≤ M := hyp.base.typeP.H_le.trans (Subgroup.map_subtype_le _)
  have hU'le : derivedInG hyp.base.typeP.U ≤ M :=
    ((Subgroup.map_subtype_le _).trans hyp.base.typeP.U_le).trans (Subgroup.map_subtype_le _)
  obtain ⟨h, hh, u', hu', hceq⟩ :=
    exists_mul_of_mem_sup_of_normalized hHle hU'le hyp.H_normalized_by_M hcHU'
  have hhU : h ∈ hyp.base.typeP.U := by
    have h1 : h = c * u'⁻¹ := by rw [hceq]; group
    rw [h1]
    exact Subgroup.mul_mem _ (hyp.C_le_U hc)
      (Subgroup.inv_mem _ ((Subgroup.map_subtype_le _) hu'))
  have hh1 : h = 1 := by
    have := hyp.H_inf_U_eq_bot.le ⟨hh, hhU⟩
    rwa [Subgroup.mem_bot] at this
  rw [hceq, hh1, one_mul]
  exact hu'

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (10.10), case (a) of Definition (8.7)** ("If case (a) of Definition (8.7)
holds, then `S` is coherent by Theorem (6.8)"): for a type-V maximal `M` whose kernel sharp
set `H^# = (M')^#` is a TI-subset, the (10.1) family `S = hyp.Sset` is coherent for the §10
Dade isometry `hyp.tau` on the support `A₀(M)`.

Assembly: the sorry-free (6.8) capstone `sibleySetup_is_coherent` applied to the case-(a)
Sibley datum `typeVSibleyDadeHypothesis` gives coherence for the Sibley–Dade map on the
`(M')^#`-support (its `S`-field is definitionally `inducedFamily M = hyp.Sset`);
`IsCoherent.congrMap` re-targets it to `hyp.tau` along the (2.11)+(2.5) agreement
`typeVSibleyDadeHypothesis_tau_agree`; `S07.isCoherent_of_supportedSpan_le` enlarges the support
to `A₀(M)` — members `Ind_{M'}^M θ` vanish off `M'` and `1 ∉ A₀`, so an `A₀`-supported
`ℤ[S]`-combination is already `(M')^#`-supported — with the `A₀`-witness `ζ̄ − ζ` (a member
exists by (10.2), and odd order admits no real characters). -/
noncomputable def typeV_caseA_coherence [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hyp : OddOrder.Peterfalvi.S12.Hypothesis M)
    (dV : TypeVData M)
    (hTI : IsTISubset (sharpSubgroup hyp.typeP.H)
      (Subgroup.normalizer (hyp.typeP.H : Set G))) :
    OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Sset hyp.A0 := by
  classical
  -- the (6.8) coherence on the `(M')^#`-support, for the Sibley–Dade map
  have c0 := OddOrder.Peterfalvi.S08.sibleySetup_is_coherent
    (OddOrder.Peterfalvi.S12.typeVSibleyDadeHypothesis hG hyp dV hTI)
  -- re-target to `hyp.tau` along the (2.11)+(2.5) agreement (the family and support are
  -- definitionally `hyp.Sset` and the `(M')^#`-support)
  have c1 : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Sset
      (OddOrder.Peterfalvi.S04.supportInSubgroup
        (OddOrder.Peterfalvi.S08.sharpImage ((derivedInG M).subgroupOf M)) M) :=
    c0.congrMap (fun φ hφ =>
      OddOrder.Peterfalvi.S12.typeVSibleyDadeHypothesis_tau_agree hG hyp dV hTI hφ.2)
  refine OddOrder.Peterfalvi.S07.isCoherent_of_supportedSpan_le c1 ?_ ?_
  · -- `ℤ[S, A₀] ⊆ ℤ[S, (M')^#]`: members vanish off `M'`, and `1 ∉ A₀`
    have hHnorm : ((derivedInG M).subgroupOf M).Normal := by
      rw [show (derivedInG M).subgroupOf M = commutator ↥M by
        rw [derivedInG, Subgroup.subgroupOf,
          Subgroup.comap_map_eq_self_of_injective M.subtype_injective]]
      infer_instance
    rintro φ ⟨hφspan, hφsupp⟩
    refine ⟨hφspan, ?_⟩
    have hsuppH : φ.support ⊆ {x : ↥M | x ∈ (derivedInG M).subgroupOf M} := by
      have hle' : OddOrder.Peterfalvi.S07.zSpan (L := ↥M) hyp.Sset ≤
          (ClassFunction.supportedSubmodule (G := ↥M) (k := ℂ)
            {x : ↥M | x ∈ (derivedInG M).subgroupOf M}).restrictScalars ℤ := by
        refine Submodule.span_le.mpr (fun s hs => ?_)
        obtain ⟨θ, -, rfl⟩ := hs
        simp only [SetLike.mem_coe, Submodule.restrictScalars_mem,
          ClassFunction.mem_supportedSubmodule]
        intro x hx
        rw [ClassFunction.mem_support] at hx
        by_contra hxH
        exact hx (ClassFunction.induce_apply_eq_zero_of_not_mem_normal _ _ hxH)
      exact (ClassFunction.mem_supportedSubmodule).mp (hle' hφspan)
    intro x hx
    have hxA0 : x ∈ hyp.A0 := hφsupp hx
    have hx1 : x ≠ 1 := fun h => hyp.one_notMem_A0 (h ▸ hxA0)
    exact ⟨Subgroup.mem_map.mpr ⟨x, hsuppH hx, rfl⟩,
      fun hc => hx1 (Subtype.ext (Set.mem_singleton_iff.mp hc))⟩
  · -- the `A₀`-witness `ζ̄ − ζ` for a (10.2) member `ζ`
    have hHall := OddOrder.Peterfalvi.S12.typePData_W1_hall_coprime hG hyp.maximal
      (hyp.bgTypeP hG) hyp.typeP
    obtain ⟨ζ, hζmem, -, -⟩ :=
      OddOrder.Peterfalvi.S12.exists_zeta_in_inducedFamily_degree_w1 hyp.typeP hG.odd hHall
    have hζSK : ζ ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily
        ((derivedInG M).subgroupOf M) ⊥ := by
      obtain ⟨θ, hθne, hζeq⟩ := hζmem
      refine ⟨θ, hθne, ?_, hζeq⟩
      intro y hy
      have hy1 : y = 1 :=
        Subtype.ext (Subgroup.mem_bot.mp (Subgroup.mem_subgroupOf.mp hy))
      rw [hy1]
      exact OddOrder.Peterfalvi.S03.one_mem_characterKernel _
    have hζc : ζ.conj ∈ hyp.Sset :=
      OddOrder.Peterfalvi.S12.inducedFamily_closedUnderConjugate M hζmem
    refine ⟨ζ.conj - ζ, ⟨?_, ?_⟩, ?_⟩
    · exact Submodule.sub_mem _ (Submodule.subset_span hζc) (Submodule.subset_span hζmem)
    · exact OddOrder.Peterfalvi.S08.inducedKernelFamily_conjDiff_support
        hyp.mderivSharp_subset_A0 hζSK
    · intro h
      exact OddOrder.Peterfalvi.S08.inducedKernelFamily_hasNoRealCharacters
        (hyp.card_odd_of_isMinimalSimpleOdd hG) _ hζSK (sub_eq_zero.mp h)

end OddOrder.Peterfalvi.S13


