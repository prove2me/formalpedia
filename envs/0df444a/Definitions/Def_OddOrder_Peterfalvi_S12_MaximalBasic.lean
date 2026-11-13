-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S12_MaximalBasic
-- name    : OddOrder_Peterfalvi_S12_MaximalBasic
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T13:12:38.060021+00:00
-- url     : https://prove2.me/theorems/e240bcb7-fbab-44a9-a8d7-368e7026cda1
-- title:
--   Peterfalvi (10.8): coherent-extension norm bounds for maximal types III, IV, V
-- statement:
--   Formalizes input estimates for Peterfalvi (10.8): norm and sum bounds for the coherent extension $\zeta^{\tau_1}$ under Hypothesis (10.1).
--
--   Main declarations: `Hypothesis.inner_tau1_zeta_self_eq_one` (`‖ζ^{τ₁}‖² = 1`); `Hypothesis.sum_zeta_tau1_normSq_ge_card` (The `(10.6.b)`-summed bound for `ζ^{τ₁}`); `Hypothesis.chiRhoNormSq_zeta_le_line83` (Peterfalvi (10.8), line 83); `Hypothesis.mem_restricted_dadeSupport_of_coprime` (Coprime-order elements of the full Dade support lie in the `A(M)`-restricted support).
--
--   The bundle also proves 11 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S12_MaximalBasic.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S12_MaximalBasic.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S12_Section9Counts
import Definitions.Def_OddOrder_Peterfalvi_S12_TypeIIFrobenius
import Definitions.Def_OddOrder_Peterfalvi_S09_CertificateDischarge

namespace OddOrder.Peterfalvi.S12

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

/-- **Closing arithmetic contradiction of Peterfalvi (10.8)** — the numerical heart of the
non-coherence proof, isolated from the character machinery.

The structural facts derived (under the *coherence* assumption) for the Type-II partner `S` are:
* `w₁ ≥ 3` and the Frobenius bound `|U| ≥ 2w₂+1 ≥ 7` (since `UW₂` is Frobenius and `w₂ ≥ 3`);
* the lower bound `|M'| ≥ (2w₁+1)·w₂`, from `|M'/M''| ≥ 2w₁+1` (the odd Frobenius group
  `(M'/M'')⋊W₁`, Peterfalvi (8.4.d)) and `|M''| ≥ w₂`.

The `(7.5)`/`(7.8.b)`/`(10.6.b)` norm-counting estimate, after the `G₁ ⊆ (H#)^G ∪ V^G` bound,
yields `w₁w₂/|M'| > 1 − 1/w₁ − 1/|U|`.  Its right side exceeds `1 − 1/3 − 1/7 > 1/2`, forcing
`|M'| < 2w₁w₂`; this contradicts `|M'| ≥ (2w₁+1)w₂ = 2w₁w₂ + w₂`.  Pure arithmetic over `ℚ`. -/
theorem typeII_noncoherence_arithmetic
    {w₁ w₂ u Mp : ℕ} (hw1 : 3 ≤ w₁) (hu : 7 ≤ u) (hw2 : 1 ≤ w₂)
    (hMp : (2 * w₁ + 1) * w₂ ≤ Mp)
    (hbound : (1 : ℚ) - 1 / (w₁ : ℚ) - 1 / (u : ℚ) < (w₁ : ℚ) * (w₂ : ℚ) / (Mp : ℚ)) :
    False := by
  have hw1q : (3 : ℚ) ≤ (w₁ : ℚ) := by exact_mod_cast hw1
  have huq : (7 : ℚ) ≤ (u : ℚ) := by exact_mod_cast hu
  have hw2q : (1 : ℚ) ≤ (w₂ : ℚ) := by exact_mod_cast hw2
  have hMppos : 0 < Mp := lt_of_lt_of_le (Nat.mul_pos (by omega) (by omega)) hMp
  have hMpq : (0 : ℚ) < (Mp : ℚ) := by exact_mod_cast hMppos
  -- `1/w₁ ≤ 1/3` and `1/u ≤ 1/7`, so the coherence bound exceeds `1 − 1/3 − 1/7 > 1/2`.
  have h1 : 1 / (w₁ : ℚ) ≤ 1 / 3 := one_div_le_one_div_of_le (by norm_num) hw1q
  have h2 : 1 / (u : ℚ) ≤ 1 / 7 := one_div_le_one_div_of_le (by norm_num) huq
  have hhalf : (1 : ℚ) / 2 < (w₁ : ℚ) * (w₂ : ℚ) / (Mp : ℚ) := by
    have h112 : (1 : ℚ) - 1 / 3 - 1 / 7 > 1 / 2 := by norm_num
    linarith
  -- Clear the denominator: `Mp < 2·w₁w₂`.
  have hhalf' : (1 : ℚ) / 2 * (Mp : ℚ) < (w₁ : ℚ) * (w₂ : ℚ) := (lt_div_iff₀ hMpq).mp hhalf
  -- The lower bound `(2w₁+1)w₂ = 2·w₁w₂ + w₂ ≤ Mp` contradicts it.
  have hMpcast : 2 * ((w₁ : ℚ) * (w₂ : ℚ)) + (w₂ : ℚ) ≤ (Mp : ℚ) := by
    have : ((2 * w₁ + 1) * w₂ : ℚ) ≤ (Mp : ℚ) := by exact_mod_cast hMp
    linarith
  linarith

/-- **Peterfalvi (10.8), structural lower bound** `(2w₁+1)·w₂ ≤ |M'|` (the `hMp` input to the
non-coherence arithmetic `typeII_noncoherence_arithmetic`).

Peterfalvi's "By (8.4.d), `(M'/M'')⋊W₁` is a Frobenius group of odd order; it follows that
`|M':M''| ≥ 2w₁+1`": the cyclic Hall complement `W₁` acts on the abelian section `M'/M''`
fixed-point-freely (its fixed points on `M'` are `C_{M'}(x) = W₂` by `TypePData.centralizer_W1`, and
`W₂ ⊆ M''` by `TypePData.W2_le`), so `w₁ ∣ |M':M''| − 1`
(`S08.caseB_W1_dvd_index_of_centralizer_le`,
the `W₁`-conjugation action on `H = M'.subgroupOf M` with `M'' = ⁅H,H⁆`); with all orders odd and
`M'' < M'`
    (`M'` solvable nontrivial, `Group.IsSolvable.commutator_lt_top_of_nontrivial`) this forces
`|M':M''| ≥ 2w₁+1` (`S08.two_mul_add_one_le_of_odd_dvd`).  Then `|M'| = |M''|·|M':M''| ≥ w₂·(2w₁+1)`
(`Subgroup.index_mul_card`) since `w₂ = |W₂| ≤ |M''|` (`W₂ ⊆ M''`).  Genuine group theory,
**proven**; the one upstream citation is `typePData_W1_hall_coprime`, the shared §10 type-P
coprimality. -/
theorem Hypothesis.card_derived_ge [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M) :
    (2 * hyp.w1 + 1) * hyp.w2 ≤ Nat.card ↥(derivedInG M) := by
  have := hyp.finiteG
  classical
  have hM'le : derivedInG M ≤ M := Subgroup.map_subtype_le _
  -- `derivedInG K = ⁅K, K⁆` (the commutator of `K` with itself in `G`).
  have hderiv : ∀ K : Subgroup G, derivedInG K = ⁅K, K⁆ := fun K => by
    rw [derivedInG, commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  -- `H = M'` realised inside `↥M`; normal, `H.map subtype = M'`, `⁅H,H⁆.map subtype = M''`.
  set H : Subgroup ↥M := (derivedInG M).subgroupOf M with hHdef
  have hKcomm : H = _root_.commutator ↥M := by
    rw [hHdef, derivedInG, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
  have hHnorm : H.Normal := by rw [hKcomm]; infer_instance
  have hHmap : H.map M.subtype = derivedInG M := by
    rw [hHdef, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hM'le]
  have hmapcomm : (⁅H, H⁆ : Subgroup ↥M).map M.subtype = secondDerivedInAmbient M := by
    rw [Subgroup.map_commutator, hHmap, ← hderiv]; rfl
  have hW2leM' : hyp.typeP.W2 ≤ derivedInG M :=
    (hyp.typeP.W2_le.trans inf_le_right).trans (Subgroup.map_subtype_le _)
  -- `↥H` is solvable and nontrivial, so `M'' = ⁅H,H⁆ < H` and the index is `> 1`.
  have : Group.IsSolvable ↥M := hG.isSolvable_of_mem_maximalSubgroups hyp.maximal
  have hHsolv : Group.IsSolvable ↥H :=
    Group.isSolvable_of_isSolvable_injective (f := H.subtype) (Subgroup.subtype_injective H)
  have hHnt : Nontrivial ↥H := by
    have h1 : 1 < Nat.card ↥H := by
      rw [hHdef, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hM'le).toEquiv]
      calc 1 < Nat.card ↥hyp.typeP.W2 :=
            (Subgroup.one_lt_card_iff_ne_bot _).mpr hyp.typeP.W2_nontrivial
        _ ≤ Nat.card ↥(derivedInG M) := Subgroup.card_le_of_le hW2leM'
    exact Finite.one_lt_card_iff_nontrivial.mp h1
  -- the FPF divisibility `w₁ ∣ |H : ⁅H,H⁆| − 1`.
  have hcardW1 : Nat.card ↥(hyp.W1.subgroupOf M) = hyp.w1 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hyp.typeP.W1_le).toEquiv
  have hcop : Nat.Coprime (Nat.card ↥(hyp.W1.subgroupOf M)) (Nat.card ↥H) := by
    rw [hcardW1, hHdef, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hM'le).toEquiv]
    exact (typePData_W1_hall_coprime hG hyp.maximal (hyp.bgTypeP hG) hyp.typeP).symm
  have hdvd : Nat.card ↥(hyp.W1.subgroupOf M) ∣ (_root_.commutator ↥H).index - 1 := by
    refine OddOrder.Peterfalvi.S08.caseB_W1_dvd_index_of_centralizer_le (hyp.W1.subgroupOf M) hcop
      (_root_.commutator ↥H) ?_
    intro a ha x hcomm
    have haW1 : ((↑(↑a : ↥M) : G)) ∈ hyp.W1 := Subgroup.mem_subgroupOf.mp a.2
    have hane : ((↑(↑a : ↥M) : G)) ≠ 1 := fun h => ha (Subtype.ext (Subtype.ext h))
    have hxM' : ((↑(↑x : ↥M) : G)) ∈ derivedInG M :=
      Subgroup.mem_subgroupOf.mp (hHdef ▸ x.2)
    have hcommG : ((↑(↑x : ↥M) : G)) * ((↑(↑a : ↥M) : G))
        = ((↑(↑a : ↥M) : G)) * ((↑(↑x : ↥M) : G)) := by
      simpa using (congrArg (fun t : ↥M => (↑t : G)) hcomm).symm
    have hxW2 : ((↑(↑x : ↥M) : G)) ∈ hyp.typeP.W2 := by
      rw [← hyp.typeP.centralizer_W1 _ haW1 hane]
      exact Subgroup.mem_inf.mpr ⟨hxM', Subgroup.mem_centralizer_singleton_iff.mpr hcommG⟩
    have key : (↑x : ↥M) ∈ (⁅H, H⁆ : Subgroup ↥M) := by
      refine (Subgroup.mem_map_iff_mem M.subtype_injective).mp ?_
      rw [hmapcomm]
      exact (hyp.typeP.W2_le.trans inf_le_right) hxW2
    exact OddOrder.Peterfalvi.S08.commutator_subgroupOf_self H ▸ Subgroup.mem_subgroupOf.mpr key
  -- `|H : ⁅H,H⁆| ≥ 2w₁ + 1` (odd Frobenius bound).
  have hidxgt : 1 < (_root_.commutator ↥H).index := by
    have hne1 : (_root_.commutator ↥H).index ≠ 1 := by
      rw [Ne, Subgroup.index_eq_one]
      exact (Group.IsSolvable.commutator_lt_top_of_nontrivial ↥H).ne
    have hpos : (_root_.commutator ↥H).index ≠ 0 :=
      Subgroup.index_ne_zero_of_finite
    omega
  have hidxge : 2 * hyp.w1 + 1 ≤ (_root_.commutator ↥H).index := by
    have hw1odd : Odd hyp.w1 := hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card hyp.W1)
    have hidxodd : Odd (_root_.commutator ↥H).index :=
      hG.odd.of_dvd_nat (dvd_trans (Subgroup.index_dvd_card _)
        (dvd_trans (Subgroup.card_subgroup_dvd_card H) (Subgroup.card_subgroup_dvd_card M)))
    exact OddOrder.Peterfalvi.S08.two_mul_add_one_le_of_odd_dvd hw1odd hidxodd
      (hcardW1 ▸ hdvd) hidxgt
  -- `|⁅H,H⁆| = |M''| ≥ w₂`.
  have hcommle : (⁅H, H⁆ : Subgroup ↥M) ≤ H := by
    rw [Subgroup.commutator_le]
    intro p hp q hq
    rw [commutatorElement_def]
    exact H.mul_mem (H.mul_mem (H.mul_mem hp hq) (H.inv_mem hp)) (H.inv_mem hq)
  have hcardge : hyp.w2 ≤ Nat.card ↥(_root_.commutator ↥H) := by
    have eMap := Subgroup.equivMapOfInjective (⁅H, H⁆ : Subgroup ↥M) M.subtype M.subtype_injective
    rw [← OddOrder.Peterfalvi.S08.commutator_subgroupOf_self,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hcommle).toEquiv,
      Nat.card_congr eMap.toEquiv, hmapcomm]
    exact Subgroup.card_le_of_le (hyp.typeP.W2_le.trans inf_le_right)
  -- combine: `|M'| = |H| = |⁅H,H⁆|·|H:⁅H,H⁆| ≥ w₂·(2w₁+1)`.
  have hHcard : Nat.card ↥H = Nat.card ↥(derivedInG M) := by
    rw [hHdef]; exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hM'le).toEquiv
  calc (2 * hyp.w1 + 1) * hyp.w2
      ≤ (_root_.commutator ↥H).index * Nat.card ↥(_root_.commutator ↥H) :=
        Nat.mul_le_mul hidxge hcardge
    _ = Nat.card ↥H := (_root_.commutator ↥H).index_mul_card
    _ = Nat.card ↥(derivedInG M) := hHcard

/-- **Peterfalvi (10.8), line-87 strict bound** `|A(M)|/|M| < 1/w₁`.

Since `A(M) = typePA M = (M')#` (`typePA_eq_sharpSubgroup_derivedInG`), `|A(M)| = |M'| − 1`; and
`|M| = w₁·|M'|` because `[M : M'] = w₁` (`TypePData.card_W1_eq_derived_index`,
`Subgroup.index_mul_card`). Hence `|A(M)|/|M| = (|M'|−1)/(w₁·|M'|) < 1/w₁` (as `|M'| ≥ 1`,
`w₁ ≥ 1`).
This is the strict inequality Peterfalvi (10.8) uses at line 87 to turn `w₁/|M'| ≥ 1 − |G₁|/|G| −
|A(M)|/|M|` into `> 1 − |G₁|/|G| − 1/w₁` (the `hA` consumed by `typeII_coherence_estimate_chain`).
-/
theorem Hypothesis.card_typePA_div_card_lt_inv_w1 [Finite G]
    {M : Subgroup G} (hyp : Hypothesis M) :
    (Nat.card ↥(typePA M hyp.typeP) : ℚ) / (Nat.card ↥M : ℚ) < 1 / (hyp.w1 : ℚ) := by
  have := hyp.finiteG
  have hM'le : derivedInG M ≤ M := Subgroup.map_subtype_le _
  -- `|A(M)| = |M'| − 1` (sharp of the derived subgroup).
  have hcardA : Nat.card ↥(typePA M hyp.typeP) = Nat.card ↥(derivedInG M) - 1 := by
    rw [typePA_eq_sharpSubgroup_derivedInG, Nat.card_coe_set_eq]
    have hc : Nat.card ↥(derivedInG M) = ((derivedInG M : Set G)).ncard := by
      rw [← Nat.card_coe_set_eq]; exact Nat.card_congr (Equiv.refl _)
    rw [sharpSubgroup, Set.ncard_sdiff (Set.singleton_subset_iff.mpr (derivedInG M).one_mem),
      Set.ncard_singleton, hc]
  -- `|M| = w₁·|M'|` since `[M : M'] = w₁`.
  have hcardM : Nat.card ↥M = hyp.w1 * Nat.card ↥(derivedInG M) := by
    have hidx : ((derivedInG M).subgroupOf M).index = hyp.w1 := by
      rw [Hypothesis.w1, Hypothesis.W1]; exact hyp.typeP.card_W1_eq_derived_index.symm
    have hsub : Nat.card ↥((derivedInG M).subgroupOf M) = Nat.card ↥(derivedInG M) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hM'le).toEquiv
    rw [← Subgroup.index_mul_card ((derivedInG M).subgroupOf M), hidx, hsub]
  -- arithmetic over `ℚ`.
  have hm1 : 1 ≤ Nat.card ↥(derivedInG M) := Nat.card_pos
  have hw1 : 1 ≤ hyp.w1 := Nat.card_pos
  rw [hcardA, hcardM, Nat.cast_sub hm1, Nat.cast_mul]
  have hmq : (0 : ℚ) < (Nat.card ↥(derivedInG M) : ℚ) := by exact_mod_cast hm1
  have hwq : (0 : ℚ) < (hyp.w1 : ℚ) := by exact_mod_cast hw1
  rw [div_lt_div_iff₀ (by positivity) hwq]
  push_cast
  nlinarith [hmq, hwq]

open scoped FiniteInduce in
/-- **`‖ζ^{τ₁}‖² = 1`** (Peterfalvi (10.8) line 81 input): the coherent extension `τ₁` of the Dade
isometry is an isometry on `ℤ[S]` (`coh.coherent.extension_inner_eq`), and `ζ = params.zeta ∈ S` is
irreducible (`params.zeta_irreducible`, `params.zeta_mem_S`), so `‖ζ^{τ₁}‖² = ‖ζ‖² = 1`.

This is the norm-one hypothesis that `S09.family_inequality` (7.5) demands of its character argument
`χ = ζ^{τ₁}`, so it is the bridge that lets the now-self-contained `toFamilyHypothesis71` feed the
(10.8) line-81 inequality. -/
theorem Hypothesis.inner_tau1_zeta_self_eq_one [Finite G] [Fintype G] {M : Subgroup G} [Fintype ↥M]
    [Invertible (Nat.card ↥M : ℂ)] [Invertible (Nat.card G : ℂ)]
    {hyp : Hypothesis M} {params : CharacterParameters hyp} (coh : CoherentHypothesis hyp params) :
    ClassFunction.inner (coh.tau1 params.zeta) (coh.tau1 params.zeta) = 1 := by
  have hspan : params.zeta ∈ OddOrder.Peterfalvi.S07.zSpan (L := ↥M) hyp.Sset :=
    Submodule.subset_span params.zeta_mem_S
  change ClassFunction.inner (coh.coherent.extension params.zeta)
    (coh.coherent.extension params.zeta) = 1
  rw [coh.coherent.extension_inner_eq params.zeta params.zeta hspan hspan]
  simpa using OddOrder.RepresentationTheory.irreducibleCharacter_inner_eq_ite
    (⟨params.zeta, params.zeta_irreducible⟩ : OddOrder.RepresentationTheory.IrreducibleCharacter ↥M)
    (⟨params.zeta, params.zeta_irreducible⟩ : OddOrder.RepresentationTheory.IrreducibleCharacter ↥M)

/-- **The `(10.6.b)`-summed bound** (the analytic core of Peterfalvi (10.8) line 83): if a function
`χ : G → ℂ` takes **odd integer** values on a finite set `S` (in particular `|χ(g)| ≥ 1` there),
then
`|S| ≤ Σ_{g ∈ S} ‖χ(g)‖²`.  General and reusable (no §10 hypotheses): per element, an odd integer
`m ≠ 0` has `‖(m : ℂ)‖² = |m|² ≥ 1`, and `Σ_S 1 = |S|`.  In the (10.8) proof this is applied to
`χ = ζ^{τ₁}` on `G₀ = {g | g ∉ Ã(M), (ord g).Coprime w₁}` via (10.6.b) `zeta_tau1_norm_ge_one`,
dropping the `G₀`-part of the (7.5) sum to reach line 83. -/
theorem card_le_sum_normSq_of_forall_eq_odd_intCast {ι : Type*} (S : Finset ι) {χ : ι → ℂ}
    (h : ∀ g ∈ S, ∃ m : ℤ, χ g = (m : ℂ) ∧ Odd m) :
    (S.card : ℝ) ≤ ∑ g ∈ S, ‖χ g‖ ^ 2 := by
  calc (S.card : ℝ) = ∑ _g ∈ S, (1 : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    _ ≤ ∑ g ∈ S, ‖χ g‖ ^ 2 := by
        refine Finset.sum_le_sum (fun g hg => ?_)
        obtain ⟨m, hm, hodd⟩ := h g hg
        have hm0 : m ≠ 0 := by obtain ⟨k, hk⟩ := hodd; omega
        have hnorm : ‖χ g‖ = |(m : ℝ)| := by rw [hm, Complex.norm_intCast]
        have h1 : (1 : ℝ) ≤ |(m : ℝ)| := by
          rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hm0
        rw [hnorm]; nlinarith [h1, abs_nonneg ((m : ℝ))]

open scoped Classical FiniteInduce in
/-- **The `(10.6.b)`-summed bound for `ζ^{τ₁}`** — `|G₀| ≤ Σ_{g ∈ G₀} ‖ζ^{τ₁}(g)‖²` over
`G₀ = {g | g ∉ Ã(M), (ord g).Coprime w₁}`.  Composes `card_le_sum_normSq_of_forall_eq_odd_intCast`
(the analytic core) with the per-`g` (10.6.b) bound `tau1_values_and_norm_bound` (`ζ^{τ₁}(g)` is an
odd integer off `Ã(M)` at orders prime to `w₁`).  The 7 parameter conditions are exactly those
supplied by `exists_charParameters_full`.  This is the `G₀`-drop term Peterfalvi (10.8) uses to pass
from the family inequality (7.5) (line 81) to line 83. -/
theorem Hypothesis.sum_zeta_tau1_normSq_ge_card [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    {hyp : Hypothesis M} {params : CharacterParameters hyp} (coh : CoherentHypothesis hyp params)
    (hmu : params.mu = hyp.muGrid hG hG.odd)
    (hos : params.omegaSigma = hyp.alignedOmegaSigmaGrid hG hG.odd)
    (hzS : params.zeta ∈ inducedFamily M) (hz1 : params.zeta 1 = (hyp.w1 : ℂ))
    (hzconj : params.zeta.conj ≠ params.zeta)
    (hδpm : params.delta = 1 ∨ params.delta = -1)
    (hδj : ∀ j : Fin hyp.w2, j ≠ 0 → hyp.muColumnSign hG hG.odd j = params.delta) :
    ((Finset.univ.filter
        (fun g : G => g ∉ hyp.dadeData.dade.dadeSupport ∧ (orderOf g).Coprime hyp.w1)).card : ℝ)
      ≤ ∑ g ∈ Finset.univ.filter
          (fun g : G => g ∉ hyp.dadeData.dade.dadeSupport ∧ (orderOf g).Coprime hyp.w1),
          ‖coh.tau1 params.zeta g‖ ^ 2 := by
  classical
  apply card_le_sum_normSq_of_forall_eq_odd_intCast
  intro g hg
  rw [Finset.mem_filter] at hg
  exact (tau1_values_and_norm_bound hG coh hmu hos hzS hz1 hzconj hδpm hδj).2 g hg.2.1 hg.2.2

/-- **Restricting the Dade support shrinks it**: for `A₁ ⊆ A`, the Dade support of the restricted
hypothesis `hyp.restrict` is contained in that of `hyp` (`mem_dadeSupport_iff`: a witness
`a ∈ A₁, h ∈ H(a)` for the restriction is a witness `⟨a, _⟩ ∈ A` for `hyp`, since
`(hyp.restrict ..).H a = hyp.H ⟨a, _⟩`).  In the (10.8) line-83 step this gives `G₀ ⊆ famG₀`: the
`A_0(M)`-support complement `G₀` is inside the `A(M)`-support complement `famG₀` (the family `(7.4)`
support for `A(M) = typePA ⊆ typePA0 = A_0(M)`). -/
theorem dadeSupport_restrict_subset {A A₁ : Set G} {L : Subgroup G} [Fintype G]
    (hyp : OddOrder.Peterfalvi.S04.Hypothesis G A L) (hA₁A : A₁ ⊆ A)
    (hA₁_norm : ∀ (l : L) ⦃a : G⦄, a ∈ A₁ → (l : G) * a * (l : G)⁻¹ ∈ A₁) :
    (hyp.restrict hA₁A hA₁_norm).dadeSupport ⊆ hyp.dadeSupport := by
  intro g hg
  rw [OddOrder.Peterfalvi.S04.Hypothesis.mem_dadeSupport_iff] at hg ⊢
  obtain ⟨a, h, hh, hconj⟩ := hg
  exact ⟨⟨a.1, hA₁A a.2⟩, h, hh, hconj⟩

open scoped Classical FiniteInduce in
/-- **Peterfalvi (10.8), line 83** (the mechanical `(7.5)`+`(10.6.b)` combination): the `ρ`-norm of
`ζ^{τ₁}` for the one-member family `{(M, A(M))}` is bounded by `|A(M)|/|M|` plus the `|G₁|/|G|`-term
`(|famG₀| − |G₀|)/|G|`.

This is Peterfalvi (10.8) 04.12 line 81 → 83: apply the family inequality (7.5)
(`S09.family_inequality` on the now-self-contained `toFamilyHypothesis71`, with the norm-one
`inner_tau1_zeta_self_eq_one`) and drop the `G₀`-part of the sum via the `(10.6.b)` bound
(`sum_zeta_tau1_normSq_ge_card`, using `G₀ ⊆ famG₀` from `dadeSupport_restrict_subset` and
`‖·‖² ≥ 0` on the rest).  Pure real-arithmetic bookkeeping over the family inequality; the genuine
`‖ζ^{τ₁,ρ}‖²` lower bound (7.8.b) and the `|G₁|`-count (TI-counting, §9) are the remaining gates
that
turn this into line 87 and the contradiction.  Here `famG₀ = (toFamilyHypothesis71).G0` is the
`A(M)`-support complement and `G₀ = {g ∉ Ã(M), (ord g).Coprime w₁}` the `A_0(M)`-support coprime
subset (`G₀ ⊆ famG₀`). -/
theorem Hypothesis.chiRhoNormSq_zeta_le_line83 [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    {hyp : Hypothesis M} {params : CharacterParameters hyp} (coh : CoherentHypothesis hyp params)
    (hmu : params.mu = hyp.muGrid hG hG.odd)
    (hos : params.omegaSigma = hyp.alignedOmegaSigmaGrid hG hG.odd)
    (hzS : params.zeta ∈ inducedFamily M) (hz1 : params.zeta 1 = (hyp.w1 : ℂ))
    (hzconj : params.zeta.conj ≠ params.zeta)
    (hδpm : params.delta = 1 ∨ params.delta = -1)
    (hδj : ∀ j : Fin hyp.w2, j ≠ 0 → hyp.muColumnSign hG hG.odd j = params.delta) :
    (hyp.toFamilyHypothesis71).chiRhoNormSq (coh.tau1 params.zeta) 0
      ≤ (Nat.card ↥(typePA M hyp.typeP) : ℝ) / (Nat.card ↥M : ℝ)
        + (Nat.card G : ℝ)⁻¹ * ((Nat.card (hyp.toFamilyHypothesis71).G0 : ℝ)
          - ((Finset.univ.filter (fun g : G => g ∉ hyp.dadeData.dade.dadeSupport
              ∧ (orderOf g).Coprime hyp.w1)).card : ℝ)) := by
  have := hyp.finiteG
  -- `F.A 0 = A(M)`, `F.L 0 = M` (structure projections).
  have hA0 : (hyp.toFamilyHypothesis71).A 0 = typePA M hyp.typeP := rfl
  have hL0 : (hyp.toFamilyHypothesis71).L 0 = M := rfl
  -- (7.5) line 81 (single member, `k = 1`).
  have h81 := OddOrder.Peterfalvi.S09.family_inequality (hyp.toFamilyHypothesis71)
    (coh.tau1 params.zeta) (hyp.inner_tau1_zeta_self_eq_one coh)
  rw [Fin.sum_univ_one, hA0, hL0] at h81
  -- `G₀ ⊆ famG₀`: a `g` off the `A_0(M)`-support is off the restricted `A(M)`-support.
  have hsub : Finset.univ.filter (fun g : G => g ∉ hyp.dadeData.dade.dadeSupport
        ∧ (orderOf g).Coprime hyp.w1)
      ⊆ Finset.univ.filter (fun g : G => g ∈ (hyp.toFamilyHypothesis71).G0) := by
    intro g hg
    rw [Finset.mem_filter] at hg ⊢
    refine ⟨Finset.mem_univ g, fun i => ?_⟩
    have hsupp : ((hyp.toFamilyHypothesis71).hyp71 i).hyp.dadeSupport
        ⊆ hyp.dadeData.dade.dadeSupport :=
      dadeSupport_restrict_subset hyp.dadeData.dade Set.subset_union_left _
    exact fun hmem => hg.2.1 (hsupp hmem)
  -- drop the `G₀`-part: `|G₀| ≤ Σ_{G₀} ‖χ‖² ≤ Σ_{famG₀} ‖χ‖²`.
  have hdrop : ((Finset.univ.filter (fun g : G => g ∉ hyp.dadeData.dade.dadeSupport
        ∧ (orderOf g).Coprime hyp.w1)).card : ℝ)
      ≤ ∑ g ∈ Finset.univ.filter (fun g : G => g ∈ (hyp.toFamilyHypothesis71).G0),
          ‖(coh.tau1 params.zeta : G → ℂ) g‖ ^ 2 := by
    refine le_trans (hyp.sum_zeta_tau1_normSq_ge_card hG coh hmu hos hzS hz1 hzconj hδpm hδj) ?_
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun g _ _ => by positivity)
  -- rearrange the family inequality.
  have hGinv : (0 : ℝ) ≤ (Nat.card G : ℝ)⁻¹ := by positivity
  have hcS := mul_le_mul_of_nonneg_left hdrop hGinv
  rw [mul_sub] at h81 ⊢
  linarith [h81, hcS]

/-- **Peterfalvi (10.8), the analytic chain** (04.12 p.61, lines 87--99) — the pure-`ℚ` assembly
that turns the §7 norm output (line 87) and the §8 TI-counting bound (lines 89--91) into the
coherence bound `1 − 1/w₁ − 1/u < w₁w₂/|M'|`.

Faithful inputs (with `Mp = |M'|`, `cardH = |H| = |S_F|`, `cardS = |S|`, `u = |U|`,
`g1g = |G₁|/|G|`):
* `hA` — the §7 output `w₁/|M'| > 1 − |G₁|/|G| − 1/w₁` (Peterfalvi line 87, from (7.5), (7.8.b),
  (10.6.b), and `|M'| ≥ 2w₁+1`);
* `hB` — the TI-counting bound `|G₁|/|G| ≤ (|H|−1)/|S| + (w₁w₂−w₁−w₂+1)/(w₁w₂)` (from the inclusion
  `G₁ ⊆ (H#)^G ∪ V^G` and the orbit cardinalities, Peterfalvi lines 89--91);
* `hS` — `|S| = |H|·|U|·w₂` (the Type-II partner `S = (H ⋊ U) ⋊ W₂`).

The derivation substitutes `(w₁w₂−w₁−w₂+1)/(w₁w₂) = 1 − 1/w₂ − 1/w₁ + 1/(w₁w₂)` and
`(|H|−1)/|S| ≤ |H|/|S| = 1/(|U|w₂)`, yielding `w₁/|M'| > 1/w₂ − 1/(w₁w₂) − 1/(|U|w₂)`, then
multiplies by `w₂`.  Pure arithmetic over `ℚ`; the genuine character/group inputs are `hA`/`hB`. -/
theorem typeII_coherence_estimate_chain
    {w₁ w₂ u cardH cardS Mp : ℕ} {g1g : ℚ}
    (hw1 : 1 ≤ w₁) (hw2 : 1 ≤ w₂) (hu : 1 ≤ u) (hH : 1 ≤ cardH)
    (hMp : 1 ≤ Mp) (hS : cardS = cardH * u * w₂)
    (hA : 1 - g1g - 1 / (w₁ : ℚ) < (w₁ : ℚ) / (Mp : ℚ))
    (hB : g1g ≤ ((cardH : ℚ) - 1) / (cardS : ℚ)
        + ((w₁ : ℚ) * w₂ - w₁ - w₂ + 1) / ((w₁ : ℚ) * w₂)) :
    (1 : ℚ) - 1 / (w₁ : ℚ) - 1 / (u : ℚ) < (w₁ : ℚ) * w₂ / (Mp : ℚ) := by
  have hw1q : (0 : ℚ) < w₁ := by exact_mod_cast hw1
  have hw2q : (0 : ℚ) < w₂ := by exact_mod_cast hw2
  have huq : (0 : ℚ) < u := by exact_mod_cast hu
  have hHq : (0 : ℚ) < cardH := by exact_mod_cast hH
  have hMpq : (0 : ℚ) < Mp := by exact_mod_cast hMp
  have hw1ne : (w₁ : ℚ) ≠ 0 := ne_of_gt hw1q
  have hw2ne : (w₂ : ℚ) ≠ 0 := ne_of_gt hw2q
  have hune : (u : ℚ) ≠ 0 := ne_of_gt huq
  have hScast : (cardS : ℚ) = (cardH : ℚ) * u * w₂ := by exact_mod_cast hS
  -- `(|H|−1)/|S| ≤ 1/(|U|w₂)` (drop the `−1`, then cancel `|H|`).
  have hHS : ((cardH : ℚ) - 1) / (cardS : ℚ) ≤ 1 / ((u : ℚ) * w₂) := by
    rw [hScast, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_pos huq hw2q]
  -- `(w₁w₂−w₁−w₂+1)/(w₁w₂) = 1 − 1/w₂ − 1/w₁ + 1/(w₁w₂)`.
  have hident : ((w₁ : ℚ) * w₂ - w₁ - w₂ + 1) / ((w₁ : ℚ) * w₂)
      = 1 - 1 / w₂ - 1 / w₁ + 1 / ((w₁ : ℚ) * w₂) := by
    field_simp
  -- `w₁/|M'| > 1/w₂ − 1/(w₁w₂) − 1/(|U|w₂)`.
  have hKey : 1 / (w₂ : ℚ) - 1 / ((w₁ : ℚ) * w₂) - 1 / ((u : ℚ) * w₂) < (w₁ : ℚ) / Mp := by
    rw [hident] at hB
    linarith [hA, hB, hHS]
  -- multiply by `w₂` and simplify the four products.
  have e1 : (w₂ : ℚ) * (1 / w₂) = 1 := by rw [mul_one_div, div_self hw2ne]
  have e2 : (w₂ : ℚ) * (1 / ((w₁ : ℚ) * w₂)) = 1 / w₁ := by
    rw [mul_one_div, mul_comm (w₁ : ℚ) w₂, div_mul_eq_div_div, div_self hw2ne]
  have e3 : (w₂ : ℚ) * (1 / ((u : ℚ) * w₂)) = 1 / u := by
    rw [mul_one_div, mul_comm (u : ℚ) w₂, div_mul_eq_div_div, div_self hw2ne]
  have e4 : (w₂ : ℚ) * ((w₁ : ℚ) / Mp) = (w₁ : ℚ) * w₂ / Mp := by ring
  have hmul := mul_lt_mul_of_pos_left hKey hw2q
  rw [mul_sub, mul_sub, e1, e2, e3, e4] at hmul
  linarith [hmul]

/-- **`V`-elements have order divisible by a `|W₁|`-prime** (the (8.10)/(10.8) support
bookkeeping): `v ∈ V = W ∖ (W₁ ∪ W₂)` factors as `v₁·v₂` with `v₁ ∈ W₁ ∖ {1}`
(`TypePData.exists_mul_eq_of_mem_W`; a trivial `W₁`-part would put `v ∈ W₂`), and any prime of
`orderOf v₁ ∣ |W₁|` divides `orderOf v` — a power killing `v` puts `v₁ ^ n ∈ W₁ ⊓ W₂ = ⊥`. -/
theorem exists_prime_dvd_orderOf_of_mem_typePV [Finite G] {M : Subgroup G}
    (data : TypePData M) {v : G} (hv : v ∈ typePV M data) :
    ∃ p : ℕ, p.Prime ∧ p ∣ orderOf v ∧ p ∣ Nat.card ↥data.W1 := by
  have hW1le : data.W1 ≤ data.W := data.W_eq ▸ le_sup_left
  have hW2le : data.W2 ≤ data.W := data.W_eq ▸ le_sup_right
  obtain ⟨hvW, hvnot⟩ := hv
  rw [Set.mem_union] at hvnot
  push Not at hvnot
  obtain ⟨v₁, hv₁, v₂, hv₂, rfl⟩ :=
    data.exists_mul_eq_of_mem_W (SetLike.mem_coe.mp hvW)
  have hv₁ne : v₁ ≠ 1 := by
    rintro rfl
    exact hvnot.2 (by simpa using hv₂)
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd
    (fun h => hv₁ne (orderOf_eq_one_iff.mp h))
  have hpW1 : p ∣ Nat.card ↥data.W1 := by
    refine hpd.trans ?_
    have h1 : orderOf v₁ = orderOf (⟨v₁, hv₁⟩ : ↥data.W1) :=
      orderOf_injective data.W1.subtype data.W1.subtype_injective ⟨v₁, hv₁⟩
    rw [h1]
    exact orderOf_dvd_natCard _
  have hcomm : Commute v₁ v₂ := by
    have := data.W_cyclic
    let : CommGroup ↥data.W := IsCyclic.commGroup
    have := mul_comm (⟨v₁, hW1le hv₁⟩ : ↥data.W) ⟨v₂, hW2le hv₂⟩
    exact Subtype.ext_iff.mp this
  refine ⟨p, hp, ?_, hpW1⟩
  have hkill : v₁ ^ orderOf (v₁ * v₂) = 1 := by
    have h1 : (v₁ * v₂) ^ orderOf (v₁ * v₂) = 1 := pow_orderOf_eq_one _
    rw [hcomm.mul_pow] at h1
    have hmem : v₁ ^ orderOf (v₁ * v₂) ∈ data.W1 ⊓ data.W2 := by
      refine ⟨data.W1.pow_mem hv₁ _, ?_⟩
      have heq : v₁ ^ orderOf (v₁ * v₂) = (v₂ ^ orderOf (v₁ * v₂))⁻¹ :=
        eq_inv_of_mul_eq_one_right (((hcomm.pow_pow _ _).symm.eq).trans h1)
      rw [heq]
      exact data.W2.inv_mem (data.W2.pow_mem hv₂ _)
    rwa [disjoint_iff.mp (typePData_disjoint_W1_W2 data), Subgroup.mem_bot] at hmem
  exact hpd.trans (orderOf_dvd_of_pow_eq_one hkill)

open scoped Classical FiniteInduce in
/-- **Coprime-order elements of the full Dade support lie in the `A(M)`-restricted support**
(the (10.8) `G₀`-bookkeeping): the extra support over `A₀(M) ∖ A(M) = V^M` consists of
conjugates of `a·h` with `a` conjugate into `V` — whose order is divisible by a `w₁`-prime
(`exists_prime_dvd_orderOf_of_mem_typePV`, carried through the coprime `H(a)`-part) — so an
element of `w₁`-coprime order must arise from the `A(M)`-part. -/
theorem Hypothesis.mem_restricted_dadeSupport_of_coprime [Finite G] {M : Subgroup G}
    (hyp : Hypothesis M) {g : G} (hg : g ∈ hyp.dadeData.dade.dadeSupport)
    (hcop : (orderOf g).Coprime hyp.w1) :
    g ∈ hyp.toHypothesis71.hyp.dadeSupport := by
  classical
  obtain ⟨a, h, hh, hconj⟩ := hyp.dadeData.dade.mem_dadeSupport_iff.mp hg
  have ha2 : a.1 ∈ typePA M hyp.typeP ∪ conjClassSetIn M (typePV M hyp.typeP) := a.2
  rcases ha2 with haA | haV
  · -- the `A(M)`-part: the same witness lives in the restricted support
    exact hyp.toHypothesis71.hyp.mem_dadeSupport_iff.mpr ⟨⟨a.1, haA⟩, h, hh, hconj⟩
  · -- the `V^M`-part: its orders are divisible by a `w₁`-prime — contradiction
    exfalso
    obtain ⟨t, htV, m, hmM, hma⟩ := haV
    obtain ⟨p, hp, hpv, hpw⟩ := exists_prime_dvd_orderOf_of_mem_typePV hyp.typeP htV
    -- `p ∣ orderOf a` (conjugation-invariance of the order)
    have hoa : orderOf a.1 = orderOf t := by
      rw [← hma]
      have := orderOf_injective (MulAut.conj m).toMonoidHom (MulAut.conj m).injective t
      simpa [MulAut.conj_apply] using this
    have hpa : p ∣ orderOf a.1 := hoa ▸ hpv
    -- `h ∈ H(a)` commutes with `a` and has coprime order ((2.2.b)/(2.2.c))
    have hhc : h ∈ Subgroup.centralizer ({a.1} : Set G) := by
      have hsup : h ∈ hyp.dadeData.dade.H a ⊔ OddOrder.Peterfalvi.S04.centralizerIn M a.1 :=
        (le_sup_left : hyp.dadeData.dade.H a ≤ _) hh
      rwa [← hyp.dadeData.dade.centralizer_eq_sup a] at hsup
    have hcomm : Commute a.1 h :=
      Subgroup.mem_centralizer_iff.mp hhc a.1 rfl
    have hcopah : Nat.Coprime (orderOf a.1) (orderOf h) := by
      have h1 : orderOf h ∣ Nat.card (hyp.dadeData.dade.H a) := by
        have he : orderOf h = orderOf (⟨h, hh⟩ : ↥(hyp.dadeData.dade.H a)) :=
          orderOf_injective (hyp.dadeData.dade.H a).subtype
            (hyp.dadeData.dade.H a).subtype_injective ⟨h, hh⟩
        rw [he]; exact orderOf_dvd_natCard _
      have h2 : orderOf a.1 ∣ Nat.card (OddOrder.Peterfalvi.S04.centralizerIn M a.1) := by
        have haC : a.1 ∈ OddOrder.Peterfalvi.S04.centralizerIn M a.1 :=
          ⟨hyp.dadeData.dade.subset_L a.2, Subgroup.mem_centralizer_iff.mpr
            (fun z hz => by rw [Set.mem_singleton_iff.mp hz])⟩
        have he : orderOf a.1 = orderOf (⟨a.1, haC⟩ : ↥(OddOrder.Peterfalvi.S04.centralizerIn M
            a.1)) :=
          orderOf_injective (OddOrder.Peterfalvi.S04.centralizerIn M a.1).subtype
            (OddOrder.Peterfalvi.S04.centralizerIn M a.1).subtype_injective ⟨a.1, haC⟩
        rw [he]; exact orderOf_dvd_natCard _
      exact ((hyp.dadeData.dade.centralizer_coprime a a).coprime_dvd_left h1).coprime_dvd_right
        h2 |>.symm
    -- `p ∣ orderOf (a·h)`: the killing power lands `a ^ n` in the trivial coprime overlap
    have hpah : p ∣ orderOf (a.1 * h) := by
      have hkill : a.1 ^ orderOf (a.1 * h) = 1 := by
        have h1 : (a.1 * h) ^ orderOf (a.1 * h) = 1 := pow_orderOf_eq_one _
        rw [hcomm.mul_pow] at h1
        have hd1 : orderOf (a.1 ^ orderOf (a.1 * h)) ∣ orderOf a.1 := orderOf_pow_dvd _
        have hd2 : orderOf (a.1 ^ orderOf (a.1 * h)) ∣ orderOf h := by
          have heq : a.1 ^ orderOf (a.1 * h) = (h ^ orderOf (a.1 * h))⁻¹ :=
            eq_inv_of_mul_eq_one_left h1
          rw [heq, orderOf_inv]
          exact orderOf_pow_dvd _
        have hone : orderOf (a.1 ^ orderOf (a.1 * h)) = 1 :=
          Nat.dvd_one.mp (hcopah ▸ Nat.dvd_gcd hd1 hd2)
        exact orderOf_eq_one_iff.mp hone
      exact hpa.trans (orderOf_dvd_of_pow_eq_one hkill)
    -- transport along the conjugacy to `g` and contradict the coprimality
    have hog : orderOf g = orderOf (a.1 * h) := by
      obtain ⟨c, hc⟩ := isConj_iff.mp hconj
      rw [← hc]
      have := orderOf_injective (MulAut.conj c).toMonoidHom (MulAut.conj c).injective (a.1 * h)
      simpa [MulAut.conj_apply] using this
    have hpg : p ∣ orderOf g := hog ▸ hpah
    have hpw1 : p ∣ hyp.w1 := hpw
    exact hp.ne_one (Nat.dvd_one.mp (hcop ▸ Nat.dvd_gcd hpg hpw1))

/-- **The (8.7) type-V trichotomy transfers across `TypePData` choices** (issue 1021): the
alternative field of a `TypeVData` mentions only `H = M_F` (data-independent, `H_eq`) and
`|W₁| = [M : M′]` (data-independent, `card_W1_eq_derived_index`), so it holds verbatim for any
other `TypePData` of the same `M` — in particular for the (10.1) `Hypothesis`'s own datum. -/
theorem TypeVData.alternative_transfer [Finite G] {M : Subgroup G}
    (dV : OddOrder.GroupTheory.TypeVData M) (data : TypePData M) :
    OddOrder.GroupTheory.IsTISubset (sharpSubgroup data.H)
      (Subgroup.normalizer (data.H : Set G)) ∨
    (∃ p : ℕ, p.Prime ∧ p ∈ (Nat.card ↥data.H).primeFactors ∧
      Nat.card ↥data.W1 ∣ p - 1 ∧ IsCyclic ↥(opiCoreInG {p}ᶜ data.H)) ∨
    (∃ p : ℕ, p.Prime ∧ p ∈ (Nat.card ↥data.H).primeFactors ∧
      Nat.card ↥(opiCoreInG {p} data.H) = p ^ 3 ∧ Nat.card ↥data.W1 ∣ p + 1 ∧
      IsCyclic ↥(opiCoreInG {p}ᶜ data.H)) := by
  have hH : dV.typeP.H = data.H := dV.typeP.H_eq.trans data.H_eq.symm
  have hW1 : Nat.card ↥dV.typeP.W1 = Nat.card ↥data.W1 := by
    rw [dV.typeP.card_W1_eq_derived_index, data.card_W1_eq_derived_index]
  rcases dV.alternative with h | h | h
  · exact Or.inl (hH ▸ h)
  · exact Or.inr (Or.inl (hW1 ▸ hH ▸ h))
  · exact Or.inr (Or.inr (hW1 ▸ hH ▸ h))

/-- **The pair κ-Hall dual is `W₂`**: `M_σ ⊓ C_G(W₁) = W₂` for type-`P` data.  This is the
identification `K = W₂(M)` of the `M`-seeded maximal pair (`mp.K_eq` has exactly this LHS with
`mp.Kstar = W₁` literal), the pair-linkage input of the (10.8) partner supply (issue 1020).

`⊇`: `W₂ ≤ H = M_F ≤ M_σ` (`maxNilpotentNormalHall_le_Msigma`) and `W₂` centralises `W₁`
(both sit in the commutative `W`).  `⊆`: `M_σ ≤ M′` (`Msigma_le_derived`), and
`M′ ⊓ C_G(w) = W₂` for a nonidentity `w ∈ W₁` (`centralizer_W1`). -/
theorem typePData_Msigma_inf_centralizer_W1_eq_W2 [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (data : TypePData M) :
    OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (data.W1 : Set G) = data.W2 := by
  have hW1le : data.W1 ≤ data.W := data.W_eq ▸ le_sup_left
  have hW2le : data.W2 ≤ data.W := data.W_eq ▸ le_sup_right
  apply le_antisymm
  · -- `⊆`: pass through `M′ ⊓ C_G(w) = W₂` at a nonidentity `w ∈ W₁`
    obtain ⟨w, hwW1, hwne⟩ :=
      (data.W1.bot_or_exists_ne_one).resolve_left data.W1_nontrivial
    rintro x ⟨hxσ, hxc⟩
    rw [← data.centralizer_W1 w hwW1 hwne]
    refine ⟨OddOrder.BG.Ch3.S10.Msigma_le_derived hG hM hxσ, ?_⟩
    exact Subgroup.centralizer_le (by simpa using hwW1) hxc
  · -- `⊇`: `W₂ ≤ M_σ` via `H = M_F`, and `W₂` centralises `W₁` inside the commutative `W`
    refine le_inf ?_ ?_
    · refine le_trans ?_ (OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_Msigma hG hM)
      exact data.H_eq ▸ (data.W2_le.trans (inf_le_left.trans le_rfl))
    · intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      have := data.W_cyclic
      let : CommGroup ↥data.W := IsCyclic.commGroup
      have := mul_comm (⟨w, hW1le hw⟩ : ↥data.W) ⟨x, hW2le hx⟩
      exact Subtype.ext_iff.mp this

/-- **The `(S_F#)^G` union bound of the (10.8) TI-counting** (p. 60 line 91, `≤`-form): the
conjugacy saturation of the kernel sharp-set of a type-`P` maximal `S` has at most
`(|S_F| − 1)·[G : S]` elements.  `S` stabilises `H# = H ∖ {1}` under conjugation (`H ⊴ S`), so
the union bound `ncard_conjClassSet_le` applies with `L = S`; no TI-property is needed for the
upper bound. -/
theorem ncard_conjClassSet_sharp_H_le [Finite G] {S : Subgroup G} (data : TypePData S) :
    (conjClassSet ((data.H : Set G) \ {1})).ncard ≤ (Nat.card ↥data.H - 1) * S.index := by
  have hHle : data.H ≤ S := data.H_le.trans (Subgroup.map_subtype_le _)
  have hstab : ∀ l ∈ S, ∀ t ∈ (data.H : Set G) \ {1},
      l * t * l⁻¹ ∈ (data.H : Set G) \ {1} := by
    rintro l hl t ⟨htH, htne⟩
    have htH' : t ∈ data.H := htH
    have hnorm := OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_subgroupOf_normal S
    have hconj : l * t * l⁻¹ ∈ maxNilpotentNormalHall S := by
      have hmem := hnorm.conj_mem ⟨t, hHle htH'⟩
        (Subgroup.mem_subgroupOf.mpr (data.H_eq ▸ htH')) ⟨l, hl⟩
      exact Subgroup.mem_subgroupOf.mp hmem
    refine ⟨?_, ?_⟩
    · rw [SetLike.mem_coe, data.H_eq]; exact hconj
    · intro h1
      apply htne
      rw [Set.mem_singleton_iff]
      have := congrArg (fun z => l⁻¹ * z * l) (Set.mem_singleton_iff.mp h1)
      simpa [mul_assoc] using this
  have hle := OddOrder.GroupTheory.ncard_conjClassSet_le (L := S) hstab
  have hA : ((data.H : Set G) \ {1}).ncard = Nat.card ↥data.H - 1 := by
    rw [Set.ncard_sdiff_singleton_of_mem (by exact one_mem data.H),
      ← Nat.card_coe_set_eq]
    rfl
  rwa [hA] at hle

open scoped Classical FiniteInduce in
/-- **The (10.8) `G₁`-count bound, Nat form** (p. 60 lines 89–91): with the type-II partner
data supplied, the restricted-support complement count `|famG₀| = |∁Ã(M)|` is bounded by the
full-support `w₁`-coprime filter plus the two covering counts `(|S_F|−1)·[G:S]` and
`|V|·[G:W]`.

`∁Ã(M)` splits along `w₁`-coprimality; the coprime part equals the full-support coprime filter
(`mem_restricted_dadeSupport_of_coprime` + support monotonicity), and the non-coprime part is
covered by `𝒞((S_F)#) ∪ 𝒞(V_S)` (`mem_conjClassSet_sharpH_or_typePV_of_not_coprime`), counted
by `ncard_conjClassSet_sharp_H_le` and `typePData_conjClassSet_typePV_ncard`. -/
theorem Hypothesis.g1_card_le_of_partner [Finite G] {M S : Subgroup G} (hyp : Hypothesis M)
    (data : TypePData S) (hprime : (Nat.card ↥data.W1).Prime)
    (hcop : Nat.Coprime (Nat.card ↥(derivedInG S)) (Nat.card ↥data.W1))
    (hHall : OddOrder.Isaacs.Ch03.IsHallSubgroup (Nat.card ↥data.H).primeFactors data.H)
    (hcent : ∀ b ∈ data.H, b ≠ 1 → Subgroup.centralizer ({b} : Set G) ≤ S)
    (hfrobcap : ∀ b ∈ data.H, b ≠ 1 → ∀ y ∈ derivedInG S,
      y ∈ Subgroup.centralizer ({b} : Set G) → y ∈ data.H)
    (hW2card : Nat.card ↥data.W2 = hyp.w1) :
    Nat.card (hyp.toFamilyHypothesis71).G0
      ≤ (Finset.univ.filter (fun g : G => g ∉ hyp.dadeData.dade.dadeSupport
          ∧ (orderOf g).Coprime hyp.w1)).card
        + ((Nat.card ↥data.H - 1) * S.index
            + (Nat.card ↥data.W1 * Nat.card ↥data.W2 - Nat.card ↥data.W1
                - Nat.card ↥data.W2 + 1) * data.W.index) := by
  classical
  -- `famG₀` is the complement of the restricted support (the `Fin 1` family collapses)
  have hG0eq : (hyp.toFamilyHypothesis71).G0
      = {g : G | g ∉ hyp.toHypothesis71.hyp.dadeSupport} := by
    ext g
    rw [(hyp.toFamilyHypothesis71).mem_G0_iff]
    exact ⟨fun h => h 0, fun h _ => h⟩
  have hcard0 : Nat.card (hyp.toFamilyHypothesis71).G0
      = (Finset.univ.filter
          (fun g : G => g ∉ hyp.toHypothesis71.hyp.dadeSupport)).card := by
    rw [hG0eq, Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card', Set.toFinset_ofPred]
  -- split the complement along `w₁`-coprimality
  have hsplit : (Finset.univ.filter
        (fun g : G => g ∉ hyp.toHypothesis71.hyp.dadeSupport)).card
      = (Finset.univ.filter (fun g : G => g ∉ hyp.toHypothesis71.hyp.dadeSupport
          ∧ (orderOf g).Coprime hyp.w1)).card
        + (Finset.univ.filter (fun g : G => g ∉ hyp.toHypothesis71.hyp.dadeSupport
            ∧ ¬ (orderOf g).Coprime hyp.w1)).card := by
    rw [← Finset.filter_filter, ← Finset.filter_filter,
      Finset.card_filter_add_card_filter_not]
  -- support monotonicity: the restricted support sits inside the full one
  have hRF : hyp.toHypothesis71.hyp.dadeSupport ⊆ hyp.dadeData.dade.dadeSupport := by
    intro x hx
    obtain ⟨a, h, hh, hconj⟩ := hyp.toHypothesis71.hyp.mem_dadeSupport_iff.mp hx
    exact hyp.dadeData.dade.mem_dadeSupport_iff.mpr
      ⟨⟨a.1, Set.subset_union_left a.2⟩, h, hh, hconj⟩
  -- the coprime part is the full-support coprime filter
  have hcopeq : (Finset.univ.filter (fun g : G => g ∉ hyp.toHypothesis71.hyp.dadeSupport
        ∧ (orderOf g).Coprime hyp.w1)).card
      = (Finset.univ.filter (fun g : G => g ∉ hyp.dadeData.dade.dadeSupport
          ∧ (orderOf g).Coprime hyp.w1)).card := by
    congr 1
    refine Finset.filter_congr fun g _ => ?_
    constructor
    · rintro ⟨hgR, hgcop⟩
      exact ⟨fun hgF => hgR (hyp.mem_restricted_dadeSupport_of_coprime hgF hgcop), hgcop⟩
    · rintro ⟨hgF, hgcop⟩
      exact ⟨fun hgR => hgF (hRF hgR), hgcop⟩
  -- the non-coprime part is covered by `𝒞((S_F)#) ∪ 𝒞(V_S)`
  have hsub : {g : G | g ∉ hyp.toHypothesis71.hyp.dadeSupport
        ∧ ¬ (orderOf g).Coprime hyp.w1}
      ⊆ conjClassSet ((data.H : Set G) \ {1}) ∪ conjClassSet (typePV S data) := by
    rintro g ⟨-, hgnc⟩
    exact mem_conjClassSet_sharpH_or_typePV_of_not_coprime data hprime hcop hHall hcent
      hfrobcap (by rwa [hW2card])
  have hnc_le : (Finset.univ.filter (fun g : G => g ∉ hyp.toHypothesis71.hyp.dadeSupport
        ∧ ¬ (orderOf g).Coprime hyp.w1)).card
      ≤ (Nat.card ↥data.H - 1) * S.index
        + (Nat.card ↥data.W1 * Nat.card ↥data.W2 - Nat.card ↥data.W1
            - Nat.card ↥data.W2 + 1) * data.W.index := by
    calc (Finset.univ.filter (fun g : G => g ∉ hyp.toHypothesis71.hyp.dadeSupport
          ∧ ¬ (orderOf g).Coprime hyp.w1)).card
        = {g : G | g ∉ hyp.toHypothesis71.hyp.dadeSupport
            ∧ ¬ (orderOf g).Coprime hyp.w1}.ncard := by
          rw [Set.ncard_eq_toFinset_card', Set.toFinset_ofPred]
      _ ≤ (conjClassSet ((data.H : Set G) \ {1})
            ∪ conjClassSet (typePV S data)).ncard :=
          Set.ncard_le_ncard hsub (Set.toFinite _)
      _ ≤ (conjClassSet ((data.H : Set G) \ {1})).ncard
            + (conjClassSet (typePV S data)).ncard := Set.ncard_union_le _ _
      _ ≤ _ := by
          rw [typePData_conjClassSet_typePV_ncard]
          exact Nat.add_le_add_right (ncard_conjClassSet_sharp_H_le data) _
  rw [hcard0, hsplit, hcopeq]
  exact Nat.add_le_add_left hnc_le _

open scoped Classical FiniteInduce in
/-- **The (10.8) `hB` bound** (p. 60 lines 89–91, the rational form consumed by
`typeII_coherence_contradiction_estimate_of_partner`): with the type-II partner data supplied,

`(|famG₀| − #{g ∉ Ã₀, (|g|, w₁) = 1}) / |G| ≤ (|S_F| − 1)/|S| + (w₁w₂ − w₁ − w₂ + 1)/(w₁w₂)`.

The rational form of `g1_card_le_of_partner`, divided by `|G| = |S|·[G:S] = |W|·[G:W]`. -/
theorem Hypothesis.g1_div_le_of_partner [Finite G] {M S : Subgroup G} (hyp : Hypothesis M)
    (data : TypePData S) (hprime : (Nat.card ↥data.W1).Prime)
    (hcop : Nat.Coprime (Nat.card ↥(derivedInG S)) (Nat.card ↥data.W1))
    (hHall : OddOrder.Isaacs.Ch03.IsHallSubgroup (Nat.card ↥data.H).primeFactors data.H)
    (hcent : ∀ b ∈ data.H, b ≠ 1 → Subgroup.centralizer ({b} : Set G) ≤ S)
    (hfrobcap : ∀ b ∈ data.H, b ≠ 1 → ∀ y ∈ derivedInG S,
      y ∈ Subgroup.centralizer ({b} : Set G) → y ∈ data.H)
    (hW1card : Nat.card ↥data.W1 = hyp.w2) (hW2card : Nat.card ↥data.W2 = hyp.w1)
    (hWcard : Nat.card ↥data.W = hyp.w1 * hyp.w2) :
    ((Nat.card (hyp.toFamilyHypothesis71).G0 : ℚ)
        - ((Finset.univ.filter (fun g : G => g ∉ hyp.dadeData.dade.dadeSupport
            ∧ (orderOf g).Coprime hyp.w1)).card : ℚ)) / (Nat.card G : ℚ)
      ≤ ((Nat.card ↥data.H : ℚ) - 1) / (Nat.card ↥S : ℚ)
        + ((hyp.w1 : ℚ) * hyp.w2 - hyp.w1 - hyp.w2 + 1) / ((hyp.w1 : ℚ) * hyp.w2) := by
  classical
  have hNat := hyp.g1_card_le_of_partner data hprime hcop hHall hcent hfrobcap hW2card
  -- cardinalities and nonvanishing
  have hcH : 1 ≤ Nat.card ↥data.H := Nat.card_pos
  have hcW1 : 2 ≤ Nat.card ↥data.W1 :=
    (Subgroup.one_lt_card_iff_ne_bot _).mpr data.W1_nontrivial
  have hcW2 : 2 ≤ Nat.card ↥data.W2 :=
    (Subgroup.one_lt_card_iff_ne_bot _).mpr data.W2_nontrivial
  have hsub1 : Nat.card ↥data.W1 ≤ Nat.card ↥data.W1 * Nat.card ↥data.W2 :=
    Nat.le_mul_of_pos_right _ (by omega)
  have hsub2 : Nat.card ↥data.W2
      ≤ Nat.card ↥data.W1 * Nat.card ↥data.W2 - Nat.card ↥data.W1 := by
    have hfac : Nat.card ↥data.W1 * Nat.card ↥data.W2 - Nat.card ↥data.W1
        = Nat.card ↥data.W1 * (Nat.card ↥data.W2 - 1) := by
      rw [Nat.mul_sub, mul_one]
    rw [hfac]
    calc Nat.card ↥data.W2 ≤ 2 * (Nat.card ↥data.W2 - 1) := by omega
      _ ≤ Nat.card ↥data.W1 * (Nat.card ↥data.W2 - 1) :=
          Nat.mul_le_mul_right _ hcW1
  have hSidx0 : (S.index : ℚ) ≠ 0 := by
    exact_mod_cast Subgroup.index_ne_zero_of_finite
  have hWidx0 : (data.W.index : ℚ) ≠ 0 := by
    exact_mod_cast Subgroup.index_ne_zero_of_finite
  have hG0 : (0 : ℚ) < (Nat.card G : ℚ) := by exact_mod_cast Nat.card_pos
  -- `|G| = |S|·[G:S]` and `|G| = |W|·[G:W]`, in `ℚ`
  have hGS : (Nat.card G : ℚ) = (Nat.card ↥S : ℚ) * (S.index : ℚ) := by
    exact_mod_cast (Subgroup.card_mul_index S).symm
  have hGW : (Nat.card G : ℚ) = (Nat.card ↥data.W : ℚ) * (data.W.index : ℚ) := by
    exact_mod_cast (Subgroup.card_mul_index data.W).symm
  -- the numerator bound, cast to `ℚ`
  have hnum : (Nat.card (hyp.toFamilyHypothesis71).G0 : ℚ)
      - ((Finset.univ.filter (fun g : G => g ∉ hyp.dadeData.dade.dadeSupport
          ∧ (orderOf g).Coprime hyp.w1)).card : ℚ)
      ≤ ((Nat.card ↥data.H : ℚ) - 1) * (S.index : ℚ)
        + ((Nat.card ↥data.W1 : ℚ) * (Nat.card ↥data.W2 : ℚ) - (Nat.card ↥data.W1 : ℚ)
            - (Nat.card ↥data.W2 : ℚ) + 1) * (data.W.index : ℚ) := by
    have hc := (Nat.cast_le (α := ℚ)).mpr hNat
    push_cast [Nat.cast_sub hcH, Nat.cast_sub hsub1, Nat.cast_sub hsub2] at hc
    linarith
  -- divide by `|G|` and split into the two orbit terms
  calc ((Nat.card (hyp.toFamilyHypothesis71).G0 : ℚ)
        - ((Finset.univ.filter (fun g : G => g ∉ hyp.dadeData.dade.dadeSupport
            ∧ (orderOf g).Coprime hyp.w1)).card : ℚ)) / (Nat.card G : ℚ)
      ≤ (((Nat.card ↥data.H : ℚ) - 1) * (S.index : ℚ)
          + ((Nat.card ↥data.W1 : ℚ) * (Nat.card ↥data.W2 : ℚ) - (Nat.card ↥data.W1 : ℚ)
              - (Nat.card ↥data.W2 : ℚ) + 1) * (data.W.index : ℚ)) / (Nat.card G : ℚ) := by
        gcongr
    _ = ((Nat.card ↥data.H : ℚ) - 1) / (Nat.card ↥S : ℚ)
          + ((Nat.card ↥data.W1 : ℚ) * (Nat.card ↥data.W2 : ℚ) - (Nat.card ↥data.W1 : ℚ)
              - (Nat.card ↥data.W2 : ℚ) + 1) / (Nat.card ↥data.W : ℚ) := by
        rw [add_div]
        congr 1
        · rw [hGS, mul_div_mul_right _ _ hSidx0]
        · rw [hGW, mul_div_mul_right _ _ hWidx0]
    _ = ((Nat.card ↥data.H : ℚ) - 1) / (Nat.card ↥S : ℚ)
          + ((hyp.w1 : ℚ) * hyp.w2 - hyp.w1 - hyp.w2 + 1) / ((hyp.w1 : ℚ) * hyp.w2) := by
        have e1 : (Nat.card ↥data.W1 : ℚ) = (hyp.w2 : ℚ) := by exact_mod_cast hW1card
        have e2 : (Nat.card ↥data.W2 : ℚ) = (hyp.w1 : ℚ) := by exact_mod_cast hW2card
        have e3 : (Nat.card ↥data.W : ℚ) = (hyp.w1 : ℚ) * (hyp.w2 : ℚ) := by
          exact_mod_cast hWcard
        rw [e1, e2, e3]
        ring

/-- **Type-`P` order factorization** `|M| = |M_F|·|U|·|W₁|`.  The type-`P` decomposition is a double
semidirect product `M = (H ⋊ U) ⋊ W₁`: `W₁` complements the derived subgroup `M' = [M,M]` in `M`
(`M_complement`, `|M| = |M'|·|W₁|`), and `U` complements the Fitting kernel `H = M_F` in `M'`
(`derived_complement`, `|M'| = |H|·|U|`).  For the Type-II partner `S` with `|W₁(S)| = w₂` this is
the `|S| = |S_F|·|U|·w₂` input (`hS`) to Peterfalvi (10.8)'s coherence estimate. -/
theorem typePData_card_eq_H_mul_U_mul_W1 [Finite G] {M : Subgroup G} (data : TypePData M) :
    Nat.card ↥M = Nat.card ↥data.H * Nat.card ↥data.U * Nat.card ↥data.W1 := by
  have hM'le : derivedInG M ≤ M := Subgroup.map_subtype_le _
  -- `|M'|·|W₁| = |M|` (the `M = M' ⋊ W₁` complement).
  have h1 : Nat.card ↥(derivedInG M) * Nat.card ↥data.W1 = Nat.card ↥M := by
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hM'le).toEquiv,
      ← Nat.card_congr (Subgroup.subgroupOfEquivOfLe data.W1_le).toEquiv]
    exact data.M_complement.card_mul_card
  -- `|H|·|U| = |M'|` (the `M' = H ⋊ U` complement).
  have h2 : Nat.card ↥data.H * Nat.card ↥data.U = Nat.card ↥(derivedInG M) := by
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe data.H_le).toEquiv,
      ← Nat.card_congr (Subgroup.subgroupOfEquivOfLe data.U_le).toEquiv]
    exact data.derived_complement.card_mul_card
  calc Nat.card ↥M = Nat.card ↥(derivedInG M) * Nat.card ↥data.W1 := h1.symm
    _ = Nat.card ↥data.H * Nat.card ↥data.U * Nat.card ↥data.W1 := by rw [← h2]

open scoped Classical FiniteInduce in
open OddOrder.Peterfalvi.S09 in
open OddOrder.Peterfalvi.S09.Cert in
/-- **Peterfalvi (10.8), line 87 lower bound — the (7.8.b) ρ-norm bound for `ζ^{τ₁}`**:
`‖ζ^{τ₁,ρ}‖² ≥ 1 − ŵ₁/|M'|`.

This is Peterfalvi (7.8.b) specialised to the coherent extension `τ₁` of `ζ ∈ 𝒮` in the present
type-`P` `Hypothesis M`.  It is the M-side analogue of the §14 pattern
`MHypothesis.rhoNormSq_ge_lower` (`S16_NonExistenceG.lean`), which couples the `ρ`-norm to the
(7.8.b) Dade-integral engine `zetaNuRhoNormSqGeOfDade` (`S09_CertificateDischarge.lean`) via a
`Hypothesis78`-for-`M` certificate (`H = M'`, `ν = coh.tau1`).  Together with the proven line-83
**upper** bound (`chiRhoNormSq_zeta_le_line83`) and the strict `|A(M)|/|M| < 1/w₁`
(`card_typePA_div_card_lt_inv_w1`) this closes the (10.8) estimate's `hA` (line 87).

**Genuine, ungated lane-a gate** (the last §7 char-theoretic input to `hA`): the honest route is the
S16 `chiRhoNormSq_eq_zetaNuRhoNormSq` coupling ported to type-`P` `M`; it does **not** depend on the
(10.7) partner Frobenius structure (that gates only `hB`).  See
`notes/peterfalvi/s10_7_derived_frobenius.md` (2026-07-08 update²).

**Proof (type-`P` port of S16 `exists_M_hypothesis78`)**: assemble a §7 Dade certificate
`S09.Hypothesis78 G (typePA M) M` with `H = M' = derivedInG M`, `K = M'.subgroupOf M`, distinguished
`ζ_0 = Ind_K θ_0 = params.zeta` (placed by `exists_placed_induced_family`), and `ν = coh.tau1`, then
feed the (7.8.b) Dade-integral engine `zetaNuRhoNormSqGeOfDade`.  The `(7.8.a)` agreement `hagree`
bridges the *restricted* Dade map `toHypothesis71.τ` (over `A(M)`) to the *full* map
(`coherence_hagree_dadeMap`, over `A_0(M)`) via `S04.FullDadeIsometryData.restrict_apply`; the
`ζ_0^ν ⊥ 1_G` fact is `coherence_extension_orthogonal_constOne` (using the conjugate member `ζ̄_0`);
`2e+1 ≤ h` is `card_derived_ge`.  The engine bound `1 − e/h ≤ ‖ζ_0^{νρ}‖²` is then rewritten to the
goal via `e = w₁`, `h = |M'|`, and the `chiRhoNormSq = zetaNuRhoNormSq` bridge (mirroring
S16 `chiRhoNormSq_eq_zetaNuRhoNormSq`). -/
theorem Hypothesis.chiRhoNormSq_zeta_ge_line78 [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    {hyp : Hypothesis M} {params : CharacterParameters hyp} (coh : CoherentHypothesis hyp params)
    (_hmu : params.mu = hyp.muGrid hG hG.odd)
    (_hos : params.omegaSigma = hyp.alignedOmegaSigmaGrid hG hG.odd)
    (hzS : params.zeta ∈ inducedFamily M) (hz1 : params.zeta 1 = (hyp.w1 : ℂ))
    (hzconj : params.zeta.conj ≠ params.zeta)
    (_hδpm : params.delta = 1 ∨ params.delta = -1)
    (_hδj : ∀ j : Fin hyp.w2, j ≠ 0 → hyp.muColumnSign hG hG.odd j = params.delta) :
    (1 : ℝ) - (hyp.w1 : ℝ) / (Nat.card ↥(derivedInG M) : ℝ)
      ≤ (hyp.toFamilyHypothesis71).chiRhoNormSq (coh.tau1 params.zeta) 0 := by
  have := hyp.finiteG
  classical
  -- **Setup**: `H = M' = derivedInG M`, `K = M'.subgroupOf M ⊴ M`.
  have hHL : derivedInG M ≤ M := Subgroup.map_subtype_le _
  have hKnormal0 : ((derivedInG M).subgroupOf M).Normal := by
    rw [derivedInG, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
    infer_instance
  set K : Subgroup ↥M := (derivedInG M).subgroupOf M with hKdef
  have : K.Normal := hKnormal0
  have hHnorm : ∀ (l : ↥M) ⦃h : G⦄, h ∈ derivedInG M →
      (↑l : G) * h * (↑l : G)⁻¹ ∈ derivedInG M := by
    intro l h hh
    have hhM : h ∈ M := hHL hh
    have hmem : (⟨h, hhM⟩ : ↥M) ∈ K := (Subgroup.mem_subgroupOf).mpr hh
    have hconj := hKnormal0.conj_mem ⟨h, hhM⟩ hmem l
    rw [Subgroup.mem_subgroupOf] at hconj
    simpa using hconj
  have hAH : typePA M hyp.typeP = (derivedInG M : Set G) \ {1} :=
    typePA_eq_sharpSubgroup_derivedInG M hyp.typeP
  -- `M`-stability of `A(M) = typePA` (the input to `toHypothesis71`).
  have hnorm : ∀ (l : ↥M) ⦃a : G⦄, a ∈ typePA M hyp.typeP →
      (↑l : G) * a * (↑l : G)⁻¹ ∈ typePA M hyp.typeP := fun l a ha =>
    ((Subgroup.mem_set_normalizer_iff).mp (hyp.le_normalizer_typePA l.2) a).mp ha
  -- **Placed induced family** with the distinguished `ζ_0 = Ind_K θ_0 = params.zeta`.
  obtain ⟨θz, hθz_ne, hθz_eq⟩ := hzS
  have hχ_range : params.zeta ∈ Set.range
      (fun φ : IrreducibleCharacter ↥K =>
        ClassFunction.induce K (φ : ClassFunction ↥K ℂ)) :=
    ⟨θz, hθz_eq.symm⟩
  have hχ_ne : params.zeta ≠ ClassFunction.induce K
      (trivialIrreducibleCharacter ↥K : ClassFunction ↥K ℂ) := by
    rw [hθz_eq]; exact induce_ne_trivialChar_induce K θz hθz_ne
  obtain ⟨n, θ, ind1H, hind1H, hθ0eq, htriv, hinj, hcover⟩ :=
    exists_placed_induced_family K params.zeta hχ_range hχ_ne
  have hne_triv : ∀ i : Fin (n + 1), i ≠ ind1H →
      θ i ≠ trivialIrreducibleCharacter ↥K := by
    intro i hi hcontra
    apply hi; apply hinj
    change ClassFunction.induce K (θ i : ClassFunction ↥K ℂ)
      = ClassFunction.induce K (θ ind1H : ClassFunction ↥K ℂ)
    rw [hcontra, htriv]
  have hSmem : ∀ i : Fin (n + 1), i ≠ ind1H →
      ClassFunction.induce K (θ i : ClassFunction ↥K ℂ) ∈ hyp.Sset :=
    fun i hi => ⟨θ i, hne_triv i hi, rfl⟩
  -- **Degrees**: `d i = θ_i(1)`, `Ind(θ_0)(1) = [M:K] = w₁`, and `|M| = w₁·|M'|`.
  have hKindex : K.index = hyp.w1 := by
    rw [hKdef, Hypothesis.w1, Hypothesis.W1]; exact hyp.typeP.card_W1_eq_derived_index.symm
  have hcardM : Nat.card ↥M = hyp.w1 * Nat.card ↥(derivedInG M) := by
    have hsub : Nat.card ↥K = Nat.card ↥(derivedInG M) := by
      rw [hKdef]; exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHL).toEquiv
    rw [← Subgroup.index_mul_card K, hKindex, hsub]
  let d : Fin (n + 1) → ℂ := fun i => (θ i : ClassFunction ↥K ℂ) (1 : ↥K)
  have hd : ∀ i, d i = (θ i : ClassFunction ↥K ℂ) (1 : ↥K) := fun _ => rfl
  have hz0eq : ClassFunction.induce K (θ 0 : ClassFunction ↥K ℂ) (1 : ↥M)
      = params.zeta 1 := by rw [hθ0eq]
  have hdeg0 : ClassFunction.induce K (θ 0 : ClassFunction ↥K ℂ) (1 : ↥M)
      = (K.index : ℂ) := by
    rw [hz0eq, hz1, hKindex]
  have hdeg : ∀ i, ClassFunction.induce K (θ i : ClassFunction ↥K ℂ) (1 : ↥M)
      = d i * ClassFunction.induce K (θ 0 : ClassFunction ↥K ℂ) (1 : ↥M) := by
    intro i
    rw [ClassFunction.induce_apply_one K (θ i : ClassFunction ↥K ℂ), hdeg0, hd i]; ring
  have hdeg_match : ClassFunction.induce K (θ 0 : ClassFunction ↥K ℂ) (1 : ↥M)
      = ClassFunction.induce K (θ ind1H : ClassFunction ↥K ℂ) (1 : ↥M) := by
    rw [hdeg0, htriv]
    exact (induce_trivialChar_apply_eq_index K (Subgroup.one_mem _)).symm
  -- **Support** of the difference vectors in `A(M) = (M')#` and in `A_0(M)`.
  have psi_support : ∀ i, (ClassFunction.induce K (θ i : ClassFunction ↥K ℂ)
        - d i • ClassFunction.induce K (θ 0 : ClassFunction ↥K ℂ)).support
      ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (typePA M hyp.typeP) M := by
    intro i
    refine (induce_diff_support (θ i) (θ 0) (d i) (hdeg i)).trans ?_
    intro x hx
    rw [Set.mem_sdiff, SetLike.mem_coe, Set.mem_singleton_iff] at hx
    exact (mem_supportInSubgroup_sharp_subgroupOf_iff (derivedInG M) hAH x).mpr ⟨hx.1, hx.2⟩
  have hsupp_full : ∀ i, (ClassFunction.induce K (θ i : ClassFunction ↥K ℂ)
        - d i • ClassFunction.induce K (θ 0 : ClassFunction ↥K ℂ)).support
      ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (typePA0 M hyp.typeP) M := by
    intro i
    refine (psi_support i).trans ?_
    intro x hx
    rw [OddOrder.Peterfalvi.S04.mem_supportInSubgroup] at hx ⊢
    exact Set.mem_union_left _ hx
  have hzeta_ind1H : θ ind1H = trivialIrreducibleCharacter ↥K := htriv
  -- The restricted Dade isometry certificate for `H71.τ = toHypothesis71.τ`.
  have hτ : OddOrder.Peterfalvi.S04.IsDadeIsometry (G := G) (k := ℂ) (L := M)
      hyp.toHypothesis71.τ :=
    ((hyp.dadeData.dade.fullDadeIsometryData).restrict Set.subset_union_left
      hnorm).toDadeIsometryData.isDadeIsometry
  -- **`ν`-isometry** on the family (`ν = coh.tau1 = coherent extension`).
  have hnu_isometry : ∀ i j : Fin (n + 1), i ≠ ind1H → j ≠ ind1H →
      ClassFunction.inner (coh.tau1 (ClassFunction.induce K (θ i : ClassFunction ↥K ℂ)))
          (coh.tau1 (ClassFunction.induce K (θ j : ClassFunction ↥K ℂ)))
        = ClassFunction.inner (ClassFunction.induce K (θ i : ClassFunction ↥K ℂ))
          (ClassFunction.induce K (θ j : ClassFunction ↥K ℂ)) :=
    fun i j hi hj => coherence_extension_inner_eq_on_family coh.coherent (hSmem i hi) (hSmem j hj)
  -- **(7.8.a) agreement** — the restricted-vs-full Dade-map bridge.
  have hagree : ∀ i : Fin (n + 1), i ≠ 0 → i ≠ ind1H →
      hyp.toHypothesis71.τ ⟨ClassFunction.induce K (θ i : ClassFunction ↥K ℂ)
          - d i • ClassFunction.induce K (θ 0 : ClassFunction ↥K ℂ), psi_support i⟩
        = coh.tau1 (ClassFunction.induce K (θ i : ClassFunction ↥K ℂ))
          - d i • coh.tau1 (ClassFunction.induce K (θ 0 : ClassFunction ↥K ℂ)) := by
    intro i hi0 hi_ind
    obtain ⟨deg_i, -, hdeg_i_eq⟩ := irreducibleCharacter_apply_one_eq_pos_natCast (θ i)
    have hcohag := coherence_hagree_dadeMap hyp.dadeData.dade coh.coherent
      (hSmem i hi_ind) (hSmem 0 (Ne.symm hind1H)) (m0 := 1) (mi := deg_i) (by norm_num)
      (by rw [hd i, hdeg_i_eq, Nat.cast_one, div_one]) (hsupp_full i)
    have hbridge : hyp.toHypothesis71.τ ⟨ClassFunction.induce K (θ i : ClassFunction ↥K ℂ)
          - d i • ClassFunction.induce K (θ 0 : ClassFunction ↥K ℂ), psi_support i⟩
        = (hyp.dadeData.dade.fullDadeIsometryData).toDadeMap
          ⟨ClassFunction.induce K (θ i : ClassFunction ↥K ℂ)
            - d i • ClassFunction.induce K (θ 0 : ClassFunction ↥K ℂ),
            (ClassFunction.mem_supportedSubmodule).mpr (hsupp_full i)⟩ := by
      change ((hyp.dadeData.dade.fullDadeIsometryData).restrict Set.subset_union_left
          hnorm).toDadeMap ⟨_, psi_support i⟩ = _
      -- `restrict_apply` は `rfl` なので `exact` が直接見通す (v4.33 では `rw` が照合できない)
      exact congrArg _ (Subtype.ext rfl)
    rw [hbridge]; exact hcohag
  -- **Assemble** the (7.8) Dade certificate.
  set H78 := hypothesis78OfDade hyp.toHypothesis71 hτ (derivedInG M) hHL hHnorm hAH θ hinj hcover
    d psi_support hdeg ind1H hind1H hzeta_ind1H hdeg_match coh.tau1 hnu_isometry hagree
    with hH78def
  -- `e = [M:M'] = w₁`, `h = |M'|`.
  have hci : H78.complementIndex = hyp.w1 := by
    have hcieq : H78.complementIndex = Nat.card ↥M / Nat.card ↥(derivedInG M) := rfl
    rw [hcieq, hcardM, Nat.mul_div_cancel _ Nat.card_pos]
  have hko : H78.kernelOrder = Nat.card ↥(derivedInG M) := rfl
  have hsmall : H78.smallIndex := by
    change 2 * H78.complementIndex + 1 ≤ H78.kernelOrder
    rw [hci, hko]
    have hMp := hyp.card_derived_ge hG
    have hw2 : 0 < hyp.w2 := Nat.card_pos
    calc 2 * hyp.w1 + 1 = (2 * hyp.w1 + 1) * 1 := (mul_one _).symm
      _ ≤ (2 * hyp.w1 + 1) * hyp.w2 := Nat.mul_le_mul_left _ hw2
      _ ≤ Nat.card ↥(derivedInG M) := hMp
  -- **(7.8.a) coefficient** `a`.
  obtain ⟨a, ha⟩ := exists_betaDecomp_a H78
    (Submodule.sub_mem _
      (ClassFunction.induce_mem_ZIrr K (θ ind1H).property.mem_ZIrr)
      (ClassFunction.induce_mem_ZIrr K (θ 0).property.mem_ZIrr))
    (coh.coherent.extension_mem_ZIrr _ (Submodule.subset_span (hSmem 0 (Ne.symm hind1H))))
  -- **`ζ_0^ν ⊥ 1_G`** via the conjugate member `ζ̄_0 = Ind_K θ̄_0 ∈ S`.
  obtain ⟨θ0', hθ0'coe⟩ : ∃ t : IrreducibleCharacter ↥K,
      (t : ClassFunction ↥K ℂ) = (θ 0 : ClassFunction ↥K ℂ).conj :=
    ⟨⟨(θ 0 : ClassFunction ↥K ℂ).conj, (θ 0).isIrreducible.conj⟩, rfl⟩
  have hθ0_ne : θ 0 ≠ trivialIrreducibleCharacter ↥K := hne_triv 0 (Ne.symm hind1H)
  have hθ0'_ne : θ0' ≠ trivialIrreducibleCharacter ↥K := by
    intro h
    apply hθ0_ne
    have hcoe : (θ 0 : ClassFunction ↥K ℂ).conj = trivialClassFunction ↥K := by
      rw [← hθ0'coe]
      simpa using congrArg (fun c : IrreducibleCharacter ↥K => (c : ClassFunction ↥K ℂ)) h
    apply Subtype.ext
    change (θ 0 : ClassFunction ↥K ℂ) = trivialClassFunction ↥K
    rw [← ClassFunction.conj_conj (θ 0 : ClassFunction ↥K ℂ), hcoe]
    exact trivialClassFunction_isReal
  have hnorm0 : ClassFunction.inner (ClassFunction.induce K (θ 0 : ClassFunction ↥K ℂ))
      (ClassFunction.induce K (θ 0 : ClassFunction ↥K ℂ)) = 1 := by
    rw [hθ0eq]
    simpa using irreducibleCharacter_inner_eq_ite
      (⟨params.zeta, params.zeta_irreducible⟩ : IrreducibleCharacter ↥M)
      (⟨params.zeta, params.zeta_irreducible⟩ : IrreducibleCharacter ↥M)
  have hnorm0' : ClassFunction.inner (ClassFunction.induce K (θ0' : ClassFunction ↥K ℂ))
      (ClassFunction.induce K (θ0' : ClassFunction ↥K ℂ)) = 1 := by
    rw [hθ0'coe, ← ClassFunction.induce_conj, inner_conj_conj, hnorm0, star_one]
  have hne_zeta : (⟨params.zeta, params.zeta_irreducible⟩ : IrreducibleCharacter ↥M)
      ≠ ⟨params.zeta.conj, params.zeta_irreducible.conj⟩ := by
    intro h
    exact hzconj
      (congrArg (fun c : IrreducibleCharacter ↥M => (c : ClassFunction ↥M ℂ)) h).symm
  have horth : ClassFunction.inner (ClassFunction.induce K (θ 0 : ClassFunction ↥K ℂ))
      (ClassFunction.induce K (θ0' : ClassFunction ↥K ℂ)) = 0 := by
    rw [hθ0'coe, ← ClassFunction.induce_conj, hθ0eq]
    have hite := irreducibleCharacter_inner_eq_ite
      (⟨params.zeta, params.zeta_irreducible⟩ : IrreducibleCharacter ↥M)
      (⟨params.zeta.conj, params.zeta_irreducible.conj⟩ : IrreducibleCharacter ↥M)
    rw [if_neg hne_zeta] at hite
    simpa using hite
  have hdeg' : ClassFunction.induce K (θ0' : ClassFunction ↥K ℂ) (1 : ↥M)
      = 1 * ClassFunction.induce K (θ 0 : ClassFunction ↥K ℂ) (1 : ↥M) := by
    rw [one_mul, ClassFunction.induce_apply_one, ClassFunction.induce_apply_one]
    congr 1
    rw [hθ0'coe, ClassFunction.conj_apply]
    obtain ⟨m, -, hm⟩ := irreducibleCharacter_apply_one_eq_pos_natCast (θ 0)
    rw [hm, star_natCast]
  have hsupp : (ClassFunction.induce K (θ0' : ClassFunction ↥K ℂ)
        - ClassFunction.induce K (θ 0 : ClassFunction ↥K ℂ)).support ⊆ hyp.A0 := by
    have hds := induce_diff_support θ0' (θ 0) 1 hdeg'
    rw [one_smul] at hds
    intro x hx
    have hxd := hds hx
    rw [Set.mem_sdiff, SetLike.mem_coe, Set.mem_singleton_iff] at hxd
    have hmem := (mem_supportInSubgroup_sharp_subgroupOf_iff (derivedInG M) hAH x).mpr
      ⟨hxd.1, hxd.2⟩
    change x ∈ OddOrder.Peterfalvi.S04.supportInSubgroup (typePA0 M hyp.typeP) M
    rw [OddOrder.Peterfalvi.S04.mem_supportInSubgroup] at hmem ⊢
    exact Set.mem_union_left _ hmem
  have hζ0_1 : ClassFunction.inner (ClassFunction.induce K (θ 0 : ClassFunction ↥K ℂ))
      (Hypothesis71.constOne ↥M) = 0 := inner_induce_constOne_eq_zero K (θ 0) hθ0_ne
  have hζ0'_1 : ClassFunction.inner (ClassFunction.induce K (θ0' : ClassFunction ↥K ℂ))
      (Hypothesis71.constOne ↥M) = 0 := inner_induce_constOne_eq_zero K θ0' hθ0'_ne
  have hτ_smul : ∀ (c : ℂ) (x : ClassFunction ↥M ℂ), hyp.tau (c • x) = c • hyp.tau x :=
    dadeIntegralCharacterMap_smul_complex hyp.dadeData.dade
      (hyp.dadeData.dade.fullDadeIsometryData)
  have htau1 : ∀ φ : ClassFunction ↥M ℂ, φ.support ⊆ hyp.A0 →
      ClassFunction.inner (hyp.tau φ) (Hypothesis71.constOne G)
        = ClassFunction.inner φ (Hypothesis71.constOne ↥M) := by
    intro φ hφ
    rw [show hyp.tau φ = hyp.dadeData.dade.dadeMap (k := ℂ)
        ⟨φ, (ClassFunction.mem_supportedSubmodule).mpr hφ⟩ from
      OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_apply_of_support hyp.dadeData.dade
        (hyp.dadeData.dade.fullDadeIsometryData) hφ]
    exact inner_tau_supported_constOne
      ({ hyp := hyp.dadeData.dade
         τ := hyp.dadeData.dade.dadeMap (k := ℂ)
         isDadeMap := hyp.dadeData.dade.isDadeMap_dadeMap }
        : Hypothesis71 G (typePA0 M hyp.typeP) M)
      ⟨φ, (ClassFunction.mem_supportedSubmodule).mpr hφ⟩
  have hζ0'mem : ClassFunction.induce K (θ0' : ClassFunction ↥K ℂ) ∈ hyp.Sset :=
    ⟨θ0', hθ0'_ne, rfl⟩
  have hzeta0nu : ClassFunction.inner
      (coh.tau1 (ClassFunction.induce K (θ 0 : ClassFunction ↥K ℂ)))
      (Hypothesis71.constOne G) = 0 :=
    coherence_extension_orthogonal_constOne coh.coherent hτ_smul htau1
      (hSmem 0 (Ne.symm hind1H)) hζ0'mem hnorm0 hnorm0' horth hsupp hζ0_1 hζ0'_1
  -- **The (7.8.b) engine bound** `1 − e/h ≤ ‖ζ_0^{νρ}‖²`.
  have hbound : (1 : ℝ) - (H78.complementIndex : ℝ) / (H78.kernelOrder : ℝ)
      ≤ H78.zetaNuRhoNormSq :=
    zetaNuRhoNormSqGeOfDade hyp.toHypothesis71 hτ (derivedInG M) hHL hHnorm hAH θ hinj hcover d
      psi_support hdeg ind1H hind1H hzeta_ind1H hdeg_match coh.tau1 hnu_isometry hagree hzeta0nu
      hnorm0 a ha hsmall
  -- **Norm bridge** `chiRhoNormSq = zetaNuRhoNormSq` (mirrors S16's norm-bridge lemma).
  have hpsi : coh.tau1 params.zeta = H78.nu (H78.hyp76.zeta H78.zetaDistinct) := by
    change coh.tau1 params.zeta = coh.tau1 (ClassFunction.induce K (θ 0 : ClassFunction ↥K ℂ))
    rw [hθ0eq]
  have hnorm_eq : (hyp.toFamilyHypothesis71).chiRhoNormSq (coh.tau1 params.zeta) 0
      = H78.zetaNuRhoNormSq := by
    have hH71 : H78.hyp76.hyp71 = hyp.toHypothesis71 := rfl
    have hcf : ((hyp.toFamilyHypothesis71).hyp71 0).chiRhoCF (coh.tau1 params.zeta)
        = H78.zetaNuRho := by
      change hyp.toHypothesis71.chiRhoCF (coh.tau1 params.zeta) = H78.zetaNuRho
      rw [Hypothesis78.zetaNuRho, hH71, ← hpsi]
    simp only [FamilyHypothesis71.chiRhoNormSq, Hypothesis78.zetaNuRhoNormSq, hcf]
    congr 1
  rw [hnorm_eq, ← hci, ← hko]
  exact hbound

open scoped Classical FiniteInduce in
/-- **The (10.8) coherence-contradiction estimate, partner-supplied form** (issue 1020
Phase 3): the norm-counting estimate with the Type-II partner and its §8/(10.7) supply
facts taken as hypotheses, so that `hB` is discharged by `g1_div_le_of_partner`.  The
unconditional form is assembled downstream (`S12_Noncoherence`), where the pair machinery
provides the supply; see issue 1020.  (The former in-file legacy instantiation — the
bare-sorry `hB` estimate and the legacy `S_not_coherent` — is retired, issue 9087.) -/
theorem typeII_coherence_contradiction_estimate_of_partner [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    {hyp : Hypothesis M} {params : CharacterParameters hyp}
    (coh : CoherentHypothesis hyp params)
    {S : Subgroup G} (data : TypePData S)
    (hSidx : ((derivedInG S).subgroupOf S).index = hyp.w2)
    (hU7 : 7 ≤ Nat.card ↥data.U)
    (hprime : (Nat.card ↥data.W1).Prime)
    (hcop : Nat.Coprime (Nat.card ↥(derivedInG S)) (Nat.card ↥data.W1))
    (hHall : OddOrder.Isaacs.Ch03.IsHallSubgroup
      (Nat.card ↥data.H).primeFactors data.H)
    (hcent : ∀ b ∈ data.H, b ≠ 1 → Subgroup.centralizer ({b} : Set G) ≤ S)
    (hfrobcap : ∀ b ∈ data.H, b ≠ 1 → ∀ y ∈ derivedInG S,
      y ∈ Subgroup.centralizer ({b} : Set G) → y ∈ data.H)
    (hW2card : Nat.card ↥data.W2 = hyp.w1)
    (hWcard : Nat.card ↥data.W = hyp.w1 * hyp.w2) :
    ∃ u : ℕ, 7 ≤ u ∧
      (1 : ℚ) - 1 / (hyp.w1 : ℚ) - 1 / (u : ℚ)
        < (hyp.w1 : ℚ) * (hyp.w2 : ℚ) / (Nat.card ↥(derivedInG M) : ℚ) := by
  classical
  obtain ⟨params', hmu, hos, hzS, hz1, hzconj, hδpm, hδj⟩ := hyp.exists_charParameters_full hG
  let coh' : CoherentHypothesis hyp params' := ⟨coh.coherent⟩
  refine ⟨Nat.card ↥data.U, hU7, ?_⟩
  have hW1card : Nat.card ↥data.W1 = hyp.w2 := by
    rw [data.card_W1_eq_derived_index]; exact hSidx
  have hS_struct : Nat.card ↥S = Nat.card ↥data.H * Nat.card ↥data.U * hyp.w2 := by
    rw [typePData_card_eq_H_mul_U_mul_W1 data, hW1card]
  have h83 := hyp.chiRhoNormSq_zeta_le_line83 hG coh' hmu hos hzS hz1 hzconj hδpm hδj
  have h78 := hyp.chiRhoNormSq_zeta_ge_line78 hG coh' hmu hos hzS hz1 hzconj hδpm hδj
  set g1g : ℚ := ((Nat.card (hyp.toFamilyHypothesis71).G0 : ℚ)
      - ((Finset.univ.filter (fun g : G => g ∉ hyp.dadeData.dade.dadeSupport
          ∧ (orderOf g).Coprime hyp.w1)).card : ℚ)) / (Nat.card G : ℚ) with hg1g_def
  have hA : (1 : ℚ) - g1g - 1 / (hyp.w1 : ℚ)
      < (hyp.w1 : ℚ) / (Nat.card ↥(derivedInG M) : ℚ) := by
    have hpaR : (Nat.card ↥(typePA M hyp.typeP) : ℝ) / (Nat.card ↥M : ℝ)
        < 1 / (hyp.w1 : ℝ) := by
      have h := (Rat.cast_lt (K := ℝ)).mpr hyp.card_typePA_div_card_lt_inv_w1
      push_cast at h; exact h
    have hg1gR : (g1g : ℝ) = (Nat.card G : ℝ)⁻¹
        * ((Nat.card (hyp.toFamilyHypothesis71).G0 : ℝ)
          - ((Finset.univ.filter (fun g : G => g ∉ hyp.dadeData.dade.dadeSupport
              ∧ (orderOf g).Coprime hyp.w1)).card : ℝ)) := by
      rw [hg1g_def]; push_cast; rw [div_eq_inv_mul]
    rw [← Rat.cast_lt (K := ℝ)]
    push_cast
    linarith [h78, h83, hpaR, hg1gR]
  have hB : g1g ≤ ((Nat.card ↥data.H : ℚ) - 1) / (Nat.card ↥S : ℚ)
      + ((hyp.w1 : ℚ) * hyp.w2 - hyp.w1 - hyp.w2 + 1) / ((hyp.w1 : ℚ) * hyp.w2) := by
    rw [hg1g_def]
    exact hyp.g1_div_le_of_partner data hprime hcop hHall hcent hfrobcap
      hW1card hW2card hWcard
  have hw1 : 1 ≤ hyp.w1 := Nat.card_pos
  have hw2 : 1 ≤ hyp.w2 := Nat.card_pos
  have hu : 1 ≤ Nat.card ↥data.U := by omega
  have hH : 1 ≤ Nat.card ↥data.H := Nat.card_pos
  have hMp : 1 ≤ Nat.card ↥(derivedInG M) := Nat.card_pos
  exact typeII_coherence_estimate_chain hw1 hw2 hu hH hMp hS_struct hA hB

end OddOrder.Peterfalvi.S12


