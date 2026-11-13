-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S15_HonestTypeP2A0
-- name    : OddOrder_Peterfalvi_S15_HonestTypeP2A0
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T15:58:02.799473+00:00
-- url     : https://prove2.me/theorems/9e1b2618-3140-4b5c-a86a-cb3cfa3678b4
-- title:
--   Peterfalvi (8.10)/(8.15): the honest type $P_2$ support $A_0(S)=A(S)\cup V^S$
-- statement:
--   Formalizes the honest Dade support $A_0(S)=A(S)\cup V^S$ for a type $P_2$ maximal subgroup $S$ (Peterfalvi, *Character Theory for the Odd Order Theorem*, §8/§13, (8.10)/(8.15)).
--
--   Main declarations: `Hypothesis.dadeHypS0` ((13.18) `S`-instance `'A0`-Dade hypothesis); `Hypothesis.dadeHypT0` (`T`-instance `'A0`-Dade hypothesis); `Hypothesis.sInstance_dade0_eq_induce` (`τ_S = Ind_S^G` on `A₀(S)`-supported functions); `Hypothesis.tauS_mu_vanish_on_V` (Prime-`TI` `V`-value pin, full-grid form).
--
--   The bundle also proves 10 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S15_HonestTypeP2A0.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S15_HonestTypeP2A0.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S15_SAndT_Setup_HypothesisBasics
import Definitions.Def_OddOrder_Peterfalvi_S15_SAndT_Setup_HypothesisSwap
import Definitions.Def_OddOrder_Peterfalvi_S15_SAndT_Setup_DegreesFirstSplit
import Definitions.Def_OddOrder_Peterfalvi_S15_SAndT_Setup_PairStructure
import Definitions.Def_OddOrder_Peterfalvi_S15_SAndT_Setup_CountingLayer
import Definitions.Def_OddOrder_Peterfalvi_S15_SAndT_Setup_Canonicalization
import Definitions.Def_OddOrder_Peterfalvi_S13_ElementaryAbelianKernel
import Definitions.Def_OddOrder_BG_Ch2_Uniqueness_S07_Theorem74
import Definitions.Def_OddOrder_Peterfalvi_S15_SAndT_Setup_TSideDegrees
import Definitions.Def_OddOrder_Peterfalvi_S10_TypePSupportA0
import Definitions.Def_OddOrder_Peterfalvi_S10_MinimalSimpleStructure
import Definitions.Def_OddOrder_Peterfalvi_S12_MaximalIII_IV_V_Core_Hypothesis
import Definitions.Def_OddOrder_Peterfalvi_S12_MaximalIII_IV_V_Core_CharacterParameters
import Definitions.Def_OddOrder_Peterfalvi_S12_MaximalIII_IV_V_Core_DadeCalculations
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_PrimeTIResidue
import Definitions.Def_OddOrder_Peterfalvi_S10_StructureSetup
import Definitions.Def_OddOrder_BG_Ch4_FamilyOfMaximal_S15_MF_SetupLemma151

namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

variable {G : Type*} [Group G]

/-- **(13.2.e) `normedTI` core for the `A₀`-support: no `A₀(S)`-point escapes.**  Every escaping
`A₀(S)`-point reduces to an escaping `A(S)`-point
(`S10.escaping_typePACore0_mem_typePACore`,
since `V^S` does not escape), and the honest `A(S)` has no escaping point on a type-`P₂` maximal
(`escaping_typePACore_eq_empty`, the proven (13.2.e) core via BG Theorem D(4)).  So the full
`'A0(S)` support is `normedTI`: this is the trivial-stabilizer input `∀ a, dadeHypS0.H a = ⊥` the
`τ_S = Ind_S^G` Dade=Ind bridge needs (feeding (13.18.c) `⟨Γ, 1_G⟩ = 0` etc., issue 9076). -/
theorem escaping_typePACore0_eq_empty [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hTP : OddOrder.BG.Ch4.S14.IsTypeP M) (data : TypePData M) :
    OddOrder.GroupTheory.escapingCentralizerSet M (S10.typePACore0 M data) = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro a ha
  have hAesc := S10.escaping_typePACore0_mem_typePACore data ha
  rw [escaping_typePACore_eq_empty hG hnoV hM hTP] at hAesc
  exact Set.notMem_empty a hAesc

/-- **(13.18) `S`-instance `'A0`-Dade hypothesis**: the `Hypothesis`-level instantiation of
`S10.dadeSupportHypothesisData_typePACore0` at the type-`P` maximal `S` (via `hyp.S_maximal`/
`hyp.S_isTypeP`/`hyp.Sdata`), packaging the honest full support `A₀(S) = A(S) ∪ V^S` as an
`S04.Hypothesis`.  This is the `S`-side Dade datum for the (13.18) cross-relation
`τ_S(μ_{0j} − μ_{01}) = η_{0j} − η_{01}` — the `μ`-column differences are `A₀(S)`-supported (the
`V_S`-part falls outside `A(S) ⊆ S'`), so the `A(S)`-Dade `dadeHypS` cannot see them; `dadeHypS0`
is the correction.  (Its `.fullDadeIsometryData` inherits the one deep `'A0`-`normedTI` pin
`S10.not_isConj_typePACore_typePV`.) -/
noncomputable def Hypothesis.dadeHypS0 [Fintype G] [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G)) :
    OddOrder.Peterfalvi.S04.Hypothesis G (S10.typePACore0 hyp.S hyp.Sdata) hyp.S :=
  (S10.dadeSupportHypothesisData_typePACore0 hG hyp.S_maximal (hyp.S_isTypeP hG)
    hyp.Sdata).some.dade

/-- **`T`-instance `'A0`-Dade hypothesis** (the S↔T mirror of `dadeHypS0`): the honest
`A₀(T) = A(T) ∪ (V_T)^T` Dade datum for `T`, from the generic type-`P₂` construction
`S10.dadeSupportHypothesisData_typePACore0` at `T`.  The constructor itself needs only
`IsTypeP T`, so it is taken as a parameter together with a `T`-side reconciled
`TypePData` (supplied by `reconciled_typePData_T`).  This is the `τ_T` underlying the (14.3.b)
bridge image `τ_T(β_T)` (`tauTbetaGrid`). -/
noncomputable def Hypothesis.dadeHypT0 [Fintype G] [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hTP : OddOrder.BG.Ch4.S14.IsTypeP hyp.T) (Tdata : TypePData hyp.T) :
    OddOrder.Peterfalvi.S04.Hypothesis G (S10.typePACore0 hyp.T Tdata) hyp.T :=
  (S10.dadeSupportHypothesisData_typePACore0 hG hyp.T_maximal hTP Tdata).some.dade

/-- **`dadeHypS0.H a = ftSupportKernel S (A₀(S)) a`** (A₀ analogue of
`dadeHypS_H_eq_ftSupportKernel`). The `'A0(S)`-instance Dade stabilizer at a support point `a` is
the faithful (8.14) signalizer kernel
`R(a) = ftSupportKernel S (A₀(S)) a`, read off the `H_eq_ftSupportKernel` field of the underlying
`DadeSupportHypothesisData` that `dadeHypS0` is projected from. -/
theorem Hypothesis.dadeHypS0_H_eq_ftSupportKernel [Fintype G] [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (a : {a : G // a ∈ S10.typePACore0 hyp.S hyp.Sdata}) :
    (hyp.dadeHypS0 hG).H a =
      OddOrder.Peterfalvi.S10.ftSupportKernel hyp.S (S10.typePACore0 hyp.S hyp.Sdata) a.1 :=
  (S10.dadeSupportHypothesisData_typePACore0 hG hyp.S_maximal (hyp.S_isTypeP hG)
    hyp.Sdata).some.H_eq_ftSupportKernel a

/-- **All `'A0(S)`-instance Dade stabilizers vanish** (the (13.2.e) `A₀` `normedTI` conclusion):
since no `A₀(S)`-point escapes (`escaping_typePACore0_eq_empty`), the faithful kernel
`ftSupportKernel S (A₀(S)) a` is `⊥` at every support point
(`ftSupportKernel_eq_bot_of_not_escaping`).  This is the trivial-stabilizer input the
`τ_S = Ind_S^G` Dade=Ind bridge consumes (for (13.18.c) `⟨Γ,1_G⟩ = 0` and pin C
`tauS_mu_row0_vanish_on_V`). -/
theorem Hypothesis.forall_dadeHypS0_H_eq_bot [Fintype G] [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G)) :
    ∀ a : {a : G // a ∈ S10.typePACore0 hyp.S hyp.Sdata}, (hyp.dadeHypS0 hG).H a = ⊥ := by
  intro a
  rw [hyp.dadeHypS0_H_eq_ftSupportKernel hG a]
  have hempty := escaping_typePACore0_eq_empty hG hnoV hyp.S_maximal
    (hyp.S_isTypeP hG) hyp.Sdata
  exact OddOrder.Peterfalvi.S10.ftSupportKernel_eq_bot_of_not_escaping
    (fun hesc => Set.notMem_empty a.1 (hempty ▸ hesc))

open OddOrder.RepresentationTheory in
open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **`τ_S = Ind_S^G` on `A₀(S)`-supported functions** (the honest `'A0`-Dade=Ind bridge): for `f`
supported in `A₀(S)`, the `'A0(S)`-Dade lift `dadeIntegralCharacterMap (dadeHypS0 …) f` equals plain
induction `Ind_S^G f`.  All `'A0(S)`-instance Dade stabilizers vanish
(`forall_dadeHypS0_H_eq_bot`, the (13.2.e) `A₀` `normedTI`), so on the `A₀(S)`-supported span the
Dade map coincides with the induction map (`dadeMap_eq_induce_of_supported_on_trivial_H` at the full
support `A₁ = A₀(S)`).  This is the `'A0` analogue of `sInstance_dade_eq_induce`; it is the
`τ_S = Ind` half of (13.18.c) `⟨Γ,1_G⟩ = 0` (`gammaGrid_orthogonal_one`) and of pin C
`tauS_mu_row0_vanish_on_V` (both additionally need prime-`TI` `μ`-value content, issue 9014). -/
theorem Hypothesis.sInstance_dade0_eq_induce [Fintype G] [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G))
    {f : ClassFunction ↥hyp.S ℂ}
    (hf : f.support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (S10.typePACore0 hyp.S hyp.Sdata) hyp.S) :
    OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS0 hG)
        ((hyp.dadeHypS0 hG).fullDadeIsometryData) f
      = ClassFunction.induce hyp.S f := by
  rw [OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_apply_of_support (hyp.dadeHypS0 hG)
    ((hyp.dadeHypS0 hG).fullDadeIsometryData) hf]
  exact OddOrder.Peterfalvi.S14.dadeMap_eq_induce_of_supported_on_trivial_H (hyp.dadeHypS0 hG)
    (subset_refl _)
    (fun l _ ha => (S10.typePACore0_conj_mem hyp.Sdata l.2).mpr ha)
    (fun a => by
      rw [OddOrder.Peterfalvi.S04.Hypothesis.restrict_H]
      exact hyp.forall_dadeHypS0_H_eq_bot hG hnoV ⟨a.1, a.2⟩)
    ⟨f, (ClassFunction.mem_supportedSubmodule).mpr hf⟩

/-- **Peterfalvi (4.8), full-grid `μ`-column-difference support** (issue 1017; the all-rows/all-cols
generalization of `tauS_mu_row0_diff_support`).  For any row `i` and any two nontrivial columns
`j₁, j₂ ≠ 0`, the difference `μ_{i,j₁} − μ_{i,j₂}` is supported in `A₀(S) = A(S) ∪ V^S`.  Both
columns have equal degree `u` (`mu_apply_one_eq_u`), so the (4.3.c) support grounding field
`mu_diff_support` applies.  This is the support input the general prime-`TI` cross-relation
`tauS_mu_cross` (`S15_BridgeCharacter`) consumes on each row of a reducible μ-column difference. -/
theorem Hypothesis.tauS_mu_diff_support [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (i : Fin hyp.q) {j1 j2 : Fin hyp.p}
    (hj1 : j1 ≠ ⟨0, hyp.p_prime.pos⟩) (hj2 : j2 ≠ ⟨0, hyp.p_prime.pos⟩) :
    (hyp.mu i j1 - hyp.mu i j2).support
      ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (S10.typePACore0 hyp.S hyp.Sdata) hyp.S :=
  hyp.mu_diff_support i hj1 hj2
    ((hyp.mu_apply_one_eq_u hG i j1 hj1).trans (hyp.mu_apply_one_eq_u hG i j2 hj2).symm)

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Prime-`TI` `V`-value pin, full-grid form** (the all-rows/all-cols generalization of
`tauS_mu_row0_vanish_on_V`).  On the regular set `V^S = conjClassSet(W ∖ (W₁ ∪ W₂))`, for any row
`i` and columns `j₁, j₂` (arbitrary — the value identity `mu_apply_of_not_mem_W2` holds off `W₂`
regardless of column), the `'A0(S)`-Dade lift `τ_S(μ_{i,j₁} − μ_{i,j₂})` agrees with the grid
difference `η_{i,j₁} − η_{i,j₂}`.  Both reduce to the same `ω`-value there (`μ_{i,l}|_V = δ_l·ω = ω`
by `mu_apply_of_not_mem_W2` + `delta_eq_one_S`; `η_{i,l}|_V = ω` by `eta_eq_tau_omega` +
`tau3_apply_of_regular`).  The nontriviality `j₁, j₂ ≠ 0` is only needed for the *support* input
`tauS_mu_diff_support`. -/
theorem Hypothesis.tauS_mu_vanish_on_V [Fintype G] [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G)) (i : Fin hyp.q)
    {j1 j2 : Fin hyp.p}
    (hj1 : j1 ≠ ⟨0, hyp.p_prime.pos⟩) (hj2 : j2 ≠ ⟨0, hyp.p_prime.pos⟩) :
    ∀ x ∈ conjClassSet ((hyp.W : Set G) \ ((hyp.W1 : Set G) ∪ (hyp.W2 : Set G))),
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypS0 hG)
          ((hyp.dadeHypS0 hG).fullDadeIsometryData)
          (hyp.mu i j1 - hyp.mu i j2)
        - (hyp.eta i j1 - hyp.eta i j2)) x = 0 := by
  classical
  intro x hx
  obtain ⟨w, hw, g, hg⟩ := OddOrder.GroupTheory.mem_conjClassSet.mp hx
  have hwW : w ∈ hyp.W := hw.1
  have hw12 : w ∉ (hyp.W1 : Set G) ∪ (hyp.W2 : Set G) := hw.2
  have hw2 : w ∉ (hyp.W2 : Set G) := fun h => hw12 (Or.inr h)
  have hwS : w ∈ hyp.S := ((le_of_eq hyp.W_eq_inter).trans inf_le_left) hwW
  have hconjwx : IsConj w x := isConj_iff.mpr ⟨g, hg⟩
  have hwV : w ∈ OddOrder.GroupTheory.typePV hyp.S hyp.Sdata := by
    constructor
    · have hWeq : (hyp.Sdata.W : Set G) = (hyp.W : Set G) := by
        rw [hyp.Sdata.W_eq, hyp.Sdata_W1_eq, hyp.Sdata_W2_eq, ← hyp.W_eq_join]
      rw [hWeq]; exact hwW
    · rw [hyp.Sdata_W1_eq, hyp.Sdata_W2_eq]; exact hw12
  have hwA0 : w ∈ S10.typePACore0 hyp.S hyp.Sdata :=
    Or.inr (OddOrder.GroupTheory.subset_conjClassSetIn hwV)
  have hsupp := hyp.tauS_mu_diff_support hG i hj1 hj2
  rw [OddOrder.RepresentationTheory.ClassFunction.sub_apply,
    OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_apply_of_support (hyp.dadeHypS0 hG)
      ((hyp.dadeHypS0 hG).fullDadeIsometryData) hsupp,
    (hyp.dadeHypS0 hG).dadeMap_apply]
  have h1H : (1 : G) ∈ (hyp.dadeHypS0 hG).H ⟨w, hwA0⟩ := by
    rw [hyp.forall_dadeHypS0_H_eq_bot hG hnoV ⟨w, hwA0⟩]
    exact Subgroup.mem_bot.mpr rfl
  have hconj1 : IsConj ((⟨w, hwA0⟩ :
      {a : G // a ∈ S10.typePACore0 hyp.S hyp.Sdata}).1 * 1) x := by
    rw [mul_one]; exact hconjwx
  rw [(hyp.dadeHypS0 hG).dadeValue_eq _ h1H hconj1]
  have hmu : ∀ (l : Fin hyp.p),
      hyp.mu i l ⟨w, (hyp.dadeHypS0 hG).mem_L hwA0⟩ = hyp.omega i l ⟨w, hwW⟩ := by
    intro l
    rw [hyp.mu_apply_of_not_mem_W2 i l w hwW
      ((hyp.dadeHypS0 hG).mem_L hwA0) hw2, hyp.delta_eq_one_S hG l]
    norm_num
  have heta : ∀ (l : Fin hyp.p), hyp.eta i l x = hyp.omega i l ⟨w, hwW⟩ := by
    intro l
    rw [(hyp.eta i l).of_isConj hconjwx.symm, hyp.eta_eq_tau_omega,
      hyp.tau3_apply_of_regular _ w hwW hw12]
  rw [OddOrder.RepresentationTheory.ClassFunction.sub_apply,
    OddOrder.RepresentationTheory.ClassFunction.sub_apply, hmu j1, hmu j2, heta j1, heta j2]
  ring

/-- **`dadeHypT0.H a = ftSupportKernel T (A₀(T)) a`** (mirror of
`dadeHypS0_H_eq_ftSupportKernel`). -/
theorem Hypothesis.dadeHypT0_H_eq_ftSupportKernel [Fintype G] [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hTP : OddOrder.BG.Ch4.S14.IsTypeP hyp.T) (Tdata : TypePData hyp.T)
    (a : {a : G // a ∈ S10.typePACore0 hyp.T Tdata}) :
    (hyp.dadeHypT0 hG hTP Tdata).H a =
      OddOrder.Peterfalvi.S10.ftSupportKernel hyp.T (S10.typePACore0 hyp.T Tdata) a.1 :=
  (S10.dadeSupportHypothesisData_typePACore0 hG hyp.T_maximal hTP
    Tdata).some.H_eq_ftSupportKernel a

/-- **All `'A0(T)`-instance Dade stabilizers vanish** (mirror of
`forall_dadeHypS0_H_eq_bot`; the `T`-side (13.2.e) `A₀` `normedTI` conclusion, from the generic
`escaping_typePACore0_eq_empty` at the (14.9)-parametric `hTP`/`Tdata`). -/
theorem Hypothesis.forall_dadeHypT0_H_eq_bot [Fintype G] [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G))
    (hTP : OddOrder.BG.Ch4.S14.IsTypeP hyp.T) (Tdata : TypePData hyp.T) :
    ∀ a : {a : G // a ∈ S10.typePACore0 hyp.T Tdata},
      (hyp.dadeHypT0 hG hTP Tdata).H a = ⊥ := by
  intro a
  rw [hyp.dadeHypT0_H_eq_ftSupportKernel hG hTP Tdata a]
  have hempty := escaping_typePACore0_eq_empty hG hnoV hyp.T_maximal hTP Tdata
  exact OddOrder.Peterfalvi.S10.ftSupportKernel_eq_bot_of_not_escaping
    (fun hesc => Set.notMem_empty a.1 (hempty ▸ hesc))

/-- **Peterfalvi (4.8), full-grid `ν`-row-difference support** (mirror of
`tauS_mu_diff_support`): for any column `j` and nontrivial rows `r, s ≠ 0`, the difference
`ν_{r,j} − ν_{s,j}` is supported in `A₀(T) = A(T) ∪ (V_T)^T` — both rows have equal degree `v`
(`nu_apply_one_eq_v`), so the (4.8)-at-`T` grid field `nu_diff_support` applies. -/
theorem Hypothesis.tauT_nu_diff_support [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (pins : NuGridSupplyData hyp)
    (Tdata : TypePData hyp.T) (hU : Tdata.U = hyp.V)
    (hW1 : Tdata.W1 = hyp.W2) (hW2 : Tdata.W2 = hyp.W1)
    (j : Fin hyp.p) {r s : Fin hyp.q}
    (hr : r ≠ ⟨0, hyp.q_prime.pos⟩) (hs : s ≠ ⟨0, hyp.q_prime.pos⟩) :
    (hyp.nu r j - hyp.nu s j).support
      ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (S10.typePACore0 hyp.T Tdata) hyp.T :=
  pins.nu_diff_support Tdata hU hW1 hW2 j hr hs
    ((hyp.nu_apply_one_eq_v hG pins r j hr).trans
      (hyp.nu_apply_one_eq_v hG pins s j hs).symm)

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Prime-`TI` `V`-value pin, `T`-side full-grid form** (mirror of `tauS_mu_vanish_on_V`):
on the regular set `(V_T)^T = conjClassSet(W ∖ (W₁ ∪ W₂))`, the `'A0(T)`-Dade lift
`τ_T(ν_{r,j} − ν_{s,j})` agrees with the grid difference `η_{r,j} − η_{s,j}` — both reduce to
the same `ω`-value (`ν_{l,j}|_V = δ'_l·ω = ω` by `nu_apply_of_not_mem_W1` +
`deltaPrime_eq_one_pins`; `η|_V = ω` by `eta_eq_tau_omega` + `tau3_apply_of_regular`). -/
theorem Hypothesis.tauT_nu_vanish_on_V [Fintype G] [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G)) (pins : NuGridSupplyData hyp)
    (hTP : OddOrder.BG.Ch4.S14.IsTypeP hyp.T)
    (Tdata : TypePData hyp.T) (hU : Tdata.U = hyp.V)
    (hW1 : Tdata.W1 = hyp.W2) (hW2 : Tdata.W2 = hyp.W1)
    (j : Fin hyp.p) {r s : Fin hyp.q}
    (hr : r ≠ ⟨0, hyp.q_prime.pos⟩) (hs : s ≠ ⟨0, hyp.q_prime.pos⟩) :
    ∀ x ∈ conjClassSet ((hyp.W : Set G) \ ((hyp.W1 : Set G) ∪ (hyp.W2 : Set G))),
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypT0 hG hTP Tdata)
          ((hyp.dadeHypT0 hG hTP Tdata).fullDadeIsometryData)
          (hyp.nu r j - hyp.nu s j)
        - (hyp.eta r j - hyp.eta s j)) x = 0 := by
  classical
  intro x hx
  obtain ⟨w, hw, g, hg⟩ := OddOrder.GroupTheory.mem_conjClassSet.mp hx
  have hwW : w ∈ hyp.W := hw.1
  have hw12 : w ∉ (hyp.W1 : Set G) ∪ (hyp.W2 : Set G) := hw.2
  have hw1 : w ∉ (hyp.W1 : Set G) := fun h => hw12 (Or.inl h)
  have hwT : w ∈ hyp.T := ((le_of_eq hyp.W_eq_inter).trans inf_le_right) hwW
  have hconjwx : IsConj w x := isConj_iff.mpr ⟨g, hg⟩
  have hwV : w ∈ OddOrder.GroupTheory.typePV hyp.T Tdata := by
    constructor
    · have hWeq : (Tdata.W : Set G) = (hyp.W : Set G) := by
        rw [Tdata.W_eq, hW1, hW2, sup_comm, ← hyp.W_eq_join]
      rw [hWeq]; exact hwW
    · rw [hW1, hW2, Set.union_comm]; exact hw12
  have hwA0 : w ∈ S10.typePACore0 hyp.T Tdata :=
    Or.inr (OddOrder.GroupTheory.subset_conjClassSetIn hwV)
  have hsupp := hyp.tauT_nu_diff_support hG pins Tdata hU hW1 hW2 j hr hs
  rw [OddOrder.RepresentationTheory.ClassFunction.sub_apply,
    OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_apply_of_support
      (hyp.dadeHypT0 hG hTP Tdata)
      ((hyp.dadeHypT0 hG hTP Tdata).fullDadeIsometryData)
      hsupp,
    (hyp.dadeHypT0 hG hTP Tdata).dadeMap_apply]
  have h1H : (1 : G) ∈ (hyp.dadeHypT0 hG hTP Tdata).H ⟨w, hwA0⟩ := by
    rw [hyp.forall_dadeHypT0_H_eq_bot hG hnoV hTP Tdata ⟨w, hwA0⟩]
    exact Subgroup.mem_bot.mpr rfl
  have hconj1 : IsConj ((⟨w, hwA0⟩ :
      {a : G // a ∈ S10.typePACore0 hyp.T Tdata}).1 * 1) x := by
    rw [mul_one]; exact hconjwx
  rw [(hyp.dadeHypT0 hG hTP Tdata).dadeValue_eq _ h1H hconj1]
  have hnu : ∀ (l : Fin hyp.q),
      hyp.nu l j ⟨w, (hyp.dadeHypT0 hG hTP Tdata).mem_L hwA0⟩ = hyp.omega l j ⟨w, hwW⟩ := by
    intro l
    rw [pins.nu_apply_of_not_mem_W1 l j w hwW
      ((hyp.dadeHypT0 hG hTP Tdata).mem_L hwA0) hw1, hyp.deltaPrime_eq_one_pins hG pins l]
    norm_num
  have heta : ∀ (l : Fin hyp.q), hyp.eta l j x = hyp.omega l j ⟨w, hwW⟩ := by
    intro l
    rw [(hyp.eta l j).of_isConj hconjwx.symm, hyp.eta_eq_tau_omega,
      hyp.tau3_apply_of_regular _ w hwW hw12]
  rw [OddOrder.RepresentationTheory.ClassFunction.sub_apply,
    OddOrder.RepresentationTheory.ClassFunction.sub_apply, hnu r, hnu s, heta r, heta s]
  ring

/-- **`dadeHypT.H a = ftSupportKernel T (A(T)) a`** (mirror of
`dadeHypS_H_eq_ftSupportKernel`). -/
theorem Hypothesis.dadeHypT_H_eq_ftSupportKernel [Fintype G] [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hTP : OddOrder.BG.Ch4.S14.IsTypeP hyp.T)
    (a : {a : G // a ∈ S10.typePACore hyp.T}) :
    (hyp.dadeHypT hG hTP).H a =
      OddOrder.Peterfalvi.S10.ftSupportKernel hyp.T (S10.typePACore hyp.T) a.1 :=
  (S10.dadeSupportHypothesisData_typePACore hG hyp.T_maximal hTP).some.H_eq_ftSupportKernel a

/-- **No `A(T)`-point escapes `T`** (mirror of `no_escaping_typePACore`, at the
(14.9)-parametric `hTP`). -/
theorem Hypothesis.no_escaping_typePACore_T [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G)) (hTP : OddOrder.BG.Ch4.S14.IsTypeP hyp.T) :
    ∀ a ∈ S10.typePACore hyp.T,
      a ∉ OddOrder.GroupTheory.escapingCentralizerSet hyp.T (S10.typePACore hyp.T) := by
  intro a _ ha
  rw [escaping_typePACore_eq_empty hG hnoV hyp.T_maximal hTP] at ha
  exact Set.notMem_empty a ha

/-- **(13.2.e)-at-`T`, stabilizer form: every `T`-instance Dade stabilizer is trivial**
(mirror of `forall_dadeHypS_H_eq_bot`). -/
theorem Hypothesis.forall_dadeHypT_H_eq_bot [Fintype G] [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G)) (hTP : OddOrder.BG.Ch4.S14.IsTypeP hyp.T) :
    ∀ a : {a : G // a ∈ S10.typePACore hyp.T}, (hyp.dadeHypT hG hTP).H a = ⊥ := by
  intro a
  rw [hyp.dadeHypT_H_eq_ftSupportKernel hG hTP a]
  exact OddOrder.Peterfalvi.S10.ftSupportKernel_eq_bot_of_not_escaping
    (hyp.no_escaping_typePACore_T hG hnoV hTP a.1 a.2)

open OddOrder.RepresentationTheory in
open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **`τ_T = Ind_T^G` on `A(T)`-supported functions** (mirror of `sInstance_dade_eq_induce`):
the `T`-instance `A(T)`-Dade isometry agrees with plain induction on every `A(T)`-supported
class function. -/
theorem Hypothesis.tInstance_dade_eq_induce [Fintype G] [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G)) (hTP : OddOrder.BG.Ch4.S14.IsTypeP hyp.T)
    {f : ClassFunction ↥hyp.T ℂ}
    (hf : f.support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (S10.typePACore hyp.T) hyp.T) :
    OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypT hG hTP)
        ((hyp.dadeHypT hG hTP).fullDadeIsometryData) f
      = ClassFunction.induce hyp.T f := by
  rw [OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_apply_of_support (hyp.dadeHypT hG hTP)
    ((hyp.dadeHypT hG hTP).fullDadeIsometryData) hf]
  exact OddOrder.Peterfalvi.S14.dadeMap_eq_induce_of_supported_on_trivial_H
    (hyp.dadeHypT hG hTP)
    (subset_refl _)
    (fun l _ ha => S10.typePACore_conj_mem l.2 ha)
    (fun a => by
      rw [OddOrder.Peterfalvi.S04.Hypothesis.restrict_H]
      exact hyp.forall_dadeHypT_H_eq_bot hG hnoV hTP ⟨a.1, a.2⟩)
    ⟨f, (ClassFunction.mem_supportedSubmodule).mpr hf⟩

open OddOrder.RepresentationTheory in
open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **`τ_T⁰ = Ind_T^G` on `A₀(T)`-supported functions** (mirror of
`sInstance_dade0_eq_induce`, from the `A₀(T)` normedTI `forall_dadeHypT0_H_eq_bot`). -/
theorem Hypothesis.tInstance_dade0_eq_induce [Fintype G] [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hyp : Hypothesis (G := G))
    (hTP : OddOrder.BG.Ch4.S14.IsTypeP hyp.T) (Tdata : TypePData hyp.T)
    {f : ClassFunction ↥hyp.T ℂ}
    (hf : f.support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (S10.typePACore0 hyp.T Tdata) hyp.T) :
    OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap (hyp.dadeHypT0 hG hTP Tdata)
        ((hyp.dadeHypT0 hG hTP Tdata).fullDadeIsometryData) f
      = ClassFunction.induce hyp.T f := by
  rw [OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_apply_of_support
    (hyp.dadeHypT0 hG hTP Tdata)
    ((hyp.dadeHypT0 hG hTP Tdata).fullDadeIsometryData) hf]
  exact OddOrder.Peterfalvi.S14.dadeMap_eq_induce_of_supported_on_trivial_H
    (hyp.dadeHypT0 hG hTP Tdata)
    (subset_refl _)
    (fun l _ ha => (S10.typePACore0_conj_mem Tdata l.2).mpr ha)
    (fun a => by
      rw [OddOrder.Peterfalvi.S04.Hypothesis.restrict_H]
      exact hyp.forall_dadeHypT0_H_eq_bot hG hnoV hTP Tdata ⟨a.1, a.2⟩)
    ⟨f, (ClassFunction.mem_supportedSubmodule).mpr hf⟩

end OddOrder.Peterfalvi.S15


