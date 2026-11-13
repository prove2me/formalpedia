-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S08_CaseBSeedSetup
-- name    : OddOrder_Peterfalvi_S08_CaseBSeedSetup
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T07:20:26.833084+00:00
-- url     : https://prove2.me/theorems/88602f69-d3e9-4649-b979-d597488349fc
-- title:
--   Peterfalvi §8: the case-(B) anchored seed, setup layer
-- statement:
--   The setup layer of the case-(B) anchored coherence seed in Peterfalvi (6.8.2.3).
--
--   Results: `exists_central_phi_data` (the per-column central-character data) and `compHom_phi_ne_trivial_of_restrict` (nontriviality of the central character from the master restriction equation).
--
--   The bundle also proves 2 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S08_CaseBSeedSetup.lean

/-
Copyright (c) 2026 The Odd Order Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S08_CaseBSeedSetup.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S08_CaseBAssembly
import Definitions.Def_OddOrder_Peterfalvi_S08_CaseBXChiCoherence
import Definitions.Def_OddOrder_Peterfalvi_S08_CaseBEnumeration

namespace OddOrder.Peterfalvi.S08

open OddOrder.RepresentationTheory

variable {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]

variable {L : Subgroup G} [Fintype ↥L] [Invertible (Nat.card ↥L : ℂ)]

variable {H : Subgroup ↥L} [Invertible (Nat.card ↥H : ℂ)]

omit [Invertible (Nat.card G : ℂ)] in
omit [Fintype ↥L] [Invertible (Nat.card ↥L : ℂ)] [Invertible (Nat.card ↥H : ℂ)] in
omit [Fintype G] in
/-- **(6.8.2.3) per-column central-character data** (the Q1 "central gap").

For any irreducible character `θ` of `H` and a central subgroup `W₂ ≤ Z(H)`, the central **linear**
character `φ_θ` of `θ` ([Is] Lemma 2.27 `exists_central_linear_restriction`,
`Res^H_{W₂} θ = θ(1)·φ_θ`), transported from `W₂.subgroupOf H` to the ambient `L`-subgroup `W₂` via
`subgroupOfEquivOfLe`, packages every datum the per-`φ` machinery needs:

* `hφ' : IsIrreducibleCharacter (compHom e φ)` — irreducibility on `W₂.subgroupOf H`, the form
  consumed by `caseB_per_phi_anchored_fromYset` / `caseB_hcol` / `caseB_hirr`;
* `IsIrreducibleCharacter φ` (on the `L`-subgroup `W₂`, via `compHom_of_surjective`) and `φ 1 = 1`
  (linearity) — the form consumed by the `(6.8.2.2)` aggregate `exists_decomposition_caseB`
  (`φ : IrreducibleCharacter ↥W₂`, `φ(1) = 1`);
* `0 < constituentWeight hφ' θ` — positivity (`= θ(1)`), so `θ` is a positive-weight constituent of
  `φ_θ`;
* `Res^H_{W₂} θ = θ(1)·(compHom e φ_θ)` — the master central-restriction equation ([Is] 2.27), from
  which nontriviality (`φ_θ ≠ 1 ⟺ W₂ ⊄ ker θ`) is downstream-derivable.

This resolves the fixed-`φ` mismatch of the naive reading: the certain-type columns each lie over
their **own** central `φ_θ` (read off from `θ` via the central restriction), not over a single
shared `φ`.  Positivity is immediate from `⟨φ_θ, Res θ⟩ = θ(1)·⟨φ_θ,φ_θ⟩ = θ(1) ≠ 0`. -/
theorem exists_central_phi_data
    {W2 : Subgroup ↥L} (hW2H : W2 ≤ H) [Fintype ↥(W2.subgroupOf H)]
    [Invertible (Nat.card ↥(W2.subgroupOf H) : ℂ)] [Finite ↥H]
    (hcen : W2.subgroupOf H ≤ Subgroup.center ↥H)
    (θ : IrreducibleCharacter ↥H) :
    ∃ (φ : ClassFunction ↥W2 ℂ)
      (hφ' : IsIrreducibleCharacter
        (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hW2H).toMonoidHom φ)),
      IsIrreducibleCharacter φ ∧ φ 1 = 1 ∧ 0 < constituentWeight hφ' θ ∧
      ClassFunction.restrict (W2.subgroupOf H) (θ : ClassFunction ↥H ℂ)
        = (θ : ClassFunction ↥H ℂ) 1 •
          ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hW2H).toMonoidHom φ := by
  have : Fintype ↥H := Fintype.ofFinite _
  obtain ⟨φN, hφNirr, hφN1, hres, _⟩ :=
    θ.2.exists_central_linear_restriction (W2.subgroupOf H) hcen
  set e := Subgroup.subgroupOfEquivOfLe hW2H with he
  have htrans : ClassFunction.compHom e.toMonoidHom
      (ClassFunction.compHom e.symm.toMonoidHom φN) = φN := by
    ext x
    simp only [ClassFunction.compHom_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
  refine ⟨ClassFunction.compHom e.symm.toMonoidHom φN, by rw [htrans]; exact hφNirr,
    IsIrreducibleCharacter.compHom_of_surjective e.symm.surjective hφNirr, ?_, ?_, ?_⟩
  · rw [ClassFunction.compHom_apply, map_one]; exact hφN1
  · rw [constituentWeight_pos_iff, htrans, hres, OddOrder.RepresentationTheory.inner_smul_right]
    obtain ⟨d, hdpos, hd⟩ := irreducibleCharacter_apply_one_eq_pos_natCast θ
    have hself : ClassFunction.inner φN φN = 1 := by
      have h := irreducibleCharacter_inner_eq_ite
        (⟨φN, hφNirr⟩ : IrreducibleCharacter ↥(W2.subgroupOf H))
        (⟨φN, hφNirr⟩ : IrreducibleCharacter ↥(W2.subgroupOf H))
      rwa [if_pos rfl] at h
    rw [hself, mul_one, star_ne_zero, hd]
    exact_mod_cast hdpos.ne'
  · rw [htrans]; exact hres

omit [Fintype G] in
omit [Invertible (Nat.card G : ℂ)] [Fintype ↥L] [Invertible (Nat.card ↥L : ℂ)]
  [Invertible (Nat.card ↥H : ℂ)] in
/-- **Central character nontriviality** from the master restriction equation.  If
`Res^H_N θ = θ(1)·χ` (the [Is] 2.27 form, `χ = compHom e φ_θ`) and `θ` is **not** constant on `N`
(some `w ∈ N` with `θ(w) ≠ θ(1)`, i.e. `N ⊄ ker θ`), then the central character `χ` is nontrivial.
Indeed `χ = trivial` would force `θ(w) = θ(1)·1 = θ(1)` for every `w ∈ N`. -/
theorem compHom_phi_ne_trivial_of_restrict
    {N : Subgroup ↥H} {θ : ClassFunction ↥H ℂ} {χ : ClassFunction ↥N ℂ}
    (hres : ClassFunction.restrict N θ = θ 1 • χ)
    (hne : ∃ w : ↥N, θ (w : ↥H) ≠ θ 1) :
    χ ≠ trivialClassFunction ↥N := by
  obtain ⟨w, hw⟩ := hne
  intro htriv
  apply hw
  have hval := congrFun (congrArg (fun f : ClassFunction ↥N ℂ => (f : ↥N → ℂ)) hres) w
  rw [htriv] at hval
  simpa [ClassFunction.restrict_apply, ClassFunction.smul_apply, trivialClassFunction_apply,
    smul_eq_mul] using hval

/-- **(6.8.2.2) aggregate against an arbitrary `Y`-coherence `cY`** — the `hYcard`-free,
uniform-`cY` form of `exists_decomposition_caseB_coherentYset`.  Given the good anchor multiplicity
`hgood : ⟨(Ind^L_{W₂}φ − |H:W₂|·η₁)^τ, cY.extension η₁⟩ = −|H:W₂|` (supplied uniformly across all
`φ`
by `SibleyDadeHypothesis.exists_Ycoherence_hgood_uniform_caseB`, folding in the `m = 2` relabel),
produces the anchored decomposition against `cY` with `X ⊥ cY.extension(𝒴)` and `X ∈ ZIrr`.
Replaces
the `coeff_eq_neg_or_edge_caseB` + `hYcard` derivation by the `hgood` hypothesis; the rest of the
proof (`orthogonal_tau_indW2_add_extension_general_caseB`, already `cY`-generic) is unchanged.  This
is the bottom of the `hYcard`-free case-(B) `X ∪ Y`-coherence chain. -/
theorem exists_decomposition_caseB_anchorCY
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    {W2 : Subgroup ↥L} [W2.Normal] [Invertible (Nat.card ↥W2 : ℂ)]
    (hW2comm : W2 ≤ ⁅H, H⁆)
    (cY : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Yset
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    (φ : IrreducibleCharacter ↥W2) (hφ1 : (φ : ClassFunction ↥W2 ℂ) 1 = 1)
    (hgood : ClassFunction.inner (hyp.tau (ClassFunction.induce W2 (φ : ClassFunction ↥W2 ℂ)
        - ((W2.subgroupOf H).index : ℂ) • η₁)) (cY.extension η₁)
        = -((W2.subgroupOf H).index : ℂ)) :
    ∃ X : ClassFunction G ℂ,
      (∀ η ∈ hyp.Yset, ClassFunction.inner X (cY.extension η) = 0)
        ∧ X ∈ ZIrr G
        ∧ hyp.tau (ClassFunction.induce W2 (φ : ClassFunction ↥W2 ℂ)
            - ((W2.subgroupOf H).index : ℂ) • η₁)
          = X - ((W2.subgroupOf H).index : ℂ) • cY.extension η₁ := by
  have : Fintype ↥W2 := Fintype.ofFinite _
  have hW2H : W2 ≤ H := by
    have hle : ⁅H, H⁆ ≤ H := by
      rw [Subgroup.commutator_le]; intro a ha b hb; rw [commutatorElement_def]
      exact H.mul_mem (H.mul_mem (H.mul_mem ha hb) (H.inv_mem ha)) (H.inv_mem hb)
    exact hW2comm.trans hle
  have h1 : ClassFunction.induce W2 (φ : ClassFunction ↥W2 ℂ) 1
      = ((W2.subgroupOf H).index : ℂ) * η₁ 1 := by
    rw [ClassFunction.induce_apply_one, hφ1, mul_one, hyp.Yset_apply_one hη₁]
    have hidx : W2.index = (W2.subgroupOf H).index * H.index :=
      (Subgroup.relIndex_mul_index hW2H).symm
    rw [hidx, hyp.index_H_eq_card_W1]; push_cast; ring
  obtain ⟨horth, hXZ⟩ :=
    hyp.orthogonal_tau_indW2_add_extension_general_caseB hW2H hW2comm cY hη₁ φ hφ1 h1 hgood
  refine ⟨hyp.tau (ClassFunction.induce W2 (φ : ClassFunction ↥W2 ℂ)
      - ((W2.subgroupOf H).index : ℂ) • η₁)
      + ((W2.subgroupOf H).index : ℂ) • cY.extension η₁, horth, hXZ, ?_⟩
  abel

/-- **(6.8.2.3) per-member anchored image — general `χ = Ind^L_H θ ∈ X`.**  Generalizes
`caseB_column_anchored_image` from a certain-type column to an **arbitrary** irreducible `θ` of `H`
that is nonconstant on `W₂` (`hθne`, i.e. `W₂ ⊄ ker θ`, equivalently `Ind^L_H θ ∈ X = S − S(W₂)`),
and additionally exposes the **seam orthogonality** `⟨X, η₁^{τ₁}⟩ = 0`
(`caseB_constituentDecomposition_X_orthogonal`).

Returns the Peterfalvi (6.8.2.3) anchored image
`τ(Ind^L_H θ − a·η₁) = X − a·η₁^{τ₁}` (`a = θ(1)`) together with `X ⊥ η₁^{τ₁}`.  Since under central
`W₂` every `χ = Ind^L_H θ ∈ X` (reducible certain-type column **or** irreducible) arises as a
positive-weight constituent of the central `φ_θ`-induction (`exists_central_phi_data`), this single
lemma is the uniform (6.8.2.3) `hXanchored` + `hXmixed` content for the **whole** of `X` — the basis
of the case-(B) `X ∪ Y` coherence seed (`coherentXunionYset_caseB_of_glued`).

The proof mirrors `caseB_column_anchored_image` (central char + (6.8.2.2) aggregate + bundles +
per-`φ` producer) with `θ` taken directly instead of `Res^H μ_{0,χ₂}`, plus the `X ⊥ Y^{τ₁}` call
with the textbook partner `η' = η̄₁` reconstructed from `η₁ ∈ Y`. -/
theorem caseB_member_anchored_image
    (hyp : SibleyDadeHypothesis G L H) [H.Normal] [Finite ↥H]
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L) (hHK : h46.K = H)
    (hW1 : h46.W1 = hyp.W1)
    [NeZero (Nat.card h46.W1)] [Invertible (Nat.card ↥h46.K : ℂ)]
    [Finite ↥(h46.W1 ⊔ h46.W2)] [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    [Finite (OddOrder.Peterfalvi.S06.ticVdiff h46).W]
    [Invertible (Nat.card (OddOrder.Peterfalvi.S06.ticVdiff h46).W : ℂ)]
    [h46.W2.Normal] [Invertible (Nat.card ↥h46.W2 : ℂ)]
    [Finite ↥(h46.W2.subgroupOf H)] [Invertible (Nat.card ↥(h46.W2.subgroupOf H) : ℂ)]
    (hW2H : h46.W2 ≤ H)
    (hcen : h46.W2.subgroupOf H ≤ Subgroup.center ↥H)
    (hderiv : h46.W2.subgroupOf H ≤ commutator ↥H)
    (_hcop : Nat.Coprime (Nat.card ↥H) (Nat.card hyp.W1))
    {p : ℕ} (_hp : p.Prime) (_hHp : IsPGroup p ↥H)
    (_hprime : (Nat.card h46.W2).Prime) (hW2comm : h46.W2 ≤ ⁅H, H⁆)
    (_hW2cenL : h46.W2 ≤ Subgroup.center ↥L)
    (_hc2 : 2 ≤ (h46.W2.subgroupOf H).index)
    (_hFPF : (h46.W2.index : ℤ) < ((h46.W2.subgroupOf H).index : ℤ) ^ 2)
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    (θ : IrreducibleCharacter ↥H)
    (hθne : ∃ w : ↥(h46.W2.subgroupOf H),
      (θ : ClassFunction ↥H ℂ) (w : ↥H) ≠ (θ : ClassFunction ↥H ℂ) 1)
    (cY : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Yset
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    (hcYgood : ∀ φ : IrreducibleCharacter ↥h46.W2, (φ : ClassFunction ↥h46.W2 ℂ) 1 = 1 →
      φ ≠ trivialIrreducibleCharacter ↥h46.W2 →
      ClassFunction.inner (hyp.tau (ClassFunction.induce h46.W2 (φ : ClassFunction ↥h46.W2 ℂ)
          - ((h46.W2.subgroupOf H).index : ℂ) • η₁)) (cY.extension η₁)
          = -((h46.W2.subgroupOf H).index : ℂ)) :
    ∃ (X : ClassFunction G ℂ) (a : ℕ),
      ((ClassFunction.induce H (θ : ClassFunction ↥H ℂ) : ClassFunction ↥L ℂ) 1 = (a : ℂ) * η₁ 1) ∧
      hyp.tau (ClassFunction.induce H (θ : ClassFunction ↥H ℂ) - a • η₁)
        = X - (a : ℂ) • cY.extension η₁ ∧
      ClassFunction.inner X (cY.extension η₁) = 0 ∧
      X ∈ ZIrr G := by
  classical
  have : Fintype ↥H := Fintype.ofFinite _
  have : Fintype ↥(h46.W1 ⊔ h46.W2) := Fintype.ofFinite _
  have : Fintype (OddOrder.Peterfalvi.S06.ticVdiff h46).W := Fintype.ofFinite _
  have : Fintype ↥(h46.W2.subgroupOf H) := Fintype.ofFinite _
  have : Fintype ↥h46.W2 := Fintype.ofFinite _
  obtain ⟨φ, hφ', hφirr, hφ1, hweight, hreseq⟩ := exists_central_phi_data hW2H hcen θ
  have hφne : ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hW2H).toMonoidHom φ
      ≠ trivialClassFunction ↥(h46.W2.subgroupOf H) :=
    compHom_phi_ne_trivial_of_restrict hreseq hθne
  have hφneIrr : (⟨φ, hφirr⟩ : IrreducibleCharacter ↥h46.W2)
      ≠ trivialIrreducibleCharacter ↥h46.W2 := by
    intro heq
    apply hφne
    have hφtriv : φ = trivialClassFunction ↥h46.W2 := by
      have h := congrArg (fun c : IrreducibleCharacter ↥h46.W2 => (c : ClassFunction ↥h46.W2 ℂ)) heq
      simpa using h
    rw [hφtriv]; ext x
    simp [ClassFunction.compHom_apply, trivialClassFunction_apply]
  obtain ⟨Xagg, hXaggorth, hXZ, hdecomp⟩ :=
    exists_decomposition_caseB_anchorCY hyp hW2comm cY hη₁
      (⟨φ, hφirr⟩ : IrreducibleCharacter ↥h46.W2) hφ1
      (hcYgood (⟨φ, hφirr⟩ : IrreducibleCharacter ↥h46.W2) hφ1 hφneIrr)
  simp only [IrreducibleCharacter.coe_mk] at hdecomp
  have hnonlin := caseB_hnonlin hW2H hderiv hφ' hφne
  have hcol := caseB_hcol hyp h46 hHK hW1 hW2H hcen hφ' hη₁
  have hirr := caseB_hirr hyp h46 hHK hW2H hcen hφ' hη₁ hnonlin
  have hirrAnc := caseB_hirrAnc hyp h46 hHK hW2H hφ' hη₁ hnonlin
  have hanc := caseB_per_phi_anchored_fromYset hyp h46 hHK hW2H hcen hφ' cY hη₁
    hcol hirr hirrAnc (hXaggorth η₁ hη₁) hdecomp ⟨θ, hweight⟩
  -- seam orthogonality `⟨X, η₁^{τ₁}⟩ = 0`, textbook partner `η' = η̄₁` reconstructed from `η₁ ∈ Y`.
  have hη₁irr : IsIrreducibleCharacter η₁ := hyp.isIrreducibleCharacter_of_mem_Yset hη₁
  have hconj : η₁.conj ∈ hyp.Yset := hyp.Yset_closedUnderConjugate hη₁
  have hrealc1 : ¬ ClassFunction.IsReal η₁ :=
    fun hreal => hyp.Yset_hasNoRealCharacters.not_mem_of_isReal hreal hη₁
  have hne : η₁ ≠ η₁.conj := fun heq => hrealc1 heq.symm
  have hee : ClassFunction.inner η₁ η₁.conj = 0 := by
    have h := irreducibleCharacter_inner_eq_ite (⟨η₁, hη₁irr⟩ : IrreducibleCharacter ↥L)
      (⟨η₁.conj, hη₁irr.conj⟩ : IrreducibleCharacter ↥L)
    rw [if_neg (fun heq => hne (Subtype.ext_iff.mp heq))] at h
    simpa using h
  have hval : η₁ (1 : ↥L) = η₁.conj (1 : ↥L) :=
    (hyp.Yset_apply_one hη₁).trans (hyp.Yset_apply_one hconj).symm
  have hsupp : (η₁ - η₁.conj).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
    hyp.sMember_diffSupport_of_charValue_eq (hyp.Yset_subset_S hη₁) (hyp.Yset_subset_S hconj) hval
  have hdiffsuppc1 : (η₁.conj - η₁).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
    hyp.sMember_diffSupport_of_charValue_eq (hyp.Yset_subset_S hconj) (hyp.Yset_subset_S hη₁)
      hval.symm
  have hXorth := caseB_constituentDecomposition_X_orthogonal hyp h46 hHK θ
    (hcol ⟨θ, hweight⟩) (hirr ⟨θ, hweight⟩) cY hη₁ hη₁irr hrealc1 hdiffsuppc1 hconj
    (cY.extension_mem_ZIrr η₁ (Submodule.subset_span hη₁)) hee hconj hη₁irr.conj hee
    hsupp (hirrAnc ⟨θ, hweight⟩)
  refine ⟨(caseB_phi_family hyp h46 hW2H hφ' hcol hirr ⟨θ, hweight⟩).X,
    constituentWeight hφ' θ, ?_, hanc, hXorth,
    characterPsiDecomposition_X_mem_ZIrr _⟩
  rw [ClassFunction.induce_apply_one, hyp.index_H_eq_card_W1, hyp.Yset_apply_one hη₁,
    constituentWeight_eq_apply_one hW2H hcen hφ' hweight]
  ring

end OddOrder.Peterfalvi.S08


