-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S08_YsetConjugation_InducedFamilies
-- name    : OddOrder_Peterfalvi_S08_YsetConjugation_InducedFamilies
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T06:19:00.404948+00:00
-- url     : https://prove2.me/theorems/ca9ab160-cf7b-4ae1-9340-0de4ee26a9bc
-- title:
--   Peterfalvi §8: induced degree-one families
-- statement:
--   Inertia, induced irreducibility and coherent degree-one families for the Peterfalvi §8 development.
--
--   Main definitions: `tau` (the coherence map of the (6.8) setup, realized as the genuine §4 Dade isometry), `CoherenceTarget` (the (6.8) target: $S$ is coherent for the real Dade map), `coherentInducedDegreeOneFamily` (equal-degree induced irreducible families from degree-one source characters), `coherentYFamily` (the (6.8) coherence of $Y=S(H')$ from a constructed family) and `coherentYFamily_of_pairwiseNonconj` (the same, with induced irreducibility discharged internally).
--
--   The bundle also proves 8 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S08_YsetConjugation/InducedFamilies.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S08_YsetConjugation/InducedFamilies.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S08_CoherenceCorePart1
import Definitions.Def_OddOrder_GroupTheory_TISubset
import Definitions.Def_OddOrder_GroupTheory_ConjClassSet
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_InducedCharacter
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Index
import Mathlib.Algebra.BigOperators.GroupWithZero.Action

namespace OddOrder.Peterfalvi.S08

open OddOrder.RepresentationTheory

open scoped commutatorElement

variable {L G : Type*} [Group L] [Group G]

namespace SibleyDadeHypothesis

variable {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]

variable {L : Subgroup G} [Fintype ↥L] [Invertible (Nat.card L : ℂ)]

variable {H : Subgroup ↥L} [Invertible (Nat.card ↥H : ℂ)]

/-- The coherence map `τ` of the (6.8) setup, realized as the genuine §4 Dade isometry
(`dadeIntegralCharacterMap`) — **not** an opaque global isometry. -/
noncomputable abbrev tau (hyp : SibleyDadeHypothesis G L H) :
    OddOrder.Peterfalvi.S07.IntegralCharacterMap (↥L) G :=
  OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp.dade
    (hyp.dade.fullDadeIsometryData)

/-- The (6.8) coherence target: `S` is coherent for the **real Dade map** `tau`.  This is exactly
the conclusion shape produced by the §7 engine, hence honestly dischargeable — unlike the legacy
`SibleySetup.CoherenceTarget`, which required a nonexistent global isometry. -/
abbrev CoherenceTarget (hyp : SibleyDadeHypothesis G L H) :=
  OddOrder.Peterfalvi.S07.IsCoherent (L := ↥L) (G := G) hyp.tau hyp.S
    (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)

/-- **(6.8.1) Dade reciprocity for the Sibley carrier.**  Since `H^#` is TI (`dade_H_eq_bot`), the
real Dade map `tau` satisfies `⟨α^τ, ψ⟩_G = ⟨α, Res_L^G ψ⟩_L` for supported `α ∈ CF(L, H^#)` and any
`ψ ∈ CF(G)` (`inner_dadeIntegralCharacterMap_eq_inner_restrict`).  This is the move the (6.8.1)
proof (mmd L176) uses to rewrite `⟨η₁^{τ₁}, (χᵢ − dᵢχ₁)^τ⟩ = ⟨Res_L(η₁^{τ₁}), χᵢ − dᵢχ₁⟩`, feeding
the `Res_L(η₁^{τ₁}) = c∑dᵢχᵢ + χ′` decomposition. -/
theorem inner_tau_eq_inner_restrict (hyp : SibleyDadeHypothesis G L H)
    {α : ClassFunction ↥L ℂ}
    (hαsupp : α.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)
    (ψ : ClassFunction G ℂ) :
    ClassFunction.inner (hyp.tau α) ψ = ClassFunction.inner α (ClassFunction.restrict L ψ) :=
  inner_dadeIntegralCharacterMap_eq_inner_restrict hyp.dade hyp.dade_H_eq_bot hαsupp ψ

/-- (6.8)(a) consequence: `[L : H] = |W₁|`.  From the complement `L = H ⋊ W₁` (`hyp.split`).
This is the common degree of the members of `Y = S(H')`: by [Is] Thm 6.34
(`isIrreducibleCharacter_induce_of_inertia_eq`), `(Ind_H^L θ)(1) = [L:H]·θ(1) = |W₁|` for the
degree-`1` characters `θ ∈ Irr(H/H')`. -/
theorem index_H_eq_card_W1 (hyp : SibleyDadeHypothesis G L H) :
    H.index = Nat.card hyp.W1 :=
  (Subgroup.IsComplement.card_right (Subgroup.isComplement'_def.mp hyp.split)).symm

/-- Degree-one source characters induce to class functions of degree |W1| in the (6.8)
setup. This is the degree side of the Y = S(Hprime) family used in the final coherence assembly. -/
theorem induce_apply_one_eq_card_W1_of_degree_one
    (hyp : SibleyDadeHypothesis G L H) (θ : IrreducibleCharacter ↥H)
    (hθ_one : (θ : ClassFunction ↥H ℂ) (1 : ↥H) = 1) :
    OddOrder.RepresentationTheory.ClassFunction.induce H (θ : ClassFunction ↥H ℂ) (1 : ↥L) =
      (Nat.card hyp.W1 : ℂ) := by
  rw [OddOrder.RepresentationTheory.ClassFunction.induce_apply_one, hθ_one, mul_one,
    hyp.index_H_eq_card_W1]

/-- If two source class functions induce to the same value at 1, their induced difference is
supported on H-sharp in the (6.8) Dade support. -/
theorem support_sub_induce_subset_sharpImage_of_apply_one_eq
    (hyp : SibleyDadeHypothesis G L H) (θ ψ : ClassFunction ↥H ℂ)
    (hone : OddOrder.RepresentationTheory.ClassFunction.induce H θ (1 : ↥L) =
      OddOrder.RepresentationTheory.ClassFunction.induce H ψ (1 : ↥L)) :
    (OddOrder.RepresentationTheory.ClassFunction.induce H θ -
        OddOrder.RepresentationTheory.ClassFunction.induce H ψ).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L := by
  let : H.Normal := hyp.H_normal
  intro x hx
  have hθsupp :
      (OddOrder.RepresentationTheory.ClassFunction.induce H θ).support ⊆ H :=
    OddOrder.RepresentationTheory.ClassFunction.support_induce_subset_of_normal
      (G := ↥L) (k := ℂ) H θ
  have hψsupp :
      (OddOrder.RepresentationTheory.ClassFunction.induce H ψ).support ⊆ H :=
    OddOrder.RepresentationTheory.ClassFunction.support_induce_subset_of_normal
      (G := ↥L) (k := ℂ) H ψ
  have hxH : x ∈ H := by
    rcases OddOrder.RepresentationTheory.ClassFunction.support_sub_subset
        (OddOrder.RepresentationTheory.ClassFunction.induce H θ)
        (OddOrder.RepresentationTheory.ClassFunction.induce H ψ) hx with hxθ | hxψ
    · exact hθsupp hxθ
    · exact hψsupp hxψ
  have hxne : x ≠ 1 := by
    intro hx1
    apply hx
    rw [hx1, OddOrder.RepresentationTheory.ClassFunction.sub_apply, hone, sub_self]
  change (x : G) ∈ sharpImage H
  refine ⟨?_, ?_⟩
  · exact Subgroup.mem_map.mpr ⟨x, hxH, rfl⟩
  · intro hx1G
    exact hxne (Subtype.ext hx1G)

/-- Degree-one source characters give induced differences supported on H-sharp. -/
theorem support_sub_induce_subset_sharpImage_of_degree_one
    (hyp : SibleyDadeHypothesis G L H) (θ ψ : IrreducibleCharacter ↥H)
    (hθ_one : (θ : ClassFunction ↥H ℂ) (1 : ↥H) = 1)
    (hψ_one : (ψ : ClassFunction ↥H ℂ) (1 : ↥H) = 1) :
    (OddOrder.RepresentationTheory.ClassFunction.induce H (θ : ClassFunction ↥H ℂ) -
        OddOrder.RepresentationTheory.ClassFunction.induce H (ψ : ClassFunction ↥H ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
  hyp.support_sub_induce_subset_sharpImage_of_apply_one_eq
    (θ : ClassFunction ↥H ℂ) (ψ : ClassFunction ↥H ℂ) (by
      rw [hyp.induce_apply_one_eq_card_W1_of_degree_one θ hθ_one,
        hyp.induce_apply_one_eq_card_W1_of_degree_one ψ hψ_one])

/-- Equal-degree induced irreducible families from degree-one source characters are coherent for
Sibley's Dade map. This is the engine-call form of the (6.8) Y = S(Hprime) step: once the
eta-family of irreducible induced characters is constructed and shown injective, the remaining
(1.1)+(1.4) equal-degree coherence hypotheses are discharged by the Sibley carrier. -/
noncomputable def coherentInducedDegreeOneFamily
    (hyp : SibleyDadeHypothesis G L H) {n : ℕ} [NeZero n] (hn : 2 ≤ n)
    (θ : Fin n → IrreducibleCharacter ↥H) (η : Fin n → IrreducibleCharacter ↥L)
    (hη_ind : ∀ j,
      (η j : ClassFunction ↥L ℂ) =
        OddOrder.RepresentationTheory.ClassFunction.induce H (θ j : ClassFunction ↥H ℂ))
    (hηinj : Function.Injective η)
    (hθ_one : ∀ j, (θ j : ClassFunction ↥H ℂ) (1 : ↥H) = 1) :
    OddOrder.Peterfalvi.S07.IsCoherent (L := ↥L) (G := G) hyp.tau
      (Set.range (fun j => (η j : ClassFunction ↥L ℂ)))
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) := by
  classical
  have hdeg : ∀ j, ((η j : ClassFunction ↥L ℂ) : ↥L → ℂ) 1 =
      ((η 0 : ClassFunction ↥L ℂ) : ↥L → ℂ) 1 := by
    intro j
    rw [hη_ind j, hη_ind 0,
      hyp.induce_apply_one_eq_card_W1_of_degree_one (θ j) (hθ_one j),
      hyp.induce_apply_one_eq_card_W1_of_degree_one (θ 0) (hθ_one 0)]
  have hsuppdiff : ∀ j,
      (OddOrder.RepresentationTheory.irreducibleCharacterDifference η j).support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L := by
    intro j
    simpa [OddOrder.RepresentationTheory.irreducibleCharacterDifference, hη_ind j, hη_ind 0] using
      hyp.support_sub_induce_subset_sharpImage_of_degree_one (θ j) (θ 0)
        (hθ_one j) (hθ_one 0)
  have h1notA : (1 : G) ∉ sharpImage H := by
    intro h
    exact h.2 rfl
  exact OddOrder.Peterfalvi.S07.coherentEqualDegree_fromDade hyp.dade hn η hηinj
    hdeg hsuppdiff h1notA

/-- **(6.8)(c2) inertia equality** for a nontrivial linear `θ`.

Under the (4.6)/(c2) data — `H ⋊ W₁`, `C_H(w) = W₂ ⊆ ⁅H,H⁆` for `w ∈ W₁∖1`, and the Hall
coprimality `gcd(|H|,|W₁|) = 1` — the inertia group of a nontrivial degree-one `θ` is exactly `H`.

Proof.  Pass to `Ḡ = L/⁅H,H⁆`, `H̄ = H/⁅H,H⁆` (abelian).  `θ` is linear, so inflates from a
nontrivial `θ̄ ∈ Irr H̄`.  The coprimality + Isaacs (3.28) lift gives `C_{H̄}(w̄) = 1` for
`w̄ ∈ W̄₁∖1`; since `H̄` is abelian, Brauer's permutation lemma turns this into "`w̄` fixes only the
trivial irreducible", so `w̄ ∉ I_{Ḡ}(θ̄)`.  The inertia-transfer bridge then gives `w ∉ I_L(θ)` for
`w ∈ W₁∖1`, and the complement `L = H ⋊ W₁` reduces a general `g ∉ H` to this case (`I_L(θ) ⊇ H`, so
the `H`-part is absorbed). -/
theorem inertia_eq_H_of_c2 (hyp : SibleyDadeHypothesis G L H)
    (cert : OddOrder.Peterfalvi.S06.CertainTypeHypothesis (sharpImage H) L)
    (hK : cert.K = H) (hW1 : cert.W1 = hyp.W1) (hW2 : cert.W2 ≤ ⁅H, H⁆)
    (hcop : Nat.Coprime (Nat.card ↥H) (Nat.card hyp.W1))
    {θ : IrreducibleCharacter ↥H}
    (hθ_one : (θ : ClassFunction ↥H ℂ) (1 : ↥H) = 1)
    (hθ_ne : θ ≠ trivialIrreducibleCharacter ↥H) :
    letI : H.Normal := hyp.H_normal
    ClassFunction.inertia (θ : ClassFunction ↥H ℂ) = H := by
  classical
  let : H.Normal := hyp.H_normal
  have : Fintype ↥H := Fintype.ofFinite _
  have : Finite ↥L := Fintype.finite (Fintype.ofFinite _)
  -- The quotient `Ḡ = L/⁅H,H⁆` and the image `H̄ = H/⁅H,H⁆`.
  set M : Subgroup ↥L := ⁅H, H⁆ with hM_def
  have hMnormal : M.Normal := by rw [hM_def]; infer_instance
  set mkM : ↥L →* (↥L ⧸ M) := QuotientGroup.mk' M with hmkM_def
  set Hbar : Subgroup (↥L ⧸ M) := H.map mkM with hHbar_def
  have hHbar_normal : Hbar.Normal := by rw [hHbar_def, hmkM_def]; infer_instance
  -- `H̄` is abelian: images of `H` commute since their commutators land in `⁅H,H⁆ = ker mkM`.
  have hHbar_comm : ∀ a b : ↥Hbar, Commute a b := by
    rintro ⟨a, ha⟩ ⟨b, hb⟩
    rw [hHbar_def, Subgroup.mem_map] at ha hb
    obtain ⟨x, hxH, rfl⟩ := ha
    obtain ⟨y, hyH, rfl⟩ := hb
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul]
    -- `mkM x` and `mkM y` commute because `⁅x,y⁆ ∈ ⁅H,H⁆ = ker mkM`.
    have hcomm_elt : ⁅(x : ↥L), (y : ↥L)⁆ ∈ M := by
      rw [hM_def]; exact Subgroup.commutator_mem_commutator hxH hyH
    have hmk_one : mkM ⁅(x : ↥L), (y : ↥L)⁆ = 1 := (QuotientGroup.eq_one_iff _).mpr hcomm_elt
    rw [map_commutatorElement] at hmk_one
    exact commutatorElement_eq_one_iff_mul_comm.mp hmk_one
  -- The corestriction `q : ↥H →* ↥H̄` with `(q x : Ḡ) = mkM x`.
  set q : ↥H →* ↥Hbar :=
    (mkM.comp H.subtype).codRestrict Hbar (fun x => by
      rw [hHbar_def]; exact Subgroup.mem_map.mpr ⟨x, x.property, rfl⟩) with hq_def
  have hq : ∀ x : ↥H, ((q x : ↥Hbar) : ↥L ⧸ M) = mkM (x : ↥L) := fun x => rfl
  have hq_surj : Function.Surjective q := by
    rintro ⟨z, hz⟩
    rw [hHbar_def, Subgroup.mem_map] at hz
    obtain ⟨x, hxH, hxz⟩ := hz
    exact ⟨⟨x, hxH⟩, Subtype.ext hxz⟩
  have hqinj : Function.Injective
      (ClassFunction.compHom q : ClassFunction ↥Hbar ℂ → ClassFunction ↥H ℂ) :=
    ClassFunction.compHom_injective_of_surjective hq_surj
  -- `θ` is linear, hence kills `⁅H,H⁆.subgroupOf H = commutator ↥H`, so inflates from `H̄`.
  set N : Subgroup ↥H := M.subgroupOf H with hN_def
  have hN_normal : N.Normal := by rw [hN_def, hM_def]; exact hMnormal.subgroupOf H
  have hN_eq : N = _root_.commutator ↥H := by
    rw [hN_def, hM_def, ← Subgroup.map_subtype_commutator H, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective H.subtype_injective]
  have hker : (N : Set ↥H) ⊆ OddOrder.Peterfalvi.S03.characterKernel (θ : ClassFunction ↥H ℂ) := by
    intro n hn
    rw [OddOrder.Peterfalvi.S03.mem_characterKernel,
      OddOrder.Peterfalvi.S03.characterDegree_def, hθ_one]
    -- `θ` is multiplicative with `θ(1)=1`, so `{x | θ x = 1}` is a subgroup containing commutators.
    have hθ1 : (θ : ClassFunction ↥H ℂ) (1 : ↥H) = 1 := hθ_one
    have hn' : n ∈ Subgroup.closure (commutatorSet ↥H) := by
      have : n ∈ N := hn
      rwa [hN_eq, _root_.commutator_eq_closure] at this
    refine Subgroup.closure_induction
      (p := fun g _ => (θ : ClassFunction ↥H ℂ) g = 1) ?_ ?_ ?_ ?_ hn'
    · rintro _ ⟨a, b, rfl⟩
      exact θ.isIrreducible.apply_commutatorElement_eq_one_of_apply_one_eq_one hθ1 a b
    · exact hθ1
    · intro a b _ _ ha hb
      rw [θ.isIrreducible.map_mul_of_apply_one_eq_one hθ1, ha, hb, one_mul]
    · intro a _ ha
      have hai := θ.isIrreducible.map_mul_of_apply_one_eq_one hθ1 a a⁻¹
      rw [mul_inv_cancel, hθ1, ha, one_mul] at hai
      exact hai.symm
  have hkerq : q.ker = N := by
    ext x
    rw [MonoidHom.mem_ker]
    change q x = 1 ↔ (x : ↥L) ∈ M
    constructor
    · intro hx
      have hx1 : mkM (x : ↥L) = 1 := by rw [← hq x, hx]; rfl
      rw [hmkM_def] at hx1
      exact (QuotientGroup.eq_one_iff _).mp hx1
    · intro hx
      apply Subtype.ext
      rw [hq x, hmkM_def]
      exact (QuotientGroup.eq_one_iff _).mpr hx
  -- `θ` inflates from a `θ̄ : Irr ↥H̄` along the surjection `q` (linear ⟹ `ker q = N ⊆ ker θ`).
  obtain ⟨θbar, hcompq⟩ :=
    exists_compHom_eq_of_subset_characterKernel hq_surj θ (by rw [hkerq]; exact hker)
  -- `θ̄` is nontrivial, else `θ = compHom q (triv) = triv`.
  have hθbar_ne : θbar ≠ trivialIrreducibleCharacter ↥Hbar := by
    intro hbar
    apply hθ_ne
    apply IrreducibleCharacter.ext
    rw [← hcompq, hbar]
    ext x
    simp [ClassFunction.compHom_apply, trivialIrreducibleCharacter,
      trivialClassFunction_apply]
  -- **B1′** (fixed-point-free action of `W̄₁` on `H̄`): `C_{H̄}(w̄) = 1` for `w̄ ∈ W̄₁∖1`.
  -- We only need the specific `w̄ = mkM w`; the S03 `≤ N` quotient lemma supplies it.
  have hNK : (⁅H, H⁆ : Subgroup ↥L) ≤ H := Subgroup.commutator_le_left H H
  have hcentral : ∀ x ∈ hyp.W1, x ≠ 1 →
      Subgroup.centralizer ({x} : Set ↥L) ⊓ H ≤ M := by
    intro x hxW1 hxne
    have hcw2 : Subgroup.centralizer ({x} : Set ↥L) ⊓ cert.K = cert.W2 :=
      cert.centralizer_W2 x (hW1 ▸ hxW1) hxne
    rw [hK] at hcw2
    rw [hcw2, hM_def]; exact hW2
  have hlift : ∀ x ∈ hyp.W1, x ≠ 1 → ∀ y ∈ H,
      mkM (x * y * x⁻¹) = mkM y →
        ∃ c : ↥L, c ∈ H ∧ mkM c = mkM y ∧ x * c * x⁻¹ = c := by
    intro x hxW1 hxne y hyH hfix
    have hcop_x : Nat.Coprime (Nat.card ↥(Subgroup.zpowers x)) (Nat.card ↥H) := by
      rw [Nat.card_zpowers]
      have hdvd : orderOf x ∣ Nat.card hyp.W1 := hyp.W1.orderOf_dvd_natCard hxW1
      exact (hcop.coprime_dvd_right hdvd).symm
    exact OddOrder.BG.Ch1.S03.fixedPoint_lift_of_generator_quotient_fixed
      hNK hcop_x (Or.inl (by infer_instance)) hyH hfix
  have hB1 : ∀ qx ∈ hyp.W1.map mkM, qx ≠ 1 →
      Subgroup.centralizer ({qx} : Set (↥L ⧸ M)) ⊓ Hbar = ⊥ := by
    rw [hHbar_def, hmkM_def]
    exact OddOrder.BG.Ch1.S03.quotient_centralizer_inf_kernel_eq_bot_of_fixedPoint_lift_of_le
      hcentral hlift
  -- Assemble: `I_L(θ) = H` by `le_antisymm`.
  apply le_antisymm
  · -- `I_L(θ) ≤ H`: a `g ∉ H` is `h·w` with `w ∈ W₁∖1`, and `w ∉ I_L(θ)`.
    intro g hg
    by_contra hgH
    -- Write `g = h * w` via the complement `L = H ⋊ W₁`.
    obtain ⟨⟨h, w⟩, hgw⟩ := (hyp.split.existsUnique g).exists
    rw [ClassFunction.mem_inertia] at hg
    -- `w ≠ 1`, else `g = h ∈ H`.
    have hwne : (w : ↥L) ≠ 1 := by
      rintro hw1
      apply hgH
      have : g = (h : ↥L) := by rw [← hgw, hw1, mul_one]
      rw [this]; exact h.property
    -- `h ∈ H ⊆ I_L(θ)`, so `w = h⁻¹·g ∈ I_L(θ)`.
    have hhinertia : (h : ↥L) ∈ ClassFunction.inertia (θ : ClassFunction ↥H ℂ) :=
      ClassFunction.subgroup_le_inertia (θ : ClassFunction ↥H ℂ) h.property
    have hwinertia : (w : ↥L) ∈ ClassFunction.inertia (θ : ClassFunction ↥H ℂ) := by
      have hwval : (w : ↥L) = (h : ↥L)⁻¹ * g := by rw [← hgw]; group
      rw [hwval]
      exact (ClassFunction.inertia (θ : ClassFunction ↥H ℂ)).mul_mem
        ((ClassFunction.inertia (θ : ClassFunction ↥H ℂ)).inv_mem hhinertia)
        (ClassFunction.mem_inertia.mpr hg)
    -- Transfer `w ∈ I_L(θ)` to `w̄ ∈ I_{Ḡ}(θ̄)`.
    rw [← hcompq] at hwinertia
    have hwbar : mkM (w : ↥L) ∈ ClassFunction.inertia (θbar : ClassFunction ↥Hbar ℂ) :=
      (mem_inertia_compHom_iff q hq hqinj (θbar : ClassFunction ↥Hbar ℂ) (w : ↥L)).mp hwinertia
    -- But `w̄ ∉ I_{Ḡ}(θ̄)`: `C_{H̄}(w̄) = 1`, abelian Brauer, `θ̄ ≠ triv`.
    have hwbar_mem : mkM (w : ↥L) ∈ hyp.W1.map mkM :=
      Subgroup.mem_map.mpr ⟨w, w.property, rfl⟩
    have hwbar_ne : mkM (w : ↥L) ≠ 1 := by
      intro hw1
      have hwM : (w : ↥L) ∈ M := by
        rw [hmkM_def, QuotientGroup.mk'_apply] at hw1
        exact (QuotientGroup.eq_one_iff _).mp hw1
      exact hwne (Subgroup.disjoint_def.mp hyp.split.disjoint (hNK (hM_def ▸ hwM)) w.property)
    have hfree : Subgroup.centralizer ({mkM (w : ↥L)} : Set (↥L ⧸ M)) ⊓ Hbar = ⊥ :=
      hB1 (mkM (w : ↥L)) hwbar_mem hwbar_ne
    have hclass : Nat.card (Function.fixedPoints
        (ConjClasses.conjByPerm (G := ↥L ⧸ M) (H := Hbar) (mkM (w : ↥L)))) = 1 :=
      card_fixedPoints_conjClassPerm_eq_one_of_commute_of_centralizer_inf_eq_bot
        (mkM (w : ↥L)) hHbar_comm hfree
    exact not_mem_inertia_of_ne_trivial_of_card_fixedClasses_eq_one
      (G := ↥L ⧸ M) (H := Hbar) (mkM (w : ↥L)) hclass hθbar_ne hwbar
  · exact ClassFunction.subgroup_le_inertia (θ : ClassFunction ↥H ℂ)

/-- **(T7-c2 case A) Inertia `I_L(θ) = H`** via the **fixed-point-free action on `Z`**.  Here
`Z ≤ H` is central in `H` (`Z.subgroupOf H ≤ Z(H)`), normalized by `W₁`, with `W₁∖1` acting
fixed-point-freely (`C_Z(w) = Z ∩ W₂ = 1` in case A).  If `w ∈ W₁∖1` fixed `θ`, the central linear
character `φ` of `Res_Z θ` ([Is] 2.27) would be `σ = (·)^w`-invariant, hence `≡ 1`
(`eq_one_of_fixedPointFree_invariant`), forcing `Z.subgroupOf H ⊆ Ker θ`, contradicting `hZker`.
So `I_L(θ) ∩ W₁ = 1` and the complement split `L = H ⋊ W₁` gives `I_L(θ) = H`.  Needs no Hall
coprimality and works for an arbitrary (not necessarily linear) `θ`. -/
theorem inertia_eq_H_of_c2_caseA (hyp : SibleyDadeHypothesis G L H)
    {Z : Subgroup ↥L} (hZH : Z ≤ H) (hZcentral : Z.subgroupOf H ≤ Subgroup.center ↥H)
    (hZnorm : ∀ w ∈ hyp.W1, w ∈ Subgroup.normalizer Z)
    (hZfpf : ∀ w ∈ hyp.W1, w ≠ 1 → Subgroup.centralizer ({w} : Set ↥L) ⊓ Z = ⊥)
    {θ : IrreducibleCharacter ↥H}
    (hZker : ¬ ((Z.subgroupOf H : Set ↥H) ⊆
      OddOrder.Peterfalvi.S03.characterKernel (θ : ClassFunction ↥H ℂ))) :
    letI : H.Normal := hyp.H_normal
    ClassFunction.inertia (θ : ClassFunction ↥H ℂ) = H := by
  classical
  let : H.Normal := hyp.H_normal
  have : Fintype ↥H := Fintype.ofFinite _
  have : Finite ↥L := Fintype.finite (Fintype.ofFinite _)
  obtain ⟨φ, hφirr, hφ1, -, hφpt⟩ :=
    θ.isIrreducible.exists_central_linear_restriction (Z.subgroupOf H) hZcentral
  have hφmul : ∀ a b : ↥(Z.subgroupOf H), φ (a * b) = φ a * φ b :=
    hφirr.map_mul_of_apply_one_eq_one hφ1
  have hθ1_ne : (θ : ClassFunction ↥H ℂ) 1 ≠ 0 := by
    obtain ⟨n, hpos, hn1, -⟩ := θ.isIrreducible.exists_natDegree_charValue_one_dvd_card
    rw [hn1]; exact_mod_cast hpos.ne'
  apply le_antisymm
  · intro g hg
    by_contra hgH
    obtain ⟨⟨h, w⟩, hgw⟩ := (hyp.split.existsUnique g).exists
    rw [ClassFunction.mem_inertia] at hg
    have hwne : (w : ↥L) ≠ 1 := by
      rintro hw1; apply hgH
      have : g = (h : ↥L) := by rw [← hgw, hw1, mul_one]
      rw [this]; exact h.property
    have hhinertia : (h : ↥L) ∈ ClassFunction.inertia (θ : ClassFunction ↥H ℂ) :=
      ClassFunction.subgroup_le_inertia (θ : ClassFunction ↥H ℂ) h.property
    have hwinertia : (w : ↥L) ∈ ClassFunction.inertia (θ : ClassFunction ↥H ℂ) := by
      have hwval : (w : ↥L) = (h : ↥L)⁻¹ * g := by rw [← hgw]; group
      rw [hwval]
      exact (ClassFunction.inertia _).mul_mem
        ((ClassFunction.inertia _).inv_mem hhinertia) (ClassFunction.mem_inertia.mpr hg)
    have hwW1 : (w : ↥L) ∈ hyp.W1 := w.property
    -- Conjugation `σ` by `w` on `Z`, fixed-point-free (`C_Z(w) = Z ∩ W₂ = 1`).
    set σ : MulAut ↥Z := Z.normalizerMonoidHom ⟨(w : ↥L), hZnorm (w : ↥L) hwW1⟩ with hσ_def
    have hσval : ∀ z : ↥Z, ((σ z : ↥Z) : ↥L) = (w : ↥L) * (z : ↥L) * (w : ↥L)⁻¹ := fun _ => rfl
    have hσfpf : MonoidHom.FixedPointFree σ := by
      intro z hz
      have hzmem : ((z : ↥Z) : ↥L) ∈ Subgroup.centralizer ({(w : ↥L)} : Set ↥L) ⊓ Z := by
        refine Subgroup.mem_inf.mpr ⟨?_, z.property⟩
        rw [Subgroup.mem_centralizer_iff]
        rintro y hy; rw [Set.mem_singleton_iff] at hy; subst hy
        have hzL := congrArg (Subtype.val : ↥Z → ↥L) hz
        rw [hσval] at hzL
        rw [mul_inv_eq_iff_eq_mul] at hzL
        exact hzL
      rw [hZfpf (w : ↥L) hwW1 hwne, Subgroup.mem_bot] at hzmem
      exact Subtype.ext hzmem
    -- `f = φ ∘ iso` is multiplicative and `σ`-invariant; brick ① gives `φ ≡ 1`.
    set iso : ↥Z ≃* ↥(Z.subgroupOf H) := (Subgroup.subgroupOfEquivOfLe hZH).symm with hiso_def
    have hisoL : ∀ z : ↥Z, (((iso z : ↥(Z.subgroupOf H)) : ↥H) : ↥L) = (z : ↥L) := fun _ => rfl
    set f : ↥Z → ℂ := fun z => φ (iso z) with hf_def
    have hfmul : ∀ a b : ↥Z, f (a * b) = f a * f b := fun a b => by
      simp only [hf_def, map_mul, hφmul]
    have hfone : f 1 = 1 := by simp only [hf_def, map_one, hφ1]
    have hfinv : ∀ z : ↥Z, f (σ z) = f z := by
      intro z
      have hconj : ClassFunction.conjBy (w : ↥L) (θ : ClassFunction ↥H ℂ)
          = (θ : ClassFunction ↥H ℂ) := ClassFunction.mem_inertia.mp hwinertia
      have hval : (θ : ClassFunction ↥H ℂ) ((iso (σ z) : ↥(Z.subgroupOf H)) : ↥H)
          = (θ : ClassFunction ↥H ℂ) ((iso z : ↥(Z.subgroupOf H)) : ↥H) := by
        have hc := congrArg (fun ψ : ClassFunction ↥H ℂ => ψ ((iso z : ↥(Z.subgroupOf H)) : ↥H))
          hconj
        simp only [ClassFunction.conjBy_apply] at hc
        rw [← hc]
        congr 1
      have e1 := hφpt (iso (σ z))
      have e2 := hφpt (iso z)
      have hmul : φ (iso (σ z)) * (θ : ClassFunction ↥H ℂ) 1
          = φ (iso z) * (θ : ClassFunction ↥H ℂ) 1 := by rw [← e1, hval]; exact e2
      simp only [hf_def]
      exact mul_right_cancel₀ hθ1_ne hmul
    -- `φ ≡ 1` forces `Z.subgroupOf H ⊆ Ker θ`, contradicting `hZker`.
    apply hZker
    intro x hx
    rw [SetLike.mem_coe] at hx
    rw [OddOrder.Peterfalvi.S03.mem_characterKernel, OddOrder.Peterfalvi.S03.characterDegree_def]
    have hφx : φ (⟨x, hx⟩ : ↥(Z.subgroupOf H)) = 1 := by
      have hfx := eq_one_of_fixedPointFree_invariant hσfpf hfmul hfone hfinv
        (iso.symm ⟨x, hx⟩)
      simpa only [hf_def, MulEquiv.apply_symm_apply] using hfx
    have hpt := hφpt (⟨x, hx⟩ : ↥(Z.subgroupOf H))
    rw [hφx, one_mul] at hpt
    exact hpt
  · exact ClassFunction.subgroup_le_inertia (θ : ClassFunction ↥H ℂ)

/-- **Peterfalvi (6.8) Y-family irreducibility.**  For a nontrivial degree-one (linear) source
character `θ` of `H`, the induced character `Ind_H^L θ` is irreducible.  Inertia `I_L(θ) = H`
(free action of `W₁`) is discharged via the (6.8)(c) disjunction and fed to [Is] Thm 6.34
(`isIrreducibleCharacter_induce_of_inertia_eq`):

* **(c1)** `L` Frobenius with kernel `H`: `isIrreducibleCharacter_induce_of_frobeniusGroup`
  (needs only `θ ≠ 1`; degree-one not used).
* **(c2)** Hyp (4.6): the inertia bridge `inertia_eq_H_of_c2` from
  `CertainTypeHypothesis.centralizer_W2` + Hall coprimality + Isaacs 3.28 on `H/H'` (T6 §5). -/
theorem isIrreducibleCharacter_induce_of_degree_one (hyp : SibleyDadeHypothesis G L H)
    {θ : IrreducibleCharacter ↥H}
    (hθ_one : (θ : ClassFunction ↥H ℂ) (1 : ↥H) = 1)
    (hθ_ne : θ ≠ trivialIrreducibleCharacter ↥H) :
    IsIrreducibleCharacter (ClassFunction.induce H (θ : ClassFunction ↥H ℂ)) := by
  let : H.Normal := hyp.H_normal
  have : Fintype ↥H := Fintype.ofFinite _
  rcases hyp.cases with hF | ⟨h46, _hdade, hK, hW1, _hprime, hW2, hcop⟩
  · exact isIrreducibleCharacter_induce_of_frobeniusGroup hF θ hθ_ne
  · -- (c2) inertia bridge: `I_L(θ) = H` via the abelian quotient `H/⁅H,H⁆` (Brauer + Isaacs 3.28).
    -- `cases` now carries the full `Hypothesis46`; project to the underlying
    -- `CertainTypeHypothesis`.
    exact isIrreducibleCharacter_induce_of_inertia_eq θ
      (hyp.inertia_eq_H_of_c2 h46.toCertainTypeHypothesis hK hW1 hW2 hcop hθ_one hθ_ne)

/-- **(6.8) `Y = S(H')` coherence (engine call from a constructed family).**  Given a family of
nontrivial linear source characters `χ_j : H →* ℂˣ` indexed by `Fin n` (`n ≥ 2`), pairwise
non-`L`-conjugate, with each `Ind_H^L (linear χ_j)` irreducible (`hirr`), the induced family
`Y = {Ind_H^L (linear χ_j)}` is coherent for Sibley's Dade map `tau`.

This is the (6.8) `Y`-step: the `χ_j` are the `Irr(H/H') ∖ {1}` orbit representatives (degree one,
so each `Ind` has the common degree `|W₁|`).  `hirr` and the pairwise non-conjugacy come from the
free `W₁`-action (`isIrreducibleCharacter_induce_of_degree_one`).  Injectivity of
`j ↦ Ind_H^L (linear χ_j)` is the cross-Mackey orthogonality `inner_induce_eq_zero_of_not_conj`;
the equal-degree coherence is then `coherentInducedDegreeOneFamily`. -/
noncomputable def coherentYFamily (hyp : SibleyDadeHypothesis G L H) [H.Normal] {n : ℕ} [NeZero n]
    (hn : 2 ≤ n) (χ : Fin n → (↥H →* ℂˣ))
    (hpairwise : ∀ i j : Fin n, i ≠ j → ∀ g : ↥L,
      IrreducibleCharacter.conjBy g (linearIrreducibleCharacter (χ i)) ≠
        linearIrreducibleCharacter (χ j))
    (hirr : ∀ j, IsIrreducibleCharacter
      (ClassFunction.induce H (linearIrreducibleCharacter (χ j) : ClassFunction ↥H ℂ))) :
    OddOrder.Peterfalvi.S07.IsCoherent (L := ↥L) (G := G) hyp.tau
      (Set.range (fun j => ClassFunction.induce H
        (linearIrreducibleCharacter (χ j) : ClassFunction ↥H ℂ)))
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) := by
  haveI : Fintype ↥H := Fintype.ofFinite _
  have hηinj : Function.Injective
      (fun j => (⟨ClassFunction.induce H (linearIrreducibleCharacter (χ j) : ClassFunction ↥H ℂ),
        hirr j⟩ : IrreducibleCharacter ↥L)) := by
    intro i j hij
    by_contra hne
    have h0 := inner_induce_eq_zero_of_not_conj
      (linearIrreducibleCharacter (χ i)) (linearIrreducibleCharacter (χ j))
      (fun g => hpairwise i j hne g)
    have hcoe : ClassFunction.induce H (linearIrreducibleCharacter (χ i) : ClassFunction ↥H ℂ) =
        ClassFunction.induce H (linearIrreducibleCharacter (χ j) : ClassFunction ↥H ℂ) :=
      congrArg Subtype.val hij
    rw [hcoe] at h0
    have h1 : ClassFunction.inner
        (ClassFunction.induce H (linearIrreducibleCharacter (χ j) : ClassFunction ↥H ℂ))
        (ClassFunction.induce H (linearIrreducibleCharacter (χ j) : ClassFunction ↥H ℂ)) = 1 := by
      simpa using irreducibleCharacter_inner_eq_ite
        (⟨ClassFunction.induce H (linearIrreducibleCharacter (χ j) : ClassFunction ↥H ℂ),
          hirr j⟩ : IrreducibleCharacter ↥L)
        (⟨ClassFunction.induce H (linearIrreducibleCharacter (χ j) : ClassFunction ↥H ℂ), hirr j⟩)
    rw [h1] at h0
    exact one_ne_zero h0
  exact coherentInducedDegreeOneFamily hyp hn
    (fun j => linearIrreducibleCharacter (χ j))
    (fun j => ⟨ClassFunction.induce H (linearIrreducibleCharacter (χ j) : ClassFunction ↥H ℂ),
      hirr j⟩)
    (fun _ => rfl) hηinj (fun j => linearIrreducibleCharacter_apply_one (χ j))

/-- **(6.8) `Y = S(H')` coherence, with induced irreducibility discharged internally.**
Compared with `coherentYFamily`, the caller supplies only nontrivial linear source characters and
pairwise non-`L`-conjugacy.  The irreducibility of each induced member is the genuine T6/c1-c2
brick `isIrreducibleCharacter_induce_of_degree_one`, not an extra hypothesis. -/
noncomputable def coherentYFamily_of_pairwiseNonconj
    (hyp : SibleyDadeHypothesis G L H) [H.Normal] {n : ℕ} [NeZero n]
    (hn : 2 ≤ n) (χ : Fin n → (↥H →* ℂˣ))
    (hχ_ne : ∀ j, χ j ≠ 1)
    (hpairwise : ∀ i j : Fin n, i ≠ j → ∀ g : ↥L,
      IrreducibleCharacter.conjBy g (linearIrreducibleCharacter (χ i)) ≠
        linearIrreducibleCharacter (χ j)) :
    OddOrder.Peterfalvi.S07.IsCoherent (L := ↥L) (G := G) hyp.tau
      (Set.range (fun j => ClassFunction.induce H
        (linearIrreducibleCharacter (χ j) : ClassFunction ↥H ℂ)))
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) := by
  refine hyp.coherentYFamily hn χ hpairwise ?_
  intro j
  exact hyp.isIrreducibleCharacter_induce_of_degree_one
    (linearIrreducibleCharacter_apply_one (χ j)) (by
      rw [Ne, linearIrreducibleCharacter_eq_trivial_iff]
      exact hχ_ne j)

end SibleyDadeHypothesis

end OddOrder.Peterfalvi.S08


