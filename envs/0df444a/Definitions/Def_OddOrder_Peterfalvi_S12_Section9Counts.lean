-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S12_Section9Counts
-- name    : OddOrder_Peterfalvi_S12_Section9Counts
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T12:59:56.3742+00:00
-- url     : https://prove2.me/theorems/065249de-5c6d-425f-9582-368f9da99972
-- title:
--   Peterfalvi §9/(11.8.1): counts for the Clifford sections (continuation)
-- statement:
--   A continuation file with counting results for Peterfalvi (11.8.1): linear-character counts via the abelianization and the orbit count $\#\{\text{nontrivial linear}\} = w_1\cdot|S(HC)|$.
--
--   Main declarations: `None` (`M' = (derivedInG M).subgroupOf M` is normal in `↥M` (it is `commutator ↥M` under…); `Hypothesis.mem_commutator_of_commute_W1` (Nonidentity `↥K`-elements commuting with a nonidentity `W₁`-element lie in `commutator ↥K`); `card_filter_degree_one_eq_card_abelianization` (The linear-character count); `Hypothesis.card_filter_linear_eq_w1_mul_card_SHCSet_filter` (Peterfalvi (11.8.1), the orbit count `#{nontrivial linear} = w₁ · |S(HC)|`).
--
--   The bundle also proves 4 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S12_Section9Counts.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S12_Section9Counts.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S12_HcBound

namespace OddOrder.Peterfalvi.S12

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

/-- `M' = (derivedInG M).subgroupOf M` is normal in `↥M` (it is `commutator ↥M` under
`comap_map_eq_self`). -/
instance {M : Subgroup G} : ((derivedInG M).subgroupOf M).Normal := by
  rw [derivedInG, Subgroup.subgroupOf,
    Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- **Nonidentity `↥K`-elements commuting with a nonidentity `W₁`-element lie in
`commutator ↥K`** — the `hfix` translation of Peterfalvi (8.4.d): such an element lands in
`M' ⊓ C_G(w) = W₂` (`TypePData.centralizer_W1`) and `W₂ ≤ M''` (`W2_le`), and `M''` pulls back
to `commutator ↥K` across `↥K ≃* ↥M'`. -/
theorem Hypothesis.mem_commutator_of_commute_W1 [Finite G] {M : Subgroup G}
    (hyp : Hypothesis M)
    {v : ↥M} (hv : v ∈ hyp.W1.subgroupOf M) (hvne : v ≠ 1)
    {x : ↥((derivedInG M).subgroupOf M)}
    (hcomm : (v : ↥M) * (x : ↥M) = (x : ↥M) * (v : ↥M)) :
    x ∈ commutator ↥((derivedInG M).subgroupOf M) := by
  -- `(x:G)` commutes with `(v:G)`, so lies in `M' ⊓ C_G(v) = W₂ ≤ M''`.
  have hvG : ((v : ↥M) : G) ∈ hyp.W1 := Subgroup.mem_subgroupOf.mp hv
  have hvGne : ((v : ↥M) : G) ≠ 1 := fun h => hvne (by ext; exact h)
  have hxG : ((x : ↥M) : G) ∈ derivedInG M := Subgroup.mem_subgroupOf.mp x.2
  have hxcen : ((x : ↥M) : G) ∈ Subgroup.centralizer ({((v : ↥M) : G)} : Set G) := by
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    have := congrArg (fun m : ↥M => (m : G)) hcomm
    simpa using this.symm
  have hxW2 : ((x : ↥M) : G) ∈ hyp.typeP.W2 := by
    rw [← hyp.typeP.centralizer_W1 _ hvG hvGne]
    exact ⟨hxG, hxcen⟩
  have hxM'' : ((x : ↥M) : G) ∈ secondDerivedInAmbient M := (hyp.typeP.W2_le hxW2).2
  -- pull `M'' = derivedInG M'` back to `commutator ↥K` across `e : ↥K ≃* ↥M'`.
  rw [secondDerivedInAmbient, derivedInG] at hxM''
  obtain ⟨c, hc, hcx⟩ := hxM''
  set e := Subgroup.subgroupOfEquivOfLe
    (Subgroup.map_subtype_le (commutator ↥M) : derivedInG M ≤ M) with he
  have hex : e x = c := by
    ext
    exact hcx.symm
  have hcmem : e.symm c ∈ commutator ↥((derivedInG M).subgroupOf M) := by
    have hmap : (commutator ↥(derivedInG M)).map e.symm.toMonoidHom
        ≤ commutator ↥((derivedInG M).subgroupOf M) := by
      have h1 : (commutator ↥(derivedInG M)).map e.symm.toMonoidHom
          = ⁅(⊤ : Subgroup ↥(derivedInG M)).map e.symm.toMonoidHom,
              (⊤ : Subgroup ↥(derivedInG M)).map e.symm.toMonoidHom⁆ :=
        Subgroup.map_commutator ⊤ ⊤ _
      rw [h1]
      exact Subgroup.commutator_mono le_top le_top
    exact hmap (Subgroup.mem_map_of_mem _ hc)
  rw [← hex, MulEquiv.symm_apply_apply] at hcmem
  exact hcmem

/-- **A nontrivial linear character of `M'` has inertia group exactly `M'`** — Peterfalvi's
(8.4.d) at the character level, the heart of the h56 anchor.

If some `w ∈ M ∖ M'` fixed `θ`, its `W₁`-component `v ≠ 1` (through `M = M' ⋊ W₁`,
`M_complement`; the `M'`-component is absorbed by `ClassFunction.subgroup_le_inertia`) would fix
`θ` too.  The
`W₁`-conjugation action on `M'/M''` is fixed-point-free (`quotient_of_fixedPoints_le`, from
`(|W₁|, |M'|) = 1` (`coprime_card_W1_derived`) and `C_{M'}(v) = W₂ ≤ M''`
(`mem_commutator_of_commute_W1`)), so `x ↦ (v•x)·x⁻¹` is injective, hence *surjective* on the
finite `M'/M''`.  Every `y ∈ M'` is then `(v•x)·x⁻¹` mod `M''`; a `v`-fixed multiplicative `θ`
(trivial on `M''` by multiplicativity) evaluates to `θ(v•x)·θ(x)⁻¹ = 1` on it — so `θ = 1`,
a contradiction. -/
theorem Hypothesis.inertia_eq_derived_of_linear [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    {θ : IrreducibleCharacter ↥((derivedInG M).subgroupOf M)}
    (hθne : θ ≠ trivialIrreducibleCharacter ↥((derivedInG M).subgroupOf M))
    (hθdeg : (θ : ClassFunction ↥((derivedInG M).subgroupOf M) ℂ) 1 = 1) :
    ClassFunction.inertia (θ : ClassFunction ↥((derivedInG M).subgroupOf M) ℂ)
      = (derivedInG M).subgroupOf M := by
  classical
  have : Fintype G := Fintype.ofFinite _
  refine le_antisymm ?_ (ClassFunction.subgroup_le_inertia _)
  intro w hw
  by_contra hwK
  -- decompose `w = k · v` through the complement `M = M' ⋊ W₁`; `v ≠ 1` since `w ∉ M'`.
  obtain ⟨⟨k, v⟩, hkv, -⟩ := hyp.typeP.M_complement.existsUnique (w : ↥M)
  have hvI : (v : ↥M) ∈ ClassFunction.inertia
      (θ : ClassFunction ↥((derivedInG M).subgroupOf M) ℂ) := by
    have hkI : (k : ↥M) ∈ ClassFunction.inertia
        (θ : ClassFunction ↥((derivedInG M).subgroupOf M) ℂ) :=
      ClassFunction.subgroup_le_inertia _ k.2
    have hveq : (v : ↥M) = (k : ↥M)⁻¹ * w := by
      rw [← hkv]; group
    rw [hveq]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hkI) hw
  have hvne : (v : ↥M) ≠ 1 := by
    intro hv1
    refine hwK ?_
    have hwk : w = (k : ↥M) := by rw [← hkv, hv1, mul_one]
    rw [hwk]; exact k.2
  have hvfix : ClassFunction.conjBy (v : ↥M)
      (θ : ClassFunction ↥((derivedInG M).subgroupOf M) ℂ)
      = (θ : ClassFunction ↥((derivedInG M).subgroupOf M) ℂ) := hvI
  -- rebind the complement component as a subgroup-subtype element for the action.
  have hvW1s : (v : ↥M) ∈ hyp.W1.subgroupOf M := v.2
  -- the `W₁`-conjugation action on `↥M'` and its fixed-point-free quotient action mod `M''`.
  let act : MulDistribMulAction ↥(hyp.W1.subgroupOf M) ↥((derivedInG M).subgroupOf M) :=
    MulDistribMulAction.compHom _
      ((MulAut.conjNormal (H := (derivedInG M).subgroupOf M)).comp
        (hyp.W1.subgroupOf M).subtype)
  have hsmul : ∀ (a : ↥(hyp.W1.subgroupOf M)) (x : ↥((derivedInG M).subgroupOf M)),
      ((a • x : ↥((derivedInG M).subgroupOf M)) : ↥M)
      = (a : ↥M) * (x : ↥M) * (a : ↥M)⁻¹ := by
    intro a x
    change ((MulAut.conjNormal (H := (derivedInG M).subgroupOf M)
      ((hyp.W1.subgroupOf M).subtype a)) x : ↥M) = _
    rw [MulAut.conjNormal_apply]; rfl
  have hMinv : ∀ a : ↥(hyp.W1.subgroupOf M),
      ∀ m ∈ commutator ↥((derivedInG M).subgroupOf M),
      a • m ∈ commutator ↥((derivedInG M).subgroupOf M) := by
    intro a m hm
    have hmap := Subgroup.characteristic_iff_map_eq.mp
      (inferInstance : (commutator ↥((derivedInG M).subgroupOf M)).Characteristic)
      (MulDistribMulAction.toMulAut _ _ a)
    have hmem : (MulDistribMulAction.toMulAut _ _ a).toMonoidHom m
        ∈ commutator ↥((derivedInG M).subgroupOf M) := by
      rw [← hmap]; exact Subgroup.mem_map_of_mem _ hm
    simpa using hmem
  have hfixle : ∀ a : ↥(hyp.W1.subgroupOf M), a ≠ 1 →
      ∀ x : ↥((derivedInG M).subgroupOf M), a • x = x →
      x ∈ commutator ↥((derivedInG M).subgroupOf M) := by
    intro a ha x hax
    have haMne : (a : ↥M) ≠ 1 := fun h => ha (Subtype.ext h)
    refine hyp.mem_commutator_of_commute_W1 a.2 haMne (x := x) ?_
    have h1 := hsmul a x
    rw [hax] at h1
    exact mul_inv_eq_iff_eq_mul.mp h1.symm
  have hCop : Nat.Coprime (Nat.card ↥(hyp.W1.subgroupOf M))
      (Nat.card ↥((derivedInG M).subgroupOf M)) := by
    have h1 : Nat.card ↥(hyp.W1.subgroupOf M) = Nat.card ↥hyp.W1 :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hyp.typeP.W1_le).toEquiv
    have h2 : Nat.card ↥((derivedInG M).subgroupOf M) = Nat.card ↥(derivedInG M) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (Subgroup.map_subtype_le (commutator ↥M) : derivedInG M ≤ M)).toEquiv
    rw [h1, h2]
    exact (typePData_W1_hall_coprime hG hyp.maximal (hyp.bgTypeP hG) hyp.typeP).symm
  have hFrob := OddOrder.Isaacs.Ch06.IsFrobeniusAction.quotient_of_fixedPoints_le
    hCop (commutator ↥((derivedInG M).subgroupOf M)) hMinv hfixle
  let actQ := OddOrder.Isaacs.Ch06.IsFrobeniusAction.invariantQuotientMulDistribMulAction
    (N := ↥((derivedInG M).subgroupOf M)) (commutator ↥((derivedInG M).subgroupOf M)) hMinv
  -- `x ↦ (v•x)·x⁻¹` is injective mod `M''` (fixed-point-freeness), hence surjective.
  set v' : ↥(hyp.W1.subgroupOf M) := ⟨(v : ↥M), hvW1s⟩ with hv'
  have hvne' : v' ≠ 1 := fun h => hvne (congrArg Subtype.val h)
  have hinj : Function.Injective
      (fun q : (↥((derivedInG M).subgroupOf M)
        ⧸ commutator ↥((derivedInG M).subgroupOf M)) => (v' • q) * q⁻¹) := by
    intro q₁ q₂ h12
    simp only at h12
    have hstep : v' • (q₂⁻¹ * q₁) = q₂⁻¹ * q₁ := by
      have h2 := mul_inv_eq_iff_eq_mul.mp h12
      rw [smul_mul', smul_inv']
      have h3 : v' • q₁ = (v' • q₂) * q₂⁻¹ * q₁ := by rw [← h2]
      rw [h3]
      group
    by_contra hne
    refine hFrob v' hvne' (q₂⁻¹ * q₁) (fun h => hne ?_) hstep
    have h4 : q₁ = q₂ * (q₂⁻¹ * q₁) := by group
    rw [h4, h, mul_one]
  have hsurj := Finite.surjective_of_injective hinj
  -- `θ` is multiplicative, trivial on `M''`, and `v`-conjugation-invariant.
  have hmul := θ.isIrreducible.map_mul_of_apply_one_eq_one hθdeg
  have hinv : ∀ x : ↥((derivedInG M).subgroupOf M),
      (θ : ClassFunction ↥((derivedInG M).subgroupOf M) ℂ) x⁻¹
      = ((θ : ClassFunction ↥((derivedInG M).subgroupOf M) ℂ) x)⁻¹ := by
    intro x
    have h1 : (θ : ClassFunction ↥((derivedInG M).subgroupOf M) ℂ) x
        * (θ : ClassFunction ↥((derivedInG M).subgroupOf M) ℂ) x⁻¹ = 1 := by
      rw [← hmul, mul_inv_cancel]; exact hθdeg
    exact eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact h1)
  have hval_ne : ∀ x : ↥((derivedInG M).subgroupOf M),
      (θ : ClassFunction ↥((derivedInG M).subgroupOf M) ℂ) x ≠ 0 := by
    intro x h0
    have h1 : (θ : ClassFunction ↥((derivedInG M).subgroupOf M) ℂ) x
        * (θ : ClassFunction ↥((derivedInG M).subgroupOf M) ℂ) x⁻¹ = 1 := by
      rw [← hmul, mul_inv_cancel]; exact hθdeg
    rw [h0, zero_mul] at h1
    exact one_ne_zero h1.symm
  have hN1 : ∀ n ∈ commutator ↥((derivedInG M).subgroupOf M),
      (θ : ClassFunction ↥((derivedInG M).subgroupOf M) ℂ) n = 1 := by
    intro n hn
    rw [commutator_eq_closure] at hn
    induction hn using Subgroup.closure_induction with
    | mem x hx =>
        obtain ⟨a, b, rfl⟩ := hx
        change (θ : ClassFunction ↥((derivedInG M).subgroupOf M) ℂ) (a * b * a⁻¹ * b⁻¹) = 1
        rw [hmul, hmul, hmul, hinv, hinv]
        field_simp [hval_ne a, hval_ne b]
    | one => exact hθdeg
    | mul x y _ _ hx hy => rw [hmul, hx, hy, one_mul]
    | inv x _ hx => rw [hinv, hx, inv_one]
  -- every `y ∈ M'` is `(v•x)·x⁻¹ · n`, so `θ y = θ(v•x)·θ(x)⁻¹ = 1`.
  have hall : ∀ y : ↥((derivedInG M).subgroupOf M),
      (θ : ClassFunction ↥((derivedInG M).subgroupOf M) ℂ) y = 1 := by
    intro y
    obtain ⟨q, hq⟩ := hsurj (QuotientGroup.mk y)
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    have hmk : (QuotientGroup.mk ((v' • x) * x⁻¹) :
        ↥((derivedInG M).subgroupOf M) ⧸ commutator ↥((derivedInG M).subgroupOf M))
        = QuotientGroup.mk y := by
      rw [← hq]; rfl
    have hmem := (QuotientGroup.eq (s := commutator ↥((derivedInG M).subgroupOf M))).mp hmk
    have hyeq : y = (v' • x) * x⁻¹ * (((v' • x) * x⁻¹)⁻¹ * y) := by group
    have hθvsx : (θ : ClassFunction ↥((derivedInG M).subgroupOf M) ℂ) (v' • x)
        = (θ : ClassFunction ↥((derivedInG M).subgroupOf M) ℂ) x := by
      have hcoe : ((v' • x : ↥((derivedInG M).subgroupOf M)) : ↥M)
          = (v : ↥M) * (x : ↥M) * (v : ↥M)⁻¹ := hsmul v' x
      have h5 := congrArg
        (fun f : ClassFunction ↥((derivedInG M).subgroupOf M) ℂ => f x) hvfix
      simp only [ClassFunction.conjBy_apply] at h5
      rw [← h5]
      exact congrArg _ (Subtype.ext hcoe)
    rw [hyeq, hmul, hmul, hθvsx, hinv, hN1 _ hmem]
    field_simp [hval_ne x]
  -- contradiction: `θ` is the trivial character.
  refine hθne (Subtype.ext ?_)
  ext x
  rw [hall x]
  rfl

/-- **Peterfalvi (8.5.a)/(11.2): `C = C_U(H)` is normalized by `M`** (the `C_normalized_by_M`
obligation of the (11.2) setup): `F(M) = H ⊔ C` (`TypePData.fitting_eq`) is `M`-invariant; `H` and
`C` centralize each other with coprime orders (`typeP_coprime_H_uW1`), so the `M`-conjugate of a
`C`-element, decomposed along `F(M) = H·C`, has trivial `H`-part by the uniqueness of the
commuting coprime (`π(H)`, `π(H)'`) decomposition (`isPiElement_mul_unique`). -/
theorem typePData_C_normalized_by_M [Finite G] {M : Subgroup G} (data : TypePData M)
    (hU : data.U ≠ ⊥) :
    M ≤ Subgroup.normalizer
      ((data.U ⊓ Subgroup.centralizer (data.H : Set G) : Subgroup G) : Set G) := by
  classical
  -- `F(M)` mapped to `G` is normalized by all of `M`
  have hFn : M ≤ Subgroup.normalizer
      (((OddOrder.Isaacs.Ch01.fitting ↥M).map M.subtype : Subgroup G) : Set G) := by
    have h := Subgroup.le_normalizer_map (H := OddOrder.Isaacs.Ch01.fitting ↥M) M.subtype
    rwa [Subgroup.normalizer_eq_top_iff.mpr inferInstance, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype] at h
  -- `C ≤ N(H)` (it centralizes `H`), so `↑(H ⊔ C) = ↑H * ↑C` as sets
  have hCleNH : (data.U ⊓ Subgroup.centralizer (data.H : Set G) : Subgroup G)
      ≤ Subgroup.normalizer (data.H : Set G) :=
    inf_le_right.trans (Subgroup.centralizer_le_normalizer (data.H : Set G))
  have hHC : ((data.H ⊔ (data.U ⊓ Subgroup.centralizer (data.H : Set G)) : Subgroup G) : Set G)
      = (data.H : Set G) * ((data.U ⊓ Subgroup.centralizer (data.H : Set G) : Subgroup G) : Set
          G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left _ _ hCleNH
  -- coprimality of `|H|` and `|U|`
  have hcoHU : Nat.Coprime (Nat.card ↥data.H) (Nat.card ↥data.U) :=
    (OddOrder.Peterfalvi.S11.typeP_coprime_H_uW1 data hU).coprime_dvd_right
      (Subgroup.card_dvd_of_le le_sup_left)
  -- orders of `C`-elements are `π(H)'`; orders of `H`-elements are `π(H)`
  set π : Set ℕ := {p : ℕ | p ∣ Nat.card ↥data.H} with hπ_def
  have hPiH : ∀ h ∈ data.H, IsPiElement π h := by
    intro h hh p hp
    have hdvd : orderOf h ∣ Nat.card ↥data.H := by
      have h1 : orderOf ((⟨h, hh⟩ : ↥data.H) : G) = orderOf (⟨h, hh⟩ : ↥data.H) :=
        orderOf_injective data.H.subtype data.H.subtype_injective ⟨h, hh⟩
      rw [show ((⟨h, hh⟩ : ↥data.H) : G) = h from rfl] at h1
      rw [h1]
      exact orderOf_dvd_natCard _
    exact (Nat.dvd_of_mem_primeFactors hp).trans hdvd
  have hPiC : ∀ c ∈ data.U, IsPiElement πᶜ c := by
    intro c hc p hp
    have hdvd : orderOf c ∣ Nat.card ↥data.U := by
      have h1 : orderOf ((⟨c, hc⟩ : ↥data.U) : G) = orderOf (⟨c, hc⟩ : ↥data.U) :=
        orderOf_injective data.U.subtype data.U.subtype_injective ⟨c, hc⟩
      rw [show ((⟨c, hc⟩ : ↥data.U) : G) = c from rfl] at h1
      rw [h1]
      exact orderOf_dvd_natCard _
    intro hpH
    have hprime := Nat.prime_of_mem_primeFactors hp
    have hpU : p ∣ Nat.card ↥data.U := (Nat.dvd_of_mem_primeFactors hp).trans hdvd
    have hgcd : p ∣ Nat.gcd (Nat.card ↥data.H) (Nat.card ↥data.U) := Nat.dvd_gcd hpH hpU
    rw [hcoHU] at hgcd
    exact hprime.one_lt.ne' (Nat.dvd_one.mp hgcd)
  -- one-sided conjugation stability suffices
  have key : ∀ g ∈ M, ∀ x ∈ (data.U ⊓ Subgroup.centralizer (data.H : Set G) : Subgroup G),
      g * x * g⁻¹ ∈ (data.U ⊓ Subgroup.centralizer (data.H : Set G) : Subgroup G) := by
    intro g hg x hx
    -- the conjugate lies in `F(M) = H ⊔ C`
    have hxF : x ∈ (OddOrder.Isaacs.Ch01.fitting ↥M).map M.subtype := by
      rw [data.fitting_eq]
      exact Subgroup.mem_sup_right hx
    have hgxF : g * x * g⁻¹ ∈ (OddOrder.Isaacs.Ch01.fitting ↥M).map M.subtype :=
      ((Subgroup.mem_normalizer_iff.mp (hFn hg)) x).mp hxF
    rw [data.fitting_eq, ← SetLike.mem_coe, hHC, Set.mem_mul] at hgxF
    obtain ⟨h, hh, c, hc, hhc⟩ := hgxF
    -- `h` and `c` commute (`c` centralizes `H`)
    have hcomm : Commute h c := Subgroup.mem_centralizer_iff.mp hc.2 h hh
    -- the conjugate is a `π'`-element (conjugation preserves order, `x ∈ U`)
    have hgx_pi : IsPiElement πᶜ (g * x * g⁻¹) := by
      intro p hp
      have horder : orderOf (g * x * g⁻¹) = orderOf x := by
        have h1 := orderOf_injective (MulAut.conj g).toMonoidHom
          (MulAut.conj g).injective x
        simpa [MulAut.conj_apply] using h1
      rw [horder] at hp
      exact hPiC x hx.1 p hp
    -- uniqueness of the commuting coprime decomposition: the `H`-part is trivial
    obtain ⟨hh1, hceq⟩ := isPiElement_mul_unique (π := π) hhc hcomm
      (hPiH h hh) (hPiC c hc.1)
      (one_mul (g * x * g⁻¹)) (Commute.one_left _) (isPiElement_one π) hgx_pi
    rw [← hhc, hh1, one_mul]
    exact hc
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact key g hg x hx
  · intro hx
    have h1 := key g⁻¹ (inv_mem hg) _ hx
    simpa [mul_assoc] using h1

open scoped Classical in
/-- **The linear-character count** (Pontryagin): for a finite group `H`, the number of degree-one
irreducible characters equals `|H^{ab}| = [H : H']`.  Degree-one irreducibles are exactly the
multiplicative characters `H →* ℂˣ` (`linearIrreducibleCharacter`,
`exists_linearIrreducibleCharacter_eq_of_apply_one_eq_one`); those factor through the
abelianization (`Abelianization.lift`), whose dual has the same cardinality (Pontryagin,
`CommGroup.monoidHom_mulEquiv_of_hasEnoughRootsOfUnity`).  This is the
`#(linear sources) = |HU/HC| = |U/C| = u` input of the (11.8.1) `|S(HC)| = n` count
(Coq `size_S1`, `card_Iirr_abelian`). -/
theorem card_filter_degree_one_eq_card_abelianization (H : Type*) [Group H] [Finite H] :
    (Finset.univ.filter fun θ : IrreducibleCharacter H =>
        (θ : ClassFunction H ℂ) 1 = 1).card = Nat.card (Abelianization H) := by
  classical
  have hbij : Function.Bijective (fun ψ : H →* ℂˣ =>
      (⟨linearIrreducibleCharacter ψ, linearIrreducibleCharacter_apply_one ψ⟩ :
        {θ : IrreducibleCharacter H // (θ : ClassFunction H ℂ) 1 = 1})) := by
    constructor
    · intro a b hab
      exact linearIrreducibleCharacter_injective (congrArg Subtype.val hab)
    · rintro ⟨θ, hθ⟩
      obtain ⟨ψ, hψ⟩ := θ.property.exists_linearIrreducibleCharacter_eq_of_apply_one_eq_one hθ
      exact ⟨ψ, Subtype.ext (Subtype.ext hψ)⟩
  calc (Finset.univ.filter fun θ : IrreducibleCharacter H =>
          (θ : ClassFunction H ℂ) 1 = 1).card
      = Nat.card {θ : IrreducibleCharacter H // (θ : ClassFunction H ℂ) 1 = 1} := by
        rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    _ = Nat.card (H →* ℂˣ) := (Nat.card_eq_of_bijective _ hbij).symm
    _ = Nat.card (Abelianization H →* ℂˣ) := Nat.card_congr Abelianization.lift
    _ = Nat.card (Abelianization H) :=
        Nat.card_congr (CommGroup.monoidHom_mulEquiv_of_hasEnoughRootsOfUnity
          (Abelianization H) ℂ).some.toEquiv

open scoped Classical FiniteInduce in
/-- **Peterfalvi (11.8.1), the orbit count `#{nontrivial linear} = w₁ · |S(HC)|`** (Coq `size_S1`
without the (11.5) arithmetic): every nontrivial linear character `θ` of `M'` induces irreducibly
to a degree-`w₁` member of `S = inducedFamily M` (`inertia_eq_derived_of_linear` + [Is] 6.34);
every degree-`w₁` irreducible member arises this way (the degree forces a linear source); and each
such member has exactly `w₁ = [M : M']` sources — its conjugation orbit, free since the inertia
group is `M'` (`card_filter_induce_eq_index_inertia`).  So the nontrivial linear characters of
`M'` are counted with multiplicity `w₁` by the degree-`w₁` irreducible members `S(HC)` of `S`. -/
theorem Hypothesis.card_filter_linear_eq_w1_mul_card_SHCSet_filter [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M) :
    (Finset.univ.filter fun θ : IrreducibleCharacter ↥((derivedInG M).subgroupOf M) =>
        θ ≠ trivialIrreducibleCharacter ↥((derivedInG M).subgroupOf M) ∧
          (θ : ClassFunction ↥((derivedInG M).subgroupOf M) ℂ) 1 = 1).card
      = hyp.w1 * (Finset.univ.filter fun χ : IrreducibleCharacter ↥M =>
          (χ : ClassFunction ↥M ℂ) ∈ inducedFamily M ∧
            ((χ : ClassFunction ↥M ℂ) : ↥M → ℂ) 1 = (hyp.w1 : ℂ)).card := by
  have := hyp.finiteG
  classical
  have hidx : ((derivedInG M).subgroupOf M).index = hyp.w1 :=
    hyp.typeP.card_W1_eq_derived_index.symm
  have hw1ne : (hyp.w1 : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne _)
  -- a nontrivial linear character of `M'` induces irreducibly
  have hirr : ∀ θ : IrreducibleCharacter ↥((derivedInG M).subgroupOf M),
      θ ≠ trivialIrreducibleCharacter ↥((derivedInG M).subgroupOf M) →
      (θ : ClassFunction ↥((derivedInG M).subgroupOf M) ℂ) 1 = 1 →
      IsIrreducibleCharacter (ClassFunction.induce ((derivedInG M).subgroupOf M)
        (θ : ClassFunction ↥((derivedInG M).subgroupOf M) ℂ)) := fun θ hne hdeg =>
    isIrreducibleCharacter_induce_of_inertia_eq θ (hyp.inertia_eq_derived_of_linear hG hne hdeg)
  -- the nontrivial linear characters are closed under `↥M`-conjugation
  have hTinv : ∀ θ ∈ (Finset.univ.filter
        fun θ : IrreducibleCharacter ↥((derivedInG M).subgroupOf M) =>
          θ ≠ trivialIrreducibleCharacter ↥((derivedInG M).subgroupOf M) ∧
            (θ : ClassFunction ↥((derivedInG M).subgroupOf M) ℂ) 1 = 1),
      ∀ g : ↥M, IrreducibleCharacter.conjBy g θ ∈ (Finset.univ.filter
        fun θ : IrreducibleCharacter ↥((derivedInG M).subgroupOf M) =>
          θ ≠ trivialIrreducibleCharacter ↥((derivedInG M).subgroupOf M) ∧
            (θ : ClassFunction ↥((derivedInG M).subgroupOf M) ℂ) 1 = 1) := by
    intro θ hθ g
    rw [Finset.mem_filter] at hθ ⊢
    obtain ⟨-, hne, hdeg⟩ := hθ
    refine ⟨Finset.mem_univ _, ?_, ?_⟩
    · intro heq
      refine hne ?_
      have h1 : IrreducibleCharacter.conjBy (g⁻¹ : ↥M) (IrreducibleCharacter.conjBy g θ) = θ := by
        rw [← IrreducibleCharacter.conjBy_mul]
        simp
      rw [heq] at h1
      have h2 : IrreducibleCharacter.conjBy (g⁻¹ : ↥M)
          (trivialIrreducibleCharacter ↥((derivedInG M).subgroupOf M))
          = trivialIrreducibleCharacter ↥((derivedInG M).subgroupOf M) := by
        apply IrreducibleCharacter.ext
        rw [IrreducibleCharacter.coe_conjBy]
        ext x
        simp [ClassFunction.conjBy_apply]
      rw [h2] at h1
      exact h1.symm
    · rw [conjBy_apply_one]
      exact hdeg
  -- fiberwise count over the induction map: each fiber is a free conjugation orbit of size `w₁`
  rw [Finset.card_eq_sum_card_fiberwise (fun θ hθ => Finset.mem_image_of_mem
    (fun θ' : IrreducibleCharacter ↥((derivedInG M).subgroupOf M) =>
      ClassFunction.induce ((derivedInG M).subgroupOf M) θ'.toClassFunction) hθ)]
  have hfib : ∀ φ ∈ (Finset.univ.filter
        fun θ : IrreducibleCharacter ↥((derivedInG M).subgroupOf M) =>
          θ ≠ trivialIrreducibleCharacter ↥((derivedInG M).subgroupOf M) ∧
            (θ : ClassFunction ↥((derivedInG M).subgroupOf M) ℂ) 1 = 1).image
        (fun θ' : IrreducibleCharacter ↥((derivedInG M).subgroupOf M) =>
          ClassFunction.induce ((derivedInG M).subgroupOf M) θ'.toClassFunction),
      ((Finset.univ.filter
        fun θ : IrreducibleCharacter ↥((derivedInG M).subgroupOf M) =>
          θ ≠ trivialIrreducibleCharacter ↥((derivedInG M).subgroupOf M) ∧
            (θ : ClassFunction ↥((derivedInG M).subgroupOf M) ℂ) 1 = 1).filter
        fun θ => ClassFunction.induce ((derivedInG M).subgroupOf M) θ.toClassFunction = φ).card
        = hyp.w1 := by
    intro φ hφ
    obtain ⟨θ₀, hθ₀, rfl⟩ := Finset.mem_image.mp hφ
    rw [card_filter_induce_eq_index_inertia _ hTinv θ₀ hθ₀]
    rw [Finset.mem_filter] at hθ₀
    rw [show IrreducibleCharacter.inertia (G := ↥M) θ₀ = (derivedInG M).subgroupOf M from
      hyp.inertia_eq_derived_of_linear hG hθ₀.2.1 hθ₀.2.2]
    exact hidx
  rw [Finset.sum_congr rfl hfib, Finset.sum_const, smul_eq_mul]
  -- identify the image with the degree-`w₁` irreducible members of `S`
  have himage : (Finset.univ.filter
        fun θ : IrreducibleCharacter ↥((derivedInG M).subgroupOf M) =>
          θ ≠ trivialIrreducibleCharacter ↥((derivedInG M).subgroupOf M) ∧
            (θ : ClassFunction ↥((derivedInG M).subgroupOf M) ℂ) 1 = 1).image
        (fun θ' : IrreducibleCharacter ↥((derivedInG M).subgroupOf M) =>
          ClassFunction.induce ((derivedInG M).subgroupOf M) θ'.toClassFunction)
      = (Finset.univ.filter fun χ : IrreducibleCharacter ↥M =>
          (χ : ClassFunction ↥M ℂ) ∈ inducedFamily M ∧
            ((χ : ClassFunction ↥M ℂ) : ↥M → ℂ) 1 = (hyp.w1 : ℂ)).image
          (fun χ : IrreducibleCharacter ↥M => (χ : ClassFunction ↥M ℂ)) := by
    ext φ
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨θ, ⟨hne, hdeg⟩, rfl⟩
      refine ⟨⟨ClassFunction.induce ((derivedInG M).subgroupOf M)
        (θ : ClassFunction ↥((derivedInG M).subgroupOf M) ℂ), hirr θ hne hdeg⟩,
        ⟨⟨θ, hne, rfl⟩, ?_⟩, rfl⟩
      change ((ClassFunction.induce ((derivedInG M).subgroupOf M)
        (θ : ClassFunction ↥((derivedInG M).subgroupOf M) ℂ) :
          ClassFunction ↥M ℂ) : ↥M → ℂ) 1 = (hyp.w1 : ℂ)
      rw [ClassFunction.induce_apply_one, hdeg, mul_one, hidx]
    · rintro ⟨χ, ⟨⟨θ, hθne, hχeq⟩, hχdeg⟩, rfl⟩
      have hθdeg : (θ : ClassFunction ↥((derivedInG M).subgroupOf M) ℂ) 1 = 1 := by
        have h1 := ClassFunction.induce_apply_one ((derivedInG M).subgroupOf M)
          (θ : ClassFunction ↥((derivedInG M).subgroupOf M) ℂ)
        rw [← hχeq] at h1
        rw [hχdeg, hidx] at h1
        exact mul_left_cancel₀ hw1ne (h1.symm.trans (mul_one (hyp.w1 : ℂ)).symm)
      exact ⟨θ, ⟨hθne, hθdeg⟩, hχeq.symm⟩
  rw [himage, Finset.card_image_of_injective _
    (fun a b hab => IrreducibleCharacter.ext hab), Nat.mul_comm]

open scoped Classical in
/-- **Peterfalvi (11.8.1), abelianization form of the `S(HC)` count**:
`|M'/M''| = w₁ · |S(HC)| + 1`.  The linear characters of `M'` number `|M'{}^{ab}|`
(`card_filter_degree_one_eq_card_abelianization`); one of them is trivial, and the nontrivial
ones are counted with multiplicity `w₁` by the degree-`w₁` irreducible members of `S`
(`card_filter_linear_eq_w1_mul_card_SHCSet_filter`).  Downstream ((11.5) `M'' = HC`,
`S13.secondDerived_eq_HC`) this becomes `u = w₁·|S(HC)| + 1`, i.e. `|S(HC)| = (u−1)/w₁ = n`. -/
theorem Hypothesis.card_abelianization_derived_eq_w1_mul_card_SHCSet_add_one [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M) :
    Nat.card (Abelianization ↥((derivedInG M).subgroupOf M))
      = hyp.w1 * (Finset.univ.filter fun χ : IrreducibleCharacter ↥M =>
          (χ : ClassFunction ↥M ℂ) ∈ inducedFamily M ∧
            ((χ : ClassFunction ↥M ℂ) : ↥M → ℂ) 1 = (hyp.w1 : ℂ)).card + 1 := by
  have := hyp.finiteG
  classical
  rw [← card_filter_degree_one_eq_card_abelianization,
    ← hyp.card_filter_linear_eq_w1_mul_card_SHCSet_filter hG]
  -- the trivial character is the one degree-one character excluded by the nontriviality filter
  have htriv : trivialIrreducibleCharacter ↥((derivedInG M).subgroupOf M)
      ∈ (Finset.univ.filter fun θ : IrreducibleCharacter ↥((derivedInG M).subgroupOf M) =>
        (θ : ClassFunction ↥((derivedInG M).subgroupOf M) ℂ) 1 = 1) := by
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, rfl⟩
  have herase : (Finset.univ.filter
        fun θ : IrreducibleCharacter ↥((derivedInG M).subgroupOf M) =>
          θ ≠ trivialIrreducibleCharacter ↥((derivedInG M).subgroupOf M) ∧
            (θ : ClassFunction ↥((derivedInG M).subgroupOf M) ℂ) 1 = 1)
      = (Finset.univ.filter
        fun θ : IrreducibleCharacter ↥((derivedInG M).subgroupOf M) =>
          (θ : ClassFunction ↥((derivedInG M).subgroupOf M) ℂ) 1 = 1).erase
        (trivialIrreducibleCharacter ↥((derivedInG M).subgroupOf M)) := by
    ext θ
    simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [herase, Finset.card_erase_of_mem htriv,
    Nat.sub_add_cancel (Finset.card_pos.mpr ⟨_, htriv⟩)]

open scoped Classical FiniteInduce in
/-- **Peterfalvi (11.8.1), `|S(HC)| = n` — the arithmetic reduction** (sorry-free).  Given the
abelianization order `|M'{}^{ab}| = |M'/M''| = d`, the count `|S(HC)| = n` follows purely from the
orbit count `|M'{}^{ab}| = w₁·|S(HC)| + 1`
(`card_abelianization_derived_eq_w1_mul_card_SHCSet_add_one`) and the index relation
`n·w₁ = d − δ = d − 1` (`n_formula` at `δ = 1`): `w₁·|S(HC)| = d − 1 = n·w₁`, so `|S(HC)| = n`. -/
theorem Hypothesis.card_SHCSet_filter_eq_charParam_n_of_card_abelianization_eq [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    (params : CharacterParameters hyp) (hdelta : params.delta = 1)
    (hab : Nat.card (Abelianization ↥((derivedInG M).subgroupOf M)) = params.d) :
    (Finset.univ.filter (fun χ : IrreducibleCharacter ↥M =>
      (χ : ClassFunction ↥M ℂ) ∈ inducedFamily M ∧
        ((χ : ClassFunction ↥M ℂ) : ↥M → ℂ) 1 = (hyp.w1 : ℂ))).card = params.n := by
  have := hyp.finiteG
  classical
  -- `d = w₁·|S(HC)| + 1`
  have horbit := hyp.card_abelianization_derived_eq_w1_mul_card_SHCSet_add_one hG
  rw [hab] at horbit
  -- `n·w₁ = d − 1 = w₁·|S(HC)|`
  have hnw : params.n * hyp.w1
      = hyp.w1 * (Finset.univ.filter fun χ : IrreducibleCharacter ↥M =>
          (χ : ClassFunction ↥M ℂ) ∈ inducedFamily M ∧
            ((χ : ClassFunction ↥M ℂ) : ↥M → ℂ) 1 = (hyp.w1 : ℂ)).card := by
    have h := params.n_formula
    rw [hdelta, horbit] at h
    have : (params.n * hyp.w1 : ℤ)
        = (hyp.w1 * (Finset.univ.filter fun χ : IrreducibleCharacter ↥M =>
            (χ : ClassFunction ↥M ℂ) ∈ inducedFamily M ∧
              ((χ : ClassFunction ↥M ℂ) : ↥M → ℂ) 1 = (hyp.w1 : ℂ)).card : ℤ) := by
      push_cast at h ⊢
      linarith
    exact_mod_cast this
  have hw1pos : 0 < hyp.w1 := Nat.pos_of_ne_zero (NeZero.ne hyp.w1)
  rw [mul_comm hyp.w1] at hnw
  exact (Nat.eq_of_mul_eq_mul_right hw1pos hnw).symm

/-- **Structural index identity for the (11.8.1) count**: `|M'|·|C| = |HC|·|U|`, where
`C = U ⊓ C_G(H)` and `HC = H ⊔ C`.  Since `M' = H ⋊ U` (`derived_complement`; `H ⊴ M'`,
`H ⊓ U = ⊥`) we have `|M'| = |H|·|U|`, and `HC = H ⋊ C` (`C ≤ U`, same disjointness) gives
`|HC| = |H|·|C|`.  Rearranged this is `[M' : HC] = [U : C]` — the structural half of
`|M'/M''| = |U/C|` (with (11.5) `M'' = HC`) feeding the count. -/
theorem typePData_card_derived_mul_card_C_eq [Finite G] {M : Subgroup G} (data : TypePData M) :
    Nat.card ↥(derivedInG M)
      * Nat.card ↥(data.U ⊓ Subgroup.centralizer (data.H : Set G))
      = Nat.card ↥(data.H ⊔ (data.U ⊓ Subgroup.centralizer (data.H : Set G)))
        * Nat.card ↥data.U := by
  classical
  set C := data.U ⊓ Subgroup.centralizer (data.H : Set G) with hCdef
  have hCleU : C ≤ data.U := inf_le_left
  have hHleM' : data.H ≤ derivedInG M := data.H_le
  have hCleM' : C ≤ derivedInG M := hCleU.trans data.U_le
  have hM'leM : derivedInG M ≤ M := Subgroup.map_subtype_le _
  -- `H ⊓ U = ⊥` from the complement `M' = H ⋊ U`
  have hHUbot : data.H ⊓ data.U = ⊥ := by
    have hd : (data.H ⊓ data.U).subgroupOf (derivedInG M) = ⊥ := by
      have h1 : (data.H ⊓ data.U).subgroupOf (derivedInG M)
          = data.H.subgroupOf (derivedInG M) ⊓ data.U.subgroupOf (derivedInG M) :=
        Subgroup.comap_inf _ _ _
      rw [h1]; exact disjoint_iff.mp data.derived_complement.disjoint
    have hle : data.H ⊓ data.U ≤ derivedInG M := inf_le_left.trans data.H_le
    rw [Subgroup.subgroupOf_eq_bot, disjoint_iff, inf_of_le_left hle] at hd
    exact hd
  -- `C ⊓ H = ⊥`
  have hCHbot : C ⊓ data.H = ⊥ := by
    refine le_bot_iff.mp ?_
    calc C ⊓ data.H ≤ data.U ⊓ data.H := inf_le_inf_right _ hCleU
      _ = data.H ⊓ data.U := inf_comm _ _
      _ = ⊥ := hHUbot
  -- `|M'| = |H|·|U|`
  have hHU : Nat.card ↥data.H * Nat.card ↥data.U = Nat.card ↥(derivedInG M) := by
    have h := data.derived_complement.card_mul_card
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe data.H_le).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe data.U_le).toEquiv] at h
  -- `H ⊴ M'`
  have hHn : (data.H.subgroupOf (derivedInG M)).Normal := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer data.H_le).mpr ?_
    have hnM : M ≤ Subgroup.normalizer (data.H : Set G) := by
      rw [data.H_eq]; exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer M
    exact hM'leM.trans hnM
  -- `|HC| = |H|·|C|`, via disjoint-normal card in `↥M'`
  have hHC : Nat.card ↥(data.H ⊔ C) = Nat.card ↥data.H * Nat.card ↥C := by
    have hdisj : C.subgroupOf (derivedInG M) ⊓ data.H.subgroupOf (derivedInG M) = ⊥ := by
      have h1 : (C ⊓ data.H).subgroupOf (derivedInG M)
          = C.subgroupOf (derivedInG M) ⊓ data.H.subgroupOf (derivedInG M) :=
        Subgroup.comap_inf _ _ _
      rw [← h1, hCHbot, Subgroup.bot_subgroupOf]
    have hcard := OddOrder.BG.Ch1.S01.card_sup_eq_card_mul_card_of_disjoint_normal
      (T := C.subgroupOf (derivedInG M)) (M := data.H.subgroupOf (derivedInG M)) hdisj
    rw [← Subgroup.subgroupOf_sup hCleM' hHleM',
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (sup_le hCleM' hHleM')).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCleM').toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHleM').toEquiv, sup_comm] at hcard
    rw [hcard, Nat.mul_comm]
  rw [← hHU, hHC]
  ring

/-- **Structural core of the (11.8.1) count `|M'/M''| = |U : C|`** (`C = U ⊓ C_G(H)`).  Given the
(11.5) identity `M'' = HC` — supplied here in the `TypePData`-expressible form
`secondDerivedInAmbient M = H ⊔ C` — the abelianization order `|M'{}^{ab}| = |M' : M''|` equals the
relative index `|U : C|`.

Three steps, all sorry-free group theory: (1) `|M'{}^{ab}| = |M'{}^{ab}|` transports along
`M' = (derivedInG M).subgroupOf M ≃* derivedInG M` (`MulEquiv.abelianizationCongr`); (2)
`|(derivedInG M){}^{ab}| = |M' : M''|` because `Abelianization = quotient by the commutator` and
`M''.subgroupOf M' = commutator ↥M'` (`comap_map_eq_self_of_injective`); (3) `|M' : HC| = |U : C|`
by cancelling the common factor `|H|` in the structural card identity `|M'|·|C| = |HC|·|U|`
(`typePData_card_derived_mul_card_C_eq`), mirroring the S13 `HC_relIndex_derived`.

This isolates the *char-free* half of `card_SHCSet_filter_eq_charParam_n`'s remaining input
`|M'{}^{ab}| = d`: with (11.5) discharged it reduces `d = |M'{}^{ab}|` to `|U : C| = u = d`, whose
`|U : C| = u` half is the (11.7) `H₀ = 1` collapse `C_U(H̄) = C` and whose `u = d` half is
`charParam_d_eq_u`. -/
theorem typePData_card_abelianization_derived_eq_relIndex_C [Finite G] {M : Subgroup G}
    (data : TypePData M)
    (hM2 : secondDerivedInAmbient M
      = data.H ⊔ (data.U ⊓ Subgroup.centralizer (data.H : Set G))) :
    Nat.card (Abelianization ↥((derivedInG M).subgroupOf M))
      = (data.U ⊓ Subgroup.centralizer (data.H : Set G)).relIndex data.U := by
  classical
  set C := data.U ⊓ Subgroup.centralizer (data.H : Set G) with hCdef
  set HC := data.H ⊔ C with hHCdef
  have hCleU : C ≤ data.U := inf_le_left
  have hHCleM' : HC ≤ derivedInG M := sup_le data.H_le (hCleU.trans data.U_le)
  -- (1) transport the abelianization along `↥(M'.subgroupOf M) ≃* ↥M'`
  have hiso : Nat.card (Abelianization ↥((derivedInG M).subgroupOf M))
      = Nat.card (Abelianization ↥(derivedInG M)) :=
    Nat.card_congr (MulEquiv.abelianizationCongr
      (Subgroup.subgroupOfEquivOfLe (Subgroup.map_subtype_le _))).toEquiv
  -- (2) `M''.subgroupOf M' = commutator ↥M'`, so `|M'{}^{ab}| = |M' : M''|`
  have hcomm : (secondDerivedInAmbient M).subgroupOf (derivedInG M)
      = commutator ↥(derivedInG M) := by
    have hdef : secondDerivedInAmbient M
        = (commutator ↥(derivedInG M)).map (derivedInG M).subtype := rfl
    rw [hdef, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective (derivedInG M).subtype_injective]
  have hab : Nat.card (Abelianization ↥(derivedInG M))
      = (secondDerivedInAmbient M).relIndex (derivedInG M) := by
    rw [Subgroup.relIndex, hcomm]; rfl
  -- (3) `|M' : HC| = |U : C|` by cancelling `|H|·|C|` in `|M'|·|C| = |HC|·|U|`
  have h1 : Nat.card ↥HC * HC.relIndex (derivedInG M) = Nat.card ↥(derivedInG M) := by
    have := Subgroup.card_mul_index (HC.subgroupOf (derivedInG M))
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHCleM').toEquiv] at this
  have h2 : Nat.card ↥C * C.relIndex data.U = Nat.card ↥data.U := by
    have := Subgroup.card_mul_index (C.subgroupOf data.U)
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCleU).toEquiv] at this
  have hcardid : Nat.card ↥(derivedInG M) * Nat.card ↥C = Nat.card ↥HC * Nat.card ↥data.U := by
    have h := typePData_card_derived_mul_card_C_eq data
    rw [← hCdef, ← hHCdef] at h
    exact h
  have hkey : Nat.card ↥HC * Nat.card ↥C * HC.relIndex (derivedInG M)
      = Nat.card ↥HC * Nat.card ↥C * C.relIndex data.U := by
    calc Nat.card ↥HC * Nat.card ↥C * HC.relIndex (derivedInG M)
        = Nat.card ↥C * (Nat.card ↥HC * HC.relIndex (derivedInG M)) := by ring
      _ = Nat.card ↥C * Nat.card ↥(derivedInG M) := by rw [h1]
      _ = Nat.card ↥(derivedInG M) * Nat.card ↥C := by ring
      _ = Nat.card ↥HC * Nat.card ↥data.U := hcardid
      _ = Nat.card ↥HC * (Nat.card ↥C * C.relIndex data.U) := by rw [h2]
      _ = Nat.card ↥HC * Nat.card ↥C * C.relIndex data.U := by ring
  have hpos : 0 < Nat.card ↥HC * Nat.card ↥C := Nat.mul_pos Nat.card_pos Nat.card_pos
  rw [hiso, hab, hM2]
  exact Nat.eq_of_mul_eq_mul_left hpos hkey

open OddOrder.Peterfalvi.S11 in
/-- **Peterfalvi (11.8.1), the abelianization order `|M'{}^{ab}| = d`** — the assembled
`|M'/M''| = d`
input to the `|S(HC)| = n` count, given the two structural facts of (11.5)/(11.7): `M'' = HC`
(`hM2`, i.e. `secondDerivedInAmbient M = H ⊔ C`) and `H₀ = 1` (`hN`, i.e. `chief.N = ⊥`).

Chains the three sorry-free pieces: `|M'{}^{ab}| = |U : C|`
(`typePData_card_abelianization_derived_eq_relIndex_C`, given `M'' = HC`), `|U : C| = u`
(`u_eq_relIndex_C`, given `H₀ = 1`), and `u = d` (`charParam_d_eq_u`).  The two hypotheses are
Peterfalvi (11.5) `secondDerived_eq_HC` and (11.7) `H_elementaryAbelian` — proven in `S13`
(downstream of this file), so `card_SHCSet_filter_eq_charParam_n` (below) discharges its
`|M'/M''| = d` obligation by threading them from the `FeitThompson` layer where `S13` is
available. -/
theorem Hypothesis.card_abelianization_derived_eq_charParam_d [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    (htype : IsTypeIII M ∨ IsTypeIV M)
    (params : CharacterParameters hyp) (hmu : params.mu = hyp.muGrid hG hG.odd)
    (hnt : OddOrder.GroupTheory.TypePNontrivialCore M hyp.typeP)
    (chief : ChiefFactorData (hyp.toTypesIIIIIIVSetup htype hnt))
    (hM2 : secondDerivedInAmbient M
      = hyp.typeP.H ⊔ (hyp.typeP.U ⊓ Subgroup.centralizer (hyp.typeP.H : Set G)))
    (hN : chief.N = ⊥) :
    Nat.card (Abelianization ↥((derivedInG M).subgroupOf M)) = params.d := by
  have h1 : Nat.card (Abelianization ↥((derivedInG M).subgroupOf M))
      = (hyp.typeP.U ⊓ Subgroup.centralizer (hyp.typeP.H : Set G)).relIndex hyp.typeP.U :=
    typePData_card_abelianization_derived_eq_relIndex_C hyp.typeP hM2
  have h2 : (hyp.mkSection11CharacterData (hyp.toTypesIIIIIIVSetup htype hnt) chief).u
      = (hyp.typeP.U ⊓ Subgroup.centralizer (hyp.typeP.H : Set G)).relIndex hyp.typeP.U :=
    hyp.u_eq_relIndex_C (hyp.toTypesIIIIIIVSetup htype hnt) chief hN
  have h3 : params.d = (hyp.mkSection11CharacterData (hyp.toTypesIIIIIIVSetup htype hnt) chief).u :=
    hyp.charParam_d_eq_u hG htype params hmu hnt chief
  rw [h1, ← h2, h3]

open scoped Classical FiniteInduce in
/-- **Peterfalvi (11.8.1), `|S(HC)| = n`** (§9 count, named obligation).  The number of degree-`w₁`
irreducible members of `S = inducedFamily M` equals `n = (d − δ)/w₁ = (d − 1)/w₁`.  `S(HC) = S₁`
consists of the `(u − 1)/q` degree-`q = w₁` irreducible constituents of the constant-degree
Frobenius
family `(U/C) ⋊ W₁`, so `|S(HC)| = (u − 1)/q = (d − 1)/w₁ = n` by (11.8.1).  This is the cardinality
matching the isometric coherent image (`exists_coherentImage_SHC`, `|R| = |S(HC)|`) to `n`.

The orbit count `|M'{}^{ab}| = w₁·|S(HC)| + 1` and the `n·w₁ = d − 1` arithmetic are discharged by
`card_SHCSet_filter_eq_charParam_n_of_card_abelianization_eq` (sorry-free); the remaining
`|M'/M''| = d` input is assembled by `card_abelianization_derived_eq_charParam_d` from the two
(11.5)/
(11.7) structural facts threaded here: `hM2` (`M'' = HC`, Peterfalvi (11.5)
`S13.secondDerived_eq_HC`)
and `hHcard` (`|H| = |W₂|^{|W₁|} = p^q`, Peterfalvi (11.7)/(13.2.b) `S13.H_elementaryAbelian`),
which
force any chief kernel `N ◁ H` to be trivial (`H/N` has order `p^q = |H|`, so `|N| = 1`).  Both are
`params`-free and expressed in the §12 `Hypothesis`; they are discharged at the `FeitThompson` layer
(where `S13` is available).  See `notes/peterfalvi/s13_11_8_orthogonality.md`. -/
theorem Hypothesis.card_SHCSet_filter_eq_charParam_n [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    (htype : IsTypeIII M ∨ IsTypeIV M)
    (params : CharacterParameters hyp) (hmu : params.mu = hyp.muGrid hG hG.odd)
    (hδpm : params.delta = 1 ∨ params.delta = -1)
    (hM2 : secondDerivedInAmbient M
      = hyp.typeP.H ⊔ (hyp.typeP.U ⊓ Subgroup.centralizer (hyp.typeP.H : Set G)))
    (hHcard : Nat.card ↥hyp.typeP.H = hyp.w2 ^ hyp.w1) :
    (Finset.univ.filter (fun χ : IrreducibleCharacter ↥M =>
      (χ : ClassFunction ↥M ℂ) ∈ inducedFamily M ∧
        ((χ : ClassFunction ↥M ℂ) : ↥M → ℂ) 1 = (hyp.w1 : ℂ))).card = params.n := by
  have := hyp.finiteG
  classical
  refine hyp.card_SHCSet_filter_eq_charParam_n_of_card_abelianization_eq hG params
    (hyp.charParam_delta_eq_one hG htype params hmu hδpm) ?_
  -- **The remaining (11.5)/(11.7) gate**: `|M'/M''| = u = d`.  Obtain the §11 chief factor on
  -- `M`, prove its kernel `N = ⊥` from `|H| = |W₂|^{|W₁|}` (any proper chief kernel would make
  -- `|H/N| < |H|`), then assemble `|M'{}^{ab}| = d` via
  -- `card_abelianization_derived_eq_charParam_d`.
  have hnt : TypePNontrivialCore M hyp.typeP :=
    typePNontrivialCore_of_isTypeIIIorIV htype hyp.typeP
  obtain ⟨chief, -⟩ := OddOrder.Peterfalvi.S11.exists_chiefFactorData hG
    (hyp.toTypesIIIIIIVSetup htype hnt)
  -- `chief.N = ⊥`: `|H/N| = chief.p ^ q = |W₂|^q = |H|`, so `|N| = 1`.
  have hN : chief.N = ⊥ := by
    have := chief.N_normal
    -- `chief.p = |W₂| = w₂` for type III/IV.
    have hpW2 : chief.p = hyp.w2 := (chief.typeIII_IV_p_eq_W2 htype).symm
    -- `data.H = H` and `data.q = w₁` hold by `rfl` through the `TypesIIIIIIVSetup` projections.
    have hHcard' : Nat.card ↥(hyp.toTypesIIIIIIVSetup htype hnt).typeP.H = hyp.w2 ^ hyp.w1 :=
      hHcard
    have hq : (hyp.toTypesIIIIIIVSetup htype hnt).q = hyp.w1 := rfl
    have hquot : Nat.card (↥(hyp.toTypesIIIIIIVSetup htype hnt).typeP.H ⧸ chief.N)
        = hyp.w2 ^ hyp.w1 := by
      rw [OddOrder.Peterfalvi.S11.chiefFactor_quotient_card chief, hpW2, hq]
    have hsplit := Subgroup.card_eq_card_quotient_mul_card_subgroup chief.N
    rw [hquot, hHcard'] at hsplit
    have hN1 : Nat.card ↥chief.N = 1 := by
      have hpos : 0 < hyp.w2 ^ hyp.w1 := hHcard' ▸ Nat.card_pos
      nlinarith [Nat.card_pos (α := ↥chief.N), hsplit, hpos]
    exact Subgroup.card_eq_one.mp hN1
  exact hyp.card_abelianization_derived_eq_charParam_d hG htype params hmu hnt chief hM2 hN

open scoped FiniteInduce in
/-- **The `Fin w₂`-indexed `W₂`-dual character of the §10 μ-grid**: column `j` of `muGrid` is the
§6 `columnFamily` at this character (`muGrid_columnSum_eq_columnSum`).  Extracted from the `muGrid`
definition (the `finCardEquivCharacterGroup`-reindex of `j`) so the §6 ↔ §10 column identification
can be *stated*. -/
noncomputable def Hypothesis.muColumnChar [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hyp : Hypothesis M) (hodd : Odd (Nat.card G)) (j : Fin hyp.w2) :
    ((hyp.toHypothesis46 hG hodd).W2.subgroupOf
      ((hyp.toHypothesis46 hG hodd).W1 ⊔ (hyp.toHypothesis46 hG hodd).W2)) →* ℂˣ := by
  haveI := hyp.finiteG
  classical
  let h := (hyp.toCertainTypeHypothesis hG hodd).toHypothesis
  haveI : IsCyclic ↥(h.W1 ⊔ h.W2) := h.isCyclic_sup
  letI : CommGroup ↥(h.W1 ⊔ h.W2) := IsCyclic.commGroup
  have hW2le : hyp.typeP.W2 ≤ M := typePData_W2_le_self hyp.typeP
  have hcardW2sub : Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2)) = hyp.w2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right)).toEquiv]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW2le).toEquiv
  haveI : NeZero (Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2))) := ⟨Nat.card_pos.ne'⟩
  exact finCardEquivCharacterGroup _ (finCongr hcardW2sub.symm j)

open scoped FiniteInduce in
/-- **A nontrivial μ-grid column has a nontrivial `W₂`-dual**: `muColumnChar j ≠ 1` for `j ≠ 0`.
The Pontryagin reindex `finCardEquivCharacterGroup` is normalized to send `0` to the trivial
character (`finCardEquivCharacterGroup_zero`), so by injectivity a nonzero column index gives a
nontrivial dual.  This is the `χ₂ ≠ 1` input of `columnSum_mem_certainTypeSet` for the μ-grid
column sums. -/
theorem Hypothesis.muColumnChar_ne_one [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hyp : Hypothesis M) (hodd : Odd (Nat.card G))
    {j : Fin hyp.w2} (hj : j ≠ 0) :
    hyp.muColumnChar hG hodd j ≠ 1 := by
  have := hyp.finiteG
  classical
  -- rebuild the `muColumnChar` definition chain (instance-defeq trap §5)
  set h := (hyp.toCertainTypeHypothesis hG hodd).toHypothesis with hhdef
  have : IsCyclic ↥(h.W1 ⊔ h.W2) := h.isCyclic_sup
  let : CommGroup ↥(h.W1 ⊔ h.W2) := IsCyclic.commGroup
  have hW2le : hyp.typeP.W2 ≤ M := typePData_W2_le_self hyp.typeP
  have hcardW2sub : Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2)) = hyp.w2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right)).toEquiv]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW2le).toEquiv
  have : NeZero (Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2))) := ⟨Nat.card_pos.ne'⟩
  set χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ :=
    finCardEquivCharacterGroup _ (finCongr hcardW2sub.symm j) with hχ₂def
  have hchar : hyp.muColumnChar hG hodd j = χ₂ := by
    unfold Hypothesis.muColumnChar
    rfl
  rw [hchar, hχ₂def]
  intro heq
  -- `1 = fCECG 0`, so injectivity forces `finCongr … j = 0`, i.e. `j = 0`
  have heq' : finCardEquivCharacterGroup _ (finCongr hcardW2sub.symm j)
      = finCardEquivCharacterGroup (↥(h.W2.subgroupOf (h.W1 ⊔ h.W2))) 0 := by
    rw [finCardEquivCharacterGroup_zero]
    exact heq
  have hj0 : finCongr hcardW2sub.symm j = 0 :=
    (finCardEquivCharacterGroup _).injective heq'
  apply hj
  ext
  simpa using congrArg Fin.val hj0

open scoped FiniteInduce in
/-- **§10 μ-grid column sum = §6 certain-type column sum** (the world-joining identification):
`∑ᵢ muGrid i j = columnSum (toHypothesis46 …) (muColumnChar j)`.  Both sides enumerate the same
§6 `columnFamily` column — `muGrid` through the `finCongr` row-reindex (a bijection, so
`Equiv.sum_comp` collapses the sum), `columnSum` directly.  Through this equation the
`certainTypeSet` coherence (`certainTypeSet_isCoherent_A0`) applies to the μ-grid column sums
named by `reducible_mem_inducedKernelFamily_eq_muGrid_columnSum`. -/
theorem Hypothesis.muGrid_columnSum_eq_columnSum [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    (hodd : Odd (Nat.card G))
    [NeZero (Nat.card (hyp.toHypothesis46 hG hodd).W1)]
    (j : Fin hyp.w2) :
    (∑ i : Fin hyp.w1, hyp.muGrid hG hodd i j)
      = OddOrder.Peterfalvi.S06.columnSum (hyp.toHypothesis46 hG hodd)
          (hyp.muColumnChar hG hodd j) := by
  have := hyp.finiteG
  classical
  -- rebuild the very `let`/`have` chain of the `muGrid`/`muColumnChar` definitions, so the
  -- entrywise `unfold …; rfl` identifications fire against syntactically matching variables
  set h := (hyp.toCertainTypeHypothesis hG hodd).toHypothesis with hhdef
  have : NeZero (Nat.card h.W1) := ⟨by have := h.one_lt_card_W1; omega⟩
  have : IsCyclic ↥(h.W1 ⊔ h.W2) := h.isCyclic_sup
  let : CommGroup ↥(h.W1 ⊔ h.W2) := IsCyclic.commGroup
  have hW1le : hyp.typeP.W1 ≤ M := hyp.typeP.W1_le
  have hW2le : hyp.typeP.W2 ≤ M := typePData_W2_le_self hyp.typeP
  have hcardW1 : Nat.card ↥h.W1 = hyp.w1 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW1le).toEquiv
  have hcardW2sub : Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2)) = hyp.w2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right)).toEquiv]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW2le).toEquiv
  have : NeZero (Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2))) := ⟨Nat.card_pos.ne'⟩
  set χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ :=
    finCardEquivCharacterGroup _ (finCongr hcardW2sub.symm j) with hχ₂def
  -- entrywise: `muGrid i j = (h.columnFamily χ₂).mu (finCongr … i)`
  have hstep1 : (∑ i : Fin hyp.w1, hyp.muGrid hG hodd i j)
      = ∑ i' : Fin (Nat.card ↥h.W1), ((h.columnFamily χ₂).mu i' : ClassFunction ↥M ℂ) := by
    rw [← Equiv.sum_comp (finCongr hcardW1.symm)
      (fun i' => ((h.columnFamily χ₂).mu i' : ClassFunction ↥M ℂ))]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    show hyp.muGrid hG hodd i j
      = ((h.columnFamily χ₂).mu ((finCongr hcardW1.symm) i) : ClassFunction ↥M ℂ)
    unfold Hypothesis.muGrid
    rfl
  -- the extracted dual character is the same `χ₂`
  have hchar : hyp.muColumnChar hG hodd j = χ₂ := by
    unfold Hypothesis.muColumnChar
    rfl
  rw [hstep1, OddOrder.Peterfalvi.S06.columnSum_def, hchar]
  with_unfolding_all rfl

end OddOrder.Peterfalvi.S12


