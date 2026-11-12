-- Prove2me | Definitions.Def_OddOrder_BG_Ch1_Preliminary_OperatorMaschke
-- name    : OddOrder_BG_Ch1_Preliminary_OperatorMaschke
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T05:26:05.208179+00:00
-- url     : https://prove2.me/theorems/c4ae4ba7-deef-4454-b390-3ff1294fe256
-- title:
--   Bender–Glauberman §4: Maschke $A$-invariant complement bridge
-- statement:
--   Supports Bender–Glauberman §4 (pp. 38–41), Theorem 4.12(a) (Huppert) step a-3 and Theorem 4.16 (Blackburn) Case B-2. An operator group $A$ acts on a quotient $R/S$ by an $A$-invariant normal subgroup $S$; the section $\Omega_1(R/S)$ is an elementary abelian $p$-group, hence an $\mathbb{F}_p$-vector space, and since $(|A|,|R|)=1$, Maschke's theorem splits off an $A$-invariant complement.
--
--   Main definitions: `isAInvariant_map_mk'` and `isAInvariant_comap_mk'` (invariance of images and preimages under the quotient map), `mulAutToEnd` (a `MulAut`-action on a commutative $p$-group as a monoid homomorphism into endomorphisms), and `exists_aInvariant_complement_in_omega1_quotient` (the Maschke bridge).
--
--   The bundle also proves 7 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/Ch1_Preliminary/OperatorMaschke.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/BG/Ch1_Preliminary/OperatorMaschke.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_Main_CommutatorBasics
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_Main_ThreeSubgroupsCoprime
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_Main_BaerTrick
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_Main_ChainNilpotent
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_ForwardFromCh03
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_Main_ThreeSubgroups
import Definitions.Def_OddOrder_GroupTheory_PRank
import Definitions.Def_OddOrder_GroupTheory_OmegaSubgroup
import Definitions.Def_OddOrder_GroupTheory_ElementaryAbelian
import Mathlib.RepresentationTheory.Maschke
import Mathlib.RepresentationTheory.Submodule
import Mathlib.RepresentationTheory.Subrepresentation
import Mathlib.Algebra.Module.ZMod

open scoped IsMulCommutative

namespace OddOrder.BG.Ch1_Preliminary

open OddOrder.GroupTheory OddOrder.Isaacs.Ch03 OddOrder.Isaacs.Ch04

variable {p : ℕ}

/-- In an abelian group, every element of `Ω₁` has `p`-th power `1`.

For abelian `Q` the set `{g | gᵖ = 1}` is already a subgroup, so the closure `Ω₁(Q)` adds
nothing; we prove it directly by closure induction using commutativity for the product case. -/
theorem pow_eq_one_of_mem_omega_one_of_comm {Q : Type*} [Group Q]
    (hQ : ∀ x y : Q, x * y = y * x) {g : Q} (hg : g ∈ Omega Q p 1) : g ^ p = 1 := by
  induction hg using Subgroup.closure_induction with
  | mem x hx => simpa only [Set.mem_ofPred_eq, pow_one] using hx
  | one => exact one_pow p
  | mul a b _ _ ha hb =>
      have hab : Commute a b := hQ a b
      rw [hab.mul_pow, ha, hb, mul_one]
  | inv a _ ha => rw [inv_pow, ha, inv_one]

/-- **M-a-1**: `Ω₁` of an abelian `p`-group is elementary abelian.

`Ω₁(Q) = ⟨ g : gᵖ = 1 ⟩`; commutativity comes from `Q` abelian and every element has order
dividing `p` by `pow_eq_one_of_mem_omega_one_of_comm`. -/
theorem isElementaryAbelian_omega_one_of_comm {Q : Type*} [Group Q]
    (hQ : ∀ x y : Q, x * y = y * x) :
    IsElementaryAbelian p ↥(Omega Q p 1) := by
  refine ⟨fun x y => ?_, fun x => ?_⟩
  · exact Subtype.ext (hQ x.val y.val)
  · refine Subtype.ext ?_
    rw [Subgroup.coe_pow, OneMemClass.coe_one]
    exact pow_eq_one_of_mem_omega_one_of_comm hQ x.property

/-- **M-e-1**: from `(nA, nR)` coprime and `p ∣ nR` we get `(nA : ZMod p) ≠ 0`, the
`NeZero` instance Maschke needs (`p ∤ |A|` because `p ∣ |R|` and `gcd = 1`). -/
theorem neZero_natCast_zmod_of_coprime {p nA nR : ℕ} [Fact p.Prime]
    (hcop : Nat.Coprime nA nR) (hpR : p ∣ nR) : NeZero ((nA : ZMod p)) := by
  refine ⟨?_⟩
  rw [Ne, CharP.cast_eq_zero_iff (ZMod p) p]
  intro hpA
  have hp1 : p ∣ 1 := hcop ▸ Nat.dvd_gcd hpA hpR
  exact (Fact.out : p.Prime).ne_one (Nat.dvd_one.mp hp1)

variable {R : Type*} [Group R] {A : Type*} [Group A] {φ : A →* MulAut R}

open OddOrder.Isaacs.Ch03.IsAInvariant
  (quotientMulAutHom quotientMulAutHom_apply_mk') in
/-- An `A`-invariant subgroup maps to an `A`-invariant subgroup under the quotient action
`φ̄ = quotientMulAutHom hS`. -/
theorem isAInvariant_map_mk' {S : Subgroup R} [S.Normal] (hS : IsAInvariant φ S)
    {H : Subgroup R} (hH : IsAInvariant φ H) :
    IsAInvariant (quotientMulAutHom hS) (H.map (QuotientGroup.mk' S)) := by
  rw [isAInvariant_iff_smul_mem]
  intro a q hq
  rw [Subgroup.mem_map] at hq ⊢
  obtain ⟨g, hg, rfl⟩ := hq
  exact ⟨(φ a) g, hH.smul_mem a hg, by rw [quotientMulAutHom_apply_mk']⟩

open OddOrder.Isaacs.Ch03.IsAInvariant
  (quotientMulAutHom quotientMulAutHom_apply_mk') in
/-- The preimage under `mk' S` of a `φ̄`-invariant subgroup is `φ`-invariant. -/
theorem isAInvariant_comap_mk' {S : Subgroup R} [S.Normal] (hS : IsAInvariant φ S)
    {Y : Subgroup (R ⧸ S)} (hY : IsAInvariant (quotientMulAutHom hS) Y) :
    IsAInvariant φ (Y.comap (QuotientGroup.mk' S)) := by
  rw [isAInvariant_iff_smul_mem]
  intro a r hr
  rw [Subgroup.mem_comap] at hr ⊢
  rw [← quotientMulAutHom_apply_mk']
  exact hY.smul_mem a hr

/-- The restriction to an `A`-invariant `K` of a `φ`-invariant `H` (as `H.subgroupOf K`) is
invariant under the restricted action `hK.restrict`. -/
theorem isAInvariant_subgroupOf_restrict {K : Subgroup R} (hK : IsAInvariant φ K)
    {H : Subgroup R} (hH : IsAInvariant φ H) :
    IsAInvariant hK.restrict (H.subgroupOf K) := by
  rw [isAInvariant_iff_smul_mem]
  intro a h hh
  rw [Subgroup.mem_subgroupOf] at hh ⊢
  rw [IsAInvariant.restrict_apply_val]
  exact hH.smul_mem a hh

/-- A subgroup of `↥K` invariant under `hK.restrict` maps (via `K.subtype`) to a `φ`-invariant
subgroup of `R`. -/
theorem isAInvariant_map_subtype_of_restrict {K : Subgroup R} (hK : IsAInvariant φ K)
    {H : Subgroup ↥K} (hH : IsAInvariant hK.restrict H) :
    IsAInvariant φ (H.map K.subtype) := by
  rw [isAInvariant_iff_smul_mem]
  intro a q hq
  rw [Subgroup.mem_map] at hq ⊢
  obtain ⟨h, hh, rfl⟩ := hq
  exact ⟨(hK.restrict a) h, hH.smul_mem a hh, IsAInvariant.restrict_apply_val hK a h⟩

/-- A `MulAut`-action on a commutative `p`-group `W`, packaged as a monoid hom into the
`F_p`-linear endomorphisms of `Additive W`. Composing with `φ : A →* MulAut W` yields a
`Representation (ZMod p) A (Additive W)`.

**共有版** — BG §3/§4, App.A, Peterfalvi §16 と補章がここを使う。⚠ 新設しないこと:
2026-08-08 に `AppA_PStability` の private 複製を本定義に寄せ、さらに `PRank` に 3 つ目を
足しかけて `ExtraspecialSinger` の名前解決を壊した (引数順が `(W) (p)` と `(p) {W}` で
違うため型エラーとして露見)。スカラー倍を冪に読み替えるのは
`OddOrder.GroupTheory.zmod_smul_ofMul` (`CommGroupAut`)。 -/
noncomputable def mulAutToEnd (W : Type*) [Group W] [IsMulCommutative W] (p : ℕ)
    [Module (ZMod p) (Additive W)] :
    MulAut W →* Module.End (ZMod p) (Additive W) where
  toFun φ := ((MulEquiv.toAdditive φ).toLinearEquiv
      (fun c x => ZMod.map_smul (MulEquiv.toAdditive φ).toAddMonoidHom c x)).toLinearMap
  map_one' := by ext x; rfl
  map_mul' φ ψ := by ext x; rfl

open OddOrder.Isaacs.Ch03.IsAInvariant (quotientMulAutHom) in
/-- **N-4 Maschke bridge** (BG §4; supports Thm 4.12(a) step a-3 and Thm 4.16 Case B-2).

Let `φ : A →* MulAut R` with `(|A|, |R|)` coprime, `p` prime with `p ∣ |R|`, `S` an
`A`-invariant normal subgroup with **abelian** quotient `R ⧸ S`. For any `A`-invariant
`W₀ ≤ R` whose image in `R ⧸ S` lies in `Ω₁(R ⧸ S)`, there is an `A`-invariant `X` with
`S ≤ X` whose image `X ⧸ S` is an `A`-invariant **complement** of `W₀ ⧸ S` inside
`Ω₁(R ⧸ S)` (`⊓ = ⊥`, `⊔ = Ω₁`).

`Ω₁(R ⧸ S)` is an `F_p`-vector space and `A` acts on it coprimely, so Maschke's theorem
(`MonoidAlgebra.Submodule.exists_isCompl`) splits it. -/
theorem exists_aInvariant_complement_in_omega1_quotient
    {R : Type*} [Group R] [Finite R] {p : ℕ} [Fact p.Prime] (hpR : p ∣ Nat.card R)
    {A : Type*} [Group A] [Finite A] {φ : A →* MulAut R}
    (hcop : Nat.Coprime (Nat.card A) (Nat.card R))
    {S : Subgroup R} [S.Normal] (hS : IsAInvariant φ S)
    (hQab : ∀ x y : R ⧸ S, x * y = y * x)
    {W₀ : Subgroup R} (hWinv : IsAInvariant φ W₀)
    (hWΩ : W₀.map (QuotientGroup.mk' S) ≤ Omega (R ⧸ S) p 1) :
    ∃ X : Subgroup R, S ≤ X ∧ IsAInvariant φ X ∧
      X.map (QuotientGroup.mk' S) ≤ Omega (R ⧸ S) p 1 ∧
      X.map (QuotientGroup.mk' S) ⊓ W₀.map (QuotientGroup.mk' S) = ⊥ ∧
      X.map (QuotientGroup.mk' S) ⊔ W₀.map (QuotientGroup.mk' S) = Omega (R ⧸ S) p 1 := by
  classical
  -- `E := Ω₁(R ⧸ S)` is elementary abelian, hence an `F_p`-module on `Additive ↥E`.
  have hEea : IsElementaryAbelian p ↥(Omega (R ⧸ S) p 1) :=
    isElementaryAbelian_omega_one_of_comm hQab
  have hEcomm : IsMulCommutative ↥(Omega (R ⧸ S) p 1) := ⟨⟨fun a b => hEea.comm a b⟩⟩
  have hpsmul : ∀ x : Additive ↥(Omega (R ⧸ S) p 1), (p : ℕ) • x = 0 := by
    intro x
    apply Additive.toMul.injective
    rw [toMul_nsmul, toMul_zero]
    exact hEea.pow_eq_one x.toMul
  have : Module (ZMod p) (Additive ↥(Omega (R ⧸ S) p 1)) := AddCommGroup.zmodModule hpsmul
  have : NeZero ((Nat.card A : ZMod p)) := neZero_natCast_zmod_of_coprime hcop hpR
  have hEinv : IsAInvariant (quotientMulAutHom hS) (Omega (R ⧸ S) p 1) :=
    IsAInvariant.of_characteristic _
  -- the `F_p[A]`-representation `ρ` carried by the restricted quotient action.
  set ρ : Representation (ZMod p) A (Additive ↥(Omega (R ⧸ S) p 1)) :=
    (mulAutToEnd ↥(Omega (R ⧸ S) p 1) p).comp hEinv.restrict with hρ_def
  have key_rho : ∀ (a : A) (v : Additive ↥(Omega (R ⧸ S) p 1)),
      Additive.toMul (ρ a v) = (hEinv.restrict a) (Additive.toMul v) := fun _ _ => rfl
  -- `W' = W₀ ⧸ S` as a subgroup of `↥E`, and its invariance.
  set W' := W₀.map (QuotientGroup.mk' S) with hW'_def
  have hW'inv : IsAInvariant (quotientMulAutHom hS) W' := isAInvariant_map_mk' hS hWinv
  set pWg : Subgroup ↥(Omega (R ⧸ S) p 1) := W'.subgroupOf (Omega (R ⧸ S) p 1) with hpWg_def
  have hpWg : IsAInvariant hEinv.restrict pWg := isAInvariant_subgroupOf_restrict hEinv hW'inv
  -- `W'` as a `ZMod p`-submodule `pW`.
  set pW := AddSubgroup.toZModSubmodule (n := p) (Subgroup.toAddSubgroup pWg) with hpW_def
  have hmem_pW : ∀ v : Additive ↥(Omega (R ⧸ S) p 1), v ∈ pW ↔ Additive.toMul v ∈ pWg := by
    intro v
    simp only [hpW_def, AddSubgroup.mem_toZModSubmodule, Additive.mem_toAddSubgroup]
  have hpW_invt : pW ∈ ρ.invtSubmodule := by
    rw [ρ.mem_invtSubmodule]; intro a
    rw [Module.End.mem_invtSubmodule_iff_forall_mem_of_mem]
    intro v hv
    rw [hmem_pW] at hv ⊢
    rw [key_rho]
    exact hpWg.smul_mem a hv
  -- Maschke: `pW` is a subrepresentation, and the subrepresentation lattice is complemented
  -- (`IsSemisimpleRepresentation`), so `pW` has an invariant complement `qc`.
  have hpW_sub : ∀ (a : A) ⦃v : Additive ↥(Omega (R ⧸ S) p 1)⦄, v ∈ pW → ρ a v ∈ pW := by
    intro a v hv
    have hmem := ρ.mem_invtSubmodule.mp hpW_invt a
    rw [Module.End.mem_invtSubmodule_iff_forall_mem_of_mem] at hmem
    exact hmem v hv
  obtain ⟨qcSub, hcompl⟩ :=
    ComplementedLattice.exists_isCompl (⟨pW, hpW_sub⟩ : Subrepresentation ρ)
  set qc : Submodule (ZMod p) (Additive ↥(Omega (R ⧸ S) p 1)) := qcSub.toSubmodule with hqc_def
  have hqc_invt : qc ∈ ρ.invtSubmodule := by
    rw [ρ.mem_invtSubmodule]; intro a
    rw [Module.End.mem_invtSubmodule_iff_forall_mem_of_mem]
    exact fun v hv => qcSub.apply_mem_toSubmodule a hv
  -- `(⊥/⊤ : Subrepresentation _).toSubmodule = ⊥/⊤` and `(· ⊓/⊔ ·).toSubmodule` reduce by
  -- `rfl`, so the `congrArg` proofs close the goals definitionally.
  have hinf : pW ⊓ qc = ⊥ :=
    congrArg Subrepresentation.toSubmodule hcompl.inf_eq_bot
  have hsup : pW ⊔ qc = ⊤ :=
    congrArg Subrepresentation.toSubmodule hcompl.sup_eq_top
  -- transport `qc` to a subgroup `Hc` of `↥E` via the order-iso `Φ`.
  let Φ : Submodule (ZMod p) (Additive ↥(Omega (R ⧸ S) p 1)) ≃o Subgroup ↥(Omega (R ⧸ S) p 1) :=
    (AddSubgroup.toZModSubmodule (n := p)).symm.trans AddSubgroup.toSubgroup'
  set Hc : Subgroup ↥(Omega (R ⧸ S) p 1) := Φ qc with hHc_def
  have hΦpW : Φ pW = pWg := by
    have h1 : (AddSubgroup.toZModSubmodule (n := p)).symm pW = Subgroup.toAddSubgroup pWg := by
      rw [hpW_def, OrderIso.symm_apply_apply]
    simp only [Φ, OrderIso.trans_apply, h1]
    exact Subgroup.toAddSubgroup.symm_apply_apply pWg
  have hmem_Hc : ∀ h : ↥(Omega (R ⧸ S) p 1), h ∈ Hc ↔ (Additive.ofMul h) ∈ qc := by
    intro h
    rw [hHc_def]
    simp only [Φ, OrderIso.trans_apply, AddSubgroup.mem_toSubgroup',
      AddSubgroup.toZModSubmodule_symm, Submodule.mem_toAddSubgroup]
  -- `Hc` is `A`-invariant (under `hEinv.restrict`).  `(ρ a) (ofMul h) = ofMul ((restrict a) h)`
  -- definitionally, so the invariant-submodule membership transfers by `exact`.
  have hHc_inv : IsAInvariant hEinv.restrict Hc := by
    rw [isAInvariant_iff_smul_mem]
    intro a h hh
    rw [hmem_Hc] at hh ⊢
    have hmem := ρ.mem_invtSubmodule.mp hqc_invt a
    rw [Module.End.mem_invtSubmodule_iff_forall_mem_of_mem] at hmem
    exact hmem _ hh
  -- subgroup-level complement inside `↥E`.
  have hinf_g : pWg ⊓ Hc = ⊥ := by
    have h := congrArg Φ hinf; rwa [Φ.map_inf, Φ.map_bot, hΦpW, ← hHc_def] at h
  have hsup_g : pWg ⊔ Hc = ⊤ := by
    have h := congrArg Φ hsup; rwa [Φ.map_sup, Φ.map_top, hΦpW, ← hHc_def] at h
  -- lift `Hc` to `Y := Hc ⧸ S`-as-subgroup-of-`R ⧸ S`, and `X := Y.comap (mk' S)`.
  set Y : Subgroup (R ⧸ S) := Hc.map (Omega (R ⧸ S) p 1).subtype with hY_def
  have hY_le : Y ≤ Omega (R ⧸ S) p 1 := by rw [hY_def]; exact Subgroup.map_subtype_le _
  have hYinv : IsAInvariant (quotientMulAutHom hS) Y :=
    isAInvariant_map_subtype_of_restrict hEinv hHc_inv
  have hpWg_map : pWg.map (Omega (R ⧸ S) p 1).subtype = W' := by
    rw [hpWg_def, Subgroup.subgroupOf, Subgroup.map_comap_eq, Subgroup.range_subtype,
      inf_eq_right.mpr hWΩ]
  have hYW_inf : Y ⊓ W' = ⊥ := by
    rw [hY_def, ← hpWg_map,
      ← Subgroup.map_inf _ _ _ (Omega (R ⧸ S) p 1).subtype_injective,
      inf_comm, hinf_g, Subgroup.map_bot]
  have hYW_sup : Y ⊔ W' = Omega (R ⧸ S) p 1 := by
    rw [hY_def, ← hpWg_map, ← Subgroup.map_sup, sup_comm, hsup_g, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  -- assemble `X`.
  refine ⟨Y.comap (QuotientGroup.mk' S), ?_, isAInvariant_comap_mk' hS hYinv, ?_, ?_, ?_⟩
  · intro s hs
    rw [Subgroup.mem_comap, QuotientGroup.coe_mk', (QuotientGroup.eq_one_iff s).mpr hs]
    exact Y.one_mem
  · rw [Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective S)]; exact hY_le
  · rw [Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective S)]; exact hYW_inf
  · rw [Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective S)]; exact hYW_sup

/-- **Operator Maschke for an elementary abelian group.**  A coprime `MulAut`-action of `A`
on an elementary abelian `p`-group `E` splits any `A`-invariant subgroup off via an
`A`-invariant complement: `E = U ⊕ W` (`U ⊓ W = ⊥`, `U ⊔ W = ⊤`).

This is the direct (no-quotient) form of `exists_aInvariant_complement_in_omega1_quotient`,
canonical home for the module-Maschke split.  It is used through its subgroup form
`exists_aInvariant_complement_of_isElementaryAbelian_subgroup` (an ambient `Q ≤ G`) in
Peterfalvi (13.16). -/
theorem exists_aInvariant_complement_of_isElementaryAbelian
    {E : Type*} [Group E] [Finite E] {A : Type*} [Group A] [Finite A]
    {p : ℕ} [Fact p.Prime] (hpE : p ∣ Nat.card E) {φ : A →* MulAut E}
    (hcop : Nat.Coprime (Nat.card A) (Nat.card E)) (hE : IsElementaryAbelian p E)
    {U : Subgroup E} (hUinv : IsAInvariant φ U) :
    ∃ W : Subgroup E, IsAInvariant φ W ∧ U ⊓ W = ⊥ ∧ U ⊔ W = ⊤ := by
  classical
  have hEcomm : IsMulCommutative E := IsMulCommutative.of_comm hE.comm
  let : CommGroup E := { (inferInstance : Group E) with mul_comm := hE.comm }
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hpsmul : ∀ x : Additive E, (p : ℕ) • x = 0 := by
    intro x; apply Additive.toMul.injective
    rw [toMul_nsmul, toMul_zero]; exact hE.pow_eq_one x.toMul
  have : Module (ZMod p) (Additive E) := AddCommGroup.zmodModule hpsmul
  have : NeZero ((Nat.card A : ZMod p)) := neZero_natCast_zmod_of_coprime hcop hpE
  set ρ : Representation (ZMod p) A (Additive E) := (mulAutToEnd E p).comp φ with hρ_def
  have key_rho : ∀ (a : A) (v : Additive E),
      Additive.toMul (ρ a v) = (φ a) (Additive.toMul v) := fun _ _ => rfl
  set pU := AddSubgroup.toZModSubmodule (n := p) (Subgroup.toAddSubgroup U) with hpU_def
  have hmem_pU : ∀ v : Additive E, v ∈ pU ↔ Additive.toMul v ∈ U := by
    intro v
    simp only [hpU_def, AddSubgroup.mem_toZModSubmodule, Additive.mem_toAddSubgroup]
  have hpU_invt : pU ∈ ρ.invtSubmodule := by
    rw [ρ.mem_invtSubmodule]; intro a
    rw [Module.End.mem_invtSubmodule_iff_forall_mem_of_mem]
    intro v hv
    rw [hmem_pU] at hv ⊢
    rw [key_rho]
    exact hUinv.smul_mem a hv
  have hpU_sub : ∀ (a : A) ⦃v : Additive E⦄, v ∈ pU → ρ a v ∈ pU := by
    intro a v hv
    have hmem := ρ.mem_invtSubmodule.mp hpU_invt a
    rw [Module.End.mem_invtSubmodule_iff_forall_mem_of_mem] at hmem
    exact hmem v hv
  obtain ⟨qcSub, hcompl⟩ :=
    ComplementedLattice.exists_isCompl (⟨pU, hpU_sub⟩ : Subrepresentation ρ)
  set qc : Submodule (ZMod p) (Additive E) := qcSub.toSubmodule with hqc_def
  have hqc_invt : qc ∈ ρ.invtSubmodule := by
    rw [ρ.mem_invtSubmodule]; intro a
    rw [Module.End.mem_invtSubmodule_iff_forall_mem_of_mem]
    exact fun v hv => qcSub.apply_mem_toSubmodule a hv
  -- as above, `Subrepresentation.toSubmodule` commutes with `⊓/⊔/⊥/⊤` definitionally.
  have hinf : pU ⊓ qc = ⊥ :=
    congrArg Subrepresentation.toSubmodule hcompl.inf_eq_bot
  have hsup : pU ⊔ qc = ⊤ :=
    congrArg Subrepresentation.toSubmodule hcompl.sup_eq_top
  let Φ : Submodule (ZMod p) (Additive E) ≃o Subgroup E :=
    (AddSubgroup.toZModSubmodule (n := p)).symm.trans AddSubgroup.toSubgroup'
  set W : Subgroup E := Φ qc with hW_def
  have hΦpU : Φ pU = U := by
    have h1 : (AddSubgroup.toZModSubmodule (n := p)).symm pU = Subgroup.toAddSubgroup U := by
      rw [hpU_def, OrderIso.symm_apply_apply]
    simp only [Φ, OrderIso.trans_apply, h1]
    exact Subgroup.toAddSubgroup.symm_apply_apply U
  have hmem_W : ∀ h : E, h ∈ W ↔ (Additive.ofMul h) ∈ qc := by
    intro h
    rw [hW_def]
    simp only [Φ, OrderIso.trans_apply, AddSubgroup.mem_toSubgroup',
      AddSubgroup.toZModSubmodule_symm, Submodule.mem_toAddSubgroup]
  have hW_inv : IsAInvariant φ W := by
    rw [isAInvariant_iff_smul_mem]
    intro a h hh
    rw [hmem_W] at hh ⊢
    have hmem := ρ.mem_invtSubmodule.mp hqc_invt a
    rw [Module.End.mem_invtSubmodule_iff_forall_mem_of_mem] at hmem
    exact hmem _ hh
  refine ⟨W, hW_inv, ?_, ?_⟩
  · have h := congrArg Φ hinf; rwa [Φ.map_inf, Φ.map_bot, hΦpU, ← hW_def] at h
  · have h := congrArg Φ hsup; rwa [Φ.map_sup, Φ.map_top, hΦpU, ← hW_def] at h

/-- **Semisimple decomposition: an irreducible summand avoiding a proper invariant subgroup.**
Let `A` act coprimely on a finite elementary abelian `p`-group `V` (so `V` is a semisimple
`𝔽ₚ[A]`-module by operator Maschke), and let `C ≤ V` be a *proper* `A`-invariant subgroup
(`C ≠ ⊤`).  Then `V` has an `A`-invariant direct summand `S` (with `A`-invariant complement `W`,
so `V = S ⊕ W`) which is `A`-irreducible and meets `C` trivially: `C ⊓ S = ⊥` (and `S ≠ ⊥`).

This is the group-theoretic core of Peterfalvi (9.4): on `V = P/Φ(P)` operator Maschke decomposes
into `U W₁`-irreducibles, and taking `C = C_V(U)` (`U` does not centralize `V`, so `C ≠ ⊤`) yields
an irreducible summand `S` with `C_S(U) = C ⊓ S = ⊥`, i.e. on which `U` is fixed-point-free.  The
complement `W` realises `S` as the chief factor `V/W ≅ S`. -/
theorem exists_aInvariant_irreducible_summand_disjoint
    {V A : Type*} [Group V] [Finite V] [Group A] [Finite A] [Fact p.Prime]
    (hV : IsElementaryAbelian p V) {φ : A →* MulAut V}
    (hcop : Nat.Coprime (Nat.card A) (Nat.card V))
    {C : Subgroup V} (hCinv : IsAInvariant φ C) (hC : C ≠ ⊤) :
    ∃ S W : Subgroup V, IsAInvariant φ S ∧ IsAInvariant φ W ∧
      S ⊓ W = ⊥ ∧ S ⊔ W = ⊤ ∧ S ≠ ⊥ ∧
      (∀ K : Subgroup V, IsAInvariant φ K → K ≤ S → K = ⊥ ∨ K = S) ∧
      C ⊓ S = ⊥ := by
  classical
  -- `V` is nontrivial (else every subgroup, including `C`, is `⊤`), so `p ∣ |V|`.
  have hVnt : Nontrivial V := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    have := h
    refine hC (top_le_iff.mp fun x _ => ?_)
    rw [Subsingleton.elim x 1]; exact C.one_mem
  have hpV : p ∣ Nat.card V := by
    obtain ⟨x, hx⟩ := exists_ne (1 : V)
    have hord : orderOf x = p :=
      ((Fact.out : p.Prime).eq_one_or_self_of_dvd _
        (orderOf_dvd_of_pow_eq_one (hV.pow_eq_one x))).resolve_left
        (fun h1 => hx (orderOf_eq_one_iff.mp h1))
    exact hord ▸ orderOf_dvd_natCard x
  -- Step 1: split off an `A`-invariant complement `X` of `C`; `X ≠ ⊥` since `C ≠ ⊤`.
  obtain ⟨X, hXinv, hCX_inf, hCX_sup⟩ :=
    exists_aInvariant_complement_of_isElementaryAbelian hpV hcop hV hCinv
  have hX_ne : X ≠ ⊥ := by
    rintro rfl; rw [sup_bot_eq] at hCX_sup; exact hC hCX_sup
  -- Step 2: a minimal nonzero `A`-invariant subgroup `S ≤ X` (hence `A`-irreducible).
  set T : Set (Subgroup V) := {K | K ≠ ⊥ ∧ IsAInvariant φ K ∧ K ≤ X} with hT_def
  obtain ⟨S, ⟨hS_ne, hS_inv, hS_le⟩, hS_min⟩ :=
    (Set.toFinite T).exists_minimal ⟨X, hX_ne, hXinv, le_rfl⟩
  have hirr : ∀ K : Subgroup V, IsAInvariant φ K → K ≤ S → K = ⊥ ∨ K = S := by
    intro K hKinv hKS
    by_cases hK0 : K = ⊥
    · exact Or.inl hK0
    · exact Or.inr (le_antisymm hKS (hS_min ⟨hK0, hKinv, hKS.trans hS_le⟩ hKS))
  -- `C ⊓ S ≤ C ⊓ X = ⊥`.
  have hCS : C ⊓ S = ⊥ :=
    le_bot_iff.mp (hCX_inf ▸ inf_le_inf_left C hS_le)
  -- Step 3: split off an `A`-invariant complement `W` of `S`.
  obtain ⟨W, hWinv, hSW_inf, hSW_sup⟩ :=
    exists_aInvariant_complement_of_isElementaryAbelian hpV hcop hV hS_inv
  exact ⟨S, W, hS_inv, hWinv, hSW_inf, hSW_sup, hS_ne, hirr, hCS⟩

end OddOrder.BG.Ch1_Preliminary


