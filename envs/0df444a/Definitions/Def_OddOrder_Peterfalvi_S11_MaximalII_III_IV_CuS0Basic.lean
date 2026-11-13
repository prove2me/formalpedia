-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S11_MaximalII_III_IV_CuS0Basic
-- name    : OddOrder_Peterfalvi_S11_MaximalII_III_IV_CuS0Basic
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T11:45:17.038351+00:00
-- url     : https://prove2.me/theorems/3b9e6ce7-8fc6-489b-a652-c9be28916e19
-- title:
--   Peterfalvi §11: $C_U(S_0)$, opening layer
-- statement:
--   The opening layer of the $C_U(S_0)$ development for maximal subgroups of types II, III and IV: the seed homomorphism $\theta_0$ on $H$ and its extension to $H\cdot C_U(S_0)$, as in Peterfalvi (9.8.d).
--
--   Main declarations: `hcuSeedHom` (The seed hom θ₀); `hcuThetaHom` (The `θ₀`-extension hom `hcuThetaHom : H·C_U(S₀) → ℂˣ`).
--
--   The bundle also proves 8 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S11_MaximalII_III_IV/CuS0Basic.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S11_MaximalII_III_IV/CuS0Basic.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S11_MaximalII_III_IV_InertiaLift

namespace OddOrder.Peterfalvi.S11

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

open OddOrder.Isaacs.Ch03 (IsAInvariant isAInvariant_iff_smul_mem)

open OddOrder.Isaacs.Ch03.IsAInvariant (quotientMulAutHom)

variable {M : Subgroup G}

/-- **`C ≤ I_{HU}(θ₀)`**: `C = C_U(H̄)` fixes the realized chief-factor character `θ₀` (it acts
trivially on `H̄`, so `quotientMulAutHom = 1` on `cSub = ker(uActionHom)`, and the inflation is
unchanged).  The easy half of the (9.9.a) inertia lift. -/
theorem cInHu_le_inertia [Finite G] {M : Subgroup G} (data : TypesIIIIIIVSetup M)
    (chief : ChiefFactorData data) {θbar : IrreducibleCharacter (↥data.H ⧸ chief.N)} :
    cInHu data chief ≤ ClassFunction.inertia (G := ↥(huSub data)) (H := hInHu data)
        (ClassFunction.compHom (hInHuEquivH data).toMonoidHom
          (ClassFunction.compHom (QuotientGroup.mk' chief.N)
            (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ))) := by
  intro c hc
  rw [ClassFunction.mem_inertia]
  have hcG : ((c : ↥M) : G) ∈ cSub data chief := by
    simp only [cInHu, Subgroup.mem_subgroupOf] at hc; exact hc
  simp only [cSub, Subgroup.mem_map] at hcG
  obtain ⟨w, ⟨ĉ', hĉ', hĉ'w⟩, hwc⟩ := hcG
  have hq1 : quotientMulAutHom chief.N_aInvariant w = 1 := by rw [← hĉ'w]; exact hĉ'
  have hag : ((c : ↥M) : G) = (w : G) := hwc.symm
  rw [conjBy_compHom_hInHuEquivH data w c hag, compHom_typeP_conjAction_inflation, hq1]
  rfl

/-- **`I(θ₀) ⊓ U ≤ C`, parametrized over the realized stabilizer-triviality `hrealized`.**  The
case-agnostic part of the hard inertia direction: any `g ∈ I(θ₀) ⊓ U` realizes as a `U`-element `a`
whose `θ₀`-fixing (`mem_inertia`) feeds `hrealized` to conclude `a ∈ ker(uActionHom) = C`.  Case (b)
supplies `hrealized` as `caseB_inertia_realized`; case (a) via the non-Galois analog. -/
theorem inertia_inf_uInHu_le_cInHu_of_realized [Finite G] {M : Subgroup G}
    (data : TypesIIIIIIVSetup M) (chief : ChiefFactorData data)
    {θbar : IrreducibleCharacter (↥data.H ⧸ chief.N)}
    (hrealized : ∀ (a : ↥((typeP_quotientCoprimeAction data.typeP data.nontrivial.1
          chief.N_aInvariant).U)) (g : ↥(huSub data)),
        (((g : ↥M) : G) = (((typeP_quotientCoprimeAction data.typeP data.nontrivial.1
            chief.N_aInvariant).U.subtype a : ↥(data.typeP.U ⊔ data.typeP.W1)) : G)) →
        ClassFunction.conjBy g (ClassFunction.compHom (hInHuEquivH data).toMonoidHom
            (ClassFunction.compHom (QuotientGroup.mk' chief.N)
              (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ)))
          = ClassFunction.compHom (hInHuEquivH data).toMonoidHom
              (ClassFunction.compHom (QuotientGroup.mk' chief.N)
                (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ)) →
        ((typeP_quotientCoprimeAction data.typeP data.nontrivial.1 chief.N_aInvariant).φ.comp
          (typeP_quotientCoprimeAction data.typeP data.nontrivial.1
            chief.N_aInvariant).U.subtype) a = 1) :
    ClassFunction.inertia (G := ↥(huSub data)) (H := hInHu data)
        (ClassFunction.compHom (hInHuEquivH data).toMonoidHom
          (ClassFunction.compHom (QuotientGroup.mk' chief.N)
            (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ))) ⊓ uInHu data
      ≤ cInHu data chief := by
  rintro g ⟨hgin, hgu⟩
  have hgU : ((g : ↥M) : G) ∈ data.typeP.U := by
    simp only [uInHu] at hgu; exact hgu
  have hgUW1 : ((g : ↥M) : G) ∈ data.typeP.U ⊔ data.typeP.W1 := Subgroup.mem_sup_left hgU
  set a : ↥((typeP_quotientCoprimeAction data.typeP data.nontrivial.1 chief.N_aInvariant).U) :=
    ⟨⟨((g : ↥M) : G), hgUW1⟩, Subgroup.mem_subgroupOf.mpr hgU⟩ with ha_def
  have hag : ((g : ↥M) : G)
      = (((typeP_quotientCoprimeAction data.typeP data.nontrivial.1
          chief.N_aInvariant).U.subtype a : ↥(data.typeP.U ⊔ data.typeP.W1)) : G) := rfl
  have hker : a ∈ (uActionHom data chief).ker :=
    hrealized a g hag (ClassFunction.mem_inertia.mp hgin)
  simp only [cInHu, Subgroup.mem_subgroupOf, cSub, Subgroup.mem_map]
  exact ⟨_, ⟨a, hker, rfl⟩, rfl⟩

theorem inertia_inf_uInHu_le_cInHu [Finite G] {M : Subgroup G} (data : TypesIIIIIIVSetup M)
    (chief : ChiefFactorData data)
    (hcaseB : ∀ J : Subgroup (↥data.H ⧸ chief.N),
        IsAInvariant ((typeP_quotientCoprimeAction data.typeP data.nontrivial.1
          chief.N_aInvariant).φ.comp (typeP_quotientCoprimeAction data.typeP data.nontrivial.1
          chief.N_aInvariant).U.subtype) J → J = ⊥ ∨ J = ⊤)
    {θbar : IrreducibleCharacter (↥data.H ⧸ chief.N)}
    (hθbar : (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ) ≠ trivialClassFunction _) :
    ClassFunction.inertia (G := ↥(huSub data)) (H := hInHu data)
        (ClassFunction.compHom (hInHuEquivH data).toMonoidHom
          (ClassFunction.compHom (QuotientGroup.mk' chief.N)
            (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ))) ⊓ uInHu data
      ≤ cInHu data chief :=
  inertia_inf_uInHu_le_cInHu_of_realized data chief (caseB_inertia_realized hcaseB hθbar)

/-- **Peterfalvi (9.8.d) hard inertia direction: `I(θ₁₀) ⊓ U ≤ C_U(S₀)`.**  For a chief-factor
character `θ₁` nontrivial on the orbit generator `S₀ = H₁` (`hreg` on `caseA.S0`), any `U`-element
in
the inertia of the inflation `θ₁₀` centralizes `S₀`, hence lies in `C_U(S₀) = cuInHu`.  The
single-factor analog of `inertia_inf_uInHu_le_cInHu`: same `conjBy → compHom → mk'`-injective
unwrapping (`conjBy_compHom_hInHuEquivH`, `compHom_typeP_conjAction_inflation`,
`compHom_injective_of_surjective`) as `caseB_inertia_realized_of_charInertia` /
`caseB_char_inertia_inflation_of_core`, but the stabilizer-triviality core is
`chiefFactor_caseA_char_inertia_single` (`aInvariantRestrictAut S₀ a = 1`, i.e. `a ∈ C_U(S₀)`), not
`uActionHom a = 1` (`a ∈ C`).  This is the honest degree-`qa` inertia: `θ₁` is faithful only on the
single summand `S₀`, so its inertia is `H·C_U(S₀)` (index `a`), not `HC` (index `u`). -/
theorem inertia_inf_uInHu_le_cuInHu [Finite G] {M : Subgroup G} {data : TypesIIIIIIVSetup M}
    {chief : ChiefFactorData data} {chars : Section11CharacterData data chief}
    (caseA : CliffordCaseAData chars)
    {θbar : IrreducibleCharacter (↥data.H ⧸ chief.N)}
    (hreg : ∃ x ∈ caseA.S0,
      (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ) x
        ≠ (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ) 1) :
    ClassFunction.inertia (G := ↥(huSub data)) (H := hInHu data)
        (ClassFunction.compHom (hInHuEquivH data).toMonoidHom
          (ClassFunction.compHom (QuotientGroup.mk' chief.N)
            (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ))) ⊓ uInHu data
      ≤ cuInHu caseA := by
  rintro g ⟨hgin, hgu⟩
  have hgU : ((g : ↥M) : G) ∈ data.typeP.U := by
    simp only [uInHu] at hgu; exact hgu
  have hgUW1 : ((g : ↥M) : G) ∈ data.typeP.U ⊔ data.typeP.W1 := Subgroup.mem_sup_left hgU
  set a : ↥((typeP_quotientCoprimeAction data.typeP data.nontrivial.1 chief.N_aInvariant).U) :=
    ⟨⟨((g : ↥M) : G), hgUW1⟩, Subgroup.mem_subgroupOf.mpr hgU⟩ with ha_def
  have hag : ((g : ↥M) : G)
      = (((typeP_quotientCoprimeAction data.typeP data.nontrivial.1
          chief.N_aInvariant).U.subtype a : ↥(data.typeP.U ⊔ data.typeP.W1)) : G) := rfl
  -- Unwrap the `conjBy`-fixing to the abstract `uActionHom`-invariance of `θbar` (as in the
  -- case-(b) plumbing), then apply the single-factor core to get `aInvariantRestrictAut S₀ a = 1`.
  have hfix := ClassFunction.mem_inertia.mp hgin
  rw [conjBy_compHom_hInHuEquivH data
    ((typeP_quotientCoprimeAction data.typeP data.nontrivial.1 chief.N_aInvariant).U.subtype a)
    g hag] at hfix
  -- strip the `hInHuEquivH` layer (`compHom_injective` on the surjective inflation iso), …
  have hfix1 := ClassFunction.compHom_injective_of_surjective (hInHuEquivH data).surjective hfix
  -- … then the `typeP_conjAction` layer (`mk'` surjective), leaving abstract `φ`-invariance.
  rw [compHom_typeP_conjAction_inflation] at hfix1
  have hfix2 := ClassFunction.compHom_injective_of_surjective
    (QuotientGroup.mk'_surjective chief.N) hfix1
  have hinv : ∀ x, (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ) ((uActionHom data chief) a x)
      = (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ) x := by
    intro x
    exact congrFun (congrArg (fun f : ClassFunction (↥data.H ⧸ chief.N) ℂ =>
      (f : (↥data.H ⧸ chief.N) → ℂ)) hfix2) x
  have hkerAut : aInvariantRestrictAut caseA.S0_aInvariant a = 1 :=
    chiefFactor_caseA_char_inertia_single caseA hreg a hinv
  have hker : a ∈ (aInvariantRestrictAut caseA.S0_aInvariant).ker :=
    MonoidHom.mem_ker.mpr hkerAut
  simp only [cuInHu, cuSub, Subgroup.mem_subgroupOf, Subgroup.mem_map]
  exact ⟨_, ⟨a, hker, rfl⟩, rfl⟩

/-- **Peterfalvi (9.8.d) easy inertia direction `C_U(S₀) ⊆ I_{HU}(θ₁₀)`, given an `S₀`-summand
decomposition.**  For a `U`-invariant complement `W` of `S₀` (`S₀ ⊔ W = ⊤`) and a chief-factor
character `θ₁ = θbar` **trivial on `W`**, every `C_U(S₀) = cuInHu`-element fixes the inflation
`θ₁₀`.
The realized easy half of the (9.8.d) inertia lift (mirror of `cInHu_le_inertia`, but where the
`C`-element acts trivially on *all* of `H̄`, here the `C_U(S₀)`-element acts trivially on `S₀` and
merely preserves `W`).  The algebraic heart is `mulAut_fixes_char_of_id_on_summand_triv_complement`:
`c ∈ C_U(S₀)` gives `aInvariantRestrictAut S₀ = 1` (fixes `S₀` pointwise) and `W`-invariance gives
`W`-preservation, so the linear `θ₁` (trivial on `W`) is fixed. -/
theorem cuInHu_le_inertia_of_complement_triv [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars)
    {W : Subgroup (↥data.H ⧸ chief.N)}
    (hWinv : OddOrder.Isaacs.Ch03.IsAInvariant (uActionHom data chief) W)
    (hsup : caseA.S0 ⊔ W = ⊤)
    {θbar : IrreducibleCharacter (↥data.H ⧸ chief.N)}
    (htriv : ∀ w ∈ W, (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ) w
      = (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ) 1) :
    cuInHu caseA ≤ ClassFunction.inertia (G := ↥(huSub data)) (H := hInHu data)
        (ClassFunction.compHom (hInHuEquivH data).toMonoidHom
          (ClassFunction.compHom (QuotientGroup.mk' chief.N)
            (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ))) := by
  have : IsMulCommutative (↥data.H ⧸ chief.N) :=
    IsMulCommutative.of_comm chief.quotient_elementaryAbelian.comm
  intro c hc
  rw [ClassFunction.mem_inertia]
  -- unwrap `c ∈ cuInHu` to the `U`-element `a'` (in `U.subgroupOf (U ⊔ W₁)`) with
  -- `aInvariantRestrictAut S₀ a' = 1` and `((c:M):G) = subtype a'`.
  have hcG : ((c : ↥M) : G) ∈ cuSub caseA := by
    simp only [cuInHu, Subgroup.mem_subgroupOf] at hc; exact hc
  simp only [cuSub, Subgroup.mem_map] at hcG
  obtain ⟨w, ⟨a', ha', ha'w⟩, hwc⟩ := hcG
  have hkerAut : aInvariantRestrictAut caseA.S0_aInvariant a' = 1 := by
    rw [← MonoidHom.mem_ker]; exact ha'
  have hag : ((c : ↥M) : G) = (w : G) := hwc.symm
  -- `quotientMulAutHom w = uActionHom a'` (defeq); it fixes `S₀` pointwise and preserves `W`.
  have hid : ∀ x ∈ caseA.S0, (uActionHom data chief) a' x = x := by
    intro x hx
    have := aInvariantRestrictAut_coe caseA.S0_aInvariant a' ⟨x, hx⟩
    rw [hkerAut] at this
    simpa using this.symm
  have hWpres : ∀ x ∈ W, (uActionHom data chief) a' x ∈ W := fun x hx => hWinv.smul_mem a' hx
  have hfixθ : ∀ x, (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ) ((uActionHom data chief) a' x)
      = (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ) x :=
    mulAut_fixes_char_of_id_on_summand_triv_complement (uActionHom data chief a') caseA.S0 W
      hsup hid hWpres θbar htriv
  -- `uActionHom a' = quotientMulAutHom w` (`uActionHom = quotientMulAutHom ∘ subtype`;
  -- `subtype a' = w`)
  have huaw : uActionHom data chief a' = quotientMulAutHom chief.N_aInvariant w := by
    rw [show uActionHom data chief a'
        = quotientMulAutHom chief.N_aInvariant
            ((data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1)).subtype a') from rfl, ha'w]
  -- `H̄`-level fixing: `compHom (quotientMulAutHom w) θbar = θbar`.
  have hHbar : ClassFunction.compHom (quotientMulAutHom chief.N_aInvariant w).toMonoidHom
        (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ)
      = (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ) := by
    ext y
    rw [ClassFunction.compHom_apply, ← huaw]
    exact hfixθ y
  -- reduce the `conjBy`-fixing to the just-established `H̄`-level fixing.
  rw [conjBy_compHom_hInHuEquivH data w c hag, compHom_typeP_conjAction_inflation, hHbar]

/-- **Peterfalvi (9.8.d) inertia lift `I_{HU}(θ₁₀) = H·C_U(S₀)`, parametrized over the easy
direction** `C_U(S₀) ≤ I(θ₁₀)`.  The single-factor analog of `inertia_eq_hcInHu_of_inf_le`: `⊆` uses
the proven hard direction `inertia_inf_uInHu_le_cuInHu` (`I(θ₁₀) ⊓ U ≤ C_U(S₀)`, from `θ₁` faithful
on `S₀`), `⊇` from `H ≤ I(θ₁₀)` (`subgroup_le_inertia`) and the supplied `heasy`
(`C_U(S₀) ≤ I(θ₁₀)`).  The easy direction `heasy` holds precisely when `θ₁ ∈ Irr(H̄/(H₂…H_q))` is
trivial on the complementary summands (a `C_U(S₀)`-element acts trivially on `S₀` and preserves each
`Hpart`, so it fixes a character supported on `S₀`); it is isolated as a hypothesis here.  Result:
`I(θ₁₀) = H·C_U(S₀)`, whose index in `HU` is `a` (`index_hcuInHu_eq_caseA_a`), giving the source
degree `a` and character degree `qa`.  Mirrors the `hInHu ⊔ cuInHu` form of the just-landed
`C_U(S₀)` substrate. -/
theorem inertia_eq_hcuInHu_of_easy_le [Finite G] {M : Subgroup G} {data : TypesIIIIIIVSetup M}
    {chief : ChiefFactorData data} {chars : Section11CharacterData data chief}
    (caseA : CliffordCaseAData chars)
    {θbar : IrreducibleCharacter (↥data.H ⧸ chief.N)}
    (hreg : ∃ x ∈ caseA.S0,
      (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ) x
        ≠ (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ) 1)
    (heasy : cuInHu caseA ≤ ClassFunction.inertia (G := ↥(huSub data)) (H := hInHu data)
        (ClassFunction.compHom (hInHuEquivH data).toMonoidHom
          (ClassFunction.compHom (QuotientGroup.mk' chief.N)
            (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ)))) :
    ClassFunction.inertia (G := ↥(huSub data)) (H := hInHu data)
        (ClassFunction.compHom (hInHuEquivH data).toMonoidHom
          (ClassFunction.compHom (QuotientGroup.mk' chief.N)
            (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ)))
      = hInHu data ⊔ cuInHu caseA := by
  set θ₀ := ClassFunction.compHom (hInHuEquivH data).toMonoidHom
    (ClassFunction.compHom (QuotientGroup.mk' chief.N)
      (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ)) with hθ₀
  apply le_antisymm
  · intro g hg
    have hgtop : g ∈ hInHu data ⊔ uInHu data := hInHu_sup_uInHu_eq_top data ▸ Subgroup.mem_top g
    rw [Subgroup.mem_sup_of_normal_left] at hgtop
    obtain ⟨h, hh, u, hu, rfl⟩ := hgtop
    have hh_in : h ∈ ClassFunction.inertia (H := hInHu data) θ₀ :=
      ClassFunction.subgroup_le_inertia θ₀ hh
    have hu_in : u ∈ ClassFunction.inertia (H := hInHu data) θ₀ := by
      have hmem : h⁻¹ * (h * u) ∈ ClassFunction.inertia (H := hInHu data) θ₀ :=
        mul_mem (inv_mem hh_in) hg
      rwa [inv_mul_cancel_left] at hmem
    exact mul_mem (Subgroup.mem_sup_left hh)
      (Subgroup.mem_sup_right (inertia_inf_uInHu_le_cuInHu caseA hreg ⟨hu_in, hu⟩))
  · rw [sup_le_iff]
    exact ⟨ClassFunction.subgroup_le_inertia θ₀, heasy⟩

/-- **Peterfalvi (9.8.d) full inertia lift `I_{HU}(θ₁₀) = H·C_U(S₀)`**, given an `S₀`-summand
decomposition and `θ₁ = θbar` supported on `S₀` (nontrivial on `S₀`, trivial on the complement `W`).
Combines the proven hard direction (`inertia_inf_uInHu_le_cuInHu`) with the easy direction
(`cuInHu_le_inertia_of_complement_triv`) through the assembly `inertia_eq_hcuInHu_of_easy_le`.  The
index of `H·C_U(S₀)` in `HU` is `a` (`index_hcuInHu_eq_caseA_a`), so the source `θ₁·λ` has degree
`a`
and its `M`-induction degree `qa`. -/
theorem inertia_eq_hcuInHu [Finite G] {M : Subgroup G} {data : TypesIIIIIIVSetup M}
    {chief : ChiefFactorData data} {chars : Section11CharacterData data chief}
    (caseA : CliffordCaseAData chars)
    {W : Subgroup (↥data.H ⧸ chief.N)}
    (hWinv : OddOrder.Isaacs.Ch03.IsAInvariant (uActionHom data chief) W)
    (hsup : caseA.S0 ⊔ W = ⊤)
    {θbar : IrreducibleCharacter (↥data.H ⧸ chief.N)}
    (hreg : ∃ x ∈ caseA.S0,
      (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ) x
        ≠ (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ) 1)
    (htriv : ∀ w ∈ W, (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ) w
      = (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ) 1) :
    ClassFunction.inertia (G := ↥(huSub data)) (H := hInHu data)
        (ClassFunction.compHom (hInHuEquivH data).toMonoidHom
          (ClassFunction.compHom (QuotientGroup.mk' chief.N)
            (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ)))
      = hInHu data ⊔ cuInHu caseA :=
  inertia_eq_hcuInHu_of_easy_le caseA hreg
    (cuInHu_le_inertia_of_complement_triv caseA hWinv hsup htriv)

/-- **`H` and `C_U(S₀)` are complementary inside `H·C_U(S₀)`** (`IsComplement'` of the two
`subgroupOf`-realizations in the join): `H ⊓ C_U(S₀) = ⊥` (`hInHu_inf_cuInHu_eq_bot`) gives
disjointness,
`H ⊔ C_U(S₀)` is the whole ambient by construction.  This is the complement input to
`SemidirectProduct.mulEquivSubgroup`, exhibiting `H·C_U(S₀) ≃* H ⋊[φ] C_U(S₀)`. -/
theorem hInHu_isComplement'_cuInHu_in_hcuInHu [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars) :
    ((hInHu data).subgroupOf (hInHu data ⊔ cuInHu caseA)).IsComplement'
      ((cuInHu caseA).subgroupOf (hInHu data ⊔ cuInHu caseA)) := by
  have := hInHu_normal data
  have : ((hInHu data).subgroupOf (hInHu data ⊔ cuInHu caseA)).Normal :=
    (hInHu_normal data).subgroupOf _
  refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
  · rw [disjoint_iff]
    change (hInHu data).comap _ ⊓ (cuInHu caseA).comap _ = ⊥
    rw [← Subgroup.comap_inf (hInHu data) (cuInHu caseA)
      (hInHu data ⊔ cuInHu caseA).subtype, hInHu_inf_cuInHu_eq_bot caseA]
    simp
  · rw [← Subgroup.normal_mul, ← Subgroup.subgroupOf_sup le_sup_left le_sup_right,
      Subgroup.subgroupOf_self, Subgroup.coe_top]

/-- The seed hom `θ₀ : H →* ℂˣ` in raw hom form: `θ ∘ mk'(N) ∘ hInHuEquivH`.  Its
`linearClassFunction` is the seed `θ₀` used in the inertia lift `inertia_eq_hcuInHu` (via
`ClassFunction.compHom_linearIrreducibleCharacter`). -/
noncomputable def hcuSeedHom [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data} (θ : (↥data.H ⧸ chief.N) →* ℂˣ) :
    ↥(hInHu data) →* ℂˣ :=
  θ.comp ((QuotientGroup.mk' chief.N).comp (hInHuEquivH data).toMonoidHom)

/-- **The `θ₀`-extension hom `hcuThetaHom : H·C_U(S₀) →* ℂˣ`** (Peterfalvi (9.8.d)).  The extension
of the seed hom `θ ∘ mk'(N) ∘ hInHuEquivH` from the normal factor `H` to `H·C_U(S₀)`, trivial on the
complement `C_U(S₀)`.  Built by `SemidirectProduct.lift` (through the complement iso
`hInHu_isComplement'_cuInHu_in_hcuInHu`); the `lift` `φ`-compatibility `fn(φ(c) h) = fn(h)` is the
`C_U(S₀)`-invariance of `θ₀` (`hinv`, supplied by `cuInHu_le_inertia_of_complement_triv`), using
that
the codomain `ℂˣ` is abelian (`MulAut.conj = 1`).  Restricts to `θ₀` on `H`
(`hcuThetaHom_inclusion_hInHu`). -/
noncomputable def hcuThetaHom [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars)
    (θ : (↥data.H ⧸ chief.N) →* ℂˣ)
    (hinv : ∀ c : ↥(cuInHu caseA), ∀ h : ↥(hInHu data),
      hcuSeedHom (chief := chief) θ
          ⟨(c : ↥(huSub data)) * (h : ↥(huSub data)) * (c : ↥(huSub data))⁻¹,
            (hInHu_normal data).conj_mem _ h.2 (c : ↥(huSub data))⟩
        = hcuSeedHom (chief := chief) θ h) :
    ↥(hInHu data ⊔ cuInHu caseA) →* ℂˣ :=
  haveI := hInHu_normal data
  haveI : ((hInHu data).subgroupOf (hInHu data ⊔ cuInHu caseA)).Normal :=
    (hInHu_normal data).subgroupOf _
  (SemidirectProduct.lift
      ((hcuSeedHom (chief := chief) θ).comp
        (Subgroup.subgroupOfEquivOfLe
          (le_sup_left : hInHu data ≤ hInHu data ⊔ cuInHu caseA)).toMonoidHom)
      (1 : ↥((cuInHu caseA).subgroupOf (hInHu data ⊔ cuInHu caseA)) →* ℂˣ)
      (by
        intro c
        ext h
        -- RHS: `(1 : _→*ℂˣ) c = 1`, `MulAut.conj 1 = 1`; LHS: `φ(c) h = c·h·c⁻¹` in the subgroupOf.
        simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MonoidHom.one_apply, map_one,
          MulAut.one_apply]
        -- transport `c`, `h` from the join-`subgroupOf`s to `↥(cuInHu)`, `↥(hInHu)`.
        set c' := (Subgroup.subgroupOfEquivOfLe
          (le_sup_right : cuInHu caseA ≤ hInHu data ⊔ cuInHu caseA)) c with hc'
        set h' := (Subgroup.subgroupOfEquivOfLe
          (le_sup_left : hInHu data ≤ hInHu data ⊔ cuInHu caseA)) h with hh'
        -- the two `↥(hInHu data)` arguments agree, so `hcuSeedHom θ` agrees on them.
        have harg : (Subgroup.subgroupOfEquivOfLe
              (le_sup_left : hInHu data ≤ hInHu data ⊔ cuInHu caseA))
            ((((hInHu data).subgroupOf (hInHu data ⊔ cuInHu caseA)).normalizerMonoidHom
              ((Subgroup.inclusion (((hInHu data).subgroupOf
                (hInHu data ⊔ cuInHu caseA)).normalizer_eq_top ▸ le_top)) c)) h)
            = ⟨(c' : ↥(huSub data)) * (h' : ↥(huSub data)) * (c' : ↥(huSub data))⁻¹,
                (hInHu_normal data).conj_mem _ h'.2 (c' : ↥(huSub data))⟩ := by
          apply Subtype.ext
          simp only [hc', hh', Subgroup.subgroupOfEquivOfLe_apply_coe,
            Subgroup.normalizerMonoidHom_apply_apply_coe, Subgroup.coe_inclusion,
            Subgroup.coe_mul, Subgroup.coe_inv]
        rw [harg]
        exact congrArg (Units.val) (hinv c' h'))).comp
    (SemidirectProduct.mulEquivSubgroup
      (hInHu_isComplement'_cuInHu_in_hcuInHu caseA)).symm.toMonoidHom

end OddOrder.Peterfalvi.S11


