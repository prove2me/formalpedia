-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S11_MaximalII_III_IV_CaseBXi
-- name    : OddOrder_Peterfalvi_S11_MaximalII_III_IV_CaseBXi
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T11:57:14.967638+00:00
-- url     : https://prove2.me/theorems/f5075070-3b85-4407-b396-af9e4ded4cf6
-- title:
--   Peterfalvi (9.8.d)/(9.9.c): case (b) $\xi$-constructions and rigidity (continuation)
-- statement:
--   A continuation file for the Clifford case analysis. It realizes a summand complement $W$ in $G$ (Peterfalvi (9.8.d)), shows the pair characters $\zeta_{\theta_1,\lambda}$ lie in the relevant sets, and proves the rigidity statement of (9.9.c).
--
--   Main declarations: `caseA_realizedComplement` (Realized summand-complement `W` in `G`); `hcuZetaPair_mem_xiSet` (`H ⊄ Ker ζ_{θ₁,λ}`); `hcuZetaPair_mem_xiOf` (`ζ_{θ₁,λ} ∈ 𝒳(H₀U')`); `cInHuEquivC` (The realization iso `cInHu ≃ C`).
--
--   The bundle also proves 33 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S11_MaximalII_III_IV/CaseBXi.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S11_MaximalII_III_IV/CaseBXi.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S11_MaximalII_III_IV_Coherence911

namespace OddOrder.Peterfalvi.S11

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

open OddOrder.Isaacs.Ch03 (IsAInvariant isAInvariant_iff_smul_mem)

open OddOrder.Isaacs.Ch03.IsAInvariant (quotientMulAutHom)

variable {M : Subgroup G}

/-- **Realized summand-complement `W` in `G`** (Peterfalvi (9.8.d)).  A subgroup `W ≤ H̄ = H/N`
(here the summand-join complement `H₂…H_q`) realizes as the preimage-in-`H`-viewed-in-`G`
`(W.comap (mk' N)).map H.subtype`.  It contains `H₀ = N.map H.subtype` (as `⊥ ≤ W` after `mk'`) and
lies in `H`; its `HU`-realization is the kernel carrier of the (9.8.d) `θ₁`-factor. -/
noncomputable def caseA_realizedComplement {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data)
    (W : Subgroup (↥data.H ⧸ chief.N)) : Subgroup G :=
  (W.comap (QuotientGroup.mk' chief.N)).map data.H.subtype

/-- The realized complement lies in `H`. -/
theorem caseA_realizedComplement_le_H {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data)
    (W : Subgroup (↥data.H ⧸ chief.N)) :
    caseA_realizedComplement chief W ≤ data.H := by
  rintro _ ⟨x, _, rfl⟩; exact x.2

/-- The `HU`-realized complement lies in `hInHu` (as `realized W ≤ H`). -/
theorem caseA_realizedComplement_subgroupOf_le_hInHu {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data)
    (W : Subgroup (↥data.H ⧸ chief.N)) :
    ((caseA_realizedComplement chief W).subgroupOf M).subgroupOf (huSub data)
      ≤ hInHu data :=
  Subgroup.subgroupOf_mono _ (Subgroup.subgroupOf_mono _ (caseA_realizedComplement_le_H chief W))

/-- **The realization iso sends realized `W` (in `hInHu`) onto `W`** under `mk'(N) ∘ hInHuEquivH`.
Mirror of `realizedH0_subgroupOf_hInHu_eq_comap`: an element `x ∈ hInHu` lies in the realized `W`
iff `mk'(N)(hInHuEquivH x) ∈ W`. -/
theorem caseA_realizedComplement_subgroupOf_hInHu_eq_comap {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data)
    (W : Subgroup (↥data.H ⧸ chief.N)) :
    (((caseA_realizedComplement chief W).subgroupOf M).subgroupOf (huSub data)).subgroupOf
        (hInHu data)
      = W.comap ((QuotientGroup.mk' chief.N).comp (hInHuEquivH data).toMonoidHom) := by
  ext x
  rw [Subgroup.mem_comap, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf,
    caseA_realizedComplement, Subgroup.mem_map, ← hInHuEquivH_coe]
  constructor
  · rintro ⟨z, hz, hzeq⟩
    have hz_eq : z = hInHuEquivH data x := Subgroup.subtype_injective data.H hzeq
    rw [Subgroup.mem_comap, QuotientGroup.mk'_apply] at hz
    rwa [hz_eq] at hz
  · intro h
    exact ⟨hInHuEquivH data x, by rwa [Subgroup.mem_comap, QuotientGroup.mk'_apply], rfl⟩

/-- **The seed hom `θ₀ = θ ∘ mk'(N) ∘ hInHuEquivH` kills the realized complement `W`** when `θ` is
trivial on `W ≤ H̄`.  For `h ∈ hInHu` in the realized `W`, `hInHuEquivH h` maps under `mk'(N)` into
`W`, on which `θ` is `1`.  Mirror of `hcuSeedHom_eq_one_of_mem_realizedH0` (which is the `W = ⊥`,
`θ`-agnostic case). -/
theorem hcuSeedHom_eq_one_of_mem_realizedComplement [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data) (θ : (↥data.H ⧸ chief.N) →* ℂˣ)
    {W : Subgroup (↥data.H ⧸ chief.N)} (hθW : ∀ w ∈ W, θ w = 1)
    {h : ↥(hInHu data)}
    (hh : h ∈ (((caseA_realizedComplement chief W).subgroupOf M).subgroupOf (huSub data)).subgroupOf
      (hInHu data)) :
    hcuSeedHom (chief := chief) θ h = 1 := by
  have hW : (QuotientGroup.mk' chief.N) (hInHuEquivH data h) ∈ W := by
    have := (caseA_realizedComplement_subgroupOf_hInHu_eq_comap chief W) ▸ hh
    rwa [Subgroup.mem_comap, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] at this
  rw [hcuSeedHom, MonoidHom.comp_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  exact hθW _ hW

/-- **`hcuPairHom` kills the realized complement `W`** (`HC`-level, pointwise), given `θ|_W = 1`.
Every `x` in the realized `W ⊆ H` has `θ`-part `hcuThetaHom x = hcuSeedHom θ x = 1`
(`hcuThetaHom_inclusion_hInHu`, `hcuSeedHom_eq_one_of_mem_realizedComplement`) and `λ`-part
`hcuLambdaHom x = 1` (`hcuLambdaHom_eq_one_of_mem_hInHu`, since `W ⊆ H`). -/
theorem hcuPairHom_eq_one_of_mem_realizedComplement [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars)
    (θ : (↥data.H ⧸ chief.N) →* ℂˣ)
    (hinv : ∀ c : ↥(cuInHu caseA), ∀ h : ↥(hInHu data),
      hcuSeedHom (chief := chief) θ
          ⟨(c : ↥(huSub data)) * (h : ↥(huSub data)) * (c : ↥(huSub data))⁻¹,
            (hInHu_normal data).conj_mem _ h.2 (c : ↥(huSub data))⟩
        = hcuSeedHom (chief := chief) θ h)
    (lam : ↥(cuInHu caseA) →* ℂˣ)
    {W : Subgroup (↥data.H ⧸ chief.N)} (hθW : ∀ w ∈ W, θ w = 1)
    {x : ↥(hInHu data ⊔ cuInHu caseA)}
    (hx : x ∈ ((((caseA_realizedComplement chief W).subgroupOf M).subgroupOf
      (huSub data)).subgroupOf (hInHu data)).map
        (Subgroup.inclusion (le_sup_left : hInHu data ≤ hInHu data ⊔ cuInHu caseA))) :
    hcuPairHom caseA θ hinv lam x = 1 := by
  have := hInHu_normal data
  obtain ⟨h, hhmem, hxeq⟩ := hx
  -- `x` is the inclusion of `h ∈ realized W ⊆ hInHu`.
  have hhH : (h : ↥(huSub data)) ∈ hInHu data := h.2
  have hxIncl : x = Subgroup.inclusion (le_sup_left : hInHu data ≤ hInHu data ⊔ cuInHu caseA) h :=
    hxeq.symm
  -- `θ`-part.
  have hθfac : hcuThetaHom caseA θ hinv x = 1 := by
    rw [hxIncl, hcuThetaHom_inclusion_hInHu caseA θ hinv h,
      hcuSeedHom_eq_one_of_mem_realizedComplement chief θ hθW hhmem]
  -- `λ`-part (`W ⊆ H`).
  have hlamfac : hcuLambdaHom caseA lam x = 1 := by
    apply hcuLambdaHom_eq_one_of_mem_hInHu caseA lam
    rw [hxIncl, Subgroup.mem_subgroupOf, Subgroup.coe_inclusion]
    exact h.2
  simp only [hcuPairHom, MonoidHom.mul_apply, hθfac, hlamfac, mul_one]

/-- **`W ⊆ Ker ψ_{θ₁,λ}` as a `Set` inclusion** (`HC`-level): the realized summand-complement `W` is
in the character kernel of the pair character, given `θ|_W = 1`.  Pointwise from
`hcuPairHom_eq_one_of_mem_realizedComplement`.  Mirror of
`hcuPsiPair_realizedH0supUprime_subgroupOf_subset_characterKernel`. -/
theorem hcuPsiPair_realizedComplement_subset_characterKernel [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars)
    (θ : (↥data.H ⧸ chief.N) →* ℂˣ)
    (hinv : ∀ c : ↥(cuInHu caseA), ∀ h : ↥(hInHu data),
      hcuSeedHom (chief := chief) θ
          ⟨(c : ↥(huSub data)) * (h : ↥(huSub data)) * (c : ↥(huSub data))⁻¹,
            (hInHu_normal data).conj_mem _ h.2 (c : ↥(huSub data))⟩
        = hcuSeedHom (chief := chief) θ h)
    (lam : ↥(cuInHu caseA) →* ℂˣ)
    {W : Subgroup (↥data.H ⧸ chief.N)} (hθW : ∀ w ∈ W, θ w = 1) :
    (((((caseA_realizedComplement chief W).subgroupOf M).subgroupOf (huSub data)).subgroupOf
        (hInHu data)).map
        (Subgroup.inclusion (le_sup_left : hInHu data ≤ hInHu data ⊔ cuInHu caseA)) :
        Set ↥(hInHu data ⊔ cuInHu caseA)) ⊆
      OddOrder.Peterfalvi.S03.characterKernel (hcuPsiPair caseA θ hinv lam) := by
  intro x hx
  rw [OddOrder.Peterfalvi.S03.mem_characterKernel]
  simp only [hcuPsiPair]
  rw [linearIrreducibleCharacter_apply, OddOrder.Peterfalvi.S03.characterDegree_def,
    linearIrreducibleCharacter_apply_one,
    hcuPairHom_eq_one_of_mem_realizedComplement caseA θ hinv lam hθW (SetLike.mem_coe.mp hx),
    Units.val_one]

/-- **`HU` normalizes the realized summand-complement `W`** (Peterfalvi (9.8.d)).  For a
`U`-invariant `W ≤ H̄` (`IsAInvariant (uActionHom) W`), the realized `W`
(`caseA_realizedComplement`) is normalized by `H ⊔ U`: `H` normalizes it because `H̄ = H/N` is
abelian so `W ◁ H̄` and `N ≤ WH ≤ H` gives `WH ◁ H`; `U` normalizes it because `u·wh·u⁻¹` has
`H̄`-image `uActionHom(u) • (mk' wh) ∈ W` (U-invariance).  This supplies the `[A.Normal]` of the
induce-kernel step for `W ⊆ Ker ζ`. -/
theorem caseA_realizedComplement_uW_le_normalizer [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {W : Subgroup (↥data.H ⧸ chief.N)}
    (hWinv : OddOrder.Isaacs.Ch03.IsAInvariant (uActionHom data chief) W) :
    data.H ⊔ data.U
      ≤ Subgroup.normalizer ((caseA_realizedComplement chief W : Subgroup G) : Set G) := by
  have : IsMulCommutative (↥data.H ⧸ chief.N) :=
    ⟨⟨chief.quotient_elementaryAbelian.1⟩⟩
  -- `WH := W.comap (mk' N) ⊴ H` (preimage of a subgroup of the abelian `H̄`).
  set WH : Subgroup ↥data.H := W.comap (QuotientGroup.mk' chief.N) with hWH
  have hWHn : WH.Normal := by
    rw [hWH]; exact (Subgroup.normal_of_isMulCommutative W).comap _
  -- `H` normalizes `caseA_realizedComplement = WH.map subtype`.
  have hH_norm : data.H
      ≤ Subgroup.normalizer ((caseA_realizedComplement chief W : Subgroup G) : Set G) := by
    have h := Subgroup.le_normalizer_map (H := WH) data.H.subtype
    rw [Subgroup.normalizer_eq_top_iff.mpr hWHn, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype] at h
    exact h
  -- `U` normalizes it: conjugation by `u ∈ U` lands `WH` in `WH` (`U`-invariance of `W`).
  have hconj : ∀ (u : ↥data.U) {m : ↥data.H}, m ∈ WH →
      (u : G) * data.H.subtype m * (u : G)⁻¹ ∈ caseA_realizedComplement chief W := by
    intro u m hm
    have huU : (u : G) ∈ data.typeP.U := u.2
    have huUW1 : (u : G) ∈ data.typeP.U ⊔ data.typeP.W1 := Subgroup.mem_sup_left huU
    -- `typeP_conjAction (u) m ∈ WH`, i.e. `mk'(u·m·u⁻¹) ∈ W`.
    have huinv : (uActionHom data chief
        ⟨⟨(u : G), huUW1⟩, Subgroup.mem_subgroupOf.mpr huU⟩)
          (QuotientGroup.mk' chief.N m) ∈ W :=
      hWinv.smul_mem
        (⟨⟨(u : G), huUW1⟩, Subgroup.mem_subgroupOf.mpr huU⟩ :
          ↥(data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1)))
        (Subgroup.mem_comap.mp hm)
    rw [uActionHom, MonoidHom.comp_apply, Subgroup.coe_subtype,
      OddOrder.Isaacs.Ch03.IsAInvariant.quotientMulAutHom_apply_mk'] at huinv
    refine ⟨typeP_conjAction data.typeP ⟨(u : G), huUW1⟩ m,
      Subgroup.mem_comap.mpr ?_, typeP_conjAction_apply data.typeP _ m⟩
    simpa only [Subgroup.subtype_apply, QuotientGroup.mk'_apply] using huinv
  have hU_norm : data.U
      ≤ Subgroup.normalizer ((caseA_realizedComplement chief W : Subgroup G) : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨fun ⟨m, hm, hval⟩ => hval ▸ hconj ⟨g, hg⟩ hm, fun hh => ?_⟩
    obtain ⟨m, hm, hval⟩ := hh
    have key := hconj (⟨g, hg⟩ : ↥data.U)⁻¹ hm
    have hE : ((⟨g, hg⟩ : ↥data.U)⁻¹ : G) * data.H.subtype m
        * (((⟨g, hg⟩ : ↥data.U)⁻¹ : G))⁻¹ = h := by
      rw [hval]; change g⁻¹ * (g * h * g⁻¹) * (g⁻¹ : G)⁻¹ = h; group
    exact hE ▸ key
  exact sup_le hH_norm hU_norm

/-- **realized summand-complement `W ◁ M`** (Peterfalvi (9.8.d)): the realized `W` is normalized by
`M = H ⊔ (U ⊔ W₁)`; combined with `caseA_realizedComplement_le_M` this is `W ◁ M`, whose
`huSub`-restriction is the `[A.Normal]` input of the induce-kernel step.  (`W₁` need not normalize
`W`; but `H ⊔ U = HU` does, which is all the induce-kernel step over `HU` requires.) -/
theorem caseA_realizedComplement_subgroupOf_huSub_normal [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {W : Subgroup (↥data.H ⧸ chief.N)}
    (hWinv : OddOrder.Isaacs.Ch03.IsAInvariant (uActionHom data chief) W) :
    (((caseA_realizedComplement chief W).subgroupOf M).subgroupOf (huSub data)).Normal := by
  refine (Subgroup.normal_subgroupOf_iff_le_normalizer
    (Subgroup.subgroupOf_mono M
      ((caseA_realizedComplement_le_H chief W).trans (le_sup_left : data.H ≤ data.H ⊔ data.U)) :
        ((caseA_realizedComplement chief W).subgroupOf M) ≤ huSub data)).mpr ?_
  -- `huSub = (H⊔U).comap subtype ≤ (normalizer WG).comap subtype ≤ normalizer(WG.subgroupOf M)`.
  have hle : huSub data ≤ (Subgroup.normalizer
      ((caseA_realizedComplement chief W : Subgroup G) : Set G)).comap M.subtype := by
    intro x hx
    rw [Subgroup.mem_comap]
    have hxs : (x : ↥M) ∈ (data.H ⊔ data.U).subgroupOf M := hx
    rw [Subgroup.mem_subgroupOf] at hxs
    exact caseA_realizedComplement_uW_le_normalizer hWinv hxs
  refine hle.trans ?_
  have := Subgroup.le_normalizer_comap (H := (caseA_realizedComplement chief W)) M.subtype
  rwa [show (caseA_realizedComplement chief W).comap M.subtype
    = (caseA_realizedComplement chief W).subgroupOf M from rfl] at this

/-- **Peterfalvi (9.7.a) realized orbit-move (`horbit`).**  For a nontrivial `w₁ ∈ W₁`, conjugation
by `w₁` inside `HU` moves the realized generator summand `S₀` into the realized summand-complement
`W = ⨆_{w∈W₁#} S₀^w` (`caseA_realizedComplement chief (caseA_wComplement caseA)`).

The `H̄`-descent of the concrete conjugation: for `s` in the realized `S₀`, take `x_s : ↥H` with
`mk'(N) x_s ∈ S₀` and `↑x_s = ↑s`; then `w₁·s·w₁⁻¹` realizes
`x = (w₁·(·)·w₁⁻¹) x_s = typeP_conjAction
⟨w₁⟩ x_s`, whose `mk'(N)`-image is `φ(⟨w₁⟩)•(mk'(N) x_s) ∈ φ(⟨w₁⟩)•S₀ = S₀^{w₁}`
(`quotientMulAutHom_apply_mk'`). Since `w₁ ≠ 1`,
`S₀^{w₁} = caseA_wOrbit caseA ⟨w₁⟩ ≤ caseA_wComplement
caseA = W` (`caseA_wComplement` is the join over the nontrivial conjugates).  This is precisely the
`H₁^w ⊆ H₂…H_q` step (`w ∈ W₁#`) of the Coq `injXtheta` (`PFsection9.v` L1233-1253), discharging the
`horbit` hypothesis of `hcrit_of_summand_orbit`. -/
theorem caseA_wOrbit_horbit [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars) :
    ∀ w₁ : ↥M, ((w₁ : ↥M) : G) ∈ data.typeP.W1 → w₁ ≠ 1 →
      ∀ s ∈ ((caseA_realizedComplement chief caseA.S0).subgroupOf M).subgroupOf (huSub data),
        ClassFunction.conjByMulEquiv (H := huSub data) (w₁ : ↥M) s
          ∈ ((caseA_realizedComplement chief (caseA_wComplement caseA)).subgroupOf M).subgroupOf
            (huSub data) := by
  have : chief.N.Normal := chief.N_normal
  intro w₁ hw₁W1 hw₁ne s hs
  -- unpack `s ∈ realized S₀`: get `x_s : ↥H` with `mk'(N) x_s ∈ S₀`, `↑x_s = ↑↑s`.
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf] at hs
  simp only [caseA_realizedComplement, Subgroup.mem_map] at hs
  obtain ⟨x_s, hx_sS0, hx_sval⟩ := hs
  rw [Subgroup.mem_comap, QuotientGroup.mk'_apply] at hx_sS0
  -- `w₁` as an element of `U ⊔ W₁`.
  have hw₁UW1 : ((w₁ : ↥M) : G) ∈ data.typeP.U ⊔ data.typeP.W1 := Subgroup.mem_sup_right hw₁W1
  set a : ↥(data.typeP.U ⊔ data.typeP.W1) := ⟨((w₁ : ↥M) : G), hw₁UW1⟩ with ha
  -- the moved `H`-element.
  set x : ↥data.H := typeP_conjAction data.typeP a x_s with hx
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
  simp only [caseA_realizedComplement, Subgroup.mem_map]
  refine ⟨x, ?_, ?_⟩
  · -- `mk'(N) x ∈ W`.
    rw [Subgroup.mem_comap]
    have hmkx : (QuotientGroup.mk' chief.N) x
        = (quotientMulAutHom chief.N_aInvariant a) ((QuotientGroup.mk' chief.N) x_s) := by
      rw [hx, OddOrder.Isaacs.Ch03.IsAInvariant.quotientMulAutHom_apply_mk']
    rw [hmkx]
    -- `S₀^{w₁} = caseA_wOrbit caseA ⟨w₁⟩ ≤ caseA_wComplement caseA` (`w₁ ≠ 1`).
    have haW1sub : a ∈ data.typeP.W1.subgroupOf (data.typeP.U ⊔ data.typeP.W1) := by
      rw [Subgroup.mem_subgroupOf]; exact hw₁W1
    set awsub : ↥(data.typeP.W1.subgroupOf (data.typeP.U ⊔ data.typeP.W1)) := ⟨a, haW1sub⟩
      with hawsub
    have hawne : awsub ≠ 1 := by
      intro h
      apply hw₁ne
      have ha1 : (awsub : ↥(data.typeP.U ⊔ data.typeP.W1)) = 1 := by rw [h]; rfl
      exact Subtype.ext (congrArg (fun z : ↥(data.typeP.U ⊔ data.typeP.W1) => (z : G)) ha1)
    have hmem_orbit : (quotientMulAutHom chief.N_aInvariant a) ((QuotientGroup.mk' chief.N) x_s)
        ∈ caseA_wOrbit caseA awsub := by
      rw [caseA_wOrbit]
      change (quotientMulAutHom chief.N_aInvariant a) ((QuotientGroup.mk' chief.N) x_s)
        ∈ quotientMulAutHom chief.N_aInvariant ↑awsub • caseA.S0
      rw [hawsub]
      exact Subgroup.smul_mem_pointwise_smul _ _ caseA.S0 hx_sS0
    exact (le_iSup₂ (f := fun w (_ : w ≠ 1) => caseA_wOrbit caseA w) awsub hawne) hmem_orbit
  · -- `↑x = ↑↑(conjByMulEquiv w₁ s)` in `G`.
    rw [Subgroup.coe_subtype, hx, typeP_conjAction_apply, ClassFunction.conjByMulEquiv_apply]
    change (a : G) * (x_s : G) * (a : G)⁻¹
      = ((w₁ : ↥M) : G) * ((s : ↥M) : G) * ((w₁ : ↥M) : G)⁻¹
    have hxs : (x_s : G) = ((s : ↥M) : G) := by rw [← hx_sval]; rfl
    rw [hxs]

/-- **`realized W ⊆ Ker ζ_{θ₁,λ}`** (Peterfalvi (9.8.d) (γ) core (1)): the realized
summand-complement
`W = H₂…H_q` lies in the character kernel of `ζ_{θ₁,λ} = Ind_{H·C_U(S₀)}^{HU}(ψ_{θ₁,λ})`, given
`θ|_W = 1` and `W` `U`-invariant.  Since the pair `ψ_{θ₁,λ}` is `1` on the realized `W`
(`hcuPsiPair_realizedComplement_subset_characterKernel`) and `W ◁ HU`
(`caseA_realizedComplement_subgroupOf_huSub_normal`), the normal subgroup lands in the induced
kernel (`subsetCharacterKernel_induce_of_subgroupOf`).  Direct mirror of
`hcuZetaPair_H0supUprime_subset_ker`.  This is the `H₂…H_q ⊆ Ker χ` of the (9.8.d) `injXtheta`
argument. -/
theorem hcuZetaPair_summandComplement_subset_ker [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars)
    (θ : (↥data.H ⧸ chief.N) →* ℂˣ)
    (hinv : ∀ c : ↥(cuInHu caseA), ∀ h : ↥(hInHu data),
      hcuSeedHom (chief := chief) θ
          ⟨(c : ↥(huSub data)) * (h : ↥(huSub data)) * (c : ↥(huSub data))⁻¹,
            (hInHu_normal data).conj_mem _ h.2 (c : ↥(huSub data))⟩
        = hcuSeedHom (chief := chief) θ h)
    (lam : ↥(cuInHu caseA) →* ℂˣ)
    {W : Subgroup (↥data.H ⧸ chief.N)}
    (hWinv : OddOrder.Isaacs.Ch03.IsAInvariant (uActionHom data chief) W)
    (hθW : ∀ w ∈ W, θ w = 1)
    [Fintype ↥(huSub data)]
    [Finite ↥(hInHu data ⊔ cuInHu caseA)]
    [Invertible (Nat.card ↥(hInHu data ⊔ cuInHu caseA) : ℂ)] :
    (((caseA_realizedComplement chief W).subgroupOf M).subgroupOf (huSub data) :
        Set ↥(huSub data)) ⊆
      OddOrder.Peterfalvi.S03.characterKernel (ClassFunction.induce
        (hInHu data ⊔ cuInHu caseA) (hcuPsiPair caseA θ hinv lam)) := by
  have : Fintype ↥(hInHu data ⊔ cuInHu caseA) := Fintype.ofFinite _
  have := caseA_realizedComplement_subgroupOf_huSub_normal hWinv
  refine OddOrder.Peterfalvi.S03.subsetCharacterKernel_induce_of_subgroupOf
    (A := ((caseA_realizedComplement chief W).subgroupOf M).subgroupOf (huSub data))
    (H := hInHu data ⊔ cuInHu caseA)
    (le_trans (caseA_realizedComplement_subgroupOf_le_hInHu chief W) le_sup_left)
    (hcuPsiPair caseA θ hinv lam) ?_
  -- Bridge: `A.subgroupOf (hInHu⊔cuInHu) = (A.subgroupOf hInHu).map (inclusion)`, then reuse
  -- vanishing.
  have hAle : ((caseA_realizedComplement chief W).subgroupOf M).subgroupOf (huSub data)
      ≤ hInHu data := caseA_realizedComplement_subgroupOf_le_hInHu chief W
  have hbridge : (((caseA_realizedComplement chief W).subgroupOf M).subgroupOf (huSub
      data)).subgroupOf
        (hInHu data ⊔ cuInHu caseA)
      = ((((caseA_realizedComplement chief W).subgroupOf M).subgroupOf (huSub data)).subgroupOf
          (hInHu data)).map
          (Subgroup.inclusion (le_sup_left : hInHu data ≤ hInHu data ⊔ cuInHu caseA)) := by
    ext y
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_map]
    constructor
    · intro hy
      exact ⟨⟨(y : ↥(huSub data)), hAle hy⟩, Subgroup.mem_subgroupOf.mpr hy,
        Subtype.ext (by rw [Subgroup.coe_inclusion])⟩
    · rintro ⟨z, hz, hzeq⟩
      rw [Subgroup.mem_subgroupOf] at hz
      have : ((y : ↥(hInHu data ⊔ cuInHu caseA)) : ↥(huSub data)) = (z : ↥(huSub data)) := by
        rw [← hzeq, Subgroup.coe_inclusion]
      rw [this]; exact hz
  rw [hbridge]
  exact hcuPsiPair_realizedComplement_subset_characterKernel caseA θ hinv lam hθW

set_option maxHeartbeats 1000000 in
-- raised heartbeat budget for the heavy elaboration below
/-- **`H ⊄ Ker ζ_{θ₁,λ}`** (`ζ_{θ₁,λ} ∈ 𝒳`): the irreducible `ζ_{θ₁,λ}` is nontrivial on
`H = hInHu`.  Single-factor mirror of `hcZetaPair_mem_xiSet` — the pair restricts on `hInHu` to the
inflation `θ₀` (`hcuPsiPair_apply_inclusion`), so `H ⊆ Ker` would force `θ = 1`. -/
theorem hcuZetaPair_mem_xiSet [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars)
    (θ : (↥data.H ⧸ chief.N) →* ℂˣ) (hθnt : θ ≠ 1)
    (hinv : ∀ c : ↥(cuInHu caseA), ∀ h : ↥(hInHu data),
      hcuSeedHom (chief := chief) θ
          ⟨(c : ↥(huSub data)) * (h : ↥(huSub data)) * (c : ↥(huSub data))⁻¹,
            (hInHu_normal data).conj_mem _ h.2 (c : ↥(huSub data))⟩
        = hcuSeedHom (chief := chief) θ h)
    (lam : ↥(cuInHu caseA) →* ℂˣ)
    [Fintype ↥(huSub data)]
    [Finite ↥(hInHu data ⊔ cuInHu caseA)]
    [Invertible (Nat.card ↥(huSub data) : ℂ)]
    [Invertible (Nat.card ↥(hInHu data ⊔ cuInHu caseA) : ℂ)]
    [(hInHu data ⊔ cuInHu caseA).Normal]
    (hθ₀ : ClassFunction.inertia (ClassFunction.compHom (hInHuEquivH data).toMonoidHom
        (ClassFunction.compHom (QuotientGroup.mk' chief.N)
          (linearIrreducibleCharacter θ : ClassFunction (↥data.H ⧸ chief.N) ℂ)))
        = hInHu data ⊔ cuInHu caseA) :
    (⟨ClassFunction.induce (hInHu data ⊔ cuInHu caseA) (hcuPsiPair caseA θ hinv lam),
        hcuZetaPair_irreducible caseA θ hinv lam hθ₀⟩ :
        IrreducibleCharacter ↥(huSub data)) ∈ xiSet data := by
  have : Fintype ↥(hInHu data ⊔ cuInHu caseA) := Fintype.ofFinite _
  classical
  set ζ : IrreducibleCharacter ↥(huSub data) :=
    ⟨ClassFunction.induce (hInHu data ⊔ cuInHu caseA) (hcuPsiPair caseA θ hinv lam),
      hcuZetaPair_irreducible caseA θ hinv lam hθ₀⟩ with hζdef
  have hlo : OddOrder.RepresentationTheory.IrreducibleCharacter.LiesOver
      (hInHu data ⊔ cuInHu caseA) ζ (hcuPsiPair caseA θ hinv lam) := by
    rw [← OddOrder.RepresentationTheory.IrreducibleCharacter.inner_induce_ne_zero_iff_liesOver]
    have hcoe : (ζ : ClassFunction ↥(huSub data) ℂ) = ClassFunction.induce
        (hInHu data ⊔ cuInHu caseA) (hcuPsiPair caseA θ hinv lam) := by rw [hζdef]
    rw [← hcoe, OddOrder.RepresentationTheory.irreducibleCharacter_inner_eq_ite ζ ζ, if_pos rfl]
    exact one_ne_zero
  rw [xiSet, Set.mem_ofPred_eq]
  intro hsub
  apply hθnt
  have hfsurj : Function.Surjective
      ((QuotientGroup.mk' chief.N).comp (hInHuEquivH data).toMonoidHom) :=
    (QuotientGroup.mk'_surjective chief.N).comp (hInHuEquivH data).surjective
  refine MonoidHom.ext fun q => ?_
  obtain ⟨h, hhq⟩ := hfsurj q
  have hgmem : ((Subgroup.inclusion
      (le_sup_left : hInHu data ≤ hInHu data ⊔ cuInHu caseA) h :
      ↥(hInHu data ⊔ cuInHu caseA)) : ↥(huSub data)) ∈ hInHu data := by
    rw [Subgroup.coe_inclusion]; exact SetLike.coe_mem h
  have hψker := liesOver_mem_characterKernel hlo (hsub hgmem)
  have hψ1 : (hcuPsiPair caseA θ hinv lam : ClassFunction ↥(hInHu data ⊔ cuInHu caseA) ℂ)
      1 = 1 := by
    simp [hcuPsiPair]
  rw [OddOrder.Peterfalvi.S03.mem_characterKernel, OddOrder.Peterfalvi.S03.characterDegree_def,
    hcuPsiPair_apply_inclusion caseA θ hinv lam h, hψ1,
    ClassFunction.compHom_apply, ClassFunction.compHom_apply, MulEquiv.coe_toMonoidHom,
    linearIrreducibleCharacter_apply] at hψker
  have hqeq : (QuotientGroup.mk' chief.N) ((hInHuEquivH data) h) = q := hhq
  rw [hqeq] at hψker
  change θ q = (1 : ℂˣ)
  refine Units.ext ?_
  rw [Units.val_one]
  exact hψker

set_option maxHeartbeats 1000000 in
-- raised heartbeat budget for the heavy elaboration below
/-- **`ζ_{θ₁,λ} ∈ 𝒳(H₀U')`**: combining `H ⊄ Ker` (`hcuZetaPair_mem_xiSet`) and `H₀U' ⊆ Ker`
(`hcuZetaPair_H0supUprime_subset_ker`).  The source character of the (9.8.d) `𝒮(H₀U')`-member
`Ind_{HU}^M ζ_{θ₁,λ}`.  Single-factor mirror of `hcZetaPair_mem_xiOf`. -/
theorem hcuZetaPair_mem_xiOf [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars)
    (θ : (↥data.H ⧸ chief.N) →* ℂˣ) (hθnt : θ ≠ 1)
    (hinv : ∀ c : ↥(cuInHu caseA), ∀ h : ↥(hInHu data),
      hcuSeedHom (chief := chief) θ
          ⟨(c : ↥(huSub data)) * (h : ↥(huSub data)) * (c : ↥(huSub data))⁻¹,
            (hInHu_normal data).conj_mem _ h.2 (c : ↥(huSub data))⟩
        = hcuSeedHom (chief := chief) θ h)
    (lam : ↥(cuInHu caseA) →* ℂˣ)
    (hlam : ∀ c : ↥(cuInHu caseA),
      (c : ↥(huSub data)) ∈ ((uprimeSub data).subgroupOf M).subgroupOf (huSub data) →
      lam c = 1)
    [Fintype ↥(huSub data)]
    [Finite ↥(hInHu data ⊔ cuInHu caseA)]
    [Invertible (Nat.card ↥(huSub data) : ℂ)]
    [Invertible (Nat.card ↥(hInHu data ⊔ cuInHu caseA) : ℂ)]
    [(hInHu data ⊔ cuInHu caseA).Normal]
    (hθ₀ : ClassFunction.inertia (ClassFunction.compHom (hInHuEquivH data).toMonoidHom
        (ClassFunction.compHom (QuotientGroup.mk' chief.N)
          (linearIrreducibleCharacter θ : ClassFunction (↥data.H ⧸ chief.N) ℂ)))
        = hInHu data ⊔ cuInHu caseA) :
    (⟨ClassFunction.induce (hInHu data ⊔ cuInHu caseA) (hcuPsiPair caseA θ hinv lam),
        hcuZetaPair_irreducible caseA θ hinv lam hθ₀⟩ :
        IrreducibleCharacter ↥(huSub data)) ∈ xiOf data (chief.H0 ⊔ uprimeSub data) := by
  rw [mem_xiOf]
  exact ⟨hcuZetaPair_mem_xiSet caseA θ hθnt hinv lam hθ₀,
    hcuZetaPair_H0supUprime_subset_ker caseA θ hinv lam hlam⟩

/-- **`Ind_{HU}^M ζ_{θ₁,λ} ∈ 𝒮(H₀U')`** (Peterfalvi (9.8.d) membership (iii)): the `M`-induction of
the (9.8.d) source character lies in `𝒮(H₀U')`.  Direct from `hcuZetaPair_mem_xiOf` and the
definition of `sOf` (mirror of `hcZeta_induceHU_mem_sOf`). -/
theorem hcuZetaPair_induceHU_mem_sOf [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars)
    (θ : (↥data.H ⧸ chief.N) →* ℂˣ) (hθnt : θ ≠ 1)
    (hinv : ∀ c : ↥(cuInHu caseA), ∀ h : ↥(hInHu data),
      hcuSeedHom (chief := chief) θ
          ⟨(c : ↥(huSub data)) * (h : ↥(huSub data)) * (c : ↥(huSub data))⁻¹,
            (hInHu_normal data).conj_mem _ h.2 (c : ↥(huSub data))⟩
        = hcuSeedHom (chief := chief) θ h)
    (lam : ↥(cuInHu caseA) →* ℂˣ)
    (hlam : ∀ c : ↥(cuInHu caseA),
      (c : ↥(huSub data)) ∈ ((uprimeSub data).subgroupOf M).subgroupOf (huSub data) →
      lam c = 1)
    [Fintype ↥(huSub data)]
    [Finite ↥(hInHu data ⊔ cuInHu caseA)]
    [Invertible (Nat.card ↥(huSub data) : ℂ)]
    [Invertible (Nat.card ↥(hInHu data ⊔ cuInHu caseA) : ℂ)]
    [(hInHu data ⊔ cuInHu caseA).Normal]
    (hθ₀ : ClassFunction.inertia (ClassFunction.compHom (hInHuEquivH data).toMonoidHom
        (ClassFunction.compHom (QuotientGroup.mk' chief.N)
          (linearIrreducibleCharacter θ : ClassFunction (↥data.H ⧸ chief.N) ℂ)))
        = hInHu data ⊔ cuInHu caseA) :
    induceHU data (ClassFunction.induce (hInHu data ⊔ cuInHu caseA)
        (hcuPsiPair caseA θ hinv lam) : ClassFunction ↥(huSub data) ℂ)
      ∈ sOf data (chief.H0 ⊔ uprimeSub data) := by
  have : Fintype ↥(hInHu data ⊔ cuInHu caseA) := Fintype.ofFinite _
  rw [mem_sOf]
  exact ⟨⟨ClassFunction.induce (hInHu data ⊔ cuInHu caseA) (hcuPsiPair caseA θ hinv lam),
      hcuZetaPair_irreducible caseA θ hinv lam hθ₀⟩,
    hcuZetaPair_mem_xiOf caseA θ hθnt hinv lam hlam hθ₀, rfl⟩

/-- **`Ind_{HU}^M ζ_{θ₁,λ}` is irreducible** (Peterfalvi (9.8.d) (iv), `hIM`-gated).  Given the
source
character `ζ_{θ₁,λ}` is not `W₁`-fixed (`hIM : I_{HU-ambient}(ζ) ≠ ⊤`, i.e. `I_M(ζ) ≠ M`), the
`M`-induction `Ind_{HU}^M ζ` is irreducible. Since `HU ◁ M` with `[M:HU] = q` prime,
`HU ≤ I_M(ζ) ≤ M`
and `I_M(ζ) ≠ M` force `I_M(ζ) = HU` (`eq_of_le_of_prime_index`), whence `Ind` is irreducible
(`isIrreducibleCharacter_induce_of_inertia_eq`). Single-factor mirror of
`hcZeta_induceHU_irreducible`;
its `hIM` is the genuinely-hard `W₁`-free-orbit datum for the `S₀`-supported `θ₁` (see the (9.8.d)
`Still open` note on `caseA_character_counts`), left as an explicit hypothesis. -/
theorem hcuZetaPair_induceHU_irreducible [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars)
    (θ : (↥data.H ⧸ chief.N) →* ℂˣ)
    (hinv : ∀ c : ↥(cuInHu caseA), ∀ h : ↥(hInHu data),
      hcuSeedHom (chief := chief) θ
          ⟨(c : ↥(huSub data)) * (h : ↥(huSub data)) * (c : ↥(huSub data))⁻¹,
            (hInHu_normal data).conj_mem _ h.2 (c : ↥(huSub data))⟩
        = hcuSeedHom (chief := chief) θ h)
    (lam : ↥(cuInHu caseA) →* ℂˣ)
    [Fintype ↥(huSub data)]
    [Finite ↥(hInHu data ⊔ cuInHu caseA)]
    [Invertible (Nat.card ↥(hInHu data ⊔ cuInHu caseA) : ℂ)]
    [(hInHu data ⊔ cuInHu caseA).Normal]
    (hθ₀ : ClassFunction.inertia (ClassFunction.compHom (hInHuEquivH data).toMonoidHom
        (ClassFunction.compHom (QuotientGroup.mk' chief.N)
          (linearIrreducibleCharacter θ : ClassFunction (↥data.H ⧸ chief.N) ℂ)))
        = hInHu data ⊔ cuInHu caseA)
    (hIM : ClassFunction.inertia (ClassFunction.induce (hInHu data ⊔ cuInHu caseA)
        (hcuPsiPair caseA θ hinv lam) : ClassFunction ↥(huSub data) ℂ) ≠ ⊤) :
    IsIrreducibleCharacter (induceHU data (ClassFunction.induce (hInHu data ⊔ cuInHu caseA)
      (hcuPsiPair caseA θ hinv lam) : ClassFunction ↥(huSub data) ℂ)) := by
  have : Fintype ↥(hInHu data ⊔ cuInHu caseA) := Fintype.ofFinite _
  let : Fintype ↥M := Fintype.ofFinite _
  let : Invertible (Nat.card ↥(huSub data) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  let : Invertible (Nat.card ↥M : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have hIeq : ClassFunction.inertia (ClassFunction.induce (hInHu data ⊔ cuInHu caseA)
      (hcuPsiPair caseA θ hinv lam) : ClassFunction ↥(huSub data) ℂ) = huSub data := by
    refine eq_of_le_of_prime_index (ClassFunction.subgroup_le_inertia _) ?_ hIM
    rw [huSub_index_eq_q]; exact data.nontrivial.2.1
  exact isIrreducibleCharacter_induce_of_inertia_eq
    (⟨ClassFunction.induce (hInHu data ⊔ cuInHu caseA) (hcuPsiPair caseA θ hinv lam),
      hcuZetaPair_irreducible caseA θ hinv lam hθ₀⟩ : IrreducibleCharacter ↥(huSub data)) hIeq

/-- **A nontrivial linear character of the chief factor exists**: `H̄` is a nontrivial finite
abelian group, so `|Hom(H̄, ℂˣ)| = |H̄| > 1` (`card_monoidHom_of_hasEnoughRootsOfUnity`).
Supplies the `θ ≠ 1` seed of the (9.9.c) pair character in Clifford case (b) (where no regular
character is needed — `inertia_eq_hcInHu` takes any nontrivial `θ`). -/
theorem exists_chiefFactorHom_ne_one [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data) :
    ∃ θ : (↥data.H ⧸ chief.N) →* ℂˣ, θ ≠ 1 := by
  have := chief.N_normal
  let : CommGroup (↥data.H ⧸ chief.N) :=
    { (inferInstance : Group (↥data.H ⧸ chief.N)) with
      mul_comm := chief.quotient_elementaryAbelian.1 }
  have : Nontrivial (↥data.H ⧸ chief.N) := by
    obtain ⟨x, hxH, hxnot⟩ := SetLike.exists_of_lt chief.H0_lt_H
    refine ⟨⟨QuotientGroup.mk ⟨x, hxH⟩, 1, ?_⟩⟩
    rw [ne_eq, QuotientGroup.eq_one_iff]
    intro hmem
    exact hxnot (chief.H0_eq ▸ Subgroup.mem_map.mpr ⟨_, hmem, rfl⟩)
  have : NeZero (Monoid.exponent (↥data.H ⧸ chief.N)) := ⟨Monoid.exponent_ne_zero_of_finite⟩
  have hcard : Nat.card ((↥data.H ⧸ chief.N) →* ℂˣ) = Nat.card (↥data.H ⧸ chief.N) :=
    CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity _ ℂ
  have : Nontrivial ((↥data.H ⧸ chief.N) →* ℂˣ) := by
    rw [← Finite.one_lt_card_iff_nontrivial, hcard]
    exact Finite.one_lt_card_iff_nontrivial.mpr ‹_›
  obtain ⟨f, g, hfg⟩ := exists_pair_ne ((↥data.H ⧸ chief.N) →* ℂˣ)
  rcases eq_or_ne f 1 with rfl | hf
  · exact ⟨g, (Ne.symm hfg)⟩
  · exact ⟨f, hf⟩

/-- **The realization iso `cInHu ≃* C`** (`G`-value preserving): the doubly-realized
`C = C_U(H̄)` inside `HU` is isomorphic to the `G`-level `cSub`. -/
noncomputable def cInHuEquivC {M : Subgroup G} (data : TypesIIIIIIVSetup M)
    (chief : ChiefFactorData data) :
    ↥(cInHu data chief) ≃* ↥(cSub data chief) :=
  (Subgroup.subgroupOfEquivOfLe (Subgroup.subgroupOf_mono M
      (le_trans (cSub_le_U data chief) le_sup_right))).trans
    (Subgroup.subgroupOfEquivOfLe ((cSub_le_U data chief).trans (U_le_M data)))

theorem cInHuEquivC_coe {M : Subgroup G} (data : TypesIIIIIIVSetup M)
    (chief : ChiefFactorData data) (c : ↥(cInHu data chief)) :
    ((cInHuEquivC data chief c : ↥(cSub data chief)) : G)
      = (((c : ↥(huSub data)) : ↥M) : G) := rfl

/-- **A `C'`-trivial nontrivial linear character of `C` exists** (`C ≠ 1`): `C` is a nontrivial
solvable group (subgroup of the solvable maximal `M`), so its abelianization is nontrivial
(`Group.IsSolvable.commutator_lt_top_of_nontrivial`) and carries `|C/C'| > 1` linear characters; any
of them kills every element of the realized `C' = ⁅C,C⁆` (commutators die in an abelian
target).  Supplies the `λ` of the (9.9.c) pair character together with its `hlam` kernel
hypothesis. -/
theorem exists_cInHuHom_ne_one [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data)
    (hC : cSub data chief ≠ ⊥) :
    ∃ lam : ↥(cInHu data chief) →* ℂˣ, lam ≠ 1 ∧
      ∀ c : ↥(cInHu data chief),
        (c : ↥(huSub data)) ∈ ((cprimeSub data chief).subgroupOf M).subgroupOf (huSub data) →
        lam c = 1 := by
  classical
  -- `cInHu` is a nontrivial finite solvable group.
  have : Group.IsSolvable ↥M := hG.isSolvable_of_mem_maximalSubgroups data.maximal
  have : Group.IsSolvable ↥(cInHu data chief) :=
    Group.isSolvable_of_isSolvable_injective (f := (huSub data).subtype.comp
      (cInHu data chief).subtype)
      ((huSub data).subtype_injective.comp (cInHu data chief).subtype_injective)
  have : Nontrivial ↥(cSub data chief) := (Subgroup.nontrivial_iff_ne_bot _).mpr hC
  have : Nontrivial ↥(cInHu data chief) := (cInHuEquivC data chief).toEquiv.nontrivial
  -- the abelianization is nontrivial, so it has more than one linear character.
  have hlt : commutator ↥(cInHu data chief) < ⊤ :=
    Group.IsSolvable.commutator_lt_top_of_nontrivial ↥(cInHu data chief)
  have : Nontrivial (Abelianization ↥(cInHu data chief)) := by
    obtain ⟨x, -, hxnot⟩ := SetLike.exists_of_lt hlt
    exact ⟨⟨Abelianization.of x, 1, fun h => hxnot ((QuotientGroup.eq_one_iff x).mp h)⟩⟩
  have : NeZero (Monoid.exponent (Abelianization ↥(cInHu data chief))) :=
    ⟨Monoid.exponent_ne_zero_of_finite⟩
  have hcard : Nat.card (Abelianization ↥(cInHu data chief) →* ℂˣ)
      = Nat.card (Abelianization ↥(cInHu data chief)) :=
    CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity _ ℂ
  have : Nontrivial (Abelianization ↥(cInHu data chief) →* ℂˣ) := by
    rw [← Finite.one_lt_card_iff_nontrivial, hcard]
    exact Finite.one_lt_card_iff_nontrivial.mpr ‹_›
  have hf : ∃ f : Abelianization ↥(cInHu data chief) →* ℂˣ, f ≠ 1 := by
    obtain ⟨f, g, hfg⟩ := exists_pair_ne (Abelianization ↥(cInHu data chief) →* ℂˣ)
    rcases eq_or_ne f 1 with rfl | hf
    · exact ⟨g, (Ne.symm hfg)⟩
    · exact ⟨f, hf⟩
  obtain ⟨f, hf⟩ := hf
  refine ⟨f.comp Abelianization.of, ?_, ?_⟩
  · intro h1
    apply hf
    have hsurj : Function.Surjective ((Abelianization.of :
        ↥(cInHu data chief) →* Abelianization ↥(cInHu data chief))) := fun a =>
      QuotientGroup.mk_surjective a
    exact (MonoidHom.cancel_right hsurj).mp
      (h1.trans (MonoidHom.one_comp Abelianization.of).symm)
  · intro c hc
    -- `c` corresponds under the realization iso to an element of `commutator ↥C`.
    have hcG : (((c : ↥(huSub data)) : ↥M) : G) ∈ cprimeSub data chief :=
      Subgroup.mem_subgroupOf.mp (Subgroup.mem_subgroupOf.mp hc)
    obtain ⟨y, hy, hyval⟩ := Subgroup.mem_map.mp (by
      rw [show cprimeSub data chief
          = (commutator ↥(cSub data chief)).map (cSub data chief).subtype from rfl] at hcG
      exact hcG)
    have hceq : cInHuEquivC data chief c = y :=
      Subtype.ext ((cInHuEquivC_coe data chief c).trans hyval.symm)
    have hcsymm : c = (cInHuEquivC data chief).symm y := by
      rw [← hceq, MulEquiv.symm_apply_apply]
    have hccomm : c ∈ commutator ↥(cInHu data chief) := by
      have hmapped : (commutator ↥(cSub data chief)).map
          (cInHuEquivC data chief).symm.toMonoidHom = commutator ↥(cInHu data chief) := by
        rw [commutator_def, commutator_def, Subgroup.map_commutator,
          Subgroup.map_top_of_surjective _ (cInHuEquivC data chief).symm.surjective]
      rw [hcsymm, ← hmapped]
      exact Subgroup.mem_map.mpr ⟨y, hy, rfl⟩
    rw [MonoidHom.comp_apply,
      show (Abelianization.of c : Abelianization ↥(cInHu data chief))
        = QuotientGroup.mk c from rfl,
      (QuotientGroup.eq_one_iff c).mpr hccomm]
    exact map_one f

/-- **`ψ_{θ,λ}|_C = λ`** (pointwise): on the inclusion of `c ∈ cInHu` into `HC` the pair hom
returns `λ c` — the `θ`-factor dies on `C ≤ H₀C` (`hcHom_eq_one_of_mem_realizedH0supC`).
The (9.9.c) lever: `C ⊆ Ker ψ_{θ,λ}` forces `λ = 1`. -/
theorem hcPairHom_inclusion_cInHu [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data)
    (θ : (↥data.H ⧸ chief.N) →* ℂˣ) (lam : ↥(cInHu data chief) →* ℂˣ)
    (c : ↥(cInHu data chief)) :
    hcPairHom chief θ lam (Subgroup.inclusion (cInHu_le_hcRealized chief) c) = lam c := by
  have hmemHC : Subgroup.inclusion (cInHu_le_hcRealized chief) c
      ∈ ((((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)).subgroupOf
        (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))) := by
    refine Subgroup.mem_subgroupOf.mpr ?_
    exact Subgroup.subgroupOf_mono _ (Subgroup.subgroupOf_mono _ le_sup_right) c.2
  have hθfac : θ.comp (hcHom chief) (Subgroup.inclusion (cInHu_le_hcRealized chief) c) = 1 := by
    rw [MonoidHom.comp_apply, hcHom_eq_one_of_mem_realizedH0supC chief hmemHC, map_one]
  simp only [hcPairHom, MonoidHom.mul_apply, hθfac, one_mul,
    hcLambdaHom_inclusion chief lam c]

set_option maxHeartbeats 1000000 in
-- raised heartbeat budget for the heavy elaboration below
/-- **`C ⊆ Ker ζ_{θ,λ}` forces `λ = 1`** (the (9.9.c) rigidity): if the realized `C` lies in
the kernel of `ζ_{θ,λ} = Ind_{HC}^{HU}(ψ_{θ,λ})`, then kernel descent
(`mem_characterKernel_of_mem_characterKernel_induce`, `HC ◁ HU`) puts `C` in the kernel of the
pair itself, whose `C`-restriction is `λ` (`hcPairHom_inclusion_cInHu`). -/
theorem lam_eq_one_of_cInHu_subset_ker_zetaPair [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data)
    (θ : (↥data.H ⧸ chief.N) →* ℂˣ) (lam : ↥(cInHu data chief) →* ℂˣ)
    [Fintype ↥(huSub data)]
    [Finite ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))]
    [Invertible (Nat.card ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
      (huSub data)) : ℂ)]
    (hker : ∀ z : ↥(huSub data), z ∈ cInHu data chief →
      z ∈ OddOrder.Peterfalvi.S03.characterKernel (ClassFunction.induce
        (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))
        (hcPsiPair chief θ lam : ClassFunction
          ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
            (huSub data)) ℂ)))
    (c : ↥(cInHu data chief)) : lam c = 1 := by
  have : Fintype ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
      (huSub data)) := Fintype.ofFinite _
  have : (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
      (huSub data)).Normal := hcInHu_realized_normal chief
  have hdesc := OddOrder.Peterfalvi.S03.mem_characterKernel_of_mem_characterKernel_induce
    (L := ↥(huSub data))
    (H := hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))
    (hcPsiPair chief θ lam).isIrreducible
    (cInHu_le_hcRealized chief c.2) (hker (c : ↥(huSub data)) c.2)
  rw [OddOrder.Peterfalvi.S03.mem_characterKernel,
    OddOrder.Peterfalvi.S03.characterDegree_def] at hdesc
  have hint : (⟨(c : ↥(huSub data)), cInHu_le_hcRealized chief c.2⟩ :
      ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)))
      = Subgroup.inclusion (cInHu_le_hcRealized chief) c := rfl
  rw [hint] at hdesc
  have hpair1 : (hcPsiPair chief θ lam : ClassFunction
      ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)) ℂ)
      1 = 1 := by simp [hcPsiPair]
  rw [hpair1] at hdesc
  refine Units.ext ?_
  rw [Units.val_one, ← hdesc]
  simp only [hcPsiPair, linearIrreducibleCharacter_apply, hcPairHom_inclusion_cInHu chief θ lam c]

set_option maxHeartbeats 1000000 in
-- raised heartbeat budget for the heavy elaboration below
/-- **Peterfalvi (9.9.c), the `C = 1` half**: in Clifford case (b), if `𝒮(H₀C')` contains no
irreducible character then `C = ⊥`.  Otherwise take `θ ≠ 1` on `H̄`
(`exists_chiefFactorHom_ne_one`) and `λ ≠ 1` on `C` trivial on `C'`
(`exists_cInHuHom_ne_one`): the pair induction `φ = Ind_{HU}^M ζ_{θ,λ}` lies in `𝒮(H₀C')`
(`hcZetaPair_mem_xiOf`), is reducible by the hypothesis, hence lies in `𝒮(H₀C)`
(`reducible_mem_sOf_H0C`, (9.9.b)); its source is then `M`-conjugate to a `𝒳(H₀C)`-member
(`induce_eq_induce_iff_conj`), so `C ⊆ H₀C ⊆ Ker ζ_{θ,λ}` (`H₀C ◁ M` transports the kernel
along the conjugation), forcing `λ = 1` (`lam_eq_one_of_cInHu_subset_ker_zetaPair`) —
contradiction. -/
theorem caseB_no_irreducible_forces_C_bot [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    (chars : Section11CharacterData data chief) (caseB : CliffordCaseBData chars)
    (hno : ¬ ∃ χ ∈ chars.SOf (chief.H0 ⊔ chars.Cprime), IsIrreducibleCharacter χ) :
    chars.C = ⊥ := by
  classical
  by_contra hC
  let : Fintype ↥M := Fintype.ofFinite _
  let : Fintype ↥(huSub data) := Fintype.ofFinite _
  let : Fintype ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
    (huSub data)) := Fintype.ofFinite _
  let : Invertible (Nat.card ↥M : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  let : Invertible (Nat.card ↥(huSub data) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  let : Invertible (Nat.card ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf
    M).subgroupOf (huSub data)) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have : (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
    (huSub data)).Normal := hcInHu_realized_normal chief
  obtain ⟨θ, hθne⟩ := exists_chiefFactorHom_ne_one chief
  obtain ⟨lam, hlamne, hlam⟩ := exists_cInHuHom_ne_one hG chief hC
  have hθbarnt : (linearIrreducibleCharacter θ : ClassFunction (↥data.H ⧸ chief.N) ℂ)
      ≠ trivialClassFunction _ := by
    intro h0
    apply hθne
    rw [← linearIrreducibleCharacter_eq_trivial_iff]
    exact IrreducibleCharacter.ext
      (h0.trans (IrreducibleCharacter.coe_trivialIrreducibleCharacter).symm)
  have hθ₀ := inertia_eq_hcInHu data chief caseB.actsIrreducibly hθbarnt
  set ζp : IrreducibleCharacter ↥(huSub data) :=
    ⟨ClassFunction.induce
      (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))
      (hcPsiPair chief θ lam), hcZetaPair_irreducible chief θ lam hθ₀⟩ with hζpdef
  have hζpX : ζp ∈ xiOf data (chief.H0 ⊔ cprimeSub data chief) :=
    hcZetaPair_mem_xiOf chief θ hθne lam hlam hθ₀
  have hφmem : induceHU data (ζp : ClassFunction ↥(huSub data) ℂ)
      ∈ sOf data (chief.H0 ⊔ cprimeSub data chief) :=
    mem_sOf.mpr ⟨ζp, hζpX, rfl⟩
  have hred : ¬ IsIrreducibleCharacter (induceHU data (ζp : ClassFunction ↥(huSub data) ℂ)) :=
    fun hirr => hno ⟨induceHU data (ζp : ClassFunction ↥(huSub data) ℂ), hφmem, hirr⟩
  have hφH0 : induceHU data (ζp : ClassFunction ↥(huSub data) ℂ) ∈ sOf data chief.H0 :=
    sOf_antitone data le_sup_left hφmem
  have hφH0C := reducible_mem_sOf_H0C hG chars _ hφH0 hred
  obtain ⟨ζ', hζ'X, hφeq⟩ := mem_sOf.mp hφH0C
  obtain ⟨w, hw⟩ := (OddOrder.RepresentationTheory.induce_eq_induce_iff_conj
    (G := ↥M) (H := huSub data) ζp ζ').mp hφeq
  have hH0Cnormal := chiefFactor_H0supC_subgroupOf_normal chief
  have hCker : ∀ z : ↥(huSub data), z ∈ cInHu data chief →
      z ∈ OddOrder.Peterfalvi.S03.characterKernel (ζp : ClassFunction ↥(huSub data) ℂ) := by
    intro z hz
    have hzH0C : (z : ↥M) ∈ (chief.H0 ⊔ cSub data chief).subgroupOf M :=
      Subgroup.subgroupOf_mono _ le_sup_right (Subgroup.mem_subgroupOf.mp hz)
    have hymem : w⁻¹ * (z : ↥M) * w ∈ huSub data := by
      simpa using (huSub_normal data).conj_mem _ z.2 w⁻¹
    have hyH0C : (⟨w⁻¹ * (z : ↥M) * w, hymem⟩ : ↥(huSub data))
        ∈ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data) := by
      refine Subgroup.mem_subgroupOf.mpr ?_
      simpa using hH0Cnormal.conj_mem _ hzH0C w⁻¹
    have hyker : (⟨w⁻¹ * (z : ↥M) * w, hymem⟩ : ↥(huSub data))
        ∈ OddOrder.Peterfalvi.S03.characterKernel
          (ζ' : ClassFunction ↥(huSub data) ℂ) := hζ'X.2 hyH0C
    have hval : (ζ' : ClassFunction ↥(huSub data) ℂ) ⟨w⁻¹ * (z : ↥M) * w, hymem⟩
        = (ζp : ClassFunction ↥(huSub data) ℂ) z := by
      rw [← hw, IrreducibleCharacter.coe_conjBy, ClassFunction.conjBy_apply]
      exact congrArg _ (Subtype.ext
        (show w * (w⁻¹ * (z : ↥M) * w) * w⁻¹ = (z : ↥M) by group))
    have hone : (ζ' : ClassFunction ↥(huSub data) ℂ) 1
        = (ζp : ClassFunction ↥(huSub data) ℂ) 1 := by
      rw [← hw, IrreducibleCharacter.coe_conjBy, ClassFunction.conjBy_apply]
      exact congrArg _ (Subtype.ext (by simp))
    rw [OddOrder.Peterfalvi.S03.mem_characterKernel,
      OddOrder.Peterfalvi.S03.characterDegree_def] at hyker ⊢
    exact hval.symm.trans (hyker.trans hone)
  have hlam1 : ∀ c : ↥(cInHu data chief), lam c = 1 := by
    intro c
    exact lam_eq_one_of_cInHu_subset_ker_zetaPair chief θ lam (fun z hz => hCker z hz) c
  obtain ⟨c₀, hc₀⟩ := DFunLike.ne_iff.mp hlamne
  exact hc₀ (by rw [hlam1 c₀, MonoidHom.one_apply])

/-- **Inertia index of `hcPsi θ` is `u`** (regular `θ`): for a regular seed `θ` (nontrivial on each
Clifford factor `Hpart i`), the `HU`-inertia of `ζ_θ = hcPsi θ` is `HC` (`hcPsi_inertia_eq_hc` with
the
`inertia_eq_hcInHu_caseA` seed), so `[HU : I_{HU}(hcPsi θ)] = [HU:HC] = u` (`hc_index_eq_u`). This
is
the uniform fibre size `[HU : I]` of the induction map `θ ↦ Ind_{HC}^{HU}(hcPsi θ)` in the `oXtheta`
`u`-to-1 count (each `HU`-conjugation orbit of a regular `hcPsi θ` has `u` elements). -/
theorem hcPsi_inertia_index_eq_u [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars)
    {θ : (↥data.H ⧸ chief.N) →* ℂˣ}
    (hreg : ∀ i, ∃ x ∈ caseA.Hpart i, θ x ≠ 1)
    [(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)).Normal] :
    (IrreducibleCharacter.inertia (hcPsi chief θ)).index = chars.u := by
  have hreg' : ∀ i, ∃ x ∈ caseA.Hpart i,
      (linearIrreducibleCharacter θ : ClassFunction (↥data.H ⧸ chief.N) ℂ) x
        ≠ (linearIrreducibleCharacter θ : ClassFunction (↥data.H ⧸ chief.N) ℂ) 1 := by
    intro i
    obtain ⟨x, hx, hne⟩ := hreg i
    refine ⟨x, hx, ?_⟩
    rw [linearIrreducibleCharacter_apply, linearIrreducibleCharacter_apply, map_one, Units.val_one]
    simpa using hne
  have hθ₀ := inertia_eq_hcInHu_caseA data chief caseA hreg'
  change (ClassFunction.inertia (hcPsi chief θ : ClassFunction
    ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)) ℂ)).index
      = chars.u
  rw [hcPsi_inertia_eq_hc chief θ hθ₀, hc_index_eq_u chars]

/-- **Descent of `HU`-conjugation to `H̄`.**  For `g ∈ HU`, conjugation by `g` on `HC` preserves
`ker hcHom = H₀C` (`H₀C ◁ HU`, `realizedH0supC_normal_huSub`), so it descends through `hcHom` to an
endomorphism `A_g` of `H̄`: `QuotientGroup.map` on `HC/H₀C` transported by the second iso
`hcQuotientEquivHbar`.  Satisfies `A_g ∘ hcHom = hcHom ∘ (conjBy g)` (`hcHom_hcConjDescend`), the
factoring behind the conjugation-commute `conjBy g (hcPsi θ) = hcPsi (θ ∘ A_g)`. -/
noncomputable def hcConjDescend [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data) (g : ↥(huSub data))
    [(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)).Normal] :
    (↥data.H ⧸ chief.N) →* (↥data.H ⧸ chief.N) :=
  letI hK : ((((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)).subgroupOf
      (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))).Normal :=
    (realizedH0supC_normal_huSub chief).subgroupOf _
  (hcQuotientEquivHbar chief).toMonoidHom.comp
    ((QuotientGroup.map
        ((((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)).subgroupOf
          (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)))
        ((((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)).subgroupOf
          (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)))
        (ClassFunction.conjByMulEquiv g).toMonoidHom
        (by
          intro x hx
          simp only [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, Subgroup.mem_subgroupOf,
            ClassFunction.conjByMulEquiv_apply] at hx ⊢
          exact (realizedH0supC_normal_huSub chief).conj_mem _ hx g)).comp
      (hcQuotientEquivHbar chief).symm.toMonoidHom)

/-- **Factoring `A_g ∘ hcHom = hcHom ∘ conjBy g`**: `A_g (hcHom x) = hcHom (g·x·g⁻¹)`.  Unwinding
`A_g = iso ∘ QuotientGroup.map ∘ iso⁻¹` and `hcHom = iso ∘ mk'`, the `iso⁻¹∘iso` cancels and
`QuotientGroup.map_mk'` turns `map (mk' x)` into `mk' (conjBy g x)`.  The pointwise identity behind
the conjugation-commute `conjBy g (hcPsi θ) = hcPsi (θ ∘ A_g)`. -/
theorem hcConjDescend_hcHom [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data) (g : ↥(huSub data))
    [(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)).Normal]
    (x : ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))) :
    hcConjDescend chief g (hcHom chief x) = hcHom chief (ClassFunction.conjByMulEquiv g x) := by
  let hK : ((((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)).subgroupOf
      (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))).Normal :=
    (realizedH0supC_normal_huSub chief).subgroupOf _
  simp only [hcConjDescend, hcHom, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.symm_apply_apply, QuotientGroup.map_mk']
  rw [QuotientGroup.mk'_apply]

/-- **Conjugation-commute for `hcPsi`**: `conjBy g (hcPsi θ) = hcPsi (θ ∘ A_g)` for `g ∈ HU`, where
`A_g = hcConjDescend g`.  Pointwise: `(conjBy g (hcPsi θ)) y = (hcPsi θ)(g·y·g⁻¹) =
θ(hcHom(g·y·g⁻¹))
= θ(A_g(hcHom y)) = (hcPsi (θ∘A_g)) y`, using the factoring `hcConjDescend_hcHom`.  This is the
`HU`-conjugation ↔ `Ū`-precomposition equivariance: the `HU`-orbit of `hcPsi θ` consists of the
`hcPsi (θ∘A_g)`, so the regular-inflated set is conjugation-closed (modulo the case-A regularity of
`θ∘A_g`) — the `T`-invariance input to the `oXtheta` `card_filter` count. -/
theorem hcPsi_conjBy_eq [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data) (g : ↥(huSub data))
    (θ : (↥data.H ⧸ chief.N) →* ℂˣ)
    [(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)).Normal] :
    ClassFunction.conjBy g (hcPsi chief θ : ClassFunction
        ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)) ℂ)
      = (hcPsi chief (θ.comp (hcConjDescend chief g)) : ClassFunction
        ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)) ℂ) := by
  ext y
  have hval : ClassFunction.conjBy g (hcPsi chief θ : ClassFunction
      ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)) ℂ) y
      = (hcPsi chief θ : ClassFunction
        ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)) ℂ)
        (ClassFunction.conjByMulEquiv g y) := rfl
  rw [hval]
  simp only [hcPsi, linearIrreducibleCharacter_apply, MonoidHom.comp_apply, hcConjDescend_hcHom]

/-- **`A_g = hcConjDescend g` is bijective** (an automorphism of `H̄`), with inverse
`A_{g⁻¹}`: `A_g(A_{g⁻¹} z) = z` and `A_{g⁻¹}(A_g z) = z` by the factoring `hcConjDescend_hcHom`
(`hcHom` surjective) and `g·(g⁻¹·y·g)·g⁻¹ = y`.  Together with `A_g(Hpart i) ⊆ Hpart i` (case-A
`Hpart_aInvariant`, the `U`-action factor-preservation) this gives `A_g(Hpart i) = Hpart i`, hence
`θ ∘ A_g` regular ⟺ `θ` regular — the regularity half of the `oXtheta` `T`-invariance. -/
theorem hcConjDescend_bijective [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data) (g : ↥(huSub data))
    [(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)).Normal] :
    Function.Bijective (hcConjDescend chief g) := by
  refine Function.bijective_iff_has_inverse.mpr ⟨hcConjDescend chief g⁻¹, ?_, ?_⟩ <;>
  · intro z
    obtain ⟨x, rfl⟩ := hcHom_surjective chief z
    rw [hcConjDescend_hcHom, hcConjDescend_hcHom]
    congr 1
    apply Subtype.ext
    simp only [ClassFunction.conjByMulEquiv_apply]
    group

/-- **`A_g = id` for `g ∈ HC`**: conjugation by an `HC`-element descends to the identity on `H̄`,
because `H̄ = H/N` is abelian and `hcHom` is a homomorphism, so `hcHom(g·x·g⁻¹) = hcHom x`.  Since
`HC ⊇ hInHu` (the `H`-part of `HU`) and `HC ⊇ C`, the nontrivial part of `A_·` factors through
`HU/HC ≅ Ū`.  Reduces the case-A factor-preservation `A_g(Hpart i) ⊆ Hpart i` to the `U`-part
(realizable in `U ⊔ W₁`), where it is the `uActionHom` action (`Hpart_aInvariant`). -/
theorem hcConjDescend_eq_id_of_mem_hc [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data) {g : ↥(huSub data)}
    [(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)).Normal]
    (hg : g ∈ hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)) :
    hcConjDescend chief g = MonoidHom.id (↥data.H ⧸ chief.N) := by
  refine MonoidHom.ext fun z => ?_
  obtain ⟨x, hx⟩ := hcHom_surjective chief z
  rw [← hx, hcConjDescend_hcHom, MonoidHom.id_apply]
  have hconj : ClassFunction.conjByMulEquiv g x
      = (⟨g, hg⟩ : ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
          (huSub data))) * x * (⟨g, hg⟩)⁻¹ := by
    apply Subtype.ext
    simp [ClassFunction.conjByMulEquiv_apply]
  rw [hconj, map_mul, map_mul, map_inv,
    chief.quotient_elementaryAbelian.comm (hcHom chief ⟨g, hg⟩) (hcHom chief x),
    mul_assoc, mul_inv_cancel, mul_one]

/-- **`A_·` is multiplicative**: `A_{g₁·g₂} = A_{g₁} ∘ A_{g₂}` (conjugation is a homomorphism into
`End(H̄)`, preserved by the `QuotientGroup.map` transport).  With `hcConjDescend_eq_id_of_mem_hc`
(`A_h = id` for `h ∈ HC`) this reduces `A_g` for `g = h·u ∈ HU` (`h ∈ hInHu`, `u ∈ uInHu`) to the
`U`-part `A_u`, giving the case-A factor-preservation from `Hpart_aInvariant`. -/
theorem hcConjDescend_mul [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data) (g₁ g₂ : ↥(huSub data))
    [(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)).Normal] :
    hcConjDescend chief (g₁ * g₂)
      = (hcConjDescend chief g₁).comp (hcConjDescend chief g₂) := by
  refine MonoidHom.ext fun z => ?_
  obtain ⟨x, hx⟩ := hcHom_surjective chief z
  rw [← hx, MonoidHom.comp_apply, hcConjDescend_hcHom, hcConjDescend_hcHom, hcConjDescend_hcHom]
  congr 1
  apply Subtype.ext
  simp only [ClassFunction.conjByMulEquiv_apply]
  group

/-- **`A_u = uActionHom(a)` for a `U`-part element `u ∈ uInHu`** (P3 of the case-A
factor-preservation).  For `u ∈ uInHu` (a realized `U`-element inside `HU`), the descended
conjugation `A_u = hcConjDescend u` agrees on `H̄ = H/N` with the abstract `U`-action
`uActionHom data chief a`, where `a` is the realization of `u` in `↥(U.subgroupOf (U ⊔ W₁))`.
Both descend the conjugation `x ↦ u·x·u⁻¹` to `H̄`, matched pointwise by the shared `G`-value
`u_G·h_G·u_G⁻¹`: on the left via `hcHom_inclusion` (`hcHom` on the `H`-part is
`mk'_N ∘ hInHuEquivH`)
and the factoring `hcConjDescend_hcHom`, on the right via `quotientMulAutHom_apply_mk'` and
`typeP_conjAction_apply`.  Combined with `hcConjDescend_mul`/`hcConjDescend_eq_id_of_mem_hc` (the
`H`-part `A_h` is the identity), this reduces the case-A factor-preservation
`A_g(Hpart i) ⊆ Hpart i`
to the `U`-invariance `Hpart_aInvariant`. -/
theorem hcConjDescend_eq_uActionHom [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data) {u : ↥(huSub data)}
    [(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)).Normal]
    (hu : u ∈ uInHu data) :
    ∃ a, ∀ z, hcConjDescend chief u z = uActionHom data chief a z := by
  have huU : ((u : ↥M) : G) ∈ data.typeP.U :=
    Subgroup.mem_subgroupOf.mp (Subgroup.mem_subgroupOf.mp hu)
  set x₀ : ↥(data.typeP.U ⊔ data.typeP.W1) := ⟨((u : ↥M) : G), Subgroup.mem_sup_left huU⟩ with hx₀
  refine ⟨⟨x₀, Subgroup.mem_subgroupOf.mpr huU⟩, fun z => ?_⟩
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective chief.N z
  obtain ⟨h, rfl⟩ := (hInHuEquivH data).surjective y
  -- right side: the abstract `U`-action descends `mk'_N` to `typeP_conjAction x₀`
  have hRHS : uActionHom data chief ⟨x₀, Subgroup.mem_subgroupOf.mpr huU⟩
        (QuotientGroup.mk' chief.N (hInHuEquivH data h))
      = QuotientGroup.mk' chief.N (typeP_conjAction data.typeP x₀ (hInHuEquivH data h)) := by
    change (quotientMulAutHom chief.N_aInvariant) x₀
        (QuotientGroup.mk' chief.N (hInHuEquivH data h)) = _
    rw [OddOrder.Isaacs.Ch03.IsAInvariant.quotientMulAutHom_apply_mk']
  -- left side: `A_u ∘ hcHom` = `hcHom ∘ conjBy u`, and the conjugate lands in `hInHu`
  have hmem' : (u : ↥(huSub data)) * (h : ↥(huSub data)) * (u : ↥(huSub data))⁻¹ ∈ hInHu data :=
    (hInHu_normal data).conj_mem (h : ↥(huSub data)) h.2 (u : ↥(huSub data))
  have hincl : (ClassFunction.conjByMulEquiv u (Subgroup.inclusion le_sup_left h)
      : ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)))
      = Subgroup.inclusion le_sup_left ⟨_, hmem'⟩ := by
    apply Subtype.ext
    rw [ClassFunction.conjByMulEquiv_apply, Subgroup.coe_inclusion, Subgroup.coe_inclusion]
  rw [hRHS, ← hcHom_inclusion chief h, hcConjDescend_hcHom, hincl, hcHom_inclusion]
  -- both sides are `mk'_N` of the same `H`-element (equal `G`-value `u_G·h_G·u_G⁻¹`)
  refine congrArg (QuotientGroup.mk' chief.N) (Subtype.ext ?_)
  simp only [hInHuEquivH_coe, typeP_conjAction_apply, hx₀, Subgroup.coe_mul, Subgroup.coe_inv]

/-- **Case-A factor-preservation: `A_g` maps each Clifford summand `Hpart i` into itself.**  For any
`g ∈ HU`, the descended conjugation `A_g = hcConjDescend g` maps the order-`p` chief-factor summand
`caseA.Hpart i` into itself.  Decompose `g = h·u` (`h ∈ hInHu`, `u ∈ uInHu`, from
`hInHu_sup_uInHu_eq_top` + normality of `hInHu`); then `A_g = A_h ∘ A_u = A_u` (`hcConjDescend_mul`
and `hcConjDescend_eq_id_of_mem_hc`, since `h ∈ hInHu ⊆ HC`), and `A_u = uActionHom a`
(`hcConjDescend_eq_uActionHom`) preserves `Hpart i` by `Hpart_aInvariant`.  This is the geometric
core of the regularity half of the `oXtheta` `T`-invariance: `A_g` permutes the summands trivially
(each stays fixed setwise), so `θ ∘ A_g` is regular iff `θ` is. -/
theorem hcConjDescend_maps_Hpart [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars)
    (g : ↥(huSub data)) {i : Fin data.q} {z : ↥data.H ⧸ chief.N}
    [(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)).Normal]
    (hz : z ∈ caseA.Hpart i) :
    hcConjDescend chief g z ∈ caseA.Hpart i := by
  -- decompose `g = h·u` with `h ∈ hInHu`, `u ∈ uInHu`
  have hgtop : g ∈ hInHu data ⊔ uInHu data := by
    rw [hInHu_sup_uInHu_eq_top]; exact Subgroup.mem_top g
  rw [← SetLike.mem_coe, Subgroup.normal_mul] at hgtop
  obtain ⟨h, hh, u, hu, rfl⟩ := hgtop
  -- `A_{h·u} = A_h ∘ A_u`, and `A_h = id` (`h ∈ hInHu ⊆ HC`)
  rw [hcConjDescend_mul, MonoidHom.comp_apply,
    hcConjDescend_eq_id_of_mem_hc chief (Subgroup.mem_sup_left hh), MonoidHom.id_apply]
  -- `A_u = uActionHom a` preserves `Hpart i`
  obtain ⟨a, ha⟩ := hcConjDescend_eq_uActionHom chief hu
  rw [ha]
  exact (caseA.Hpart_aInvariant i).smul_mem a hz

/-- **`A_1 = id`**: `hcConjDescend 1` is the identity, since `1 ∈ HC`
(`hcConjDescend_eq_id_of_mem_hc`). -/
theorem hcConjDescend_one [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data)
    [(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)).Normal] :
    hcConjDescend chief (1 : ↥(huSub data)) = MonoidHom.id (↥data.H ⧸ chief.N) :=
  hcConjDescend_eq_id_of_mem_hc chief (Subgroup.one_mem _)

/-- **`A_g ∘ A_{g⁻¹} = id`**: `A_g (A_{g⁻¹} z) = z`, from multiplicativity (`hcConjDescend_mul`)
and `A_1 = id` (`hcConjDescend_one`).  Together with `hcConjDescend_maps_Hpart` this makes `A_g`
restrict to a *bijection* of each Clifford summand `Hpart i`. -/
theorem hcConjDescend_apply_inv_apply [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data) (g : ↥(huSub data))
    [(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)).Normal]
    (z : ↥data.H ⧸ chief.N) :
    hcConjDescend chief g (hcConjDescend chief g⁻¹ z) = z := by
  rw [← MonoidHom.comp_apply, ← hcConjDescend_mul, mul_inv_cancel, hcConjDescend_one,
    MonoidHom.id_apply]

/-- **Regularity preservation (per factor)**: for `g ∈ HU`, the precomposed character `θ ∘ A_g` is
trivial on the Clifford summand `Hpart i` iff `θ` is.  `A_g` restricts to a bijection of `Hpart i`
(`hcConjDescend_maps_Hpart` for both `g` and `g⁻¹`, inverted by `hcConjDescend_apply_inv_apply`),
so the value multisets `{θ(A_g x) | x ∈ Hpart i}` and `{θ(y) | y ∈ Hpart i}` coincide. -/
theorem hcConjDescend_comp_subtype_eq_one_iff [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars)
    (g : ↥(huSub data)) {i : Fin data.q}
    [(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)).Normal]
    (θ : (↥data.H ⧸ chief.N) →* ℂˣ) :
    (θ.comp (hcConjDescend chief g)).comp (caseA.Hpart i).subtype = 1
      ↔ θ.comp (caseA.Hpart i).subtype = 1 := by
  constructor
  · intro h
    refine MonoidHom.ext fun y => ?_
    have hval := DFunLike.congr_fun h ⟨_, hcConjDescend_maps_Hpart caseA g⁻¹ y.2⟩
    simp only [MonoidHom.comp_apply, Subgroup.subtype_apply, MonoidHom.one_apply] at hval ⊢
    rwa [hcConjDescend_apply_inv_apply] at hval
  · intro h
    refine MonoidHom.ext fun x => ?_
    have hval := DFunLike.congr_fun h ⟨_, hcConjDescend_maps_Hpart caseA g x.2⟩
    simpa only [MonoidHom.comp_apply, Subgroup.subtype_apply, MonoidHom.one_apply] using hval

/-- **Regularity preservation**: for `g ∈ HU`, `θ ∘ A_g` is regular (nontrivial on every Clifford
summand `Hpart i`) iff `θ` is.  Immediate from the per-factor
`hcConjDescend_comp_subtype_eq_one_iff`.  This is the regularity half of the `oXtheta`
`T`-invariance: combined with the conjugation-commute `hcPsi_conjBy_eq`
(`conjBy g (hcPsi θ) = hcPsi (θ ∘ A_g)`), it shows the regular-inflated set `{hcPsi θ | θ regular}`
is closed under `HU`-conjugation — the input to the `card_filter` fibre count `u·|Xθ| = (p-1)^q`. -/
theorem hcConjDescend_comp_regular_iff [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars)
    (g : ↥(huSub data))
    [(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)).Normal]
    (θ : (↥data.H ⧸ chief.N) →* ℂˣ) :
    (∀ i, (θ.comp (hcConjDescend chief g)).comp (caseA.Hpart i).subtype ≠ 1)
      ↔ (∀ i, θ.comp (caseA.Hpart i).subtype ≠ 1) :=
  forall_congr' fun _ => not_congr (hcConjDescend_comp_subtype_eq_one_iff caseA g θ)

/-- **Conjugation-commute at the `IrreducibleCharacter` level**: `(hcPsi θ)^g = hcPsi (θ ∘ A_g)`.
The `IrreducibleCharacter`-level form of `hcPsi_conjBy_eq` (`coe_conjBy` +
`IrreducibleCharacter.ext`),
the shape consumed by the conjugation-closure hypothesis of
`card_filter_induce_eq_index_inertia`. -/
theorem hcPsi_irreducibleConjBy_eq [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data) (g : ↥(huSub data))
    (θ : (↥data.H ⧸ chief.N) →* ℂˣ)
    [(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)).Normal] :
    IrreducibleCharacter.conjBy g (hcPsi chief θ)
      = hcPsi chief (θ.comp (hcConjDescend chief g)) := by
  apply IrreducibleCharacter.ext
  rw [IrreducibleCharacter.coe_conjBy, hcPsi_conjBy_eq]

/-- **The regular-inflated set is `HU`-conjugation-closed** (`oXtheta` `T`-invariance).  For a
regular
seed `θ` (nontrivial on every Clifford factor `Hpart i`) and `g ∈ HU`, the conjugate `(hcPsi θ)^g`
equals `hcPsi θ'` for the regular seed `θ' = θ ∘ A_g`: the commute `hcPsi_irreducibleConjBy_eq`
gives
the identity, and `hcConjDescend_comp_regular_iff` gives the regularity of `θ'`.  This is exactly
the
conjugation-closure hypothesis `hT` of `card_filter_induce_eq_index_inertia` for the induction
`θ ↦ Ind_{HC}^{HU}(hcPsi θ)` over `T = {hcPsi θ | θ regular}`, whose fibres have size `u`
(`hcPsi_inertia_index_eq_u`), giving the `oXtheta` count `u·|Xθ| = (p-1)^q`
(`card_regular_chars_Hbar`). -/
theorem hcPsi_regular_conjBy [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars)
    [(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)).Normal]
    {θ : (↥data.H ⧸ chief.N) →* ℂˣ} (hθ : ∀ i, θ.comp (caseA.Hpart i).subtype ≠ 1)
    (g : ↥(huSub data)) :
    ∃ θ', (∀ i, θ'.comp (caseA.Hpart i).subtype ≠ 1) ∧
      IrreducibleCharacter.conjBy g (hcPsi chief θ) = hcPsi chief θ' :=
  ⟨θ.comp (hcConjDescend chief g), (hcConjDescend_comp_regular_iff caseA g θ).mpr hθ,
    hcPsi_irreducibleConjBy_eq chief g θ⟩

/-- **Regularity, hom-form ↔ pointwise-form.**  `θ` is nontrivial on the Clifford summand `Hpart i`
(as a hom, `θ ∘ (Hpart i).subtype ≠ 1`) iff it is nontrivial at some point of `Hpart i`
(`∃ x ∈ Hpart i, θ x ≠ 1`).  Bridges the hom-form regularity of `card_regular_chars_Hbar` to the
pointwise-form `hreg` consumed by `hcPsi_inertia_index_eq_u` in the `oXtheta` fibre count. -/
theorem comp_subtype_ne_one_iff_exists {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars)
    (θ : (↥data.H ⧸ chief.N) →* ℂˣ) (i : Fin data.q) :
    θ.comp (caseA.Hpart i).subtype ≠ 1 ↔ ∃ x ∈ caseA.Hpart i, θ x ≠ 1 := by
  rw [Ne, MonoidHom.ext_iff, not_forall]
  simp only [MonoidHom.comp_apply, Subgroup.subtype_apply, MonoidHom.one_apply, Subtype.exists,
    exists_prop]

open scoped Classical in
/-- **The `oXtheta` count** (Peterfalvi (9.8) `oXtheta`): `u · |Xθ| = (p-1)^q`, where `Xθ` is the
set
of distinct `HU`-induced characters `Ind_{HC}^{HU}(hcPsi θ)` over regular seeds `θ` (nontrivial on
every Clifford factor `Hpart i`).  The induction `θ ↦ Ind(hcPsi θ)` is `u`-to-1: its fibres are the
`HU`-conjugation orbits (`card_filter_induce_eq_index_inertia`, using the `T`-invariance
`hcPsi_regular_conjBy`), each of size `[HU:HC] = u` (`hcPsi_inertia_index_eq_u`); the domain of
regular seeds has size `(p-1)^q` (`card_regular_chars_Hbar`, `hcPsi_injective`).  This is the
numerator of the (9.8.c) parity dichotomy `exists_regular_not_reducible_of_odd`. -/
theorem oXtheta_count [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars)
    [(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)).Normal]
    [Fintype ↥(huSub data)] [Fintype ((↥data.H ⧸ chief.N) →* ℂˣ)]
    [Invertible (Nat.card ↥(huSub data) : ℂ)]
    [Invertible (Nat.card ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
      (huSub data)) : ℂ)] :
    chars.u * ((Finset.univ.filter fun θ : (↥data.H ⧸ chief.N) →* ℂˣ =>
          ∀ i, θ.comp (caseA.Hpart i).subtype ≠ 1).image fun θ =>
        ClassFunction.induce (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
          (huSub data)) (hcPsi chief θ).toClassFunction).card
      = (chief.p - 1) ^ data.q := by
  classical
  let : Fintype ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
    (huSub data)) := Fintype.ofFinite _
  set RegF := Finset.univ.filter fun θ : (↥data.H ⧸ chief.N) →* ℂˣ =>
    ∀ i, θ.comp (caseA.Hpart i).subtype ≠ 1 with hRegF
  set T := RegF.image (hcPsi chief) with hTdef
  -- `T = {hcPsi θ | θ regular}` is closed under `HU`-conjugation (T-invariance)
  have hTinv : ∀ χ ∈ T, ∀ g : ↥(huSub data), IrreducibleCharacter.conjBy g χ ∈ T := by
    intro χ hχ g
    obtain ⟨θ, hθ, rfl⟩ := Finset.mem_image.mp hχ
    obtain ⟨θ', hθ', heq⟩ := hcPsi_regular_conjBy caseA (Finset.mem_filter.mp hθ).2 g
    exact heq ▸ Finset.mem_image.mpr ⟨θ', Finset.mem_filter.mpr ⟨Finset.mem_univ _, hθ'⟩, rfl⟩
  -- each induction fibre has size `u`
  have hfib : ∀ b ∈ T.image fun χ => ClassFunction.induce _ χ.toClassFunction,
      (T.filter fun χ => ClassFunction.induce _ χ.toClassFunction = b).card = chars.u := by
    intro b hb
    obtain ⟨χ₀, hχ₀, rfl⟩ := Finset.mem_image.mp hb
    rw [card_filter_induce_eq_index_inertia (G := ↥(huSub data)) T hTinv χ₀ hχ₀]
    obtain ⟨θ₀, hθ₀, rfl⟩ := Finset.mem_image.mp hχ₀
    exact hcPsi_inertia_index_eq_u caseA
      (fun i => (comp_subtype_ne_one_iff_exists caseA θ₀ i).mp ((Finset.mem_filter.mp hθ₀).2 i))
  -- fibrewise: `|T| = u · |Xθ|`
  have key : T.card
      = chars.u * (T.image fun χ => ClassFunction.induce _ χ.toClassFunction).card := by
    rw [Finset.card_eq_sum_card_fiberwise
        (fun χ hχ => Finset.mem_image_of_mem (fun χ => ClassFunction.induce _ χ.toClassFunction)
            hχ),
      Finset.sum_congr rfl hfib, Finset.sum_const, smul_eq_mul, mul_comm]
  -- `|T| = |RegF| = (p-1)^q`
  have hTeq : T.card = (chief.p - 1) ^ data.q := by
    rw [hTdef, Finset.card_image_of_injective _ (hcPsi_injective chief), hRegF,
      ← card_regular_chars_Hbar chars caseA, Nat.card_eq_fintype_card, Fintype.card_subtype]
  -- assemble: `u · |Xθ| = |T| = (p-1)^q`
  rw [key, hTdef, Finset.image_image] at hTeq
  exact hTeq

/-- **Nontriviality of a seed survives conjugation-descent**: for `θ ≠ 1` and `g ∈ HU`, the
conjugated seed `θ ∘ A_g` is again nontrivial (`A_g` bijective,
`hcConjDescend_bijective`), and `(hcPsi θ)^g = hcPsi (θ ∘ A_g)`.  The case-(b) `T`-invariance
(regularity of the case-(a) `oXtheta` replaced by mere nontriviality). -/
theorem hcPsi_ne_one_conjBy [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data)
    [(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)).Normal]
    {θ : (↥data.H ⧸ chief.N) →* ℂˣ} (hθ : θ ≠ 1) (g : ↥(huSub data)) :
    ∃ θ' : (↥data.H ⧸ chief.N) →* ℂˣ, θ' ≠ 1 ∧
      IrreducibleCharacter.conjBy g (hcPsi chief θ) = hcPsi chief θ' := by
  refine ⟨θ.comp (hcConjDescend chief g), ?_, hcPsi_irreducibleConjBy_eq chief g θ⟩
  intro h1
  apply hθ
  refine MonoidHom.ext fun z => ?_
  obtain ⟨x, rfl⟩ := (hcConjDescend_bijective chief g).surjective z
  simpa using DFunLike.congr_fun h1 x

/-- **Case-(b) inertia index of `hcPsi θ` is `u`** (any nontrivial `θ`): with the case-(b)
inertia lift `inertia_eq_hcInHu` (no regularity needed), `[HU : I(hcPsi θ)] = [HU:HC] = u`
(`hc_index_eq_u`).  The uniform fibre size of the case-(b) `oXtheta` count. -/
theorem hcPsi_inertia_index_eq_u_caseB [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseB : CliffordCaseBData chars)
    {θ : (↥data.H ⧸ chief.N) →* ℂˣ} (hθ : θ ≠ 1)
    [(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)).Normal] :
    (IrreducibleCharacter.inertia (hcPsi chief θ)).index = chars.u := by
  have hθbarnt : (linearIrreducibleCharacter θ : ClassFunction (↥data.H ⧸ chief.N) ℂ)
      ≠ trivialClassFunction _ := by
    intro h0
    apply hθ
    rw [← linearIrreducibleCharacter_eq_trivial_iff]
    exact IrreducibleCharacter.ext
      (h0.trans (IrreducibleCharacter.coe_trivialIrreducibleCharacter).symm)
  have hθ₀ := inertia_eq_hcInHu data chief caseB.actsIrreducibly hθbarnt
  change (ClassFunction.inertia (hcPsi chief θ : ClassFunction
    ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)) ℂ)).index
      = chars.u
  rw [hcPsi_inertia_eq_hc chief θ hθ₀, hc_index_eq_u chars]

open scoped Classical in
/-- **The count of nontrivial chief-factor characters**: `|{θ : H̄ →* ℂˣ | θ ≠ 1}| = p^q − 1`.
Duality `|Hom(H̄, ℂˣ)| = |H̄| = p^q` (`card_monoidHom_of_hasEnoughRootsOfUnity`,
`chiefFactor_quotient_card`) minus the trivial character.  The domain count of the case-(b)
`oXtheta`. -/
theorem card_ne_one_chiefFactorHom [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data)
    [Fintype ((↥data.H ⧸ chief.N) →* ℂˣ)] :
    (Finset.univ.filter fun θ : (↥data.H ⧸ chief.N) →* ℂˣ => θ ≠ 1).card
      = chief.p ^ data.q - 1 := by
  have := chief.N_normal
  let : CommGroup (↥data.H ⧸ chief.N) :=
    { (inferInstance : Group (↥data.H ⧸ chief.N)) with
      mul_comm := chief.quotient_elementaryAbelian.1 }
  have : NeZero (Monoid.exponent (↥data.H ⧸ chief.N)) := ⟨Monoid.exponent_ne_zero_of_finite⟩
  have hcard : Nat.card ((↥data.H ⧸ chief.N) →* ℂˣ) = Nat.card (↥data.H ⧸ chief.N) :=
    CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity _ ℂ
  rw [Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
    ← Nat.card_eq_fintype_card, hcard, chiefFactor_quotient_card chief]

open scoped Classical in
/-- **The case-(b) `oXtheta` count**: `u · |Xζ| = p^q − 1`, where `Xζ` is the set of distinct
`HU`-induced characters `Ind_{HC}^{HU}(hcPsi θ)` over *all* nontrivial seeds `θ : H̄ →* ℂˣ`.
Mirror of the case-(a) `oXtheta_count` with regularity replaced by nontriviality: fibres of
`θ ↦ Ind(hcPsi θ)` are `HU`-conjugation orbits (`card_filter_induce_eq_index_inertia`,
`T`-invariance `hcPsi_ne_one_conjBy`) of size `u` (`hcPsi_inertia_index_eq_u_caseB`), and the
domain has size `p^q − 1` (`card_ne_one_chiefFactorHom`, `hcPsi_injective`).  With `C = ⊥`
(the (9.9.c) situation) `Xζ` exhausts `𝒳(H₀)`, giving `u·|𝒳(H₀)| = p^q − 1`. -/
theorem caseB_oXtheta_count [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseB : CliffordCaseBData chars)
    [(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)).Normal]
    [Fintype ↥(huSub data)] [Fintype ((↥data.H ⧸ chief.N) →* ℂˣ)]
    [Invertible (Nat.card ↥(huSub data) : ℂ)]
    [Invertible (Nat.card ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
      (huSub data)) : ℂ)] :
    chars.u * ((Finset.univ.filter fun θ : (↥data.H ⧸ chief.N) →* ℂˣ => θ ≠ 1).image fun θ =>
        ClassFunction.induce (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
          (huSub data)) (hcPsi chief θ).toClassFunction).card
      = chief.p ^ data.q - 1 := by
  classical
  let : Fintype ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
    (huSub data)) := Fintype.ofFinite _
  set NF := Finset.univ.filter fun θ : (↥data.H ⧸ chief.N) →* ℂˣ => θ ≠ 1 with hNF
  set T := NF.image (hcPsi chief) with hTdef
  have hTinv : ∀ χ ∈ T, ∀ g : ↥(huSub data), IrreducibleCharacter.conjBy g χ ∈ T := by
    intro χ hχ g
    obtain ⟨θ, hθ, rfl⟩ := Finset.mem_image.mp hχ
    obtain ⟨θ', hθ', heq⟩ := hcPsi_ne_one_conjBy chief (Finset.mem_filter.mp hθ).2 g
    exact heq ▸ Finset.mem_image.mpr ⟨θ', Finset.mem_filter.mpr ⟨Finset.mem_univ _, hθ'⟩, rfl⟩
  have hfib : ∀ b ∈ T.image fun χ => ClassFunction.induce _ χ.toClassFunction,
      (T.filter fun χ => ClassFunction.induce _ χ.toClassFunction = b).card = chars.u := by
    intro b hb
    obtain ⟨χ₀, hχ₀, rfl⟩ := Finset.mem_image.mp hb
    rw [card_filter_induce_eq_index_inertia (G := ↥(huSub data)) T hTinv χ₀ hχ₀]
    obtain ⟨θ₀, hθ₀, rfl⟩ := Finset.mem_image.mp hχ₀
    exact hcPsi_inertia_index_eq_u_caseB caseB (Finset.mem_filter.mp hθ₀).2
  have key : T.card
      = chars.u * (T.image fun χ => ClassFunction.induce _ χ.toClassFunction).card := by
    rw [Finset.card_eq_sum_card_fiberwise
        (fun χ hχ => Finset.mem_image_of_mem (fun χ => ClassFunction.induce _ χ.toClassFunction)
            hχ),
      Finset.sum_congr rfl hfib, Finset.sum_const, smul_eq_mul, mul_comm]
  have hTeq : T.card = chief.p ^ data.q - 1 := by
    rw [hTdef, Finset.card_image_of_injective _ (hcPsi_injective chief), hNF]
    exact card_ne_one_chiefFactorHom chief
  rw [key, hTdef, Finset.image_image] at hTeq
  exact hTeq

end OddOrder.Peterfalvi.S11


