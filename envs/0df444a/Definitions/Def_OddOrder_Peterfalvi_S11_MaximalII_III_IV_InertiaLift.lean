-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S11_MaximalII_III_IV_InertiaLift
-- name    : OddOrder_Peterfalvi_S11_MaximalII_III_IV_InertiaLift
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T11:41:07.553055+00:00
-- url     : https://prove2.me/theorems/d3c50d26-a0fd-494a-83a8-9ee029dd1c3c
-- title:
--   Peterfalvi §9: inertia lift of linear characters to $H\cdot C_U(S_0)$
-- statement:
--   A continuation file for the maximal subgroups of types II, III and IV in the Clifford case (a) analysis. It realizes the single-factor centralizer $C_U(S_0)$ inside $G$ and inside $HU$, and lifts linear characters to $H\cdot C_U(S_0)$.
--
--   Main declarations: `cuSub` (The single-factor centralizer `C_U(S₀)`); `cuInHu` (`C_U(S₀)`, realized as a subgroup of `HU` inside `↥M` (mirrors `cInHu` for `C`)); `cuSub_subgroupOf_U_normal` (`C_U(S₀) ◁ U`); `cuInHu_normal` (`C_U(S₀) ◁ U`).
--
--   The bundle also proves 35 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S11_MaximalII_III_IV/InertiaLift.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S11_MaximalII_III_IV/InertiaLift.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S11_MaximalII_III_IV_CliffordData

namespace OddOrder.Peterfalvi.S11

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

open OddOrder.Isaacs.Ch03 (IsAInvariant isAInvariant_iff_smul_mem)

open OddOrder.Isaacs.Ch03.IsAInvariant (quotientMulAutHom)

variable {M : Subgroup G}

section CuS0

variable {M : Subgroup G} {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
  {chars : Section11CharacterData data chief}

/-- **The single-factor centralizer `C_U(S₀)`**, realized as a subgroup of `G` with `C_U(S₀) ≤ U`.
The kernel of the restricted `U`-action `aInvariantRestrictAut caseA.S0_aInvariant` on the order-`p`
factor `S₀`, pushed into `G` along `↥(U.subgroupOf (U ⊔ W₁)) ↪ ↥(U ⊔ W₁) ↪ G` (exactly as `cSub`
pushes `(uActionHom).ker`).  By the first isomorphism theorem `|U : C_U(S₀)| = |Ū₁| = caseA.a`
(`index_cuInHu_subgroupOf_uInHu_eq_a`). -/
noncomputable def cuSub (caseA : CliffordCaseAData chars) : Subgroup G :=
  ((aInvariantRestrictAut caseA.S0_aInvariant).ker.map
      (data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1)).subtype).map
    (data.typeP.U ⊔ data.typeP.W1).subtype

theorem cuSub_le_U (caseA : CliffordCaseAData chars) : cuSub caseA ≤ data.U :=
  (Subgroup.map_mono (Subgroup.map_subtype_le _)).trans <| by
    rw [Subgroup.subgroupOf_map_subtype]; exact inf_le_left

/-- `|C_U(S₀)| = |ker(aInvariantRestrictAut S₀)|`: the realization is the injective double-image of
the kernel (mirrors `card_cSub_eq_card_ker`). -/
theorem card_cuSub_eq_card_ker (caseA : CliffordCaseAData chars) :
    Nat.card ↥(cuSub caseA) = Nat.card ↥(aInvariantRestrictAut caseA.S0_aInvariant).ker := by
  change Nat.card ↥(((aInvariantRestrictAut caseA.S0_aInvariant).ker.map
      (data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1)).subtype).map
        (data.typeP.U ⊔ data.typeP.W1).subtype)
      = Nat.card ↥(aInvariantRestrictAut caseA.S0_aInvariant).ker
  rw [← Nat.card_congr (Subgroup.equivMapOfInjective _ _ (Subgroup.subtype_injective _)).toEquiv,
    ← Nat.card_congr (Subgroup.equivMapOfInjective _ _ (Subgroup.subtype_injective _)).toEquiv]

/-- `C_U(S₀)`, realized as a subgroup of `HU` inside `↥M` (mirrors `cInHu` for `C`). -/
noncomputable def cuInHu (caseA : CliffordCaseAData chars) : Subgroup ↥(huSub data) :=
  ((cuSub caseA).subgroupOf M).subgroupOf (huSub data)

theorem cuInHu_le_uInHu (caseA : CliffordCaseAData chars) : cuInHu caseA ≤ uInHu data :=
  Subgroup.subgroupOf_mono _ (Subgroup.subgroupOf_mono _ (cuSub_le_U caseA))

/-- `|C_U(S₀)|` realized inside `HU` equals `|C_U(S₀)|` in `G` (mirrors `card_cInHu_eq`). -/
theorem card_cuInHu_eq (caseA : CliffordCaseAData chars) :
    Nat.card ↥(cuInHu caseA) = Nat.card ↥(cuSub caseA) := by
  have hCsubM : (cuSub caseA).subgroupOf M ≤ huSub data :=
    Subgroup.subgroupOf_mono M
      ((cuSub_le_U caseA).trans (le_sup_right : data.U ≤ data.H ⊔ data.U))
  have hCleM : cuSub caseA ≤ M := (cuSub_le_U caseA).trans (U_le_M data)
  calc Nat.card ↥(cuInHu caseA)
      = Nat.card ↥((cuSub caseA).subgroupOf M) :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCsubM).toEquiv
    _ = Nat.card ↥(cuSub caseA) :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCleM).toEquiv

open Subgroup in
/-- **`C_U(S₀) ◁ U`** (mirrors `cSub_subgroupOf_U_normal`): the realization `cuSub` is the `G`-image
of a kernel, so its `subgroupOf U` is normal (kernels are normal, transported by the realization iso
`↥(U.subgroupOf (U ⊔ W₁)) ≃* ↥U`). -/
theorem cuSub_subgroupOf_U_normal (caseA : CliffordCaseAData chars) :
    ((cuSub caseA).subgroupOf data.U).Normal := by
  set e := subgroupOfEquivOfLe (le_sup_left : data.typeP.U ≤ data.typeP.U ⊔ data.typeP.W1) with he
  have heq : (cuSub caseA).subgroupOf data.U
      = (aInvariantRestrictAut caseA.S0_aInvariant).ker.map e.toMonoidHom := by
    ext x
    simp only [Subgroup.mem_subgroupOf]
    constructor
    · intro hx
      simp only [cuSub, Subgroup.mem_map] at hx
      obtain ⟨z, ⟨y, hy, hyz⟩, hzx⟩ := hx
      refine ⟨y, hy, ?_⟩
      apply Subtype.ext
      rw [MulEquiv.coe_toMonoidHom, he, subgroupOfEquivOfLe_apply_coe, ← hzx, ← hyz]
      rfl
    · rintro ⟨y, hy, rfl⟩
      simp only [cuSub, Subgroup.mem_map]
      refine ⟨_, ⟨y, hy, rfl⟩, ?_⟩
      rw [MulEquiv.coe_toMonoidHom, he, subgroupOfEquivOfLe_apply_coe]
      rfl
  rw [heq]
  exact (MonoidHom.normal_ker _).map e.toMonoidHom e.surjective

open Subgroup in
set_option backward.isDefEq.respectTransparency false in
/-- **`C_U(S₀) ◁ U`** realized inside `HU` (mirrors `cInHu_normal`): `cuInHu ◁ uInHu`, transported
from `cuSub ◁ U` along `↥uInHu ≃* ↥U`. -/
theorem cuInHu_normal (caseA : CliffordCaseAData chars) :
    ((cuInHu caseA).subgroupOf (uInHu data)).Normal := by
  have hUsubM : data.U.subgroupOf M ≤ huSub data :=
    Subgroup.subgroupOf_mono M (le_sup_right : data.U ≤ data.H ⊔ data.U)
  set f : ↥(uInHu data) ≃* ↥data.U :=
    (subgroupOfEquivOfLe hUsubM).trans (subgroupOfEquivOfLe (U_le_M data)) with hf
  have hgval : ∀ x : ↥(uInHu data), ((f x : ↥data.U) : G) = (((x : ↥(huSub data)) : ↥M) : G) := by
    intro x
    have h1 : (f x : ↥data.U)
        = subgroupOfEquivOfLe (U_le_M data) (subgroupOfEquivOfLe hUsubM x) := by rw [hf]; rfl
    rw [h1, subgroupOfEquivOfLe_apply_coe, subgroupOfEquivOfLe_apply_coe]
  have hcomap : (cuInHu caseA).subgroupOf (uInHu data)
      = ((cuSub caseA).subgroupOf data.U).comap f.toMonoidHom := by
    ext x
    simp only [cuInHu, Subgroup.mem_subgroupOf]
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf, MulEquiv.coe_toMonoidHom, hgval x]
  rw [hcomap]
  exact (cuSub_subgroupOf_U_normal caseA).comap f.toMonoidHom

/-- **`H·C_U(S₀) ◁ HU`** (mirrors `hcInHu_normal`): the inertia subgroup of the (9.8.d) source
character is normal, so `Ind_{H·C_U(S₀)}^{HU}` produces an irreducible.  From `H ◁ HU`
(`hInHu_normal`), `C_U(S₀) ◁ U` (`cuInHu_normal`), `H ⊔ U = ⊤` (`hInHu_sup_uInHu_eq_top`). -/
theorem hcuInHu_normal (caseA : CliffordCaseAData chars) :
    (hInHu data ⊔ cuInHu caseA).Normal :=
  haveI := hInHu_normal data
  haveI := cuInHu_normal caseA
  sup_normal_of_normal_left_of_normal_subgroupOf (cuInHu_le_uInHu caseA)
    (hInHu_sup_uInHu_eq_top data)

/-- **`ker(uActionHom) ≤ ker(aInvariantRestrictAut S₀)`**: an element acting trivially on the
*whole*
chief factor `H̄` acts trivially on the summand `S₀ ≤ H̄`.  The subgroup inclusion behind
`C = C_U(H̄) ≤ C_U(S₀)`. -/
theorem ker_uActionHom_le_ker_aInvariantRestrictAut (caseA : CliffordCaseAData chars) :
    (uActionHom data chief).ker ≤ (aInvariantRestrictAut caseA.S0_aInvariant).ker := by
  intro x hx
  rw [MonoidHom.mem_ker] at hx ⊢
  ext s
  rw [MulAut.one_apply, aInvariantRestrictAut_coe, hx, MulAut.one_apply]

/-- **`C = C_U(H̄) ≤ C_U(S₀)`** (`cSub ≤ cuSub`): centralizing the whole chief factor implies
centralizing the summand `S₀`.  Both are `G`-images of kernels under the same double-map, and
`ker(uActionHom) ≤ ker(aInvariantRestrictAut S₀)`. -/
theorem cSub_le_cuSub (caseA : CliffordCaseAData chars) : cSub data chief ≤ cuSub caseA :=
  Subgroup.map_mono (Subgroup.map_mono (ker_uActionHom_le_ker_aInvariantRestrictAut caseA))

theorem cInHu_le_cuInHu (caseA : CliffordCaseAData chars) : cInHu data chief ≤ cuInHu caseA :=
  Subgroup.subgroupOf_mono _ (Subgroup.subgroupOf_mono _ (cSub_le_cuSub caseA))

/-- **`U' ≤ C_U(S₀)`** (`uprimeSub ≤ cuSub`, Peterfalvi (9.8.d)): the derived subgroup `U' = [U,U]`
lies in the single-factor centralizer `C_U(S₀)`, via `U' ≤ C = C_U(H̄) ≤ C_U(S₀)`
(`uprimeSub_le_cSub` then `cSub_le_cuSub`).  This is the containment behind the (9.8.d) parameter
`λ ∈ Irr(C_U(S₀)/U')` and the `𝒮(H₀U')`-membership of the induced characters. -/
theorem uprimeSub_le_cuSub [Finite G] (caseA : CliffordCaseAData chars) :
    uprimeSub data ≤ cuSub caseA :=
  (uprimeSub_le_cSub data chief).trans (cSub_le_cuSub caseA)

/-- **`U' ≤ C_U(S₀)` realized inside `HU`** (`Uprime`/`uprimeSub` ⟶ `cuInHu`).  The `HU`-realized
form
of `uprimeSub_le_cuSub`: `(U'.subgroupOf M).subgroupOf HU ≤ cuInHu`.  Used to identify `λ` trivial
on
`U'` as a character of `C_U(S₀)/U'` in the (9.8.d) count. -/
theorem uprimeSub_subgroupOf_le_cuInHu [Finite G] (caseA : CliffordCaseAData chars) :
    ((uprimeSub data).subgroupOf M).subgroupOf (huSub data) ≤ cuInHu caseA :=
  Subgroup.subgroupOf_mono _ (Subgroup.subgroupOf_mono _ (uprimeSub_le_cuSub caseA))

/-- **`H ⊓ U ≤ C_U(S₀)`** realized (`hInHu ⊓ uInHu ≤ cuInHu`): an `H ⊓ U` element centralizes the
chief factor `H̄` (`hInHu_inf_uInHu_le_cInHu`), hence `S₀ ≤ H̄` (`cInHu_le_cuInHu`). -/
theorem hInHu_inf_uInHu_le_cuInHu [Finite G] (caseA : CliffordCaseAData chars) :
    hInHu data ⊓ uInHu data ≤ cuInHu caseA :=
  (hInHu_inf_uInHu_le_cInHu data chief).trans (cInHu_le_cuInHu caseA)

/-- **`H ⊓ C_U(S₀) = ⊥`** realized (`hInHu ⊓ cuInHu = ⊥`).  Since `C_U(S₀) ≤ U`, an element of
`hInHu ⊓ cuInHu` has `G`-image in `H ⊓ U = ⊥` (a type-P setup, `typeP_H_inf_U`), so it is trivial.
This is the trivial-intersection input `H ⊓ C_U(S₀) = ⊥` that makes the second isomorphism
`(H·C_U(S₀))/C_U(S₀) ≅ H` (used to build the `θ₁·λ` source character on `H·C_U(S₀)`), mirroring
`hInHu_inf_cInHu_eq_bot` for the (9.8.c) `hcLambdaHom`. -/
theorem hInHu_inf_cuInHu_eq_bot [Finite G] (caseA : CliffordCaseAData chars) :
    hInHu data ⊓ cuInHu caseA = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxH, hxC⟩ := Subgroup.mem_inf.mp hx
  have hxU := cuInHu_le_uInHu caseA hxC
  rw [Subgroup.mem_bot]
  have hxH' : x ∈ (data.H.subgroupOf M).subgroupOf (huSub data) := hxH
  have hxU' : x ∈ (data.U.subgroupOf M).subgroupOf (huSub data) := hxU
  have keyH : ((x : ↥M) : G) ∈ data.H :=
    Subgroup.mem_subgroupOf.mp (Subgroup.mem_subgroupOf.mp hxH')
  have keyU : ((x : ↥M) : G) ∈ data.U :=
    Subgroup.mem_subgroupOf.mp (Subgroup.mem_subgroupOf.mp hxU')
  have key : ((x : ↥M) : G) ∈ data.typeP.H ⊓ data.typeP.U := ⟨keyH, keyU⟩
  rw [typeP_H_inf_U data.typeP, Subgroup.mem_bot] at key
  exact Subtype.ext (Subtype.ext key)

/-- **`H·C_U(S₀) = C_U(S₀)·H`** (spelling bridge, mirrors `hcRealized_eq_cInHu_sup_hInHu`): the
`sup_comm` reorientation of the (9.8.d) inertia subgroup, used to phrase the `λ`-lift channel
`hcuLambdaHom` via the second isomorphism `(C_U(S₀)·H)/H ≅ C_U(S₀)`. -/
theorem hcuInHu_eq_cuInHu_sup_hInHu (caseA : CliffordCaseAData chars) :
    hInHu data ⊔ cuInHu caseA = cuInHu caseA ⊔ hInHu data :=
  sup_comm _ _

/-- **`|U| = a · |C_U(S₀)|`** (Peterfalvi (9.7.a)): the order of `U` splits as the Clifford index
`a = [U:C_U(S₀)]` times the centralizer order.  Rearranges the first-isomorphism value `|U| = |Ū₁| ·
|C_U(S₀)|` (the `hII` step of `index_cuInHu_subgroupOf_uInHu_eq_a`) using the pin `a = |Ū₁|`
(`a_eq_card_restrictAut_range`).  The arithmetic behind the (9.8.d) domain-count identity
`|U|/(a|U'|) = |C_U(S₀):U'|`. -/
theorem card_U_eq_a_mul_card_cuSub [Finite G] (caseA : CliffordCaseAData chars) :
    Nat.card ↥data.U = caseA.a * Nat.card ↥(cuSub caseA) := by
  rw [caseA.a_eq_card_restrictAut_range]
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (aInvariantRestrictAut caseA.S0_aInvariant).ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange
      (aInvariantRestrictAut caseA.S0_aInvariant)).toEquiv,
    ← card_cuSub_eq_card_ker caseA,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (le_sup_left : data.typeP.U ≤ data.typeP.U ⊔ data.typeP.W1)).toEquiv] at h
  exact h

/-- **`|U|/(a·|U'|) = |C_U(S₀):U'|`** (Peterfalvi (9.8.d) domain-count identity): the count
`((p-1)/a)·(|U|/(a|U'|))` in the (9.8.d) statement equals `((p-1)/a)·|C_U(S₀):U'|`, the number of
`(θ₁,λ)`-pairs divided by the `U`-orbit size `a`.  Since `|U| = a·|C_U(S₀)|`
(`card_U_eq_a_mul_card_cuSub`) and `|U'| ∣ |C_U(S₀)|` (`U' ≤ C_U(S₀)`, `uprimeSub_le_cuSub`), the
`a` cancels: `|U|/(a·|U'|) = a·|C_U(S₀)|/(a·|U'|) = |C_U(S₀)|/|U'| = [C_U(S₀):U']`.  Here
`[C_U(S₀):U'] = (uprimeSub data).relIndex (cuSub caseA)` (the relative index of `U'` in `C_U(S₀)`,
a genuine subgroup index since `U' ≤ C_U(S₀)`). -/
theorem card_U_div_a_mul_card_Uprime_eq_relIndex [Finite G] (caseA : CliffordCaseAData chars) :
    Nat.card ↥data.U / (caseA.a * Nat.card ↥(uprimeSub data))
      = (uprimeSub data).relIndex (cuSub caseA) := by
  have hUprime_le : uprimeSub data ≤ cuSub caseA := uprimeSub_le_cuSub caseA
  -- `[C_U(S₀):U'] · |U'| = |C_U(S₀)|` (via `[K:H]·|H| = |K|` for `H = U'.subgroupOf C_U(S₀)`)
  have hrel : (uprimeSub data).relIndex (cuSub caseA) * Nat.card ↥(uprimeSub data)
      = Nat.card ↥(cuSub caseA) := by
    have h := Subgroup.index_mul_card ((uprimeSub data).subgroupOf (cuSub caseA))
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUprime_le).toEquiv] at h
  rw [card_U_eq_a_mul_card_cuSub caseA, ← hrel]
  -- `a·([C_U(S₀):U']·|U'|) / (a·|U'|) = [C_U(S₀):U']`
  rw [show caseA.a * ((uprimeSub data).relIndex (cuSub caseA) * Nat.card ↥(uprimeSub data))
      = ((uprimeSub data).relIndex (cuSub caseA)) * (caseA.a * Nat.card ↥(uprimeSub data)) by ring]
  exact Nat.mul_div_cancel _ (Nat.mul_pos caseA.a_pos Nat.card_pos)

/-- `C_U(S₀) ≤ H·C_U(S₀)` (mirrors `cInHu_le_hcRealized`): `cuInHu` is contained in the inertia
subgroup `hInHu ⊔ cuInHu`. -/
theorem cuInHu_le_hcuInHu (caseA : CliffordCaseAData chars) :
    cuInHu caseA ≤ hInHu data ⊔ cuInHu caseA :=
  le_sup_right

/-- **The `λ`-lift `H·C_U(S₀) →* ℂˣ`** of a linear character `λ : C_U(S₀) →* ℂˣ` (the `C`-factor of
the (9.8.d) pair character `θ₁·λ`): the composite `H·C_U(S₀) → H·C_U(S₀)/H ≅ C_U(S₀)/(C_U(S₀) ⊓ H)
= C_U(S₀) —λ→ ℂˣ`, using the trivial intersection `H ⊓ C_U(S₀) = ⊥` (`hInHu_inf_cuInHu_eq_bot`).
Mirrors the (9.9.c) `hcLambdaHom` rewired from `cInHu` to `cuInHu`; `hInHu` is normal in the sup, so
the quotient map is well-defined.  Kills `H` (`hcuLambdaHom_eq_one_of_mem_hInHu`) and restricts to
`λ` on `C_U(S₀)` (`hcuLambdaHom_inclusion`). -/
noncomputable def hcuLambdaHom [Finite G] (caseA : CliffordCaseAData chars)
    (lam : ↥(cuInHu caseA) →* ℂˣ) :
    ↥(hInHu data ⊔ cuInHu caseA) →* ℂˣ :=
  haveI := hInHu_normal data
  letI : ((hInHu data).subgroupOf (cuInHu caseA ⊔ hInHu data)).Normal :=
    (hInHu_normal data).subgroupOf _
  (QuotientGroup.lift ((hInHu data).subgroupOf (cuInHu caseA)) lam
      (fun x hx => by
        have hx1 : x = 1 := by
          have hmem : (x : ↥(huSub data)) ∈ hInHu data ⊓ cuInHu caseA :=
            ⟨Subgroup.mem_subgroupOf.mp hx, x.2⟩
          rw [hInHu_inf_cuInHu_eq_bot caseA, Subgroup.mem_bot] at hmem
          exact Subtype.ext hmem
        rw [hx1]
        exact lam.ker.one_mem)).comp
    ((QuotientGroup.quotientInfEquivProdNormalQuotient (cuInHu caseA)
        (hInHu data)).symm.toMonoidHom.comp
      ((QuotientGroup.mk' ((hInHu data).subgroupOf (cuInHu caseA ⊔ hInHu data))).comp
        (MulEquiv.subgroupCongr (hcuInHu_eq_cuInHu_sup_hInHu caseA)).toMonoidHom))

/-- **`hcuLambdaHom` kills `H`** (mirrors `hcLambdaHom_eq_one_of_mem_hInHu`): the `λ`-lift is
trivial
on the `H`-part of `H·C_U(S₀)` (the quotient map by `hInHu` kills it).  So the pair character
`θ₁·λ` restricts on `hInHu` to the plain seed inflation `θ₀`, and the (9.8.d) inertia lift
`inertia_eq_hcuInHu` applies to the pair unchanged. -/
theorem hcuLambdaHom_eq_one_of_mem_hInHu [Finite G] (caseA : CliffordCaseAData chars)
    (lam : ↥(cuInHu caseA) →* ℂˣ)
    {x : ↥(hInHu data ⊔ cuInHu caseA)}
    (hx : x ∈ (hInHu data).subgroupOf (hInHu data ⊔ cuInHu caseA)) :
    hcuLambdaHom caseA lam x = 1 := by
  have := hInHu_normal data
  let : ((hInHu data).subgroupOf (cuInHu caseA ⊔ hInHu data)).Normal :=
    (hInHu_normal data).subgroupOf _
  simp only [hcuLambdaHom, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    QuotientGroup.mk'_apply]
  have hmem : (MulEquiv.subgroupCongr (hcuInHu_eq_cuInHu_sup_hInHu caseA)) x
      ∈ (hInHu data).subgroupOf (cuInHu caseA ⊔ hInHu data) :=
    Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mp hx)
  rw [(QuotientGroup.eq_one_iff _).mpr hmem, map_one, map_one]

/-- **`hcuLambdaHom` restricts to `λ` on `C_U(S₀)`** (mirrors `hcLambdaHom_inclusion`): on the
inclusion of `c ∈ cuInHu` into `H·C_U(S₀)`, the `λ`-lift returns `λ c`.  The second iso sends the
`cuInHu`-class to the `H·C_U(S₀)`-class via inclusion (`hfwd`), so the reversed iso undoes the
quotient map and the lift evaluates `λ`. -/
theorem hcuLambdaHom_inclusion [Finite G] (caseA : CliffordCaseAData chars)
    (lam : ↥(cuInHu caseA) →* ℂˣ) (c : ↥(cuInHu caseA)) :
    hcuLambdaHom caseA lam (Subgroup.inclusion (cuInHu_le_hcuInHu caseA) c) = lam c := by
  have := hInHu_normal data
  let : ((hInHu data).subgroupOf (cuInHu caseA ⊔ hInHu data)).Normal :=
    (hInHu_normal data).subgroupOf _
  have hfwd : (QuotientGroup.quotientInfEquivProdNormalQuotient (cuInHu caseA)
        (hInHu data))
      (QuotientGroup.mk' _ c)
      = QuotientGroup.mk' _ (Subgroup.inclusion le_sup_left c) := by
    simp only [QuotientGroup.quotientInfEquivProdNormalQuotient,
      QuotientGroup.quotientInfEquivProdNormalizerQuotient, MulEquiv.trans_apply,
      QuotientGroup.quotientKerEquivOfSurjective,
      QuotientGroup.quotientKerEquivOfRightInverse, MulEquiv.coe_mk]
    rfl
  simp only [hcuLambdaHom, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  have hcongr : (MulEquiv.subgroupCongr (hcuInHu_eq_cuInHu_sup_hInHu caseA))
      (Subgroup.inclusion (cuInHu_le_hcuInHu caseA) c)
      = Subgroup.inclusion le_sup_left c := by
    apply Subtype.ext
    rfl
  rw [hcongr, QuotientGroup.mk'_apply, show ((Subgroup.inclusion le_sup_left c :
      ↥(cuInHu caseA ⊔ hInHu data)) : ↥(cuInHu caseA ⊔ hInHu data)
        ⧸ (hInHu data).subgroupOf (cuInHu caseA ⊔ hInHu data))
      = QuotientGroup.mk' _ (Subgroup.inclusion le_sup_left c) from rfl, ← hfwd,
    MulEquiv.symm_apply_apply, QuotientGroup.mk'_apply, QuotientGroup.lift_mk]

/-- **`U ⊓ H·C_U(S₀) = C_U(S₀)`** realized (`uInHu ⊓ (hInHu ⊔ cuInHu) = cuInHu`), the second-iso
input for `[HU : H·C_U(S₀)] = [U : C_U(S₀)]`.  Mirrors `uInHu_inf_hcInHu_eq_cInHu`. -/
theorem uInHu_inf_hcuInHu_eq_cuInHu [Finite G] (caseA : CliffordCaseAData chars) :
    uInHu data ⊓ (hInHu data ⊔ cuInHu caseA) = cuInHu caseA := by
  have := hInHu_normal data
  apply le_antisymm
  · rintro x ⟨hxU, hxHC⟩
    obtain ⟨hh, hhmem, cc, ccmem, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hxHC
    have hcc_u : cc ∈ uInHu data := cuInHu_le_uInHu caseA ccmem
    have hh_u : hh ∈ uInHu data := by
      have h1 : hh * cc * cc⁻¹ ∈ uInHu data :=
        (uInHu data).mul_mem hxU ((uInHu data).inv_mem hcc_u)
      rwa [mul_inv_cancel_right] at h1
    have hh_c : hh ∈ cuInHu caseA :=
      hInHu_inf_uInHu_le_cuInHu caseA (Subgroup.mem_inf.mpr ⟨hhmem, hh_u⟩)
    exact (cuInHu caseA).mul_mem hh_c ccmem
  · exact le_inf (cuInHu_le_uInHu caseA) le_sup_right

/-- **Second-iso index step: `[HU : H·C_U(S₀)] = [U : C_U(S₀)]`** (realized
`(hInHu ⊔ cuInHu).index = (cuInHu.subgroupOf uInHu).index`).  Mirrors
`index_hcInHu_eq_relindex_cInHu`: the second isomorphism theorem for `H·C_U(S₀) ◁ HU` with
`uInHu ⊔ H·C_U(S₀) = ⊤`, and `uInHu ⊓ H·C_U(S₀) = cuInHu`. -/
theorem index_hcuInHu_eq_relindex_cuInHu [Finite G] (caseA : CliffordCaseAData chars) :
    (hInHu data ⊔ cuInHu caseA).index
      = ((cuInHu caseA).subgroupOf (uInHu data)).index := by
  have : (hInHu data ⊔ cuInHu caseA).Normal := hcuInHu_normal caseA
  have htop : uInHu data ⊔ (hInHu data ⊔ cuInHu caseA) = ⊤ := by
    rw [← sup_assoc, sup_comm (uInHu data) (hInHu data), hInHu_sup_uInHu_eq_top, top_sup_eq]
  have he := Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalQuotient
    (uInHu data) (hInHu data ⊔ cuInHu caseA)).toEquiv
  have hsub : (hInHu data ⊔ cuInHu caseA).subgroupOf (uInHu data)
      = (cuInHu caseA).subgroupOf (uInHu data) := by
    ext x
    simp only [Subgroup.mem_subgroupOf]
    constructor
    · intro hx
      have hxin : (x : ↥(huSub data)) ∈ uInHu data ⊓ (hInHu data ⊔ cuInHu caseA) :=
        Subgroup.mem_inf.mpr ⟨x.2, hx⟩
      rw [uInHu_inf_hcuInHu_eq_cuInHu caseA] at hxin
      exact hxin
    · intro hx; exact Subgroup.mem_sup_right hx
  rw [hsub] at he
  have hsplit := Subgroup.card_eq_card_quotient_mul_card_subgroup
    ((hInHu data ⊔ cuInHu caseA).subgroupOf (uInHu data ⊔ (hInHu data ⊔ cuInHu caseA)))
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right :
        (hInHu data ⊔ cuInHu caseA) ≤ uInHu data ⊔ (hInHu data ⊔ cuInHu caseA))).toEquiv,
    ← he, ← Subgroup.index_eq_card] at hsplit
  have htopcard : Nat.card ↥(uInHu data ⊔ (hInHu data ⊔ cuInHu caseA))
      = Nat.card ↥(huSub data) := by
    rw [htop]; exact Nat.card_congr Subgroup.topEquiv.toEquiv
  rw [htopcard] at hsplit
  have hmul := Subgroup.card_mul_index (hInHu data ⊔ cuInHu caseA)
  rw [hsplit, mul_comm (((cuInHu caseA).subgroupOf (uInHu data)).index)] at hmul
  exact Nat.eq_of_mul_eq_mul_left Nat.card_pos hmul

/-- **`[U : C_U(S₀)] = |Ū₁|`** (realized
`(cuInHu.subgroupOf uInHu).index = |range(aInvariantRestrictAut S₀)|`).
Mirrors `index_cInHu_subgroupOf_uInHu_eq_u`: the first isomorphism theorem for the restricted
`U`-action `aInvariantRestrictAut caseA.S0_aInvariant` on `S₀`, whose image `Ū₁` has order the index
`a` of `C_U(S₀)` in `U`.  This is the value `clifford_caseA_data` assigns to
`CliffordCaseAData.a`. -/
theorem index_cuInHu_subgroupOf_uInHu_eq_a [Finite G] (caseA : CliffordCaseAData chars) :
    ((cuInHu caseA).subgroupOf (uInHu data)).index
      = Nat.card ↥(aInvariantRestrictAut caseA.S0_aInvariant).range := by
  -- (I): `|C_U(S₀)| · [U:C_U(S₀)] = |U|`.
  have hI : Nat.card ↥(cuSub caseA) * ((cuInHu caseA).subgroupOf (uInHu data)).index
      = Nat.card ↥data.U := by
    have h := Subgroup.card_mul_index ((cuInHu caseA).subgroupOf (uInHu data))
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (cuInHu_le_uInHu caseA)).toEquiv,
      card_cuInHu_eq caseA, card_uInHu_eq data] at h
    exact h
  -- (II): `|U| = |Ū₁| · |C_U(S₀)|` (first iso for the restricted action hom, domain `≃* ↥U`).
  have hII : Nat.card ↥data.U
      = Nat.card ↥(aInvariantRestrictAut caseA.S0_aInvariant).range * Nat.card ↥(cuSub caseA) := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup
      (aInvariantRestrictAut caseA.S0_aInvariant).ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange
        (aInvariantRestrictAut caseA.S0_aInvariant)).toEquiv,
      ← card_cuSub_eq_card_ker caseA,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (le_sup_left : data.typeP.U ≤ data.typeP.U ⊔ data.typeP.W1)).toEquiv] at h
    exact h
  have hcancel : Nat.card ↥(cuSub caseA)
      * ((cuInHu caseA).subgroupOf (uInHu data)).index
      = Nat.card ↥(cuSub caseA) * Nat.card ↥(aInvariantRestrictAut caseA.S0_aInvariant).range := by
    rw [hI, hII, mul_comm]
  exact Nat.eq_of_mul_eq_mul_left Nat.card_pos hcancel

/-- **`[HU : H·C_U(S₀)] = |Ū₁| = a`** (Peterfalvi (9.8.d) degree index).  The inertia subgroup of
the
degree-`qa` source character `θ₁·λ` has index `a` in `HU`, giving the source degree `a` and (after
`Ind_{HU}^M`) the character degree `qa`.  Combines the second-iso step
`[HU:H·C_U(S₀)] = [U:C_U(S₀)]`
(`index_hcuInHu_eq_relindex_cuInHu`) with the first-iso value `[U:C_U(S₀)] = |Ū₁|`
(`index_cuInHu_subgroupOf_uInHu_eq_a`). Here `|Ū₁| = Nat.card (aInvariantRestrictAut …).range` is
the
genuine geometric `a = |U:C_U(H₁)|`, the value `clifford_caseA_data` assigns to `caseA.a`. -/
theorem index_hcuInHu_eq_a [Finite G] (caseA : CliffordCaseAData chars) :
    (hInHu data ⊔ cuInHu caseA).index
      = Nat.card ↥(aInvariantRestrictAut caseA.S0_aInvariant).range :=
  (index_hcuInHu_eq_relindex_cuInHu caseA).trans (index_cuInHu_subgroupOf_uInHu_eq_a caseA)

/-- **`[HU : H·C_U(S₀)] = a`** (Peterfalvi (9.8.d), with `a = CliffordCaseAData.a`).  The genuine
geometric index `[HU : H·C_U(S₀)] = |Ū₁|` (`index_hcuInHu_eq_a`) equals the carrier's `a`, since `a`
is pinned to `|Ū₁|` (`CliffordCaseAData.a_eq_card_restrictAut_range`).  This is the degree of the
(9.8.d) source character `Ind_{H·C_U(S₀)}^{HU}(θ₁·λ)`, whence `Ind_{HU}^M` of it has degree `qa`. -/
theorem index_hcuInHu_eq_caseA_a [Finite G] (caseA : CliffordCaseAData chars) :
    (hInHu data ⊔ cuInHu caseA).index = caseA.a := by
  rw [index_hcuInHu_eq_a caseA, caseA.a_eq_card_restrictAut_range]

end CuS0

/-- **realized `H₀U' = (realized H₀) ⊔ (realized U')`** (Peterfalvi (9.8.d); mirror of
`realizedH0supCprime_eq_realizedH0_sup_cprimeInHu`): the realized `H₀U'` inside `HU` equals the join
of the realized `H₀` and the realized `U'`.  Feeds the `h₀·u'` decomposition of the (9.8.d) pair
character's kernel computation. -/
theorem realizedH0supUprime_eq_realizedH0_sup_uprimeInHu {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data) :
    ((chief.H0 ⊔ uprimeSub data).subgroupOf M).subgroupOf (huSub data)
      = (chief.H0.subgroupOf M).subgroupOf (huSub data)
          ⊔ ((uprimeSub data).subgroupOf M).subgroupOf (huSub data) := by
  have hH0M : chief.H0 ≤ M := chief.H0_lt_H.le.trans (H_le_M data)
  have hUM : uprimeSub data ≤ M := (uprimeSub_le_U data).trans (U_le_M data)
  rw [Subgroup.subgroupOf_sup hH0M hUM]
  have hH0sub : (chief.H0.subgroupOf M) ≤ huSub data :=
    Subgroup.subgroupOf_mono M (le_trans chief.H0_lt_H.le le_sup_left)
  have hUsub : (uprimeSub data).subgroupOf M ≤ huSub data :=
    Subgroup.subgroupOf_mono M (le_trans (uprimeSub_le_U data) le_sup_right)
  rw [Subgroup.subgroupOf_sup hH0sub hUsub]

/-- **(9.7) Clifford dimension dichotomy** (the arithmetic heart of (9.7)).  Restricting the
`U W₁`-action on the chief factor `H̄ = H/H₀` to `U`, there is a minimal `U`-invariant `S₀ ≠ ⊥` of
order `p^d` with `0 < d` and `d ∣ q`.  Since `q` is prime, `d ∈ {1, q}`: the dichotomy of (9.7),
case (a) (`d = 1`, `U` semisimple into order-`p` pieces) vs case (b) (`d = q`, `U` irreducible).

Assembled from the spanning step (`iSup_smul_eq_top_of_irreducible`, on the `U W₁`-irreducible
`H̄`),
the orbit lemmas (each `U W₁`-translate of `S₀` is `U`-irreducible of order `|S₀|`), and the order
step (`card_eq_pow_of_iSup_aInvariant_irreducible`): `|H̄| = |S₀|^k`, while `|H̄| = p^q`, so
`p^q = (p^d)^k`, i.e. `q = d·k`. -/
theorem chiefFactor_clifford_dim_dvd_q [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data) :
    ∃ (d : ℕ) (S₀ : Subgroup (↥data.H ⧸ chief.N)),
      0 < d ∧ d ∣ data.q ∧ S₀ ≠ ⊥ ∧ Nat.card ↥S₀ = chief.p ^ d ∧
      IsAInvariant ((typeP_quotientCoprimeAction data.typeP data.nontrivial.1
          chief.N_aInvariant).φ.comp (typeP_quotientCoprimeAction data.typeP data.nontrivial.1
          chief.N_aInvariant).U.subtype) S₀ ∧
      (∀ J, IsAInvariant ((typeP_quotientCoprimeAction data.typeP data.nontrivial.1
          chief.N_aInvariant).φ.comp (typeP_quotientCoprimeAction data.typeP data.nontrivial.1
          chief.N_aInvariant).U.subtype) J → J ≤ S₀ → J = ⊥ ∨ J = S₀) := by
  classical
  have hU : data.typeP.U ≠ ⊥ := data.nontrivial.1
  have : chief.N.Normal := chief.N_normal
  have := Fact.mk chief.p_prime
  -- The descended `U W₁`-action on the chief factor `H̄` and its restriction to the kernel `U`.
  set act := typeP_quotientCoprimeAction data.typeP hU chief.N_aInvariant with hact
  set φU := act.φ.comp act.U.subtype with hφU
  have hUnorm : act.U.Normal := (typeP_uW1_frobenius data.typeP hU).isNormal
  have hKcard : Nat.card (↥data.H ⧸ chief.N) = chief.p ^ data.q := chiefFactor_quotient_card chief
  have hq_pos : 0 < data.q := Nat.card_pos
  have hKnt : Nontrivial (↥data.H ⧸ chief.N) :=
    Finite.one_lt_card_iff_nontrivial.mp (by
      rw [hKcard]; exact Nat.one_lt_pow hq_pos.ne' chief.p_prime.one_lt)
  -- A minimal nonzero `U`-invariant subgroup `S₀` (the `U`-irreducible Clifford piece).
  set T : Set (Subgroup (↥data.H ⧸ chief.N)) := {J | J ≠ ⊥ ∧ IsAInvariant φU J} with hT
  obtain ⟨S₀, ⟨hS₀ne, hS₀inv⟩, hS₀min⟩ :=
    (Set.toFinite T).exists_minimal ⟨⊤, top_ne_bot, IsAInvariant.top _⟩
  have hirr₀ : ∀ J, IsAInvariant φU J → J ≤ S₀ → J = ⊥ ∨ J = S₀ := by
    intro J hJinv hJle
    by_cases hJ0 : J = ⊥
    · exact Or.inl hJ0
    · exact Or.inr (le_antisymm hJle (hS₀min ⟨hJ0, hJinv⟩ hJle))
  -- `|S₀| = p^d` (subgroup of the elementary abelian `p`-group `H̄`).
  obtain ⟨d, hd⟩ := (chief.quotient_elementaryAbelian.to_subgroup S₀).isPGroup.exists_card_eq
  -- Spanning step (full action) + order step (restricted `U`-action) give `|H̄| = |S₀|^k`.
  have hspan : ⨆ a, act.φ a • S₀ = ⊤ :=
    iSup_smul_eq_top_of_irreducible (φ := act.φ) chief.quotient_chiefFactor hS₀ne
  obtain ⟨k, hk⟩ := card_eq_pow_of_iSup_aInvariant_irreducible
    (φ := φU) (S := fun a => act.φ a • S₀) (n := Nat.card ↥S₀)
    (fun x y => chief.quotient_elementaryAbelian.comm x y) hspan
    (fun a => isAInvariant_comp_subtype_pointwise_smul hUnorm hS₀inv a)
    (fun a J hJinv hJle => forall_aInvariant_le_pointwise_smul hUnorm hirr₀ a J hJinv hJle)
    (fun a _ => card_pointwise_smul act.φ a S₀)
  -- Arithmetic: `p^q = (p^d)^k = p^{d·k}`, so `q = d·k`.
  rw [hd, hKcard, ← pow_mul] at hk
  have hdk : data.q = d * k := Nat.pow_right_injective chief.p_prime.two_le hk
  have hdpos : 0 < d := by
    rcases Nat.eq_zero_or_pos d with h0 | h
    · rw [h0, pow_zero] at hd; exact absurd (Subgroup.card_eq_one.mp hd) hS₀ne
    · exact h
  exact ⟨d, S₀, hdpos, ⟨k, hdk⟩, hS₀ne, hd, hS₀inv, hirr₀⟩

/-- **(9.7) structural dichotomy** (the Clifford case split, read off the chief factor).  With
`q = |W₁|` prime, the chief factor `H̄` is, under the restricted `U`-action, *either*
`U`-irreducible (Clifford case (b): every `U`-invariant subgroup is `⊥` or `⊤`) *or* contains a
`U`-invariant subgroup of order `p` (Clifford case (a)).

This is the arithmetic dichotomy `d ∈ {1, q}` of `chiefFactor_clifford_dim_dvd_q` read through the
primality of `q`: the minimal nonzero `U`-invariant piece `S₀` has order `p^d` with `d ∣ q`, so
either `d = q` (`|S₀| = p^q = |H̄|`, hence `S₀ = ⊤`, and minimality forces `U`-irreducibility)
or `d = 1` (`|S₀| = p`).  Packaging the two cases into the carriers `CliffordCaseAData` /
`CliffordCaseBData` (the order-`p` factor pullback / the `End_{𝔽ₚ[U]}(H̄)` field model) is the
remaining work of `clifford_dichotomy`. -/
theorem chiefFactor_clifford_U_dichotomy [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data) :
    (∀ J : Subgroup (↥data.H ⧸ chief.N),
        IsAInvariant ((typeP_quotientCoprimeAction data.typeP data.nontrivial.1
          chief.N_aInvariant).φ.comp (typeP_quotientCoprimeAction data.typeP data.nontrivial.1
          chief.N_aInvariant).U.subtype) J → J = ⊥ ∨ J = ⊤) ∨
    (∃ S₀ : Subgroup (↥data.H ⧸ chief.N), S₀ ≠ ⊥ ∧
        IsAInvariant ((typeP_quotientCoprimeAction data.typeP data.nontrivial.1
          chief.N_aInvariant).φ.comp (typeP_quotientCoprimeAction data.typeP data.nontrivial.1
          chief.N_aInvariant).U.subtype) S₀ ∧ Nat.card ↥S₀ = chief.p ∧
        ∀ J, IsAInvariant ((typeP_quotientCoprimeAction data.typeP data.nontrivial.1
          chief.N_aInvariant).φ.comp (typeP_quotientCoprimeAction data.typeP data.nontrivial.1
          chief.N_aInvariant).U.subtype) J → J ≤ S₀ → J = ⊥ ∨ J = S₀) := by
  obtain ⟨d, S₀, _hdpos, hdq, hS₀ne, hcard, hS₀inv, hirr₀⟩ :=
    chiefFactor_clifford_dim_dvd_q chief
  -- `q = |W₁|` is prime and `d ∣ q`, so `d = 1` or `d = q`.
  have hq_prime : (data.q).Prime := data.nontrivial.2.1
  rcases hq_prime.eq_one_or_self_of_dvd d hdq with hd1 | hdq2
  · -- `d = 1`: a `U`-invariant subgroup of order `p`.  Clifford case (a).
    exact Or.inr ⟨S₀, hS₀ne, hS₀inv, by rw [hcard, hd1, pow_one], hirr₀⟩
  · -- `d = q`: `|S₀| = p^q = |H̄|` ⟹ `S₀ = ⊤`; minimality ⟹ `U`-irreducible.  Case (b).
    have hS₀top : S₀ = ⊤ :=
      Subgroup.eq_top_of_card_eq _ (by rw [hcard, hdq2, chiefFactor_quotient_card chief])
    refine Or.inl fun J hJinv => ?_
    by_cases hJ : J = ⊥
    · exact Or.inl hJ
    · exact Or.inr
        (((hirr₀ J hJinv (le_top.trans_eq hS₀top.symm)).resolve_left hJ).trans hS₀top)

open OddOrder.RepresentationTheory Representation in
open scoped commutatorElement IsMulCommutative in
/-- **Peterfalvi (9.7) case (b), chief-factor Singer conclusion.**  When `U` acts irreducibly on
the chief factor `H̄ = H/H₀` (Clifford case (b) — the left branch of
`chiefFactor_clifford_U_dichotomy`), its image `Ū = φ_U(U) ≤ Aut(H̄)` is *cyclic*, of order
dividing `p^q - 1`.

`Ū` is abelian because `[U, U]` centralizes `H` (Peterfalvi (8.5.b),
`typeP_commutator_U_centralizes_H`): a commutator `⁅a, b⁆ ∈ [U, U]` acts trivially on `H̄`, so
`φ_U ⁅a, b⁆ = 1` and the image is commutative.  Faithfulness of the inclusion `Ū ↪ Aut(H̄)` and the
irreducibility transferred from the case-(b) hypothesis feed the canonical module-level Singer
mechanism `isCyclic_and_card_dvd_of_faithful_irreducible_comm` (shared `SingerField` leaf) through
the thin adapter `elabRepresentation_isSimpleModule_and_faithful`, with `H̄` the elementary abelian
`p`-group of order `p^q` (`chiefFactor_quotient_card`).  This is the structural core behind the
`Coprime u (p-1)` / `u ∣ (p^q-1)/(p-1)` divisibilities of `CliffordCaseBData` (which additionally
pin `u = |Ū|` and use the `W₁`-fixed-point-free refinement). -/
theorem chiefFactor_caseB_image_cyclic [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data)
    (hcaseB : ∀ J : Subgroup (↥data.H ⧸ chief.N),
        IsAInvariant ((typeP_quotientCoprimeAction data.typeP data.nontrivial.1
          chief.N_aInvariant).φ.comp (typeP_quotientCoprimeAction data.typeP data.nontrivial.1
          chief.N_aInvariant).U.subtype) J → J = ⊥ ∨ J = ⊤) :
    IsCyclic ↥(((typeP_quotientCoprimeAction data.typeP data.nontrivial.1
          chief.N_aInvariant).φ.comp (typeP_quotientCoprimeAction data.typeP data.nontrivial.1
          chief.N_aInvariant).U.subtype).range) ∧
      Nat.card ↥(((typeP_quotientCoprimeAction data.typeP data.nontrivial.1
          chief.N_aInvariant).φ.comp (typeP_quotientCoprimeAction data.typeP data.nontrivial.1
          chief.N_aInvariant).U.subtype).range) ∣ chief.p ^ data.q - 1 := by
  classical
  have hU : data.typeP.U ≠ ⊥ := data.nontrivial.1
  have : chief.N.Normal := chief.N_normal
  have : NeZero chief.p := ⟨chief.p_prime.pos.ne'⟩
  set act := typeP_quotientCoprimeAction data.typeP hU chief.N_aInvariant with hact
  set φU := act.φ.comp act.U.subtype with hφU
  -- `H̄ = ↥H ⧸ N` is finite elementary abelian `p`, nontrivial, of order `p^q`.
  have hKcard : Nat.card (↥data.H ⧸ chief.N) = chief.p ^ data.q := chiefFactor_quotient_card chief
  have hq_pos : 0 < data.q := Nat.card_pos
  have hKnt : Nontrivial (↥data.H ⧸ chief.N) :=
    Finite.one_lt_card_iff_nontrivial.mp (by
      rw [hKcard]; exact Nat.one_lt_pow hq_pos.ne' chief.p_prime.one_lt)
  -- Module instances for the Singer mechanism, from `chief.quotient_elementaryAbelian`.
  let : IsMulCommutative (↥data.H ⧸ chief.N) :=
    IsMulCommutative.of_comm chief.quotient_elementaryAbelian.comm
  let : CommGroup (↥data.H ⧸ chief.N) := inferInstance
  let : Module (ZMod chief.p) (Additive (↥data.H ⧸ chief.N)) :=
    chief.quotient_elementaryAbelian.zmodModule
  -- An element of `U W₁` centralizing `H` acts trivially on `H̄`.
  have hcentral_triv : ∀ g : ↥(data.typeP.U ⊔ data.typeP.W1),
      (g : G) ∈ Subgroup.centralizer (data.typeP.H : Set G) → act.φ g = 1 := by
    intro g hg
    have hfix : ∀ x : ↥data.typeP.H, (typeP_conjAction data.typeP g) x = x := by
      intro x
      apply Subtype.ext
      rw [typeP_conjAction_apply]
      have hcom : (x : G) * (g : G) = (g : G) * (x : G) :=
        (Subgroup.mem_centralizer_iff.mp hg) (x : G) x.2
      rw [← hcom, mul_assoc, mul_inv_cancel, mul_one]
    ext y
    refine QuotientGroup.induction_on y ?_
    intro x
    change (act.φ g) (QuotientGroup.mk' chief.N x) = QuotientGroup.mk' chief.N x
    have hstep : (act.φ g) (QuotientGroup.mk' chief.N x)
        = QuotientGroup.mk' chief.N ((typeP_conjAction data.typeP g) x) := rfl
    rw [hstep, hfix x]
  -- `Ū = φU.range` is abelian: `φU ⁅a, b⁆ = 1` since `⁅a, b⁆` maps into `[U, U] ⊆ C(H)`.
  have hComm : ∀ a b : ↥act.U, Commute (φU a) (φU b) := by
    intro a b
    refine commutatorElement_eq_one_iff_commute.mp ?_
    rw [← map_commutatorElement φU a b]
    change act.φ (act.U.subtype ⁅a, b⁆) = 1
    apply hcentral_triv
    change ((data.typeP.U ⊔ data.typeP.W1).subtype.comp act.U.subtype) ⁅a, b⁆
        ∈ Subgroup.centralizer (data.typeP.H : Set G)
    rw [map_commutatorElement]
    exact typeP_commutator_U_centralizes_H data.typeP
      (Subgroup.commutator_mem_commutator
        (Subgroup.mem_subgroupOf.mp a.2) (Subgroup.mem_subgroupOf.mp b.2))
  -- Package the data for the Singer mechanism.
  have hAcomm : ∀ s t : ↥(φU.range), s * t = t * s := by
    rintro ⟨_, a, rfl⟩ ⟨_, b, rfl⟩
    exact Subtype.ext (hComm a b)
  have hirr : ∀ J : Subgroup (↥data.H ⧸ chief.N),
      IsAInvariant (φU.range).subtype J → J = ⊥ ∨ J = ⊤ := by
    intro J hJ
    apply hcaseB
    intro a
    exact hJ ⟨φU a, MonoidHom.mem_range.mpr ⟨a, rfl⟩⟩
  have hfaith : ∀ a : ↥(φU.range),
      (∀ x : (↥data.H ⧸ chief.N), ((φU.range).subtype a) x = x) → a = 1 := by
    intro a ha
    have hone : (a : MulAut (↥data.H ⧸ chief.N)) = 1 := by
      ext x
      simpa using ha x
    exact Subtype.ext hone
  -- Thin adapter into the canonical module-level Singer lemma (shared leaf, issue 9000).
  obtain ⟨hcyc, hdvd⟩ := singerAdapter_isCyclic_card_dvd
    (A := ↥(φU.range)) (K := ↥data.H ⧸ chief.N) (p := chief.p)
    (φ := (φU.range).subtype) hAcomm hKnt hirr hfaith
  exact ⟨hcyc, by rwa [hKcard] at hdvd⟩

open OddOrder.RepresentationTheory Representation in
open scoped commutatorElement IsMulCommutative in
/-- **Peterfalvi (9.7) case (b), the fixed-point-free coprimality `Coprime |Ū| (p-1)`.**  When `U`
acts irreducibly on the chief factor `H̄ = H/H₀` (Clifford case (b)), the image `Ū = φ_U(U)` has
order coprime to `p - 1`.

This discharges the hard `coprime` hypothesis of `chiefFactor_caseB_image_dvd_norm` from the
Frobenius structure of `U W₁`: a nonidentity `w₀ ∈ W₁` acts on `Ū` fixed-point-freely.  Indeed if
`act.φ(w₀)` commutes with `φ_U(u)` then `⁅w₀, u⁆` acts trivially on `H̄`, so `u` lies in a
`w₀`-fixed coset of `C_U(H̄)`; Isaacs Cor 3.28 (`coprime_fixedPoints_quotient`) extracts a
`w₀`-fixed
representative `c ∈ u·C_U(H̄)`, and `c ∈ C_U(w₀) = 1` by the Frobenius condition
(`centralizer_complement_le`, `U ⊓ W₁ = ⊥`), forcing `u ∈ C_U(H̄)`, i.e. `φ_U(u) = 1`.  The
canonical module-level `coprime_card_sub_one_of_faithful_irreducible_comm_fpf` (shared
`SingerField` leaf, via `elabRepresentation_isSimpleModule_and_faithful` +
`exists_addEquiv_asModule_fpf`) then gives the coprimality. -/
theorem chiefFactor_caseB_image_coprime [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data)
    (hcaseB : ∀ J : Subgroup (↥data.H ⧸ chief.N),
        IsAInvariant ((typeP_quotientCoprimeAction data.typeP data.nontrivial.1
          chief.N_aInvariant).φ.comp (typeP_quotientCoprimeAction data.typeP data.nontrivial.1
          chief.N_aInvariant).U.subtype) J → J = ⊥ ∨ J = ⊤) :
    Nat.Coprime (Nat.card ↥(((typeP_quotientCoprimeAction data.typeP data.nontrivial.1
          chief.N_aInvariant).φ.comp (typeP_quotientCoprimeAction data.typeP data.nontrivial.1
          chief.N_aInvariant).U.subtype).range)) (chief.p - 1) := by
  classical
  have hU : data.typeP.U ≠ ⊥ := data.nontrivial.1
  have : chief.N.Normal := chief.N_normal
  have : NeZero chief.p := ⟨chief.p_prime.pos.ne'⟩
  have : Fact chief.p.Prime := ⟨chief.p_prime⟩
  set act := typeP_quotientCoprimeAction data.typeP hU chief.N_aInvariant with hact
  set φU := act.φ.comp act.U.subtype with hφU
  have hUnorm : act.U.Normal := (typeP_uW1_frobenius data.typeP hU).isNormal
  have hKcard : Nat.card (↥data.H ⧸ chief.N) = chief.p ^ data.q := chiefFactor_quotient_card chief
  have hq_pos : 0 < data.q := Nat.card_pos
  have hKnt : Nontrivial (↥data.H ⧸ chief.N) :=
    Finite.one_lt_card_iff_nontrivial.mp (by
      rw [hKcard]; exact Nat.one_lt_pow hq_pos.ne' chief.p_prime.one_lt)
  let : IsMulCommutative (↥data.H ⧸ chief.N) :=
    IsMulCommutative.of_comm chief.quotient_elementaryAbelian.comm
  let : CommGroup (↥data.H ⧸ chief.N) := inferInstance
  let : Module (ZMod chief.p) (Additive (↥data.H ⧸ chief.N)) :=
    chief.quotient_elementaryAbelian.zmodModule
  -- Abelianness, irreducibility, faithfulness of `Ū = φU.range` (as in
  -- `chiefFactor_caseB_image_cyclic`).
  have hcentral_triv : ∀ g : ↥(data.typeP.U ⊔ data.typeP.W1),
      (g : G) ∈ Subgroup.centralizer (data.typeP.H : Set G) → act.φ g = 1 := by
    intro g hg
    have hfix : ∀ x : ↥data.typeP.H, (typeP_conjAction data.typeP g) x = x := by
      intro x
      apply Subtype.ext
      rw [typeP_conjAction_apply]
      have hcom : (x : G) * (g : G) = (g : G) * (x : G) :=
        (Subgroup.mem_centralizer_iff.mp hg) (x : G) x.2
      rw [← hcom, mul_assoc, mul_inv_cancel, mul_one]
    ext y
    refine QuotientGroup.induction_on y ?_
    intro x
    change (act.φ g) (QuotientGroup.mk' chief.N x) = QuotientGroup.mk' chief.N x
    have hstep : (act.φ g) (QuotientGroup.mk' chief.N x)
        = QuotientGroup.mk' chief.N ((typeP_conjAction data.typeP g) x) := rfl
    rw [hstep, hfix x]
  have hComm : ∀ a b : ↥act.U, Commute (φU a) (φU b) := by
    intro a b
    refine commutatorElement_eq_one_iff_commute.mp ?_
    rw [← map_commutatorElement φU a b]
    change act.φ (act.U.subtype ⁅a, b⁆) = 1
    apply hcentral_triv
    change ((data.typeP.U ⊔ data.typeP.W1).subtype.comp act.U.subtype) ⁅a, b⁆
        ∈ Subgroup.centralizer (data.typeP.H : Set G)
    rw [map_commutatorElement]
    exact typeP_commutator_U_centralizes_H data.typeP
      (Subgroup.commutator_mem_commutator
        (Subgroup.mem_subgroupOf.mp a.2) (Subgroup.mem_subgroupOf.mp b.2))
  have hAcomm : ∀ s t : ↥(φU.range), s * t = t * s := by
    rintro ⟨_, a, rfl⟩ ⟨_, b, rfl⟩
    exact Subtype.ext (hComm a b)
  have hirr : ∀ J : Subgroup (↥data.H ⧸ chief.N),
      IsAInvariant (φU.range).subtype J → J = ⊥ ∨ J = ⊤ := by
    intro J hJ
    apply hcaseB
    intro a
    exact hJ ⟨φU a, MonoidHom.mem_range.mpr ⟨a, rfl⟩⟩
  have hfaith : ∀ a : ↥(φU.range),
      (∀ x : (↥data.H ⧸ chief.N), ((φU.range).subtype a) x = x) → a = 1 := by
    intro a ha
    have hone : (a : MulAut (↥data.H ⧸ chief.N)) = 1 := by
      ext x
      simpa using ha x
    exact Subtype.ext hone
  -- The fixed-point-free witness: a nonidentity `w₀ ∈ W₁` inside `↥(U ⊔ W₁)`.
  obtain ⟨w, hwW1, hwne⟩ :=
    (data.typeP.W1.bot_or_exists_ne_one).resolve_left data.typeP.W1_nontrivial
  have hwUW1 : w ∈ data.typeP.U ⊔ data.typeP.W1 := Subgroup.mem_sup_right hwW1
  set w₀ : ↥(data.typeP.U ⊔ data.typeP.W1) := ⟨w, hwUW1⟩ with hw₀def
  have hw₀E : w₀ ∈ act.E := by
    change (⟨w, hwUW1⟩ : ↥(data.typeP.U ⊔ data.typeP.W1)) ∈
      data.typeP.W1.subgroupOf (data.typeP.U ⊔ data.typeP.W1)
    rw [Subgroup.mem_subgroupOf]; exact hwW1
  have hw₀ne : w₀ ≠ 1 := fun h => hwne (Subtype.ext_iff.mp h)
  -- Conjugation action `ψ` of `U W₁` on the kernel `act.U`, and how `φU` transforms under it.
  set ψ : ↥(data.typeP.U ⊔ data.typeP.W1) →* MulAut ↥act.U := MulAut.conjNormal with hψdef
  have hψcoe : ∀ (g : ↥(data.typeP.U ⊔ data.typeP.W1)) (y : ↥act.U),
      (act.U.subtype (ψ g y) : ↥(data.typeP.U ⊔ data.typeP.W1)) =
        (g : ↥(data.typeP.U ⊔ data.typeP.W1)) * act.U.subtype y * g⁻¹ :=
    fun g y => MulAut.conjNormal_apply g y
  have hφUconj : ∀ (g : ↥(data.typeP.U ⊔ data.typeP.W1)) (y : ↥act.U),
      φU (ψ g y) = act.φ g * φU y * (act.φ g)⁻¹ := by
    intro g y
    have he : φU (ψ g y) = act.φ ((g : ↥(data.typeP.U ⊔ data.typeP.W1)) * act.U.subtype y * g⁻¹) :=
        by
      change act.φ (act.U.subtype (ψ g y)) = _
      rw [hψcoe]
    rw [he, map_mul, map_mul, map_inv]; rfl
  -- The kernel `N = C_U(H̄)` of `φU`, and its `ψ`-invariance.
  set N : Subgroup ↥act.U := φU.ker with hNdef
  have hN_inv : IsAInvariant (ψ.comp (Subgroup.zpowers w₀).subtype) N := by
    rw [isAInvariant_iff_smul_mem]
    intro a y hy
    rw [hNdef, MonoidHom.mem_ker] at hy ⊢
    change φU (ψ ((Subgroup.zpowers w₀).subtype a) y) = 1
    rw [hφUconj, hy, mul_one, mul_inv_cancel]
  -- Coprimality and solvability inputs for Isaacs Cor 3.28.
  have hCop : Nat.Coprime (Nat.card ↥(Subgroup.zpowers w₀)) (Nat.card ↥act.U) := by
    have hkc : Nat.Coprime (Nat.card ↥act.U) (Nat.card ↥act.E) :=
      (typeP_uW1_frobenius data.typeP hU).coprime_card_kernel_complement
    exact Nat.Coprime.coprime_dvd_left
      (Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr hw₀E)) hkc.symm
  have hSolv : Group.IsSolvable ↥(Subgroup.zpowers w₀) ∨ Group.IsSolvable ↥act.U :=
    Or.inl (Group.isSolvable_of_comm fun a b => by
      obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp a.2
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp b.2
      exact Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hi, ← hj]; group))
  -- The fixed-point-free hypothesis for `σ = act.φ w₀`, in subgroup terms.
  have hfpfσ : ∀ a : ↥(φU.range),
      (∀ x : ↥data.H ⧸ chief.N,
        (act.φ w₀) (((φU.range).subtype a) x) = ((φU.range).subtype a) ((act.φ w₀) x)) →
      a = 1 := by
    intro a ha
    obtain ⟨u₀, hu₀⟩ := a.2
    -- `↑a = φU u₀ = act.φ u₀'`, and `act.φ w₀` commutes with it.
    have ha1 : ((φU.range).subtype a : MulAut (↥data.H ⧸ chief.N)) = act.φ (act.U.subtype u₀) :=
      hu₀.symm
    have hCm : Commute (act.φ w₀) (act.φ (act.U.subtype u₀)) := by
      change act.φ w₀ * act.φ (act.U.subtype u₀) = act.φ (act.U.subtype u₀) * act.φ w₀
      apply MulEquiv.ext
      intro x
      rw [MulAut.mul_apply, MulAut.mul_apply, ← ha1]
      exact ha x
    -- `hg_fix`: each `w₀^k`-conjugate of `u₀` lands in `u₀ · N`.
    have hg_fix : ∀ aa : ↥(Subgroup.zpowers w₀),
        ∃ n ∈ N, (ψ.comp (Subgroup.zpowers w₀).subtype) aa u₀ = u₀ * n := by
      intro aa
      refine ⟨u₀⁻¹ * (ψ ((Subgroup.zpowers w₀).subtype aa) u₀), ?_, ?_⟩
      · rw [hNdef, MonoidHom.mem_ker, map_mul, map_inv, hφUconj]
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp aa.2
        have hcaφ : act.φ ((Subgroup.zpowers w₀).subtype aa) = (act.φ w₀) ^ k := by
          rw [show (Subgroup.zpowers w₀).subtype aa = w₀ ^ k from hk.symm, map_zpow]
        have hcomm_k : Commute (act.φ ((Subgroup.zpowers w₀).subtype aa)) (φU u₀) := by
          rw [hcaφ]; exact hCm.zpow_left k
        rw [show act.φ ((Subgroup.zpowers w₀).subtype aa) * φU u₀ *
              (act.φ ((Subgroup.zpowers w₀).subtype aa))⁻¹ = φU u₀ by
          rw [hcomm_k.eq, mul_assoc, mul_inv_cancel, mul_one], inv_mul_cancel]
      · rw [MonoidHom.comp_apply, mul_inv_cancel_left]
    -- Isaacs Cor 3.28: a `w₀`-fixed representative `c ∈ u₀ · N`.
    obtain ⟨c, hc_fix, n, hn, hc_eq⟩ :=
      OddOrder.Isaacs.Ch04.coprime_fixedPoints_quotient
        (φ := ψ.comp (Subgroup.zpowers w₀).subtype) hCop hSolv hN_inv hg_fix
    -- `c` commutes with `w₀`, so `c ∈ C_U(w₀) ⊆ W₁`; as `c ∈ U`, `c = 1`.
    have hc_w₀ : ψ w₀ c = c := by
      have := hc_fix ⟨w₀, Subgroup.mem_zpowers w₀⟩
      rwa [MonoidHom.comp_apply] at this
    have hc_comm : (act.U.subtype c : ↥(data.typeP.U ⊔ data.typeP.W1)) * w₀ =
        w₀ * act.U.subtype c := by
      have h := congrArg act.U.subtype hc_w₀
      rw [hψcoe] at h
      -- `h : w₀ * subtype c * w₀⁻¹ = subtype c`
      rw [mul_inv_eq_iff_eq_mul] at h
      exact h.symm
    have hc_in_E : (act.U.subtype c : ↥(data.typeP.U ⊔ data.typeP.W1)) ∈ act.E := by
      refine (typeP_uW1_frobenius data.typeP hU).centralizer_complement_le w₀ hw₀E hw₀ne ?_
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hc_comm
    have hc_in_U : (act.U.subtype c : ↥(data.typeP.U ⊔ data.typeP.W1)) ∈ act.U := c.2
    have hc1 : (act.U.subtype c : ↥(data.typeP.U ⊔ data.typeP.W1)) = 1 :=
      Subgroup.disjoint_def.mp (typeP_uW1_frobenius data.typeP hU).isComplement.disjoint
        hc_in_U hc_in_E
    have hc0 : c = 1 := act.U.subtype_injective (by rw [hc1, map_one])
    -- `1 = c = u₀ · n` ⟹ `u₀ ∈ N` ⟹ `φU u₀ = 1` ⟹ `a = 1`.
    rw [hc0] at hc_eq
    have hu₀N : u₀ ∈ N := by
      have : u₀ = n⁻¹ := by rw [eq_inv_iff_mul_eq_one, ← hc_eq]
      rw [this]; exact N.inv_mem hn
    apply Subtype.ext
    rw [← hu₀, Subgroup.coe_one]
    exact (MonoidHom.mem_ker (f := φU)).mp hu₀N
  -- Thin adapter into the canonical module-level Singer FPF-coprimality (shared leaf, issue 9000).
  exact singerAdapter_coprime_fpf
    (A := ↥(φU.range)) (K := ↥data.H ⧸ chief.N) (p := chief.p) (φ := (φU.range).subtype)
    hAcomm hKnt hirr hfaith (act.φ w₀) hfpfσ

open OddOrder.RepresentationTheory Representation in
open scoped commutatorElement IsMulCommutative in
/-- **Peterfalvi (9.7) case (b), the `u ∣ (p^q-1)/(p-1)` divisibility** (unconditional).

The Singer divisibility `|Ū| ∣ p^q-1` (`chiefFactor_caseB_image_cyclic`) upgrades to
`|Ū| ∣ (p^q-1)/(p-1)` via the fixed-point-free coprimality `Coprime |Ū| (p-1)`
(`chiefFactor_caseB_image_coprime`): since `(p-1) ∣ (p^q-1)` and `|Ū|` is coprime to `p-1`,
`|Ū|·(p-1) ∣ p^q-1`, hence `|Ū| ∣ (p^q-1)/(p-1)`.  This is the second case-(b) divisibility of
`CliffordCaseBData`, now established without any external coprimality hypothesis. -/
theorem chiefFactor_caseB_image_dvd_norm [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data)
    (hcaseB : ∀ J : Subgroup (↥data.H ⧸ chief.N),
        IsAInvariant ((typeP_quotientCoprimeAction data.typeP data.nontrivial.1
          chief.N_aInvariant).φ.comp (typeP_quotientCoprimeAction data.typeP data.nontrivial.1
          chief.N_aInvariant).U.subtype) J → J = ⊥ ∨ J = ⊤) :
    Nat.card ↥(((typeP_quotientCoprimeAction data.typeP data.nontrivial.1
          chief.N_aInvariant).φ.comp (typeP_quotientCoprimeAction data.typeP data.nontrivial.1
          chief.N_aInvariant).U.subtype).range) ∣ (chief.p ^ data.q - 1) / (chief.p - 1) := by
  have hcop := chiefFactor_caseB_image_coprime chief hcaseB
  obtain ⟨_, hdvd⟩ := chiefFactor_caseB_image_cyclic chief hcaseB
  -- The arithmetic core is the shared `SingerLineBound` lemma (issue 9000 dedup).
  exact dvd_div_of_coprime_of_dvd_sub_one chief.p_prime.pos hdvd hcop

open scoped commutatorElement in
/-- **Peterfalvi (9.7) case (b): the `U`-action on `H̄` is fixed-point-free off `C = C_U(H̄)`.**
When `U` acts irreducibly on the chief factor `H̄ = H/H₀` (Clifford case (b)), any `g ∈ U` whose
image `φ_U(g)` is nontrivial (i.e. `g ∉ C`) acts fixed-point-freely on `H̄`: `φ_U(g)·x = x → x = 1`.

This is the structural heart of Peterfalvi (9.9) — `H̄ ⋊ Ū` is a Frobenius group, so a nontrivial
character `θ` of `H̄` has inertia `I(θ) ∩ U = C`, giving the degree `u = |U:C|` of the irreducible
characters of `HU` in `𝒳(H₀C')`.  The proof is pure Clifford theory: the image `Ū = φ_U(U)` is
abelian (`hComm`: `⁅a,b⁆ ∈ [U,U] ⊆ C_M(H)`) and acts irreducibly (`hcaseB`), so
`fixedPointFree_of_aInvariant_irreducible_comm` applies; the Singer field model is *not* needed. -/
theorem chiefFactor_caseB_action_fpf [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data)
    (hcaseB : ∀ J : Subgroup (↥data.H ⧸ chief.N),
        IsAInvariant ((typeP_quotientCoprimeAction data.typeP data.nontrivial.1
          chief.N_aInvariant).φ.comp (typeP_quotientCoprimeAction data.typeP data.nontrivial.1
          chief.N_aInvariant).U.subtype) J → J = ⊥ ∨ J = ⊤)
    (g : ↥(typeP_quotientCoprimeAction data.typeP data.nontrivial.1 chief.N_aInvariant).U)
    (hg : ((typeP_quotientCoprimeAction data.typeP data.nontrivial.1
          chief.N_aInvariant).φ.comp (typeP_quotientCoprimeAction data.typeP data.nontrivial.1
          chief.N_aInvariant).U.subtype) g ≠ 1)
    (x : ↥data.H ⧸ chief.N)
    (hx : ((typeP_quotientCoprimeAction data.typeP data.nontrivial.1
          chief.N_aInvariant).φ.comp (typeP_quotientCoprimeAction data.typeP data.nontrivial.1
          chief.N_aInvariant).U.subtype) g x = x) : x = 1 := by
  classical
  have : chief.N.Normal := chief.N_normal
  set act := typeP_quotientCoprimeAction data.typeP data.nontrivial.1 chief.N_aInvariant with hact
  set φU := act.φ.comp act.U.subtype with hφU
  -- An element of `U W₁` centralizing `H` acts trivially on `H̄`.
  have hcentral_triv : ∀ c : ↥(data.typeP.U ⊔ data.typeP.W1),
      (c : G) ∈ Subgroup.centralizer (data.typeP.H : Set G) → act.φ c = 1 := by
    intro c hc
    have hfix : ∀ z : ↥data.typeP.H, (typeP_conjAction data.typeP c) z = z := by
      intro z
      apply Subtype.ext
      rw [typeP_conjAction_apply]
      have hcom : (z : G) * (c : G) = (c : G) * (z : G) :=
        (Subgroup.mem_centralizer_iff.mp hc) (z : G) z.2
      rw [← hcom, mul_assoc, mul_inv_cancel, mul_one]
    ext y
    refine QuotientGroup.induction_on y ?_
    intro z
    change (act.φ c) (QuotientGroup.mk' chief.N z) = QuotientGroup.mk' chief.N z
    have hstep : (act.φ c) (QuotientGroup.mk' chief.N z)
        = QuotientGroup.mk' chief.N ((typeP_conjAction data.typeP c) z) := rfl
    rw [hstep, hfix z]
  -- `Ū = φU(U)` is abelian: `φU ⁅a, b⁆ = 1` since `⁅a, b⁆` maps into `[U, U] ⊆ C(H)`.
  have hComm : ∀ a b : ↥act.U, Commute (φU a) (φU b) := by
    intro a b
    refine commutatorElement_eq_one_iff_commute.mp ?_
    rw [← map_commutatorElement φU a b]
    change act.φ (act.U.subtype ⁅a, b⁆) = 1
    apply hcentral_triv
    change ((data.typeP.U ⊔ data.typeP.W1).subtype.comp act.U.subtype) ⁅a, b⁆
        ∈ Subgroup.centralizer (data.typeP.H : Set G)
    rw [map_commutatorElement]
    exact typeP_commutator_U_centralizes_H data.typeP
      (Subgroup.commutator_mem_commutator
        (Subgroup.mem_subgroupOf.mp a.2) (Subgroup.mem_subgroupOf.mp b.2))
  exact fixedPointFree_of_aInvariant_irreducible_comm hComm hcaseB _ hg x hx

/-- **Peterfalvi (9.9): the `U`-action on `Irr(H̄)` is fixed-point-free off `C`.**  In Clifford
case (b), if a nontrivial irreducible character `θ` of the chief factor `H̄ = ↥H ⧸ N` is invariant
under the `U`-action `φ_U(g)`, then `g` acts trivially (`φ_U(g) = 1`, i.e. `g ∈ C = C_U(H̄)`).

This is the **character-side inertia** `I_U(θ) ⊆ C` of Peterfalvi (9.9.a), proven
*realization-free*:
the abelian `Irr ↔ Hom` bridge
(`exists_units_monoidHom_of_isIrreducibleCharacter_of_isMulCommutative`)
turns `θ` into a linear character `θ̂`, and a `φ_U(g)`-invariant `θ̂` with `φ_U(g)` fixed-point-free
(`chiefFactor_caseB_action_fpf`, valid for `g ∉ C`) is trivial
(`eq_one_of_invariant_of_fixedPointFree`), contradicting `θ` nontrivial.  No realization of `H̄` as
a subgroup is needed; it works on the abstract quotient `↥H ⧸ N` with the abstract action `φ_U`. -/
theorem chiefFactor_caseB_char_inertia [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    (hcaseB : ∀ J : Subgroup (↥data.H ⧸ chief.N),
        IsAInvariant ((typeP_quotientCoprimeAction data.typeP data.nontrivial.1
          chief.N_aInvariant).φ.comp (typeP_quotientCoprimeAction data.typeP data.nontrivial.1
          chief.N_aInvariant).U.subtype) J → J = ⊥ ∨ J = ⊤)
    {θ : IrreducibleCharacter (↥data.H ⧸ chief.N)}
    (hθ : (θ : ClassFunction (↥data.H ⧸ chief.N) ℂ) ≠ trivialClassFunction _)
    (g : ↥(typeP_quotientCoprimeAction data.typeP data.nontrivial.1 chief.N_aInvariant).U)
    (hinv : ∀ x, (θ : ClassFunction (↥data.H ⧸ chief.N) ℂ)
        (((typeP_quotientCoprimeAction data.typeP data.nontrivial.1 chief.N_aInvariant).φ.comp
          (typeP_quotientCoprimeAction data.typeP data.nontrivial.1
            chief.N_aInvariant).U.subtype) g x)
          = (θ : ClassFunction (↥data.H ⧸ chief.N) ℂ) x) :
    ((typeP_quotientCoprimeAction data.typeP data.nontrivial.1 chief.N_aInvariant).φ.comp
      (typeP_quotientCoprimeAction data.typeP data.nontrivial.1 chief.N_aInvariant).U.subtype) g
        = 1 := by
  classical
  have : IsMulCommutative (↥data.H ⧸ chief.N) :=
    IsMulCommutative.of_comm chief.quotient_elementaryAbelian.comm
  by_contra hne
  have hfpf : MonoidHom.FixedPointFree
      (((typeP_quotientCoprimeAction data.typeP data.nontrivial.1 chief.N_aInvariant).φ.comp
        (typeP_quotientCoprimeAction data.typeP data.nontrivial.1
          chief.N_aInvariant).U.subtype) g) :=
    chiefFactor_caseB_action_fpf chief hcaseB g hne
  obtain ⟨θhom, hθhom⟩ :=
    exists_units_monoidHom_of_isIrreducibleCharacter_of_isMulCommutative θ.isIrreducible
  have hinvhom : ∀ x, θhom (((typeP_quotientCoprimeAction data.typeP data.nontrivial.1
      chief.N_aInvariant).φ.comp (typeP_quotientCoprimeAction data.typeP data.nontrivial.1
      chief.N_aInvariant).U.subtype) g x) = θhom x := fun x =>
    Units.ext (by rw [hθhom, hθhom]; exact hinv x)
  have h1 : θhom = 1 := eq_one_of_invariant_of_fixedPointFree hfpf hinvhom
  apply hθ
  ext x
  have hx := hθhom x
  rw [h1] at hx
  simpa using hx.symm

/-- **Non-Galois (9.8) core, generic over the factor family.**  As `chiefFactor_caseA_char_inertia`
but taking the order-`p`, `U`-invariant, spanning factor family `Hpart` directly (rather than from
`CliffordCaseAData`), so the `W1`-conjugates `{S₀^w}` — which have the same properties but are not
the producer's `caseA.Hpart` family — can drive the inertia argument for the free-`W1`-orbit
character of (9.8.c). -/
theorem chiefFactor_caseA_char_inertia_gen [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {ι : Type*} (Hpart : ι → Subgroup (↥data.H ⧸ chief.N))
    (hp_order : ∀ i, Nat.card ↥(Hpart i) = chief.p)
    (hspan : ⨆ i, Hpart i = ⊤)
    (haInv : ∀ i, IsAInvariant (uActionHom data chief) (Hpart i))
    {θ : IrreducibleCharacter (↥data.H ⧸ chief.N)}
    (hreg : ∀ i, ∃ x ∈ Hpart i,
      (θ : ClassFunction (↥data.H ⧸ chief.N) ℂ) x
        ≠ (θ : ClassFunction (↥data.H ⧸ chief.N) ℂ) 1)
    (g : ↥(typeP_quotientCoprimeAction data.typeP data.nontrivial.1 chief.N_aInvariant).U)
    (hinv : ∀ x, (θ : ClassFunction (↥data.H ⧸ chief.N) ℂ) ((uActionHom data chief) g x)
        = (θ : ClassFunction (↥data.H ⧸ chief.N) ℂ) x) :
    (uActionHom data chief) g = 1 := by
  have : IsMulCommutative (↥data.H ⧸ chief.N) :=
    IsMulCommutative.of_comm chief.quotient_elementaryAbelian.comm
  refine mulAut_eq_one_of_fixes_regular_on_prime_span ((uActionHom data chief) g) Hpart
    (fun i => ?_) (fun i x hx => ?_) hspan θ hreg hinv
  · rw [hp_order i]; exact chief.p_prime
  · exact (haInv i).smul_mem g hx

set_option backward.isDefEq.respectTransparency false in
/-- **Peterfalvi (9.8.d) single-factor char-inertia core**: the single-factor analog of
`chiefFactor_caseA_char_inertia`.  For a character `θ₁` nontrivial on the order-`p` orbit generator
`S₀ = H₁` (`hreg` on `caseA.S0`), a `U`-element `g` fixing `θ₁` acts *trivially on `S₀`*, i.e.
`aInvariantRestrictAut caseA.S0_aInvariant g = 1`.  This — not `uActionHom g = 1` — is the correct
conclusion for (9.8.d): `θ₁` need only be faithful on the *single* summand `S₀`, so the fixing
element centralizes `S₀` (lands in `C_U(S₀)`), not necessarily all of `H̄`.  The pure-algebra heart
is `mulAut_eq_id_on_of_fixes_ne_one_on_prime` (`θ₁` faithful on the prime-order `S₀`), lifted
through
`aInvariantRestrictAut_coe` (which identifies the restricted action with `uActionHom` on `S₀`).
This
gives `I(θ₁) ∩ U ⊆ C_U(S₀)` in the degree-`qa` inertia lift. -/
theorem chiefFactor_caseA_char_inertia_single [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars)
    {θ : IrreducibleCharacter (↥data.H ⧸ chief.N)}
    (hreg : ∃ x ∈ caseA.S0,
      (θ : ClassFunction (↥data.H ⧸ chief.N) ℂ) x
        ≠ (θ : ClassFunction (↥data.H ⧸ chief.N) ℂ) 1)
    (g : ↥(typeP_quotientCoprimeAction data.typeP data.nontrivial.1 chief.N_aInvariant).U)
    (hinv : ∀ x, (θ : ClassFunction (↥data.H ⧸ chief.N) ℂ) ((uActionHom data chief) g x)
        = (θ : ClassFunction (↥data.H ⧸ chief.N) ℂ) x) :
    aInvariantRestrictAut caseA.S0_aInvariant g = 1 := by
  have : IsMulCommutative (↥data.H ⧸ chief.N) :=
    IsMulCommutative.of_comm chief.quotient_elementaryAbelian.comm
  -- `φg = uActionHom g` acts as the identity on the prime-order summand `S₀` (single-factor core).
  have hS0card : Nat.card ↥caseA.S0 = chief.p := by
    have h := caseA.Hpart_order ⟨0, data.nontrivial.2.1.pos⟩
    rwa [caseA.Hpart_orbit ⟨0, data.nontrivial.2.1.pos⟩, card_pointwise_smul] at h
  have hid : ∀ x ∈ caseA.S0, (uActionHom data chief) g x = x :=
    mulAut_eq_id_on_of_fixes_ne_one_on_prime ((uActionHom data chief) g) caseA.S0
      (by rw [hS0card]; exact chief.p_prime)
      (fun x hx => caseA.S0_aInvariant.smul_mem g hx) θ hreg hinv
  -- Lift to `aInvariantRestrictAut … g = 1` via the coercion
  -- `(restrict g x : H̄) = uActionHom g x`.
  ext x
  rw [MulAut.one_apply, aInvariantRestrictAut_coe, hid x x.2]

/-- **Inflation equivariance for the chief-factor action.**  The inflation map
`compHom (mk' N) : ClassFunction (↥H/N) → ClassFunction ↥H` intertwines the conjugation action
`typeP_conjAction a` on `↥H` (upstairs) with the descended action `quotientMulAutHom a` on the
chief factor `↥H/N` (downstairs): inflating `θ̄` and acting by `a` upstairs equals acting by `a`
downstairs and then inflating.  Immediate from `quotientMulAutHom_apply_mk'`
(`mk' N (a · h) = a · (mk' N h)`).

This is the algebraic core that turns the *concrete* conjugation invariance of an inflated
character into the *abstract* `φ_U`-invariance consumed by `chiefFactor_caseB_char_inertia`,
without realizing `H̄` as a subgroup. -/
theorem compHom_typeP_conjAction_inflation [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    (a : ↥(data.typeP.U ⊔ data.typeP.W1))
    (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ) :
    ClassFunction.compHom (typeP_conjAction data.typeP a).toMonoidHom
        (ClassFunction.compHom (QuotientGroup.mk' chief.N) θbar)
      = ClassFunction.compHom (QuotientGroup.mk' chief.N)
          (ClassFunction.compHom (quotientMulAutHom chief.N_aInvariant a).toMonoidHom θbar) :=
  rfl

/-- **Char-inertia inflation, parametrized over the core stabilizer-triviality `hcore`.**
Strips the inflation (`compHom_typeP_conjAction_inflation`, `mk'` injective) from the
`compHom`-fixing
hypothesis to feed the per-element action-invariance to `hcore`.  Case (b) supplies `hcore` as
`chiefFactor_caseB_char_inertia` (`U`-irreducible); case (a) via the non-Galois `Hpart` analysis. -/
theorem caseB_char_inertia_inflation_of_core [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {θbar : IrreducibleCharacter (↥data.H ⧸ chief.N)}
    (hcore : ∀ (g : ↥(typeP_quotientCoprimeAction data.typeP data.nontrivial.1
          chief.N_aInvariant).U),
        (∀ x, (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ)
            (((typeP_quotientCoprimeAction data.typeP data.nontrivial.1 chief.N_aInvariant).φ.comp
              (typeP_quotientCoprimeAction data.typeP data.nontrivial.1
                chief.N_aInvariant).U.subtype) g x)
              = (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ) x) →
        ((typeP_quotientCoprimeAction data.typeP data.nontrivial.1 chief.N_aInvariant).φ.comp
          (typeP_quotientCoprimeAction data.typeP data.nontrivial.1
            chief.N_aInvariant).U.subtype) g = 1)
    (g : ↥(typeP_quotientCoprimeAction data.typeP data.nontrivial.1 chief.N_aInvariant).U)
    (hfix : ClassFunction.compHom (typeP_conjAction data.typeP
              ((typeP_quotientCoprimeAction data.typeP data.nontrivial.1
                chief.N_aInvariant).U.subtype g)).toMonoidHom
              (ClassFunction.compHom (QuotientGroup.mk' chief.N)
                (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ))
            = ClassFunction.compHom (QuotientGroup.mk' chief.N)
                (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ)) :
    ((typeP_quotientCoprimeAction data.typeP data.nontrivial.1 chief.N_aInvariant).φ.comp
      (typeP_quotientCoprimeAction data.typeP data.nontrivial.1
        chief.N_aInvariant).U.subtype) g = 1 := by
  rw [compHom_typeP_conjAction_inflation] at hfix
  have hfix2 := ClassFunction.compHom_injective_of_surjective
    (QuotientGroup.mk'_surjective chief.N) hfix
  apply hcore g
  intro x
  rw [show ((typeP_quotientCoprimeAction data.typeP data.nontrivial.1
        chief.N_aInvariant).φ.comp (typeP_quotientCoprimeAction data.typeP data.nontrivial.1
        chief.N_aInvariant).U.subtype) g
      = quotientMulAutHom chief.N_aInvariant
          ((typeP_quotientCoprimeAction data.typeP data.nontrivial.1
            chief.N_aInvariant).U.subtype g) from rfl]
  exact congrFun (congrArg (fun f : ClassFunction (↥data.H ⧸ chief.N) ℂ =>
    (f : (↥data.H ⧸ chief.N) → ℂ)) hfix2) x

theorem caseB_char_inertia_inflation [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    (hcaseB : ∀ J : Subgroup (↥data.H ⧸ chief.N),
        IsAInvariant ((typeP_quotientCoprimeAction data.typeP data.nontrivial.1
          chief.N_aInvariant).φ.comp (typeP_quotientCoprimeAction data.typeP data.nontrivial.1
          chief.N_aInvariant).U.subtype) J → J = ⊥ ∨ J = ⊤)
    {θbar : IrreducibleCharacter (↥data.H ⧸ chief.N)}
    (hθbar : (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ) ≠ trivialClassFunction _)
    (g : ↥(typeP_quotientCoprimeAction data.typeP data.nontrivial.1 chief.N_aInvariant).U)
    (hfix : ClassFunction.compHom (typeP_conjAction data.typeP
              ((typeP_quotientCoprimeAction data.typeP data.nontrivial.1
                chief.N_aInvariant).U.subtype g)).toMonoidHom
              (ClassFunction.compHom (QuotientGroup.mk' chief.N)
                (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ))
            = ClassFunction.compHom (QuotientGroup.mk' chief.N)
                (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ)) :
    ((typeP_quotientCoprimeAction data.typeP data.nontrivial.1 chief.N_aInvariant).φ.comp
      (typeP_quotientCoprimeAction data.typeP data.nontrivial.1
        chief.N_aInvariant).U.subtype) g = 1 :=
  caseB_char_inertia_inflation_of_core (chiefFactor_caseB_char_inertia hcaseB hθbar) g hfix

/-- The realization iso `↥(H-in-HU) ≃* ↥H`: `H` realized inside `HU = H ⊔ U` is `H`, via the
composite of `subgroupOfEquivOfLe (H.subgroupOf M ≤ HU)` and `subgroupOfEquivOfLe (H ≤ M)`. -/
noncomputable def hInHuEquivH {M : Subgroup G} (data : TypesIIIIIIVSetup M) :
    ↥(hInHu data) ≃* ↥data.H :=
  (Subgroup.subgroupOfEquivOfLe
      (Subgroup.subgroupOf_mono M (le_sup_left : data.H ≤ data.H ⊔ data.U))).trans
    (Subgroup.subgroupOfEquivOfLe (data.typeP.H_le.trans (derivedInG_le_self M)))

/-- The realization iso preserves the underlying `G`-element. -/
theorem hInHuEquivH_coe {M : Subgroup G} (data : TypesIIIIIIVSetup M) (h : ↥(hInHu data)) :
    ((hInHuEquivH data h : ↥data.H) : G) = (((h : ↥(huSub data)) : ↥M) : G) := rfl

/-- **(9.9.a) realization, conjugation equivariance.**  Under the iso
`hInHuEquivH : ↥(hInHu) ≃* ↥H`, the concrete conjugation `conjBy g` in `HU` (for `g ∈ HU`)
corresponds to the abstract conjugation `typeP_conjAction a` on `↥H` (for `a ∈ U W₁` with the same
`G`-image `↑g = ↑a`).  Both are conjugation by the same `G`-element, so the equality reduces to
`g·h·g⁻¹ = a·h·a⁻¹` in `G`. -/
theorem conjBy_compHom_hInHuEquivH {M : Subgroup G} (data : TypesIIIIIIVSetup M)
    (a : ↥(data.typeP.U ⊔ data.typeP.W1)) (g : ↥(huSub data))
    (hag : ((g : ↥M) : G) = (a : G)) (θ : ClassFunction ↥data.H ℂ) :
    ClassFunction.conjBy g (ClassFunction.compHom (hInHuEquivH data).toMonoidHom θ)
      = ClassFunction.compHom (hInHuEquivH data).toMonoidHom
          (ClassFunction.compHom (typeP_conjAction data.typeP a).toMonoidHom θ) := by
  ext h
  rw [ClassFunction.conjBy_apply, ClassFunction.compHom_apply, ClassFunction.compHom_apply,
    ClassFunction.compHom_apply]
  refine congrArg _ (Subtype.ext ?_)
  simp only [MulEquiv.coe_toMonoidHom, hInHuEquivH_coe, typeP_conjAction_apply,
    Subgroup.coe_mul, Subgroup.coe_inv]
  rw [hag]

/-- **Realized stabilizer-triviality, parametrized over the char-inertia core `hcharInertia`.**
The case-agnostic transport: a `U`-element `a` realized by `g ∈ HU` fixing `θ₀` (`conjBy` form) is
turned into the `compHom (typeP_conjAction)` form (`conjBy_compHom_hInHuEquivH`, injective
inflation)
and fed to `hcharInertia` to conclude `φ a = 1`.  Case (b) supplies `hcharInertia` as
`caseB_char_inertia_inflation`; case (a) via the non-Galois analog. -/
theorem caseB_inertia_realized_of_charInertia [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {θbar : IrreducibleCharacter (↥data.H ⧸ chief.N)}
    (hcharInertia : ∀ (g : ↥(typeP_quotientCoprimeAction data.typeP data.nontrivial.1
          chief.N_aInvariant).U),
        ClassFunction.compHom (typeP_conjAction data.typeP
              ((typeP_quotientCoprimeAction data.typeP data.nontrivial.1
                chief.N_aInvariant).U.subtype g)).toMonoidHom
              (ClassFunction.compHom (QuotientGroup.mk' chief.N)
                (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ))
            = ClassFunction.compHom (QuotientGroup.mk' chief.N)
                (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ) →
        ((typeP_quotientCoprimeAction data.typeP data.nontrivial.1 chief.N_aInvariant).φ.comp
          (typeP_quotientCoprimeAction data.typeP data.nontrivial.1
            chief.N_aInvariant).U.subtype) g = 1)
    (a : ↥(typeP_quotientCoprimeAction data.typeP data.nontrivial.1 chief.N_aInvariant).U)
    (g : ↥(huSub data))
    (hag : ((g : ↥M) : G) =
      (((typeP_quotientCoprimeAction data.typeP data.nontrivial.1
        chief.N_aInvariant).U.subtype a : ↥(data.typeP.U ⊔ data.typeP.W1)) : G))
    (hfix : ClassFunction.conjBy g
        (ClassFunction.compHom (hInHuEquivH data).toMonoidHom
          (ClassFunction.compHom (QuotientGroup.mk' chief.N)
            (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ)))
      = ClassFunction.compHom (hInHuEquivH data).toMonoidHom
          (ClassFunction.compHom (QuotientGroup.mk' chief.N)
            (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ))) :
    ((typeP_quotientCoprimeAction data.typeP data.nontrivial.1 chief.N_aInvariant).φ.comp
      (typeP_quotientCoprimeAction data.typeP data.nontrivial.1
        chief.N_aInvariant).U.subtype) a = 1 := by
  rw [conjBy_compHom_hInHuEquivH data
    ((typeP_quotientCoprimeAction data.typeP data.nontrivial.1 chief.N_aInvariant).U.subtype a)
    g hag] at hfix
  exact hcharInertia a
    (ClassFunction.compHom_injective_of_surjective (hInHuEquivH data).surjective hfix)

theorem caseB_inertia_realized [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    (hcaseB : ∀ J : Subgroup (↥data.H ⧸ chief.N),
        IsAInvariant ((typeP_quotientCoprimeAction data.typeP data.nontrivial.1
          chief.N_aInvariant).φ.comp (typeP_quotientCoprimeAction data.typeP data.nontrivial.1
          chief.N_aInvariant).U.subtype) J → J = ⊥ ∨ J = ⊤)
    {θbar : IrreducibleCharacter (↥data.H ⧸ chief.N)}
    (hθbar : (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ) ≠ trivialClassFunction _)
    (a : ↥(typeP_quotientCoprimeAction data.typeP data.nontrivial.1 chief.N_aInvariant).U)
    (g : ↥(huSub data))
    (hag : ((g : ↥M) : G) =
      (((typeP_quotientCoprimeAction data.typeP data.nontrivial.1
        chief.N_aInvariant).U.subtype a : ↥(data.typeP.U ⊔ data.typeP.W1)) : G))
    (hfix : ClassFunction.conjBy g
        (ClassFunction.compHom (hInHuEquivH data).toMonoidHom
          (ClassFunction.compHom (QuotientGroup.mk' chief.N)
            (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ)))
      = ClassFunction.compHom (hInHuEquivH data).toMonoidHom
          (ClassFunction.compHom (QuotientGroup.mk' chief.N)
            (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ))) :
    ((typeP_quotientCoprimeAction data.typeP data.nontrivial.1 chief.N_aInvariant).φ.comp
      (typeP_quotientCoprimeAction data.typeP data.nontrivial.1
        chief.N_aInvariant).U.subtype) a = 1 :=
  caseB_inertia_realized_of_charInertia (caseB_char_inertia_inflation hcaseB hθbar) a g hag hfix

end OddOrder.Peterfalvi.S11


