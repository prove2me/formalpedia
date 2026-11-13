-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S11_MaximalII_III_IV_InnerCompHom
-- name    : OddOrder_Peterfalvi_S11_MaximalII_III_IV_InnerCompHom
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T12:07:24.536207+00:00
-- url     : https://prove2.me/theorems/5d978eea-b78f-400b-944a-617b93b86390
-- title:
--   Peterfalvi (9.9.c): the inner-complement homomorphism and the $u$-formula (continuation)
-- statement:
--   A continuation file in the Clifford case analysis. It computes the degree and kernel properties of $\zeta = \mathrm{Ind}_{HC}^{HU}(\psi)$ and proves the $u$-formula half of Peterfalvi (9.9.c) in case (b).
--
--   Main declarations: `hcZeta_apply_one` (`ζ(1) = u`); `hcZeta_H0supC_subset_ker` (`H₀C ⊆ Ker ζ`); `hcZeta_mem_xiSet` (`H ⊄ Ker ζ`); `hcZeta_mem_xiOf` (`ζ ∈ 𝒳(H₀C)`).
--
--   The bundle also proves 26 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S11_MaximalII_III_IV/InnerCompHom.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S11_MaximalII_III_IV/InnerCompHom.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S11_MaximalII_III_IV_CaseBXi
import Definitions.Def_OddOrder_Peterfalvi_S11_MaximalII_III_IV_InnerCompHomBasic

namespace OddOrder.Peterfalvi.S11

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

open OddOrder.Isaacs.Ch03 (IsAInvariant isAInvariant_iff_smul_mem)

open OddOrder.Isaacs.Ch03.IsAInvariant (quotientMulAutHom)

variable {M : Subgroup G}

set_option maxHeartbeats 1000000 in
-- raised heartbeat budget for the heavy elaboration below
/-- **`ζ(1) = u`**: the degree of `ζ = Ind_{HC}^{HU}(ψ)` is `u`.  `induce_apply_one` gives
`ζ(1) = [HU:HC]·ψ(1) = u·1` (`hc_index_eq_u`, and `ψ` linear so `ψ(1)=1`).  This is the degree-`u`
of the (9.8.c) irreducible; `induceHU ζ` then has degree `q·u = qu`. -/
theorem hcZeta_apply_one [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    (chars : Section11CharacterData data chief)
    (θ : (↥data.H ⧸ chief.N) →* ℂˣ)
    [Fintype ↥(huSub data)]
    [Finite ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))]
    [Invertible (Nat.card ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
      (huSub data)) : ℂ)] :
    ClassFunction.induce
        (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))
        (hcPsi chief θ : ClassFunction
          ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)) ℂ)
        (1 : ↥(huSub data))
      = (chars.u : ℂ) := by
  have : Fintype ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
    (huSub data)) := Fintype.ofFinite _
  rw [ClassFunction.induce_apply_one, hc_index_eq_u chars,
    show (hcPsi chief θ : ClassFunction
        ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)) ℂ)
        (1 : ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)))
        = 1 from by simp [hcPsi], mul_one]

/-- **`H₀C ⊆ Ker ψ`** (`HC`-level, pointwise): every `x` in the realized `H₀C` lies in the character
kernel of the `HC`-linear character `ψ`, since `ψ = θ ∘ hcHom` and `hcHom` kills `H₀C`
(`hcHom_eq_one_of_mem_realizedH0supC`).  Stated *without* the induce/Fintype/Invertible instances so
the giant `HC` term never enters a `whnf`-exploding unification; the induce-kernel step below cites
it
pointwise. -/
theorem hcPsi_mem_characterKernel_of_mem_realizedH0supC [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data)
    (θ : (↥data.H ⧸ chief.N) →* ℂˣ)
    {x : ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))}
    (hx : x ∈ (((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)).subgroupOf
      (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))) :
    x ∈ OddOrder.Peterfalvi.S03.characterKernel (hcPsi chief θ : ClassFunction
        ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)) ℂ) := by
  rw [OddOrder.Peterfalvi.S03.mem_characterKernel]
  simp only [hcPsi]
  rw [linearIrreducibleCharacter_apply, OddOrder.Peterfalvi.S03.characterDegree_def,
    linearIrreducibleCharacter_apply_one, MonoidHom.comp_apply,
    hcHom_eq_one_of_mem_realizedH0supC chief hx, map_one, Units.val_one]

/-- **`H₀C ⊆ Ker ψ`** as a `Set` inclusion (`HC`-level), instance-free.  Packages the pointwise
`hcPsi_mem_characterKernel_of_mem_realizedH0supC` into the `hker` argument of
`subsetCharacterKernel_induce_of_subgroupOf`, kept *outside* the induce/Invertible instance scope so
the giant `HC` card never enters an `isDefEq`-exploding comparison. -/
theorem hcPsi_realizedH0supC_subgroupOf_subset_characterKernel [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data)
    (θ : (↥data.H ⧸ chief.N) →* ℂˣ) :
    ((((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)).subgroupOf
        (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)) :
        Set ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))) ⊆
      OddOrder.Peterfalvi.S03.characterKernel (hcPsi chief θ) := by
  intro x hx
  exact hcPsi_mem_characterKernel_of_mem_realizedH0supC chief θ (SetLike.mem_coe.mp hx)

set_option maxHeartbeats 1000000 in
-- raised heartbeat budget for the heavy elaboration below
/-- **`H₀C ⊆ Ker ζ`**: the realized `H₀C` lies in the character kernel of `ζ = Ind_{HC}^{HU}(ψ)`.
Since `ψ` is `1` on `H₀C` (`hcPsi_mem_characterKernel_of_mem_realizedH0supC`) and `H₀C ◁ HC ≤ HU`,
the normal subgroup `H₀C` lies in `Ker(Ind ψ)` (`subsetCharacterKernel_induce_of_subgroupOf`).  This
is the `H₀C ⊆ Ker` half of `ζ ∈ 𝒳(H₀C)`.  The pointwise body is delegated to the instance-free
lemma above so the giant `HC`/`ψ` term never enters a `whnf`-exploding manipulation here. -/
theorem hcZeta_H0supC_subset_ker [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data)
    (θ : (↥data.H ⧸ chief.N) →* ℂˣ)
    [Fintype ↥(huSub data)]
    [Finite ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))]
    [Invertible (Nat.card
        ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)) : ℂ)] :
    ((((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data) : Set ↥(huSub data))) ⊆
      OddOrder.Peterfalvi.S03.characterKernel (ClassFunction.induce
        (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))
        (hcPsi chief θ)) := by
  have : Fintype ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
    (huSub data)) := Fintype.ofFinite _
  have := realizedH0supC_normal_huSub chief
  exact OddOrder.Peterfalvi.S03.subsetCharacterKernel_induce_of_subgroupOf
    (A := ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))
    (H := hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))
    le_sup_right (hcPsi chief θ)
    (hcPsi_realizedH0supC_subgroupOf_subset_characterKernel chief θ)

set_option maxHeartbeats 1000000 in
-- raised heartbeat budget for the heavy elaboration below
/-- **`H ⊄ Ker ζ`** (`ζ ∈ 𝒳`): the irreducible `ζ = Ind_{HC}^{HU}(ψ)` is nontrivial on `H = hInHu`.
`ζ` lies over `ψ` (Frobenius: `⟨Ind ψ, ζ⟩ = ⟨ζ,ζ⟩ = 1`), so `H ⊆ Ker ζ` would descend
(`liesOver_mem_characterKernel`) to `H ⊆ Ker ψ` (`ψ|_H = 1`).  But `ψ|_H` is the inflation of `θ`
(`hcPsi_apply_inclusion`) and the descent hom `(mk' N) ∘ hInHuEquivH` is surjective, so `ψ|_H = 1`
forces `θ = 1`, contradicting `hθnt`.  The `xiSet` half of `ζ ∈ 𝒳(H₀C)`. -/
theorem hcZeta_mem_xiSet [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data)
    (θ : (↥data.H ⧸ chief.N) →* ℂˣ) (hθnt : θ ≠ 1)
    [Fintype ↥(huSub data)]
    [Finite ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))]
    [Invertible (Nat.card ↥(huSub data) : ℂ)]
    [Invertible (Nat.card ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
      (huSub data)) : ℂ)]
    [(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)).Normal]
    (hθ₀ : ClassFunction.inertia (ClassFunction.compHom (hInHuEquivH data).toMonoidHom
        (ClassFunction.compHom (QuotientGroup.mk' chief.N)
          (linearIrreducibleCharacter θ : ClassFunction (↥data.H ⧸ chief.N) ℂ)))
        = hInHu data ⊔ cInHu data chief) :
    (⟨ClassFunction.induce
        (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))
        (hcPsi chief θ), hcZeta_irreducible chief θ hθ₀⟩ :
        IrreducibleCharacter ↥(huSub data)) ∈ xiSet data := by
  have : Fintype ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
    (huSub data)) := Fintype.ofFinite _
  classical
  set ζ : IrreducibleCharacter ↥(huSub data) :=
    ⟨ClassFunction.induce
      (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))
      (hcPsi chief θ), hcZeta_irreducible chief θ hθ₀⟩ with hζdef
  -- `ζ` lies over `ψ`: Frobenius `⟨Ind ψ, ζ⟩ = ⟨ζ,ζ⟩ = 1 ≠ 0`.
  have hlo : OddOrder.RepresentationTheory.IrreducibleCharacter.LiesOver
      (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))
      ζ (hcPsi chief θ) := by
    rw [← OddOrder.RepresentationTheory.IrreducibleCharacter.inner_induce_ne_zero_iff_liesOver]
    have hcoe : (ζ : ClassFunction ↥(huSub data) ℂ) = ClassFunction.induce
        (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))
        (hcPsi chief θ) := by rw [hζdef]
    rw [← hcoe, OddOrder.RepresentationTheory.irreducibleCharacter_inner_eq_ite ζ ζ, if_pos rfl]
    exact one_ne_zero
  -- Assume `H ⊆ Ker ζ` for contradiction; show `θ = 1`.
  rw [xiSet, Set.mem_ofPred_eq]
  intro hsub
  apply hθnt
  have hfsurj : Function.Surjective
      ((QuotientGroup.mk' chief.N).comp (hInHuEquivH data).toMonoidHom) :=
    (QuotientGroup.mk'_surjective chief.N).comp (hInHuEquivH data).surjective
  refine MonoidHom.ext fun q => ?_
  obtain ⟨h, hhq⟩ := hfsurj q
  -- `(incl h : HU) ∈ H`, so it lies in `Ker ζ`, descending to `incl h ∈ Ker ψ`.
  have hgmem : ((Subgroup.inclusion
      (le_sup_left :
        hInHu data ≤ hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
          (huSub data)) h : ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
          (huSub data))) : ↥(huSub data)) ∈ hInHu data := by
    rw [Subgroup.coe_inclusion]; exact SetLike.coe_mem h
  have hψker := liesOver_mem_characterKernel hlo (hsub hgmem)
  have hψ1 : (hcPsi chief θ : ClassFunction
      ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)) ℂ)
      1 = 1 := by
    simp [hcPsi]
  rw [OddOrder.Peterfalvi.S03.mem_characterKernel, OddOrder.Peterfalvi.S03.characterDegree_def,
    hcPsi_apply_inclusion chief θ h, hψ1,
    ClassFunction.compHom_apply, ClassFunction.compHom_apply, MulEquiv.coe_toMonoidHom,
    linearIrreducibleCharacter_apply] at hψker
  -- `hψker : (θ ((mk' N) (hInHuEquivH h)) : ℂ) = 1`, and `(mk' N)(hInHuEquivH h) = q`.
  have hqeq : (QuotientGroup.mk' chief.N) ((hInHuEquivH data) h) = q := hhq
  rw [hqeq] at hψker
  change θ q = (1 : ℂˣ)
  refine Units.ext ?_
  rw [Units.val_one]
  exact hψker

set_option maxHeartbeats 1000000 in
-- raised heartbeat budget for the heavy elaboration below
/-- **`ζ ∈ 𝒳(H₀C)`**: combining the two halves `H ⊄ Ker ζ` (`hcZeta_mem_xiSet`) and `H₀C ⊆ Ker ζ`
(`hcZeta_H0supC_subset_ker`).  This is the source character of the (9.8.c) `𝒮(H₀C)`-member
`Ind_{HU}^M ζ` of degree `qu`. -/
theorem hcZeta_mem_xiOf [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data)
    (θ : (↥data.H ⧸ chief.N) →* ℂˣ) (hθnt : θ ≠ 1)
    [Fintype ↥(huSub data)]
    [Finite ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))]
    [Invertible (Nat.card ↥(huSub data) : ℂ)]
    [Invertible (Nat.card ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
      (huSub data)) : ℂ)]
    [(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)).Normal]
    (hθ₀ : ClassFunction.inertia (ClassFunction.compHom (hInHuEquivH data).toMonoidHom
        (ClassFunction.compHom (QuotientGroup.mk' chief.N)
          (linearIrreducibleCharacter θ : ClassFunction (↥data.H ⧸ chief.N) ℂ)))
        = hInHu data ⊔ cInHu data chief) :
    (⟨ClassFunction.induce
        (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))
        (hcPsi chief θ), hcZeta_irreducible chief θ hθ₀⟩ :
        IrreducibleCharacter ↥(huSub data)) ∈ xiOf data (chief.H0 ⊔ cSub data chief) := by
  have : Fintype ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
    (huSub data)) := Fintype.ofFinite _
  rw [mem_xiOf]
  exact ⟨hcZeta_mem_xiSet chief θ hθnt hθ₀, hcZeta_H0supC_subset_ker chief θ⟩

/-- A nontrivial linear seed has a nontrivial character coercion (the seed form consumed by the
case-(b) inertia lift `inertia_eq_hcInHu`). -/
theorem linearIrreducibleCharacter_coe_ne_trivial_of_ne_one {K : Type*} [Group K] [Finite K]
    {θ : K →* ℂˣ} (hθ : θ ≠ 1) :
    (linearIrreducibleCharacter θ : ClassFunction K ℂ) ≠ trivialClassFunction K := by
  intro h0
  apply hθ
  rw [← linearIrreducibleCharacter_eq_trivial_iff]
  exact IrreducibleCharacter.ext
    (h0.trans (IrreducibleCharacter.coe_trivialIrreducibleCharacter).symm)

/-- **A reducible `M`-induction has an `M`-invariant source** (inertia dichotomy at the prime
index `q = [M:HU]`): if `Ind_{HU}^M ζ` is *not* irreducible, then every `M`-conjugate of
`ζ ∈ Irr(HU)` equals `ζ`.  The inertia `I_M(ζ)` lies between `HU` and `M`
(`subgroup_le_inertia`); `[M:HU] = q` prime (`huSub_index_eq_q`) leaves `I = HU` or `I = M`
(`relIndex_mul_index`), and `I = HU` would make the induction irreducible
(`isIrreducibleCharacter_induce_of_inertia_eq`).  The injectivity input of the (9.9.c)
`|Xζ| = p−1` count. -/
theorem conjBy_eq_self_of_not_isIrreducibleCharacter_induceHU [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M}
    (ζ : IrreducibleCharacter ↥(huSub data))
    (hred : ¬ IsIrreducibleCharacter (induceHU data (ζ : ClassFunction ↥(huSub data) ℂ)))
    (w : ↥M) : IrreducibleCharacter.conjBy w ζ = ζ := by
  let : Fintype ↥M := Fintype.ofFinite _
  let : Fintype ↥(huSub data) := Fintype.ofFinite _
  let : Invertible (Nat.card ↥(huSub data) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  let : Invertible (Nat.card ↥M : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have hle : huSub data ≤ ClassFunction.inertia (ζ : ClassFunction ↥(huSub data) ℂ) :=
    ClassFunction.subgroup_le_inertia _
  have hq : (data.q).Prime := data.nontrivial.2.1
  have hmul := Subgroup.relIndex_mul_index (H := huSub data)
    (K := ClassFunction.inertia (ζ : ClassFunction ↥(huSub data) ℂ)) hle
  rw [huSub_index_eq_q] at hmul
  have hdvd : (ClassFunction.inertia (ζ : ClassFunction ↥(huSub data) ℂ)).index ∣ data.q :=
    ⟨_, by rw [mul_comm]; exact hmul.symm⟩
  have htop : ClassFunction.inertia (ζ : ClassFunction ↥(huSub data) ℂ) = ⊤ := by
    rcases (Nat.Prime.eq_one_or_self_of_dvd hq _ hdvd) with h1 | hqq
    · exact Subgroup.index_eq_one.mp h1
    · -- `I.index = q` forces `relIndex = 1`, i.e. `I ≤ HU`, so `I = HU` — induction irreducible.
      exfalso
      rw [hqq] at hmul
      have hrel1 : (huSub data).relIndex
          (ClassFunction.inertia (ζ : ClassFunction ↥(huSub data) ℂ)) = 1 :=
        Nat.eq_of_mul_eq_mul_right hq.pos (hmul.trans (one_mul data.q).symm)
      have hIle : ClassFunction.inertia (ζ : ClassFunction ↥(huSub data) ℂ) ≤ huSub data :=
        Subgroup.relIndex_eq_one.mp hrel1
      exact hred (OddOrder.RepresentationTheory.isIrreducibleCharacter_induce_of_inertia_eq ζ
        (le_antisymm hIle hle))
  have hw : w ∈ ClassFunction.inertia (ζ : ClassFunction ↥(huSub data) ℂ) :=
    htop ▸ Subgroup.mem_top w
  rw [ClassFunction.mem_inertia] at hw
  exact IrreducibleCharacter.ext (by rw [IrreducibleCharacter.coe_conjBy]; exact hw)

set_option maxHeartbeats 1600000 in
-- raised heartbeat budget for the heavy elaboration below
open scoped Classical in
/-- **Peterfalvi (9.9.c), the `u`-formula half**: in Clifford case (b), if `𝒮(H₀C')` contains
no irreducible character then `u = (p^q−1)/(p−1)`.

With `C = ⊥` (`caseB_no_irreducible_forces_C_bot`) all the joins collapse to `H₀`, so every
member of `𝒮(H₀)` is reducible.  Count `𝒳(H₀)` two ways: the case-(b) `oXtheta`
(`caseB_oXtheta_count`) gives `u·|Xζ| = p^q−1` for the set `Xζ` of `hcPsi`-inductions, which
exhausts `𝒳(H₀)` (`caseB_xiOf_H0C_eq_induce_hcPsi`); and `Ind_{HU}^M` maps `Xζ` *bijectively*
onto the `p−1` reducible members of `𝒮(H₀)` (`reducible_count_sOf_H0`) — injectivity because a
reducible induction has an `M`-invariant source (`conjBy_eq_self_of_…`, prime-index inertia
dichotomy), so `Ind ζ₁ = Ind ζ₂ ⟹ ζ₂ = ζ₁^w = ζ₁`.  Hence `u·(p−1) = p^q−1`. -/
theorem caseB_no_irreducible_u_formula [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    (chars : Section11CharacterData data chief) (caseB : CliffordCaseBData chars)
    (hno : ¬ ∃ χ ∈ chars.SOf (chief.H0 ⊔ chars.Cprime), IsIrreducibleCharacter χ) :
    chars.u = (chief.p ^ data.q - 1) / (chief.p - 1) := by
  classical
  have hCbot : cSub data chief = ⊥ := caseB_no_irreducible_forces_C_bot hG chars caseB hno
  have hCpbot : cprimeSub data chief = ⊥ :=
    le_bot_iff.mp (hCbot ▸ cprimeSub_le_C data chief)
  have hcollapse : chief.H0 ⊔ cSub data chief = chief.H0 := by rw [hCbot, sup_bot_eq]
  let : Fintype ↥M := Fintype.ofFinite _
  let : Fintype ↥(huSub data) := Fintype.ofFinite _
  let : Fintype ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
    (huSub data)) := Fintype.ofFinite _
  let : Fintype ((↥data.H ⧸ chief.N) →* ℂˣ) := Fintype.ofFinite _
  let : Invertible (Nat.card ↥M : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  let : Invertible (Nat.card ↥(huSub data) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  let : Invertible (Nat.card ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf
    M).subgroupOf (huSub data)) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have : (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
    (huSub data)).Normal := hcInHu_realized_normal chief
  -- `hno` in `𝒮(H₀)`-form (`C' = ⊥` collapses the join)
  have hno' : ∀ φ ∈ sOf data chief.H0, ¬ IsIrreducibleCharacter φ := by
    intro φ hφ hirr
    apply hno
    refine ⟨φ, ?_, hirr⟩
    change φ ∈ sOf data (chief.H0 ⊔ cprimeSub data chief)
    rw [hCpbot, sup_bot_eq]
    exact hφ
  -- the case-(b) `oXtheta` count
  have hcount := caseB_oXtheta_count (chars := chars) caseB
  set NF := Finset.univ.filter fun θ : (↥data.H ⧸ chief.N) →* ℂˣ => θ ≠ 1 with hNF
  set Xz := NF.image fun θ =>
    ClassFunction.induce (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
      (huSub data)) (hcPsi chief θ).toClassFunction with hXz
  -- every `Xζ`-member is (the coercion of) a `𝒳(H₀)`-irreducible
  have hXmem : ∀ φz ∈ Xz, ∃ ζ : IrreducibleCharacter ↥(huSub data),
      (ζ : ClassFunction ↥(huSub data) ℂ) = φz ∧ ζ ∈ xiOf data chief.H0 := by
    intro φz hφz
    obtain ⟨θ, hθNF, rfl⟩ := Finset.mem_image.mp hφz
    have hθne : θ ≠ 1 := (Finset.mem_filter.mp hθNF).2
    have hθ₀ := inertia_eq_hcInHu data chief caseB.actsIrreducibly
      (linearIrreducibleCharacter_coe_ne_trivial_of_ne_one hθne)
    refine ⟨⟨_, hcZeta_irreducible chief θ hθ₀⟩, rfl, ?_⟩
    have hxi := hcZeta_mem_xiOf chief θ hθne hθ₀
    exact (congrArg (xiOf data) hcollapse) ▸ hxi
  -- their `M`-inductions are reducible `𝒮(H₀)`-members
  have hXred : ∀ φz ∈ Xz, induceHU data φz ∈ sOf data chief.H0
      ∧ ¬ IsIrreducibleCharacter (induceHU data φz) := by
    intro φz hφz
    obtain ⟨ζ, hζcoe, hζxi⟩ := hXmem φz hφz
    have hmem : induceHU data φz ∈ sOf data chief.H0 := by
      rw [← hζcoe]
      exact mem_sOf.mpr ⟨ζ, hζxi, rfl⟩
    exact ⟨hmem, hno' _ hmem⟩
  -- `Ind_{HU}^M` is injective on `Xζ` (reducible inductions have `M`-invariant sources)
  have hinj : Set.InjOn (fun φz => induceHU data φz)
      (Xz : Set (ClassFunction ↥(huSub data) ℂ)) := by
    intro φz₁ h1 φz₂ h2 heq
    rw [Finset.mem_coe] at h1 h2
    obtain ⟨ζ₁, hζ₁coe, -⟩ := hXmem φz₁ h1
    obtain ⟨ζ₂, hζ₂coe, -⟩ := hXmem φz₂ h2
    have hred1 : ¬ IsIrreducibleCharacter (induceHU data (ζ₁ : ClassFunction _ ℂ)) := by
      rw [hζ₁coe]
      exact (hXred φz₁ h1).2
    have heq' : induceHU data (ζ₁ : ClassFunction _ ℂ)
        = induceHU data (ζ₂ : ClassFunction _ ℂ) := by
      rw [hζ₁coe, hζ₂coe]
      exact heq
    obtain ⟨w, hw⟩ := (OddOrder.RepresentationTheory.induce_eq_induce_iff_conj
      (G := ↥M) (H := huSub data) ζ₁ ζ₂).mp heq'
    have hfix := conjBy_eq_self_of_not_isIrreducibleCharacter_induceHU ζ₁ hred1 w
    rw [← hζ₁coe, ← hζ₂coe, ← hw, hfix]
  -- the image is exactly the reducible part of `𝒮(H₀)` (exhaustion for `⊇`)
  have himg : (fun φz => induceHU data φz) '' (Xz : Set (ClassFunction ↥(huSub data) ℂ))
      = {φ ∈ sOf data chief.H0 | ¬ IsIrreducibleCharacter φ} := by
    ext φ
    constructor
    · rintro ⟨φz, hφz, rfl⟩
      rw [Finset.mem_coe] at hφz
      exact ⟨(hXred φz hφz).1, (hXred φz hφz).2⟩
    · rintro ⟨hφS, hφred⟩
      obtain ⟨ζ', hζ'xi, rfl⟩ := mem_sOf.mp hφS
      have hζ'xiC : ζ' ∈ xiOf data (chief.H0 ⊔ cSub data chief) :=
        (congrArg (xiOf data) hcollapse).symm ▸ hζ'xi
      obtain ⟨θbar, hθne, hζ'eq⟩ := caseB_xiOf_H0C_eq_induce_hcPsi caseB hζ'xiC
      refine ⟨(ζ' : ClassFunction ↥(huSub data) ℂ), ?_, rfl⟩
      rw [Finset.mem_coe, hζ'eq]
      exact Finset.mem_image.mpr ⟨θbar,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hθne⟩, rfl⟩
  -- `|Xζ| = p − 1`
  have hXcard : Xz.card = chief.p - 1 :=
    calc Xz.card = (Xz : Set (ClassFunction ↥(huSub data) ℂ)).ncard :=
          (Set.ncard_coe_finset Xz).symm
      _ = ((fun φz => induceHU data φz) '' (Xz : Set (ClassFunction ↥(huSub data) ℂ))).ncard :=
          (Set.InjOn.ncard_image hinj).symm
      _ = chief.p - 1 := by rw [himg]; exact reducible_count_sOf_H0 hG chief
  -- assemble: `u·(p−1) = p^q − 1` (`set` already folded `NF`/`Xz` into `hcount`)
  rw [hXcard] at hcount
  have hp1 : 0 < chief.p - 1 := Nat.sub_pos_of_lt chief.p_prime.one_lt
  rw [← hcount]
  exact (Nat.mul_div_cancel _ hp1).symm

/-- **Degree of the (9.8.c) `𝒮`-member**: `(Ind_{HU}^M ζ)(1) = q·u = qu`.  Combines the `HU→M`
index `[M:HU] = q` (`induceHU_apply_one_eq_q_mul`) with `ζ(1) = u` (`hcZeta_apply_one`). -/
theorem hcZeta_induceHU_apply_one [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    (chars : Section11CharacterData data chief)
    (θ : (↥data.H ⧸ chief.N) →* ℂˣ)
    [Fintype ↥(huSub data)]
    [Finite ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))]
    [Invertible (Nat.card ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
      (huSub data)) : ℂ)] :
    induceHU data (ClassFunction.induce
        (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))
        (hcPsi chief θ) : ClassFunction ↥(huSub data) ℂ) (1 : ↥M)
      = ((data.q * chars.u : ℕ) : ℂ) := by
  have : Fintype ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
    (huSub data)) := Fintype.ofFinite _
  rw [induceHU_apply_one_eq_q_mul, hcZeta_apply_one chars θ, Nat.cast_mul]

/-- **`Ind_{HU}^M ζ ∈ 𝒮(H₀C)`**: the (9.8.c) degree-`qu` character is a member of `𝒮(H₀C)`,
witnessed
by its source `ζ ∈ 𝒳(H₀C)` (`hcZeta_mem_xiOf`). -/
theorem hcZeta_induceHU_mem_sOf [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    (_chars : Section11CharacterData data chief)
    (θ : (↥data.H ⧸ chief.N) →* ℂˣ) (hθnt : θ ≠ 1)
    [Fintype ↥(huSub data)]
    [Finite ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))]
    [Invertible (Nat.card ↥(huSub data) : ℂ)]
    [Invertible (Nat.card ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
      (huSub data)) : ℂ)]
    [(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)).Normal]
    (hθ₀ : ClassFunction.inertia (ClassFunction.compHom (hInHuEquivH data).toMonoidHom
        (ClassFunction.compHom (QuotientGroup.mk' chief.N)
          (linearIrreducibleCharacter θ : ClassFunction (↥data.H ⧸ chief.N) ℂ)))
        = hInHu data ⊔ cInHu data chief) :
    induceHU data (ClassFunction.induce
        (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))
        (hcPsi chief θ) : ClassFunction ↥(huSub data) ℂ)
      ∈ sOf data (chief.H0 ⊔ cSub data chief) := by
  have : Fintype ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
    (huSub data)) := Fintype.ofFinite _
  rw [mem_sOf]
  exact ⟨⟨ClassFunction.induce
      (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))
      (hcPsi chief θ), hcZeta_irreducible chief θ hθ₀⟩,
    hcZeta_mem_xiOf chief θ hθnt hθ₀, rfl⟩

/-- **`H ◁ M`** realized: `(data.H.subgroupOf M).Normal`.  Extracted as in `hInHu_normal`. -/
theorem hSubgroupOfM_normal {M : Subgroup G} (data : TypesIIIIIIVSetup M) :
    (data.H.subgroupOf M).Normal := by
  rw [show data.H = maxNilpotentNormalHall M from data.typeP.H_eq]
  exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_subgroupOf_normal M

/-- **The `m`-conjugation automorphism of `hInHu`** (`m ∈ M`).  Well-defined since `H ◁ M`
(`hSubgroupOfM_normal`), so `m` normalizes `hInHu`.  Realizing the `M`-conjugation of an
`hInHu`-character as `compHom` by this hom keeps the (9.8.c) free-`W₁`-orbit argument at the `hInHu`
level (no subgroup-realization transport). -/
noncomputable def hInHuConj {M : Subgroup G} (data : TypesIIIIIIVSetup M) (m : ↥M) :
    ↥(hInHu data) →* ↥(hInHu data) where
  toFun h := ⟨ClassFunction.conjByMulEquiv (G := ↥M) (H := huSub data) m (h : ↥(huSub data)), by
    refine Subgroup.mem_subgroupOf.mpr ?_
    rw [ClassFunction.conjByMulEquiv_apply]
    exact (hSubgroupOfM_normal data).conj_mem _ (Subgroup.mem_subgroupOf.mp h.2) m⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' h₁ h₂ := by
    apply Subtype.ext
    simp [map_mul]

@[simp] theorem hInHuConj_coe {M : Subgroup G} (data : TypesIIIIIIVSetup M) (m : ↥M)
    (h : ↥(hInHu data)) :
    (((hInHuConj data m h : ↥(hInHu data)) : ↥(huSub data)) : ↥M)
      = m * ((h : ↥(huSub data)) : ↥M) * m⁻¹ :=
  rfl

/-- **Core identity for L1**: restricting the `M`-conjugate `conjBy m ζ` of an `HU`-character `ζ`
to `H = hInHu` equals `compHom`-by-`φ_m` of `Res ζ`.  Both evaluate at `h ∈ hInHu` to
`ζ(m·h·m⁻¹)`.  This converts the `M`-conjugation (needed for `I_M(ζ)`) into a `compHom`-by-aut
at the `hInHu` level, the hinge of the (9.8.c) free-`W₁`-orbit argument. -/
theorem hInHuConj_restrict_conjBy {M : Subgroup G} (data : TypesIIIIIIVSetup M) (m : ↥M)
    (ζ : ClassFunction ↥(huSub data) ℂ) :
    ClassFunction.restrict (hInHu data) (ClassFunction.conjBy m ζ)
      = ClassFunction.compHom (hInHuConj data m) (ClassFunction.restrict (hInHu data) ζ) := by
  ext h
  rfl

/-- **Inner sum is invariant under `compHom` by a bijective endomorphism** (reindexing the sum by
the induced permutation).  Mirrors `innerSum_conjBy_conjBy`. -/
theorem innerSum_compHom_of_bijective {H : Type*} [Group H] [Fintype H]
    (e : H →* H) (he : Function.Bijective e) (a b : ClassFunction H ℂ) :
    ClassFunction.innerSum (ClassFunction.compHom e a) (ClassFunction.compHom e b)
      = ClassFunction.innerSum a b := by
  simpa [ClassFunction.innerSum, ClassFunction.compHom_apply] using
    Fintype.sum_equiv (Equiv.ofBijective e he)
      (fun h => a (e h) * star (b (e h))) (fun h => a h * star (b h)) (fun _ => rfl)

/-- **Inner product is invariant under `compHom` by a bijective endomorphism.** -/
theorem inner_compHom_of_bijective {H : Type*} [Group H] [Fintype H]
    [Invertible (Nat.card H : ℂ)] (e : H →* H) (he : Function.Bijective e)
    (a b : ClassFunction H ℂ) :
    ClassFunction.inner (ClassFunction.compHom e a) (ClassFunction.compHom e b)
      = ClassFunction.inner a b := by
  simp [ClassFunction.inner, innerSum_compHom_of_bijective e he]

/-- **`φ_m` is bijective** (inverse `φ_{m⁻¹}`), so `compHom φ_m` preserves inner products and
irreducibility. -/
theorem hInHuConj_bijective {M : Subgroup G} (data : TypesIIIIIIVSetup M) (m : ↥M) :
    Function.Bijective (hInHuConj data m) := by
  refine Function.bijective_iff_has_inverse.mpr ⟨hInHuConj data m⁻¹, ?_, ?_⟩ <;>
  · intro h
    apply Subtype.ext
    apply Subtype.ext
    simp only [hInHuConj_coe]
    group

/-- **L2 result: `LiesOver`-equivariance under an `M`-fixing `m`.**  If `ζ` is fixed by `conjBy m`
and lies over `θ₀`, then `ζ` also lies over the `φ_m`-conjugate `φθ₀ = compHom φ_m θ₀`.  Proof: the
restriction multiplicity `⟨Res ζ, φθ₀⟩ = ⟨Res ζ, compHom φ_m θ₀⟩ = ⟨compHom φ_m (Res ζ), compHom φ_m
θ₀⟩` (by `Res ζ = compHom φ_m (Res ζ)`, from `conjBy m ζ = ζ` and the L1 identity) `= ⟨Res ζ, θ₀⟩ ≠
0`
(`inner_compHom_of_bijective`). -/
theorem hcZeta_liesOver_compHom_of_fixed {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (m : ↥M)
    [Fintype ↥(hInHu data)] [Invertible (Nat.card ↥(hInHu data) : ℂ)]
    (ζ : IrreducibleCharacter ↥(huSub data)) (θ₀ φθ₀ : IrreducibleCharacter ↥(hInHu data))
    (hlo : OddOrder.RepresentationTheory.IrreducibleCharacter.LiesOver (hInHu data) ζ θ₀)
    (hfix : ClassFunction.conjBy m (ζ : ClassFunction ↥(huSub data) ℂ)
      = (ζ : ClassFunction ↥(huSub data) ℂ))
    (hφθ₀ : (φθ₀ : ClassFunction ↥(hInHu data) ℂ)
      = ClassFunction.compHom (hInHuConj data m) (θ₀ : ClassFunction ↥(hInHu data) ℂ)) :
    OddOrder.RepresentationTheory.IrreducibleCharacter.LiesOver (hInHu data) ζ φθ₀ := by
  rw [OddOrder.RepresentationTheory.IrreducibleCharacter.liesOver_iff,
    ClassFunction.restrictionMultiplicity_def, hφθ₀,
    show ClassFunction.restrict (hInHu data) (ζ : ClassFunction ↥(huSub data) ℂ)
        = ClassFunction.compHom (hInHuConj data m)
            (ClassFunction.restrict (hInHu data) (ζ : ClassFunction ↥(huSub data) ℂ)) from by
        rw [← hInHuConj_restrict_conjBy, hfix],
    inner_compHom_of_bijective _ (hInHuConj_bijective data m)]
  have h := hlo
  rwa [OddOrder.RepresentationTheory.IrreducibleCharacter.liesOver_iff,
    ClassFunction.restrictionMultiplicity_def] at h

/-- **L3: SingleOrbit reduction.**  If `ζ` is fixed by `conjBy m` and lies over `θ₀`, then `θ₀` and
its `φ_m`-conjugate are `HU`-conjugate: there is `g ∈ HU` with `conjBy g θ₀ = compHom φ_m θ₀`.  By
the L2 equivariance `ζ` lies over both `θ₀` and `φ_m·θ₀`, and Clifford's single-orbit theorem
(`restrictionConstituentsSingleOrbit_of_isIrreducible`) puts both constituents in one `HU`-orbit
(`exists_conj`).  The free-`W₁`-orbit hypothesis (L4) will deny exactly this. -/
theorem hcZeta_exists_conj_of_fixed {M : Subgroup G} {data : TypesIIIIIIVSetup M} (m : ↥M)
    [Fintype ↥(hInHu data)] [Invertible (Nat.card ↥(hInHu data) : ℂ)]
    (ζ : IrreducibleCharacter ↥(huSub data)) (θ₀ : IrreducibleCharacter ↥(hInHu data))
    (hlo : OddOrder.RepresentationTheory.IrreducibleCharacter.LiesOver (hInHu data) ζ θ₀)
    (hfix : ClassFunction.conjBy m (ζ : ClassFunction ↥(huSub data) ℂ)
      = (ζ : ClassFunction ↥(huSub data) ℂ)) :
    ∃ g : ↥(huSub data), ClassFunction.conjBy g (θ₀ : ClassFunction ↥(hInHu data) ℂ)
      = ClassFunction.compHom (hInHuConj data m) (θ₀ : ClassFunction ↥(hInHu data) ℂ) := by
  have hirr : IsIrreducibleCharacter
      (ClassFunction.compHom (hInHuConj data m) (θ₀ : ClassFunction ↥(hInHu data) ℂ)) :=
    θ₀.isIrreducible.compHom_of_surjective (hInHuConj_bijective data m).surjective
  set φθ₀ : IrreducibleCharacter ↥(hInHu data) :=
    ⟨ClassFunction.compHom (hInHuConj data m) (θ₀ : ClassFunction ↥(hInHu data) ℂ), hirr⟩
    with hφdef
  have hη := hcZeta_liesOver_compHom_of_fixed m ζ θ₀ φθ₀ hlo hfix rfl
  obtain ⟨g, hg⟩ :=
   OddOrder.RepresentationTheory.IrreducibleCharacter.RestrictionConstituentsSingleOrbit.exists_conj
      (OddOrder.RepresentationTheory.restrictionConstituentsSingleOrbit_of_isIrreducible ζ) hlo hη
  refine ⟨g, ?_⟩
  have hc := congrArg (fun x : IrreducibleCharacter ↥(hInHu data) =>
    (x : ClassFunction ↥(hInHu data) ℂ)) hg
  simpa [OddOrder.RepresentationTheory.IrreducibleCharacter.coe_conjBy, hφdef] using hc

/-- **`φ_m`-analog of the inflation-conjugation commute.**  For `m ∈ M` realized by `b ∈ U W₁`
(`↑m = ↑b`), `compHom φ_m` of an inflation equals the inflation of `typeP_conjAction b`.  Mirrors
`conjBy_compHom_hInHuEquivH` (both reduce to `m·h·m⁻¹ = b·h·b⁻¹` in `G`), turning the
`M`-conjugation
`compHom φ_m θ₀` of the chief-factor `θ₀` into the abstract `b`-action on `H`. -/
theorem compHom_hInHuConj_hInHuEquivH {M : Subgroup G} (data : TypesIIIIIIVSetup M)
    (b : ↥(data.typeP.U ⊔ data.typeP.W1)) (m : ↥M) (hmb : ((m : G)) = (b : G))
    (θ : ClassFunction ↥data.H ℂ) :
    ClassFunction.compHom (hInHuConj data m)
        (ClassFunction.compHom (hInHuEquivH data).toMonoidHom θ)
      = ClassFunction.compHom (hInHuEquivH data).toMonoidHom
          (ClassFunction.compHom (typeP_conjAction data.typeP b).toMonoidHom θ) := by
  ext h
  rw [ClassFunction.compHom_apply, ClassFunction.compHom_apply, ClassFunction.compHom_apply,
    ClassFunction.compHom_apply]
  refine congrArg _ (Subtype.ext ?_)
  simp only [MulEquiv.coe_toMonoidHom, hInHuEquivH_coe, typeP_conjAction_apply, hInHuConj_coe,
    Subgroup.coe_mul, Subgroup.coe_inv]
  rw [hmb]

/-- **L4 connection core**: the free-orbit equality `conjBy g θ₀ = compHom φ_m θ₀` (for `θ₀` the
inflation of `θ̄`, `↑g = ↑a`, `↑m = ↑b`) is equivalent to the quotient-level equality
`quotientMulAutHom a θ̄ = quotientMulAutHom b θ̄`.  Chains the two inflation-conjugation commutes
(`conjBy_compHom_hInHuEquivH`, `compHom_hInHuConj_hInHuEquivH`), the descent
(`compHom_typeP_conjAction_inflation`, `rfl`), and double inflation injectivity
(`compHom_injective_of_surjective` for `hInHuEquivH` and `mk' N`).  This turns `hfree` into the pure
free-`W₁`-orbit statement `θ̄^{w₀} ∉ U-orbit`. -/
theorem conjBy_eq_compHom_iff_quotient [Finite G] {M : Subgroup G} {data : TypesIIIIIIVSetup M}
    {chief : ChiefFactorData data} (a b : ↥(data.typeP.U ⊔ data.typeP.W1))
    (g : ↥(huSub data)) (m : ↥M) (hag : ((g : ↥M) : G) = (a : G)) (hbm : ((m : G)) = (b : G))
    (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ) :
    ClassFunction.conjBy g (ClassFunction.compHom (hInHuEquivH data).toMonoidHom
        (ClassFunction.compHom (QuotientGroup.mk' chief.N) θbar))
      = ClassFunction.compHom (hInHuConj data m)
          (ClassFunction.compHom (hInHuEquivH data).toMonoidHom
            (ClassFunction.compHom (QuotientGroup.mk' chief.N) θbar))
    ↔ ClassFunction.compHom (quotientMulAutHom chief.N_aInvariant a).toMonoidHom θbar
      = ClassFunction.compHom (quotientMulAutHom chief.N_aInvariant b).toMonoidHom θbar := by
  rw [conjBy_compHom_hInHuEquivH data a g hag, compHom_hInHuConj_hInHuEquivH data b m hbm,
    compHom_typeP_conjAction_inflation, compHom_typeP_conjAction_inflation]
  constructor
  · intro h
    exact ClassFunction.compHom_injective_of_surjective (QuotientGroup.mk'_surjective chief.N)
      (ClassFunction.compHom_injective_of_surjective (hInHuEquivH data).surjective h)
  · intro h
    rw [h]

/-- **step 2 core: `M`-fixedness gives a `U`-conjugation** (Peterfalvi (9.8.c) surjectivity route).
If `χ` is fixed by `conjBy m` (`m ∈ M`) and lies over `θ₀`, then there is a `U`-part element
`u ∈ uInHu` with `conjBy u θ₀ = compHom φ_m θ₀`.  The single-orbit `g ∈ HU` of L3
(`hcZeta_exists_conj_of_fixed`) decomposes as `g = h·u` (`hInHu_sup_uInHu_eq_top`, `HU = H·U`); the
`H`-part `h` fixes `θ₀` (`h ∈ hInHu ≤ inertia θ₀`, `subgroup_le_inertia`), so
`conjBy g θ₀ = conjBy u (conjBy h θ₀) = conjBy u θ₀` (`conjBy_mul`).  Realizing the `M`-fixed
factor-permutation by a `U`-element (in `U ⊔ W₁`) is what lets `conjBy_eq_compHom_iff_quotient` turn
it into the `H̄`-level `q(u)θbar = q(w)θbar` (`θbar∘q(w)` in the `U`-orbit of `θbar`). -/
theorem exists_uInHu_conjBy_eq_of_fixed [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (m : ↥M)
    [Fintype ↥(hInHu data)] [Invertible (Nat.card ↥(hInHu data) : ℂ)]
    (ζ : IrreducibleCharacter ↥(huSub data)) (θ₀ : IrreducibleCharacter ↥(hInHu data))
    (hlo : OddOrder.RepresentationTheory.IrreducibleCharacter.LiesOver (hInHu data) ζ θ₀)
    (hfix : ClassFunction.conjBy m (ζ : ClassFunction ↥(huSub data) ℂ)
      = (ζ : ClassFunction ↥(huSub data) ℂ)) :
    ∃ u : ↥(huSub data), u ∈ uInHu data ∧
      ClassFunction.conjBy u (θ₀ : ClassFunction ↥(hInHu data) ℂ)
        = ClassFunction.compHom (hInHuConj data m) (θ₀ : ClassFunction ↥(hInHu data) ℂ) := by
  have := hInHu_normal data
  obtain ⟨g, hg⟩ := hcZeta_exists_conj_of_fixed m ζ θ₀ hlo hfix
  -- `g = h · u` with `h ∈ hInHu`, `u ∈ uInHu` (`HU = H·U`, `hInHu ◁ HU`).
  have hgtop : g ∈ hInHu data ⊔ uInHu data :=
    hInHu_sup_uInHu_eq_top data ▸ Subgroup.mem_top g
  rw [← SetLike.mem_coe, Subgroup.normal_mul] at hgtop
  obtain ⟨h, hh, u, hu, rfl⟩ := hgtop
  refine ⟨u, hu, ?_⟩
  -- `conjBy (h·u) θ₀ = conjBy u (conjBy h θ₀) = conjBy u θ₀` since `h` fixes `θ₀`.
  have hhfix : ClassFunction.conjBy (h : ↥(huSub data)) (θ₀ : ClassFunction ↥(hInHu data) ℂ)
      = (θ₀ : ClassFunction ↥(hInHu data) ℂ) :=
    ClassFunction.mem_inertia.mp
      (ClassFunction.subgroup_le_inertia (θ₀ : ClassFunction ↥(hInHu data) ℂ) hh)
  rw [ClassFunction.conjBy_mul, hhfix] at hg
  exact hg

/-- **step 2: `M`-fixedness gives an `H̄`-level orbit equality** (Peterfalvi (9.8.c) surjectivity).
If `χ` is fixed by `conjBy m` (`↑m = ↑b`, `b ∈ U ⊔ W₁`) and lies over the inflation `θ₀` of the seed
`θbar : H̄ →* ℂˣ`, then there is a `U`-element `a` with `θbar ∘ q(a) = θbar ∘ q(b)`
(`q = quotientMulAutHom`).  Chains the `U`-conjugation `exists_uInHu_conjBy_eq_of_fixed`, the L4
bridge `conjBy_eq_compHom_iff_quotient` (turning it into `q(a)θbar = q(b)θbar` at the `H̄`-level),
and
`linearIrreducibleCharacter_injective` (stripping the linear wrapper).  Thus the `W₁`-twist
`θbar ∘ q(b)` lies in the `U`-orbit `{θbar ∘ q(a) : a ∈ U}` of `θbar` — the input to the
factor-permutation invariance of the nontrivial-`Hpart` set. -/
theorem exists_uPart_theta_comp_quotient_eq_of_fixed [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    (m : ↥M) (b : ↥(data.typeP.U ⊔ data.typeP.W1)) (hbm : ((m : G)) = (b : G))
    (θbar : (↥data.H ⧸ chief.N) →* ℂˣ)
    [Fintype ↥(hInHu data)] [Invertible (Nat.card ↥(hInHu data) : ℂ)]
    (ζ : IrreducibleCharacter ↥(huSub data))
    (hlo : OddOrder.RepresentationTheory.IrreducibleCharacter.LiesOver (hInHu data) ζ
      (linearIrreducibleCharacter (θbar.comp ((QuotientGroup.mk' chief.N).comp
        (hInHuEquivH data).toMonoidHom))))
    (hfix : ClassFunction.conjBy m (ζ : ClassFunction ↥(huSub data) ℂ)
      = (ζ : ClassFunction ↥(huSub data) ℂ)) :
    ∃ a : ↥(data.typeP.U ⊔ data.typeP.W1), ((a : G)) ∈ data.typeP.U ∧
      θbar.comp (quotientMulAutHom chief.N_aInvariant a).toMonoidHom
        = θbar.comp (quotientMulAutHom chief.N_aInvariant b).toMonoidHom := by
  obtain ⟨u, hu, hconj⟩ := exists_uInHu_conjBy_eq_of_fixed m ζ
    (linearIrreducibleCharacter (θbar.comp ((QuotientGroup.mk' chief.N).comp
      (hInHuEquivH data).toMonoidHom))) hlo hfix
  have huU : ((u : ↥M) : G) ∈ data.typeP.U :=
    Subgroup.mem_subgroupOf.mp (Subgroup.mem_subgroupOf.mp hu)
  refine ⟨⟨((u : ↥M) : G), Subgroup.mem_sup_left huU⟩, huU, ?_⟩
  -- form alignment: the step-1 `θ₀` equals the `conjBy_eq_compHom_iff_quotient` inflation form.
  have hinfl : (linearIrreducibleCharacter (θbar.comp ((QuotientGroup.mk' chief.N).comp
        (hInHuEquivH data).toMonoidHom)) : ClassFunction ↥(hInHu data) ℂ)
      = ClassFunction.compHom (hInHuEquivH data).toMonoidHom
          (ClassFunction.compHom (QuotientGroup.mk' chief.N)
            (linearIrreducibleCharacter θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ)) := by
    ext x
    simp only [ClassFunction.compHom_apply, linearIrreducibleCharacter_apply,
      MulEquiv.coe_toMonoidHom, MonoidHom.comp_apply]
  -- L4 bridge with `θbar_CF = linearIrr θbar`.
  have hbridge := (conjBy_eq_compHom_iff_quotient
    (⟨((u : ↥M) : G), Subgroup.mem_sup_left huU⟩ : ↥(data.typeP.U ⊔ data.typeP.W1)) b u m rfl hbm
    (linearIrreducibleCharacter θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ)).mp (by
      rw [← hinfl]; exact hconj)
  rw [ClassFunction.compHom_linearIrreducibleCharacter,
    ClassFunction.compHom_linearIrreducibleCharacter] at hbridge
  exact linearIrreducibleCharacter_injective (IrreducibleCharacter.ext hbridge)

/-- **`Ū`-invariance of nontriviality on a `U`-invariant `K`, `quotientMulAutHom` form**: for a
`U`-invariant `K` and a `U`-part element `a` (`↑a ∈ U`), `θ ∘ q(a)` is trivial on `K` iff `θ` is
(`q = quotientMulAutHom`).  The form-alignment (`uActionHom ⟨a,·⟩ = q(a)`) version of
`comp_uActionHom_comp_subtype_eq_one_iff_of_aInvariant` for the general-`K` uses in the (9.8.c)
surjectivity regularity argument (`K = q(w) • S₀` and `K = S₀`). -/
theorem comp_quotient_uPart_comp_subtype_eq_one_iff_of_aInvariant [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {K : Subgroup (↥data.H ⧸ chief.N)} (hK : IsAInvariant (uActionHom data chief) K)
    {a : ↥(data.typeP.U ⊔ data.typeP.W1)} (haU : ((a : G)) ∈ data.typeP.U)
    (θ : (↥data.H ⧸ chief.N) →* ℂˣ) :
    (θ.comp (quotientMulAutHom chief.N_aInvariant a).toMonoidHom).comp K.subtype = 1
      ↔ θ.comp K.subtype = 1 :=
  comp_uActionHom_comp_subtype_eq_one_iff_of_aInvariant hK
    (⟨a, Subgroup.mem_subgroupOf.mpr haU⟩ :
      ↥(typeP_quotientCoprimeAction data.typeP data.nontrivial.1 chief.N_aInvariant).U) θ

/-- **step 2 D₂: precompose–pointwise-smul bridge**.  A character `θ` is trivial on the translate
`a • S` (`a : MulAut K`) iff its precomposition `θ ∘ a` is trivial on `S` (any element of `a • S` is
`a s` for `s ∈ S`).  Used with `a = q(v)` (`quotientMulAutHom`) and `S = S₀` to turn nontriviality
on
the Clifford summand `Hpart i = q(orbitRep i) • S₀` into nontriviality of `θbar ∘ q(orbitRep i)` on
the generator `S₀`, the last bridge of the (9.8.c) surjectivity regularity argument. -/
theorem comp_subtype_pointwise_smul_eq_one_iff {K : Type*} [Group K] (a : MulAut K)
    (θ : K →* ℂˣ) (S : Subgroup K) :
    θ.comp (a • S).subtype = 1 ↔ (θ.comp a.toMonoidHom).comp S.subtype = 1 := by
  rw [MonoidHom.ext_iff, MonoidHom.ext_iff]
  refine ⟨fun h s => ?_, fun h y => ?_⟩
  · have hval := h ⟨a • (s : K), (Subgroup.smul_mem_pointwise_smul_iff).mpr s.2⟩
    simpa only [MonoidHom.comp_apply, Subgroup.subtype_apply, MonoidHom.one_apply,
      MulEquiv.coe_toMonoidHom, MulAut.smul_def] using hval
  · have hval := h ⟨a⁻¹ • (y : K), (Subgroup.mem_pointwise_smul_iff_inv_smul_mem).mp y.2⟩
    simp only [MonoidHom.comp_apply, Subgroup.subtype_apply, MonoidHom.one_apply,
      MulEquiv.coe_toMonoidHom, MulAut.smul_def, MulAut.apply_inv_self] at hval ⊢
    exact hval

/-- **step 2 E (W₁ case): `θbar ∘ q(w)` and `θbar` agree on `S₀` (triviality)** for `w` a
`W₁`-element, given `χ = ζ` is `M`-fixed.  From `M`-fixedness the orbit equality
`exists_uPart_theta_comp_quotient_eq_of_fixed` gives `a ∈ U` with `θbar ∘ q(a) = θbar ∘ q(w)`; then
`comp_quotient_uPart_..._of_aInvariant` (`S₀` is `U`-invariant, `S0_aInvariant`) collapses the
`U`-twist.  This is the `W₁`-half of the `U ⊔ W₁` orbit-invariance on `S₀`. -/
theorem caseA_theta_comp_quotient_W1_on_S0_eq_one_iff_of_fixed [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars)
    (θbar : (↥data.H ⧸ chief.N) →* ℂˣ)
    [Fintype ↥(hInHu data)] [Invertible (Nat.card ↥(hInHu data) : ℂ)]
    (ζ : IrreducibleCharacter ↥(huSub data))
    (hlo : OddOrder.RepresentationTheory.IrreducibleCharacter.LiesOver (hInHu data) ζ
      (linearIrreducibleCharacter (θbar.comp ((QuotientGroup.mk' chief.N).comp
        (hInHuEquivH data).toMonoidHom))))
    (hMfix : ClassFunction.inertia (ζ : ClassFunction ↥(huSub data) ℂ) = ⊤)
    {w : ↥(data.typeP.U ⊔ data.typeP.W1)} (hwW : ((w : G)) ∈ data.typeP.W1) :
    (θbar.comp (quotientMulAutHom chief.N_aInvariant w).toMonoidHom).comp caseA.S0.subtype = 1
      ↔ θbar.comp caseA.S0.subtype = 1 := by
  have hwM : ((w : ↥(data.typeP.U ⊔ data.typeP.W1)) : G) ∈ M := data.typeP.W1_le hwW
  have hfix : ClassFunction.conjBy (⟨(w : G), hwM⟩ : ↥M) (ζ : ClassFunction ↥(huSub data) ℂ)
      = (ζ : ClassFunction ↥(huSub data) ℂ) :=
    ClassFunction.mem_inertia.mp (hMfix ▸ Subgroup.mem_top _)
  obtain ⟨a, haU, hEq⟩ :=
    exists_uPart_theta_comp_quotient_eq_of_fixed (⟨(w : G), hwM⟩ : ↥M) w rfl θbar ζ hlo hfix
  rw [← hEq]
  exact comp_quotient_uPart_comp_subtype_eq_one_iff_of_aInvariant caseA.S0_aInvariant haU θbar

/-- **step 2 E (`U ⊔ W₁` case): `θbar ∘ q(v)` and `θbar` agree on `S₀`** for any `v ∈ U ⊔ W₁`,
given `ζ` is `M`-fixed.  Frobenius-decompose `v = u·w` (`U ◁ U W₁`, `Subgroup.normal_mul`); then
`θbar∘q(u·w)` on `S₀` `= (θbar∘q(u))∘q(w)` on `S₀` `⟺ θbar∘q(u)` on `q(w)•S₀`
(`comp_subtype_pointwise_smul`) `⟺ θbar` on `q(w)•S₀` (`comp_quotient_uPart_..._of_aInvariant`,
`q(w)•S₀` `U`-invariant) `⟺ θbar∘q(w)` on `S₀` (`comp_subtype_pointwise_smul`) `⟺ θbar` on `S₀`
(the `W₁` case).  So `θbar`'s nontriviality on `S₀` is invariant under the whole `U ⊔ W₁`-action —
the key to reducing per-`Hpart` regularity to a single `S₀` condition. -/
theorem caseA_theta_comp_quotient_on_S0_eq_one_iff_of_fixed [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars)
    (θbar : (↥data.H ⧸ chief.N) →* ℂˣ)
    [Fintype ↥(hInHu data)] [Invertible (Nat.card ↥(hInHu data) : ℂ)]
    (ζ : IrreducibleCharacter ↥(huSub data))
    (hlo : OddOrder.RepresentationTheory.IrreducibleCharacter.LiesOver (hInHu data) ζ
      (linearIrreducibleCharacter (θbar.comp ((QuotientGroup.mk' chief.N).comp
        (hInHuEquivH data).toMonoidHom))))
    (hMfix : ClassFunction.inertia (ζ : ClassFunction ↥(huSub data) ℂ) = ⊤)
    (v : ↥(data.typeP.U ⊔ data.typeP.W1)) :
    (θbar.comp (quotientMulAutHom chief.N_aInvariant v).toMonoidHom).comp caseA.S0.subtype = 1
      ↔ θbar.comp caseA.S0.subtype = 1 := by
  have hUnorm : (data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1)).Normal :=
    (typeP_uW1_frobenius data.typeP data.nontrivial.1).isNormal
  have htop : data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1)
      ⊔ data.typeP.W1.subgroupOf (data.typeP.U ⊔ data.typeP.W1) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right, Subgroup.subgroupOf_self]
  have hv : v ∈ data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1)
      ⊔ data.typeP.W1.subgroupOf (data.typeP.U ⊔ data.typeP.W1) := htop ▸ Subgroup.mem_top v
  rw [← SetLike.mem_coe, Subgroup.normal_mul] at hv
  obtain ⟨u, hu, w, hw, rfl⟩ := hv
  have huU : ((u : ↥(data.typeP.U ⊔ data.typeP.W1)) : G) ∈ data.typeP.U :=
    Subgroup.mem_subgroupOf.mp hu
  have hwW : ((w : ↥(data.typeP.U ⊔ data.typeP.W1)) : G) ∈ data.typeP.W1 :=
    Subgroup.mem_subgroupOf.mp hw
  have hsplit : (θbar.comp (quotientMulAutHom chief.N_aInvariant (u * w)).toMonoidHom).comp
        caseA.S0.subtype
      = ((θbar.comp (quotientMulAutHom chief.N_aInvariant u).toMonoidHom).comp
          (quotientMulAutHom chief.N_aInvariant w).toMonoidHom).comp caseA.S0.subtype := by
    rw [map_mul]; rfl
  rw [hsplit, ← comp_subtype_pointwise_smul_eq_one_iff,
    comp_quotient_uPart_comp_subtype_eq_one_iff_of_aInvariant
      (isAInvariant_comp_subtype_pointwise_smul hUnorm caseA.S0_aInvariant w) huU θbar,
    comp_subtype_pointwise_smul_eq_one_iff]
  exact caseA_theta_comp_quotient_W1_on_S0_eq_one_iff_of_fixed caseA θbar ζ hlo hMfix hwW

/-- **step 2 (regularity): a reducible constituent seed is regular** (Peterfalvi (9.8.c)
surjectivity).  If `ζ` is `M`-fixed (`I_M(ζ) = ⊤`, from reducibility of `Ind_M ζ`) and lies over the
inflation of a nonzero seed `θbar : H̄ →* ℂˣ`, then `θbar` is *regular*: nontrivial on every
Clifford
summand `Hpart i`.  Two steps, both via the `S₀`-aggregation
`caseA_theta_comp_quotient_on_S0_eq_one_iff_of_fixed` (`θbar ∘ q(v)` and `θbar` agree on `S₀`):
`θbar` is nontrivial on `S₀` (else it is trivial on every `Hpart i = q(orbitRep i) • S₀`, hence on
`⨆ Hpart = ⊤ = H̄`, forcing `θbar = 1`); and then each `Hpart i` inherits nontriviality from `S₀`.
This is the last input to `ζ = Ind_{HC}(hcPsi θbar) ∈ Xθ` (via `inertia_eq_hcInHu_caseA` and the
Clifford correspondence), closing the `Xmu`-surjectivity of the (9.8.c) parity dichotomy. -/
theorem caseA_reducible_theta_regular [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars)
    (θbar : (↥data.H ⧸ chief.N) →* ℂˣ)
    [Fintype ↥(hInHu data)] [Invertible (Nat.card ↥(hInHu data) : ℂ)]
    (ζ : IrreducibleCharacter ↥(huSub data))
    (hlo : OddOrder.RepresentationTheory.IrreducibleCharacter.LiesOver (hInHu data) ζ
      (linearIrreducibleCharacter (θbar.comp ((QuotientGroup.mk' chief.N).comp
        (hInHuEquivH data).toMonoidHom))))
    (hMfix : ClassFunction.inertia (ζ : ClassFunction ↥(huSub data) ℂ) = ⊤)
    (hnt : θbar ≠ 1) :
    ∀ i, θbar.comp (caseA.Hpart i).subtype ≠ 1 := by
  -- `θbar` is nontrivial on `S₀`.
  have hS0 : θbar.comp caseA.S0.subtype ≠ 1 := by
    intro h0
    apply hnt
    -- Every `Hpart i` is in `ker θbar`, and they span `H̄`, so `θbar = 1`.
    have hker : ∀ i, caseA.Hpart i ≤ θbar.ker := by
      intro i x hx
      have htriv : θbar.comp (caseA.Hpart i).subtype = 1 := by
        rw [caseA.Hpart_orbit i, comp_subtype_pointwise_smul_eq_one_iff,
          caseA_theta_comp_quotient_on_S0_eq_one_iff_of_fixed caseA θbar ζ hlo hMfix
            (caseA.orbitRep i)]
        exact h0
      have hval := DFunLike.congr_fun htriv ⟨x, hx⟩
      rw [MonoidHom.mem_ker]
      simpa only [MonoidHom.comp_apply, Subgroup.subtype_apply, MonoidHom.one_apply] using hval
    refine MonoidHom.ext fun x => ?_
    have hxker : x ∈ θbar.ker :=
      (caseA.Hpart_iSup ▸ iSup_le hker : (⊤ : Subgroup (↥data.H ⧸ chief.N)) ≤ θbar.ker)
        (Subgroup.mem_top x)
    rw [MonoidHom.mem_ker] at hxker
    rw [hxker, MonoidHom.one_apply]
  -- Each `Hpart i` inherits nontriviality from `S₀`.
  intro i
  rw [ne_eq, caseA.Hpart_orbit i, comp_subtype_pointwise_smul_eq_one_iff,
    caseA_theta_comp_quotient_on_S0_eq_one_iff_of_fixed caseA θbar ζ hlo hMfix (caseA.orbitRep i)]
  exact hS0

/-- **step 5 foundation: a reducible constituent seed has inflation-inertia `HC`** (Peterfalvi
(9.8.c)).  Chains the regularity `caseA_reducible_theta_regular` (a reducible `M`-fixed `ζ`'s
constituent seed `θbar` is regular) into `inertia_eq_hcInHu_caseA` (a regular seed's inflation `θ₀`
has `HU`-inertia `HC`), converting the hom-form regularity to the `IrreducibleCharacter` pointwise
form via `comp_subtype_ne_one_iff_exists`. This `I_{HU}(θ₀) = HC` is what makes
`Ind_{HC}(hcPsi θbar)`
irreducible (`hcZeta_irreducible`) and drives the Clifford-correspondence identification
`ζ = Ind_{HC}(hcPsi θbar) ∈ Xθ` closing the `Xmu`-surjectivity. -/
theorem caseA_reducible_inflation_inertia_eq [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars)
    (θbar : (↥data.H ⧸ chief.N) →* ℂˣ)
    [Fintype ↥(hInHu data)] [Invertible (Nat.card ↥(hInHu data) : ℂ)]
    (ζ : IrreducibleCharacter ↥(huSub data))
    (hlo : OddOrder.RepresentationTheory.IrreducibleCharacter.LiesOver (hInHu data) ζ
      (linearIrreducibleCharacter (θbar.comp ((QuotientGroup.mk' chief.N).comp
        (hInHuEquivH data).toMonoidHom))))
    (hMfix : ClassFunction.inertia (ζ : ClassFunction ↥(huSub data) ℂ) = ⊤)
    (hnt : θbar ≠ 1) :
    ClassFunction.inertia (ClassFunction.compHom (hInHuEquivH data).toMonoidHom
        (ClassFunction.compHom (QuotientGroup.mk' chief.N)
          (linearIrreducibleCharacter θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ)))
      = hInHu data ⊔ cInHu data chief := by
  refine inertia_eq_hcInHu_caseA data chief caseA (fun i => ?_)
  obtain ⟨x, hx, hne⟩ := (comp_subtype_ne_one_iff_exists caseA θbar i).mp
    (caseA_reducible_theta_regular caseA θbar ζ hlo hMfix hnt i)
  refine ⟨x, hx, ?_⟩
  rw [linearIrreducibleCharacter_apply, linearIrreducibleCharacter_apply, map_one, Units.val_one]
  simpa using hne

/-- **Restriction transitivity** (general): for `H ≤ K ≤ G`, restricting a class function to `K`
and then to `H` (realised in `K` as `H.subgroupOf K`) equals restricting directly to `H`,
transported
along the iso `H.subgroupOf K ≃* H`.  Foundational for the lies-over transitivity in the (9.8.c)
Clifford-correspondence step 5 (`ξ` over `θ₀` at `H = hInHu ⊆ HC` factors through an
`HC`-constituent).
Pointwise both sides are `φ` at the common `G`-image. -/
theorem restrict_restrict_subgroupOf {Γ k : Type*} [Group Γ] [CommRing k]
    {H K : Subgroup Γ} (hHK : H ≤ K) (φ : ClassFunction Γ k) :
    ClassFunction.restrict (H.subgroupOf K) (ClassFunction.restrict K φ)
      = ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hHK).toMonoidHom
          (ClassFunction.restrict H φ) := by
  ext x
  simp only [ClassFunction.restrict_apply, ClassFunction.compHom_apply, MulEquiv.coe_toMonoidHom]
  congr 1

/-- **`innerSum` is preserved under `compHom` by a group isomorphism** (reindex the sum by the iso).
Generalises `innerSum_compHom_of_bijective` (an endomorphism) to a `MulEquiv A ≃* B`. -/
theorem innerSum_compHom_mulEquiv {A B : Type*} [Group A] [Group B] [Fintype A] [Fintype B]
    (e : A ≃* B) (a b : ClassFunction B ℂ) :
    ClassFunction.innerSum (ClassFunction.compHom e.toMonoidHom a)
        (ClassFunction.compHom e.toMonoidHom b) = ClassFunction.innerSum a b := by
  simpa only [ClassFunction.innerSum, ClassFunction.compHom_apply, MulEquiv.coe_toMonoidHom] using
    Fintype.sum_equiv e.toEquiv
      (fun x => a (e x) * star (b (e x))) (fun y => a y * star (b y)) (fun _ => rfl)

end OddOrder.Peterfalvi.S11


