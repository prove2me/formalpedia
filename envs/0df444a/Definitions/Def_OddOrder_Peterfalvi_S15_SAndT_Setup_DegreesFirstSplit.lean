-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S15_SAndT_Setup_DegreesFirstSplit
-- name    : OddOrder_Peterfalvi_S15_SAndT_Setup_DegreesFirstSplit
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T15:43:28.583592+00:00
-- url     : https://prove2.me/theorems/1c30db0f-6fa1-430b-80b7-80f55d452986
-- title:
--   Peterfalvi (13.5): degrees, first split (continuation)
-- statement:
--   A continuation file with the generic (13.5.a) correction term in the $P'$-kernel tail of the (7.7.a) setup.
--
--   Main declarations: `hypothesis76AlphaFun` (Generic (13.5.a) correction term); `hypothesis76AlphaCF` (The generic (13.5.a) correction as a class function on `↥L`); `H_sharp_alphaFun` (The (13.5.a) correction term `α`); `H_sharp_alphaCF` (The (13.5.a) correction as a class function on `↥S`).
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S15_SAndT_Setup/DegreesFirstSplit.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S15_SAndT_Setup/DegreesFirstSplit.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S15_SAndT_Setup_Machinery135

namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

section GenericAlpha

variable {A : Set G} {L : Subgroup G}

open scoped Classical in
open scoped OddOrder.Peterfalvi.S15.FiniteInduce in
/-- Generic (13.5.a) correction term: the `P'`-kernel tail of the (7.7.a) decomposition. -/
noncomputable def hypothesis76AlphaFun [Fintype G] [Invertible (Nat.card G : ℂ)]
    (H76 : OddOrder.Peterfalvi.S09.Hypothesis76 G A L) (P' : Subgroup ↥L)
    (χ : ClassFunction G ℂ) : ↥L → ℂ :=
  fun a =>
    ∑ i ∈ (Finset.Ioi (0 : Fin (H76.n + 1))).filter
          (fun i => (P' : Set ↥L) ⊆
            OddOrder.Peterfalvi.S03.characterKernel (H76.zeta i)),
        (star (H76.cCoeff χ i) / H76.zetaNormSq i) * H76.zeta i a

open scoped Classical in
open scoped OddOrder.Peterfalvi.S15.FiniteInduce in
/-- The generic (13.5.a) correction as a class function on `↥L`.  This is the
class-function realization of `hypothesis76AlphaFun`, needed when restricting the correction
to the normal subgroup `H76.H.subgroupOf L`. -/
noncomputable def hypothesis76AlphaCF [Fintype G] [Invertible (Nat.card G : ℂ)]
    (H76 : OddOrder.Peterfalvi.S09.Hypothesis76 G A L) (P' : Subgroup ↥L)
    (χ : ClassFunction G ℂ) : ClassFunction ↥L ℂ :=
  ∑ i ∈ (Finset.Ioi (0 : Fin (H76.n + 1))).filter
        (fun i => (P' : Set ↥L) ⊆
          OddOrder.Peterfalvi.S03.characterKernel (H76.zeta i)),
      (star (H76.cCoeff χ i) / H76.zetaNormSq i) • H76.zeta i

open scoped Classical in
open scoped OddOrder.Peterfalvi.S15.FiniteInduce in
@[simp] theorem hypothesis76AlphaCF_apply [Fintype G] [Invertible (Nat.card G : ℂ)]
    (H76 : OddOrder.Peterfalvi.S09.Hypothesis76 G A L) (P' : Subgroup ↥L)
    (χ : ClassFunction G ℂ) (a : ↥L) :
    hypothesis76AlphaCF H76 P' χ a = hypothesis76AlphaFun H76 P' χ a := by
  rw [hypothesis76AlphaCF, hypothesis76AlphaFun,
    OddOrder.RepresentationTheory.ClassFunction.finset_sum_apply]
  exact Finset.sum_congr rfl (fun i _ => by rw [ClassFunction.smul_apply])

end GenericAlpha

open scoped OddOrder.Peterfalvi.S15.FiniteInduce Classical in
/-- **The (13.5.a) correction term `α`** for a test character `χ`: the `P`-kernel tail
`α = ∑_{i≥1, P⊆ker ζ_i} (c̄_i/‖ζ_i‖²)·ζ_i` of the (7.7.a) decomposition, as a function on `↥S`.
By `H_sharp_point_formula` (resp. the `a = 0` variant), `χ = (distinguished term) + α` (resp.
`χ = α`) on `H^#`; it is constant on `P` (`H_sharp_alphaFun_const_on_P`) and vanishes off `H`
(`H_sharp_alphaFun_eq_zero_of_not_mem`), which drive the (13.5.c) inflation bound. -/
noncomputable def H_sharp_alphaFun [Fintype G] [Invertible (Nat.card G : ℂ)]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (χ : ClassFunction G ℂ) : ↥hyp.S → ℂ :=
  fun a =>
    ∑ i ∈ (Finset.Ioi (0 : Fin ((H_sharp_hypothesis76 hG hyp).n + 1))).filter
          (fun i => (hyp.P.subgroupOf hyp.S : Set ↥hyp.S) ⊆
            OddOrder.Peterfalvi.S03.characterKernel ((H_sharp_hypothesis76 hG hyp).zeta i)),
        (star ((H_sharp_hypothesis76 hG hyp).cCoeff χ i) /
          (H_sharp_hypothesis76 hG hyp).zetaNormSq i) * (H_sharp_hypothesis76 hG hyp).zeta i a

open scoped OddOrder.Peterfalvi.S15.FiniteInduce Classical in
/-- **The (13.5.a) correction as a class function on `↥S`**: `H_sharp_alphaFun` is the
underlying function of the `ℂ`-combination `∑_{i≥1, P⊆ker ζ_i} (c̄_i/‖ζ_i‖²) • ζ_i`. -/
noncomputable def H_sharp_alphaCF [Fintype G] [Invertible (Nat.card G : ℂ)]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (χ : ClassFunction G ℂ) : ClassFunction ↥hyp.S ℂ :=
  ∑ i ∈ (Finset.Ioi (0 : Fin ((H_sharp_hypothesis76 hG hyp).n + 1))).filter
        (fun i => (hyp.P.subgroupOf hyp.S : Set ↥hyp.S) ⊆
          OddOrder.Peterfalvi.S03.characterKernel ((H_sharp_hypothesis76 hG hyp).zeta i)),
      (star ((H_sharp_hypothesis76 hG hyp).cCoeff χ i) /
        (H_sharp_hypothesis76 hG hyp).zetaNormSq i) • (H_sharp_hypothesis76 hG hyp).zeta i

open scoped OddOrder.Peterfalvi.S15.FiniteInduce Classical in
@[simp] theorem H_sharp_alphaCF_apply [Fintype G] [Invertible (Nat.card G : ℂ)]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (χ : ClassFunction G ℂ) (a : ↥hyp.S) :
    H_sharp_alphaCF hG hyp χ a = H_sharp_alphaFun hG hyp χ a := by
  rw [H_sharp_alphaCF, H_sharp_alphaFun,
    OddOrder.RepresentationTheory.ClassFunction.finset_sum_apply]
  exact Finset.sum_congr rfl (fun i _ => by rw [ClassFunction.smul_apply])

/-- `H = PC` is normal in `S` (it is the Fitting subgroup, `H_eq_fittingInG`) — as an
instance on the `subgroupOf` form, so that `conjBy`/`inertia` statements over `↥S` elaborate. -/
instance H_sharp_subgroupOf_normal (hyp : Hypothesis (G := G)) :
    (hyp.H.subgroupOf hyp.S).Normal := by
  rw [hyp.H_eq_fittingInG]
  exact OddOrder.BG.Ch2.S08.fittingInG_subgroupOf_normal hyp.S

/-- The generic set `G₀` of (13.9) as a `Finset`. -/
noncomputable def Hypothesis.G0Finset [Finite G] (hyp : Hypothesis (G := G)) : Finset G :=
  (Set.toFinite hyp.G0).toFinset

open scoped Classical in
/-- **The squared-norm sum `Σ_{x∈A}‖χ(x)‖²` as a rational number** — defined as the natural
number it equals when the Galois-integrality applies (`χ ∈ ℤ[Irr]`, `A` cyclic-closed:
`exists_nat_sum_normSq_of_mem_ZIrr_of_cyclicClosed`), and junk `0` otherwise.  The (13.10) atoms
`slam`/`seta` are `normSqSumQ G₀ χ / |G|`. -/
noncomputable def normSqSumQ {H : Type*} [Group H] (A : Finset H) (χ : ClassFunction H ℂ) : ℚ :=
  if h : ∃ n : ℕ, (n : ℝ) = ∑ x ∈ A, ‖χ x‖ ^ 2 then ((Classical.choose h : ℕ) : ℚ) else 0

set_option maxHeartbeats 1600000 in
-- raised heartbeat budget for the heavy elaboration below
open scoped Classical FiniteInduce in
/-- **Peterfalvi (13.3.a)**: each nonzero `μ`-column sum `μ_j = ∑_i μ_{ij}` is induced from a
*linear* (degree-one) irreducible character of `H = PC`.

This is the honest statement of the `CharacterDegreeData.mu_j_linear_induced` field
(materializing (13.3.a) at the `S`-instance).  Assembly of the campaign pieces: `μ_j` lies in
the §9 family `𝒮(H₀)` (`mu_colSum_mem_sOf_H0`) and is reducible (`mu_colSum_not_irreducible`, a
sum of `q ≥ 2` distinct irreducibles), so the case-agnostic §9 `isIndHC`
(`reducible_sOf_H0_isIndHC`) gives `μ_j = Ind_{HC}(ψ)` with `ψ` linear irreducible; the `M`-level
`HC` is `(H ⊔ C).subgroupOf S = (PC).subgroupOf S` (`hcRealized_map_subtype_eq`,
`toTypesIIIIIIVSetupS_cSub_eq_C`, `H = P ⊔ C`), through which `ψ` transports to the required `θ`
on `hyp.H.subgroupOf hyp.S`. -/
theorem Hypothesis.mu_j_isIndPC [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (j : Fin hyp.p) (hj : j ≠ ⟨0, hyp.p_prime.pos⟩) :
    ∃ θ : ClassFunction ↥(hyp.H.subgroupOf hyp.S) ℂ,
      OddOrder.RepresentationTheory.IsIrreducibleCharacter θ ∧ θ 1 = 1 ∧
        (∑ i : Fin hyp.q, hyp.mu i j)
          = ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ := by
  classical
  have := hyp.finiteG
  set data := hyp.toTypesIIIIIIVSetupS hG with hdata
  obtain ⟨chief, -⟩ := OddOrder.Peterfalvi.S11.exists_chiefFactorData hG data
  let : Fintype ↥(OddOrder.Peterfalvi.S11.huSub data) := Fintype.ofFinite _
  let : Fintype ↥(OddOrder.Peterfalvi.S11.hInHu data ⊔
      ((chief.H0 ⊔ OddOrder.Peterfalvi.S11.cSub data chief).subgroupOf hyp.S).subgroupOf
        (OddOrder.Peterfalvi.S11.huSub data)) := Fintype.ofFinite _
  let : Fintype ↥((OddOrder.Peterfalvi.S11.hInHu data ⊔
      ((chief.H0 ⊔ OddOrder.Peterfalvi.S11.cSub data chief).subgroupOf hyp.S).subgroupOf
        (OddOrder.Peterfalvi.S11.huSub data)).map
      (OddOrder.Peterfalvi.S11.huSub data).subtype) := Fintype.ofFinite _
  let : Invertible (Nat.card ↥(OddOrder.Peterfalvi.S11.hInHu data ⊔
      ((chief.H0 ⊔ OddOrder.Peterfalvi.S11.cSub data chief).subgroupOf hyp.S).subgroupOf
        (OddOrder.Peterfalvi.S11.huSub data)) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  let : Invertible (Nat.card ↥((OddOrder.Peterfalvi.S11.hInHu data ⊔
      ((chief.H0 ⊔ OddOrder.Peterfalvi.S11.cSub data chief).subgroupOf hyp.S).subgroupOf
        (OddOrder.Peterfalvi.S11.huSub data)).map
      (OddOrder.Peterfalvi.S11.huSub data).subtype) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  -- `μ_j ∈ 𝒮(H₀)`, reducible → `isIndHC`
  have hmem := hyp.mu_colSum_mem_sOf_H0 hG chief j hj
  have hred := hyp.mu_colSum_not_irreducible j
  obtain ⟨ψ, hψirr, hψone, hψeq⟩ :=
    OddOrder.Peterfalvi.S11.reducible_sOf_H0_isIndHC hG (hyp.mkSection11CharacterDataS hG chief)
      hmem hred
  -- `HC.map subtype = (H ⊔ C).subgroupOf S = (PC).subgroupOf S = hyp.H.subgroupOf S`
  have hHeq : data.H = hyp.P := by change hyp.Sdata.H = hyp.P; rw [hyp.Sdata.H_eq, hyp.P_eq_SF]
  have hsupeq : data.H ⊔ OddOrder.Peterfalvi.S11.cSub data chief = hyp.H := by
    rw [hHeq, hyp.toTypesIIIIIIVSetupS_cSub_eq_C hG chief]; rfl
  have hHC : (OddOrder.Peterfalvi.S11.hInHu data ⊔
      ((chief.H0 ⊔ OddOrder.Peterfalvi.S11.cSub data chief).subgroupOf hyp.S).subgroupOf
        (OddOrder.Peterfalvi.S11.huSub data)).map (OddOrder.Peterfalvi.S11.huSub data).subtype
      = hyp.H.subgroupOf hyp.S := by
    rw [OddOrder.Peterfalvi.S11.hcRealized_map_subtype_eq chief, hsupeq]
  -- transport `ψ` back to `hyp.H.subgroupOf S`
  set θ := ClassFunction.compHom (MulEquiv.subgroupCongr hHC.symm).toMonoidHom ψ with hθdef
  refine ⟨θ, ?_, ?_, ?_⟩
  · exact OddOrder.RepresentationTheory.IsIrreducibleCharacter.compHom_of_surjective
      (MulEquiv.subgroupCongr hHC.symm).surjective hψirr
  · rw [hθdef, ClassFunction.compHom_apply, map_one, hψone]
  · rw [hψeq, hθdef,
      OddOrder.RepresentationTheory.induce_compHom_subgroupCongr hHC.symm ψ]

/-- The distinguished `η₁₀ = τ₃(ω₁₀)` of the (13.7)/(13.9) estimates. -/
noncomputable def Hypothesis.eta10 (hyp : Hypothesis (G := G)) : ClassFunction G ℂ :=
  hyp.eta ⟨1, hyp.q_prime.one_lt⟩ ⟨0, hyp.p_prime.pos⟩

end OddOrder.Peterfalvi.S15


