-- Prove2me | Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_InertiaAbelianQuotient
-- name    : OddOrder_GroupTheory_RepresentationTheory_InertiaAbelianQuotient
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T04:46:14.841267+00:00
-- url     : https://prove2.me/theorems/8fc4f3f0-8cbb-4bba-a263-eaf6dd82e69d
-- title:
--   Abelian inertia quotient $I(\theta)/H$ from an abelian complement
-- statement:
--   Generic group theory behind the Peterfalvi (1.7)(b) precondition that the inertia quotient $I(\theta)/H$ is abelian: for a class function $\theta$ on a normal subgroup $H\trianglelefteq\Gamma$ and a complement $U$ with $\Gamma=HU$, if $I(\theta)\cap U$ lies in an abelian subgroup then $I(\theta)/H$ is abelian.
--
--   The main result is `commutator_inertia_le_of_sup_eq_top`, giving $[I(\theta),I(\theta)]\le H$.
--
--   The bundle also proves 1 supporting lemma used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/GroupTheory/RepresentationTheory/InertiaAbelianQuotient.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/GroupTheory/RepresentationTheory/InertiaAbelianQuotient.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_Inertia
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Algebra.Group.Subgroup.Pointwise

namespace OddOrder.RepresentationTheory

namespace ClassFunction

variable {Γ : Type*} [Group Γ] {k : Type*} [CommRing k]

/-- **A subgroup of an abelian subgroup is abelian, applied to the inertia complement `I(θ) ∩ U`.**
If `I(θ) ∩ U ≤ U₁` and `U₁` is abelian, then `I(θ) ∩ U` is abelian.  (In Peterfalvi's type-`F`
setting `U₁` is abelian and `I(θ) ∩ U ⊆ U₁` is (8.2.c); here that inclusion is a hypothesis.) -/
theorem inertia_inf_isMulCommutative_of_le {H U U1 : Subgroup Γ} [H.Normal]
    (θ : ClassFunction ↥H k)
    (hle : ClassFunction.inertia θ ⊓ U ≤ U1) (hU1comm : IsMulCommutative ↥U1) :
    IsMulCommutative ↥(ClassFunction.inertia θ ⊓ U) := by
  refine IsMulCommutative.of_comm (fun a b => Subtype.ext ?_)
  have hcomm := (isMulCommutative_iff.mp hU1comm) ⟨(a : Γ), hle a.2⟩ ⟨(b : Γ), hle b.2⟩
  simpa [Subgroup.coe_mul] using congrArg Subtype.val hcomm

open scoped commutatorElement in
/-- **The inertia quotient `I(θ)/H` is abelian**, in the form `⁅I(θ), I(θ)⁆ ≤ H`.  Assume
`H ⊴ Γ`, `Γ = H U` (`H ⊔ U = ⊤`), and the inertia complement `I(θ) ∩ U` is abelian.  Since
`H ≤ I(θ)` (`ClassFunction.subgroup_le_inertia`), the Dedekind modular law factors every `s ∈ I(θ)`
as `s = h · u` with `h ∈ H` and `u = h⁻¹ s ∈ I(θ) ∩ U`.  Passing to `Γ ⧸ H`, the images of any two
`s, t ∈ I(θ)` are the images of `u, u' ∈ I(θ) ∩ U`, which commute; hence `⁅s, t⁆ ∈ H`, i.e.
`⁅I(θ), I(θ)⁆ ≤ H`.

This is the abelian-inertia-quotient hypothesis of Peterfalvi (1.7)(b) that makes `Ind_H^L θ`
multiplicity-free with equal-degree constituents.  In the type-`F` application the abelianness of
`I(θ) ∩ U` comes from (8.2.c) (`I(θ) ∩ U ⊆ U₁`, `U₁` abelian) via
`inertia_inf_isMulCommutative_of_le`. -/
theorem commutator_inertia_le_of_sup_eq_top {H U : Subgroup Γ} [H.Normal]
    (hHU : H ⊔ U = ⊤) (θ : ClassFunction ↥H k)
    (hcomm : IsMulCommutative ↥(ClassFunction.inertia θ ⊓ U)) :
    ⁅ClassFunction.inertia θ, ClassFunction.inertia θ⁆ ≤ H := by
  set T := ClassFunction.inertia θ with hTdef
  have hHT : H ≤ T := ClassFunction.subgroup_le_inertia θ
  -- Dedekind: factor every `s ∈ T` as `h · u`, `h ∈ H`, `u ∈ T ⊓ U`.
  have hfactor : ∀ s ∈ T, ∃ h ∈ H, ∃ u ∈ T ⊓ U, h * u = s := by
    intro s hs
    have hmem : s ∈ (↑(H ⊔ U) : Set Γ) := by rw [hHU]; exact Subgroup.mem_top s
    rw [Subgroup.normal_mul H U] at hmem
    obtain ⟨h, hh, u, hu, hhu⟩ := Set.mem_mul.mp hmem
    rw [SetLike.mem_coe] at hh hu
    refine ⟨h, hh, u, Subgroup.mem_inf.mpr ⟨?_, hu⟩, hhu⟩
    have hueq : u = h⁻¹ * s := by rw [← hhu]; group
    rw [hueq]
    exact T.mul_mem (T.inv_mem (hHT hh)) hs
  rw [Subgroup.commutator_le]
  intro s hs t ht
  obtain ⟨h₁, hh₁, u₁, hu₁, hs_eq⟩ := hfactor s hs
  obtain ⟨h₂, hh₂, u₂, hu₂, ht_eq⟩ := hfactor t ht
  -- `u₁, u₂ ∈ T ⊓ U` commute (that subgroup is abelian).
  have hcommU : u₁ * u₂ = u₂ * u₁ := by
    have hc := (isMulCommutative_iff.mp hcomm) ⟨u₁, hu₁⟩ ⟨u₂, hu₂⟩
    simpa [Subgroup.coe_mul] using congrArg Subtype.val hc
  -- In `Γ ⧸ H` the images of `s, t` are the images of `u₁, u₂`, which commute; hence `⁅s,t⁆ ∈ H`.
  have hh₁q : (QuotientGroup.mk' H) h₁ = 1 := by
    rw [QuotientGroup.mk'_apply]; exact (QuotientGroup.eq_one_iff h₁).mpr hh₁
  have hh₂q : (QuotientGroup.mk' H) h₂ = 1 := by
    rw [QuotientGroup.mk'_apply]; exact (QuotientGroup.eq_one_iff h₂).mpr hh₂
  have hqs : (QuotientGroup.mk' H) s = (QuotientGroup.mk' H) u₁ := by
    rw [← hs_eq, map_mul, hh₁q, one_mul]
  have hqt : (QuotientGroup.mk' H) t = (QuotientGroup.mk' H) u₂ := by
    rw [← ht_eq, map_mul, hh₂q, one_mul]
  have hq : (QuotientGroup.mk' H) ⁅s, t⁆ = 1 := by
    rw [map_commutatorElement, hqs, hqt]
    refine commutatorElement_eq_one_iff_commute.mpr ?_
    have hcm : (QuotientGroup.mk' H) u₁ * (QuotientGroup.mk' H) u₂
        = (QuotientGroup.mk' H) u₂ * (QuotientGroup.mk' H) u₁ := by
      rw [← map_mul, ← map_mul, hcommU]
    exact hcm
  have hmemk : ⁅s, t⁆ ∈ (QuotientGroup.mk' H).ker := MonoidHom.mem_ker.mpr hq
  rwa [QuotientGroup.ker_mk'] at hmemk

end ClassFunction

end OddOrder.RepresentationTheory


