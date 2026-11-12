-- Prove2me | Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_PermutationInvariants
-- name    : OddOrder_GroupTheory_RepresentationTheory_PermutationInvariants
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T04:40:37.660196+00:00
-- url     : https://prove2.me/theorems/12ec3409-6f5e-4345-9788-9e01a1a548e2
-- title:
--   Invariants of a permutation representation have dimension equal to the number of orbits
-- statement:
--   For the kernel-FPF count ($\dagger$) of Peterfalvi (9.1), the Brauer permutation lemma is needed in the form that the number of $\langle e\rangle$-orbits on classes equals the number of $\langle e\rangle$-orbits on simples over $\bar{\mathbb{F}}_p$. Both counts are dimensions of $\langle e\rangle$-invariants of $Z(\bar{\mathbb{F}}_p[U])$; this file proves the cornerstone: the invariants of a permutation representation have dimension the number of orbits (any field).
--
--   Main declarations: `orbitToVec`; `repr_smul_eq`; `finrank_invariants_eq_card_orbits` (Cornerstone (Brauer permutation lemma, orbit form, any field)).
--
--   The bundle also proves 5 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/GroupTheory/RepresentationTheory/PermutationInvariants.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/GroupTheory/RepresentationTheory/PermutationInvariants.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Mathlib.RepresentationTheory.Invariants
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Dimension.Free

namespace OddOrder.GroupTheory.PermutationInvariants

open MulAction Representation Module

variable {ι G : Type*} [Group G] [MulAction G ι]

/-- `⟦g • i⟧ = ⟦i⟧`: a point and its `G`-translate lie in the same orbit. -/
theorem quotient_smul_eq (g : G) (i : ι) :
    (Quotient.mk'' (g • i) : orbitRel.Quotient G ι) = Quotient.mk'' i :=
  Quotient.sound' ⟨g, rfl⟩

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V] [Fintype ι]

/-- The linear map `(Ω → k) → V` sending a function `h` on the orbit space to the vector whose
`b`-coordinate at `i` is `h ⟦i⟧`.  Its image is exactly the `G`-invariants. -/
noncomputable def orbitToVec (b : Basis ι k V) :
    (orbitRel.Quotient G ι → k) →ₗ[k] V where
  toFun h := ∑ i, h (Quotient.mk'' i) • b i
  map_add' h₁ h₂ := by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c h := by
    simp only [Pi.smul_apply, smul_eq_mul, mul_smul, RingHom.id_apply, Finset.smul_sum]

@[simp] theorem orbitToVec_apply (b : Basis ι k V) (h : orbitRel.Quotient G ι → k) :
    orbitToVec b h = ∑ i, h (Quotient.mk'' i) • b i := rfl

/-- Every vector in the image of `orbitToVec` is `G`-invariant. -/
theorem orbitToVec_mem_invariants (b : Basis ι k V) (ρ : Representation k G V)
    (hρ : ∀ (g : G) (i : ι), ρ g (b i) = b (g • i)) (h : orbitRel.Quotient G ι → k) :
    orbitToVec b h ∈ invariants ρ := by
  rw [mem_invariants]
  intro g
  rw [orbitToVec_apply, map_sum]
  rw [Fintype.sum_bijective (g • ·) (MulAction.bijective g)
    (fun i => ρ g (h (Quotient.mk'' i) • b i)) (fun j => h (Quotient.mk'' j) • b j)]
  intro i
  rw [map_smul, hρ g i, quotient_smul_eq g i]

/-- `orbitToVec` is injective: distinct functions on the orbit space give distinct invariant
vectors (the coordinates `h ⟦i⟧` recover `h` since `Quotient.mk''` is surjective). -/
theorem orbitToVec_injective (b : Basis ι k V) :
    Function.Injective (orbitToVec (k := k) (V := V) (G := G) b) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro h hh
  have hzero : ∀ i, h (Quotient.mk'' i) = 0 := by
    have := Fintype.linearIndependent_iff.mp b.linearIndependent
      (fun i => h (Quotient.mk'' i))
    exact this (by rw [← orbitToVec_apply]; exact hh)
  funext ω
  obtain ⟨i, rfl⟩ := Quotient.mk''_surjective ω
  exact hzero i

omit [Fintype ι] in
/-- For an invariant vector, the `b`-coordinates are constant along `G`-orbits:
`(b.repr v) (g • i) = (b.repr v) i`.  (`v` invariant means `b.repr v` is fixed by the coordinate
permutation `Finsupp.mapDomain (g • ·)`.) -/
theorem repr_smul_eq (b : Basis ι k V) (ρ : Representation k G V)
    (hρ : ∀ (g : G) (i : ι), ρ g (b i) = b (g • i)) {v : V} (hv : v ∈ invariants ρ)
    (g : G) (i : ι) : b.repr v (g • i) = b.repr v i := by
  rw [mem_invariants] at hv
  have hmap : b.repr.toLinearMap.comp (ρ g) =
      (Finsupp.lmapDomain k k (g • ·)).comp b.repr.toLinearMap :=
    b.ext fun j => by
      simp [LinearMap.comp_apply, hρ g j, Basis.repr_self, Finsupp.lmapDomain_apply,
        Finsupp.mapDomain_single]
  have hv2 := LinearMap.congr_fun hmap v
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hv g, Finsupp.lmapDomain_apply] at hv2
  calc b.repr v (g • i)
      = (Finsupp.mapDomain (g • ·) (b.repr v)) (g • i) := by rw [← hv2]
    _ = b.repr v i := Finsupp.mapDomain_apply (MulAction.injective g) _ _

/-- The image of `orbitToVec` is **exactly** the `G`-invariants: every invariant vector has
`b`-coordinates constant on orbits (`repr_smul_eq`), so it is `orbitToVec b h` for the function
`h ω := b.repr v ω.out'`. -/
theorem orbitToVec_range_eq (b : Basis ι k V) (ρ : Representation k G V)
    (hρ : ∀ (g : G) (i : ι), ρ g (b i) = b (g • i)) :
    LinearMap.range (orbitToVec (G := G) b) = invariants ρ := by
  apply le_antisymm
  · rintro _ ⟨h, rfl⟩
    exact orbitToVec_mem_invariants b ρ hρ h
  · intro v hv
    refine ⟨fun ω => b.repr v (Quotient.out ω), ?_⟩
    rw [orbitToVec_apply]
    conv_rhs => rw [← b.sum_repr v]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    congr 1
    have hrel : (Quotient.mk'' (Quotient.out (Quotient.mk'' i : orbitRel.Quotient G ι))) =
        (Quotient.mk'' i : orbitRel.Quotient G ι) := Quotient.out_eq' _
    rw [Quotient.eq''] at hrel
    obtain ⟨g, hg⟩ := hrel
    rw [← hg, repr_smul_eq b ρ hρ hv]

set_option linter.unusedFintypeInType false in
/-- **Cornerstone (Brauer permutation lemma, orbit form, any field).**  If a representation `ρ` of a
finite group `G` on `V` permutes a basis `b` according to a `G`-action on `ι`
(`ρ g (b i) = b (g • i)`), then `dim Vᴳ = #(G-orbits on ι)`.  The invariants are linearly
parametrised by functions on the orbit space `Ω = orbitRel.Quotient G ι` via `orbitToVec`. -/
theorem finrank_invariants_eq_card_orbits (b : Basis ι k V) (ρ : Representation k G V)
    (hρ : ∀ (g : G) (i : ι), ρ g (b i) = b (g • i)) :
    finrank k ↥(invariants ρ) = Nat.card (orbitRel.Quotient G ι) := by
  have : Fintype (orbitRel.Quotient G ι) := Fintype.ofFinite _
  let e : (orbitRel.Quotient G ι → k) ≃ₗ[k] ↥(invariants ρ) :=
    (LinearEquiv.ofInjective (orbitToVec (G := G) b) (orbitToVec_injective b)).trans
      (LinearEquiv.ofEq _ _ (orbitToVec_range_eq b ρ hρ))
  rw [← e.finrank_eq, Module.finrank_pi, Nat.card_eq_fintype_card]

end OddOrder.GroupTheory.PermutationInvariants


