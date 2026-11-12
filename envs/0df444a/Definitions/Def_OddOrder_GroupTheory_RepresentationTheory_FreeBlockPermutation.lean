-- Prove2me | Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_FreeBlockPermutation
-- name    : OddOrder_GroupTheory_RepresentationTheory_FreeBlockPermutation
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T04:40:38.02981+00:00
-- url     : https://prove2.me/theorems/61a42eee-0e48-4a17-a557-41a37752d720
-- title:
--   Fixed-point dimension under a free block permutation
-- statement:
--   Proves the free block permutation dimension formula, the linear-algebra keystone of Bender–Glauberman Theorem 3.10(a): if a finite group $H$ acts through a representation $\rho$ on a finite-dimensional space $V=\bigoplus_i W_i$ whose blocks are permuted by $H$, with $H$ acting freely on the blocks, then the fixed-point dimension is determined by the block structure. The file builds block projections and reconstructs a vector from its block components.
--
--   Main declarations: `proj`; `proj_apply`; `proj_mem`; `proj_of_mem`; and 12 more.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/GroupTheory/RepresentationTheory/FreeBlockPermutation.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/GroupTheory/RepresentationTheory/FreeBlockPermutation.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Mathlib.RepresentationTheory.Invariants
import Mathlib.LinearAlgebra.Eigenspace.Pi
import Mathlib.GroupTheory.GroupAction.Basic

open Module LinearMap

namespace Representation

variable {F : Type*} [Field F] {G : Type*} [Group G]

variable {V : Type*} [AddCommGroup V] [Module F V]

section FreeBlock

variable (ρ : Representation F G V) (H : Subgroup G) [Finite ↥H]

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [MulAction ↥H ι]

variable {W : ι → Submodule F V}

namespace FreeBlockAux

/-- The `i`-th block component of `v : V` under the internal direct sum `V = ⨁ᵢ Wᵢ`,
as a linear endomorphism of `V` (it factors through `W i`). -/
private noncomputable def proj (hW : DirectSum.IsInternal W) (i : ι) : V →ₗ[F] V :=
  (W i).subtype ∘ₗ DirectSum.component F ι (fun i => W i) i ∘ₗ
    (LinearEquiv.ofBijective (DirectSum.coeLinearMap W) hW).symm.toLinearMap

omit [Fintype ι] in
private theorem proj_apply (hW : DirectSum.IsInternal W) (i : ι) (v : V) :
    proj hW i v = ((LinearEquiv.ofBijective (DirectSum.coeLinearMap W) hW).symm v i : V) := rfl

omit [Fintype ι] in
private theorem proj_mem (hW : DirectSum.IsInternal W) (i : ι) (v : V) : proj hW i v ∈ W i := by
  rw [proj_apply]; exact ((LinearEquiv.ofBijective (DirectSum.coeLinearMap W) hW).symm v i).2

omit [Fintype ι] in
/-- The component of a vector that already lies in block `W i` is itself in that slot, and
vanishes in the other slots. -/
private theorem proj_of_mem (hW : DirectSum.IsInternal W) {i : ι} {x : V} (hx : x ∈ W i) :
    proj hW i x = x := by
  rw [proj_apply, hW.ofBijective_coeLinearMap_of_mem hx]

omit [Fintype ι] in
private theorem proj_of_mem_ne (hW : DirectSum.IsInternal W) {i j : ι} (hij : i ≠ j) {x : V}
    (hx : x ∈ W i) : proj hW j x = 0 := by
  rw [proj_apply, hW.ofBijective_coeLinearMap_of_mem_ne hij hx, ZeroMemClass.coe_zero]

set_option backward.isDefEq.respectTransparency false in
/-- Reconstruction of a vector from its block components. -/
private theorem sum_proj (hW : DirectSum.IsInternal W) (v : V) : ∑ i, proj hW i v = v := by
  classical
  have h := DirectSum.sum_univ_of ((LinearEquiv.ofBijective (DirectSum.coeLinearMap W) hW).symm v)
  apply_fun DirectSum.coeLinearMap W at h
  rw [map_sum] at h
  simp only [DirectSum.coeLinearMap_of] at h
  rw [LinearEquiv.apply_ofBijective_symm_apply] at h
  simp only [proj_apply]
  exact h

omit [Finite ↥H] in
/-- Membership in the `H`-invariants, restated through the coercion `↥H → G`. -/
private theorem mem_invariants_iff (v : V) :
    v ∈ Representation.invariants (ρ.comp H.subtype) ↔ ∀ h : ↥H, ρ (h : G) v = v := by
  rw [Representation.mem_invariants]; rfl

variable {ρ H}

omit [Finite ↥H] in
omit [Fintype ι] in
/-- **Component-transport law.** If `v` is `H`-invariant, its `(h • i)`-component is the image
under `ρ h` of its `i`-component. -/
private theorem proj_smul_of_mem_invariants [Finite ι] (hW : DirectSum.IsInternal W)
    (hperm : ∀ (h : ↥H) (i : ι), (W i).map (ρ (h : G)) = W (h • i))
    {v : V} (hv : v ∈ Representation.invariants (ρ.comp H.subtype)) (h : ↥H) (i : ι) :
    proj hW (h • i) v = ρ (h : G) (proj hW i v) := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  -- `ρ h v = v`, and applying `ρ h` to the decomposition reshuffles the blocks.
  have hvfix : ρ (h : G) v = v := (mem_invariants_iff ρ H v).1 hv h
  -- The reshuffled decomposition: `v = ∑ j, ρ h (proj hW j v)`, with the `j`-term in block `h•j`.
  have key : ∀ j : ι, ρ (h : G) (proj hW j v) ∈ W (h • j) := by
    intro j
    rw [← hperm h j]
    exact Submodule.mem_map_of_mem (proj_mem hW j v)
  -- The reshuffled decomposition equals `v`.
  have hsum : (∑ j, ρ (h : G) (proj hW j v)) = v := by
    rw [← map_sum, sum_proj hW v, hvfix]
  -- Compute the `(h•i)`-component of `v` two ways.
  have e1 : (proj hW (h • i)) v = (proj hW (h • i)) (∑ j, ρ (h : G) (proj hW j v)) := by
    rw [hsum]
  rw [e1, map_sum]
  -- Only the `j = i` term survives in slot `h • i` (using that `h • ·` is injective).
  rw [Finset.sum_eq_single i]
  · exact proj_of_mem hW (key i)
  · intro j _ hji
    refine proj_of_mem_ne hW ?_ (key j)
    exact fun he => hji ((MulAction.injective h) he)
  · intro hi; exact absurd (Finset.mem_univ i) hi

omit [Finite ↥H] in
omit [Fintype ι] [DecidableEq ι] in
/-- Blocks in the same `H`-orbit have the same dimension: `ρ h` is invertible and maps `W i`
onto `W (h • i)`. -/
private theorem finrank_block_smul [FiniteDimensional F V]
    (hperm : ∀ (h : ↥H) (i : ι), (W i).map (ρ (h : G)) = W (h • i)) (h : ↥H) (i : ι) :
    finrank F (W (h • i)) = finrank F (W i) := by
  rw [← hperm h i]
  exact LinearEquiv.finrank_map_eq (LinearEquiv.ofBijective (ρ (h : G)) (ρ.apply_bijective _)) (W i)

variable (ρ H)

omit [Finite ↥H] in
/-- The **orbit sum** `∑_{h ∈ H} ρ h x` is always `H`-invariant: left-multiplication permutes
the summands. -/
private theorem orbitSum_mem_invariants [Fintype ↥H] (x : V) :
    (∑ h : ↥H, ρ (h : G) x) ∈ Representation.invariants (ρ.comp H.subtype) := by
  rw [mem_invariants_iff]
  intro h'
  rw [map_sum]
  rw [← Function.Bijective.sum_comp (Group.mulLeft_bijective h') (fun h : ↥H => ρ (h : G) x)]
  refine Finset.sum_congr rfl (fun h _ => ?_)
  rw [Subgroup.coe_mul, map_mul, Module.End.mul_apply]

variable {ρ H}

omit [Finite ↥H] in
omit [Fintype ι] [DecidableEq ι] in
/-- For an orbit class `o`, its chosen representative's orbit equals `o.orbit`, so any `i` with the
same class lies in `orbit ↥H o.out`. -/
private theorem mem_orbit_out_of_mk (i : ι) :
    (i : ι) ∈ MulAction.orbit ↥H ((Quotient.mk'' i : MulAction.orbitRel.Quotient ↥H ι).out) := by
  have h1 : i ∈ MulAction.orbitRel.Quotient.orbit
      (Quotient.mk'' i : MulAction.orbitRel.Quotient ↥H ι) :=
    MulAction.orbitRel.Quotient.mem_orbit.2 rfl
  rwa [MulAction.orbitRel.Quotient.orbit_eq_orbit_out _ Quotient.out_eq'] at h1

omit [Finite ↥H] in
omit [Fintype ι] [DecidableEq ι] in
/-- **Free + finite orbit partition.**  The map `(o, h) ↦ h • o.out` is a bijection from
`Ω × H` (with `Ω` the set of `H`-orbits) onto `ι`. -/
private theorem orbitProdEquiv_bijective [Finite ↥H]
    (hfree : ∀ (h : ↥H) (i : ι), h • i = i → h = 1) :
    Function.Bijective
      (fun p : (Σ _ : MulAction.orbitRel.Quotient ↥H ι, ↥H) => p.2 • (p.1.out : ι)) := by
  classical
  constructor
  · rintro ⟨o₁, h₁⟩ ⟨o₂, h₂⟩ he
    simp only at he
    -- The two representatives lie in a common orbit, hence the orbit classes agree.
    have hsame : (o₁.out : ι) ∈ MulAction.orbit ↥H (o₂.out : ι) :=
      MulAction.mem_orbit_iff.2 ⟨h₁⁻¹ * h₂, by rw [mul_smul, ← he, inv_smul_smul]⟩
    have ho : o₁ = o₂ := by
      have h1 : (Quotient.mk'' o₁.out : MulAction.orbitRel.Quotient ↥H ι)
          = Quotient.mk'' o₂.out := by
        rw [Quotient.eq'']; exact (MulAction.orbitRel_apply).2 hsame
      rwa [Quotient.out_eq', Quotient.out_eq'] at h1
    subst ho
    -- Same orbit + free action force the group elements to agree.
    have hh : (h₁⁻¹ * h₂) • (o₁.out : ι) = o₁.out := by rw [mul_smul, ← he, inv_smul_smul]
    have hone := hfree _ _ hh
    rw [inv_mul_eq_one, eq_comm] at hone
    simp [hone]
  · intro i
    -- `i` lies in the orbit of the chosen representative of its own class; pick a witness.
    obtain ⟨h, hh⟩ := MulAction.mem_orbit_iff.1 (mem_orbit_out_of_mk (H := H) i)
    exact ⟨⟨Quotient.mk'' i, h⟩, hh⟩

omit [Finite ↥H] [DecidableEq ι] in
/-- Summing a function over `ι` regroups as a double sum over orbits and group elements. -/
private theorem sum_eq_sum_orbit [Fintype ↥H] [Fintype (MulAction.orbitRel.Quotient ↥H ι)]
    (hfree : ∀ (h : ↥H) (i : ι), h • i = i → h = 1)
    {A : Type*} [AddCommMonoid A] (f : ι → A) :
    ∑ i, f i = ∑ o : MulAction.orbitRel.Quotient ↥H ι, ∑ h : ↥H, f (h • (o.out : ι)) := by
  classical
  rw [← Function.Bijective.sum_comp (orbitProdEquiv_bijective (H := H) hfree) f,
    ← Finset.univ_sigma_univ, Finset.sum_sigma]

omit [Finite ↥H] in
omit [Fintype ι] [DecidableEq ι] in
/-- Two representatives of *distinct* orbit classes can never be carried into one another. -/
private theorem smul_out_ne_out_of_ne {o o' : MulAction.orbitRel.Quotient ↥H ι} (hne : o' ≠ o)
    (h : ↥H) : h • (o.out : ι) ≠ (o'.out : ι) := by
  intro he
  apply hne
  have : (o'.out : ι) ∈ MulAction.orbit ↥H (o.out : ι) := MulAction.mem_orbit_iff.2 ⟨h, he⟩
  have h1 : (Quotient.mk'' o'.out : MulAction.orbitRel.Quotient ↥H ι) = Quotient.mk'' o.out := by
    rw [Quotient.eq'']; exact (MulAction.orbitRel_apply).2 this
  rwa [Quotient.out_eq', Quotient.out_eq'] at h1

omit [Finite ↥H] in
omit [Fintype ι] in
/-- **Per-orbit reduction of the fixed subspace.**  The fixed subspace has dimension equal to the
sum over orbits of one representative block's dimension. -/
private theorem finrank_invariants_eq_sum_orbit [FiniteDimensional F V] [Finite ↥H] [Finite ι]
    [Fintype (MulAction.orbitRel.Quotient ↥H ι)]
    (hW : DirectSum.IsInternal W)
    (hfree : ∀ (h : ↥H) (i : ι), h • i = i → h = 1)
    (hperm : ∀ (h : ↥H) (i : ι), (W i).map (ρ (h : G)) = W (h • i)) :
    finrank F (Representation.invariants (ρ.comp H.subtype))
      = ∑ o : MulAction.orbitRel.Quotient ↥H ι, finrank F (W (o.out : ι)) := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  have : Fintype ↥H := Fintype.ofFinite _
  -- The map `v ↦ (proj o.out v)_o` is a linear iso `Vᴴ ≃ ∏_o W o.out`.
  let β : Representation.invariants (ρ.comp H.subtype) →ₗ[F]
      (∀ o : MulAction.orbitRel.Quotient ↥H ι, ↥(W (o.out : ι))) :=
    LinearMap.pi (fun o =>
      (proj hW (o.out : ι)).codRestrict (W (o.out : ι)) (fun v => proj_mem hW _ v) ∘ₗ
        (Representation.invariants (ρ.comp H.subtype)).subtype)
  have hβ : ∀ (v : Representation.invariants (ρ.comp H.subtype)) (o), (β v o : V)
      = proj hW (o.out : ι) (v : V) := fun v o => rfl
  -- Conclude via the finrank of the product.
  rw [← Module.finrank_pi_fintype (R := F)]
  refine LinearEquiv.finrank_eq (LinearEquiv.ofBijective β ⟨?_, ?_⟩)
  · -- Injective.
    refine (injective_iff_map_eq_zero β).mpr (fun v hv => ?_)
    apply Subtype.ext
    -- Every component `proj o.out v` is zero; transport to all of `ι`, then reconstruct.
    have hzero : ∀ o : MulAction.orbitRel.Quotient ↥H ι, proj hW (o.out : ι) (v : V) = 0 := by
      intro o
      have := congrArg (fun (f : ∀ o, ↥(W (o.out : ι))) => (f o : V)) hv
      simpa [hβ] using this
    have hall : ∀ i : ι, proj hW i (v : V) = 0 := by
      intro i
      obtain ⟨h, hh⟩ := MulAction.mem_orbit_iff.1 (mem_orbit_out_of_mk (H := H) i)
      rw [← hh, proj_smul_of_mem_invariants hW hperm v.2 h _, hzero, map_zero]
    have : (v : V) = 0 := by rw [← sum_proj hW (v : V)]; simp [hall]
    simpa using this
  · -- Surjective.
    intro w
    -- Build the invariant vector by summing each representative's orbit.
    refine ⟨⟨∑ o : MulAction.orbitRel.Quotient ↥H ι, ∑ h : ↥H, ρ (h : G) (w o : V), ?_⟩, ?_⟩
    · -- Invariance: a sum of orbit sums.
      refine Submodule.sum_mem _ (fun o _ => ?_)
      exact orbitSum_mem_invariants ρ H _
    · -- The components recover `w`.
      funext o'
      apply Subtype.ext
      rw [hβ]
      -- `proj o'.out (∑_o ∑_h ρ h (w o)) = w o'`.
      rw [map_sum]
      rw [Finset.sum_eq_single o']
      · rw [map_sum, Finset.sum_eq_single (1 : ↥H)]
        · rw [Subgroup.coe_one, map_one, Module.End.one_apply]
          exact proj_of_mem hW (w o').2
        · intro h _ hne
          have hmem : ρ (h : G) (w o' : V) ∈ W (h • (o'.out : ι)) := by
            rw [← hperm h (o'.out : ι)]; exact Submodule.mem_map_of_mem (w o').2
          refine proj_of_mem_ne hW (j := (o'.out : ι)) ?_ hmem
          intro he; exact hne (hfree h _ he)
        · intro h1; exact absurd (Finset.mem_univ (1 : ↥H)) h1
      · intro o _ hne
        rw [map_sum]
        refine Finset.sum_eq_zero (fun h _ => ?_)
        have hmem : ρ (h : G) (w o : V) ∈ W (h • (o.out : ι)) := by
          rw [← hperm h (o.out : ι)]; exact Submodule.mem_map_of_mem (w o).2
        exact proj_of_mem_ne hW (j := (o'.out : ι))
          (smul_out_ne_out_of_ne (o := o) (o' := o') hne.symm h) hmem
      · intro ho'; exact absurd (Finset.mem_univ o') ho'

end FreeBlockAux

omit [Fintype ι] in
/-- **Free block permutation dimension formula** (BG Theorem 3.10(a) keystone).
If a finite group `H ≤ G` acts via `ρ` on a finite-dimensional `V = ⨁ᵢ Wᵢ` (internal direct sum),
permuting the blocks (`ρ h` maps `Wᵢ` onto `W (h • i)`) **freely** on the index set `ι`, then
`finrank V = |H| · finrank Vᴴ`. -/
theorem finrank_eq_card_mul_finrank_invariants_of_freeBlock
    [Finite ι] [FiniteDimensional F V] (hW : DirectSum.IsInternal W)
    (hfree : ∀ (h : ↥H) (i : ι), h • i = i → h = 1)
    (hperm : ∀ (h : ↥H) (i : ι), (W i).map (ρ (h : G)) = W (h • i)) :
    finrank F V = Nat.card ↥H * finrank F (Representation.invariants (ρ.comp H.subtype)) := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  have : Fintype ↥H := Fintype.ofFinite _
  have : Fintype (MulAction.orbitRel.Quotient ↥H ι) := Fintype.ofFinite _
  -- `finrank V = ∑ i, finrank (W i)` from the internal direct sum.
  have hVsum : finrank F V = ∑ i, finrank F (W i) := by
    rw [← (LinearEquiv.ofBijective (DirectSum.coeLinearMap W) hW).finrank_eq,
      Module.finrank_directSum]
  -- Regroup over orbits and use that blocks in one orbit share a dimension.
  rw [hVsum, FreeBlockAux.sum_eq_sum_orbit hfree (fun i => finrank F (W i))]
  have hblk : ∀ (o : MulAction.orbitRel.Quotient ↥H ι),
      ∑ _h : ↥H, finrank F (W ((_h) • (o.out : ι))) = Nat.card ↥H * finrank F (W (o.out : ι)) := by
    intro o
    rw [Finset.sum_congr rfl (fun h _ => FreeBlockAux.finrank_block_smul hperm h (o.out : ι))]
    rw [Finset.sum_const, Finset.card_univ, Nat.card_eq_fintype_card, smul_eq_mul]
  rw [Finset.sum_congr rfl (fun o _ => hblk o), ← Finset.mul_sum,
    FreeBlockAux.finrank_invariants_eq_sum_orbit hW hfree hperm]

end FreeBlock

end Representation


