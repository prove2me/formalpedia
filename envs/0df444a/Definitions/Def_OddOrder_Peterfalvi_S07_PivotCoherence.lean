-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S07_PivotCoherence
-- name    : OddOrder_Peterfalvi_S07_PivotCoherence
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T06:06:47.999133+00:00
-- url     : https://prove2.me/theorems/30a47173-ce20-40df-8fb5-583eb9155aea
-- title:
--   Peterfalvi §5: pivot coherence (uniform-degree coherence, part 1)
-- statement:
--   Formalizes pivot coherence from Peterfalvi §5 (pp. 17-25), the first part of the norm-general uniform-degree coherence result.
--
--   Main declarations: `pivotCoefficient` (The pivot coefficient functional); `pivotExtension` (The pivot extension); `pivotCoherence` (Pivot coherence); `exists_pivotPartner` (Peterfalvi (5.7), the pivot-partner construction).
--
--   The bundle also proves 11 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S07_PivotCoherence.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S07_PivotCoherence.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S07_Coherence_DifferenceImage
import Definitions.Def_OddOrder_Peterfalvi_S07_Coherence_NormInequalities
import Definitions.Def_OddOrder_Peterfalvi_S07_Coherence_PsiDecomposition
import Definitions.Def_OddOrder_Peterfalvi_S07_Coherence_CoherenceUnion
import Definitions.Def_OddOrder_Peterfalvi_S07_Coherence_FamilyBundleDade

namespace OddOrder.Peterfalvi.S07

open OddOrder.RepresentationTheory

open IntegralCharacterMap

variable {L G : Type*} [Group L] [Group G]

section InnerExpand

variable {H : Type*} [Group H] [Fintype H] [Invertible (Nat.card H : ℂ)]

/-- Sesquilinear expansion of `⟨a•w + x, b•w + y⟩` — the inner product of two
pivot decompositions against the common anchor `w`. -/
theorem inner_smul_add_smul_add (w x y : ClassFunction H ℂ) (a b : ℂ) :
    ClassFunction.inner (a • w + x) (b • w + y)
      = a * (star b * ClassFunction.inner w w) + a * star (ClassFunction.inner y w)
        + star b * ClassFunction.inner x w + ClassFunction.inner x y := by
  simp only [ClassFunction.inner_add_left, ClassFunction.inner_add_right,
    ClassFunction.inner_smul_left, ClassFunction.inner_smul_right]
  rw [inner_conj_symm y w]
  ring

end InnerExpand

section PivotExtension

variable [Fintype L] [Invertible (Nat.card L : ℂ)]

/-- **The pivot coefficient functional** `s(φ) = ∑_{η ∈ S} ⟨φ, η⟩ / ⟨η, η⟩`.  On the lattice
`ℤ[S]` of a pairwise-orthogonal family this recovers the **coefficient sum** (each member has
`s = 1`), the quantity that must vanish on the degree-zero sublattice `ℤ[S, A]`. -/
noncomputable def pivotCoefficient {S : Set (ClassFunction L ℂ)} (hSfin : S.Finite) :
    ClassFunction L ℂ →ₗ[ℤ] ℂ :=
  ∑ η ∈ hSfin.toFinset, (ClassFunction.inner η η)⁻¹ • innerLeftℤ (L := L) η

@[simp] theorem pivotCoefficient_apply {S : Set (ClassFunction L ℂ)} (hSfin : S.Finite)
    (φ : ClassFunction L ℂ) :
    pivotCoefficient (L := L) hSfin φ
      = ∑ η ∈ hSfin.toFinset, (ClassFunction.inner η η)⁻¹ * ClassFunction.inner φ η := by
  simp only [pivotCoefficient, LinearMap.sum_apply, LinearMap.smul_apply, innerLeftℤ_apply,
    smul_eq_mul]

/-- On a member of a pairwise-orthogonal family with nonzero norms, the pivot coefficient is
`1` (only the diagonal term survives). -/
theorem pivotCoefficient_apply_mem {S : Set (ClassFunction L ℂ)} (hSfin : S.Finite)
    (horth : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → ClassFunction.inner a b = 0)
    (hnormS : ∀ a ∈ S, ClassFunction.inner a a ≠ 0)
    {η : ClassFunction L ℂ} (hη : η ∈ S) :
    pivotCoefficient (L := L) hSfin η = 1 := by
  classical
  rw [pivotCoefficient_apply]
  rw [Finset.sum_eq_single η]
  · rw [inv_mul_cancel₀ (hnormS η hη)]
  · intro η' hη' hne
    rw [horth η hη η' (hSfin.mem_toFinset.mp hη') (fun h => hne h.symm), mul_zero]
  · intro h
    exact absurd (hSfin.mem_toFinset.mpr hη) h

/-- **The pivot extension** `ν φ = s(φ) • ζ₁ + τ (φ − s(φ) • η₁)`: replace the pivot component
by `ζ₁` and push the (degree-zero) rest through `τ`. -/
noncomputable def pivotExtension (τ : IntegralCharacterMap L G)
    {S : Set (ClassFunction L ℂ)} (hSfin : S.Finite)
    (η₁ : ClassFunction L ℂ) (ζ₁ : ClassFunction G ℂ) : IntegralCharacterMap L G :=
  (pivotCoefficient (L := L) hSfin).smulRight ζ₁ +
    τ ∘ₗ (LinearMap.id - (pivotCoefficient (L := L) hSfin).smulRight η₁)

@[simp] theorem pivotExtension_apply (τ : IntegralCharacterMap L G)
    {S : Set (ClassFunction L ℂ)} (hSfin : S.Finite)
    (η₁ : ClassFunction L ℂ) (ζ₁ : ClassFunction G ℂ) (φ : ClassFunction L ℂ) :
    pivotExtension (L := L) (G := G) τ hSfin η₁ ζ₁ φ
      = pivotCoefficient (L := L) hSfin φ • ζ₁
        + τ (φ - pivotCoefficient (L := L) hSfin φ • η₁) := by
  simp [pivotExtension, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.sub_apply,
    LinearMap.smulRight_apply, LinearMap.id_apply]

end PivotExtension

section PivotCoherence

variable [Fintype L] [Fintype G]

variable [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]

/-- **Pivot coherence** (Coq `pivot_coherence`, `PFsection5.v:588`, specialized to equal
degrees): a finite pairwise-orthogonal family `S` of equal-degree class functions with nonzero
norms, whose member differences are `A`-supported and mapped to virtual characters, is coherent
as soon as a pivot `η₁ ∈ S` has a partner `ζ₁ ∈ ℤ[Irr G]` with `⟨ζ₁, ζ₁⟩ = ⟨η₁, η₁⟩` and
`⟨τ(η − η₁), ζ₁⟩ = −⟨η₁, η₁⟩` for every other member `η` (`hpivot`).

The coherent extension is `pivotExtension`: `ν φ = s(φ) • ζ₁ + τ(φ − s(φ) • η₁)` with `s` the
pivot coefficient functional.  This is the norm-general engine behind Peterfalvi (5.7)
(`uniform_degree_coherence`): unlike `coherent_of_constant_degree`, the members need not be
irreducible — only pairwise orthogonal with nonzero norms — so it accepts the reducible
certain-type columns `μ_j` of the (9.11) Galois/caseB family (issue 9075). -/
noncomputable def pivotCoherence
    {τ : IntegralCharacterMap L G} {S : Set (ClassFunction L ℂ)} {A : Set L}
    (hSfin : S.Finite)
    {η₁ : ClassFunction L ℂ} (hη₁ : η₁ ∈ S)
    {ζ₁ : ClassFunction G ℂ} (hζZ : ζ₁ ∈ ZIrr G)
    (horth : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → ClassFunction.inner a b = 0)
    (hnormS : ∀ a ∈ S, ClassFunction.inner a a ≠ 0)
    (hnorm : ClassFunction.inner ζ₁ ζ₁ = ClassFunction.inner η₁ η₁)
    (hpivot : ∀ η ∈ S, η ≠ η₁ →
      ClassFunction.inner (τ (η - η₁)) ζ₁ = -ClassFunction.inner η₁ η₁)
    (hiso : ∀ φ ψ : ClassFunction L ℂ, φ ∈ zSupportedSpan (L := L) S A →
      ψ ∈ zSupportedSpan (L := L) S A →
      ClassFunction.inner (τ φ) (τ ψ) = ClassFunction.inner φ ψ)
    (hZdiff : ∀ a ∈ S, ∀ b ∈ S, τ (a - b) ∈ ZIrr G)
    (hdeg : ∀ a ∈ S,
      ((a : ClassFunction L ℂ) : L → ℂ) 1 = ((η₁ : ClassFunction L ℂ) : L → ℂ) 1)
    (hdeg0 : ((η₁ : ClassFunction L ℂ) : L → ℂ) 1 ≠ 0)
    (h1A : (1 : L) ∉ A)
    (hsuppdiff : ∀ a ∈ S, ∀ b ∈ S, ((a - b : ClassFunction L ℂ)).support ⊆ A)
    {η₂ : ClassFunction L ℂ} (hη₂ : η₂ ∈ S) (hη₂ne : η₂ ≠ η₁) :
    IsCoherent τ S A := by
  classical
  -- coefficient value on members
  have hsval : ∀ η ∈ S, pivotCoefficient (L := L) hSfin η = 1 := fun η hη =>
    pivotCoefficient_apply_mem hSfin horth hnormS hη
  -- δ-rearrangements (the defect `δφ = φ − s(φ)•η₁` is additive and `ℤ`-homogeneous)
  have hδadd : ∀ x y : ClassFunction L ℂ,
      x + y - pivotCoefficient (L := L) hSfin (x + y) • η₁
        = (x - pivotCoefficient (L := L) hSfin x • η₁)
          + (y - pivotCoefficient (L := L) hSfin y • η₁) := by
    intro x y
    rw [map_add, add_smul]
    abel
  have hδsmul : ∀ (c : ℤ) (x : ClassFunction L ℂ),
      c • x - pivotCoefficient (L := L) hSfin (c • x) • η₁
        = c • (x - pivotCoefficient (L := L) hSfin x • η₁) := by
    intro c x
    rw [map_smul, smul_sub]
    congr 1
    rw [zsmul_eq_mul, mul_smul, ← Int.cast_smul_eq_zsmul ℂ c
      (pivotCoefficient (L := L) hSfin x • η₁)]
  -- the defect lands in the supported lattice
  have hδmem : ∀ φ ∈ zSpan (L := L) S,
      φ - pivotCoefficient (L := L) hSfin φ • η₁ ∈ zSupportedSpan (L := L) S A := by
    intro φ hφ
    induction hφ using Submodule.span_induction with
    | mem η hη =>
        rw [hsval η hη, one_smul]
        exact ⟨Submodule.sub_mem _ (Submodule.subset_span hη) (Submodule.subset_span hη₁),
          hsuppdiff η hη η₁ hη₁⟩
    | zero =>
        rw [map_zero, zero_smul, sub_zero]
        exact ⟨Submodule.zero_mem _, by rw [ClassFunction.support_zero]; exact Set.empty_subset A⟩
    | add x y hx hy ihx ihy =>
        rw [hδadd x y]
        exact ⟨Submodule.add_mem _ ihx.1 ihy.1,
          (ClassFunction.support_add_subset _ _).trans (Set.union_subset ihx.2 ihy.2)⟩
    | smul c x hx ih =>
        rw [hδsmul c x]
        refine ⟨Submodule.smul_mem _ c ih.1, ?_⟩
        rw [← Int.cast_smul_eq_zsmul ℂ c]
        exact (ClassFunction.support_smul_subset _ _).trans ih.2
  -- the pivot inner product extends `ℤ`-linearly over the defect lattice
  have hτζ : ∀ φ ∈ zSpan (L := L) S,
      ClassFunction.inner (τ (φ - pivotCoefficient (L := L) hSfin φ • η₁)) ζ₁
        = ClassFunction.inner (φ - pivotCoefficient (L := L) hSfin φ • η₁) η₁ := by
    intro φ hφ
    induction hφ using Submodule.span_induction with
    | mem η hη =>
        rw [hsval η hη, one_smul]
        by_cases hne : η = η₁
        · subst hne
          rw [sub_self, map_zero, ClassFunction.inner_zero_left, ClassFunction.inner_zero_left]
        · rw [hpivot η hη hne, ClassFunction.inner_sub_left, horth η hη η₁ hη₁ hne, zero_sub]
    | zero =>
        rw [map_zero, zero_smul, sub_zero, map_zero, ClassFunction.inner_zero_left,
          ClassFunction.inner_zero_left]
    | add x y hx hy ihx ihy =>
        rw [hδadd x y, map_add, ClassFunction.inner_add_left, ClassFunction.inner_add_left,
          ihx, ihy]
    | smul c x hx ih =>
        rw [hδsmul c x, map_smul, ← Int.cast_smul_eq_zsmul ℂ c
          (τ (x - pivotCoefficient (L := L) hSfin x • η₁)),
          ← Int.cast_smul_eq_zsmul ℂ c (x - pivotCoefficient (L := L) hSfin x • η₁),
          ClassFunction.inner_smul_left, ClassFunction.inner_smul_left, ih]
  -- the defect image is a virtual character
  have hZδ : ∀ φ ∈ zSpan (L := L) S,
      τ (φ - pivotCoefficient (L := L) hSfin φ • η₁) ∈ ZIrr G := by
    intro φ hφ
    induction hφ using Submodule.span_induction with
    | mem η hη =>
        rw [hsval η hη, one_smul]
        exact hZdiff η hη η₁ hη₁
    | zero =>
        rw [map_zero, zero_smul, sub_zero, map_zero]
        exact Submodule.zero_mem _
    | add x y hx hy ihx ihy =>
        rw [hδadd x y, map_add]
        exact Submodule.add_mem _ ihx ihy
    | smul c x hx ih =>
        rw [hδsmul c x, map_smul]
        exact Submodule.smul_mem _ c ih
  -- the coefficient is integral on the lattice
  have hsmem : ∀ φ ∈ zSpan (L := L) S,
      ∃ m : ℤ, pivotCoefficient (L := L) hSfin φ = (m : ℂ) := by
    intro φ hφ
    induction hφ using Submodule.span_induction with
    | mem η hη => exact ⟨1, by rw [hsval η hη, Int.cast_one]⟩
    | zero => exact ⟨0, by rw [map_zero, Int.cast_zero]⟩
    | add x y hx hy ihx ihy =>
        obtain ⟨m, hm⟩ := ihx
        obtain ⟨n, hn⟩ := ihy
        exact ⟨m + n, by rw [map_add, hm, hn, Int.cast_add]⟩
    | smul c x hx ih =>
        obtain ⟨m, hm⟩ := ih
        exact ⟨c * m, by rw [map_smul, zsmul_eq_mul, hm, Int.cast_mul]⟩
  -- degrees: `φ(1) = s(φ)·η₁(1)` on the lattice
  have hone : ∀ φ ∈ zSpan (L := L) S,
      ((φ : ClassFunction L ℂ) : L → ℂ) 1
        = pivotCoefficient (L := L) hSfin φ * ((η₁ : ClassFunction L ℂ) : L → ℂ) 1 := by
    intro φ hφ
    induction hφ using Submodule.span_induction with
    | mem η hη => rw [hsval η hη, one_mul]; exact hdeg η hη
    | zero => rw [map_zero, zero_mul]; rfl
    | add x y hx hy ihx ihy =>
        rw [map_add, add_mul, ← ihx, ← ihy]
        rfl
    | smul c x hx ih =>
        have hs : pivotCoefficient (L := L) hSfin (c • x)
            = (c : ℂ) * pivotCoefficient (L := L) hSfin x := by
          rw [map_smul, zsmul_eq_mul]
        rw [hs, ← Int.cast_smul_eq_zsmul ℂ c x, ClassFunction.smul_apply, ih, mul_assoc]
  -- assemble the coherence witness
  refine ⟨⟨η₂ - η₁,
      ⟨Submodule.sub_mem _ (Submodule.subset_span hη₂) (Submodule.subset_span hη₁),
        hsuppdiff η₂ hη₂ η₁ hη₁⟩,
      sub_ne_zero.mpr hη₂ne⟩,
    pivotExtension (L := L) (G := G) τ hSfin η₁ ζ₁, ?_, ?_, ?_⟩
  · -- isometry on `ℤ[S]`
    intro φ ψ hφ hψ
    have hφζ := hτζ φ hφ
    have hψζ := hτζ ψ hψ
    have hδδ := hiso _ _ (hδmem φ hφ) (hδmem ψ hψ)
    have hL : ClassFunction.inner
        (pivotExtension (L := L) (G := G) τ hSfin η₁ ζ₁ φ)
        (pivotExtension (L := L) (G := G) τ hSfin η₁ ζ₁ ψ)
        = pivotCoefficient (L := L) hSfin φ * (star (pivotCoefficient (L := L) hSfin ψ)
            * ClassFunction.inner η₁ η₁)
          + pivotCoefficient (L := L) hSfin φ
            * star (ClassFunction.inner (ψ - pivotCoefficient (L := L) hSfin ψ • η₁) η₁)
          + star (pivotCoefficient (L := L) hSfin ψ)
            * ClassFunction.inner (φ - pivotCoefficient (L := L) hSfin φ • η₁) η₁
          + ClassFunction.inner (φ - pivotCoefficient (L := L) hSfin φ • η₁)
              (ψ - pivotCoefficient (L := L) hSfin ψ • η₁) := by
      rw [pivotExtension_apply, pivotExtension_apply, inner_smul_add_smul_add, hnorm,
        hφζ, hψζ, hδδ]
    have hR := inner_smul_add_smul_add (H := L) η₁
      (φ - pivotCoefficient (L := L) hSfin φ • η₁)
      (ψ - pivotCoefficient (L := L) hSfin ψ • η₁)
      (pivotCoefficient (L := L) hSfin φ) (pivotCoefficient (L := L) hSfin ψ)
    rw [show pivotCoefficient (L := L) hSfin φ • η₁
          + (φ - pivotCoefficient (L := L) hSfin φ • η₁) = φ by abel,
      show pivotCoefficient (L := L) hSfin ψ • η₁
          + (ψ - pivotCoefficient (L := L) hSfin ψ • η₁) = ψ by abel] at hR
    exact hL.trans hR.symm
  · -- agreement with `τ` on the supported lattice
    intro φ hφ
    obtain ⟨hφspan, hφsupp⟩ := hφ
    have hφ1 : ((φ : ClassFunction L ℂ) : L → ℂ) 1 = 0 := by
      by_contra h
      exact h1A (hφsupp h)
    have hs0 : pivotCoefficient (L := L) hSfin φ = 0 := by
      have := hone φ hφspan
      rw [hφ1] at this
      exact (mul_eq_zero.mp this.symm).resolve_right hdeg0
    rw [pivotExtension_apply, hs0, zero_smul, zero_smul, sub_zero, zero_add]
  · -- integrality on the lattice
    intro φ hφ
    rw [pivotExtension_apply]
    refine Submodule.add_mem _ ?_ (hZδ φ hφ)
    obtain ⟨m, hm⟩ := hsmem φ hφ
    rw [hm, Int.cast_smul_eq_zsmul ℂ m ζ₁]
    exact Submodule.smul_mem _ m hζZ

end PivotCoherence

section PivotPartner

variable [Fintype L] [Fintype G]

variable [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]

/-- Bilinear extension of pointwise orthogonality to `ℤ`-spans (both slots). -/
theorem inner_zSpan_zSpan_eq_zero {H : Type*} [Group H] [Fintype H]
    [Invertible (Nat.card H : ℂ)] {T T' : Set (ClassFunction H ℂ)}
    (h : ∀ x ∈ T, ∀ y ∈ T', ClassFunction.inner x y = 0)
    {φ ψ : ClassFunction H ℂ} (hφ : φ ∈ zSpan (L := H) T) (hψ : ψ ∈ zSpan (L := H) T') :
    ClassFunction.inner φ ψ = 0 := by
  induction hφ using Submodule.span_induction with
  | mem x hx =>
      induction hψ using Submodule.span_induction with
      | mem y hy => exact h x hx y hy
      | zero => exact ClassFunction.inner_zero_right x
      | add y z _ _ ihy ihz => rw [ClassFunction.inner_add_right, ihy, ihz, add_zero]
      | smul c y _ ih =>
          rw [← Int.cast_smul_eq_zsmul ℂ c y, ClassFunction.inner_smul_right, ih, mul_zero]
  | zero => exact ClassFunction.inner_zero_left ψ
  | add x y _ _ ihx ihy => rw [ClassFunction.inner_add_left, ihx, ihy, add_zero]
  | smul c x _ ih =>
      rw [← Int.cast_smul_eq_zsmul ℂ c x, ClassFunction.inner_smul_left, ih, mul_zero]

/-- The `X`-side of a `CharacterPsiDecomposition` lies in the `ℤ`-span of `R(χ)`. -/
theorem CharacterPsiDecomposition.X_mem_zSpan {τ : IntegralCharacterMap L G}
    {χ ψ : ClassFunction L ℂ} (D : CharacterPsiDecomposition (L := L) (G := G) τ χ ψ) :
    D.X ∈ zSpan (L := G) (↑D.imageFamily.imageSet : Set (ClassFunction G ℂ)) := by
  rw [D.X_eq]
  exact Submodule.sum_mem _ fun α hα => by
    rw [Int.cast_smul_eq_zsmul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Finset.mem_coe.mpr hα))

/-- Self inner products are (complex casts of) their real parts. -/
theorem inner_self_eq_re_cast {H : Type*} [Group H] [Fintype H]
    [Invertible (Nat.card H : ℂ)] (φ : ClassFunction H ℂ) :
    ((ClassFunction.inner φ φ).re : ℂ) = ClassFunction.inner φ φ := by
  rw [inner_self_eq_realCast, Complex.ofReal_re]

/-- **Peterfalvi (5.7), the `haveX` step** (Coq `PFsection5.v:1268-1297`): for a member `ξ`
distinct from the pivot `η₁` and its conjugate, there is `X` with

* the (5.4.b) shape: `X = ∑_{α ∈ E} α` for some `E ⊆ R(η₁)` with `|E| = ⟨η₁, η₁⟩`;
* the residual containment `X − τ(η₁ − ξ) ∈ ℤ[R(ξ)]`;
* the pivot inner product `⟨X, τ(η₁ − ξ)⟩ = ⟨η₁, η₁⟩`.

The proof runs the two projection decompositions `D₁ = (η₁, ξ)` against `R(η₁)` and
`D₂ = (ξ, η₁)` against `R(ξ)` and squeezes: `⟨ξ⟩ ≥ ‖Y₁‖²` ((5.6.2) opening on `D₁`),
`‖Y₁‖² ≥ ‖X₂‖²` (`Y₁ − X₂ ⊥ X₂` from the cross-orthogonality `R(η₁) ⊥ R(ξ)`), and
`‖X₂‖² ≥ ⟨ξ⟩` ((5.4.a) on `D₂`) — so all are equal, `Y₁ = X₂` lands in `ℤ[R(ξ)]`, and
(5.4.b) on `D₁` delivers the subset-sum shape. -/
theorem exists_pivotPartner_spec {τ : IntegralCharacterMap L G}
    {η₁ ξ : ClassFunction L ℂ}
    (R₁ : OrthonormalCharacterImageFamily (L := L) (G := G) τ η₁)
    (Rξ : OrthonormalCharacterImageFamily (L := L) (G := G) τ ξ)
    (hcross : R₁.Orthogonal Rξ)
    (hiso1 : ∀ φ ζ : ClassFunction L ℂ,
      φ ∈ zSpan (L := L) {η₁ - η₁.conj, η₁ - ξ} → ζ ∈ zSpan (L := L) {η₁ - η₁.conj, η₁ - ξ} →
      ClassFunction.inner (τ φ) (τ ζ) = ClassFunction.inner φ ζ)
    (hiso2 : ∀ φ ζ : ClassFunction L ℂ,
      φ ∈ zSpan (L := L) {ξ - ξ.conj, ξ - η₁} → ζ ∈ zSpan (L := L) {ξ - ξ.conj, ξ - η₁} →
      ClassFunction.inner (τ φ) (τ ζ) = ClassFunction.inner φ ζ)
    (hZ1 : τ (η₁ - ξ) ∈ ZIrr G) (hZ2 : τ (ξ - η₁) ∈ ZIrr G)
    (h12 : ClassFunction.inner η₁ ξ = 0) (h1c2 : ClassFunction.inner η₁.conj ξ = 0)
    (h11c : ClassFunction.inner η₁ η₁.conj = 0)
    (h21 : ClassFunction.inner ξ η₁ = 0) (h2c1 : ClassFunction.inner ξ.conj η₁ = 0)
    (h22c : ClassFunction.inner ξ ξ.conj = 0) :
    ∃ X : ClassFunction G ℂ,
      (∃ E ⊆ R₁.imageSet, X = ∑ α ∈ E, α ∧ (E.card : ℂ) = ClassFunction.inner η₁ η₁) ∧
      X - τ (η₁ - ξ) ∈ zSpan (L := G) (↑Rξ.imageSet : Set (ClassFunction G ℂ)) ∧
      ClassFunction.inner X (τ (η₁ - ξ)) = ClassFunction.inner η₁ η₁ := by
  classical
  -- the two projection decompositions
  let D₁ : CharacterPsiDecomposition (L := L) (G := G) τ η₁ ξ :=
    CharacterPsiDecomposition.ofProjection R₁ τ hiso1 rfl hZ1 h12 h1c2 h11c
  let D₂ : CharacterPsiDecomposition (L := L) (G := G) τ ξ η₁ :=
    CharacterPsiDecomposition.ofProjection Rξ τ hiso2 rfl hZ2 h21 h2c1 h22c
  have h1 : τ (η₁ - ξ) = D₁.X - D₁.Y := D₁.tau1_image
  have h2 : τ (ξ - η₁) = D₂.X - D₂.Y := D₂.tau1_image
  -- the shared image relation `Y₁ = X₂ − Y₂ + X₁` (from `τ(ξ − η₁) = −τ(η₁ − ξ)`)
  have hY₁eq : D₁.Y = D₂.X - D₂.Y + D₁.X := by
    have hneg : D₂.X - D₂.Y = -(D₁.X - D₁.Y) := by
      rw [← h1, ← h2, ← map_neg, neg_sub]
    rw [hneg]
    abel
  -- span memberships and the orthogonality bookkeeping
  have hX₁span : D₁.X ∈ zSpan (L := G) (↑R₁.imageSet : Set (ClassFunction G ℂ)) :=
    D₁.X_mem_zSpan
  have hX₂span : D₂.X ∈ zSpan (L := G) (↑Rξ.imageSet : Set (ClassFunction G ℂ)) :=
    D₂.X_mem_zSpan
  have hX₁X₂ : ClassFunction.inner D₁.X D₂.X = 0 :=
    inner_zSpan_zSpan_eq_zero
      (fun α hα β hβ => hcross α (Finset.mem_coe.mp hα) β (Finset.mem_coe.mp hβ))
      hX₁span hX₂span
  have hY₂X₂ : ClassFunction.inner D₂.Y D₂.X = 0 := by
    rw [inner_conj_symm D₂.X D₂.Y, D₂.inner_X_Y, star_zero]
  -- `⟨Y₁, X₂⟩ = ⟨X₂ − Y₂ + X₁, X₂⟩ = ⟨X₂, X₂⟩ − ⟨Y₂, X₂⟩ + ⟨X₁, X₂⟩ = ⟨X₂, X₂⟩ = ⟨X₂, Y₁⟩`
  have hY₁X₂ : ClassFunction.inner D₁.Y D₂.X = ClassFunction.inner D₂.X D₂.X := by
    rw [hY₁eq, ClassFunction.inner_add_left, ClassFunction.inner_sub_left, hY₂X₂, hX₁X₂,
      sub_zero, add_zero]
  have hX₂Y₁ : ClassFunction.inner D₂.X D₁.Y = ClassFunction.inner D₂.X D₂.X := by
    rw [inner_conj_symm D₁.Y D₂.X, hY₁X₂]
    exact (inner_conj_symm D₂.X D₂.X).symm
  -- hence `‖Y₁ − X₂‖² = ‖Y₁‖² − ‖X₂‖²`
  have hdiff_re : (ClassFunction.inner (D₁.Y - D₂.X) (D₁.Y - D₂.X)).re
      = (ClassFunction.inner D₁.Y D₁.Y).re - (ClassFunction.inner D₂.X D₂.X).re := by
    have hdiff : ClassFunction.inner (D₁.Y - D₂.X) (D₁.Y - D₂.X)
        = ClassFunction.inner D₁.Y D₁.Y - ClassFunction.inner D₂.X D₂.X := by
      rw [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
        ClassFunction.inner_sub_right, hY₁X₂, hX₂Y₁]
      ring
    rw [hdiff, Complex.sub_re]
  -- the norm squeeze `‖Y₁‖² ≤ ‖ξ‖² ≤ ‖X₂‖² ≤ ‖Y₁‖²`
  have hchain1 : (ClassFunction.inner D₁.Y D₁.Y).re ≤ (ClassFunction.inner ξ ξ).re :=
    D₁.inner_self_Y_re_le_inner_self_psi
  have hchain2 : (ClassFunction.inner ξ ξ).re ≤ (ClassFunction.inner D₂.X D₂.X).re :=
    D₂.inner_self_chi_re_le_inner_self_X
  have hchain3 : (ClassFunction.inner D₂.X D₂.X).re
      ≤ (ClassFunction.inner D₁.Y D₁.Y).re := by
    have hnn := inner_self_re_nonneg (D₁.Y - D₂.X)
    linarith
  -- equality throughout, so the residual `Y₁` *is* `X₂ ∈ ℤ[R(ξ)]`
  have hY₁X₂eq : D₁.Y = D₂.X := by
    have h0 : D₁.Y - D₂.X = 0 := by
      apply eq_zero_of_inner_self_re_eq_zero
      linarith
    exact sub_eq_zero.mp h0
  -- (5.4.b) on `D₁` delivers the subset-sum shape and the norm equality
  obtain ⟨hηX, -, E, hEsub, hXsum, hEcard⟩ :=
    D₁.norm_eq_and_X_eq_sum_of_norm_Y_ge (by linarith)
  have hX₁norm : ClassFunction.inner D₁.X D₁.X = ClassFunction.inner η₁ η₁ := by
    rw [← inner_self_eq_re_cast D₁.X, ← inner_self_eq_re_cast η₁, hηX]
  refine ⟨D₁.X, ⟨E, hEsub, hXsum, hEcard⟩, ?_, ?_⟩
  · -- `X − τ(η₁ − ξ) = Y₁ = X₂ ∈ ℤ[R(ξ)]`
    have hXd : D₁.X - τ (η₁ - ξ) = D₂.X := by
      rw [h1, hY₁X₂eq]
      abel
    rw [hXd]
    exact hX₂span
  · -- `⟨X, τ(η₁ − ξ)⟩ = ⟨X, X⟩ − ⟨X, Y₁⟩ = ‖X‖² = ⟨η₁, η₁⟩`
    rw [h1, ClassFunction.inner_sub_right, D₁.inner_X_Y, sub_zero, hX₁norm]

/-- `ℤ`-spans of subsets of the supported lattice stay in the supported lattice: the
membership predicate of `zSupportedSpan` (span membership + `A`-support) is closed under the
`ℤ`-module operations. -/
theorem mem_zSupportedSpan_of_mem_zSpan {H : Type*} [Group H]
    {S T : Set (ClassFunction H ℂ)} {A : Set H}
    (hT : T ⊆ zSupportedSpan (L := H) S A)
    {φ : ClassFunction H ℂ} (hφ : φ ∈ zSpan (L := H) T) :
    φ ∈ zSupportedSpan (L := H) S A := by
  induction hφ using Submodule.span_induction with
  | mem x hx => exact hT hx
  | zero =>
      exact ⟨Submodule.zero_mem _, by rw [ClassFunction.support_zero]; exact Set.empty_subset A⟩
  | add x y _ _ ihx ihy =>
      exact ⟨Submodule.add_mem _ ihx.1 ihy.1,
        (ClassFunction.support_add_subset _ _).trans (Set.union_subset ihx.2 ihy.2)⟩
  | smul c x _ ih =>
      refine ⟨Submodule.smul_mem _ c ih.1, ?_⟩
      rw [← Int.cast_smul_eq_zsmul ℂ c]
      exact (ClassFunction.support_smul_subset _ _).trans ih.2

open scoped Classical in
/-- **Peterfalvi (5.7), the pivot-partner construction** (Coq `uniform_degree_coherence`,
`PFsection5.v:1265-1330`): under the norm-general subcoherence data — per-member orthonormal
`R`-families (5.2.d), their cross-orthogonality (5.2.e), the `A`-supported lattice isometry
(5.2.b), pairwise orthogonality, conjugate closure, no real members — every member `χ₁ ∈ S`
with genuine-character norm (`⟨χ₁, χ₁⟩ ∈ ℕ`) has a **pivot partner** `ζ₁ ∈ ℤ[Irr G]` with

* `⟨ζ₁, ζ₁⟩ = ⟨χ₁, χ₁⟩`, and
* `⟨τ(η − χ₁), ζ₁⟩ = −⟨χ₁, χ₁⟩` for every other member `η ∈ S`

— exactly the inputs `hζZ`/`hnorm`/`hpivot` of `pivotCoherence`.

The partner is the common `X` of the `haveX` runs (`exists_pivotPartner_spec`): fixing an
anchor `ξ₁ ∈ S ∖ {χ₁, χ̄₁}` (if none exists, `S ⊆ {χ₁, χ̄₁}` is the degenerate case and any
`⟨χ₁,χ₁⟩`-element subset of `R(χ₁)` works, since `|R(χ₁)| = 2⟨χ₁,χ₁⟩`), the member cases are

* `η = χ̄₁`: automatic for any `R(χ₁)`-subset-sum, from `(χ₁ − χ̄₁)^τ = ∑_{R(χ₁)} α`;
* `η = ξ₁`: the `haveX` inner product, conjugated;
* `η = ξ̄₁`: split `τ(χ₁ − ξ̄₁) = τ(χ₁ − ξ₁) + ∑_{R(ξ₁)} β` by (5.2.d) at `ξ₁` and use
  `X ⊥ R(ξ₁)`;
* otherwise: `X = X_η` (`haveX` at `η` gives the same `X`: `⟨X, X_η⟩ = ⟨χ₁,χ₁⟩` by the residual
  containments and cross-orthogonalities, so `‖X − X_η‖² = 0`). -/
theorem exists_pivotPartner {τ : IntegralCharacterMap L G}
    {S : Set (ClassFunction L ℂ)} {A : Set L}
    {χ₁ : ClassFunction L ℂ} (hχ₁ : χ₁ ∈ S)
    (R : ∀ η ∈ S, OrthonormalCharacterImageFamily (L := L) (G := G) τ η)
    (horth : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → ClassFunction.inner a b = 0)
    (hconj : ∀ a ∈ S, a.conj ∈ S)
    (hnr : ∀ a ∈ S, a ≠ a.conj)
    (hN : ∃ n : ℕ, ClassFunction.inner χ₁ χ₁ = n)
    (hiso : ∀ ⦃φ ψ : ClassFunction L ℂ⦄, φ ∈ zSupportedSpan (L := L) S A →
      ψ ∈ zSupportedSpan (L := L) S A →
      ClassFunction.inner (τ φ) (τ ψ) = ClassFunction.inner φ ψ)
    (hZdiff : ∀ a ∈ S, ∀ b ∈ S, τ (a - b) ∈ ZIrr G)
    (hsuppdiff : ∀ a ∈ S, ∀ b ∈ S, ((a - b : ClassFunction L ℂ)).support ⊆ A)
    (hRorth : ∀ ⦃φ ξ : ClassFunction L ℂ⦄ (hφ : φ ∈ S) (hξ : ξ ∈ S),
      ClassFunction.inner φ ξ = 0 → ClassFunction.inner φ ξ.conj = 0 →
      (R φ hφ).Orthogonal (R ξ hξ)) :
    ∃ ζ₁ ∈ ZIrr G,
      ClassFunction.inner ζ₁ ζ₁ = ClassFunction.inner χ₁ χ₁ ∧
      ∀ η ∈ S, η ≠ χ₁ →
        ClassFunction.inner (τ (η - χ₁)) ζ₁ = -ClassFunction.inner χ₁ χ₁ := by
  classical
  obtain ⟨N, hNval⟩ := hN
  let R₁ := R χ₁ hχ₁
  have hχ₂ : χ₁.conj ∈ S := hconj χ₁ hχ₁
  have hne12 : χ₁ ≠ χ₁.conj := hnr χ₁ hχ₁
  have h11c : ClassFunction.inner χ₁ χ₁.conj = 0 := horth _ hχ₁ _ hχ₂ hne12
  have h1c1 : ClassFunction.inner χ₁.conj χ₁ = 0 := horth _ hχ₂ _ hχ₁ (Ne.symm hne12)
  -- member differences live in the supported lattice
  have hdmem : ∀ a ∈ S, ∀ b ∈ S,
      (a - b : ClassFunction L ℂ) ∈ zSupportedSpan (L := L) S A := fun a ha b hb =>
    ⟨Submodule.sub_mem _ (Submodule.subset_span ha) (Submodule.subset_span hb),
      hsuppdiff a ha b hb⟩
  -- the lattice isometry restricted to member-difference pair spans
  have hisopair : ∀ ⦃a b c : ClassFunction L ℂ⦄, a ∈ S → b ∈ S → c ∈ S →
      ∀ φ ζ : ClassFunction L ℂ,
        φ ∈ zSpan (L := L) {a - b, a - c} → ζ ∈ zSpan (L := L) {a - b, a - c} →
        ClassFunction.inner (τ φ) (τ ζ) = ClassFunction.inner φ ζ := by
    intro a b c ha hb hc φ ζ hφ hζ
    have hsub : ({a - b, a - c} : Set (ClassFunction L ℂ)) ⊆
        zSupportedSpan (L := L) S A := by
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact hdmem a ha b hb
      · exact hdmem a ha c hc
    exact hiso (mem_zSupportedSpan_of_mem_zSpan hsub hφ)
      (mem_zSupportedSpan_of_mem_zSpan hsub hζ)
  -- the `haveX` applicator for a member `ξ ∉ {χ₁, χ̄₁}`
  have haveX : ∀ ⦃ξ : ClassFunction L ℂ⦄ (hξ : ξ ∈ S), ξ ≠ χ₁ → ξ ≠ χ₁.conj →
      ∃ X : ClassFunction G ℂ,
        (∃ E ⊆ R₁.imageSet, X = ∑ α ∈ E, α ∧
          (E.card : ℂ) = ClassFunction.inner χ₁ χ₁) ∧
        X - τ (χ₁ - ξ) ∈ zSpan (L := G) (↑(R ξ hξ).imageSet : Set (ClassFunction G ℂ)) ∧
        ClassFunction.inner X (τ (χ₁ - ξ)) = ClassFunction.inner χ₁ χ₁ := by
    intro ξ hξ hξ1 hξ2
    have hξc : ξ.conj ∈ S := hconj ξ hξ
    have hξcne1 : ξ.conj ≠ χ₁ := fun h => hξ2 (by rw [← h, ClassFunction.conj_conj])
    exact exists_pivotPartner_spec R₁ (R ξ hξ)
      (hRorth hχ₁ hξ (horth _ hχ₁ _ hξ (Ne.symm hξ1)) (horth _ hχ₁ _ hξc (Ne.symm hξcne1)))
      (hisopair hχ₁ hχ₂ hξ) (hisopair hξ hξc hχ₁)
      (hZdiff _ hχ₁ _ hξ) (hZdiff _ hξ _ hχ₁)
      (horth _ hχ₁ _ hξ (Ne.symm hξ1)) (horth _ hχ₂ _ hξ (fun h => hξ2 h.symm))
      h11c
      (horth _ hξ _ hχ₁ hξ1) (horth _ hξc _ hχ₁ hξcne1)
      (horth _ hξ _ hξc (hnr ξ hξ))
  by_cases hdegen : ∃ ξ ∈ S, ξ ≠ χ₁ ∧ ξ ≠ χ₁.conj
  case neg =>
    -- degenerate case `S ⊆ {χ₁, χ̄₁}`: any `N`-element subset of `R(χ₁)` works
    -- `‖χ̄₁‖² = ‖χ₁‖²`
    have hconjnorm : ClassFunction.inner χ₁.conj χ₁.conj = ClassFunction.inner χ₁ χ₁ := by
      rw [inner_conj_conj, hNval, star_natCast]
    -- `|R(χ₁)| = 2N`, via the isometry on `χ₁ − χ̄₁` and (5.2.d)
    have hcard : R₁.imageSet.card = 2 * N := by
      have h1 : ClassFunction.inner (τ (χ₁ - χ₁.conj)) (τ (χ₁ - χ₁.conj))
          = ClassFunction.inner (χ₁ - χ₁.conj) (χ₁ - χ₁.conj) :=
        hiso (hdmem _ hχ₁ _ hχ₂) (hdmem _ hχ₁ _ hχ₂)
      rw [R₁.image_eq,
        inner_sum_sum_of_orthonormal R₁.orthonormal (Finset.Subset.refl _)
          (Finset.Subset.refl _), Finset.inter_self,
        ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
        ClassFunction.inner_sub_right, h11c, h1c1, hconjnorm, hNval] at h1
      have h2 : ((R₁.imageSet.card : ℕ) : ℂ) = ((2 * N : ℕ) : ℂ) := by
        rw [h1]; push_cast; ring
      exact_mod_cast h2
    obtain ⟨E, hEsub, hEcard⟩ :=
      Finset.exists_subset_card_eq (s := R₁.imageSet) (n := N) (by rw [hcard]; omega)
    refine ⟨∑ α ∈ E, α, ?_, ?_, ?_⟩
    · exact Submodule.sum_mem _ fun α hα => R₁.mem_ZIrr α (hEsub hα)
    · rw [inner_sum_sum_of_orthonormal R₁.orthonormal hEsub hEsub, Finset.inter_self,
        hEcard, hNval]
    · intro η hη hηne
      have hηc : η = χ₁.conj := by
        by_contra h
        exact hdegen ⟨η, hη, hηne, h⟩
      subst hηc
      have himg2 : τ (χ₁.conj - χ₁) = -∑ α ∈ R₁.imageSet, α := by
        rw [← R₁.image_eq, ← map_neg, neg_sub]
      rw [himg2, ClassFunction.inner_neg_left,
        inner_sum_sum_of_orthonormal R₁.orthonormal (Finset.Subset.refl _) hEsub,
        Finset.inter_eq_right.mpr hEsub, hEcard, hNval]
  case pos =>
    -- an anchor `ξ₁ ∈ S ∖ {χ₁, χ̄₁}` exists; its `haveX` output is the partner
    obtain ⟨ξ₁, hξ₁S, hξ₁ne1, hξ₁ne2⟩ := hdegen
    obtain ⟨X, ⟨E, hEsub, hXsum, hEcard⟩, hXres, hXD⟩ := haveX hξ₁S hξ₁ne1 hξ₁ne2
    have hXnorm : ClassFunction.inner X X = ClassFunction.inner χ₁ χ₁ := by
      rw [hXsum, inner_sum_sum_of_orthonormal R₁.orthonormal hEsub hEsub,
        Finset.inter_self, hEcard]
    have hXZ : X ∈ ZIrr G := by
      rw [hXsum]
      exact Submodule.sum_mem _ fun α hα => R₁.mem_ZIrr α (hEsub hα)
    have hXspan : X ∈ zSpan (L := G) (↑R₁.imageSet : Set (ClassFunction G ℂ)) := by
      rw [hXsum]
      exact Submodule.sum_mem _ fun α hα =>
        Submodule.subset_span (Finset.mem_coe.mpr (hEsub hα))
    -- (5.2.e) instances at the anchor
    have horthξ₁χ₁ : (R ξ₁ hξ₁S).Orthogonal R₁ :=
      hRorth hξ₁S hχ₁ (horth _ hξ₁S _ hχ₁ hξ₁ne1) (horth _ hξ₁S _ hχ₂ hξ₁ne2)
    refine ⟨X, hXZ, hXnorm, ?_⟩
    intro η hη hηne
    by_cases hηc : η = χ₁.conj
    · -- `η = χ̄₁`: `⟨τ(χ̄₁ − χ₁), X⟩ = −⟨∑_{R(χ₁)} α, ∑_E α⟩ = −|E| = −⟨χ₁,χ₁⟩`
      subst hηc
      have himg2 : τ (χ₁.conj - χ₁) = -∑ α ∈ R₁.imageSet, α := by
        rw [← R₁.image_eq, ← map_neg, neg_sub]
      rw [himg2, ClassFunction.inner_neg_left, hXsum,
        inner_sum_sum_of_orthonormal R₁.orthonormal (Finset.Subset.refl _) hEsub,
        Finset.inter_eq_right.mpr hEsub, hEcard]
    · by_cases hηξ : η = ξ₁
      · -- `η = ξ₁`: conjugate the `haveX` inner product
        subst hηξ
        have hneg : τ (η - χ₁) = -τ (χ₁ - η) := by rw [← map_neg, neg_sub]
        rw [hneg, ClassFunction.inner_neg_left, inner_conj_symm X (τ (χ₁ - η)), hXD,
          hNval, star_natCast]
      · by_cases hηξc : η = ξ₁.conj
        · -- `η = ξ̄₁`: split `τ(χ₁ − ξ̄₁) = τ(χ₁ − ξ₁) + ∑_{R(ξ₁)} β`, use `X ⊥ R(ξ₁)`
          subst hηξc
          have himgsplit : τ (χ₁ - ξ₁.conj)
              = τ (χ₁ - ξ₁) + ∑ β ∈ (R ξ₁ hξ₁S).imageSet, β := by
            rw [← (R ξ₁ hξ₁S).image_eq, ← map_add]
            congr 1
            abel
          have h0 : ClassFunction.inner (∑ β ∈ (R ξ₁ hξ₁S).imageSet, β) X = 0 := by
            rw [hXsum, inner_sum_left]
            refine Finset.sum_eq_zero fun β hβ => ?_
            rw [inner_sum_right]
            exact Finset.sum_eq_zero fun α hα => horthξ₁χ₁ β hβ α (hEsub hα)
          have hneg : τ (ξ₁.conj - χ₁) = -τ (χ₁ - ξ₁.conj) := by rw [← map_neg, neg_sub]
          rw [hneg, ClassFunction.inner_neg_left, himgsplit, ClassFunction.inner_add_left,
            h0, add_zero, inner_conj_symm X (τ (χ₁ - ξ₁)), hXD, hNval, star_natCast]
        · -- generic `η`: the common-`X` argument — `haveX` at `η` returns the same `X`
          obtain ⟨X', ⟨E', hE'sub, hX'sum, hE'card⟩, hX'res, hX'D⟩ := haveX hη hηne hηc
          have hX'norm : ClassFunction.inner X' X' = ClassFunction.inner χ₁ χ₁ := by
            rw [hX'sum, inner_sum_sum_of_orthonormal R₁.orthonormal hE'sub hE'sub,
              Finset.inter_self, hE'card]
          have hX'span : X' ∈ zSpan (L := G) (↑R₁.imageSet : Set (ClassFunction G ℂ)) := by
            rw [hX'sum]
            exact Submodule.sum_mem _ fun α hα =>
              Submodule.subset_span (Finset.mem_coe.mpr (hE'sub hα))
          -- (5.2.e) instances at `η`
          have hηconjS : η.conj ∈ S := hconj η hη
          have horthR₁η : R₁.Orthogonal (R η hη) :=
            hRorth hχ₁ hη (horth _ hχ₁ _ hη (Ne.symm hηne))
              (horth _ hχ₁ _ hηconjS
                (fun h => hηc (by rw [h, ClassFunction.conj_conj])))
          have horthξ₁η : (R ξ₁ hξ₁S).Orthogonal (R η hη) :=
            hRorth hξ₁S hη (horth _ hξ₁S _ hη (fun h => hηξ h.symm))
              (horth _ hξ₁S _ hηconjS
                (fun h => hηξc (by rw [h, ClassFunction.conj_conj])))
          -- orthogonality bookkeeping between the two residuals and the two `X`s
          have z1 : ClassFunction.inner (X - τ (χ₁ - ξ₁)) X' = 0 :=
            inner_zSpan_zSpan_eq_zero
              (fun a ha b hb =>
                horthξ₁χ₁ a (Finset.mem_coe.mp ha) b (Finset.mem_coe.mp hb))
              hXres hX'span
          have z2 : ClassFunction.inner (X - τ (χ₁ - ξ₁)) (X' - τ (χ₁ - η)) = 0 :=
            inner_zSpan_zSpan_eq_zero
              (fun a ha b hb =>
                horthξ₁η a (Finset.mem_coe.mp ha) b (Finset.mem_coe.mp hb))
              hXres hX'res
          have z3 : ClassFunction.inner X (X' - τ (χ₁ - η)) = 0 :=
            inner_zSpan_zSpan_eq_zero
              (fun a ha b hb =>
                horthR₁η a (Finset.mem_coe.mp ha) b (Finset.mem_coe.mp hb))
              hXspan hX'res
          -- the isometry value `⟨τ(χ₁ − ξ₁), τ(χ₁ − η)⟩ = ⟨χ₁, χ₁⟩`
          have hDD : ClassFunction.inner (τ (χ₁ - ξ₁)) (τ (χ₁ - η))
              = ClassFunction.inner χ₁ χ₁ := by
            rw [hiso (hdmem _ hχ₁ _ hξ₁S) (hdmem _ hχ₁ _ hη),
              ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
              ClassFunction.inner_sub_right, horth _ hχ₁ _ hη (Ne.symm hηne),
              horth _ hξ₁S _ hχ₁ hξ₁ne1, horth _ hξ₁S _ hη (fun h => hηξ h.symm)]
            ring
          -- `⟨X, X′⟩ = ⟨χ₁, χ₁⟩`
          have hZ₁D : ClassFunction.inner (X - τ (χ₁ - ξ₁)) (τ (χ₁ - η)) = 0 := by
            have hτη : τ (χ₁ - η) = X' - (X' - τ (χ₁ - η)) := by abel
            rw [hτη, ClassFunction.inner_sub_right, z1, z2, sub_zero]
          have hXX' : ClassFunction.inner X X' = ClassFunction.inner χ₁ χ₁ := by
            have hX'd : X' = (X' - τ (χ₁ - η)) + τ (χ₁ - η) := by abel
            have hXd : X = (X - τ (χ₁ - ξ₁)) + τ (χ₁ - ξ₁) := by abel
            calc ClassFunction.inner X X'
                = ClassFunction.inner X ((X' - τ (χ₁ - η)) + τ (χ₁ - η)) := by rw [← hX'd]
              _ = ClassFunction.inner X (X' - τ (χ₁ - η))
                  + ClassFunction.inner X (τ (χ₁ - η)) := by
                  rw [ClassFunction.inner_add_right]
              _ = ClassFunction.inner X (τ (χ₁ - η)) := by rw [z3, zero_add]
              _ = ClassFunction.inner ((X - τ (χ₁ - ξ₁)) + τ (χ₁ - ξ₁)) (τ (χ₁ - η)) := by
                  rw [← hXd]
              _ = ClassFunction.inner (X - τ (χ₁ - ξ₁)) (τ (χ₁ - η))
                  + ClassFunction.inner (τ (χ₁ - ξ₁)) (τ (χ₁ - η)) := by
                  rw [ClassFunction.inner_add_left]
              _ = ClassFunction.inner χ₁ χ₁ := by rw [hZ₁D, zero_add, hDD]
          have hX'X : ClassFunction.inner X' X = ClassFunction.inner χ₁ χ₁ := by
            rw [inner_conj_symm X X', hXX', hNval, star_natCast]
          -- `‖X − X′‖² = 0`, so `X = X′`
          have hXeq : X = X' := by
            have h0 : (ClassFunction.inner (X - X') (X - X')).re = 0 := by
              have hexp : ClassFunction.inner (X - X') (X - X')
                  = ClassFunction.inner X X - ClassFunction.inner X X'
                    - (ClassFunction.inner X' X - ClassFunction.inner X' X') := by
                rw [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
                  ClassFunction.inner_sub_right]
              rw [hexp, hXnorm, hXX', hX'X, hX'norm]
              simp
            exact sub_eq_zero.mp (eq_zero_of_inner_self_re_eq_zero h0)
          have hneg : τ (η - χ₁) = -τ (χ₁ - η) := by rw [← map_neg, neg_sub]
          rw [hneg, ClassFunction.inner_neg_left, hXeq,
            inner_conj_symm X' (τ (χ₁ - η)), hX'D, hNval, star_natCast]

end PivotPartner

section UniformDegreeCoherence

variable [Fintype L] [Fintype G]

variable [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]

/-- **Peterfalvi (5.7): norm-general uniform-degree coherence, raw-family form** (Coq
`uniform_degree_coherence`, `PFsection5.v:1234`).

Given a finite pairwise-orthogonal, conjugate-closed, no-real family `S` with per-member
**general orthonormal `R`-families** `R(η)` (any length — `2` for irreducibles, `2q` for the
reducible certain-type columns `μ_j` of norm `q`), their (5.2.e) cross-orthogonality, the
`A`-supported lattice isometry, and a common nonzero degree, `S` is coherent — with **no norm-1
restriction**.

Unlike `coherent_of_constant_degree` (which requires every member irreducible via a 2-element
`CharacterDifferenceImage`, forcing `⟨ζ, ζ⟩ = 1`), this takes the raw per-member
`OrthonormalCharacterImageFamily`, so it accepts members of any genuine-character norm.  The pivot
`η₁` needs only a natural-number self-norm (`hN`, the "`⟨χ₁⟩ ∈ Num.nat`" of Coq's subcoherent
clause (a)); the partner `ζ₁` is built by `exists_pivotPartner`.

The nonzero-norm requirement of every member (needed for the pivot coefficient functional) is
*derived* from `hnr`: `a ≠ ā` forces `a ≠ 0` (since `0̄ = 0`), whence `⟨a, a⟩ ≠ 0`.

This is the (9.11) Galois/caseB engine: applied to the whole `𝒮(H₀C′)` — reducible `μ`-columns
included — it discharges coherence in one shot, with no auxiliary `2 < |cut|` count. -/
theorem uniform_degree_coherence_of_families
    {τ : IntegralCharacterMap L G} {S : Set (ClassFunction L ℂ)} {A : Set L}
    (hSfin : S.Finite)
    {η₁ : ClassFunction L ℂ} (hη₁ : η₁ ∈ S)
    (R : ∀ η ∈ S, OrthonormalCharacterImageFamily (L := L) (G := G) τ η)
    (horth : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → ClassFunction.inner a b = 0)
    (hconj : ∀ a ∈ S, a.conj ∈ S)
    (hnr : ∀ a ∈ S, a ≠ a.conj)
    (hN : ∃ n : ℕ, ClassFunction.inner η₁ η₁ = (n : ℂ))
    (hiso : ∀ ⦃φ ψ : ClassFunction L ℂ⦄, φ ∈ zSupportedSpan (L := L) S A →
      ψ ∈ zSupportedSpan (L := L) S A →
      ClassFunction.inner (τ φ) (τ ψ) = ClassFunction.inner φ ψ)
    (hZdiff : ∀ a ∈ S, ∀ b ∈ S, τ (a - b) ∈ ZIrr G)
    (hsuppdiff : ∀ a ∈ S, ∀ b ∈ S, ((a - b : ClassFunction L ℂ)).support ⊆ A)
    (hRorth : ∀ ⦃φ ξ : ClassFunction L ℂ⦄ (hφ : φ ∈ S) (hξ : ξ ∈ S),
      ClassFunction.inner φ ξ = 0 → ClassFunction.inner φ ξ.conj = 0 →
      (R φ hφ).Orthogonal (R ξ hξ))
    (hdeg : ∀ a ∈ S,
      ((a : ClassFunction L ℂ) : L → ℂ) 1 = ((η₁ : ClassFunction L ℂ) : L → ℂ) 1)
    (hdeg0 : ((η₁ : ClassFunction L ℂ) : L → ℂ) 1 ≠ 0)
    (h1A : (1 : L) ∉ A)
    {η₂ : ClassFunction L ℂ} (hη₂ : η₂ ∈ S) (hη₂ne : η₂ ≠ η₁) :
    Nonempty (IsCoherent τ S A) := by
  classical
  -- nonzero self-norm of every member: `a ≠ ā` forces `a ≠ 0`
  have hnormNe : ∀ a ∈ S, ClassFunction.inner a a ≠ 0 := by
    intro a ha hz
    have ha0 : a ≠ 0 := fun h => hnr a ha (by rw [h, ClassFunction.conj_zero])
    have hare : (ClassFunction.inner a a).re = 0 := by rw [hz, Complex.zero_re]
    exact ha0 (eq_zero_of_inner_self_re_eq_zero hare)
  -- build the pivot partner `ζ₁` for `η₁`
  obtain ⟨ζ₁, hζZ, hnorm, hpivot⟩ :=
    exists_pivotPartner (τ := τ) (A := A) hη₁ R horth hconj hnr hN hiso hZdiff hsuppdiff hRorth
  -- fire the pivot coherence engine
  exact ⟨pivotCoherence hSfin hη₁ hζZ horth hnormNe hnorm hpivot
    (fun φ ψ hφ hψ => hiso hφ hψ) hZdiff hdeg hdeg0 h1A hsuppdiff hη₂ hη₂ne⟩

end UniformDegreeCoherence

/-- **Coherence transports along a support change that shrinks the supported lattice**
(the support-side companion of `isCoherent_of_subset`: same family `S`, different support set).
If `S` is coherent on `A₁` and every `A₂`-supported lattice element is already `A₁`-supported
(`ℤ[S, A₂] ⊆ ℤ[S, A₁]`), then `S` is coherent on `A₂` with the *same* extension — only the
`nonzero` witness must be re-supplied on `A₂`.

The (9.11)/(6.8) use: the certain-type coherence (4.9)(b) lives on `A(M)`
(`supportInSubgroup (typePA M) M`) while the §10–§13 coherence interface uses
`A₀(M) ⊇ A(M)`; the column characters `μ_j` vanish off `A ∪ {1}` and `1 ∉ A₀`, so an
`A₀`-supported `ℤ[𝒯]`-combination is automatically `A`-supported and the lattices agree. -/
noncomputable def isCoherent_of_supportedSpan_le {G : Type*} [Group G] {L : Type*} [Group L]
    [Fintype L] [Fintype G]
    [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]
    {τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap L G}
    {S : Set (ClassFunction L ℂ)} {A₁ A₂ : Set L}
    (h : OddOrder.Peterfalvi.S07.IsCoherent τ S A₁)
    (hle : OddOrder.Peterfalvi.S07.zSupportedSpan (L := L) S A₂ ⊆
      OddOrder.Peterfalvi.S07.zSupportedSpan (L := L) S A₁)
    (hwit : ∃ φ : ClassFunction L ℂ,
      φ ∈ OddOrder.Peterfalvi.S07.zSupportedSpan (L := L) S A₂ ∧ φ ≠ 0) :
    OddOrder.Peterfalvi.S07.IsCoherent τ S A₂ where
  nonzero := hwit
  extension := h.extension
  extension_inner_eq := h.extension_inner_eq
  extends_on_supported := fun a ha => h.extends_on_supported a (hle ha)
  extension_mem_ZIrr := h.extension_mem_ZIrr

section BesselCount

variable {Γ : Type*} [Group Γ] [Fintype Γ] [Invertible (Nat.card Γ : ℂ)]

/-- **Bessel's inequality, integer-constituent count**: if `(θ i)_{i ∈ T}` is a finite
orthonormal family and every `⟨A, θ i⟩` is a *nonzero integer*, then `|T| ≤ ‖A‖²`.
Pythagoras against `S = ∑ᵢ ⟨A, θᵢ⟩ • θᵢ`: `0 ≤ ‖A − S‖² = ‖A‖² − ∑ᵢ ‖⟨A, θᵢ⟩‖²`, and each
`‖⟨A, θᵢ⟩‖² = mᵢ² ≥ 1`.  Coq `PFsection9.v:2036-2047` (the `cnorm_dconstt` count) in
Fourier-free form. -/
theorem card_le_inner_self_re_of_orthonormal_inner_int_ne {ι : Type*}
    (A : ClassFunction Γ ℂ) (T : Finset ι)
    (θ : ι → ClassFunction Γ ℂ)
    (hON1 : ∀ i ∈ T, ClassFunction.inner (θ i) (θ i) = 1)
    (hON2 : ∀ i ∈ T, ∀ j ∈ T, i ≠ j → ClassFunction.inner (θ i) (θ j) = 0)
    (hint : ∀ i ∈ T, ∃ m : ℤ, ClassFunction.inner A (θ i) = (m : ℂ))
    (hne : ∀ i ∈ T, ClassFunction.inner A (θ i) ≠ 0) :
    (T.card : ℝ) ≤ (ClassFunction.inner A A).re := by
  classical
  set c : ι → ℂ := fun i => ClassFunction.inner A (θ i) with hc
  set S : ClassFunction Γ ℂ := ∑ i ∈ T, c i • θ i with hS
  -- sum expansions of the sesquilinear inner product
  have hsum_left : ∀ (s : Finset ι) (ψ : ClassFunction Γ ℂ),
      ClassFunction.inner (∑ i ∈ s, c i • θ i) ψ
        = ∑ i ∈ s, c i * ClassFunction.inner (θ i) ψ := by
    intro s ψ
    induction s using Finset.cons_induction with
    | empty => simp
    | cons a s ha ih =>
        rw [Finset.sum_cons, Finset.sum_cons, ClassFunction.inner_add_left,
          ClassFunction.inner_smul_left, ih]
  have hsum_right : ∀ (s : Finset ι) (ψ : ClassFunction Γ ℂ),
      ClassFunction.inner ψ (∑ i ∈ s, c i • θ i)
        = ∑ i ∈ s, star (c i) * ClassFunction.inner ψ (θ i) := by
    intro s ψ
    induction s using Finset.cons_induction with
    | empty => simp
    | cons a s ha ih =>
        rw [Finset.sum_cons, Finset.sum_cons, ClassFunction.inner_add_right,
          OddOrder.RepresentationTheory.inner_smul_right, ih]
  -- the three cross terms all equal `∑ᵢ cᵢ·conj cᵢ`
  have hSA : ClassFunction.inner S A = ∑ i ∈ T, c i * star (c i) := by
    rw [hS, hsum_left T A]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show ClassFunction.inner (θ i) A = star (c i) from
      OddOrder.RepresentationTheory.inner_conj_symm A (θ i)]
  have hAS : ClassFunction.inner A S = ∑ i ∈ T, c i * star (c i) := by
    rw [hS, hsum_right T A]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hci : ClassFunction.inner A (θ i) = c i := rfl
    rw [hci, mul_comm]
  have hθS : ∀ i ∈ T, ClassFunction.inner (θ i) S = star (c i) := by
    intro i hi
    rw [hS, hsum_right T (θ i)]
    rw [Finset.sum_eq_single i
      (fun j hj hji => by rw [hON2 i hi j hj (fun h => hji h.symm), mul_zero])
      (fun hnotin => absurd hi hnotin)]
    rw [hON1 i hi, mul_one]
  have hSS : ClassFunction.inner S S = ∑ i ∈ T, c i * star (c i) := by
    rw [hS, hsum_left T S]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [show ClassFunction.inner (θ i) (∑ i ∈ T, c i • θ i) = star (c i) from by
      rw [← hS]; exact hθS i hi]
  -- Pythagoras: `0 ≤ ‖A − S‖² = ‖A‖² − ∑ᵢ ‖cᵢ‖²`
  have hkey : ClassFunction.inner (A - S) (A - S)
      = ClassFunction.inner A A - ∑ i ∈ T, c i * star (c i) := by
    rw [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
      ClassFunction.inner_sub_right, hSA, hAS, hSS]
    ring
  have hnorm : (∑ i ∈ T, c i * star (c i))
      = ((∑ i ∈ T, Complex.normSq (c i) : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    exact Finset.sum_congr rfl fun i _ => Complex.mul_conj (c i)
  have h0 := OddOrder.RepresentationTheory.inner_self_re_nonneg (A - S)
  rw [hkey, hnorm, Complex.sub_re, Complex.ofReal_re] at h0
  -- each `‖cᵢ‖² = mᵢ² ≥ 1`
  have hone : ∀ i ∈ T, (1 : ℝ) ≤ Complex.normSq (c i) := by
    intro i hi
    obtain ⟨m, hm⟩ := hint i hi
    have hmne : m ≠ 0 := by
      intro h0'
      apply hne i hi
      rw [hm, h0', Int.cast_zero]
    have hm1 : (1 : ℤ) ≤ m * m := by
      rcases lt_or_gt_of_ne hmne with h | h
      · nlinarith
      · nlinarith
    have hm' : c i = ((m : ℝ) : ℂ) := by
      have h : ClassFunction.inner A (θ i) = ((m : ℝ) : ℂ) := by
        rw [hm]
        push_cast
        ring
      exact h
    rw [hm', Complex.normSq_ofReal]
    exact_mod_cast hm1
  calc (T.card : ℝ) = ∑ _i ∈ T, (1 : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    _ ≤ ∑ i ∈ T, Complex.normSq (c i) := Finset.sum_le_sum hone
    _ ≤ (ClassFunction.inner A A).re := by linarith

end BesselCount

end OddOrder.Peterfalvi.S07


