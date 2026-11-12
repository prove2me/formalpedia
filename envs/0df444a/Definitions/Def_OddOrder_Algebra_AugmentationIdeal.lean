-- Prove2me | Definitions.Def_OddOrder_Algebra_AugmentationIdeal
-- name    : OddOrder_Algebra_AugmentationIdeal
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T04:40:25.28428+00:00
-- url     : https://prove2.me/theorems/eb2c972a-dbd5-4387-b98d-da554d038bb3
-- title:
--   The augmentation ideal of an integral group ring
-- statement:
--   Formalizes the augmentation map $\delta:\mathbb{Z}[G]\to\mathbb{Z}$ (sum of coefficients) of an integral group ring and the augmentation ideal $\Delta(G)=\ker\delta$. This is the groundwork for Isaacs, *Finite Group Theory*, §10C: the principal ideal theorem (Furtwängler, Thm 10.18) and Alperin–Kuo (Cor 10.28).
--
--   Main definitions: `augmentation` (the coefficient-sum ring homomorphism), `augmentationIdeal` ($\Delta(G)$ as a $\mathbb{Z}$-submodule), `augmentationIdealBasis` (Lemma 10.19: the $g-1$, $g\ne 1$, form a $\mathbb{Z}$-basis), `AugmentationQuotient` ($\Delta(G)/\Delta(G)^2$), `abelianizationEquivAugmentationQuotient` (Theorem 10.20: $G/G'\cong\Delta(G)/\Delta(G)^2$), and the subgroup versions (`augmentationIdealOf`, `groupRingOf`, `AugmentationQuotientOf`, `abelianizationEquivAugmentationQuotientOf` for Corollary 10.23), together with the transversal component map `transversalComponentSum`.
--
--   The bundle also proves 49 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Algebra/AugmentationIdeal.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Algebra/AugmentationIdeal.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.Algebra.Operations
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.GroupTheory.Complement

namespace OddOrder.Algebra

open MonoidAlgebra

section Augmentation

variable (R : Type*) [CommRing R] (G : Type*) [Group G]

/-- The **augmentation homomorphism** `δ : R[G] → R`, summing the coefficients:
`δ (∑ e_g · g) = ∑ e_g`. Realized as the lift of the trivial homomorphism
`G →* R`.

The integral group ring (`R = ℤ`) is the case Isaacs §10C uses; over a general base the
restriction to the centre is the trivial central character, which names the principal block
(`OddOrder.GroupTheory.CenterSimplesOrbit.aug`). -/
noncomputable def augmentation : MonoidAlgebra R G →ₐ[R] R :=
  MonoidAlgebra.lift R R G 1

@[simp]
theorem augmentation_of (g : G) : augmentation R G (MonoidAlgebra.of R G g) = 1 := by
  simp [augmentation]

@[simp]
theorem augmentation_single (g : G) (c : R) :
    augmentation R G (MonoidAlgebra.single g c) = c := by
  rw [augmentation, MonoidAlgebra.lift_single]
  simp

end Augmentation

variable (G : Type*) [Group G]

/-- The **augmentation ideal** `Δ(G) = ker δ`, as a `ℤ`-submodule of `ℤ[G]`. -/
noncomputable def augmentationIdeal : Submodule ℤ (MonoidAlgebra ℤ G) :=
  LinearMap.ker (augmentation ℤ G).toLinearMap

theorem mem_augmentationIdeal_iff {G : Type*} [Group G] {α : MonoidAlgebra ℤ G} :
    α ∈ augmentationIdeal G ↔ augmentation ℤ G α = 0 := Iff.rfl

theorem sub_one_mem_augmentationIdeal (g : G) :
    MonoidAlgebra.of ℤ G g - 1 ∈ augmentationIdeal G := by
  rw [mem_augmentationIdeal_iff, map_sub, map_one, augmentation_of, sub_self]

/-- Every element of `ℤ[G]` differs from `(δ α) • 1` by an element of the span
of the `g - 1` (key computation for Lemma 10.19). -/
theorem sub_augmentation_smul_one_mem_span {G : Type*} [Group G]
    (α : MonoidAlgebra ℤ G) :
    α - (augmentation ℤ G α) • 1
      ∈ Submodule.span ℤ (Set.range fun g : G => MonoidAlgebra.of ℤ G g - 1) := by
  induction α using MonoidAlgebra.induction_linear with
  | zero => simp
  | add f g hf hg =>
    have h1 : f + g - (augmentation ℤ G (f + g)) • 1
        = (f - (augmentation ℤ G f) • 1) + (g - (augmentation ℤ G g) • 1) := by
      rw [map_add, add_smul]
      abel
    rw [h1]
    exact Submodule.add_mem _ hf hg
  | single g c =>
    have h2 : c • MonoidAlgebra.of ℤ G g = MonoidAlgebra.single g c := by
      simp only [MonoidAlgebra.of_apply]
      exact (MonoidAlgebra.smul_single' c g 1).trans (by rw [mul_one])
    have h1 : MonoidAlgebra.single g c
        - (augmentation ℤ G (MonoidAlgebra.single g c)) • 1
        = c • (MonoidAlgebra.of ℤ G g - 1) := by
      rw [augmentation_single, ← h2]
      exact (smul_sub c _ _).symm
    rw [h1]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨g, rfl⟩)

/-- **Isaacs Lemma 10.19 (spanning half)**: `Δ(G)` is spanned over `ℤ` by the
elements `g - 1`, `g ∈ G`. -/
theorem augmentationIdeal_eq_span :
    augmentationIdeal G
      = Submodule.span ℤ (Set.range fun g : G => MonoidAlgebra.of ℤ G g - 1) := by
  apply le_antisymm
  · intro α hα
    rw [mem_augmentationIdeal_iff] at hα
    have hkey := sub_augmentation_smul_one_mem_span α
    rwa [hα, zero_smul, sub_zero] at hkey
  · rw [Submodule.span_le]
    rintro _ ⟨g, rfl⟩
    exact sub_one_mem_augmentationIdeal G g

/-- **Isaacs Lemma 10.19 (independence half)**: the family `g - 1` for
`1 ≠ g ∈ G` is `ℤ`-linearly independent in `ℤ[G]` (extract the coefficient at
`j ≠ 1` with the standard-basis coordinate functional). -/
theorem linearIndependent_of_sub_one :
    LinearIndependent ℤ (fun g : {g : G // g ≠ 1} =>
      MonoidAlgebra.of ℤ G g.val - 1) := by
  classical
  rw [linearIndependent_iff']
  intro s f hsum j hj
  have hc := congrArg ((MonoidAlgebra.basis G ℤ).coord j.val) hsum
  rw [map_sum, map_zero] at hc
  have hterm : ∀ i ∈ s,
      (MonoidAlgebra.basis G ℤ).coord j.val
        (f i • (MonoidAlgebra.of ℤ G i.val - 1))
      = if i = j then f i else 0 := by
    intro i _
    rw [map_smul, map_sub]
    have h1 : (MonoidAlgebra.basis G ℤ).coord j.val (MonoidAlgebra.of ℤ G i.val)
        = if i.val = j.val then 1 else 0 := by
      rw [show MonoidAlgebra.of ℤ G i.val = MonoidAlgebra.basis G ℤ i.val from
        (MonoidAlgebra.basis_apply ℤ i.val).symm]
      rw [Module.Basis.coord_apply, Module.Basis.repr_self,
        Finsupp.single_apply]
    have h2 : (MonoidAlgebra.basis G ℤ).coord j.val (1 : MonoidAlgebra ℤ G)
        = 0 := by
      rw [show (1 : MonoidAlgebra ℤ G) = MonoidAlgebra.basis G ℤ 1 from
        by rw [MonoidAlgebra.basis_apply]; rfl]
      rw [Module.Basis.coord_apply, Module.Basis.repr_self,
        Finsupp.single_apply, if_neg (fun h => j.2 h.symm)]
    rw [h1, h2, sub_zero]
    rcases eq_or_ne i j with rfl | hij
    · rw [if_pos rfl, if_pos rfl, smul_eq_mul, mul_one]
    · rw [if_neg (fun h => hij (Subtype.ext h)), if_neg hij, smul_zero]
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' s j (fun i => f i),
    if_pos hj] at hc
  exact hc

/-- **Isaacs Lemma 10.19**: the `g - 1` for `1 ≠ g ∈ G` form a `ℤ`-basis of the
augmentation ideal `Δ(G)`. -/
noncomputable def augmentationIdealBasis :
    Module.Basis {g : G // g ≠ 1} ℤ ↥(augmentationIdeal G) := by
  refine Module.Basis.mk (v := fun g : {g : G // g ≠ 1} =>
    (⟨MonoidAlgebra.of ℤ G g.val - 1, sub_one_mem_augmentationIdeal G g.val⟩ :
      ↥(augmentationIdeal G))) ?_ ?_
  · -- independence: push forward along the (injective) inclusion
    have hamb := linearIndependent_of_sub_one G
    exact hamb.of_comp (augmentationIdeal G).subtype
  · -- spanning: transport `augmentationIdeal_eq_span` into the subtype
    rintro ⟨α, hα⟩ -
    have hspan : α ∈ Submodule.span ℤ
        (Set.range fun g : G => MonoidAlgebra.of ℤ G g - 1) := by
      rw [← augmentationIdeal_eq_span]
      exact hα
    induction hspan using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, rfl⟩ := hx
      rcases eq_or_ne g 1 with rfl | hg
      · have h0 : (⟨MonoidAlgebra.of ℤ G 1 - 1, hα⟩ :
            ↥(augmentationIdeal G)) = 0 := by
          apply Subtype.ext
          change MonoidAlgebra.of ℤ G 1 - 1 = 0
          rw [map_one, sub_self]
        rw [h0]
        exact Submodule.zero_mem _
      · exact Submodule.subset_span ⟨⟨g, hg⟩, rfl⟩
    | zero =>
      have h0 : (⟨(0 : MonoidAlgebra ℤ G), hα⟩ : ↥(augmentationIdeal G)) = 0 :=
        rfl
      rw [h0]
      exact Submodule.zero_mem _
    | add x y hx hy ihx ihy =>
      have hxm : x ∈ augmentationIdeal G := by
        rw [augmentationIdeal_eq_span]; exact hx
      have hym : y ∈ augmentationIdeal G := by
        rw [augmentationIdeal_eq_span]; exact hy
      have hsplit : (⟨x + y, hα⟩ : ↥(augmentationIdeal G))
          = ⟨x, hxm⟩ + ⟨y, hym⟩ := rfl
      rw [hsplit]
      exact Submodule.add_mem _ (ihx hxm) (ihy hym)
    | smul c x hx ihx =>
      have hxm : x ∈ augmentationIdeal G := by
        rw [augmentationIdeal_eq_span]; exact hx
      have hsplit : (⟨c • x, hα⟩ : ↥(augmentationIdeal G)) = c • ⟨x, hxm⟩ :=
        rfl
      rw [hsplit]
      exact Submodule.smul_mem _ _ (ihx hxm)

@[simp]
theorem augmentationIdealBasis_apply (g : {g : G // g ≠ 1}) :
    ((augmentationIdealBasis G g : ↥(augmentationIdeal G)) :
        MonoidAlgebra ℤ G)
      = MonoidAlgebra.of ℤ G g.val - 1 := by
  rw [augmentationIdealBasis, Module.Basis.mk_apply]

section AugmentationQuotient

/-- `Δ(G)` absorbs multiplication on the left (it is a two-sided ideal, being
the kernel of the ring homomorphism `δ`). -/
theorem mul_mem_augmentationIdeal_left (α : MonoidAlgebra ℤ G)
    {β : MonoidAlgebra ℤ G} (hβ : β ∈ augmentationIdeal G) :
    α * β ∈ augmentationIdeal G := by
  rw [mem_augmentationIdeal_iff] at hβ ⊢
  rw [map_mul, hβ, mul_zero]

/-- `Δ(G)` absorbs multiplication on the right. -/
theorem mul_mem_augmentationIdeal_right {α : MonoidAlgebra ℤ G}
    (hα : α ∈ augmentationIdeal G) (β : MonoidAlgebra ℤ G) :
    α * β ∈ augmentationIdeal G := by
  rw [mem_augmentationIdeal_iff] at hα ⊢
  rw [map_mul, hα, zero_mul]

theorem augmentationIdeal_sq_le :
    augmentationIdeal G * augmentationIdeal G ≤ augmentationIdeal G :=
  Submodule.mul_le.mpr fun _ hα β _ => mul_mem_augmentationIdeal_right G hα β

/-- `Δ(G)²` pulled back to a `ℤ`-submodule of `Δ(G)` along the inclusion, so
that the additive group `Δ(G)/Δ(G)²` is available as a module quotient. -/
noncomputable def augmentationIdealSq : Submodule ℤ ↥(augmentationIdeal G) :=
  (augmentationIdeal G * augmentationIdeal G).comap (augmentationIdeal G).subtype

theorem mem_augmentationIdealSq {G : Type*} [Group G]
    {α : ↥(augmentationIdeal G)} :
    α ∈ augmentationIdealSq G
      ↔ (α : MonoidAlgebra ℤ G) ∈ augmentationIdeal G * augmentationIdeal G :=
  Iff.rfl

/-- The additive group `Δ(G)/Δ(G)²`, as a `ℤ`-module quotient. -/
abbrev AugmentationQuotient :=
  ↥(augmentationIdeal G) ⧸ augmentationIdealSq G

/-- The identity `xy - 1 = (x - 1) + (y - 1) + (x - 1)(y - 1)` in `ℤ[G]`
(Isaacs p. 310), which drives both directions of Theorem 10.20. -/
theorem of_mul_sub_one (x y : G) :
    MonoidAlgebra.of ℤ G (x * y) - 1
      = (MonoidAlgebra.of ℤ G x - 1) + (MonoidAlgebra.of ℤ G y - 1)
        + (MonoidAlgebra.of ℤ G x - 1) * (MonoidAlgebra.of ℤ G y - 1) := by
  rw [map_mul, mul_sub, sub_mul, mul_one, one_mul]
  abel

/-- The forward map of **Isaacs Theorem 10.20**: the homomorphism
`φ : G →* Δ(G)/Δ(G)²` (target written multiplicatively),
`g ↦ (g - 1) + Δ(G)²`. -/
noncomputable def toAugmentationQuotient :
    G →* Multiplicative (AugmentationQuotient G) where
  toFun g := Multiplicative.ofAdd (Submodule.Quotient.mk
    ⟨MonoidAlgebra.of ℤ G g - 1, sub_one_mem_augmentationIdeal G g⟩)
  map_one' := by
    have h0 : (⟨MonoidAlgebra.of ℤ G 1 - 1, sub_one_mem_augmentationIdeal G 1⟩ :
        ↥(augmentationIdeal G)) = 0 := by
      apply Subtype.ext
      change MonoidAlgebra.of ℤ G 1 - 1 = 0
      rw [map_one, sub_self]
    rw [h0, Submodule.Quotient.mk_zero, ofAdd_zero]
  map_mul' x y := by
    have key : (Submodule.Quotient.mk
          ⟨MonoidAlgebra.of ℤ G (x * y) - 1,
            sub_one_mem_augmentationIdeal G (x * y)⟩ :
          AugmentationQuotient G)
        = Submodule.Quotient.mk
            ⟨MonoidAlgebra.of ℤ G x - 1, sub_one_mem_augmentationIdeal G x⟩
          + Submodule.Quotient.mk
            ⟨MonoidAlgebra.of ℤ G y - 1, sub_one_mem_augmentationIdeal G y⟩ := by
      rw [← Submodule.Quotient.mk_add, Submodule.Quotient.eq]
      have hval : ((⟨MonoidAlgebra.of ℤ G (x * y) - 1,
              sub_one_mem_augmentationIdeal G (x * y)⟩
            - (⟨MonoidAlgebra.of ℤ G x - 1, sub_one_mem_augmentationIdeal G x⟩
              + ⟨MonoidAlgebra.of ℤ G y - 1,
                  sub_one_mem_augmentationIdeal G y⟩) :
            ↥(augmentationIdeal G)) : MonoidAlgebra ℤ G)
          = (MonoidAlgebra.of ℤ G x - 1) * (MonoidAlgebra.of ℤ G y - 1) := by
        push_cast
        rw [of_mul_sub_one]
        abel
      rw [mem_augmentationIdealSq, hval]
      exact Submodule.mul_mem_mul (sub_one_mem_augmentationIdeal G x)
        (sub_one_mem_augmentationIdeal G y)
    rw [key, ofAdd_add]

/-- The reverse map of **Isaacs Theorem 10.20**: the `ℤ`-linear retraction
`θ : Δ(G) → G/G'` (target written additively), determined on the basis of
Lemma 10.19 by `θ(g - 1) = G'g`. -/
noncomputable def augmentationRetraction :
    ↥(augmentationIdeal G) →ₗ[ℤ] Additive (Abelianization G) :=
  (augmentationIdealBasis G).constr ℤ fun g =>
    Additive.ofMul (Abelianization.of g.val)

theorem augmentationRetraction_sub_one (g : G)
    (h : MonoidAlgebra.of ℤ G g - 1 ∈ augmentationIdeal G) :
    augmentationRetraction G ⟨MonoidAlgebra.of ℤ G g - 1, h⟩
      = Additive.ofMul (Abelianization.of g) := by
  rcases eq_or_ne g 1 with rfl | hg
  · have h0 : (⟨MonoidAlgebra.of ℤ G 1 - 1, h⟩ : ↥(augmentationIdeal G)) = 0 := by
      apply Subtype.ext
      change MonoidAlgebra.of ℤ G 1 - 1 = 0
      rw [map_one, sub_self]
    rw [h0, map_zero, map_one, ofMul_one]
  · have hb : (⟨MonoidAlgebra.of ℤ G g - 1, h⟩ : ↥(augmentationIdeal G))
        = augmentationIdealBasis G ⟨g, hg⟩ := by
      apply Subtype.ext
      rw [augmentationIdealBasis_apply]
    rw [hb]
    exact (augmentationIdealBasis G).constr_basis ℤ _ ⟨g, hg⟩

/-- `θ` kills the products of two generators: applying `θ` to the identity
`xy - 1 = (x - 1) + (y - 1) + (x - 1)(y - 1)` gives
`θ((x-1)(y-1)) = G'(xy) - G'x - G'y = 0` (Isaacs p. 311). -/
theorem augmentationRetraction_sub_one_mul_sub_one (x y : G)
    (h : (MonoidAlgebra.of ℤ G x - 1) * (MonoidAlgebra.of ℤ G y - 1)
      ∈ augmentationIdeal G) :
    augmentationRetraction G
      ⟨(MonoidAlgebra.of ℤ G x - 1) * (MonoidAlgebra.of ℤ G y - 1), h⟩ = 0 := by
  have hsplit : (⟨(MonoidAlgebra.of ℤ G x - 1) * (MonoidAlgebra.of ℤ G y - 1),
        h⟩ : ↥(augmentationIdeal G))
      = ⟨MonoidAlgebra.of ℤ G (x * y) - 1,
          sub_one_mem_augmentationIdeal G (x * y)⟩
        - ⟨MonoidAlgebra.of ℤ G x - 1, sub_one_mem_augmentationIdeal G x⟩
        - ⟨MonoidAlgebra.of ℤ G y - 1, sub_one_mem_augmentationIdeal G y⟩ := by
    apply Subtype.ext
    push_cast
    rw [of_mul_sub_one]
    abel
  rw [hsplit, map_sub, map_sub, augmentationRetraction_sub_one,
    augmentationRetraction_sub_one, augmentationRetraction_sub_one, map_mul,
    ofMul_mul]
  abel

/-- Left multiplication by a fixed `α : ℤ[G]`, as a `ℤ`-linear endomorphism
of `Δ(G)`. -/
noncomputable def augmentationIdealMulLeft (α : MonoidAlgebra ℤ G) :
    ↥(augmentationIdeal G) →ₗ[ℤ] ↥(augmentationIdeal G) :=
  (LinearMap.mulLeft ℤ α).restrict fun _ hβ =>
    mul_mem_augmentationIdeal_left G α hβ

/-- Right multiplication by a fixed `β : ℤ[G]`, as a `ℤ`-linear endomorphism
of `Δ(G)`. -/
noncomputable def augmentationIdealMulRight (β : MonoidAlgebra ℤ G) :
    ↥(augmentationIdeal G) →ₗ[ℤ] ↥(augmentationIdeal G) :=
  (LinearMap.mulRight ℤ β).restrict fun _ hα =>
    mul_mem_augmentationIdeal_right G hα β

theorem augmentationRetraction_comp_mulLeft (x : G) :
    (augmentationRetraction G).comp
        (augmentationIdealMulLeft G (MonoidAlgebra.of ℤ G x - 1)) = 0 :=
  (augmentationIdealBasis G).ext fun y => by
    rw [LinearMap.comp_apply, LinearMap.zero_apply]
    have hb : augmentationIdealMulLeft G (MonoidAlgebra.of ℤ G x - 1)
          (augmentationIdealBasis G y)
        = ⟨(MonoidAlgebra.of ℤ G x - 1) * (MonoidAlgebra.of ℤ G y.val - 1),
            mul_mem_augmentationIdeal_left G _
              (sub_one_mem_augmentationIdeal G y.val)⟩ := by
      apply Subtype.ext
      change (MonoidAlgebra.of ℤ G x - 1)
          * ((augmentationIdealBasis G y : ↥(augmentationIdeal G)) :
              MonoidAlgebra ℤ G) = _
      rw [augmentationIdealBasis_apply]
    rw [hb, augmentationRetraction_sub_one_mul_sub_one]

theorem augmentationRetraction_comp_mulRight (β : ↥(augmentationIdeal G)) :
    (augmentationRetraction G).comp
        (augmentationIdealMulRight G (β : MonoidAlgebra ℤ G)) = 0 :=
  (augmentationIdealBasis G).ext fun x => by
    rw [LinearMap.comp_apply, LinearMap.zero_apply]
    have hb : augmentationIdealMulRight G (β : MonoidAlgebra ℤ G)
          (augmentationIdealBasis G x)
        = augmentationIdealMulLeft G (MonoidAlgebra.of ℤ G x.val - 1) β := by
      apply Subtype.ext
      change ((augmentationIdealBasis G x : ↥(augmentationIdeal G)) :
            MonoidAlgebra ℤ G) * (β : MonoidAlgebra ℤ G)
          = (MonoidAlgebra.of ℤ G x.val - 1) * (β : MonoidAlgebra ℤ G)
      rw [augmentationIdealBasis_apply]
    rw [hb]
    exact LinearMap.congr_fun
      (augmentationRetraction_comp_mulLeft G x.val) β

/-- `θ` vanishes on `Δ(G)²` (Isaacs p. 311). -/
theorem augmentationRetraction_eq_zero_of_mem_sq
    {α : ↥(augmentationIdeal G)} (hα : α ∈ augmentationIdealSq G) :
    augmentationRetraction G α = 0 := by
  obtain ⟨a, ha⟩ := α
  replace hα : a ∈ augmentationIdeal G * augmentationIdeal G := hα
  refine Submodule.mul_induction_on'
    (C := fun r _ => ∀ hr : r ∈ augmentationIdeal G,
      augmentationRetraction G ⟨r, hr⟩ = 0) ?_ ?_ hα ha
  · intro m hm n hn h
    exact LinearMap.congr_fun
      (augmentationRetraction_comp_mulRight G ⟨n, hn⟩) ⟨m, hm⟩
  · intro x hx y hy ihx ihy h
    have hxm : x ∈ augmentationIdeal G := augmentationIdeal_sq_le G hx
    have hym : y ∈ augmentationIdeal G := augmentationIdeal_sq_le G hy
    have hsplit : (⟨x + y, h⟩ : ↥(augmentationIdeal G))
        = ⟨x, hxm⟩ + ⟨y, hym⟩ := rfl
    rw [hsplit, map_add, ihx hxm, ihy hym, add_zero]

/-- `θ` descends to the quotient: `Δ(G)/Δ(G)² →ₗ[ℤ] G/G'`. -/
noncomputable def augmentationQuotientRetraction :
    AugmentationQuotient G →ₗ[ℤ] Additive (Abelianization G) :=
  (augmentationIdealSq G).liftQ (augmentationRetraction G) fun _ hα =>
    LinearMap.mem_ker.mpr (augmentationRetraction_eq_zero_of_mem_sq G hα)

@[simp]
theorem augmentationQuotientRetraction_mk (α : ↥(augmentationIdeal G)) :
    augmentationQuotientRetraction G (Submodule.Quotient.mk α)
      = augmentationRetraction G α := rfl

/-- `θ ∘ φ = id` on `G/G'` (Isaacs p. 311, the containment
`ker φ ⊆ G'`). -/
theorem augmentationQuotientRetraction_lift (a : Abelianization G) :
    augmentationQuotientRetraction G
        ((Abelianization.lift (toAugmentationQuotient G) a).toAdd)
      = Additive.ofMul a := by
  refine QuotientGroup.induction_on a fun g => ?_
  change augmentationRetraction G
      ⟨MonoidAlgebra.of ℤ G g - 1, sub_one_mem_augmentationIdeal G g⟩
    = Additive.ofMul (Abelianization.of g)
  exact augmentationRetraction_sub_one G g _

/-- `φ ∘ θ = id` on `Δ(G)/Δ(G)²` (Isaacs p. 311, surjectivity of `φ`
made quantitative). -/
theorem lift_augmentationQuotientRetraction (q : AugmentationQuotient G) :
    (Abelianization.lift (toAugmentationQuotient G)
        ((augmentationQuotientRetraction G q).toMul)).toAdd = q := by
  obtain ⟨α, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  obtain ⟨a, ha⟩ := α
  have hspan : a ∈ Submodule.span ℤ
      (Set.range fun g : G => MonoidAlgebra.of ℤ G g - 1) := by
    rw [← augmentationIdeal_eq_span]
    exact ha
  induction hspan using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨g, rfl⟩ := hz
    rw [augmentationQuotientRetraction_mk, augmentationRetraction_sub_one,
      toMul_ofMul, Abelianization.lift_apply_of]
    rfl
  | zero =>
    have h0 : (⟨(0 : MonoidAlgebra ℤ G), ha⟩ : ↥(augmentationIdeal G)) = 0 := rfl
    rw [h0, Submodule.Quotient.mk_zero, map_zero, toMul_zero, map_one, toAdd_one]
  | add x y hx hy ihx ihy =>
    have hxm : x ∈ augmentationIdeal G := by
      rw [augmentationIdeal_eq_span]; exact hx
    have hym : y ∈ augmentationIdeal G := by
      rw [augmentationIdeal_eq_span]; exact hy
    have hsplit : (⟨x + y, ha⟩ : ↥(augmentationIdeal G))
        = ⟨x, hxm⟩ + ⟨y, hym⟩ := rfl
    rw [hsplit, Submodule.Quotient.mk_add, map_add, toMul_add, map_mul,
      toAdd_mul, ihx hxm, ihy hym]
  | smul c x hx ihx =>
    have hxm : x ∈ augmentationIdeal G := by
      rw [augmentationIdeal_eq_span]; exact hx
    have hsplit : (⟨c • x, ha⟩ : ↥(augmentationIdeal G)) = c • ⟨x, hxm⟩ := rfl
    rw [hsplit, Submodule.Quotient.mk_smul, map_smul, toMul_zsmul, map_zpow,
      toAdd_zpow, ihx hxm]

/-- **Isaacs Theorem 10.20**: `G/G' ≅ Δ(G)/Δ(G)²` via `G'g ↦ (g - 1) + Δ(G)²`
(the additive quotient is written multiplicatively through `Multiplicative`). -/
noncomputable def abelianizationEquivAugmentationQuotient :
    Abelianization G ≃* Multiplicative (AugmentationQuotient G) :=
  MulEquiv.mk'
    { toFun := Abelianization.lift (toAugmentationQuotient G)
      invFun := fun q => (augmentationQuotientRetraction G q.toAdd).toMul
      left_inv := fun a => by
        change (augmentationQuotientRetraction G
            ((Abelianization.lift (toAugmentationQuotient G) a).toAdd)).toMul = a
        rw [augmentationQuotientRetraction_lift, toMul_ofMul]
      right_inv := fun q => by
        apply Multiplicative.toAdd.injective
        exact lift_augmentationQuotientRetraction G q.toAdd }
    fun x y => map_mul (Abelianization.lift (toAugmentationQuotient G)) x y

@[simp]
theorem abelianizationEquivAugmentationQuotient_of (g : G) :
    abelianizationEquivAugmentationQuotient G (Abelianization.of g)
      = Multiplicative.ofAdd (Submodule.Quotient.mk
          ⟨MonoidAlgebra.of ℤ G g - 1, sub_one_mem_augmentationIdeal G g⟩) :=
  rfl

end AugmentationQuotient

section TransversalComponents

/-- The identity `(x - 1)(y - 1) = xy - x - y + 1` in `ℤ[G]`. -/
theorem sub_one_mul_sub_one (x y : G) :
    (MonoidAlgebra.of ℤ G x - 1) * (MonoidAlgebra.of ℤ G y - 1)
      = MonoidAlgebra.of ℤ G (x * y) - MonoidAlgebra.of ℤ G x
        - MonoidAlgebra.of ℤ G y + 1 := by
  rw [map_mul, mul_sub, sub_mul, mul_one, one_mul]
  abel

variable (K : Subgroup G)

/-- The copy of the augmentation ideal `Δ(K)` of a subgroup `K ≤ G` inside
`ℤ[G]`: the `ℤ`-span of `{k - 1 | k ∈ K}` (Isaacs p. 311). -/
noncomputable def augmentationIdealOf : Submodule ℤ (MonoidAlgebra ℤ G) :=
  Submodule.span ℤ (Set.range fun k : K => MonoidAlgebra.of ℤ G ↑k - 1)

theorem sub_one_mem_augmentationIdealOf {x : G} (hx : x ∈ K) :
    MonoidAlgebra.of ℤ G x - 1 ∈ augmentationIdealOf G K :=
  Submodule.subset_span ⟨⟨x, hx⟩, rfl⟩

theorem augmentationIdealOf_le :
    augmentationIdealOf G K ≤ augmentationIdeal G :=
  Submodule.span_le.mpr <| by
    rintro _ ⟨k, rfl⟩
    exact sub_one_mem_augmentationIdeal G ↑k

/-- Reduction of `span S₁ * span S₂ ≤ P` to generators. Stated for `ℤ[G]`;
this sidesteps `Submodule.span_mul_span`, whose Algebra-section `*`-instance
(`Algebra.toModule`) does not match the Module-section `Submodule.mul`
instance under keyed rewriting. -/
theorem span_mul_span_le {S₁ S₂ : Set (MonoidAlgebra ℤ G)}
    {P : Submodule ℤ (MonoidAlgebra ℤ G)}
    (h : ∀ s₁ ∈ S₁, ∀ s₂ ∈ S₂, s₁ * s₂ ∈ P) :
    Submodule.span ℤ S₁ * Submodule.span ℤ S₂ ≤ P := by
  rw [Submodule.mul_le]
  intro m hm n hn
  induction hm using Submodule.span_induction with
  | mem s₁ hs₁ =>
    have hspan : Submodule.span ℤ S₂ ≤ P.comap (LinearMap.mulLeft ℤ s₁) :=
      Submodule.span_le.mpr fun s₂ hs₂ => h s₁ hs₁ s₂ hs₂
    exact hspan hn
  | zero =>
    rw [zero_mul]
    exact P.zero_mem
  | add x y hx hy ihx ihy =>
    rw [add_mul]
    exact P.add_mem ihx ihy
  | smul c x hx ihx =>
    rw [smul_mul_assoc]
    exact P.smul_mem c ihx

variable {T : Set G}

/-- Isaacs p. 311, the map `f = ∑ₜ fₜ : ℤ[G] → ℤ[K] ⊆ ℤ[G]`: on a basis
element `g` with unique factorization `g = kt` (`k ∈ K`, `t ∈ T`, along the
right transversal `T`), returns `k` — i.e. the sum of all `t`-components. -/
noncomputable def transversalComponentSum
    (hT : Subgroup.IsComplement (K : Set G) T) :
    MonoidAlgebra ℤ G →ₗ[ℤ] MonoidAlgebra ℤ G :=
  (MonoidAlgebra.basis G ℤ).constr ℤ fun g =>
    MonoidAlgebra.of ℤ G ((hT.equiv g).1 : G)

theorem transversalComponentSum_of (hT : Subgroup.IsComplement (K : Set G) T)
    (u : G) :
    transversalComponentSum G K hT (MonoidAlgebra.of ℤ G u)
      = MonoidAlgebra.of ℤ G ((hT.equiv u).1 : G) := by
  rw [show MonoidAlgebra.of ℤ G u = MonoidAlgebra.basis G ℤ u from
    (MonoidAlgebra.basis_apply ℤ u).symm]
  exact (MonoidAlgebra.basis G ℤ).constr_basis ℤ _ u

theorem transversalComponentSum_one (hT : Subgroup.IsComplement (K : Set G) T)
    (h1 : (1 : G) ∈ T) :
    transversalComponentSum G K hT 1 = 1 := by
  rw [show (1 : MonoidAlgebra ℤ G) = MonoidAlgebra.of ℤ G 1 from
      (map_one (MonoidAlgebra.of ℤ G)).symm,
    transversalComponentSum_of, hT.equiv_one (K.one_mem) h1]

/-- The key computation of Isaacs Lemma 10.21: for generators,
`f((k-1)(g-1)) = (k-1)(h-1)` where `g = ht` is the transversal
factorization. -/
theorem transversalComponentSum_sub_one_mul_sub_one
    (hT : Subgroup.IsComplement (K : Set G) T) (h1 : (1 : G) ∈ T)
    (k : K) (g : G) :
    transversalComponentSum G K hT
        ((MonoidAlgebra.of ℤ G ↑k - 1) * (MonoidAlgebra.of ℤ G g - 1))
      = (MonoidAlgebra.of ℤ G ↑k - 1)
        * (MonoidAlgebra.of ℤ G ((hT.equiv g).1 : G) - 1) := by
  have hfst_mul : ((hT.equiv (↑k * g)).1 : G) = ↑k * ((hT.equiv g).1 : G) := by
    rw [hT.equiv_mul_left_of_mem k.2]
    rfl
  have hfst_self : ((hT.equiv ↑k).1 : G) = ↑k := by
    rw [hT.equiv_fst_eq_self_of_mem_of_one_mem h1 k.2]
  rw [sub_one_mul_sub_one, map_add, map_sub, map_sub,
    transversalComponentSum_of, transversalComponentSum_of,
    transversalComponentSum_of, transversalComponentSum_one G K hT h1,
    hfst_mul, hfst_self, sub_one_mul_sub_one, map_mul]

/-- **Isaacs Lemma 10.21** (component-sum half): if `α ∈ Δ(K)Δ(G)` then
`f(α) = ∑ₜ αₜ ∈ Δ(K)²`. -/
theorem transversalComponentSum_mem_sq
    (hT : Subgroup.IsComplement (K : Set G) T) (h1 : (1 : G) ∈ T)
    {α : MonoidAlgebra ℤ G}
    (hα : α ∈ augmentationIdealOf G K * augmentationIdeal G) :
    transversalComponentSum G K hT α
      ∈ augmentationIdealOf G K * augmentationIdealOf G K := by
  have hle : augmentationIdealOf G K * augmentationIdeal G
      ≤ (augmentationIdealOf G K * augmentationIdealOf G K).comap
          (transversalComponentSum G K hT) := by
    rw [augmentationIdeal_eq_span]
    refine span_mul_span_le G ?_
    rintro _ ⟨k, rfl⟩ _ ⟨g, rfl⟩
    have : transversalComponentSum G K hT
        ((MonoidAlgebra.of ℤ G ↑k - 1) * (MonoidAlgebra.of ℤ G g - 1))
        ∈ augmentationIdealOf G K * augmentationIdealOf G K := by
      rw [transversalComponentSum_sub_one_mul_sub_one G K hT h1]
      exact Submodule.mul_mem_mul (sub_one_mem_augmentationIdealOf G K k.2)
        (sub_one_mem_augmentationIdealOf G K (hT.equiv g).1.2)
    exact this
  exact hle hα

/-- The copy of the group ring `ℤ[K]` of a subgroup `K ≤ G` inside `ℤ[G]`:
the `ℤ`-span of the basis elements `k ∈ K`. -/
noncomputable def groupRingOf : Submodule ℤ (MonoidAlgebra ℤ G) :=
  Submodule.span ℤ (Set.range fun k : K => MonoidAlgebra.of ℤ G ↑k)

theorem of_mem_groupRingOf {x : G} (hx : x ∈ K) :
    MonoidAlgebra.of ℤ G x ∈ groupRingOf G K :=
  Submodule.subset_span ⟨⟨x, hx⟩, rfl⟩

theorem one_mem_groupRingOf : (1 : MonoidAlgebra ℤ G) ∈ groupRingOf G K := by
  rw [show (1 : MonoidAlgebra ℤ G) = MonoidAlgebra.of ℤ G 1 from
    (map_one (MonoidAlgebra.of ℤ G)).symm]
  exact of_mem_groupRingOf G K K.one_mem

theorem augmentationIdealOf_le_groupRingOf :
    augmentationIdealOf G K ≤ groupRingOf G K :=
  Submodule.span_le.mpr <| by
    rintro _ ⟨k, rfl⟩
    exact Submodule.sub_mem _ (of_mem_groupRingOf G K k.2)
      (one_mem_groupRingOf G K)

/-- `Δ(K)² ⊆ Δ(K)`: same computation as `augmentationIdeal_sq_le`, inside the
subgroup copy. -/
theorem augmentationIdealOf_sq_le :
    augmentationIdealOf G K * augmentationIdealOf G K
      ≤ augmentationIdealOf G K := by
  refine span_mul_span_le G ?_
  rintro _ ⟨k, rfl⟩ _ ⟨k', rfl⟩
  rw [sub_one_mul_sub_one]
  have h : MonoidAlgebra.of ℤ G (↑k * ↑k') - MonoidAlgebra.of ℤ G ↑k
      - MonoidAlgebra.of ℤ G ↑k' + 1
      = (MonoidAlgebra.of ℤ G (↑k * ↑k') - 1)
        - (MonoidAlgebra.of ℤ G ↑k - 1)
        - (MonoidAlgebra.of ℤ G ↑k' - 1) := by
    abel
  rw [h]
  exact Submodule.sub_mem _
    (Submodule.sub_mem _
      (sub_one_mem_augmentationIdealOf G K (K.mul_mem k.2 k'.2))
      (sub_one_mem_augmentationIdealOf G K k.2))
    (sub_one_mem_augmentationIdealOf G K k'.2)

/-- `f` is the identity on `ℤ[K]` (each basis element `k ∈ K` factors as
`k·1` along the transversal). -/
theorem transversalComponentSum_eq_self {T : Set G}
    (hT : Subgroup.IsComplement (K : Set G) T) (h1 : (1 : G) ∈ T)
    {α : MonoidAlgebra ℤ G} (hα : α ∈ groupRingOf G K) :
    transversalComponentSum G K hT α = α := by
  have hle : groupRingOf G K
      ≤ LinearMap.ker (transversalComponentSum G K hT - LinearMap.id) :=
    Submodule.span_le.mpr <| by
      rintro _ ⟨k, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.sub_apply,
        LinearMap.id_apply, transversalComponentSum_of, sub_eq_zero,
        hT.equiv_fst_eq_self_of_mem_of_one_mem h1 k.2]
  have hker := hle hα
  rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
    sub_eq_zero] at hker
  exact hker

/-- **Isaacs Corollary 10.22** (ℤ[K]-form):
`Δ(K)² = Δ(K)Δ(G) ⊓ ℤ[K]` in `ℤ[G]`. -/
theorem augmentationIdealOf_sq_eq_inf_groupRingOf :
    augmentationIdealOf G K * augmentationIdealOf G K
      = (augmentationIdealOf G K * augmentationIdeal G) ⊓ groupRingOf G K := by
  obtain ⟨T, hT, h1⟩ := Subgroup.exists_isComplement_right K 1
  apply le_antisymm
  · exact le_inf (mul_le_mul_right (augmentationIdealOf_le G K) _)
      ((augmentationIdealOf_sq_le G K).trans
        (augmentationIdealOf_le_groupRingOf G K))
  · rintro α ⟨hα₁, hα₂⟩
    have hmem := transversalComponentSum_mem_sq G K hT h1 hα₁
    rwa [transversalComponentSum_eq_self G K hT h1 hα₂] at hmem

/-- **Isaacs Corollary 10.22** (Δ(K)-form):
`Δ(K)² = Δ(K)Δ(G) ⊓ Δ(K)` in `ℤ[G]`. -/
theorem augmentationIdealOf_sq_eq_inf :
    augmentationIdealOf G K * augmentationIdealOf G K
      = (augmentationIdealOf G K * augmentationIdeal G)
          ⊓ augmentationIdealOf G K := by
  apply le_antisymm
  · exact le_inf (mul_le_mul_right (augmentationIdealOf_le G K) _)
      (augmentationIdealOf_sq_le G K)
  · exact le_trans
      (inf_le_inf_left _ (augmentationIdealOf_le_groupRingOf G K))
      (le_of_eq (augmentationIdealOf_sq_eq_inf_groupRingOf G K).symm)

section SubgroupAugmentationQuotient

theorem linearIndependent_of_sub_one_subgroup :
    LinearIndependent ℤ (fun k : {k : K // k ≠ 1} =>
      MonoidAlgebra.of ℤ G ↑k.val - 1) := by
  classical
  rw [linearIndependent_iff']
  intro s f hsum j hj
  have hc := congrArg ((MonoidAlgebra.basis G ℤ).coord ↑j.val) hsum
  rw [map_sum, map_zero] at hc
  have hterm : ∀ i ∈ s,
      (MonoidAlgebra.basis G ℤ).coord ↑j.val
        (f i • (MonoidAlgebra.of ℤ G ↑i.val - 1))
      = if i = j then f i else 0 := by
    intro i _
    rw [map_smul, map_sub]
    have h1 : (MonoidAlgebra.basis G ℤ).coord ↑j.val
        (MonoidAlgebra.of ℤ G ↑i.val)
        = if (↑i.val : G) = ↑j.val then 1 else 0 := by
      rw [show MonoidAlgebra.of ℤ G (↑i.val : G) = MonoidAlgebra.basis G ℤ ↑i.val
        from (MonoidAlgebra.basis_apply ℤ (↑i.val : G)).symm]
      rw [Module.Basis.coord_apply, Module.Basis.repr_self,
        Finsupp.single_apply]
    have h2 : (MonoidAlgebra.basis G ℤ).coord ↑j.val (1 : MonoidAlgebra ℤ G)
        = 0 := by
      rw [show (1 : MonoidAlgebra ℤ G) = MonoidAlgebra.basis G ℤ 1 from
        by rw [MonoidAlgebra.basis_apply]; rfl]
      rw [Module.Basis.coord_apply, Module.Basis.repr_self,
        Finsupp.single_apply,
        if_neg (fun h => j.2 (OneMemClass.coe_eq_one.mp h.symm))]
    rw [h1, h2, sub_zero]
    rcases eq_or_ne i j with rfl | hij
    · rw [if_pos rfl, if_pos rfl, smul_eq_mul, mul_one]
    · have hne : (↑i.val : G) ≠ ↑j.val := fun h =>
        hij (Subtype.ext (Subtype.ext h))
      rw [if_neg hne, if_neg hij, smul_zero]
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' s j (fun i => f i),
    if_pos hj] at hc
  exact hc

/-- The elements `k - 1`, `1 ≠ k ∈ K`, form a `ℤ`-basis of the copy of
`Δ(K)` inside `ℤ[G]` (Lemma 10.19 for the subgroup copy). -/
noncomputable def augmentationIdealOfBasis :
    Module.Basis {k : K // k ≠ 1} ℤ ↥(augmentationIdealOf G K) := by
  refine Module.Basis.mk (v := fun k : {k : K // k ≠ 1} =>
    (⟨MonoidAlgebra.of ℤ G ↑k.val - 1,
      sub_one_mem_augmentationIdealOf G K k.val.2⟩ :
      ↥(augmentationIdealOf G K))) ?_ ?_
  · have hamb := linearIndependent_of_sub_one_subgroup G K
    exact hamb.of_comp (augmentationIdealOf G K).subtype
  · rintro ⟨α, hα⟩ -
    have hspan : α ∈ Submodule.span ℤ
        (Set.range fun k : K => MonoidAlgebra.of ℤ G ↑k - 1) := hα
    induction hspan using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      rcases eq_or_ne k 1 with rfl | hk
      · have h0 : (⟨MonoidAlgebra.of ℤ G ↑(1 : K) - 1, hα⟩ :
            ↥(augmentationIdealOf G K)) = 0 := by
          apply Subtype.ext
          change MonoidAlgebra.of ℤ G ↑(1 : K) - 1 = 0
          rw [OneMemClass.coe_one, map_one, sub_self]
        rw [h0]
        exact Submodule.zero_mem _
      · exact Submodule.subset_span ⟨⟨k, hk⟩, rfl⟩
    | zero =>
      have h0 : (⟨(0 : MonoidAlgebra ℤ G), hα⟩ :
          ↥(augmentationIdealOf G K)) = 0 := rfl
      rw [h0]
      exact Submodule.zero_mem _
    | add x y hx hy ihx ihy =>
      have hsplit : (⟨x + y, hα⟩ : ↥(augmentationIdealOf G K))
          = ⟨x, hx⟩ + ⟨y, hy⟩ := rfl
      rw [hsplit]
      exact Submodule.add_mem _ (ihx hx) (ihy hy)
    | smul c x hx ihx =>
      have hsplit : (⟨c • x, hα⟩ : ↥(augmentationIdealOf G K))
          = c • ⟨x, hx⟩ := rfl
      rw [hsplit]
      exact Submodule.smul_mem _ _ (ihx hx)

@[simp]
theorem augmentationIdealOfBasis_apply (k : {k : K // k ≠ 1}) :
    ((augmentationIdealOfBasis G K k : ↥(augmentationIdealOf G K)) :
        MonoidAlgebra ℤ G)
      = MonoidAlgebra.of ℤ G ↑k.val - 1 := by
  rw [augmentationIdealOfBasis, Module.Basis.mk_apply]

/-- `Δ(K)Δ(G) ∩ Δ(K)` pulled back to a submodule of `Δ(K)` — the kernel of
`Δ(K) → Δ(K)‾` (Isaacs p. 312). -/
noncomputable def augmentationIdealOfRel : Submodule ℤ ↥(augmentationIdealOf G K) :=
  (augmentationIdealOf G K * augmentationIdeal G).comap
    (augmentationIdealOf G K).subtype

theorem mem_augmentationIdealOfRel {G : Type*} [Group G] {K : Subgroup G}
    {α : ↥(augmentationIdealOf G K)} :
    α ∈ augmentationIdealOfRel G K
      ↔ (α : MonoidAlgebra ℤ G)
          ∈ augmentationIdealOf G K * augmentationIdeal G :=
  Iff.rfl

/-- The quotient `Δ(K)‾ = Δ(K)/(Δ(K)Δ(G) ∩ Δ(K))`. -/
abbrev AugmentationQuotientOf :=
  ↥(augmentationIdealOf G K) ⧸ augmentationIdealOfRel G K

/-- The forward map of Corollary 10.23: `K →* Δ(K)‾`, `k ↦ (k-1)‾`. -/
noncomputable def toAugmentationQuotientOf :
    K →* Multiplicative (AugmentationQuotientOf G K) where
  toFun k := Multiplicative.ofAdd (Submodule.Quotient.mk
    ⟨MonoidAlgebra.of ℤ G ↑k - 1, sub_one_mem_augmentationIdealOf G K k.2⟩)
  map_one' := by
    have h0 : (⟨MonoidAlgebra.of ℤ G ↑(1 : K) - 1,
        sub_one_mem_augmentationIdealOf G K (1 : K).2⟩ :
        ↥(augmentationIdealOf G K)) = 0 := by
      apply Subtype.ext
      change MonoidAlgebra.of ℤ G ↑(1 : K) - 1 = 0
      rw [OneMemClass.coe_one, map_one, sub_self]
    rw [h0, Submodule.Quotient.mk_zero, ofAdd_zero]
  map_mul' x y := by
    have key : (Submodule.Quotient.mk
          ⟨MonoidAlgebra.of ℤ G ↑(x * y) - 1,
            sub_one_mem_augmentationIdealOf G K (x * y).2⟩ :
          AugmentationQuotientOf G K)
        = Submodule.Quotient.mk
            ⟨MonoidAlgebra.of ℤ G ↑x - 1,
              sub_one_mem_augmentationIdealOf G K x.2⟩
          + Submodule.Quotient.mk
            ⟨MonoidAlgebra.of ℤ G ↑y - 1,
              sub_one_mem_augmentationIdealOf G K y.2⟩ := by
      rw [← Submodule.Quotient.mk_add, Submodule.Quotient.eq]
      have hval : ((⟨MonoidAlgebra.of ℤ G ↑(x * y) - 1,
              sub_one_mem_augmentationIdealOf G K (x * y).2⟩
            - (⟨MonoidAlgebra.of ℤ G ↑x - 1,
                sub_one_mem_augmentationIdealOf G K x.2⟩
              + ⟨MonoidAlgebra.of ℤ G ↑y - 1,
                  sub_one_mem_augmentationIdealOf G K y.2⟩) :
            ↥(augmentationIdealOf G K)) : MonoidAlgebra ℤ G)
          = (MonoidAlgebra.of ℤ G ↑x - 1) * (MonoidAlgebra.of ℤ G ↑y - 1) := by
        push_cast
        rw [of_mul_sub_one]
        abel
      rw [mem_augmentationIdealOfRel, hval]
      exact Submodule.mul_mem_mul (sub_one_mem_augmentationIdealOf G K x.2)
        (sub_one_mem_augmentationIdeal G ↑y)
    rw [key, ofAdd_add]

/-- The retraction `θ : Δ(K) →ₗ[ℤ] K/K'` on the basis of the subgroup copy,
`θ(k - 1) = K'k`. -/
noncomputable def augmentationIdealOfRetraction :
    ↥(augmentationIdealOf G K) →ₗ[ℤ] Additive (Abelianization K) :=
  (augmentationIdealOfBasis G K).constr ℤ fun k =>
    Additive.ofMul (Abelianization.of k.val)

theorem augmentationIdealOfRetraction_sub_one (k : K)
    (h : MonoidAlgebra.of ℤ G ↑k - 1 ∈ augmentationIdealOf G K) :
    augmentationIdealOfRetraction G K ⟨MonoidAlgebra.of ℤ G ↑k - 1, h⟩
      = Additive.ofMul (Abelianization.of k) := by
  rcases eq_or_ne k 1 with rfl | hk
  · have h0 : (⟨MonoidAlgebra.of ℤ G ↑(1 : K) - 1, h⟩ :
        ↥(augmentationIdealOf G K)) = 0 := by
      apply Subtype.ext
      change MonoidAlgebra.of ℤ G ↑(1 : K) - 1 = 0
      rw [OneMemClass.coe_one, map_one, sub_self]
    rw [h0, map_zero, map_one, ofMul_one]
  · have hb : (⟨MonoidAlgebra.of ℤ G ↑k - 1, h⟩ :
        ↥(augmentationIdealOf G K))
        = augmentationIdealOfBasis G K ⟨k, hk⟩ := by
      apply Subtype.ext
      rw [augmentationIdealOfBasis_apply]
    rw [hb]
    exact (augmentationIdealOfBasis G K).constr_basis ℤ _ ⟨k, hk⟩

theorem augmentationIdealOfRetraction_sub_one_mul_sub_one (x y : K)
    (h : (MonoidAlgebra.of ℤ G ↑x - 1) * (MonoidAlgebra.of ℤ G ↑y - 1)
      ∈ augmentationIdealOf G K) :
    augmentationIdealOfRetraction G K
      ⟨(MonoidAlgebra.of ℤ G ↑x - 1) * (MonoidAlgebra.of ℤ G ↑y - 1), h⟩
      = 0 := by
  have hsplit : (⟨(MonoidAlgebra.of ℤ G ↑x - 1) * (MonoidAlgebra.of ℤ G ↑y - 1),
        h⟩ : ↥(augmentationIdealOf G K))
      = ⟨MonoidAlgebra.of ℤ G ↑(x * y) - 1,
          sub_one_mem_augmentationIdealOf G K (x * y).2⟩
        - ⟨MonoidAlgebra.of ℤ G ↑x - 1, sub_one_mem_augmentationIdealOf G K x.2⟩
        - ⟨MonoidAlgebra.of ℤ G ↑y - 1,
            sub_one_mem_augmentationIdealOf G K y.2⟩ := by
    apply Subtype.ext
    push_cast
    rw [of_mul_sub_one]
    abel
  rw [hsplit, map_sub, map_sub, augmentationIdealOfRetraction_sub_one,
    augmentationIdealOfRetraction_sub_one, augmentationIdealOfRetraction_sub_one,
    map_mul, ofMul_mul]
  abel

/-- Left multiplication by `α`, as an endomorphism of `Δ(K)` (well-defined
when `α ∈ Δ(K)` since `Δ(K)² ⊆ Δ(K)`). -/
noncomputable def augmentationIdealOfMulLeft (α : MonoidAlgebra ℤ G)
    (hα : α ∈ augmentationIdealOf G K) :
    ↥(augmentationIdealOf G K) →ₗ[ℤ] ↥(augmentationIdealOf G K) :=
  (LinearMap.mulLeft ℤ α).restrict fun _ hβ =>
    augmentationIdealOf_sq_le G K (Submodule.mul_mem_mul hα hβ)

/-- Right multiplication by `β`, as an endomorphism of `Δ(K)`. -/
noncomputable def augmentationIdealOfMulRight (β : MonoidAlgebra ℤ G)
    (hβ : β ∈ augmentationIdealOf G K) :
    ↥(augmentationIdealOf G K) →ₗ[ℤ] ↥(augmentationIdealOf G K) :=
  (LinearMap.mulRight ℤ β).restrict fun _ hα =>
    augmentationIdealOf_sq_le G K (Submodule.mul_mem_mul hα hβ)

theorem augmentationIdealOfRetraction_comp_mulLeft (x : K) :
    (augmentationIdealOfRetraction G K).comp
        (augmentationIdealOfMulLeft G K (MonoidAlgebra.of ℤ G ↑x - 1)
          (sub_one_mem_augmentationIdealOf G K x.2)) = 0 :=
  (augmentationIdealOfBasis G K).ext fun y => by
    rw [LinearMap.comp_apply, LinearMap.zero_apply]
    have hb : augmentationIdealOfMulLeft G K (MonoidAlgebra.of ℤ G ↑x - 1)
          (sub_one_mem_augmentationIdealOf G K x.2)
          (augmentationIdealOfBasis G K y)
        = ⟨(MonoidAlgebra.of ℤ G ↑x - 1) * (MonoidAlgebra.of ℤ G ↑y.val - 1),
            augmentationIdealOf_sq_le G K (Submodule.mul_mem_mul
              (sub_one_mem_augmentationIdealOf G K x.2)
              (sub_one_mem_augmentationIdealOf G K y.val.2))⟩ := by
      apply Subtype.ext
      change (MonoidAlgebra.of ℤ G ↑x - 1)
          * ((augmentationIdealOfBasis G K y : ↥(augmentationIdealOf G K)) :
              MonoidAlgebra ℤ G) = _
      rw [augmentationIdealOfBasis_apply]
    rw [hb, augmentationIdealOfRetraction_sub_one_mul_sub_one]

theorem augmentationIdealOfRetraction_comp_mulRight
    (β : ↥(augmentationIdealOf G K)) :
    (augmentationIdealOfRetraction G K).comp
        (augmentationIdealOfMulRight G K (β : MonoidAlgebra ℤ G) β.2) = 0 :=
  (augmentationIdealOfBasis G K).ext fun x => by
    rw [LinearMap.comp_apply, LinearMap.zero_apply]
    have hb : augmentationIdealOfMulRight G K (β : MonoidAlgebra ℤ G) β.2
          (augmentationIdealOfBasis G K x)
        = augmentationIdealOfMulLeft G K (MonoidAlgebra.of ℤ G ↑x.val - 1)
            (sub_one_mem_augmentationIdealOf G K x.val.2) β := by
      apply Subtype.ext
      change ((augmentationIdealOfBasis G K x : ↥(augmentationIdealOf G K)) :
            MonoidAlgebra ℤ G) * (β : MonoidAlgebra ℤ G)
          = (MonoidAlgebra.of ℤ G ↑x.val - 1) * (β : MonoidAlgebra ℤ G)
      rw [augmentationIdealOfBasis_apply]
    rw [hb]
    exact LinearMap.congr_fun
      (augmentationIdealOfRetraction_comp_mulLeft G K x.val) β

/-- `θ` vanishes on the kernel `Δ(K)Δ(G) ∩ Δ(K)`: by Corollary 10.22 this is
`Δ(K)²`, on which `θ` vanishes as in Theorem 10.20. -/
theorem augmentationIdealOfRetraction_eq_zero_of_mem_rel
    {α : ↥(augmentationIdealOf G K)} (hα : α ∈ augmentationIdealOfRel G K) :
    augmentationIdealOfRetraction G K α = 0 := by
  obtain ⟨a, ha⟩ := α
  replace hα : a ∈ augmentationIdealOf G K * augmentationIdeal G := hα
  have hsq : a ∈ augmentationIdealOf G K * augmentationIdealOf G K := by
    rw [augmentationIdealOf_sq_eq_inf]
    exact Submodule.mem_inf.mpr ⟨hα, ha⟩
  refine Submodule.mul_induction_on'
    (C := fun r _ => ∀ hr : r ∈ augmentationIdealOf G K,
      augmentationIdealOfRetraction G K ⟨r, hr⟩ = 0) ?_ ?_ hsq ha
  · intro m hm n hn h
    exact LinearMap.congr_fun
      (augmentationIdealOfRetraction_comp_mulRight G K ⟨n, hn⟩) ⟨m, hm⟩
  · intro x hx y hy ihx ihy h
    have hxm : x ∈ augmentationIdealOf G K := augmentationIdealOf_sq_le G K hx
    have hym : y ∈ augmentationIdealOf G K := augmentationIdealOf_sq_le G K hy
    have hsplit : (⟨x + y, h⟩ : ↥(augmentationIdealOf G K))
        = ⟨x, hxm⟩ + ⟨y, hym⟩ := rfl
    rw [hsplit, map_add, ihx hxm, ihy hym, add_zero]

/-- `θ` descends to `Δ(K)‾ →ₗ[ℤ] K/K'`. -/
noncomputable def augmentationQuotientOfRetraction :
    AugmentationQuotientOf G K →ₗ[ℤ] Additive (Abelianization K) :=
  (augmentationIdealOfRel G K).liftQ (augmentationIdealOfRetraction G K)
    fun _ hα => LinearMap.mem_ker.mpr
      (augmentationIdealOfRetraction_eq_zero_of_mem_rel G K hα)

@[simp]
theorem augmentationQuotientOfRetraction_mk (α : ↥(augmentationIdealOf G K)) :
    augmentationQuotientOfRetraction G K (Submodule.Quotient.mk α)
      = augmentationIdealOfRetraction G K α := rfl

theorem augmentationQuotientOfRetraction_lift (a : Abelianization K) :
    augmentationQuotientOfRetraction G K
        ((Abelianization.lift (toAugmentationQuotientOf G K) a).toAdd)
      = Additive.ofMul a := by
  refine QuotientGroup.induction_on a fun k => ?_
  change augmentationIdealOfRetraction G K
      ⟨MonoidAlgebra.of ℤ G ↑k - 1, sub_one_mem_augmentationIdealOf G K k.2⟩
    = Additive.ofMul (Abelianization.of k)
  exact augmentationIdealOfRetraction_sub_one G K k _

theorem lift_augmentationQuotientOfRetraction (q : AugmentationQuotientOf G K) :
    (Abelianization.lift (toAugmentationQuotientOf G K)
        ((augmentationQuotientOfRetraction G K q).toMul)).toAdd = q := by
  obtain ⟨α, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  obtain ⟨a, ha⟩ := α
  have hspan : a ∈ Submodule.span ℤ
      (Set.range fun k : K => MonoidAlgebra.of ℤ G ↑k - 1) := ha
  induction hspan using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨k, rfl⟩ := hz
    rw [augmentationQuotientOfRetraction_mk,
      augmentationIdealOfRetraction_sub_one, toMul_ofMul,
      Abelianization.lift_apply_of]
    rfl
  | zero =>
    have h0 : (⟨(0 : MonoidAlgebra ℤ G), ha⟩ :
        ↥(augmentationIdealOf G K)) = 0 := rfl
    rw [h0, Submodule.Quotient.mk_zero, map_zero, toMul_zero, map_one,
      toAdd_one]
  | add x y hx hy ihx ihy =>
    have hsplit : (⟨x + y, ha⟩ : ↥(augmentationIdealOf G K))
        = ⟨x, hx⟩ + ⟨y, hy⟩ := rfl
    rw [hsplit, Submodule.Quotient.mk_add, map_add, toMul_add, map_mul,
      toAdd_mul, ihx hx, ihy hy]
  | smul c x hx ihx =>
    have hsplit : (⟨c • x, ha⟩ : ↥(augmentationIdealOf G K))
        = c • ⟨x, hx⟩ := rfl
    rw [hsplit, Submodule.Quotient.mk_smul, map_smul, toMul_zsmul, map_zpow,
      toAdd_zpow, ihx hx]

/-- **Isaacs Corollary 10.23**: `Δ(K)‾ ≅ K/K'` via `(k-1)‾ ↦ K'k`, where
`Δ(K)‾ = Δ(K)/(Δ(K)Δ(G) ∩ Δ(K))` is (the second-isomorphism-theorem model
of) the image of `Δ(K)` in `Δ(G)/Δ(K)Δ(G)`. -/
noncomputable def abelianizationEquivAugmentationQuotientOf :
    Abelianization K ≃* Multiplicative (AugmentationQuotientOf G K) :=
  MulEquiv.mk'
    { toFun := Abelianization.lift (toAugmentationQuotientOf G K)
      invFun := fun q => (augmentationQuotientOfRetraction G K q.toAdd).toMul
      left_inv := fun a => by
        change (augmentationQuotientOfRetraction G K
            ((Abelianization.lift (toAugmentationQuotientOf G K) a).toAdd)).toMul
          = a
        rw [augmentationQuotientOfRetraction_lift, toMul_ofMul]
      right_inv := fun q => by
        apply Multiplicative.toAdd.injective
        exact lift_augmentationQuotientOfRetraction G K q.toAdd }
    fun x y => map_mul (Abelianization.lift (toAugmentationQuotientOf G K)) x y

@[simp]
theorem abelianizationEquivAugmentationQuotientOf_of (k : K) :
    abelianizationEquivAugmentationQuotientOf G K (Abelianization.of k)
      = Multiplicative.ofAdd (Submodule.Quotient.mk
          ⟨MonoidAlgebra.of ℤ G ↑k - 1,
            sub_one_mem_augmentationIdealOf G K k.2⟩) :=
  rfl

end SubgroupAugmentationQuotient

end TransversalComponents

end OddOrder.Algebra


