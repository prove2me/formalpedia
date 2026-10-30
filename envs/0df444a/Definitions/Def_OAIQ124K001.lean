-- Prove2me | Definitions.Def_OAIQ124K001
-- name    : OAIQ124K001
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T05:42:14.55267+00:00
-- url     : https://prove2.me/theorems/30c3cb74-f401-4156-a621-b3151eb3a23c
-- title:
--   Definitions bundle OAIQ124K001 of the split of OpenAI, Combinatorial invariance of Kazhdan–Lusztig polynomials (result family 168)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.KLInvariance.combinatorial_invariance`, carved from OpenAI's openai/math development (OpenAI, *Combinatorial invariance of Kazhdan–Lusztig polynomials (result family 168)*, OpenAI Math Release, September 24, 2026, result family 168, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 187 declarations of OpenAI's Lean: 74 definitions, 5 inductive types or structures, 10 instances and 98 theorems. The definitions and types are `OAI.KLInvariance.CoefficientChange`, `OAI.KLInvariance.CoefficientChange.dualEquiv`, `OAI.KLInvariance.CoefficientChange.dualFrom`, `OAI.KLInvariance.CoefficientChange.dualTo`, `OAI.KLInvariance.CoefficientChange.equiv`, `OAI.KLInvariance.CoefficientChange.equivVal`, `OAI.KLInvariance.CoefficientChange.kEquiv`, `OAI.KLInvariance.CoefficientChange.map`, `OAI.KLInvariance.CoefficientChange.mapEquiv`, `OAI.KLInvariance.CoefficientChange.pairingEquiv`, `OAI.KLInvariance.CoordinateProjection.eval`, `OAI.KLInvariance.CoordinateProjection.image`, `OAI.KLInvariance.CoordinateProjection.project`, `OAI.KLInvariance.DiamondEdges`, `OAI.KLInvariance.FiniteCharacterLocalization.diagonal`, `OAI.KLInvariance.FiniteCharacterLocalization.residueSetoid`, `OAI.KLInvariance.FrobeniusDuality.PairedBimodule`, `OAI.KLInvariance.FrobeniusDuality.PairedModule`, `OAI.KLInvariance.FrobeniusDuality.extendPairing`, `OAI.KLInvariance.FrobeniusDuality.fiber`, `OAI.KLInvariance.FrobeniusDuality.inducedBasis`, `OAI.KLInvariance.FrobeniusDuality.inducedBimodule`, `OAI.KLInvariance.FrobeniusDuality.inducedModule`, `OAI.KLInvariance.FrobeniusDuality.inducedRight`, `OAI.KLInvariance.FrobeniusDuality.recoverDual`, `OAI.KLInvariance.FrobeniusDuality.restrictDual`, `OAI.KLInvariance.FrobeniusDuality.restrictPairing`, `OAI.KLInvariance.FrobeniusDuality.restrictedModule`, `OAI.KLInvariance.FrobeniusDuality.restrictedRight`, `OAI.KLInvariance.FrobeniusDuality.restrictionBasis`, `OAI.KLInvariance.FrobeniusDuality.restrictionEquiv`, `OAI.KLInvariance.FrobeniusDuality.unitBimodule`, `OAI.KLInvariance.FrobeniusDuality.unitModule`, `OAI.KLInvariance.FrobeniusDuality.unitPairing`, `OAI.KLInvariance.IntegralSupport.cut`, `OAI.KLInvariance.IntegralSupport.dualToSupport`, `OAI.KLInvariance.IntegralSupport.projection`, `OAI.KLInvariance.IntegralSupport.supportEquivDual`, `OAI.KLInvariance.IntegralSupport.supported`, `OAI.KLInvariance.MomentGraph.Sheaf.addZeroRight` and 39 more.
--
--   **Sources.** They come from these modules of lean/OAI/RepresentationTheory, in whole or in part: `KazhdanLusztig_BottSamelson`, `KazhdanLusztig_Bruhat`, `KazhdanLusztig_CanonicalKL`, `KazhdanLusztig_Decomposition`, `KazhdanLusztig_Frobenius`, `KazhdanLusztig_GradedSheaves`, `KazhdanLusztig_IntegralPairings`, `KazhdanLusztig_MinimalExtensions`, `KazhdanLusztig_ModuleAlgebra`, `KazhdanLusztig_ReflectionOrders`, `KazhdanLusztig_ReflectionPlane`, `KazhdanLusztig_ReflectionSchedules`, `KazhdanLusztig_SheafMorphisms`, `KazhdanLusztig_Support`, `KazhdanLusztig_Tits`.
--
--   **Imports.** It imports the published bundle `Def_KLInvariance`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ124K004`, `OAIQ124K005`, `OAIQ124K006` and `OAIQ124K007`.
-- source:
--   OpenAI, Combinatorial invariance of Kazhdan–Lusztig polynomials (result family 168), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 168; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Combinatorial-Invariance-of-Kazhdan-Lusztig-Polynomials-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/RepresentationTheory at commit adc7f12

import Mathlib
import Definitions.Def_KLInvariance

section
-- module Solutions.OAIQ124_KL.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : c) :
    dite c a b = a h := dif_pos h
theorem dite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : ¬c) :
    dite c a b = b h := dif_neg h

/-- Mathlib's newer `TensorProduct.inductionOn` (no `zero` case: it is the `tmul` case at
`0 ⊗ₜ 0`); ours has only `TensorProduct.induction_on`, which asks for one. Not named
`TensorProduct.inductionOn`: inside `namespace OAI` that would make `open TensorProduct` open
`OAI.TensorProduct` instead of Mathlib's. -/
@[elab_as_elim]
theorem tensorInductionOn {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] {motive : TensorProduct R M N → Prop} (z : TensorProduct R M N)
    (tmul : ∀ x y, motive (TensorProduct.tmul R x y))
    (add : ∀ x y, motive x → motive y → motive (x + y)) : motive z :=
  TensorProduct.induction_on z (by simpa using tmul 0 0) tmul add
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_ModuleAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Height-one membership into free targets, minimal covers, graded Nakayama, reverse projectivity, saturated edge kernels and strict Hilbert detection.
-/

section

namespace KLInvariance.Graded
open scoped Pointwise
variable {A F P : Type*} [CommRing A]
  [AddCommGroup F] [Module A F] [AddCommGroup P] [Module A P]

/-- If a split cover is minimal modulo I, its complementary kernel equals
its own I-multiple. This is the exact input to the graded Nakayama step. -/
theorem positive_smul_kernel_of_minimal_split
    (I : Ideal A) (f : F →ₗ[A] P) (s : P →ₗ[A] F)
    (hs : f.comp s = LinearMap.id)
    (hmin : LinearMap.ker f ≤ I • (⊤ : Submodule A F)) :
    I • (⊤ : Submodule A (LinearMap.ker f)) = ⊤ := by
  have hs' (y : P) : f (s y) = y := LinearMap.congr_fun hs y
  let k : F →ₗ[A] LinearMap.ker f :=
    { toFun := fun x => ⟨x - s (f x), by simp [LinearMap.mem_ker, hs']⟩
      map_add' := fun x y => Subtype.ext (by simp; abel)
      map_smul' := fun r x => Subtype.ext (by simp [smul_sub]) }
  apply le_antisymm le_top
  intro x _
  have hx : (x : F) ∈ I • (⊤ : Submodule A F) := hmin x.property
  have hkx : k (x : F) = x := by
    apply Subtype.ext
    simp [k]
  rw [← hkx]
  refine Submodule.smul_induction_on hx ?_ ?_
  · intro r hr y _
    rw [map_smul]
    exact Submodule.smul_mem_smul hr (Submodule.mem_top : k y ∈ (⊤ : Submodule A _))
  · intro y z hy hz
    rw [map_add]
    exact Submodule.add_mem _ hy hz

end KLInvariance.Graded


end

end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_Bruhat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Strong Bruhat order, subwords, length, finite lower ideals and arbitrary finite intervals; the selected R family.
-/

section


namespace KLInvariance

open Polynomial

universe u v u' v'

variable {B : Type u} {W : Type v} [klPreservedInstance1 : Group W] {M : CoxeterMatrix B}


/-! Exchange consequences required for the source's finite-rank reduction
and for consistency of the equal-parameter Hecke recursion. -/


/-- Inversion preserves the actual strong Bruhat graph. -/
theorem bruhatStep_inv (cs : CoxeterSystem M W) {x y : W}
    (hxy : BruhatStep cs x y) : BruhatStep cs x⁻¹ y⁻¹ := by
  obtain ⟨hlen, t, ht, heq⟩ := hxy
  refine ⟨by simpa using hlen, x⁻¹ * t * x, by simpa using ht.conj x⁻¹, ?_⟩
  rw [heq, mul_inv_rev, ht.inv]
  group


end KLInvariance
end

end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_CanonicalKL
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Canonical low-part construction, strict halfdegree, reciprocity and uniqueness; certification of the selected polynomials and interval ranks.
-/

section
namespace KLInvariance

open Polynomial

universe u v u' v'

variable {B : Type u} {W : Type v} [klPreservedInstance1 : Group W] {M : CoxeterMatrix B}

noncomputable local instance instDecidableEq_solutions_2 : DecidableEq W := Classical.decEq W

end KLInvariance

end

end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_ReflectionPlane
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Linear reflection products and common root planes for nondegenerate ambient forms.
-/

section


namespace KLInvariance.ReflectionPlane
variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]

/-- Independent linear forms give a surjection to the coordinate plane. -/
theorem formPair_surjective (f g : Module.Dual k V)
    (hfg : LinearIndependent k ![f, g]) : Function.Surjective (f.prod g) := by
  apply LinearMap.dualMap_injective_iff.mp
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm _ bot_le
  intro l hl
  change l = 0
  have hl' (v : V) : l (f v, g v) = 0 := LinearMap.congr_fun hl v
  have heval (c d : k) : l (c, d) = c * l (1, 0) + d * l (0, 1) := by
    have heq : (c, d) = c • ((1, 0) : k × k) + d • ((0, 1) : k × k) := by
      ext <;> simp
    rw [heq, map_add, map_smul, map_smul]
    rfl
  have hrel : l (1, 0) • f + l (0, 1) • g = 0 := by
    ext v
    change l (1, 0) * f v + l (0, 1) * g v = 0
    have hv := hl' v
    rw [heval] at hv
    simpa only [mul_comm] using hv
  obtain ⟨h₁, h₂⟩ := LinearIndependent.pair_iff.mp hfg _ _ hrel
  apply LinearMap.ext
  intro x
  obtain ⟨c, d⟩ := x
  change l (c, d) = 0
  rw [heval, h₁, h₂, mul_zero, mul_zero, add_zero]

/-- The range of the difference of a two-reflection product from the
identity is exactly the span of the two roots. -/
theorem range_preReflection_product_sub_id (α β : V) (f g : Module.Dual k V)
    (hfg : LinearIndependent k ![f, g]) :
    LinearMap.range ((Module.preReflection α f).comp (Module.preReflection β g) -
      LinearMap.id) = Submodule.span k {α, β} := by
  have hformula (v : V) :
      ((Module.preReflection α f).comp (Module.preReflection β g) -
        (LinearMap.id : V →ₗ[k] V)) v = (-f v + f β * g v) • α + (-g v) • β := by
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, Module.preReflection_apply,
      LinearMap.id_apply, map_sub, map_smul]
    module
  apply le_antisymm
  · rintro z ⟨v, rfl⟩
    rw [hformula]
    exact Submodule.mem_span_pair.mpr ⟨_, _, rfl⟩
  · intro z hz
    obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hz
    obtain ⟨v, hv⟩ := formPair_surjective f g hfg (-a - f β * b, -b)
    have hf : f v = -a - f β * b := congrArg Prod.fst hv
    have hg : g v = -b := congrArg Prod.snd hv
    refine ⟨v, ?_⟩
    rw [hformula, hf, hg]
    module


theorem range_reflection_product_sub_id
    (B : LinearMap.BilinForm k V) (hB : B.Nondegenerate)
    (α β : V) (hα : B α α = 2) (hβ : B β β = 2)
    (hαβ : LinearIndependent k ![α, β]) :
    LinearMap.range (((Module.reflection hα).toLinearMap).comp
      (Module.reflection hβ).toLinearMap - LinearMap.id) = Submodule.span k {α, β} := by
  apply range_preReflection_product_sub_id
  have h := hαβ.map' B hB.ker_eq_bot
  have heq : (⇑B ∘ ![α, β]) = ![B α, B β] := by
    funext i
    fin_cases i <;> rfl
  rw [heq] at h
  exact h

/-- Equal products of two normalized reflections recover equal root
planes, the exact local geometric input to `dih:transport`. -/
theorem plane_eq_of_reflection_product_eq
    (B : LinearMap.BilinForm k V) (hB : B.Nondegenerate)
    (α β γ δ : V)
    (hα : B α α = 2) (hβ : B β β = 2) (hγ : B γ γ = 2) (hδ : B δ δ = 2)
    (hαβ : LinearIndependent k ![α, β]) (hγδ : LinearIndependent k ![γ, δ])
    (heq : (Module.reflection hα).toLinearMap.comp (Module.reflection hβ).toLinearMap =
      (Module.reflection hγ).toLinearMap.comp (Module.reflection hδ).toLinearMap) :
    Submodule.span k {α, β} = Submodule.span k {γ, δ} := by
  rw [← range_reflection_product_sub_id B hB α β hα hβ hαβ,
    ← range_reflection_product_sub_id B hB γ δ hγ hδ hγδ, heq]

end KLInvariance.ReflectionPlane


end

end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_Tits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Actual Bruhat graph labels, Tits realizations and extended root spaces, cotangent coordinates and standard parabolic support.
-/

section


namespace KLInvariance.Realization
open Module
variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- An actual rank-one perturbation that preserves a nondegenerate symmetric
form is an orthogonal reflection, not a unipotent transvection. -/
theorem orthogonal_rank_one_form
    (B : LinearMap.BilinForm ℝ V) (hs : B.IsSymm) (hn : B.Nondegenerate)
    (u : V) (hu : u ≠ 0) (f : Module.Dual ℝ V) (hf : f ≠ 0)
    (hg : ∀ v w, B (v + f v • u) (w + f w • u) = B v w) :
    f u = -2 ∧ B u u ≠ 0 ∧
      ∀ v, v + f v • u = Module.preReflection u ((2 / B u u) • B u) v := by
  obtain ⟨v, hv⟩ : ∃ v, f v = 1 := by
    have hex : ∃ w, f w ≠ 0 := by
      by_contra! h
      exact hf (LinearMap.ext h)
    obtain ⟨w, hw⟩ := hex
    exact ⟨(f w)⁻¹ • w, by simp [hw]⟩
  have hz (z : V) (h : f z = 0) : B u z = 0 := by
    have h' := hg v z
    simpa [hv, h, map_add] using h'
  have hprop (z : V) : B u z = f z * B u v := by
    have h := hz (z - f z • v) (by simp [hv])
    exact sub_eq_zero.mp (by simpa [map_sub, map_smul] using h)
  have hc : B u v ≠ 0 := by
    intro h
    apply hu
    exact hn.1 u (fun z => by rw [hprop z, h, mul_zero])
  have hself := hg v v
  simp only [hv, one_smul, map_add, LinearMap.add_apply] at hself
  rw [hs.eq v u] at hself
  have hfu : f u = -2 := by
    rw [hprop u] at hself
    apply (mul_right_cancel₀ hc)
    linarith
  have hne : B u u ≠ 0 := by
    rw [hprop u, hfu]
    exact mul_ne_zero (by norm_num) hc
  refine ⟨hfu, hne, fun z => ?_⟩
  rw [Module.preReflection_apply]
  have heq : ((2 / B u u) • B u) z = -f z := by
    simp only [LinearMap.smul_apply, smul_eq_mul]
    rw [hprop z, hprop u, hfu]
    field_simp [hc]
  rw [heq, neg_smul, sub_neg_eq_add]

/-- This is the rank-one assertion in `bg:realization` stated without a chosen
rank-one normal form. Its conclusion uses the library's actual reflection. -/
theorem orthogonal_finrank_one
    (B : LinearMap.BilinForm ℝ V) (hs : B.IsSymm) (hn : B.Nondegenerate)
    (g : V ≃ₗ[ℝ] V) (hg : ∀ v w, B (g v) (g w) = B v w)
    (hr : Module.finrank ℝ (LinearMap.range (g.toLinearMap - LinearMap.id)) = 1) :
    ∃ u : V, B u u ≠ 0 ∧
      ∀ v, g v = Module.preReflection u ((2 / B u u) • B u) v := by
  let d : V →ₗ[ℝ] V := g.toLinearMap - LinearMap.id
  obtain ⟨e⟩ := nonempty_linearEquiv_of_finrank_eq_one hr
  let u : V := (e 1).val
  let f : Module.Dual ℝ V := e.symm.toLinearMap.comp d.rangeRestrict
  have hu : u ≠ 0 := by
    intro h
    have : e 1 = 0 := Subtype.ext h
    have := e.injective (this.trans e.map_zero.symm)
    norm_num at this
  have hform (v : V) : f v • u = d v := by
    change f v • (e 1).val = d v
    have h := congrArg Subtype.val (e.apply_symm_apply (d.rangeRestrict v))
    have he : e (f v) = f v • e 1 := by
      rw [← map_smul, smul_eq_mul, mul_one]
    rw [show e.symm (d.rangeRestrict v) = f v from rfl, he] at h
    exact h
  have hf : f ≠ 0 := by
    intro h
    obtain ⟨v, hv⟩ := (e 1).property
    have hh := hform v
    rw [h, LinearMap.zero_apply, zero_smul, hv] at hh
    exact hu hh.symm
  have hgform (v : V) : g v = v + f v • u := by
    rw [hform]
    change g v = v + (g v - v)
    abel
  obtain ⟨_, hnonzero, hreflection⟩ := orthogonal_rank_one_form B hs hn u hu f hf
    (fun v w => by rw [← hgform, ← hgform]; exact hg v w)
  exact ⟨u, hnonzero, fun v => (hgform v).trans (hreflection v)⟩
end KLInvariance.Realization

/-! The finite Coxeter relations for the actual real geometric reflection
operators required in `bg:realization`. Faithfulness is not assumed or claimed. -/

namespace KLInvariance.Realization
open Module
variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The moving subspace of a genuine reflection is exactly its root line. -/
theorem range_reflection_sub_id (e : V) (f : Module.Dual ℝ V) (h : f e = 2) :
    LinearMap.range ((Module.reflection h).toLinearMap - LinearMap.id) =
      Submodule.span ℝ {e} := by
  apply le_antisymm
  · rintro z ⟨v, rfl⟩
    apply Submodule.mem_span_singleton.mpr
    refine ⟨-f v, ?_⟩
    simp only [LinearMap.sub_apply, LinearEquiv.coe_coe, LinearMap.id_apply,
      Module.reflection_apply, neg_smul]
    abel
  · apply Submodule.span_le.mpr
    intro z hz
    have hz' : z = e := Set.mem_singleton_iff.mp hz
    rw [hz']
    refine ⟨(- (1 / 2 : ℝ)) • e, ?_⟩
    simp only [LinearMap.sub_apply, LinearEquiv.coe_coe, LinearMap.id_apply,
      Module.reflection_apply, map_smul, h]
    module

end KLInvariance.Realization

/-! Coordinate-dual geometric action. This exists in arbitrary rank and is
used only to prove the finite standard-parabolic reduction of the main goal. -/

/-! Construction of the source's geometric reflection schedule. The moment
curve avoids every forbidden hyperplane of a countable root set, using only
finite polynomial root sets and uncountability of the real field. -/

end

end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_ReflectionSchedules
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Reflection schedules, decreasing paths, root-space and edge algebra, and dihedral path recursions.
-/

section

namespace KLInvariance.EdgeAlgebra
open Module
universe u v
variable {k : Type u} [Field k] {V : Type v} [AddCommGroup V] [Module k V]
noncomputable section

theorem symmetric_ι_injective : Function.Injective (SymmetricAlgebra.ι k V) := by
  apply LinearMap.ker_eq_bot.mp
  apply eq_bot_iff.mpr
  intro v hv
  change v = 0
  by_contra hn
  obtain ⟨f,hf⟩ := Module.Projective.exists_dual_ne_zero k hn
  have h := congrArg (SymmetricAlgebra.lift f) (LinearMap.mem_ker.mp hv)
  rw [SymmetricAlgebra.lift_ι_apply,map_zero] at h
  exact hf h


end
end KLInvariance.EdgeAlgebra

/-! NEW GRAPH CLOSURE -/

namespace KLInvariance
universe u

/-- The entirely unlabelled closure used in graph reconstruction. Its
completeness for Bruhat graphs is a separate obligation; this definition
neither changes Bruhat order nor defines the R/KL polynomials. -/
inductive DiamondEdges {X : Type u} [PartialOrder X] : X → X → Prop
  | cover {x y : X} : x ⋖ y → DiamondEdges x y
  | diamond {x a b c d z : X} :
      DiamondEdges x a → DiamondEdges x b →
      DiamondEdges a c → DiamondEdges a d →
      DiamondEdges b c → DiamondEdges b d →
      DiamondEdges c z → DiamondEdges d z →
      a ≠ b → c ≠ d → DiamondEdges x z

 theorem DiamondEdges.map {X Y : Type*} [PartialOrder X] [PartialOrder Y]
    (e : X ≃o Y) {x y : X} (h : DiamondEdges x y) : DiamondEdges (e x) (e y) := by
  induction h with
  | cover h => exact DiamondEdges.cover ((apply_covBy_apply_iff e).mpr h)
  | diamond _ _ _ _ _ _ _ _ hab hcd hxa hxb hac had hbc hbd hcz hdz =>
    exact DiamondEdges.diamond hxa hxb hac had hbc hbd hcz hdz
      (fun he => hab (e.injective he)) (fun he => hcd (e.injective he))

 theorem DiamondEdges.map_iff {X Y : Type*} [PartialOrder X] [PartialOrder Y]
    (e : X ≃o Y) {x y : X} : DiamondEdges (e x) (e y) ↔ DiamondEdges x y := by
  constructor
  · intro h
    simpa only [OrderIso.symm_apply_apply] using h.map e.symm
  · exact DiamondEdges.map e

end KLInvariance


end

end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_GradedSheaves
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Graded moment-graph sheaves, boundary sections, graded covers and morphisms.
-/


section

namespace KLInvariance.QuotientEdge
variable {R M N E F : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup E] [Module R E] [AddCommGroup F] [Module R F]

/-- The edge isomorphism forced by an upper stalk isomorphism and exact quotient maps. -/
noncomputable def iso (f : M →ₗ[R] E) (g : N →ₗ[R] F)
    (hf : Function.Surjective f) (hg : Function.Surjective g)
    (h : M ≃ₗ[R] N) (hk : (LinearMap.ker f).map h.toLinearMap = LinearMap.ker g) : E ≃ₗ[R] F :=
  (f.quotKerEquivOfSurjective hf).symm.trans
    ((Submodule.Quotient.equiv _ _ h hk).trans (g.quotKerEquivOfSurjective hg))

end KLInvariance.QuotientEdge

end


end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_MinimalExtensions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Minimal-boundary extension sheaves, graded splittings and sheaf decomposition.
-/


section

namespace KLInvariance.MomentGraph.Sheaf
universe u v w z
variable {R : Type u}
  [CommRing R]
  {V : Type v}
  [PartialOrder V]
  {E : Type w}

noncomputable def addZeroRight (M N : Type z) [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [Subsingleton N] : M ≃ₗ[R] M × N where
  toFun m := (m,0)
  invFun := Prod.fst
  left_inv _ := rfl
  right_inv _ := Prod.ext rfl (Subsingleton.elim _ _)
  map_add' _ _ := Prod.ext rfl (zero_add _).symm
  map_smul' _ _ := Prod.ext rfl (smul_zero _).symm

@[simp] lemma addZeroRight_apply (M N : Type z) [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [Subsingleton N] (m : M) :
    addZeroRight (R := R) M N m = (m,0) := rfl

end KLInvariance.MomentGraph.Sheaf

end


section

/-! Pullback along a directed graph map. Relative-order flabbiness requires
only outgoing completeness for the surviving edges, not equality of the two
orders on a coset. -/
namespace KLInvariance.MomentGraph
universe ur uv ue uw uf um
variable {V : Type uv} [PartialOrder V] {E : Type ue}
  {W : Type uw} [PartialOrder W] {F : Type uf}

namespace Sheaf
variable {R : Type ur}
  [CommRing R]
noncomputable section

 def moduleEq {M N : ModuleCat.{um} R} (h : M=N) : M ≃ₗ[R] N := h ▸ LinearEquiv.refl R M

 theorem moduleEq_apply {X : Type*} (M : X → ModuleCat.{um} R) {x y : X} (h : x=y)
    (s : ∀ z, M z) : moduleEq (congrArg M h) (s x) = s y := by subst y; rfl

end
end Sheaf
end KLInvariance.MomentGraph

end


end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_SheafMorphisms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Graded sheaf morphisms, exact section constructions and character sums.
-/


section

namespace KLInvariance.QuotientEdge
variable {R M N E F : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup E] [Module R E] [AddCommGroup F] [Module R F]
noncomputable section

 def descend (f : M →ₗ[R] E) (g : N →ₗ[R] F)
    (hf : Function.Surjective f) (h : M →ₗ[R] N)
    (hk : LinearMap.ker f ≤ LinearMap.ker (g.comp h)) : E →ₗ[R] F :=
  ((LinearMap.ker f).liftQ (g.comp h) hk).comp (f.quotKerEquivOfSurjective hf).symm.toLinearMap

 theorem descend_apply (f : M →ₗ[R] E) (g : N →ₗ[R] F)
    (hf : Function.Surjective f) (h : M →ₗ[R] N)
    (hk : LinearMap.ker f ≤ LinearMap.ker (g.comp h)) (v : M) :
    descend f g hf h hk (f v) = g (h v) := by
  simp [descend]

 theorem kernel_scalar_le (f : M →ₗ[R] E) (g : N →ₗ[R] F) (r : R)
    (hf : ∀ v, f v = 0 ↔ ∃ w, v=r • w)
    (hg : ∀ v, g v = 0 ↔ ∃ w, v=r • w) (h : M →ₗ[R] N) :
    LinearMap.ker f ≤ LinearMap.ker (g.comp h) := by
  intro v hv
  obtain ⟨w,rfl⟩ := (hf v).mp hv
  change g (h (r • w))=0
  rw [h.map_smul]
  exact (hg _).mpr ⟨h w,rfl⟩

end
end KLInvariance.QuotientEdge

end


end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_Decomposition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Graded decomposition characters, reflection-plane algebras and reflection Frobenius structures.
-/


section

/-! Integral pair-projection quotients. The purpose is the actual localization
functor from a tensor bimodule to a moment-graph sheaf; no flabbiness, stalk
freeness, BMP identification or character theorem is assumed or asserted. -/
namespace KLInvariance.PairProjection
universe u v w z
variable {R : Type u} [CommRing R]
  {M : Type v} [AddCommGroup M] [Module R M]
  {X : Type w} [AddCommGroup X] [Module R X]
  {Y : Type z} [AddCommGroup Y] [Module R Y]
  (f : M →ₗ[R] X) (g : M →ₗ[R] Y)
noncomputable section

def relation : Submodule R (X × Y) := LinearMap.range (f.prod g)
abbrev Edge := (X × Y) ⧸ relation f g

def lower : X →ₗ[R] Edge f g := (relation f g).mkQ.comp (LinearMap.inl R X Y)
def upper : Y →ₗ[R] Edge f g := -((relation f g).mkQ.comp (LinearMap.inr R X Y))

theorem diagonal_zero (m : M) : (relation f g).mkQ (f m,g m)=0 := by
  exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨m,rfl⟩

theorem compatible (m : M) : lower f g (f m)=upper f g (g m) := by
  have h := diagonal_zero f g m
  have hp : (f m,g m)=(f m,0)+(0,g m) := by simp
  rw [hp,map_add] at h
  exact eq_neg_of_add_eq_zero_left h

theorem compatible_iff (x : X) (y : Y) :
    lower f g x=upper f g y ↔ ∃ m : M, f m=x ∧ g m=y := by
  change (relation f g).mkQ (x,0) = -((relation f g).mkQ (0,y)) ↔ _
  rw [eq_neg_iff_add_eq_zero,← map_add]
  rw [show ((x,0)+(0,y) : X × Y)=(x,y) by simp]
  change (Submodule.Quotient.mk (x,y) : Edge f g)=0 ↔ _
  rw [Submodule.Quotient.mk_eq_zero]
  constructor
  · rintro ⟨m,hm⟩
    exact ⟨m,congrArg Prod.fst hm,congrArg Prod.snd hm⟩
  · rintro ⟨m,hm,hn⟩
    exact ⟨m,Prod.ext hm hn⟩

theorem kernel_lower (x : X) : lower f g x=0 ↔ ∃ m : M, f m=x ∧ g m=0 := by
  change (relation f g).mkQ (x,0)=0 ↔ _
  change Submodule.Quotient.mk (x,0) = 0 ↔ _
  rw [Submodule.Quotient.mk_eq_zero]
  constructor
  · rintro ⟨m,hm⟩
    exact ⟨m,congrArg Prod.fst hm,congrArg Prod.snd hm⟩
  · rintro ⟨m,hm,hn⟩
    exact ⟨m,Prod.ext hm hn⟩

theorem lower_surjective (hg : Function.Surjective g) :
    Function.Surjective (lower f g) := by
  intro v
  obtain ⟨⟨x,y⟩,rfl⟩ := (relation f g).mkQ_surjective v
  obtain ⟨m,rfl⟩ := hg y
  refine ⟨x-f m,?_⟩
  change (relation f g).mkQ (x-f m,0) = (relation f g).mkQ (x,g m)
  have hp : (x-f m,0)=(x,g m)-(f m,g m) := by simp
  rw [hp,map_sub,diagonal_zero,sub_zero]

theorem upper_surjective (hf : Function.Surjective f) :
    Function.Surjective (upper f g) := by
  intro v
  obtain ⟨⟨x,y⟩,rfl⟩ := (relation f g).mkQ_surjective v
  obtain ⟨m,rfl⟩ := hf x
  refine ⟨g m-y,?_⟩
  change -((relation f g).mkQ (0,g m-y)) = (relation f g).mkQ (f m,y)
  have hp : (0,g m-y)=(f m,g m)-(f m,y) := by simp
  rw [hp,map_sub,diagonal_zero,zero_sub,neg_neg]

/-- A genuine right-action eigenvalue difference annihilates the edge
quotient. This uses only the integral module, not a fraction-field equality. -/
theorem difference_annihilates (hf : Function.Surjective f)
    (hg : Function.Surjective g) (T : M →ₗ[R] M) (r s : R)
    (hr : ∀ m, f (T m)=r • f m) (hs : ∀ m, g (T m)=s • g m)
    (v : Edge f g) : (r-s) • v=0 := by
  obtain ⟨x,rfl⟩ := lower_surjective f g hg v
  rw [← map_smul]
  apply (kernel_lower f g _).mpr
  obtain ⟨m,rfl⟩ := hf x
  refine ⟨T m-s • m,?_,?_⟩
  · rw [map_sub,map_smul,hr,sub_smul]
  · rw [map_sub,map_smul,hs,sub_self]

end
end KLInvariance.PairProjection

end


section

/-! Rank-two Frobenius extension for an actual reflection on a symmetric
algebra. This supplies the elementary simple-reflection duality input; it
is not a proof of BMP or Elias--Williamson self-duality/characters. -/
namespace KLInvariance.ReflectionFrobenius
universe uk ua uv
variable {k : Type uk} [Field k] [CharZero k]
  {A : Type ua} [CommRing A] [IsDomain A] [Algebra k A]

noncomputable section

def fixed (τ : A ≃ₐ[k] A) : Subalgebra k A :=
  AlgHom.equalizer τ.toAlgHom (AlgHom.id k A)

omit [CharZero k] [IsDomain A] in
@[simp] theorem mem_fixed (τ : A ≃ₐ[k] A) (a : A) :
    a ∈ fixed τ ↔ τ a = a := Iff.rfl

omit [CharZero k] [IsDomain A] in
 theorem fixed_val (τ : A ≃ₐ[k] A) (a : fixed τ) : τ (a : A) = a := a.property

variable (τ : A ≃ₐ[k] A) (α : A)

def expand : (fixed τ × fixed τ) →ₗ[fixed τ] A where
  toFun a := (a.1 : A) + α * (a.2 : A)
  map_add' a b := by simp; ring
  map_smul' c a := by simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
    Subalgebra.coe_mul, Subalgebra.smul_def, RingHom.id_apply]; ring

omit [CharZero k] [IsDomain A] in
@[simp] theorem expand_apply (a : fixed τ × fixed τ) :
    expand τ α a = (a.1 : A) + α * (a.2 : A) := rfl

variable (hinv : Function.Involutive τ) (hα : α ≠ 0) (hanti : τ α = -α)
  (hdiv : ∀ a : A, α ∣ a - τ a)

omit [CharZero k] in
include hinv hα hanti in
 theorem quotient_fixed {a d : A} (hd : a - τ a = α * d) : τ d = d := by
  have hh := congrArg τ hd
  simp only [map_sub, map_mul, hinv a, hanti] at hh
  apply mul_left_cancel₀ hα
  linear_combination hh + hd

include hα hanti in
 theorem expand_injective : Function.Injective (expand τ α) := by
  intro a b hab
  have ht := congrArg τ hab
  simp only [expand_apply, map_add, map_mul, fixed_val, hanti] at ht
  have he : (2 : A) * α * ((a.2 : A) - (b.2 : A)) = 0 := by
    simp only [expand_apply] at hab
    linear_combination hab - ht
  have htwo : (2 : A) ≠ 0 := by
    have hi : Function.Injective (algebraMap k A) := (algebraMap k A).injective
    exact fun h => two_ne_zero (hi (by simpa only [map_ofNat, map_zero] using h : algebraMap k A (2:k) = algebraMap k A 0))
  have h2 : (a.2 : A) = (b.2 : A) := sub_eq_zero.mp
    ((mul_eq_zero.mp he).resolve_left (mul_ne_zero htwo hα))
  have h1 : (a.1 : A) = (b.1 : A) := by
    simpa only [expand_apply, h2, add_left_inj] using hab
  exact Prod.ext (Subtype.ext h1) (Subtype.ext h2)

include hinv hα hanti hdiv in
 theorem expand_surjective : Function.Surjective (expand τ α) := by
  intro a
  obtain ⟨d, hd⟩ := hdiv a
  have hdf : τ d = d := quotient_fixed τ α hinv hα hanti hd
  let h : k := (2:k)⁻¹
  have htwo : (2:A) * algebraMap k A h = 1 := by
    rw [show (2:A) = algebraMap k A (2:k) by exact (map_ofNat (algebraMap k A) 2).symm, ← map_mul]
    simp [h]
  let c₀ : fixed τ := ⟨algebraMap k A h * (a + τ a), by
    simp only [mem_fixed, map_mul, AlgEquiv.commutes, map_add, hinv a]
    ring⟩
  let c₁ : fixed τ := ⟨algebraMap k A h * d, by
    simp only [mem_fixed, map_mul, AlgEquiv.commutes, hdf]⟩
  refine ⟨(c₀,c₁), ?_⟩
  change algebraMap k A h * (a + τ a) + α * (algebraMap k A h * d) = a
  linear_combination a * htwo - (algebraMap k A h) * hd

/-- The actual invariant-ring basis `1, α`, with no finiteness assumption. -/
def coordinates : A ≃ₗ[fixed τ] (fixed τ × fixed τ) :=
  (LinearEquiv.ofBijective (expand τ α)
    ⟨expand_injective τ α hα hanti, expand_surjective τ α hinv hα hanti hdiv⟩).symm

@[simp] theorem expand_coordinates (a : A) :
    expand τ α (coordinates τ α hinv hα hanti hdiv a) = a :=
  (coordinates τ α hinv hα hanti hdiv).symm_apply_apply a

@[simp] theorem coordinates_expand (a : fixed τ × fixed τ) :
    coordinates τ α hinv hα hanti hdiv (expand τ α a) = a :=
  (coordinates τ α hinv hα hanti hdiv).apply_symm_apply a


def trace : A →ₗ[fixed τ] fixed τ :=
  (LinearMap.snd _ _ _).comp (coordinates τ α hinv hα hanti hdiv).toLinearMap

 theorem trace_expand (a : fixed τ × fixed τ) :
    trace τ α hinv hα hanti hdiv (expand τ α a) = a.2 := by
  change (coordinates τ α hinv hα hanti hdiv (expand τ α a)).2 = a.2
  rw [coordinates_expand]

omit [CharZero k] [IsDomain A] in
include hanti in
 theorem square_fixed : α * α ∈ fixed τ := by
  simp only [mem_fixed, map_mul, hanti, neg_mul_neg]

 theorem trace_mul (a b : A) :
    trace τ α hinv hα hanti hdiv (a*b) =
      (coordinates τ α hinv hα hanti hdiv a).1 *
        (coordinates τ α hinv hα hanti hdiv b).2 +
      (coordinates τ α hinv hα hanti hdiv a).2 *
        (coordinates τ α hinv hα hanti hdiv b).1 := by
  let c := coordinates τ α hinv hα hanti hdiv a
  let d := coordinates τ α hinv hα hanti hdiv b
  let α₂ : fixed τ := ⟨α*α, square_fixed τ α hanti⟩
  have he : a*b = expand τ α
      (c.1*d.1+α₂*c.2*d.2, c.1*d.2+c.2*d.1) := by
    rw [← expand_coordinates τ α hinv hα hanti hdiv a,
      ← expand_coordinates τ α hinv hα hanti hdiv b]
    change ((c.1:A)+α*(c.2:A))*((d.1:A)+α*(d.2:A)) =
      (c.1:A)*(d.1:A)+(α*α)*(c.2:A)*(d.2:A)+
        α*((c.1:A)*(d.2:A)+(c.2:A)*(d.1:A))
    ring
  rw [he,trace_expand]

section Pair
variable (R : Type*) [CommRing R]

def crossPair : (R × R) →ₗ[R] Module.Dual R (R × R) where
  toFun a :=
    { toFun := fun b => a.1*b.2+a.2*b.1
      map_add' := by intro b c; simp; ring
      map_smul' := by intro r b; simp; ring }
  map_add' := by intro a b; apply LinearMap.ext; intro c; simp; ring
  map_smul' := by intro r a; apply LinearMap.ext; intro b; simp; ring

 theorem crossPair_bijective : Function.Bijective (crossPair R) := by
  constructor
  · intro a b hab
    have h₁ := congrArg (fun f : Module.Dual R (R×R) => f (0,1)) hab
    have h₂ := congrArg (fun f : Module.Dual R (R×R) => f (1,0)) hab
    exact Prod.ext (by simpa [crossPair] using h₁) (by simpa [crossPair] using h₂)
  · intro f
    refine ⟨(f (0,1), f (1,0)), ?_⟩
    apply LinearMap.ext
    intro a
    have ha : a = a.1 • (1,0) + a.2 • (0,1) := by simp
    change f (0,1)*a.2 + f (1,0)*a.1 = f a
    calc
      _ = a.1 * f (1,0) + a.2 * f (0,1) := by ring
      _ = f (a.1 • (1,0) + a.2 • (0,1)) := by rw [map_add,map_smul,map_smul]; rfl
      _ = f a := congrArg f ha.symm

def crossPairEquiv : (R × R) ≃ₗ[R] Module.Dual R (R × R) :=
  LinearEquiv.ofBijective (crossPair R) (crossPair_bijective R)

end Pair

/-- The Frobenius duality over the invariant ring is integral and perfect. -/
def duality : A ≃ₗ[fixed τ] Module.Dual (fixed τ) A :=
  (coordinates τ α hinv hα hanti hdiv).trans
    ((crossPairEquiv (fixed τ)).trans
      (coordinates τ α hinv hα hanti hdiv).dualMap)

 theorem duality_apply (a b : A) :
    duality τ α hinv hα hanti hdiv a b = trace τ α hinv hα hanti hdiv (a*b) := by
  rw [trace_mul]
  rfl


section Symmetric
variable {V : Type uv} [AddCommGroup V] [Module k V]

def symmetricMap (e : V ≃ₗ[k] V) : SymmetricAlgebra k V →ₐ[k] SymmetricAlgebra k V :=
  SymmetricAlgebra.lift ((SymmetricAlgebra.ι k V).comp e.toLinearMap)

omit [CharZero k] in
@[simp] theorem symmetricMap_ι (e : V ≃ₗ[k] V) (v : V) :
    symmetricMap e (SymmetricAlgebra.ι k V v) = SymmetricAlgebra.ι k V (e v) := by
  simp [symmetricMap]

omit [CharZero k] in
 theorem symmetricMap_comp (e d : V ≃ₗ[k] V) :
    (symmetricMap d).comp (symmetricMap e) = symmetricMap (e.trans d) := by
  apply SymmetricAlgebra.algHom_ext
  ext v
  simp

omit [CharZero k] in
 theorem symmetricMap_refl : symmetricMap (LinearEquiv.refl k V) =
    AlgHom.id k (SymmetricAlgebra k V) := by
  apply SymmetricAlgebra.algHom_ext
  ext v
  simp

/-- The algebra action is induced by the linear reflection, not postulated. -/
def symmetricAction (e : V ≃ₗ[k] V) : SymmetricAlgebra k V ≃ₐ[k] SymmetricAlgebra k V :=
  AlgEquiv.ofAlgHom (symmetricMap e) (symmetricMap e.symm)
    (by rw [symmetricMap_comp,LinearEquiv.symm_trans_self,symmetricMap_refl])
    (by rw [symmetricMap_comp,LinearEquiv.self_trans_symm,symmetricMap_refl])

omit [CharZero k] in
@[simp] theorem symmetricAction_ι (e : V ≃ₗ[k] V) (v : V) :
    symmetricAction e (SymmetricAlgebra.ι k V v) = SymmetricAlgebra.ι k V (e v) :=
  symmetricMap_ι e v

variable (root : V) (coroot : Module.Dual k V) (hroot : coroot root = 2)

abbrev reflectionAction : SymmetricAlgebra k V ≃ₐ[k] SymmetricAlgebra k V :=
  symmetricAction (Module.reflection hroot)

omit [CharZero k] in
 theorem reflectionAction_involutive : Function.Involutive (reflectionAction root coroot hroot) := by
  intro a
  have he : (reflectionAction root coroot hroot).toAlgHom.comp
      (reflectionAction root coroot hroot).toAlgHom =
        AlgHom.id k (SymmetricAlgebra k V) := by
    apply SymmetricAlgebra.algHom_ext
    ext v
    simp [Module.involutive_reflection hroot v]
  exact congrArg (fun f : SymmetricAlgebra k V →ₐ[k] SymmetricAlgebra k V => f a) he

omit [CharZero k] in
 theorem reflectionAction_anti :
    reflectionAction root coroot hroot (SymmetricAlgebra.ι k V root) =
      -SymmetricAlgebra.ι k V root := by
  simp

include hroot in
 theorem reflectionRoot_ne_zero : SymmetricAlgebra.ι k V root ≠ 0 := by
  intro he
  have hh := congrArg (SymmetricAlgebra.lift coroot) he
  rw [SymmetricAlgebra.lift_ι_apply,map_zero,hroot] at hh
  exact two_ne_zero hh

omit [CharZero k] in
 theorem reflectionAction_divisible (a : SymmetricAlgebra k V) :
    SymmetricAlgebra.ι k V root ∣ a-reflectionAction root coroot hroot a := by
  induction a using SymmetricAlgebra.induction with
  | algebraMap c => simp
  | ι v =>
    refine ⟨algebraMap k (SymmetricAlgebra k V) (coroot v), ?_⟩
    rw [reflectionAction,symmetricAction_ι,Module.reflection_apply,map_sub,map_smul]
    simp only [sub_sub_cancel,Algebra.smul_def]
    ring
  | mul a b ha hb =>
    obtain ⟨c,hc⟩ := ha
    obtain ⟨d,hd⟩ := hb
    refine ⟨c*b+(reflectionAction root coroot hroot a)*d, ?_⟩
    rw [map_mul]
    linear_combination b*hc+(reflectionAction root coroot hroot a)*hd
  | add a b ha hb =>
    simpa only [map_add, add_sub_add_comm] using dvd_add ha hb

end Symmetric

end
end KLInvariance.ReflectionFrobenius

end


end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_Frobenius
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Coxeter Frobenius extensions, tensor duality and translation across reflection pairs.
-/


section

/-! Integral restriction and extension of perfect pairings for a genuine
Frobenius extension. This supplies the duality operation used by
Bott--Samelson translation, not an assumed duality on a BMP sheaf. -/
namespace KLInvariance.FrobeniusDuality
open Module TensorProduct
universe ur ua um
variable {R : Type ur} [CommRing R] {A : Type ua} [CommRing A] [Algebra R A]
  (tr : A →ₗ[R] R) (d : A ≃ₗ[R] Dual R A)
  (hd : ∀ a b, d a b = tr (a*b))
  (M : Type um) [AddCommGroup M] [Module A M] [Module R M] [IsScalarTower R A M]
noncomputable section

 def restrictDual : Dual A M →ₗ[R] Dual R M where
  toFun f := tr.comp (f.restrictScalars R)
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

 def fiber (f : Dual R M) (m : M) : Dual R A :=
  f.comp ((LinearMap.toSpanSingleton A M m).restrictScalars R)

@[simp] theorem fiber_apply (f : Dual R M) (m : M) (a : A) :
    fiber M f m a = f (a • m) := rfl

include hd in
 theorem trace_recover_fiber (f : Dual R M) (m : M) (a : A) :
    tr (d.symm (fiber M f m) * a) = f (a • m) := by
  rw [← hd,d.apply_symm_apply,fiber_apply]

include hd in
 theorem recover_fiber_smul (f : Dual R M) (m : M) (a : A) :
    d.symm (fiber M f (a • m)) = a * d.symm (fiber M f m) := by
  apply d.injective
  apply LinearMap.ext
  intro b
  rw [d.apply_symm_apply,hd,fiber_apply]
  have he : a * d.symm (fiber M f m) * b = d.symm (fiber M f m) * (b*a) := by ring
  rw [he,trace_recover_fiber tr d hd]
  simp only [mul_smul]

 def recoverDual (f : Dual R M) : Dual A M where
  toFun m := d.symm (fiber M f m)
  map_add' m n := by
    apply d.injective
    rw [map_add,d.apply_symm_apply,d.apply_symm_apply,d.apply_symm_apply]
    ext a
    simp [smul_add]
  map_smul' a m := by
    simpa only [RingHom.id_apply,smul_eq_mul] using recover_fiber_smul tr d hd M f m a

@[simp] theorem recoverDual_apply (f : Dual R M) (m : M) :
    recoverDual tr d hd M f m = d.symm (fiber M f m) := rfl

 theorem restrict_recover (f : Dual R M) :
    restrictDual tr M (recoverDual tr d hd M f) = f := by
  ext m
  change tr (d.symm (fiber M f m)) = f m
  simpa only [mul_one,one_smul] using trace_recover_fiber tr d hd M f m 1

 theorem recover_restrict (f : Dual A M) :
    recoverDual tr d hd M (restrictDual tr M f) = f := by
  ext m
  apply d.injective
  change d (d.symm _) = d (f m)
  rw [d.apply_symm_apply]
  ext a
  change tr (f (a • m)) = d (f m) a
  rw [map_smul,smul_eq_mul,hd,mul_comm]

 def restrictionEquiv : Dual A M ≃ₗ[R] Dual R M :=
  LinearEquiv.ofBijective (restrictDual tr M)
    ⟨fun f g h => by
      have hh := congrArg (recoverDual tr d hd M) h
      simpa only [recover_restrict] using hh,
    fun f => ⟨recoverDual tr d hd M f,restrict_recover tr d hd M f⟩⟩

/-- Restricting an integral perfect pairing along a Frobenius trace is again
integral and perfect; no localization or fraction-field argument is used. -/
 def restrictPairing (p : M ≃ₗ[A] Dual A M) : M ≃ₗ[R] Dual R M :=
  (p.restrictScalars R).trans (restrictionEquiv tr d hd M)

 theorem restrictPairing_apply (p : M ≃ₗ[A] Dual A M) (m n : M) :
    restrictPairing tr d hd M p m n = tr (p m n) := rfl

end
end KLInvariance.FrobeniusDuality

namespace KLInvariance.FrobeniusDuality
open Module TensorProduct
universe ur ua um
variable {R : Type ur} [CommRing R] (A : Type ua) [CommRing A] [Algebra R A]
  {M : Type um} [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]
noncomputable section

 def extendPairing (p : M ≃ₗ[R] Dual R M) :
    (A ⊗[R] M) ≃ₗ[A] Dual A (A ⊗[R] M) :=
  (p.baseChange R A M (Dual R M)).trans
    (TensorProduct.isBaseChange (R := R) (S := A) (M := M)).toDualBaseChange

 theorem extendPairing_tmul (p : M ≃ₗ[R] Dual R M) (a b : A) (m n : M) :
    extendPairing A p (a ⊗ₜ[R] m) (b ⊗ₜ[R] n) =
      a * b * algebraMap R A (p m n) := by
  have hn : b ⊗ₜ[R] n = b • (1 ⊗ₜ[R] n) := by simp only [smul_tmul',smul_eq_mul,mul_one]
  rw [hn,map_smul]
  change b * ((TensorProduct.isBaseChange (R := R) (S := A) (M := M)).toDualBaseChange
    (a ⊗ₜ[R] p m) ((TensorProduct.mk R A M 1) n)) = _
  rw [IsBaseChange.toDualBaseChange_tmul]
  ring

end
end KLInvariance.FrobeniusDuality

end


section

/-! Tensor induction of integral self-dual bimodules across a Frobenius
extension. All pairings refer to actual integral modules. -/
namespace KLInvariance.FrobeniusDuality
open Module TensorProduct
universe ur ua um
noncomputable section

structure PairedModule (A : Type ua) [CommRing A] where
  carrier : Type um
  [add : AddCommGroup carrier]
  [module : Module A carrier]
  free : Module.Free A carrier
  finite : Module.Finite A carrier
  pairing : carrier ≃ₗ[A] Dual A carrier

attribute [instance] PairedModule.add PairedModule.module PairedModule.free PairedModule.finite
instance instCoeSortPairedModuleType {A : Type ua} [CommRing A] : CoeSort (PairedModule.{ua,um} A) (Type um) := ⟨PairedModule.carrier⟩

 def unitPairing (A : Type ua) [CommRing A] : A ≃ₗ[A] Dual A A where
  toFun a := LinearMap.mul A A a
  invFun f := f 1
  left_inv a := mul_one a
  right_inv f := by
    apply LinearMap.ext
    intro a
    change f 1 * a = f a
    rw [mul_comm,← smul_eq_mul,← map_smul,smul_eq_mul,mul_one]
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

 def unitModule (A : Type ua) [CommRing A] : PairedModule A where
  carrier := A
  free := inferInstance
  finite := inferInstance
  pairing := unitPairing A

variable {R : Type ur} [CommRing R] {A : Type ua} [CommRing A] [Algebra R A]
  [Module.Free R A] [Module.Finite R A]
  (tr : A →ₗ[R] R) (d : A ≃ₗ[R] Dual R A) (hd : ∀ a b, d a b = tr (a*b))
  (N : PairedModule.{ua,um} A)

local instance restrictedModule : Module R N := Module.compHom N (algebraMap R A)
local instance restrictedTower : IsScalarTower R A N := IsScalarTower.of_algebraMap_smul fun _ _ => rfl

 def restrictionBasis : Basis
    (Module.Free.ChooseBasisIndex R A × Module.Free.ChooseBasisIndex A N) R N :=
  (Module.Free.chooseBasis R A).smulTower (Module.Free.chooseBasis A N)

local instance restrictedFree : Module.Free R N := Module.Free.of_basis (restrictionBasis N)
local instance restrictedFinite : Module.Finite R N := Module.Finite.trans A N

 def inducedModule : PairedModule A where
  carrier := A ⊗[R] N
  free := inferInstance
  finite := inferInstance
  pairing := extendPairing A (restrictPairing tr d hd N N.pairing)

end
end KLInvariance.FrobeniusDuality

end


section

/-! Integral balanced duality under Bott--Samelson tensor induction. -/
namespace KLInvariance.FrobeniusDuality
open Module TensorProduct
universe ur ua um
noncomputable section

structure PairedBimodule (A : Type ua) [CommRing A] where
  obj : PairedModule.{ua,um} A
  right : A →+* End A obj
  balanced : ∀ a m n, obj.pairing (right a m) n = obj.pairing m (right a n)
  symmetric : ∀ m n, obj.pairing m n = obj.pairing n m

 def unitBimodule (A : Type ua) [CommRing A] : PairedBimodule A where
  obj := unitModule A
  right := Algebra.lmul A A |>.toRingHom
  balanced a m n := by
    change A at m n
    change (a*m)*n = m*(a*n)
    ring
  symmetric m n := by
    change A at m n
    exact mul_comm m n

variable {R : Type ur} [CommRing R] {A : Type ua} [CommRing A] [Algebra R A]
  [Module.Free R A] [Module.Finite R A]
  (tr : A →ₗ[R] R) (d : A ≃ₗ[R] Dual R A) (hd : ∀ a b, d a b = tr (a*b))
  (N : PairedModule.{ua,um} A)

attribute [local instance] restrictedModule restrictedTower restrictedFree restrictedFinite

 def restrictedRight (right : A →+* End A N) : A →+* End R N where
  toFun a := (right a).restrictScalars R
  map_one' := by ext m; change (right 1) m = m; rw [map_one]; rfl
  map_mul' a b := by
    ext m
    change (right (a*b)) m = (right a) ((right b) m)
    rw [map_mul]
    rfl
  map_zero' := by ext m; change (right 0) m = 0; rw [map_zero]; rfl
  map_add' a b := by ext m; change (right (a+b)) m = (right a) m + (right b) m; rw [map_add]; rfl

 def inducedRight (right : A →+* End A N) : A →+* End A (inducedModule tr d hd N) :=
  (Module.End.baseChangeHom R A N).toRingHom.comp (restrictedRight N right)

@[simp] theorem inducedRight_tmul (right : A →+* End A N) (r a : A) (m : N) :
    inducedRight tr d hd N right r (a ⊗ₜ[R] m) = a ⊗ₜ[R] right r m := rfl

 theorem inducedPairing_balanced (right : A →+* End A N)
    (hb : ∀ a m n, N.pairing (right a m) n = N.pairing m (right a n))
    (r : A) (m n : inducedModule tr d hd N) :
    (inducedModule tr d hd N).pairing (inducedRight tr d hd N right r m) n =
      (inducedModule tr d hd N).pairing m (inducedRight tr d hd N right r n) := by
  change A ⊗[R] N at m n
  change extendPairing A (restrictPairing tr d hd N N.pairing)
    (((right r).restrictScalars R).baseChange A m) n =
    extendPairing A (restrictPairing tr d hd N N.pairing) m
    (((right r).restrictScalars R).baseChange A n)
  induction m using OAI.tensorInductionOn with
  | add m₁ m₂ h₁ h₂ => simp only [map_add,LinearMap.add_apply,h₁,h₂]
  | tmul a m =>
    induction n using OAI.tensorInductionOn with
    | add n₁ n₂ h₁ h₂ => simp only [map_add,h₁,h₂]
    | tmul b n =>
      simp only [LinearMap.baseChange_tmul,extendPairing_tmul,restrictPairing_apply,
        LinearMap.restrictScalars_apply,hb]

 theorem inducedPairing_symmetric (hs : ∀ m n, N.pairing m n = N.pairing n m)
    (m n : inducedModule tr d hd N) :
    (inducedModule tr d hd N).pairing m n = (inducedModule tr d hd N).pairing n m := by
  change A ⊗[R] N at m n
  change extendPairing A (restrictPairing tr d hd N N.pairing) m n =
    extendPairing A (restrictPairing tr d hd N N.pairing) n m
  induction m using OAI.tensorInductionOn with
  | add m₁ m₂ h₁ h₂ => simp only [map_add,LinearMap.add_apply,h₁,h₂]
  | tmul a m =>
    induction n using OAI.tensorInductionOn with
    | add n₁ n₂ h₁ h₂ => simp only [map_add,LinearMap.add_apply,h₁,h₂]
    | tmul b n =>
      rw [extendPairing_tmul,extendPairing_tmul,restrictPairing_apply,restrictPairing_apply,hs,mul_comm a b]

 def inducedBimodule (N : PairedBimodule.{ua,um} A) : PairedBimodule A where
  obj := inducedModule tr d hd N.obj
  right := inducedRight tr d hd N.obj N.right
  balanced := inducedPairing_balanced tr d hd N.obj N.right N.balanced
  symmetric := inducedPairing_symmetric tr d hd N.obj N.symmetric

end
end KLInvariance.FrobeniusDuality

end


section

/-! The actual two-element homogeneous basis of a reflection Frobenius
extension. This basis is used in the tensor-defined Bott--Samelson modules. -/
namespace KLInvariance.ReflectionFrobenius
open Module
universe uk ua
variable {k : Type uk} [Field k] [CharZero k]
  {A : Type ua} [CommRing A] [IsDomain A] [Algebra k A]
  (τ : A ≃ₐ[k] A) (α : A) (hinv : Function.Involutive τ) (hα : α ≠ 0)
  (hanti : τ α = -α) (hdiv : ∀ a : A, α ∣ a-τ a)
noncomputable section

 def reflectionBasis : Basis (Fin 2) (fixed τ) A :=
  (Basis.finTwoProd (fixed τ)).map (coordinates τ α hinv hα hanti hdiv).symm

 theorem reflectionBasis_zero : reflectionBasis τ α hinv hα hanti hdiv 0 = 1 := by
  change expand τ α (Basis.finTwoProd (fixed τ) 0) = 1
  simp [expand_apply]

 theorem reflectionBasis_one : reflectionBasis τ α hinv hα hanti hdiv 1 = α := by
  change expand τ α (Basis.finTwoProd (fixed τ) 1) = α
  simp [expand_apply]

end
end KLInvariance.ReflectionFrobenius

end


section

/-! Homogeneous integral Bott--Samelson pairing at the genuine tensor basis.
No indecomposable summand or character identity is postulated here. -/
namespace KLInvariance.FrobeniusDuality
open Module TensorProduct ReflectionFrobenius
universe uk ua um ui
variable {k : Type uk} [Field k] [CharZero k]
  {A : Type ua} [CommRing A] [IsDomain A] [Algebra k A]
  (τ : A ≃ₐ[k] A) (α : A) (hinv : Function.Involutive τ) (hα : α ≠ 0)
  (hanti : τ α = -α) (hdiv : ∀ a : A, α ∣ a-τ a)
noncomputable section

variable [Module.Free (fixed τ) A] [Module.Finite (fixed τ) A]

variable (N : PairedModule.{ua,um} A)
  {ι : Type ui} (b : Basis ι A N)
attribute [local instance] restrictedModule restrictedTower restrictedFree restrictedFinite

 def inducedBasis : Basis (Fin 2 × ι) A
    (inducedModule (trace τ α hinv hα hanti hdiv)
      (duality τ α hinv hα hanti hdiv) (duality_apply τ α hinv hα hanti hdiv) N) :=
  ((reflectionBasis τ α hinv hα hanti hdiv).smulTower b).baseChange A

 theorem inducedBasis_apply (i : Fin 2) (j : ι) :
    inducedBasis τ α hinv hα hanti hdiv N b (i,j) =
      (1:A) ⊗ₜ[fixed τ] (reflectionBasis τ α hinv hα hanti hdiv i • b j) := by
  change (((reflectionBasis τ α hinv hα hanti hdiv).smulTower b).baseChange A) (i,j) = _
  rw [Basis.baseChange_apply,Basis.smulTower_apply]

end
end KLInvariance.FrobeniusDuality

end


section

namespace KLInvariance.ReflectionFrobenius
open Module KLInvariance.Graded
universe uk uv us
variable {k : Type uk} [Field k] [CharZero k]
  {V : Type uv} [AddCommGroup V] [Module k V]
  {σ : Type us} [Fintype σ] (basis : Basis σ k V)
noncomputable section

 def polynomialLinear (v : V) : MvPolynomial σ k :=
  SymmetricAlgebra.equivMvPolynomial basis (SymmetricAlgebra.ι k V v)

 def polynomialAction (e : V ≃ₗ[k] V) : MvPolynomial σ k ≃ₐ[k] MvPolynomial σ k :=
  ((SymmetricAlgebra.equivMvPolynomial basis).symm.trans (symmetricAction e)).trans
    (SymmetricAlgebra.equivMvPolynomial basis)

omit [CharZero k] [Fintype σ] in
@[simp] theorem polynomialAction_linear (e : V ≃ₗ[k] V) (v : V) :
    polynomialAction basis e (polynomialLinear basis v) = polynomialLinear basis (e v) := by
  simp [polynomialAction,polynomialLinear]

end
end KLInvariance.ReflectionFrobenius

end


section

/-! Localization coordinates for tensor induction over a reflection wall.
This is an integral injectivity argument, not character normalization. -/
namespace KLInvariance.ReflectionFrobenius
open scoped Matrix
universe ua ui
variable {A : Type ua} [CommRing A] [IsDomain A] [CharZero A]
  {ι : Type ui} [Fintype ι] (τ : A ≃+* A) (α : A)
noncomputable section

 def wallCoordinate (E : Matrix ι ι A) (v : Fin 2 × ι → A) : Fin 2 × ι → A := fun e =>
  if e.1=0 then (E *ᵥ (fun j => v (0,j)+α*v (1,j))) e.2
  else ((E.map τ) *ᵥ (fun j => v (0,j)-α*v (1,j))) e.2

 def wallMatrix (E : Matrix ι ι A) : Matrix (Fin 2 × ι) (Fin 2 × ι) A := fun e f =>
  if e.1=0 then (if f.1=0 then E e.2 f.2 else α*E e.2 f.2)
  else if f.1=0 then τ (E e.2 f.2) else -α*τ (E e.2 f.2)

omit [IsDomain A] [CharZero A] in
 theorem wallMatrix_mulVec (E : Matrix ι ι A) (v : Fin 2 × ι → A) :
    wallMatrix τ α E *ᵥ v = wallCoordinate τ α E v := by
  classical
  funext ⟨r,j⟩
  change (∑ c : Fin 2 × ι, wallMatrix τ α E (r,j) c * v c) = _
  rw [Fintype.sum_prod_type,Fin.sum_univ_two]
  fin_cases r <;>
    simp [wallMatrix,wallCoordinate,Matrix.mulVec,dotProduct,
      Finset.sum_add_distrib,mul_add,
      mul_left_comm,mul_assoc,sub_eq_add_neg]

omit [IsDomain A] [CharZero A] in
 theorem matrixTwist_injective (E : Matrix ι ι A)
    (hE : Function.Injective (Matrix.mulVec E)) : Function.Injective (Matrix.mulVec (E.map τ)) := by
  intro v w hv
  have hh : E *ᵥ (fun j => τ.symm (v j)) = E *ᵥ (fun j => τ.symm (w j)) := by
    funext i
    have h := congrArg τ.symm (congrFun hv i)
    simpa only [Matrix.mulVec,dotProduct,map_sum,map_mul,Matrix.map_apply,
      RingEquiv.symm_apply_apply] using h
  have hh' := hE hh
  funext i
  exact τ.symm.injective (congrFun hh' i)

end
end KLInvariance.ReflectionFrobenius

end


section

/-! Exact kernels of the actual pair-projection quotient, in a form that
separates integral divisibility from annihilation of the edge. -/
namespace KLInvariance.PairProjection
universe u v w z
variable {R : Type u} [CommRing R]
  {M : Type v} [AddCommGroup M] [Module R M]
  {X : Type w} [AddCommGroup X] [Module R X]
  {Y : Type z} [AddCommGroup Y] [Module R Y]
  (f : M →ₗ[R] X) (g : M →ₗ[R] Y)

 theorem kernel_upper (y : Y) : upper f g y=0 ↔ ∃ m : M, f m=0 ∧ g m=y := by
  have he : upper f g y=0 ↔ lower f g 0=upper f g y := by
    rw [map_zero, eq_comm]
  rw [he, compatible_iff]

 theorem upper_kernel_of_divisibility (α : R)
    (hker : ∀ m : M, f m=0 → ∃ n : Y, g m=α • n)
    (hann : ∀ z : Edge f g, α • z=0) (y : Y) :
    upper f g y=0 ↔ ∃ n : Y, y=α • n := by
  constructor
  · intro h
    obtain ⟨m,hm,rfl⟩ := (kernel_upper f g y).mp h
    exact hker m hm
  · rintro ⟨n,rfl⟩
    rw [map_smul]
    exact hann _

end KLInvariance.PairProjection

end


section

/-! Integral simple-wall translation of a two-stalk projection lattice.
The hypotheses are explicit old-word edge properties, not character claims.
No freeness of a submodule is inferred merely from finite generation. -/
namespace KLInvariance.ReflectionPairTranslation
universe u v w z
variable {R : Type u} [CommRing R]

attribute [local instance] RingHomInvPair.of_ringEquiv

/-- Restriction of the scalar action along a ring automorphism. -/
@[ext] structure Twist (_τ : R ≃+* R) (Y : Type z) where
  val : Y
namespace Twist
variable (τ : R ≃+* R) (Y : Type z) [AddCommGroup Y] [Module R Y]
local instance instRingHomInvPairToRingHomSymm : RingHomInvPair τ.symm.toRingHom τ.toRingHom :=
  RingHomInvPair.of_ringEquiv_symm τ
local instance instRingHomInvPairToRingHomSymm_1 : RingHomInvPair τ.toRingHom τ.symm.toRingHom :=
  RingHomInvPair.of_ringEquiv τ
def equivVal : Twist τ Y ≃ Y where
  toFun := val
  invFun := mk
  left_inv _ := rfl
  right_inv _ := rfl
instance instAddCommGroup : AddCommGroup (Twist τ Y) := (equivVal τ Y).addCommGroup
instance instModule : Module R (Twist τ Y) := by
  letI : Module R Y := Module.compHom Y τ.toRingHom
  exact ({ equivVal τ Y with map_add' := fun _ _ => rfl } : Twist τ Y ≃+ Y).module R

def equiv : Y ≃ₛₗ[τ.symm.toRingHom] Twist τ Y where
  toFun := mk
  invFun := val
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' r y := by
    change mk (r • y) = mk (τ (τ.symm r) • y)
    rw [τ.apply_symm_apply]

instance instFree [Module.Free R Y] : Module.Free R (Twist τ Y) :=
  Module.Free.of_equiv (equiv τ Y)
end Twist

variable {N : Type v} [AddCommGroup N] [Module R N]
  {X : Type w} [AddCommGroup X] [Module R X]
  {Y : Type z} [AddCommGroup Y] [Module R Y]
  (f : N →ₗ[R] X) (g : N →ₗ[R] Y) (τ : R ≃+* R) (α : R)
  (hdiv : ∀ r : R, α ∣ τ r-r)
  (hinc : ∀ y : Y, ∃ n : N, f n=0 ∧ g n=α • y)

/-- The old pair relation with the scalar action on its second factor twisted.
Alpha-annihilation of the old edge is what makes this an R-submodule. -/
def lattice : Submodule R (X × Twist τ Y) where
  carrier := {p | ∃ n : N, f n=p.1 ∧ g n=p.2.val}
  zero_mem' := ⟨0,map_zero _,map_zero _⟩
  add_mem' := by
    rintro _ _ ⟨m,hm,hm'⟩ ⟨n,hn,hn'⟩
    exact ⟨m+n,by rw [map_add,hm,hn]; rfl,by rw [map_add,hm',hn']; rfl⟩
  smul_mem' := by
    rintro r ⟨x,y⟩ ⟨n,hn,hn'⟩
    obtain ⟨c,hc⟩ := hdiv r
    obtain ⟨m,hm,hm'⟩ := hinc (c • y.val)
    have hm'' : g m=(τ r-r) • y.val := by rw [hm',hc,mul_smul]
    refine ⟨r • n+m,?_,?_⟩
    · change f (r • n+m)=r • x
      rw [map_add,map_smul,hn,hm,add_zero]
    · change g (r • n+m)=τ r • y.val
      rw [map_add,map_smul,hn',hm'',sub_smul]
      abel

/-- Saturation away from the simple wall. Regularity on the old edge module,
not an unjustified reflexivity assertion, removes a non-wall factor. -/
theorem lattice_saturated (β : R)
    (hann : ∀ e : PairProjection.Edge f g, α • e=0)
    (hreg : Function.Injective (fun e : PairProjection.Edge f g => β • e))
    (p : X × Twist τ Y) :
    β • p ∈ lattice f g τ α hdiv hinc ↔ p ∈ lattice f g τ α hdiv hinc := by
  constructor
  · rintro ⟨n,hn,hn'⟩
    apply (PairProjection.compatible_iff f g p.1 p.2.val).mp
    apply hreg
    have hn'' : g n=τ β • p.2.val := hn'
    have h := PairProjection.compatible f g n
    have hn1 : f n=β • p.1 := hn
    rw [hn1,hn'',map_smul,map_smul] at h
    obtain ⟨c,hc⟩ := hdiv β
    have he : (τ β-β) • PairProjection.upper f g p.2.val=0 := by
      rw [hc,mul_smul,smul_comm,hann,smul_zero]
    rw [sub_smul,sub_eq_zero] at he
    exact h.trans he
  · exact (lattice f g τ α hdiv hinc).smul_mem β

/-- Surjective projection to the untwisted (lower) stalk. -/
def left : lattice f g τ α hdiv hinc →ₗ[R] X :=
  (LinearMap.fst R X (Twist τ Y)).comp (lattice f g τ α hdiv hinc).subtype

 theorem left_surjective (hf : Function.Surjective f) :
    Function.Surjective (left f g τ α hdiv hinc) := by
  intro x
  obtain ⟨n,rfl⟩ := hf x
  exact ⟨⟨(f n,⟨g n⟩),n,rfl,rfl⟩,rfl⟩

 variable (hker : ∀ y : Y, (∃ n : N, f n=0 ∧ g n=y) ↔ ∃ z : Y, y=α • z)

/-- A split extension of free modules is free. This does not assert the
false statement that every submodule of a free polynomial module is free. -/
theorem free_of_surjective_of_ker_free {P : Type*} [AddCommGroup P] [Module R P]
    {Q : Type*} [AddCommGroup Q] [Module R Q]
    (π : P →ₗ[R] Q) (hπ : Function.Surjective π)
    [Module.Free R Q] [Module.Free R (LinearMap.ker π)] : Module.Free R P := by
  obtain ⟨s,hs⟩ := π.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hπ)
  let e : (LinearMap.ker π × Q) →ₗ[R] P :=
    (LinearMap.ker π).subtype.coprod s
  have hps (q : Q) : π (s q)=q := DFunLike.congr_fun hs q
  have he : Function.Bijective e := by
    constructor
    · rintro ⟨k,q⟩ ⟨k',q'⟩ h
      have hq : q=q' := by
        have hh := congrArg π h
        simpa only [e,LinearMap.coprod_apply,Submodule.subtype_apply,map_add,LinearMap.mem_ker.mp k.property,
          LinearMap.mem_ker.mp k'.property,hps,zero_add] using hh
      subst q'
      refine Prod.ext ?_ rfl
      apply Subtype.ext
      exact add_right_cancel h
    · intro p
      refine ⟨(⟨p-s (π p),?_⟩,π p),?_⟩
      · change π (p-s (π p))=0
        rw [map_sub,hps,sub_self]
      · change p-s (π p)+s (π p)=p
        abel
  exact Module.Free.of_equiv (LinearEquiv.ofBijective e he)

end KLInvariance.ReflectionPairTranslation

end


end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_BottSamelson
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Bott-Samelson tensor ranges, actual sections, grading and right kernels.
-/

section

namespace KLInvariance
open TensorProduct
universe uc ua un uv up
variable {C : Type uc} [CommRing C] {A : Type ua} [CommRing A] [Algebra C A]
  {N : Type un} [AddCommGroup N] [Module C N]
  {V : Type uv} [AddCommGroup V] [Module A V]
  {P : Type up} [AddCommGroup P] [Module A P]
 theorem tensor_range_le_of_one_tmul (F : (A ⊗[C] N) →ₗ[A] V) (G : P →ₗ[A] V)
    (h : ∀ n : N, F ((1 : A) ⊗ₜ[C] n) ∈ LinearMap.range G) :
    LinearMap.range F ≤ LinearMap.range G := by
  rintro _ ⟨m,rfl⟩
  induction m using OAI.tensorInductionOn with
  | add m n hm hn => rw [map_add]; exact (LinearMap.range G).add_mem hm hn
  | tmul a n =>
    have he : a ⊗ₜ[C] n = a • ((1 : A) ⊗ₜ[C] n) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul,mul_one]
    rw [he,map_smul]
    exact (LinearMap.range G).smul_mem a (h n)
 theorem tensor_maps_eq_of_one_tmul (F G : (A ⊗[C] N) →ₗ[A] V)
    (h : ∀ n : N, F ((1 : A) ⊗ₜ[C] n)=G ((1 : A) ⊗ₜ[C] n)) : F=G := by
  apply LinearMap.ext
  intro m
  induction m using OAI.tensorInductionOn with
  | add m n hm hn => rw [map_add,map_add,hm,hn]
  | tmul a n =>
    have he : a ⊗ₜ[C] n = a • ((1 : A) ⊗ₜ[C] n) := by
      rw [TensorProduct.smul_tmul',smul_eq_mul,mul_one]
    rw [he,map_smul,map_smul,h n]

 theorem codRestrict_surjective_of_range_le (G : P →ₗ[A] V) (S : Submodule A V)
    (hG : ∀ p, G p ∈ S) (hS : S ≤ LinearMap.range G) :
    Function.Surjective (LinearMap.codRestrict S G hG) := by
  intro z
  obtain ⟨p,hp⟩ := hS z.property
  exact ⟨p,Subtype.ext hp⟩
end KLInvariance

end


section

/-! The two common tail components of a reflected tensor. They are defined
on the actual tensor, so divisibility assertions at different weights use the
same tail vectors rather than unrelated existential lifts. -/
namespace KLInvariance.ReflectionPairTranslation
open TensorProduct
universe uc ua un
variable {C : Type uc} [CommRing C] {A : Type ua} [CommRing A] [Algebra C A]
  {N : Type un} [AddCommGroup N] [Module A N] [Module C N] [IsScalarTower C A N]
  (τ : A ≃+* A) (hfix : ∀ c : C, τ (algebraMap C A c)=algebraMap C A c)
noncomputable section

 def tensorFirst : (A ⊗[C] N) →ₗ[A] N :=
  AlgebraTensorModule.lift ((LinearMap.id : A →ₗ[A] A).smulRight
    (LinearMap.id : N →ₗ[C] N))

 @[simp] theorem tensorFirst_tmul (a : A) (n : N) :
    tensorFirst (C := C) (a ⊗ₜ[C] n)=a • n := rfl

 def tensorSecond : (A ⊗[C] N) →ₗ[A] Twist τ N := by
  letI : Module C (Twist τ N) := Module.compHom _ (algebraMap C A)
  letI : IsScalarTower C A (Twist τ N) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let F : N →ₗ[C] Twist τ N := {
    toFun := Twist.mk
    map_add' := fun _ _ => rfl
    map_smul' := fun c n => by
      apply Twist.ext
      change c • n=τ (algebraMap C A c) • n
      rw [hfix,algebraMap_smul] }
  exact AlgebraTensorModule.lift ((LinearMap.id : A →ₗ[A] A).smulRight F)

 @[simp] theorem tensorSecond_tmul (a : A) (n : N) :
    tensorSecond τ hfix (a ⊗ₜ[C] n)=Twist.mk (τ a • n) := rfl

 def twistMap {P : Type*} [AddCommGroup P] [Module A P] (f : N →ₗ[A] P) :
    Twist τ N →ₗ[A] Twist τ P where
  toFun m := ⟨f m.val⟩
  map_add' m n := Twist.ext (map_add f m.val n.val)
  map_smul' a m := Twist.ext (map_smul f (τ a) m.val)
end
end KLInvariance.ReflectionPairTranslation

end


section
namespace KLInvariance
universe ua up uv un
variable {A : Type ua} [CommRing A]
  {P : Type up} [AddCommGroup P] [Module A P]
  {V : Type uv} [AddCommGroup V] [Module A V]
  {N : Type un} [AddCommGroup N] [Module A N]
 theorem linearMap_mem_of_coordinates (S : Submodule A P)
    (F : P →ₗ[A] V) (G : N →ₗ[A] P) (E : N →ₗ[A] V)
    (hF : Function.Injective F) (heq : F.comp G = E)
    (hrange : LinearMap.range E ≤ LinearMap.range (F.comp S.subtype)) (n : N) : G n ∈ S := by
  obtain ⟨p,hp⟩ := hrange (show E n ∈ LinearMap.range E from ⟨n,rfl⟩)
  have he : (p : P) = G n := hF (hp.trans (LinearMap.congr_fun heq n).symm)
  exact he ▸ p.property
end KLInvariance

end


section

namespace KLInvariance.FiniteFreeScalar
universe ur um un ui
variable {R : Type ur} [CommRing R]
  {M : Type um} [AddCommGroup M] [Module R M]
  {ι : Type ui} [Fintype ι] (b : Module.Basis ι R M)


 theorem exists_smul_iff (r : R) (m : M) :
    (∃ n, r • n = m) ↔ ∀ i, r ∣ b.equivFun m i := by
  classical
  constructor
  · rintro ⟨n,rfl⟩ i
    exact ⟨b.equivFun n i, by simp⟩
  · intro h
    choose n hn using h
    refine ⟨b.equivFun.symm n,b.equivFun.injective ?_⟩
    ext i
    simp only [map_smul,LinearEquiv.apply_symm_apply,Pi.smul_apply,smul_eq_mul]
    exact (hn i).symm

include b in
 theorem exists_prod_smul [DecompositionMonoid R] {J : Type*} (s : Finset J) (r : J → R)
    (hrel : (s : Set J).Pairwise (Function.onFun IsRelPrime r)) (m : M)
    (h : ∀ j ∈ s, ∃ n, r j • n = m) : ∃ n, (∏ j ∈ s, r j) • n = m := by
  apply (exists_smul_iff b _ m).mpr
  intro i
  apply Finset.prod_dvd_of_isRelPrime hrel
  intro j hj
  exact (exists_smul_iff b _ _).mp (h j hj) i

include b in


 theorem scalar_quotient_regular
    {N : Type un} [AddCommGroup N] [Module R N]
    (q : M →ₗ[R] N) (hq : Function.Surjective q)
    (a r : R) (ha : Prime a) (hr : ¬ a ∣ r)
    (hker : ∀ m, q m = 0 ↔ ∃ n, m=a • n) :
    Function.Injective (fun v : N => r • v) := by
  suffices hh : ∀ v : N, r • v = 0 → v = 0 by
    intro v w hvw
    change r • v = r • w at hvw
    have hv : r • (v-w) = 0 := by rw [smul_sub,hvw,sub_self]
    exact sub_eq_zero.mp (hh _ hv)
  intro v hv
  obtain ⟨m,rfl⟩ := hq v
  have h0 : q (r • m) = 0 := by simpa only [map_smul] using hv
  obtain ⟨n,hn⟩ := (hker _).mp h0
  have hdiv : ∀ i, a ∣ b.equivFun m i := by
    intro i
    have hc := congrArg (fun z => b.equivFun z i) hn
    simp only [map_smul,Pi.smul_apply,smul_eq_mul] at hc
    apply (ha.dvd_mul.mp ?_).resolve_left hr
    exact ⟨b.equivFun n i,hc⟩
  obtain ⟨z,hz⟩ := (exists_smul_iff b a m).mpr hdiv
  exact (hker m).mpr ⟨z,hz.symm⟩

end KLInvariance.FiniteFreeScalar

end


section

namespace KLInvariance.ReflectionPairTranslation
universe u v w z
variable {R : Type u} [CommRing R]
  {N : Type v} [AddCommGroup N] [Module R N]
  {X : Type w} [AddCommGroup X] [Module R X]
  {Y : Type z} [AddCommGroup Y] [Module R Y]
  (f : N →ₗ[R] X) (g : N →ₗ[R] Y) (τ : R ≃+* R) (α : R)
  (hdiv : ∀ r : R, α ∣ τ r-r)
  (hinc : ∀ y : Y, ∃ n : N, f n=0 ∧ g n=α • y)
  (hker : ∀ x : X, (∃ n : N, f n=x ∧ g n=0) ↔ ∃ z : X, x=α • z)

 def right : lattice f g τ α hdiv hinc →ₗ[R] Twist τ Y :=
  (LinearMap.snd R X (Twist τ Y)).comp (lattice f g τ α hdiv hinc).subtype

 theorem right_surjective (hg : Function.Surjective g) :
    Function.Surjective (right f g τ α hdiv hinc) := by
  intro y
  obtain ⟨n,hn⟩ := hg y.val
  exact ⟨⟨(f n,y),n,rfl,hn⟩,rfl⟩

 def rightKernelMap : X →ₗ[R] LinearMap.ker (right f g τ α hdiv hinc) where
  toFun x := ⟨⟨(α • x,⟨0⟩),(hker (α • x)).mpr ⟨x,rfl⟩⟩,rfl⟩
  map_add' x y := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · exact smul_add α x y
    · apply Twist.ext
      exact (zero_add (0 : Y)).symm
  map_smul' r x := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · exact smul_comm α r x
    · apply Twist.ext
      exact (smul_zero _).symm

 theorem rightKernelMap_surjective :
    Function.Surjective (rightKernelMap f g τ α hdiv hinc hker) := by
  rintro ⟨⟨⟨x,y⟩,n,hn,hn'⟩,hy⟩
  have hy' : y.val=0 := congrArg Twist.val hy
  obtain ⟨z,hz⟩ := (hker x).mp ⟨n,hn,hn'.trans hy'⟩
  refine ⟨z,?_⟩
  apply Subtype.ext
  apply Subtype.ext
  exact Prod.ext hz.symm (Twist.ext hy'.symm)

 theorem rightKernelMap_injective (hinj : Function.Injective (fun x : X => α • x)) :
    Function.Injective (rightKernelMap f g τ α hdiv hinc hker) := by
  intro x y h
  exact hinj (congrArg (fun p => p.val.val.1) h)

 noncomputable def rightKernelEquiv (hinj : Function.Injective (fun x : X => α • x)) :
    X ≃ₗ[R] LinearMap.ker (right f g τ α hdiv hinc) :=
  LinearEquiv.ofBijective (rightKernelMap f g τ α hdiv hinc hker)
    ⟨rightKernelMap_injective f g τ α hdiv hinc hker hinj,
      rightKernelMap_surjective f g τ α hdiv hinc hker⟩

 include hker in
 theorem lattice_free_right (hg : Function.Surjective g)
    (hinj : Function.Injective (fun x : X => α • x))
    [Module.Free R X] [Module.Free R Y] :
    Module.Free R (lattice f g τ α hdiv hinc) := by
  let : Module.Free R (LinearMap.ker (right f g τ α hdiv hinc)) :=
    Module.Free.of_equiv (rightKernelEquiv f g τ α hdiv hinc hker hinj)
  exact free_of_surjective_of_ker_free (right f g τ α hdiv hinc)
    (right_surjective f g τ α hdiv hinc hg)
end KLInvariance.ReflectionPairTranslation

end


section

/-! Honest change of the coefficient algebra along an algebra equivalence.
Both scalar actions and semilinear identifications are explicit. -/
namespace KLInvariance
universe uk ua ub um un
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {B : Type ub} [CommRing B] [Algebra k B]

@[ext] structure CoefficientChange (_e : A ≃ₐ[k] B) (M : Type um) where
  val : M

namespace CoefficientChange
variable (e : A ≃ₐ[k] B) (M : Type um) [AddCommGroup M] [Module A M] [Module k M]
  [IsScalarTower k A M]

 def equivVal : CoefficientChange e M ≃ M where
  toFun := val
  invFun := mk
  left_inv _ := rfl
  right_inv _ := rfl

 instance instAddCommGroup : AddCommGroup (CoefficientChange e M) := (equivVal e M).addCommGroup
 instance instModule : Module B (CoefficientChange e M) := by
   letI : Module B M := Module.compHom M e.symm.toRingHom
   exact ({ equivVal e M with map_add' := fun _ _ => rfl } : CoefficientChange e M ≃+ M).module B
 instance instModule_1 : Module k (CoefficientChange e M) :=
   ({ equivVal e M with map_add' := fun _ _ => rfl } : CoefficientChange e M ≃+ M).module k
 instance instIsScalarTower : IsScalarTower k B (CoefficientChange e M) where
   smul_assoc c b m := by
     apply CoefficientChange.ext
     change e.symm (c • b) • m.val=c • (e.symm b • m.val)
     rw [map_smul,smul_assoc]

 local instance instRingHomInvPairToRingHomToRingEquivSymm : RingHomInvPair e.symm.toRingHom e.toRingHom := RingHomInvPair.of_ringEquiv_symm e.toRingEquiv
 local instance instRingHomInvPairToRingHomToRingEquivSymm_1 : RingHomInvPair e.toRingHom e.symm.toRingHom := RingHomInvPair.of_ringEquiv e.toRingEquiv

 def equiv : M ≃ₛₗ[e.toRingHom] CoefficientChange e M where
   toFun := mk
   invFun := val
   left_inv _ := rfl
   right_inv _ := rfl
   map_add' _ _ := rfl
   map_smul' a m := by
     change mk (a • m)=mk (e.symm (e a) • m)
     rw [e.symm_apply_apply]

 def kEquiv : M ≃ₗ[k] CoefficientChange e M where
   toFun := mk
   invFun := val
   left_inv _ := rfl
   right_inv _ := rfl
   map_add' _ _ := rfl
   map_smul' _ _ := rfl

 instance instFree [Module.Free A M] : Module.Free B (CoefficientChange e M) :=
   Module.Free.of_equiv (equiv e M)
 instance instFinite [Module.Finite A M] : Module.Finite B (CoefficientChange e M) :=
   Module.Finite.of_surjective (equiv e M).toLinearMap (equiv e M).surjective

 variable {M} {N : Type un} [AddCommGroup N] [Module A N] [Module k N] [IsScalarTower k A N]
 def map (f : M →ₗ[A] N) : CoefficientChange e M →ₗ[B] CoefficientChange e N where
   toFun m := mk (f m.val)
   map_add' m n := CoefficientChange.ext (map_add f m.val n.val)
   map_smul' b m := CoefficientChange.ext (map_smul f (e.symm b) m.val)

 omit [Module k M] [IsScalarTower k A M] [Module k N] [IsScalarTower k A N] in
 theorem map_surjective (f : M →ₗ[A] N) (hf : Function.Surjective f) :
     Function.Surjective (map e f) := by
   intro n
   obtain ⟨m,hm⟩ := hf n.val
   exact ⟨mk m,CoefficientChange.ext hm⟩

end CoefficientChange
end KLInvariance

end


end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_IntegralPairings
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Hilbert recurrences, projective section ranges, integral lattices and graded perfect adjoints.
-/


section

/-! Range-valued projections to sets of coordinates and their natural
surjective restriction maps. -/
namespace KLInvariance.CoordinateProjection
universe ur un uv ux
variable {R : Type ur} [CommRing R] {N : Type un} [AddCommGroup N] [Module R N]
  {V : Type uv} {X : V → Type ux} [∀ x, AddCommGroup (X x)] [∀ x, Module R (X x)]
  (f : ∀ x, N →ₗ[R] X x)
noncomputable section

 def eval (U : Set V) : N →ₗ[R] (∀ x : U, X x.val) := LinearMap.pi (fun x => f x.val)
 def image (U : Set V) : Submodule R (∀ x : U, X x.val) := LinearMap.range (eval f U)
 def project (U : Set V) : N →ₗ[R] image f U := (eval f U).rangeRestrict

end
end KLInvariance.CoordinateProjection

end


section

namespace KLInvariance.ProjectiveRange
universe ur um uh up us
variable {R : Type ur} [CommRing R]
  {M : Type um} [AddCommGroup M] [Module R M]
  {H : Type uh} [AddCommGroup H] [Module R H]
  {P : Type up} [AddCommGroup P] [Module R P]
  {S : Type us} [AddCommGroup S] [Module R S]
  (r : M →ₗ[R] H) (f : M →ₗ[R] P) (k : P →ₗ[R] S)
  (h : ∀ m, r m=0 → k (f m)=0)
noncomputable section

 def onKernel : LinearMap.ker r →ₗ[R] LinearMap.ker k :=
  (f.comp (LinearMap.ker r).subtype).codRestrict (LinearMap.ker k) (fun m => h m.val m.property)

end
end KLInvariance.ProjectiveRange

end


section

/-! Integral local projectors for finite character lattices. This lemma does
not assert any BMP character theorem or identify a chosen summand with BMP. -/
namespace KLInvariance.FiniteCharacterLocalization
universe u v w
variable {R : Type u} [CommRing R] {X : Type v}
  {E : X → Type w} [∀ x, AddCommGroup (E x)] [∀ x, Module R (E x)]
noncomputable section

 def diagonal (f : X → R) : (∀ x, E x) →ₗ[R] (∀ x, E x) where
  toFun m x := f x • m x
  map_add' := by intro m n; funext x; exact smul_add _ _ _
  map_smul' := by intro r m; funext x; exact smul_comm _ _ _

 def residueSetoid {A : Type*} (p : R) (χ : A → X → R) : Setoid X where
  r x y := ∀ a, p ∣ χ a x-χ a y
  iseqv := ⟨fun x a => by rw [sub_self]; exact dvd_zero _,
    fun h a => by simpa only [neg_sub] using dvd_neg.mpr (h a),
    fun h h' a => by simpa only [sub_add_sub_cancel] using dvd_add (h a) (h' a)⟩

end
end KLInvariance.FiniteCharacterLocalization

end


end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_Support
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Graded unit splittings, integral support and balanced cuts, and boundary-sheaf support and recognition.
-/


section


namespace KLInvariance.IntegralSupport

universe ur uv um
variable {R : Type ur} [CommRing R]
  {V : Type uv} [DecidableEq V] {A : V → Type um} [∀ x, AddCommGroup (A x)] [∀ x, Module R (A x)]
  (M : Submodule R (∀ x, A x))

noncomputable def projection (x : V) : M →ₗ[R] A x := (LinearMap.proj x).comp M.subtype

def supported (x : V) : Submodule R M where
  carrier := {m | ∀ y, y ≠ x → m.val y = 0}
  zero_mem' := by intro y hy; rfl
  add_mem' := by intro m n hm hn y hy; exact congrArg₂ (· + ·) (hm y hy) (hn y hy) |>.trans (zero_add _)
  smul_mem' := by intro r m hm y hy; exact congrArg (r • ·) (hm y hy) |>.trans (smul_zero r)

variable (p : R)
  (hcut : ∀ x (m : M), (p • Pi.single x (m.val x)) ∈ M)

noncomputable def cut (x : V) : M →ₗ[R] M := by
  exact ((p • (LinearMap.single R A x).comp (LinearMap.proj x)).domRestrict M).codRestrict M (hcut x)

@[simp] theorem cut_apply (x : V) (m : M) : (cut M p hcut x m).val = p • Pi.single x (m.val x) := rfl

@[simp] theorem cut_self (x : V) (m : M) : (cut M p hcut x m).val x = p • m.val x := by
  simp [cut_apply]

 theorem cut_other (x y : V) (h : y ≠ x) (m : M) : (cut M p hcut x m).val y = 0 := by
  simp [cut_apply,h]

 theorem cut_of_supported (x : V) (m : M) (h : m ∈ supported M x) :
    cut M p hcut x m = p • m := by
  apply Subtype.ext
  funext y
  by_cases hy : y=x
  · subst y; exact cut_self M p hcut x m
  · rw [cut_other M p hcut x y hy]
    change 0 = p • m.val y
    rw [h y hy,smul_zero]

 theorem cut_eq_zero (x : V) (m : M) (h : projection M x m = 0) : cut M p hcut x m = 0 := by
  apply Subtype.ext
  change p • Pi.single x (m.val x) = 0
  change m.val x = 0 at h
  simp [h]

variable [IsDomain R] [∀ x, Module.IsTorsionFree R (A x)] (hp : p ≠ 0)
  (d : M ≃ₗ[R] Module.Dual R M)
  (hbalanced : ∀ x m n, d (cut M p hcut x m) n = d m (cut M p hcut x n))

include hp hbalanced in
/-- The exact integral annihilator, not merely its generic vector space. -/
 theorem supported_iff_annihilates (x : V) (m : M) :
    m ∈ supported M x ↔ ∀ n : M, projection M x n = 0 → d m n = 0 := by
  constructor
  · intro hm n hn
    have hh := hbalanced x m n
    rw [cut_of_supported M p hcut x m hm,cut_eq_zero M p hcut x n hn] at hh
    simpa only [map_smul,LinearMap.smul_apply,map_zero,smul_eq_zero_iff_right hp] using hh
  · intro hm y hy
    have hc : cut M p hcut y m = 0 := by
      apply d.injective
      apply LinearMap.ext
      intro n
      rw [hbalanced]
      simpa only [map_zero,LinearMap.zero_apply] using
        hm (cut M p hcut y n) (cut_other M p hcut y x (Ne.symm hy) n)
    have hv := congrArg (fun s : M => s.val y) hc
    simpa only [cut_self,Submodule.coe_zero,Pi.zero_apply,smul_eq_zero_iff_right hp] using hv

/-- Precomposition with a surjective stalk projection gives the integral
single-support module. No field extension was used anywhere in this map. -/
noncomputable def dualToSupport (x : V) : Module.Dual R (A x) →ₗ[R] supported M x :=
  (d.symm.toLinearMap.comp (projection M x).dualMap).codRestrict (supported M x) (by
    intro lam
    apply (supported_iff_annihilates M p hcut hp d hbalanced x _).mpr
    intro n hn
    simp only [LinearMap.comp_apply,LinearEquiv.coe_coe,LinearEquiv.apply_symm_apply,
      LinearMap.dualMap_apply]
    change lam (projection M x n) = 0
    rw [hn,map_zero])

 theorem dualToSupport_bijective (x : V) (hπ : Function.Surjective (projection M x)) :
    Function.Bijective (dualToSupport M p hcut hp d hbalanced x) := by
  constructor
  · intro lam mu he
    apply LinearMap.dualMap_injective_of_surjective hπ
    apply d.symm.injective
    exact congrArg Subtype.val he
  · intro m
    have hm : d m.val ∈ (LinearMap.ker (projection M x)).dualAnnihilator := by
      rw [Submodule.mem_dualAnnihilator]
      intro n hn
      exact (supported_iff_annihilates M p hcut hp d hbalanced x m.val).mp m.property n hn
    rw [← LinearMap.range_dualMap_eq_dualAnnihilator_ker_of_surjective _ hπ] at hm
    obtain ⟨lam,hlam⟩ := hm
    refine ⟨lam,?_⟩
    apply Subtype.ext
    change d.symm ((projection M x).dualMap lam) = m.val
    rw [hlam,LinearEquiv.symm_apply_apply]

noncomputable def supportEquivDual (x : V) (hπ : Function.Surjective (projection M x)) :
    supported M x ≃ₗ[R] Module.Dual R (A x) :=
  (LinearEquiv.ofBijective (dualToSupport M p hcut hp d hbalanced x)
    (dualToSupport_bijective M p hcut hp d hbalanced x hπ)).symm

end KLInvariance.IntegralSupport

end


section

namespace KLInvariance.MomentGraph.Sheaf
universe ur uv ue um
variable {R : Type ur}
  [CommRing R]
  {V : Type uv}
  [PartialOrder V]
  {E : Type ue}

variable [Fintype E] (α : E → R)

def labelProduct : R := ∏ e, α e

 theorem labelProduct_ne_zero [IsDomain R] (hα : ∀ e, α e ≠ 0) : labelProduct α ≠ 0 := by
  exact Finset.prod_ne_zero_iff.mpr (fun e _ => hα e)

end KLInvariance.MomentGraph.Sheaf

end


section

namespace KLInvariance.CoefficientChange
open Module
universe uk ua ub um un
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {B : Type ub} [CommRing B] [Algebra k B]
  (e : A ≃ₐ[k] B) {M : Type um} [AddCommGroup M] [Module A M]
  [Module k M] [IsScalarTower k A M]
noncomputable section

 def mapEquiv {N : Type un} [AddCommGroup N] [Module A N] [Module k N]
    [IsScalarTower k A N] (f : M ≃ₗ[A] N) : CoefficientChange e M ≃ₗ[B] CoefficientChange e N where
  toLinearMap := map e f.toLinearMap
  invFun n := mk (f.symm n.val)
  left_inv m := CoefficientChange.ext (f.symm_apply_apply m.val)
  right_inv n := CoefficientChange.ext (f.apply_symm_apply n.val)

 def dualTo (f : CoefficientChange e (Dual A M)) : Dual B (CoefficientChange e M) where
  toFun m := e (f.val m.val)
  map_add' m n := by change e (f.val (m.val+n.val))=_; rw [map_add,map_add]
  map_smul' b m := by
    change e (f.val (e.symm b • m.val))=b * e (f.val m.val)
    rw [map_smul]
    change e (e.symm b * f.val m.val)=_
    rw [map_mul,e.apply_symm_apply]

 def dualFrom (f : Dual B (CoefficientChange e M)) : Dual A M where
  toFun m := e.symm (f (mk m))
  map_add' m n := by
    change e.symm (f (mk m+mk n))=_
    rw [map_add,map_add]
  map_smul' a m := by
    change e.symm (f (mk (a • m)))=a * e.symm (f (mk m))
    rw [show (mk (a • m) : CoefficientChange e M)=e a • mk m from by
      apply CoefficientChange.ext
      change a • m=e.symm (e a) • m
      rw [e.symm_apply_apply],
      map_smul]
    change e.symm (e a * f (mk m))=_
    rw [map_mul,e.symm_apply_apply]

 def dualEquiv : CoefficientChange e (Dual A M) ≃ₗ[B] Dual B (CoefficientChange e M) where
  toFun := dualTo e
  invFun f := mk (dualFrom e f)
  left_inv f := by
    apply CoefficientChange.ext
    apply LinearMap.ext
    intro m
    exact e.symm_apply_apply (f.val m)
  right_inv f := by
    apply LinearMap.ext
    intro m
    exact e.apply_symm_apply (f m)
  map_add' f g := by
    apply LinearMap.ext
    intro m
    exact map_add e (f.val m.val) (g.val m.val)
  map_smul' b f := by
    apply LinearMap.ext
    intro m
    change e (e.symm b * f.val m.val)=b * e (f.val m.val)
    rw [map_mul,e.apply_symm_apply]

 def pairingEquiv (d : M ≃ₗ[A] Dual A M) :
    CoefficientChange e M ≃ₗ[B] Dual B (CoefficientChange e M) :=
  (mapEquiv e d).trans (dualEquiv e)

end
end KLInvariance.CoefficientChange

end


end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_ReflectionOrders
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Finite sweep algebra, wall orders and the full reflection-order path formula.
-/


section

/-! Algebra and finite ordered-list bookkeeping for wall crossings. -/
namespace KLInvariance.SchedulePaths
universe u v w
variable {E : Type u} {A : Type v} {Λ : Type w} [LinearOrder A] [LinearOrder Λ]
noncomputable section
local instance instDecidable_solutions_4 (p : Prop) : Decidable p := Classical.propDecidable p
local instance instDecidableEq_solutions : DecidableEq E := Classical.decEq E

def sortedSchedule (F : Finset E) (score : E → Λ) : List E :=
  F.toList.mergeSort (fun e f => score f ≤ score e)

end
end KLInvariance.SchedulePaths

end


end OAI
end


