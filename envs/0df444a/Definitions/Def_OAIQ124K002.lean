-- Prove2me | Definitions.Def_OAIQ124K002
-- name    : OAIQ124K002
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T05:41:14.635598+00:00
-- url     : https://prove2.me/theorems/b54c7677-4e0e-4e9a-8f77-4ff3fefbb940
-- title:
--   Definitions bundle OAIQ124K002 of the split of OpenAI, Combinatorial invariance of Kazhdan–Lusztig polynomials (result family 168)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.KLInvariance.combinatorial_invariance`, carved from OpenAI's openai/math development (OpenAI, *Combinatorial invariance of Kazhdan–Lusztig polynomials (result family 168)*, OpenAI Math Release, September 24, 2026, result family 168, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 59 declarations of OpenAI's Lean: 31 definitions, 1 inductive type or structure and 27 theorems. The definitions and types are `OAI.KLInvariance.BruhatGraph.charDecEqC`, `OAI.KLInvariance.BruhatGraph.instDecidableEq_solutions`, `OAI.KLInvariance.BruhatGraph.instDecidable_solutions_1`, `OAI.KLInvariance.BruhatGraph.instDecidable_solutions_2`, `OAI.KLInvariance.BruhatGraph.instDecidable_solutions_3`, `OAI.KLInvariance.BruhatGraph.instDecidable_solutions_4`, `OAI.KLInvariance.CanonicalP.lowPart`, `OAI.KLInvariance.Comparison.scaledPolynomial`, `OAI.KLInvariance.Dihedral.GoodIndex`, `OAI.KLInvariance.Dihedral.indexWord`, `OAI.KLInvariance.Dihedral.instDecidableEq_solutions`, `OAI.KLInvariance.Dihedral.rotation`, `OAI.KLInvariance.Graded.NonnegativeBasis`, `OAI.KLInvariance.Graded.NonnegativeBasis.polynomial`, `OAI.KLInvariance.Hilbert.piece`, `OAI.KLInvariance.Hilbert.term`, `OAI.KLInvariance.Hilbert.value`, `OAI.KLInvariance.MomentGraph.GradedSheaf.Witness`, `OAI.KLInvariance.MomentGraph.Sheaf.quotientLinear`, `OAI.KLInvariance.OrdinaryR.variableUnit`, `OAI.KLInvariance.ProjectiveRange.descend`, `OAI.KLInvariance.ProjectiveRange.kernelRetraction`, `OAI.KLInvariance.ProjectiveRange.splitEquiv`, `OAI.KLInvariance.SchedulePaths.instDecidable_solutions`, `OAI.KLInvariance.SchedulePaths.instDecidable_solutions_3`, `OAI.KLInvariance.SignedDihedral.instDecidable_solutions`, `OAI.KLInvariance.TitsSpace.instDecidable_solutions_5`, `OAI.KLInvariance.TitsSpace.simpleInter`, `OAI.KLInvariance.TitsSpace.simplePull`, `OAI.KLInvariance.TitsSpace.simpleUnion`, `OAI.LinearDescent.descend`, `OAI.PerfectAdjoint.adjoint`.
--
--   **Sources.** They come from these modules of lean/OAI/RepresentationTheory, in whole or in part: `KazhdanLusztig_BalancedPairings`, `KazhdanLusztig_CanonicalKL`, `KazhdanLusztig_CharacterReciprocity`, `KazhdanLusztig_Decomposition`, `KazhdanLusztig_DihedralIntervals`, `KazhdanLusztig_GradedSheaves`, `KazhdanLusztig_IntegralPairings`, `KazhdanLusztig_MinimalExtensions`, `KazhdanLusztig_ModuleAlgebra`, `KazhdanLusztig_OrdinaryR`, `KazhdanLusztig_ReflectionOrders`, `KazhdanLusztig_ReflectionSchedules`, `KazhdanLusztig_SheafMorphisms`, `KazhdanLusztig_SimultaneousInvariance`, `KazhdanLusztig_TerminalKernels`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ124K006` and `OAIQ124K007`.
-- source:
--   OpenAI, Combinatorial invariance of Kazhdan–Lusztig polynomials (result family 168), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 168; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Combinatorial-Invariance-of-Kazhdan-Lusztig-Polynomials-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/RepresentationTheory at commit adc7f12

import Mathlib

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


namespace KLInvariance.EdgeLattice

variable {R : Type*} [CommRing R] [klPreservedInstance2 : IsDomain R] [klPreservedInstance3 : UniqueFactorizationMonoid R]

include klPreservedInstance2 klPreservedInstance3 in
theorem finsupp_divide {ι : Type*} (r : R) (f : ι →₀ R)
    (h : ∀ i, r ∣ f i) : ∃ g : ι →₀ R, r • g = f := by
  have _ := klPreservedInstance2
  have _ := klPreservedInstance3
  classical
  let g : ι →₀ R := ∑ i ∈ f.support, Finsupp.single i (Classical.choose (h i))
  refine ⟨g, ?_⟩
  dsimp [g]
  rw [Finset.smul_sum]
  have heq : (∑ i ∈ f.support, r • Finsupp.single i (Classical.choose (h i))) =
      ∑ i ∈ f.support, Finsupp.single i (f i) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finsupp.smul_single, smul_eq_mul, ← Classical.choose_spec (h i)]
  rw [heq]
  exact Finsupp.sum_single f

/-- In a free module, divisibility can be checked on a basis. -/
theorem basis_divide {E : Type*} [AddCommGroup E] [Module R E]
    {ι : Type*} (b : Module.Basis ι R E) (p : R) (m : E)
    (h : ∀ i, p ∣ b.repr m i) : ∃ n : E, p • n = m := by
  obtain ⟨f, hf⟩ := finsupp_divide p (b.repr m) h
  refine ⟨b.repr.symm f, b.repr.injective ?_⟩
  simpa only [map_smul, b.repr.apply_symm_apply] using hf

/-- Scalar-denominator formulation of the height-one intersection property.
A generic-span witness and local denominators away from each prime element
force membership in a free target, with no reflexivity hypothesis on a source. -/
theorem mem_of_prime_local_membership
    {E : Type*} [AddCommGroup E] [Module R E] [Module.IsTorsionFree R E]
    (M : Submodule R E) [Module.Free R M] (x : E)
    (hgeneric : ∃ c : R, c ≠ 0 ∧ c • x ∈ M)
    (hlocal : ∀ p : R, Prime p → ∃ a : R, ¬p ∣ a ∧ a • x ∈ M) : x ∈ M := by
  classical
  obtain ⟨c, hcz, hcx⟩ := hgeneric
  suffices ∀ c : R, c ≠ 0 → c • x ∈ M → x ∈ M from this c hcz hcx
  intro c
  induction c using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => simp
  | h₂ c hc =>
    intro _ hcx
    obtain ⟨u, rfl⟩ := hc
    simpa using M.smul_mem (↑u⁻¹ : R) hcx
  | h₃ c p hcz hp ih =>
    intro _ hpcx
    obtain ⟨a, hpa, hax⟩ := hlocal p hp
    let m : M := ⟨(p * c) • x, hpcx⟩
    let n : M := ⟨a • x, hax⟩
    have heq : a • m = (p * c) • n := by
      apply Subtype.ext
      change a • ((p * c) • x) = (p * c) • (a • x)
      exact smul_comm a (p * c) x
    let b := Module.Free.chooseBasis R M
    have hdvd : ∀ i, p ∣ b.repr m i := by
      intro i
      have hcoord := congrArg (fun z : M => b.repr z i) heq
      simp only [map_smul, Finsupp.smul_apply, smul_eq_mul] at hcoord
      have hmul : p ∣ a * b.repr m i := by
        rw [hcoord]
        exact dvd_mul_of_dvd_left (dvd_mul_right p c) _
      exact (hp.dvd_mul.mp hmul).resolve_left hpa
    obtain ⟨m', hm'⟩ := basis_divide b p m hdvd
    have hcx : c • x = (m' : E) := by
      apply smul_right_injective E hp.ne_zero
      have hval := congrArg (fun z : M => (z : E)) hm'
      change p • (m' : E) = (p * c) • x at hval
      simpa only [mul_smul] using hval.symm
    exact ih hcz (hcx ▸ m'.property)

end KLInvariance.EdgeLattice


end

section

namespace KLInvariance.Hilbert
universe uk um
variable {k : Type uk} {M : Type um} [Field k] [AddCommGroup M] [Module k M]

/-- The actual degree-n vector space of a submodule, expressed in the fixed
ambient homogeneous piece. -/
def piece (𝓜 : ℤ → Submodule k M) (S : Submodule k M) (n : ℤ) :
    Submodule k (𝓜 n) := S.comap (𝓜 n).subtype

noncomputable def term (𝓜 : ℤ → Submodule k M) (S : Submodule k M)
    (q : ℝ) (n : ℤ) : ℝ := (Module.finrank k (piece 𝓜 S n) : ℝ)*q^n

noncomputable def value (𝓜 : ℤ → Submodule k M) (S : Submodule k M)
    (q : ℝ) : ℝ := ∑' n : ℤ, term 𝓜 S q n

end KLInvariance.Hilbert

end


end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_OrdinaryR
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Construction of ordinary R-polynomials, left-simple recursion, degree bounds and inverse kernels.
-/

section
namespace KLInvariance

open Polynomial

universe u v u' v'

variable {B : Type u} {W : Type v} [klPreservedInstance1 : Group W] {M : CoxeterMatrix B}

namespace OrdinaryR

open LaurentPolynomial

noncomputable local instance instDecidableEq_solutions_1_rae6711_1 : DecidableEq W := Classical.decEq W
noncomputable def variableUnit : (LaurentPolynomial ℤ)ˣ :=
  (LaurentPolynomial.isUnit_T (R := ℤ) 1).unit

@[simp] theorem variableUnit_val : (variableUnit : LaurentPolynomial ℤ) = T 1 :=
  (LaurentPolynomial.isUnit_T (R := ℤ) 1).unit_spec

end OrdinaryR


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

namespace CanonicalP

noncomputable local instance instDecidableEq_solutions_2_rae6711_1 : DecidableEq W := Classical.decEq W
/-- The strict lower half of a polynomial, used in the KL recursion. -/
noncomputable def lowPart (d : ℕ) (p : ℤ[X]) : ℤ[X] :=
  ∑ n ∈ Finset.range ((d + 1) / 2), Polynomial.monomial n (p.coeff n)

@[simp] theorem coeff_lowPart (d : ℕ) (p : ℤ[X]) (n : ℕ) :
    (lowPart d p).coeff n = if 2 * n < d then p.coeff n else 0 := by
  classical
  simp only [lowPart, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
  rw [Finset.sum_ite_eq']
  have he : n < (d + 1) / 2 ↔ 2 * n < d := by omega
  simp only [Finset.mem_range, he]

end CanonicalP

end KLInvariance

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

namespace KLInvariance.TitsSpace
open Module
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
noncomputable section
local instance instDecidable_solutions_5 (p : Prop) : Decidable p := Classical.propDecidable p

end
end KLInvariance.TitsSpace


namespace KLInvariance.SchedulePaths
universe u v w
variable {V : Type u} {E : Type v} {R : Type w}
noncomputable section
local instance instDecidable_solutions (p : Prop) : Decidable p := Classical.propDecidable p

end
end KLInvariance.SchedulePaths

/-! NEW GRAPH CLOSURE -/


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

namespace KLInvariance.LocalCover
universe u v w
variable {R : Type u} [CommRing R] {ι : Type v} [Fintype ι]
  (M : ι → Type w) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]

/-- Coordinatewise membership in the ideal multiple of a finite product. -/
lemma pi_mem_ideal_smul (I : Ideal R) (f : ∀ i, M i)
    (hf : ∀ i, f i ∈ I • (⊤ : Submodule R (M i))) :
    f ∈ I • (⊤ : Submodule R (∀ i, M i)) := by
  classical
  have hs (i : ι) : Pi.single i (f i) ∈ I • (⊤ : Submodule R (∀ i, M i)) := by
    have hmap : (I • (⊤ : Submodule R (M i))).map (LinearMap.single R M i) ≤
        I • (⊤ : Submodule R (∀ i, M i)) := by
      rw [Submodule.map_smul'']
      exact Submodule.smul_mono le_rfl le_top
    exact hmap ⟨f i,hf i,rfl⟩
  simpa only [Finset.univ_sum_single] using Submodule.sum_mem (I • (⊤ : Submodule R (∀ i, M i))) (t := Finset.univ) (fun i _ => hs i)

end KLInvariance.LocalCover

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

/-! Extension by zero from a full lower ideal. Proof-indexed finite products
avoid informal identifications of the integral stalks at boundary vertices. -/
namespace KLInvariance.MomentGraph
universe uk ua um
variable {k : Type uk}
  [Field k]
  {A : Type ua}
  [CommRing A]
  [Algebra k A]
  {𝓐 : ℤ → Submodule k A}
  {V E : Type um}
  [PartialOrder V]
  (K : Set V)
  (hK : IsLowerSet K)

namespace GradedSheaf
noncomputable section
attribute [local instance] Classical.propDecidable

abbrev Witness (p : Prop) := ULift.{um} (PLift p)

end
end GradedSheaf
end KLInvariance.MomentGraph

end


section


namespace KLInvariance.MomentGraph.Sheaf
universe ur uv ue
variable {R : Type ur}
  [CommRing R]
  {V : Type uv}
  [PartialOrder V]
  {E : Type ue}
  (α : E → R)
  (c : V)
noncomputable section

def quotientLinear (e : E) : R →ₗ[R] R ⧸ Ideal.span {α e} :=
  (Ideal.Quotient.mkₐ R (Ideal.span {α e})).toLinearMap

end
end KLInvariance.MomentGraph.Sheaf

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

namespace KLInvariance.Graded
open Polynomial
universe uk us um ui
variable {k : Type uk}
  [Field k]
  {σ : Type us}
  [Finite σ]
  {M : Type um}
  [AddCommGroup M]
  [Module k M]
  [Module (MvPolynomial σ k) M]
  [IsScalarTower k (MvPolynomial σ k) M]
  (𝓜 : ℤ → Submodule k M)
  [DirectSum.Decomposition 𝓜]

structure NonnegativeBasis where
  index : Type um
  finite : Fintype index
  basis : Module.Basis index (MvPolynomial σ k) M
  degree : index → ℕ
  homogeneous : ∀ i, basis i ∈ 𝓜 (degree i)

attribute [instance] NonnegativeBasis.finite

namespace NonnegativeBasis
variable {𝓜} (b : NonnegativeBasis (σ := σ) 𝓜)

noncomputable def polynomial : ℤ[X] := ∑ i, X ^ b.degree i

end NonnegativeBasis

end KLInvariance.Graded

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

namespace KLInvariance.BruhatGraph
open Module TitsSpace _root_.OAI.KLInvariance.Graded MomentGraph Polynomial
universe u
variable {I : Type u}
  [Fintype I]
  {M : CoxeterMatrix I}
  {W : Type u}
  [Group W]
  (cs : CoxeterSystem M W)
  (b : W)
  {σ : Type u}
  [Fintype σ]
noncomputable section
local instance instDecidable_solutions_1 (p : Prop) : Decidable p := Classical.propDecidable p

end
end KLInvariance.BruhatGraph

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

/-! Upper sets and actual finite-word projection predicates. -/
namespace KLInvariance.TitsSpace
open Module
universe u v
variable {I : Type u} [klPreservedInstance11 : Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section

 def simpleUnion (i : I) (U : Set W) : Set W := {x | x∈U ∨ cs.simple i*x∈U}
 def simpleInter (i : I) (U : Set W) : Set W := {x | x∈U ∧ cs.simple i*x∈U}

 omit [Fintype I] in
 theorem simpleInter_stable (i : I) (U : Set W) (x : W) :
    cs.simple i*x∈simpleInter cs i U ↔ x∈simpleInter cs i U := by
  change (cs.simple i*x∈U ∧ cs.simple i*(cs.simple i*x)∈U) ↔ (x∈U ∧ cs.simple i*x∈U)
  rw [cs.simple_mul_simple_cancel_left,and_comm]

end
end KLInvariance.TitsSpace

end


section

/-! Explicit linear descent and split exact sequences for projected modules. -/
namespace KLInvariance.ProjectiveRange
universe ur um up uq
variable {R : Type ur} [CommRing R]
  {M : Type um} [AddCommGroup M] [Module R M]
  {P : Type up} [AddCommGroup P] [Module R P]
  {Q : Type uq} [AddCommGroup Q] [Module R Q]
noncomputable section

 def descend (f : M →ₗ[R] P) (hf : Function.Surjective f) (g : M →ₗ[R] Q)
    (hg : ∀ m, f m=0 → g m=0) : P →ₗ[R] Q :=
  ((LinearMap.ker f).liftQ g hg).comp (f.quotKerEquivOfSurjective hf).symm.toLinearMap

 theorem descend_apply (f : M →ₗ[R] P) (hf : Function.Surjective f) (g : M →ₗ[R] Q)
    (hg : ∀ m, f m=0 → g m=0) (m : M) : descend f hf g hg (f m)=g m := by
  change (LinearMap.ker f).liftQ g hg ((f.quotKerEquivOfSurjective hf).symm (f m))=g m
  rw [LinearMap.quotKerEquivOfSurjective_symm_apply]
  rfl

 theorem projective_of_end (f : M →ₗ[R] P) (hf : Function.Surjective f)
    [Module.Projective R M] (e : Module.End R M)
    (he : ∀ m, f (e m)=f m) (hz : ∀ m, f m=0 → e m=0) : Module.Projective R P := by
  apply Module.Projective.of_split (descend f hf e hz) f
  apply LinearMap.ext
  intro p
  obtain ⟨m,rfl⟩ := hf p
  rw [LinearMap.comp_apply,descend_apply,he,LinearMap.id_apply]

 def kernelRetraction (f : M →ₗ[R] P) (s : P →ₗ[R] M)
    (hs : ∀ p, f (s p)=p) : M →ₗ[R] LinearMap.ker f :=
  (LinearMap.id-s.comp f).codRestrict (LinearMap.ker f) (fun m => by
    change f (m-s (f m))=0
    rw [map_sub,hs,sub_self])

 theorem kernel_projective (f : M →ₗ[R] P) (hf : Function.Surjective f)
    [Module.Projective R M] [Module.Projective R P] : Module.Projective R (LinearMap.ker f) := by
  obtain ⟨s,hs⟩ := Module.projective_lifting_property f (LinearMap.id : P →ₗ[R] P) hf
  have hs' : ∀ p, f (s p)=p := LinearMap.congr_fun hs
  apply Module.Projective.of_split (LinearMap.ker f).subtype (kernelRetraction f s hs')
  apply LinearMap.ext
  intro m
  apply Subtype.ext
  change (m : M)-s (f m)=m
  rw [m.property,map_zero,sub_zero]

 def splitEquiv (f : M →ₗ[R] P) (s : P →ₗ[R] M) (hs : ∀ p, f (s p)=p) :
    M ≃ₗ[R] (LinearMap.ker f × P) :=
  { (kernelRetraction f s hs).prod f with
    invFun := fun z => z.1.val+s z.2
    left_inv := fun m => sub_add_cancel m (s (f m))
    right_inv := by
      intro z
      apply Prod.ext
      · apply Subtype.ext
        change z.1.val+s z.2-s (f (z.1.val+s z.2))=z.1.val
        rw [map_add,z.1.property,zero_add,hs]
        exact add_sub_cancel_right _ _
      · change f (z.1.val+s z.2)=z.2
        rw [map_add,z.1.property,zero_add,hs] }

 theorem projective_of_kernel (f : M →ₗ[R] P) (hf : Function.Surjective f)
    [Module.Projective R P] [Module.Projective R (LinearMap.ker f)] : Module.Projective R M := by
  obtain ⟨s,hs⟩ := Module.projective_lifting_property f (LinearMap.id : P →ₗ[R] P) hf
  exact Module.Projective.of_equiv (splitEquiv f s (LinearMap.congr_fun hs)).symm

end
end KLInvariance.ProjectiveRange

end


section

namespace KLInvariance
universe ur un up uq
variable {R : Type ur} [CommRing R]
  {N : Type un} [klPreservedInstance12 : AddCommGroup N] [Module R N]
  {P : Type up} [klPreservedInstance13 : AddCommGroup P] [Module R P]
  {Q : Type uq} [klPreservedInstance14 : AddCommGroup Q] [Module R Q]
 theorem injective_of_zero_lift (f : N →ₗ[R] P) (hf : Function.Surjective f) (g : P →ₗ[R] Q)
    (h : ∀ n, g (f n)=0 → f n=0) : Function.Injective g := by
  apply LinearMap.ker_eq_bot.mp
  rw [LinearMap.ker_eq_bot']
  intro p hp
  obtain ⟨n,rfl⟩ := hf p
  exact h n hp
 theorem maps_eq_iff_of_zero_iff (f : N →ₗ[R] P) (g : N →ₗ[R] Q)
    (h : ∀ n, f n=0 ↔ g n=0) (m n : N) : f m=f n ↔ g m=g n := by
  rw [← sub_eq_zero,← map_sub,h,map_sub,sub_eq_zero]
include klPreservedInstance12 klPreservedInstance13 klPreservedInstance14 in
 theorem functions_eq_of_surjective (f : N → P) (hf : Function.Surjective f)
    (g h : P → Q) (he : ∀ n, g (f n)=h (f n)) (p : P) : g p=h p := by
  have _ := klPreservedInstance12
  have _ := klPreservedInstance13
  have _ := klPreservedInstance14
  obtain ⟨n,rfl⟩ := hf p
  exact he n
end KLInvariance

end


section

/-! Genuine first/reflected-tail maps on projected upper-set images. -/
namespace KLInvariance.TitsSpace
open Module TensorProduct
open ProjectiveRange
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section

 def simplePull (i : I) (U : Set W) : Set W := {x | cs.simple i*x∈U}

end
end KLInvariance.TitsSpace

end


section

namespace KLInvariance
universe ur um un up
variable {R : Type ur} [CommRing R]
  {M : Type um} [AddCommGroup M] [Module R M]
  {N : Type un} [AddCommGroup N] [Module R N]
  {P : Type up} [AddCommGroup P] [Module R P]
noncomputable section
 theorem projective_of_same_range (f : M →ₗ[R] P) (hf : Function.Injective f)
    (g : N →ₗ[R] P) (hg : Function.Injective g) (h : LinearMap.range f=LinearMap.range g)
    [Module.Projective R N] : Module.Projective R M :=
  Module.Projective.of_equiv (((LinearEquiv.ofInjective g hg).trans
    (LinearEquiv.ofEq _ _ h.symm)).trans (LinearEquiv.ofInjective f hf).symm)

attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

end
end KLInvariance

end


section

namespace KLInvariance
universe ur um uh up us
variable {R : Type ur} [CommRing R]
  {M : Type um} [AddCommGroup M] [Module R M]
  {H : Type uh} [AddCommGroup H] [Module R H]
  {P : Type up} [AddCommGroup P] [Module R P]
  {S : Type us} [AddCommGroup S] [Module R S]

 theorem kernel_coordinate_injective (f : M →ₗ[R] P) (g : M →ₗ[R] S)
    (h : Function.Injective (f.prod g)) :
    Function.Injective (g.comp (LinearMap.ker f).subtype) := by
  intro m n he
  apply Subtype.ext
  apply h
  exact Prod.ext (m.property.trans n.property.symm) he

 theorem common_kernel_coordinate_injective (r : M →ₗ[R] H) (f : M →ₗ[R] P) (g : M →ₗ[R] S)
    (h : Function.Injective (f.prod g)) :
    Function.Injective (g.comp (LinearMap.ker r ⊓ LinearMap.ker f).subtype) := by
  intro m n he
  apply Subtype.ext
  apply h
  exact Prod.ext (m.property.2.trans n.property.2.symm) he

 theorem projective_of_coordinates (f : M →ₗ[R] P) (hf : Function.Injective f)
    (g : H →ₗ[R] P) (hg : Function.Injective g)
    (hfg : ∀ m, ∃ n, f m=g n) (hgf : ∀ n, ∃ m, f m=g n)
    [Module.Projective R H] : Module.Projective R M := by
  apply projective_of_same_range f hf g hg
  ext p
  constructor
  · rintro ⟨m,rfl⟩
    obtain ⟨n,hn⟩ := hfg m
    exact ⟨n,hn.symm⟩
  · rintro ⟨n,rfl⟩
    exact hgf n

end KLInvariance

end


section

/-! Integral adjoints, not restrictions of a form to arbitrary summands.
This is used to transport a genuine BMP projector through the word duality. -/
namespace PerfectAdjoint
open Module
universe ur um
variable {R : Type ur} [CommRing R]
  {M : Type um} [AddCommGroup M] [Module R M]
  (d : M ≃ₗ[R] Dual R M)
noncomputable section

 def adjoint (f : End R M) : End R M :=
  d.symm.toLinearMap.comp (f.dualMap.comp d.toLinearMap)

 theorem pairing (f : End R M) (m n : M) : d (adjoint d f m) n=d m (f n) := by
  change d (d.symm (f.dualMap (d m))) n=d m (f n)
  rw [LinearEquiv.apply_symm_apply]
  rfl

 theorem adjoint_comp (f g : End R M) : adjoint d (f.comp g)=(adjoint d g).comp (adjoint d f) := by
  apply LinearMap.ext
  intro m
  apply d.injective
  apply LinearMap.ext
  intro n
  rw [pairing]
  change d m (f (g n))=d (adjoint d g (adjoint d f m)) n
  rw [pairing,pairing]

 theorem adjoint_idempotent (f : End R M) (hf : ∀ m, f (f m)=f m) (m : M) :
    adjoint d f (adjoint d f m)=adjoint d f m := by
  apply d.injective
  apply LinearMap.ext
  intro n
  rw [pairing,pairing,hf,pairing]

 theorem symmetric_pairing (hsym : ∀ m n, d m n=d n m)
    (f : End R M) (m n : M) : d m (adjoint d f n)=d (f m) n := by
  rw [hsym,pairing,hsym]

 theorem adjoint_adjoint (hsym : ∀ m n, d m n=d n m) (f : End R M) :
    adjoint d (adjoint d f)=f := by
  apply LinearMap.ext
  intro m
  apply d.injective
  apply LinearMap.ext
  intro n
  rw [pairing,symmetric_pairing d hsym]

end
end PerfectAdjoint

end


end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_BalancedPairings
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Graded stalk duality, integral perfect balanced all-sections pairings, recognition and top grading.
-/


section

namespace LinearDescent
universe ur um ux
variable {R : Type ur} [CommRing R]
  {M : Type um} [AddCommGroup M] [Module R M]
  {X : Type ux} [AddCommGroup X] [Module R X]
  (f : M →ₗ[R] X) (hf : Function.Surjective f) (e : Module.End R M)
  (he : ∀ m, f m=0 → f (e m)=0)
noncomputable section

 def descend : Module.End R X :=
  ((LinearMap.ker f).liftQ (f.comp e) he).comp
    (f.quotKerEquivOfSurjective hf).symm.toLinearMap

 theorem descend_apply (m : M) : descend f hf e he (f m)=f (e m) := by
  change (LinearMap.ker f).liftQ (f.comp e) he
    ((f.quotKerEquivOfSurjective hf).symm (f m))=f (e m)
  rw [LinearMap.quotKerEquivOfSurjective_symm_apply]
  rfl

end
end LinearDescent

end


section

namespace PerfectAdjoint
open Module
universe ur um
variable {R : Type ur} [CommRing R]
  {M : Type um} [AddCommGroup M] [Module R M]
  (d : M ≃ₗ[R] Dual R M) (f : End R M) (hf : ∀ m, f (f m)=f m)
noncomputable section

include hf in
 theorem range_projector_split (m : f.range) : f.rangeRestrict (f.range.subtype m)=m := by
  apply Subtype.ext
  obtain ⟨n,hn⟩ := m.property
  change f m.val=m.val
  rw [← hn,hf]

end
end PerfectAdjoint

end


section


namespace PerfectAdjoint
open Module
universe ur um
variable {R : Type ur} [CommRing R] {N : Type um} [AddCommGroup N] [Module R N]
 theorem adjoint_zero (d : N ≃ₗ[R] Dual R N) : adjoint d (0 : End R N)=0 := by
  apply LinearMap.ext
  intro m
  apply d.injective
  apply LinearMap.ext
  intro n
  rw [pairing]
  simp
end PerfectAdjoint

end


end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_CharacterReciprocity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Conditional boundary-sheaf duality and stalk-character propositions, free sheaves, actual R-reciprocity and lower convolution. StalkCharacterObligation remains a Prop, not an unconditional character theorem or a premise of the R-first route.
-/


section


namespace KLInvariance.BruhatGraph
open Module TitsSpace _root_.OAI.KLInvariance.Graded MomentGraph
universe u
variable {I : Type u}
  [Fintype I]
  {M : CoxeterMatrix I}
  {W : Type u}
  [Group W]
  (cs : CoxeterSystem M W)
  (b : W)
  {σ : Type u}
  [Fintype σ]
noncomputable section

local instance charDecEqC (a : Type*) : DecidableEq a := Classical.decEq a

end
end KLInvariance.BruhatGraph

end


section

namespace KLInvariance.BruhatGraph
open Module TitsSpace _root_.OAI.KLInvariance.Graded MomentGraph Polynomial
universe u
variable {I : Type u}
  [Fintype I]
  {M : CoxeterMatrix I}
  {W : Type u}
  [Group W]
  (cs : CoxeterSystem M W)
  (b : W)
  {σ : Type u}
  [Fintype σ]
noncomputable section
local instance instDecidable_solutions_2 (p : Prop) : Decidable p := Classical.propDecidable p

end
end KLInvariance.BruhatGraph

end


section

namespace KLInvariance.BruhatGraph
open Module TitsSpace _root_.OAI.KLInvariance.Graded MomentGraph Polynomial
universe u
variable {I : Type u}
  [Fintype I]
  {M : CoxeterMatrix I}
  {W : Type u}
  [Group W]
  (cs : CoxeterSystem M W)
  (b : W)
  {σ : Type u}
  [Fintype σ]
noncomputable section
local instance instDecidable_solutions_3 (p : Prop) : Decidable p := Classical.propDecidable p

end
end KLInvariance.BruhatGraph

end


section

namespace KLInvariance.BruhatGraph
open Module TitsSpace _root_.OAI.KLInvariance.Graded MomentGraph Polynomial
universe u
variable {I : Type u}
  [Fintype I]
  {M : CoxeterMatrix I}
  {W : Type u}
  [Group W]
  (cs : CoxeterSystem M W)
  (b : W)
  {σ : Type u}
  [Fintype σ]
noncomputable section
local instance instDecidable_solutions_4 (p : Prop) : Decidable p := Classical.propDecidable p

end
end KLInvariance.BruhatGraph

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

namespace KLInvariance.SchedulePaths
open scoped BigOperators
universe u v w
variable {V : Type u} {E : Type v} {R : Type w}
noncomputable section
local instance instDecidable_solutions_3 (p : Prop) : Decidable p := Classical.propDecidable p

end
end KLInvariance.SchedulePaths

end


end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_DihedralIntervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Signed dihedral coordinates, actual dihedral intervals, exact later-edge counts and root-plane calculations.
-/

section

namespace KLInvariance.Dihedral
variable {W : Type*} [Group W] {M : CoxeterMatrix Bool}
noncomputable section

 def rotation (cs : CoxeterSystem M W) : W := cs.simple false * cs.simple true

/-- The signed coordinate evaluates both alternating rays in the same group.
The Euclidean quotient also gives the correct odd negative coordinates. -/
 def indexWord (cs : CoxeterSystem M W) (i : ℤ) : W :=
  if i % 2 = 0 then rotation cs ^ (i/2)
  else rotation cs ^ (i/2) * cs.simple false

 theorem indexWord_even (cs : CoxeterSystem M W) (n : ℤ) :
    indexWord cs (2*n) = rotation cs ^ n := by simp [indexWord]

end
end KLInvariance.Dihedral

end


section


namespace KLInvariance.SignedDihedral
noncomputable section
local instance instDecidable_solutions (p : Prop) : Decidable p := Classical.propDecidable p

end
end KLInvariance.SignedDihedral

end


section

namespace KLInvariance.Dihedral
variable {W : Type*} [Group W] {M : CoxeterMatrix Bool}
noncomputable section
local instance instDecidableEq_solutions : DecidableEq W := Classical.decEq W

end
end KLInvariance.Dihedral

end


section

namespace KLInvariance.Dihedral
variable {W : Type*} [Group W] {M : CoxeterMatrix Bool}
noncomputable section

 def GoodIndex (cs : CoxeterSystem M W) (i : ℤ) : Prop :=
  ∀ w, (∀ z, cs.length z ≤ cs.length w) → -(cs.length w:ℤ) < i ∧ i ≤ (cs.length w:ℤ)

end
end KLInvariance.Dihedral

end


end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_TerminalKernels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
All-section transport, terminal kernels, scalar quotients, height-one membership in free targets and scaled edge-image inclusion.
-/


section

/-! Native endpoint normalization from the ACTUAL stalk characters. Unlike the
KL-labelled endpoints, these need neither character recognition nor Hodge. -/
namespace KLInvariance.BruhatGraph
open Module TitsSpace _root_.OAI.KLInvariance.Graded MomentGraph Polynomial SchedulePaths
universe u
variable {I : Type u}
  [Fintype I]
  {M : CoxeterMatrix I}
  {W : Type u}
  [Group W]
  (cs : CoxeterSystem M W)
  (b : W)
  {σ : Type u}
  [Fintype σ]
noncomputable section
local instance instDecidableEq_solutions (a : Type*) : DecidableEq a := Classical.decEq a

end
end KLInvariance.BruhatGraph

end


end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_SimultaneousInvariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
R-first simultaneous invariance and transported-schedule terminal-kernel freeness: upper-interval freeness, lower-interval cancellation, reversal and endpoint bottom freeness; all-entry transport and KL degree rigidity.
-/


section


namespace KLInvariance.Comparison
open Polynomial
noncomputable section

def scaledPolynomial (t : ℝ) (d : ℕ) (p : ℤ[X]) : ℝ :=
  t ^ (-(d : ℤ)) * p.eval₂ (Int.castRingHom ℝ) (t^2)

end
end KLInvariance.Comparison

end


end OAI
end


