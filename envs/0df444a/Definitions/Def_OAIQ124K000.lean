-- Prove2me | Definitions.Def_OAIQ124K000
-- name    : OAIQ124K000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-30T05:43:15.311042+00:00
-- url     : https://prove2.me/theorems/e1b0530a-32ce-4992-9dfd-cb5c76ec04b2
-- title:
--   Definitions bundle OAIQ124K000 of the split of OpenAI, Combinatorial invariance of Kazhdan–Lusztig polynomials (result family 168)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.KLInvariance.combinatorial_invariance`, carved from OpenAI's openai/math development (OpenAI, *Combinatorial invariance of Kazhdan–Lusztig polynomials (result family 168)*, OpenAI Math Release, September 24, 2026, result family 168, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 553 declarations of OpenAI's Lean: 195 definitions, 10 inductive types or structures, 9 instances and 339 theorems. The definitions and types are `OAI.AdjointSummandDuality.adjointEquivDual`, `OAI.AdjointSummandDuality.adjointProjector`, `OAI.AdjointSummandDuality.adjointSummand`, `OAI.AdjointSummandDuality.dualProjection`, `OAI.AdjointSummandDuality.dualSection`, `OAI.ConjugateRange.conjugate`, `OAI.ConjugateRange.equiv`, `OAI.ConjugateRange.map`, `OAI.KLInvariance.AdaptedDyer.Edge`, `OAI.KLInvariance.AdaptedDyer.Nonsimple`, `OAI.KLInvariance.AdaptedDyer.edgeFinset`, `OAI.KLInvariance.AdaptedDyer.instDecidable_solutions`, `OAI.KLInvariance.AdaptedDyer.nonsimplePaths`, `OAI.KLInvariance.AdaptedDyer.paths`, `OAI.KLInvariance.AdaptedDyer.polynomial`, `OAI.KLInvariance.AdaptedDyer.rootLabel`, `OAI.KLInvariance.AdaptedDyer.rotateEdge`, `OAI.KLInvariance.AdaptedDyer.schedule`, `OAI.KLInvariance.AdaptedDyer.score`, `OAI.KLInvariance.AdaptedDyer.simpleEdge`, `OAI.KLInvariance.AdaptedDyer.source`, `OAI.KLInvariance.AdaptedDyer.target`, `OAI.KLInvariance.BruhatGraph.Coefficient`, `OAI.KLInvariance.BruhatGraph.Edge`, `OAI.KLInvariance.BruhatGraph.graph`, `OAI.KLInvariance.BruhatGraph.label`, `OAI.KLInvariance.BruhatGraph.polynomialLabel`, `OAI.KLInvariance.BruhatGraph.root`, `OAI.KLInvariance.BruhatGraph.source`, `OAI.KLInvariance.BruhatGraph.target`, `OAI.KLInvariance.Cotangent.action`, `OAI.KLInvariance.Cotangent.root`, `OAI.KLInvariance.Cotangent.simple`, `OAI.KLInvariance.CoxeterSupport.instDecidableEq_solutions`, `OAI.KLInvariance.CoxeterSupport.reflectionAction`, `OAI.KLInvariance.CoxeterSupport.simpleAction`, `OAI.KLInvariance.CoxeterSupport.wordAction`, `OAI.KLInvariance.Dihedral.alt`, `OAI.KLInvariance.Dihedral.edgeFlip`, `OAI.KLInvariance.Dihedral.instDecidable_solutions` and 165 more.
--
--   **Sources.** They come from these modules of lean/OAI/RepresentationTheory, in whole or in part: `KazhdanLusztig_BalancedPairings`, `KazhdanLusztig_Bruhat`, `KazhdanLusztig_CharacterReciprocity`, `KazhdanLusztig_Coxeter`, `KazhdanLusztig_Decomposition`, `KazhdanLusztig_Dihedral`, `KazhdanLusztig_DyerPaths`, `KazhdanLusztig_GradedModules`, `KazhdanLusztig_GradedSheaves`, `KazhdanLusztig_Hecke`, `KazhdanLusztig_ModuleAlgebra`, `KazhdanLusztig_OrdinaryR`, `KazhdanLusztig_ReflectionOrders`, `KazhdanLusztig_ReflectionSchedules`, `KazhdanLusztig_SheafMorphisms`, `KazhdanLusztig_Sheaves`, `KazhdanLusztig_Tits`.
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
theorem ite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : c) :
    (if c then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : ¬c) :
    (if c then a else b) = b := if_neg h
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


/-! The local algebra step in `loc:decomposition`, source §4.4. The maps
are actual linear maps; neither a decomposition nor a lift is assumed. -/


namespace KLInvariance.Graded

variable {k A M : Type*} [CommRing k] [CommRing A] [Algebra k A]
  [AddCommGroup M] [Module k M] [Module A M] [klPreservedInstance4 : IsScalarTower k A M]

noncomputable def component (𝓜 : ℤ → Submodule k M)
    [DirectSum.Decomposition 𝓜] (n : ℤ) : M →ₗ[k] M where
  toFun m := DirectSum.decompose 𝓜 m n
  map_add' x y := by simp [DirectSum.decompose_add]
  map_smul' r m := by simp [DirectSum.decompose_smul, DirectSum.smul_apply]

def positiveIdeal (𝓐 : ℤ → Submodule k A) : Ideal A :=
  Ideal.span {a | ∃ n : ℤ, 0 < n ∧ a ∈ 𝓐 n}

end KLInvariance.Graded


end

end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_GradedModules
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Graded polynomial modules, projective presentations, finite homogeneous generators and uniqueness of minimal covers.
-/

section

namespace KLInvariance.Graded
open scoped Pointwise
universe uk ua um
variable {k : Type uk} {A : Type ua} {M : Type um} [Field k] [CommRing A] [klPreservedInstance9 : Algebra k A]
  [AddCommGroup M] [Module k M] [Module A M] [klPreservedInstance8 : IsScalarTower k A M]

include klPreservedInstance8 in
/-- Graded Nakayama in its generation form. The submodule is closed under
actual homogeneous components, rather than assumed to be the whole module. -/
theorem eq_top_of_positive_smul_sup
    (𝓐 : ℤ → Submodule k A) (𝓜 : ℤ → Submodule k M)
    [DirectSum.Decomposition 𝓜] [SetLike.GradedSMul 𝓐 𝓜]
    (d₀ : ℤ) (hbound : ∀ j < d₀, 𝓜 j = ⊥)
    (N : Submodule A M) (hN : ∀ n m, m ∈ N → (DirectSum.decompose 𝓜 m n : M) ∈ N)
    (hgen : N ⊔ positiveIdeal 𝓐 • (⊤ : Submodule A M) = ⊤) : N = ⊤ := by
  have _ := klPreservedInstance8
  classical
  have hlow : ∀ j < d₀, ∀ m ∈ 𝓜 j, m ∈ N := by
    intro j hj m hm
    have hm0 : m = 0 := by simpa [hbound j hj] using hm
    simp [hm0]
  have hind : ∀ n : ℕ, ∀ m ∈ 𝓜 (d₀+n), m ∈ N := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      let p := component 𝓜 (d₀+n)
      have hsmul (i : ℤ) (hi : 0 < i) (a : A) (ha : a ∈ 𝓐 i) :
          ∀ m : M, p (a • m) ∈ N := by
        intro m
        refine DirectSum.Decomposition.inductionOn 𝓜 ?_ ?_ ?_ m
        · simp
        · intro j m
          by_cases hj : j < d₀+n
          · have hm : (m : M) ∈ N := by
              by_cases hj₀ : j < d₀
              · exact hlow j hj₀ m m.property
              · have heq : d₀ + (j-d₀).toNat = j := by omega
                exact ih (j-d₀).toNat (by omega) m (heq.symm ▸ m.property)
            exact hN _ _ (N.smul_mem a hm)
          · have hdeg : i+j ≠ d₀+n := by omega
            have ham : a • (m : M) ∈ 𝓜 (i+j) :=
              SetLike.GradedSMul.smul_mem ha m.property
            have heq : p (a • (m : M)) = 0 :=
              DirectSum.decompose_of_mem_ne 𝓜 ham hdeg
            simp [heq]
        · intro x y hx hy
          simpa only [smul_add, map_add] using N.add_mem hx hy
      let J : Ideal A :=
        { carrier := {a | ∀ m : M, p (a • m) ∈ N}
          zero_mem' := by simp [N.zero_mem]
          add_mem' := by
            intro a b ha hb m
            simpa only [add_smul, map_add] using N.add_mem (ha m) (hb m)
          smul_mem' := by
            intro r a ha m
            change p ((r*a) • m) ∈ N
            rw [mul_comm r a, mul_smul]
            exact ha (r • m) }
      have hIJ : positiveIdeal 𝓐 ≤ J := by
        apply Ideal.span_le.mpr
        rintro a ⟨i,hi,ha⟩
        exact hsmul i hi a ha
      have hp : ∀ m : M, p m ∈ N := by
        intro m
        have hm : m ∈ N ⊔ positiveIdeal 𝓐 • (⊤ : Submodule A M) := by
          rw [hgen]; trivial
        obtain ⟨x,hx,y,hy,rfl⟩ := Submodule.mem_sup.mp hm
        rw [map_add]
        apply N.add_mem (hN _ _ hx)
        refine Submodule.smul_induction_on hy ?_ ?_
        · intro a ha z _; exact hIJ ha z
        · intro z w hz hw; simpa only [map_add] using N.add_mem hz hw
      intro m hm
      have hcomp : p m=m := DirectSum.decompose_of_mem_same 𝓜 hm
      exact hcomp ▸ hp m
  have homogeneous_mem (j : ℤ) (m : M) (hm : m ∈ 𝓜 j) : m ∈ N := by
    by_cases hj : j < d₀
    · exact hlow j hj m hm
    · have heq : d₀ + (j-d₀).toNat = j := by omega
      exact hind (j-d₀).toNat m (heq.symm ▸ hm)
  apply top_unique
  intro m _
  exact DirectSum.Decomposition.inductionOn 𝓜 N.zero_mem
    (fun m => homogeneous_mem _ m m.property)
    (fun _ _ hx hy => N.add_mem hx hy) m

include klPreservedInstance8 in
/-- Projection of a scalar multiple of a homogeneous vector. -/
theorem component_smul_homogeneous
    (𝓐 : ℤ → Submodule k A) (𝓜 : ℤ → Submodule k M)
    [DirectSum.Decomposition 𝓐] [DirectSum.Decomposition 𝓜]
    [SetLike.GradedSMul 𝓐 𝓜] (a : A) (m : M) (d n : ℤ) (hm : m ∈ 𝓜 d) :
    component 𝓜 n (a • m) = component 𝓐 (n-d) a • m := by
  have _ := klPreservedInstance8
  classical
  refine DirectSum.Decomposition.inductionOn 𝓐 ?_ ?_ ?_ a
  · simp
  · intro i a
    by_cases hi : i = n-d
    · have hsum : i+d = n := by omega
      have ham : (a : A) • m ∈ 𝓜 n := hsum ▸
        SetLike.GradedSMul.smul_mem a.property hm
      rw [show component 𝓜 n ((a : A) • m) = (a : A) • m from
        DirectSum.decompose_of_mem_same 𝓜 ham]
      rw [show component 𝓐 (n-d) (a : A) = (a : A) from
        DirectSum.decompose_of_mem_same 𝓐 (hi ▸ a.property)]
    · have hsum : i+d ≠ n := by omega
      rw [show component 𝓜 n ((a : A) • m) = 0 from
        DirectSum.decompose_of_mem_ne 𝓜
          (SetLike.GradedSMul.smul_mem a.property hm) hsum,
        show component 𝓐 (n-d) (a : A) = 0 from
        DirectSum.decompose_of_mem_ne 𝓐 a.property hi, zero_smul]
  · intro a b ha hb
    simp only [add_smul, map_add, ha, hb]

include klPreservedInstance9 klPreservedInstance8 in
/-- Finite generation can be made homogeneous using the actual finite
support decomposition of each generator. -/
theorem exists_finite_homogeneous_generators
    (𝓜 : ℤ → Submodule k M) [DirectSum.Decomposition 𝓜] [Module.Finite A M] :
    ∃ t : Finset M, Submodule.span A (t : Set M) = ⊤ ∧
      ∀ m ∈ t, ∃ d : ℤ, m ∈ 𝓜 d := by
  have _ := klPreservedInstance9
  have _ := klPreservedInstance8
  classical
  obtain ⟨s,hs⟩ := Module.Finite.fg_top (R := A) (M := M)
  let t : Finset M := s.biUnion fun m =>
    (DirectSum.decompose 𝓜 m).support.image fun j => (DirectSum.decompose 𝓜 m j : M)
  refine ⟨t, ?_, ?_⟩
  · apply top_unique
    rw [← hs]
    apply Submodule.span_le.mpr
    intro m hm
    rw [← DirectSum.sum_support_decompose 𝓜 m]
    apply Submodule.sum_mem
    intro j hj
    apply Submodule.subset_span
    exact Finset.mem_biUnion.mpr ⟨m,hm,Finset.mem_image.mpr ⟨j,hj,rfl⟩⟩
  · intro m hm
    obtain ⟨a,ha,hma⟩ := Finset.mem_biUnion.mp hm
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hma
    exact ⟨j,(DirectSum.decompose 𝓜 a j).property⟩

/-- The span of finitely many homogeneous vectors is closed under each
component, as required for graded Nakayama. -/
theorem homogeneous_span_components {ι : Type*} [Fintype ι]
    (𝓐 : ℤ → Submodule k A) (𝓜 : ℤ → Submodule k M)
    [DirectSum.Decomposition 𝓐] [DirectSum.Decomposition 𝓜]
    [SetLike.GradedSMul 𝓐 𝓜] (v : ι → M) (d : ι → ℤ)
    (hv : ∀ i, v i ∈ 𝓜 (d i)) (n : ℤ) (m : M)
    (hm : m ∈ Submodule.span A (Set.range v)) :
    component 𝓜 n m ∈ Submodule.span A (Set.range v) := by
  classical
  obtain ⟨c,rfl⟩ := (Submodule.mem_span_range_iff_exists_fun A).mp hm
  rw [map_sum]
  apply Submodule.sum_mem
  intro i _
  rw [component_smul_homogeneous 𝓐 𝓜 _ _ (d i) n (hv i)]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i))

/-- Reduction of a scalar modulo the augmentation ideal gives precisely
its scalar-field action on the reduced module. -/
theorem quotient_smul_of_scalar_mod (I : Ideal A) (a : A) (c : k)
    (hac : a-algebraMap k A c ∈ I) (m : M) :
    (I • (⊤ : Submodule A M)).mkQ (a • m) =
      c • (I • (⊤ : Submodule A M)).mkQ m := by
  let J := I • (⊤ : Submodule A M)
  have hz : J.mkQ ((a-algebraMap k A c) • m) = 0 :=
    (Submodule.Quotient.mk_eq_zero J).mpr
      (Submodule.smul_mem_smul hac (Submodule.mem_top : m ∈ (⊤ : Submodule A M)))
  rw [sub_smul, map_sub] at hz
  have heq := sub_eq_zero.mp hz
  calc
    _ = J.mkQ (algebraMap k A c • m) := heq
    _ = algebraMap k A c • J.mkQ m := map_smul J.mkQ _ _
    _ = c • J.mkQ m := IsScalarTower.algebraMap_smul A c (J.mkQ m)

/-- Images of any finite generating family span the augmentation quotient
as a vector space over the degree-zero field. -/
theorem quotient_span_of_scalar_mod {ι : Type*} [Fintype ι]
    (I : Ideal A) (hscalar : ∀ a : A, ∃ c : k, a-algebraMap k A c ∈ I)
    (v : ι → M) (hv : Submodule.span A (Set.range v) = ⊤) :
    Submodule.span k (Set.range (fun i => (I • (⊤ : Submodule A M)).mkQ (v i))) = ⊤ := by
  classical
  let J := I • (⊤ : Submodule A M)
  apply top_unique
  intro z _
  obtain ⟨m,rfl⟩ := J.mkQ_surjective z
  obtain ⟨a,ha⟩ := (Submodule.mem_span_range_iff_exists_fun A).mp (hv ▸ Submodule.mem_top :
    m ∈ Submodule.span A (Set.range v))
  choose c hc using fun i => hscalar (a i)
  apply (Submodule.mem_span_range_iff_exists_fun k).mpr
  refine ⟨c, ?_⟩
  calc
    _ = J.mkQ (∑ i, a i • v i) := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i _
      exact (quotient_smul_of_scalar_mod I (a i) (c i) (hc i) (v i)).symm
    _ = J.mkQ m := congrArg J.mkQ ha


/-- The augmentation for a nonnegatively supported integer grading is
actual degree-zero projection. -/
noncomputable def nonnegativeAugmentation
    (𝓐 : ℤ → Submodule k A) [DirectSum.Decomposition 𝓐]
    [SetLike.GradedMonoid 𝓐] (hneg : ∀ j < 0, 𝓐 j = ⊥) : A →+* A where
  toFun := component 𝓐 0
  map_zero' := map_zero _
  map_one' := DirectSum.decompose_of_mem_same 𝓐 SetLike.GradedOne.one_mem
  map_add' := map_add _
  map_mul' := by
    intro a b
    refine DirectSum.Decomposition.inductionOn 𝓐 ?_ ?_ ?_ a
    · simp
    · intro i a
      refine DirectSum.Decomposition.inductionOn 𝓐 ?_ ?_ ?_ b
      · simp
      · intro j b
        by_cases hi : i < 0
        · have ha : (a : A) = 0 := by simpa [hneg i hi] using a.property
          simp [ha]
        by_cases hj : j < 0
        · have hb : (b : A) = 0 := by simpa [hneg j hj] using b.property
          simp [hb]
        by_cases hij : i+j=0
        · have hi0 : i=0 := by omega
          have hj0 : j=0 := by omega
          have hab := SetLike.GradedMul.mul_mem a.property b.property
          change component 𝓐 0 ((a:A)*(b:A)) = component 𝓐 0 (a:A) * component 𝓐 0 (b:A)
          rw [show component 𝓐 0 ((a:A)*(b:A)) = (a:A)*(b:A) from
            DirectSum.decompose_of_mem_same 𝓐 (hij ▸ hab),
            show component 𝓐 0 (a:A) = a from
              DirectSum.decompose_of_mem_same 𝓐 (hi0 ▸ a.property),
            show component 𝓐 0 (b:A) = b from
              DirectSum.decompose_of_mem_same 𝓐 (hj0 ▸ b.property)]
        · change component 𝓐 0 ((a:A)*(b:A)) = component 𝓐 0 (a:A) * component 𝓐 0 (b:A)
          rw [show component 𝓐 0 ((a:A)*(b:A))=0 from
            DirectSum.decompose_of_mem_ne 𝓐
              (SetLike.GradedMul.mul_mem a.property b.property) hij]
          by_cases hi0 : i=0
          · have hj0 : j≠0 := by omega
            rw [show component 𝓐 0 (b:A)=0 from
              DirectSum.decompose_of_mem_ne 𝓐 b.property hj0,mul_zero]
          · rw [show component 𝓐 0 (a:A)=0 from
              DirectSum.decompose_of_mem_ne 𝓐 a.property hi0,zero_mul]
      · intro b c hb hc
        simp only [mul_add,map_add,hb,hc]
    · intro a c ha hc
      simp only [add_mul,map_add,ha,hc]

/-- The positive ideal is exactly the augmentation kernel. -/
theorem positiveIdeal_eq_augmentation_ker
    (𝓐 : ℤ → Submodule k A) [DirectSum.Decomposition 𝓐]
    [SetLike.GradedMonoid 𝓐] (hneg : ∀ j < 0, 𝓐 j = ⊥) :
    positiveIdeal 𝓐 = RingHom.ker (nonnegativeAugmentation 𝓐 hneg) := by
  classical
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro a ⟨i,hi,ha⟩
    exact DirectSum.decompose_of_mem_ne 𝓐 ha (by omega)
  · intro a ha
    rw [← DirectSum.sum_support_decompose 𝓐 a]
    apply Ideal.sum_mem
    intro j hj
    by_cases hjpos : 0 < j
    · exact Ideal.subset_span ⟨j,hjpos,(DirectSum.decompose 𝓐 a j).property⟩
    have hz : (DirectSum.decompose 𝓐 a j : A)=0 := by
      by_cases hjzero : j=0
      · subst j; exact ha
      · have hjneg : j<0 := by omega
        simpa [hneg j hjneg] using (DirectSum.decompose 𝓐 a j).property
    rw [hz]
    exact Ideal.zero_mem _


/-- The actual polynomial grading, with each variable in degree one, on
integer degrees as used for shifted stalks. -/
abbrev polynomialGrading (k : Type*) [Field k] (σ : Type*) :=
  MvPolynomial.weightedHomogeneousSubmodule k (fun _ : σ => (1 : ℤ))

noncomputable instance polynomialGrading_decomposition (k : Type*) [Field k] (σ : Type*) :
    DirectSum.Decomposition (polynomialGrading k σ) :=
  MvPolynomial.weightedDecomposition k (fun _ : σ => (1 : ℤ))

instance polynomialGrading_monoid (k : Type*) [Field k] (σ : Type*) :
    SetLike.GradedMonoid (polynomialGrading k σ) :=
  MvPolynomial.WeightedHomogeneousSubmodule.gradedMonoid

theorem polynomialGrading_negative (k : Type*) [Field k] (σ : Type*)
    (j : ℤ) (hj : j < 0) : polynomialGrading k σ j = ⊥ := by
  classical
  apply eq_bot_iff.mpr
  intro p hp
  change p=0
  apply MvPolynomial.ext
  intro d
  by_contra hd
  have heq := hp (show p.coeff d≠0 by simpa using hd)
  have hn : 0 ≤ Finsupp.weight (fun _ : σ => (1 : ℤ)) d := by
    simp only [Finsupp.weight_apply,Finsupp.sum]
    exact Finset.sum_nonneg fun i _ => nsmul_nonneg (by norm_num) _
  omega

theorem polynomialGrading_zero (k : Type*) [Field k] (σ : Type*)
    (p : MvPolynomial σ k) (hp : p ∈ polynomialGrading k σ 0) :
    ∃ c : k, algebraMap k (MvPolynomial σ k) c=p := by
  classical
  refine ⟨p.coeff 0,?_⟩
  apply MvPolynomial.ext
  intro d
  by_cases hd : d=0
  · subst d; simp
  · have hc : p.coeff d=0 := by
      by_contra hc
      have heq := hp hc
      obtain ⟨i,hi⟩ := Finsupp.ne_iff.mp hd
      have hb := Finsupp.le_weight_of_ne_zero (M := ℤ)
        (w := fun _ : σ => (1 : ℤ)) (fun _ => by norm_num)
        (show d i≠0 by simpa using hi)
      omega
    simp [MvPolynomial.coeff_C,Ne.symm hd,hc]


end KLInvariance.Graded


end

section

namespace KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {M : Type um} [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]

theorem exists_homogeneous_minimal_generators
    [Module.Finite A M]
    (𝓐 : ℤ → Submodule k A) (𝓜 : ℤ → Submodule k M)
    [DirectSum.Decomposition 𝓐] [DirectSum.Decomposition 𝓜]
    [SetLike.GradedSMul 𝓐 𝓜]
    (d₀ : ℤ) (hbound : ∀ j < d₀, 𝓜 j = ⊥)
    (hscalar : ∀ a : A, ∃ c : k, a-algebraMap k A c ∈ positiveIdeal 𝓐) :
    ∃ (ι : Type um), Finite ι ∧ ∃ (v : ι → M) (d : ι → ℤ),
      (∀ i, v i ∈ 𝓜 (d i)) ∧ Submodule.span A (Set.range v) = ⊤ ∧
      LinearIndependent k (fun i => (positiveIdeal 𝓐 • (⊤ : Submodule A M)).mkQ (v i)) := by
  classical
  obtain ⟨t,ht,hth⟩ := exists_finite_homogeneous_generators (A := A) 𝓜
  let v : t → M := Subtype.val
  have hv : Submodule.span A (Set.range v) = ⊤ := by
    simpa [v] using ht
  let I := positiveIdeal 𝓐
  let J := I • (⊤ : Submodule A M)
  have hq := quotient_span_of_scalar_mod I hscalar v hv
  obtain ⟨ι,a,ha,hsp,hli⟩ := exists_linearIndependent' k (fun i => J.mkQ (v i))
  let : Finite ι := Finite.of_injective a ha
  let : Fintype ι := Fintype.ofFinite ι
  let w : ι → M := v ∘ a
  have hw : ∀ i, ∃ d : ℤ, w i ∈ 𝓜 d := fun i => hth _ (a i).property
  choose d hd using hw
  have hqw : Submodule.span k (Set.range (fun i => J.mkQ (w i))) = ⊤ := hsp.trans hq
  let N := Submodule.span A (Set.range w)
  have hN : ∀ n m, m ∈ N → (DirectSum.decompose 𝓜 m n : M) ∈ N :=
    homogeneous_span_components 𝓐 𝓜 w d hd
  have hgen : N ⊔ I • (⊤ : Submodule A M) = ⊤ := by
    apply top_unique
    intro m _
    obtain ⟨c,hc⟩ := (Submodule.mem_span_range_iff_exists_fun k).mp
      (hqw ▸ Submodule.mem_top : J.mkQ m ∈
        Submodule.span k (Set.range (fun i => J.mkQ (w i))))
    let z : M := ∑ i, algebraMap k A (c i) • w i
    have hz : z ∈ N := by
      apply Submodule.sum_mem
      intro i _
      exact N.smul_mem _ (Submodule.subset_span (Set.mem_range_self i))
    have hqz : J.mkQ z = J.mkQ m := by
      change J.mkQ (∑ i, algebraMap k A (c i) • w i) = J.mkQ m
      rw [map_sum]
      convert hc using 1
      all_goals try with_reducible_and_instances rfl
      apply Finset.sum_congr rfl
      intro i _
      exact (map_smul J.mkQ _ _).trans (IsScalarTower.algebraMap_smul A (c i) _)
    have hdiff : m-z ∈ J := by
      apply (Submodule.Quotient.mk_eq_zero J).mp
      change J.mkQ (m-z)=0
      rw [map_sub,hqz,sub_self]
    exact Submodule.mem_sup.mpr ⟨z,hz,m-z,hdiff,by abel⟩
  have hspan : N=⊤ := eq_top_of_positive_smul_sup 𝓐 𝓜 d₀ hbound N hN hgen
  exact ⟨ι,inferInstance,w,d,hd,hspan,hli⟩

 theorem kernel_minimal_cover (I : Ideal A)
    (hscalar : ∀ a : A, ∃ c : k, a-algebraMap k A c ∈ I)
    {ι : Type*} [Fintype ι] (v : ι → M)
    (hind : LinearIndependent k (fun i => (I • (⊤ : Submodule A M)).mkQ (v i))) :
    LinearMap.ker (Fintype.linearCombination A v) ≤ I • (⊤ : Submodule A (ι → A)) := by
  classical
  intro f hf
  let J := I • (⊤ : Submodule A M)
  choose c hc using fun i => hscalar (f i)
  have hz : ∑ i, c i • J.mkQ (v i) = 0 := by
    have hm : ∑ i, f i • v i = 0 := LinearMap.mem_ker.mp hf
    have hq := congrArg J.mkQ hm
    rw [map_sum,map_zero] at hq
    convert hq using 1
    all_goals try with_reducible_and_instances rfl
    apply Finset.sum_congr rfl
    intro i _
    exact (quotient_smul_of_scalar_mod I (f i) (c i) (hc i) (v i)).symm
  have hc0 : ∀ i, c i = 0 := (Fintype.linearIndependent_iff.mp hind) c hz
  have hfi (i : ι) : f i ∈ I := by simpa [hc0 i] using hc i
  have he : f = ∑ i, f i • Pi.single i (1 : A) := by
    ext i
    simp [Pi.single_apply]
  rw [he]
  apply Submodule.sum_mem
  intro i _
  exact Submodule.smul_mem_smul (hfi i) Submodule.mem_top

end KLInvariance.Graded

end


section

namespace KLInvariance.Graded
universe uk ua um un
variable {k : Type uk} [Field k]
  {M : Type um} [AddCommGroup M] [Module k M]
  {N : Type un} [AddCommGroup N] [Module k N]

 theorem internal_of_components
    (𝓜 : ℤ → Submodule k M) (p : ℤ → M →ₗ[k] M)
    (hmem : ∀ i m, p i m ∈ 𝓜 i)
    (hsame : ∀ i m, m ∈ 𝓜 i → p i m = m)
    (hne : ∀ i j m, i ≠ j → m ∈ 𝓜 j → p i m = 0)
    (hsum : ∀ m, ∃ s : Finset ℤ, ∑ i ∈ s, p i m = m) :
    DirectSum.IsInternal 𝓜 := by
  classical
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
  · apply (iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero _).mpr
    intro s v hv hz i hi
    have hp := congrArg (p i) hz
    rw [map_sum, map_zero, Finset.sum_eq_single_of_mem i hi] at hp
    · simpa only [hsame i _ (hv i hi)] using hp
    · intro j hj hji
      exact hne i j _ (Ne.symm hji) (hv j hj)
  · apply top_unique
    intro m _
    obtain ⟨s,hs⟩ := hsum m
    rw [← hs]
    apply Submodule.sum_mem
    intro i _
    exact (le_iSup 𝓜 i) (hmem i m)

 theorem image_isInternal
    (𝓜 : ℤ → Submodule k M) [DirectSum.Decomposition 𝓜]
    (f : M →ₗ[k] N) (hf : Function.Surjective f)
    (hker : ∀ i m, f m = 0 → f (component 𝓜 i m) = 0) :
    DirectSum.IsInternal (fun i => (𝓜 i).map f) := by
  classical
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
  · apply (iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero _).mpr
    intro s v hv hz i hi
    choose w hw hfw using fun j : s => (Submodule.mem_map.mp (hv j.val j.property))
    let w' : ℤ → M := fun j => if hj : j ∈ s then w ⟨j,hj⟩ else 0
    have hw' (j) : w' j ∈ 𝓜 j := by
      dsimp [w']; split_ifs with hj
      · exact hw ⟨j,hj⟩
      · exact Submodule.zero_mem _
    have hfw' (j) (hj : j ∈ s) : f (w' j) = v j := by simpa [w',hj] using hfw ⟨j,hj⟩
    have hsum : f (∑ j ∈ s, w' j) = 0 := by
      rw [map_sum]
      exact (Finset.sum_congr rfl hfw').trans hz
    have hc := hker i _ hsum
    rw [map_sum, Finset.sum_eq_single_of_mem i hi] at hc
    · change f (DirectSum.decompose 𝓜 (w' i) i : M) = 0 at hc
      rw [DirectSum.decompose_of_mem_same 𝓜 (hw' i), hfw' i hi] at hc
      exact hc
    · intro j _ hji
      exact DirectSum.decompose_of_mem_ne 𝓜 (hw' j) hji
  · apply top_unique
    intro n _
    obtain ⟨m,rfl⟩ := hf n
    rw [← DirectSum.sum_support_decompose 𝓜 m, map_sum]
    apply Submodule.sum_mem
    intro i _
    exact (le_iSup (fun i => (𝓜 i).map f) i)
      (Submodule.mem_map.mpr ⟨_,(DirectSum.decompose 𝓜 m i).property,rfl⟩)

variable {A : Type ua} [CommRing A] [Algebra k A]
  [Module A M] [IsScalarTower k A M]

 def subPiece (𝓜 : ℤ → Submodule k M) (S : Submodule A M) : ℤ → Submodule k S :=
  fun i => (𝓜 i).comap (S.subtype.restrictScalars k)

 theorem sub_isInternal
    (𝓜 : ℤ → Submodule k M) [DirectSum.Decomposition 𝓜]
    (S : Submodule A M)
    (hS : ∀ i m, m ∈ S → component 𝓜 i m ∈ S) :
    DirectSum.IsInternal (subPiece 𝓜 S) := by
  classical
  let p : ℤ → S →ₗ[k] S := fun i =>
    LinearMap.codRestrict (S.restrictScalars k)
      ((component 𝓜 i).comp (S.subtype.restrictScalars k)) (fun m => hS i m m.property)
  apply internal_of_components (subPiece 𝓜 S) p
  · intro i m
    exact (DirectSum.decompose 𝓜 (m : M) i).property
  · intro i m hm
    apply Subtype.ext
    exact DirectSum.decompose_of_mem_same 𝓜 hm
  · intro i j m hij hm
    apply Subtype.ext
    exact DirectSum.decompose_of_mem_ne 𝓜 hm hij.symm
  · intro m
    refine ⟨(DirectSum.decompose 𝓜 (m : M)).support, ?_⟩
    apply Subtype.ext
    change (∑ i ∈ (DirectSum.decompose 𝓜 (m : M)).support, p i m : S).val = (m : M)
    rw [Submodule.coe_sum]
    exact DirectSum.sum_support_decompose 𝓜 (m : M)

 def quotientPiece (𝓜 : ℤ → Submodule k M) (S : Submodule A M) :
    ℤ → Submodule k (M ⧸ S) := fun i => (𝓜 i).map (S.mkQ.restrictScalars k)

 theorem quotient_isInternal
    (𝓜 : ℤ → Submodule k M) [DirectSum.Decomposition 𝓜]
    (S : Submodule A M)
    (hS : ∀ i m, m ∈ S → component 𝓜 i m ∈ S) :
    DirectSum.IsInternal (quotientPiece 𝓜 S) := by
  apply image_isInternal 𝓜 (S.mkQ.restrictScalars k) S.mkQ_surjective
  intro i m hm
  apply (Submodule.Quotient.mk_eq_zero S).mpr
  exact hS i m ((Submodule.Quotient.mk_eq_zero S).mp hm)

 instance sub_gradedSMul
    (𝓐 : ℤ → Submodule k A) (𝓜 : ℤ → Submodule k M)
    [SetLike.GradedSMul 𝓐 𝓜] (S : Submodule A M) :
    SetLike.GradedSMul 𝓐 (subPiece 𝓜 S) where
  smul_mem := by
    intro i j a m ha hm
    change a • (m : M) ∈ 𝓜 (i+j)
    exact SetLike.GradedSMul.smul_mem ha (show (m : M) ∈ 𝓜 j from hm)

 instance quotient_gradedSMul
    (𝓐 : ℤ → Submodule k A) (𝓜 : ℤ → Submodule k M)
    [SetLike.GradedSMul 𝓐 𝓜] (S : Submodule A M) :
    SetLike.GradedSMul 𝓐 (quotientPiece 𝓜 S) where
  smul_mem := by
    intro i j a m ha hm
    obtain ⟨v,hv,rfl⟩ := Submodule.mem_map.mp hm
    exact Submodule.mem_map.mpr ⟨a • v,SetLike.GradedSMul.smul_mem ha hv,map_smul S.mkQ a v⟩

 theorem subPiece_eq_bot (𝓜 : ℤ → Submodule k M) (S : Submodule A M)
    (i : ℤ) (h : 𝓜 i = ⊥) : subPiece 𝓜 S i = ⊥ := by
  apply le_antisymm _ bot_le
  intro m hm
  apply Subtype.ext
  exact (Submodule.mem_bot k).mp (h ▸ hm)

 theorem quotientPiece_eq_bot (𝓜 : ℤ → Submodule k M) (S : Submodule A M)
    (i : ℤ) (h : 𝓜 i = ⊥) : quotientPiece 𝓜 S i = ⊥ := by
  simp [quotientPiece,h]

 def shiftedPiece {ι : Type*} (𝓐 : ℤ → Submodule k A) (d : ι → ℤ) :
    ℤ → Submodule k (ι → A) := fun n =>
  { carrier := {v | ∀ i, v i ∈ 𝓐 (n-d i)}
    zero_mem' := fun _ => Submodule.zero_mem _
    add_mem' := fun hx hy i => Submodule.add_mem _ (hx i) (hy i)
    smul_mem' := fun c _ hx i => Submodule.smul_mem _ c (hx i) }

 theorem shifted_isInternal {ι : Type*} [Fintype ι]
    (𝓐 : ℤ → Submodule k A) [DirectSum.Decomposition 𝓐] (d : ι → ℤ) :
    DirectSum.IsInternal (shiftedPiece 𝓐 d) := by
  classical
  let p : ℤ → (ι → A) →ₗ[k] (ι → A) := fun n =>
    LinearMap.pi fun i => (component 𝓐 (n-d i)).comp (LinearMap.proj i)
  apply internal_of_components (shiftedPiece 𝓐 d) p
  · intro n v i
    exact (DirectSum.decompose 𝓐 (v i) (n-d i)).property
  · intro n v hv
    funext i
    exact DirectSum.decompose_of_mem_same 𝓐 (hv i)
  · intro n j v hnj hv
    funext i
    apply DirectSum.decompose_of_mem_ne 𝓐 (hv i)
    omega
  · intro v
    let s : ι → Finset ℤ := fun i =>
      (DirectSum.decompose 𝓐 (v i)).support.image (fun n => n+d i)
    refine ⟨Finset.univ.biUnion s, ?_⟩
    funext i
    change (∑ n ∈ Finset.univ.biUnion s, p n v) i = v i
    rw [Finset.sum_apply]
    have hsub : s i ⊆ Finset.univ.biUnion s :=
      Finset.subset_biUnion_of_mem s (Finset.mem_univ i)
    have hout (n : ℤ) (_ : n ∈ Finset.univ.biUnion s) (hn : n ∉ s i) :
        p n v i = 0 := by
      have hni : n-d i ∉ (DirectSum.decompose 𝓐 (v i)).support := by
        intro hni
        exact hn (Finset.mem_image.mpr ⟨n-d i,hni,by omega⟩)
      have hz := DFinsupp.notMem_support_iff.mp hni
      exact congrArg Subtype.val hz
    rw [← Finset.sum_subset hsub hout]
    change ∑ n ∈ (DirectSum.decompose 𝓐 (v i)).support.image (fun n => n+d i),
      component 𝓐 (n-d i) (v i) = v i
    rw [Finset.sum_image (fun a _ b _ h => by omega)]
    simp only [add_sub_cancel_right]
    exact DirectSum.sum_support_decompose 𝓐 (v i)

 instance shifted_gradedSMul {ι : Type*}
    (𝓐 : ℤ → Submodule k A) [SetLike.GradedMonoid 𝓐] (d : ι → ℤ) :
    SetLike.GradedSMul 𝓐 (shiftedPiece 𝓐 d) where
  smul_mem := by
    intro i j a m ha hm t
    have h := SetLike.GradedMul.mul_mem ha (hm t)
    simpa [sub_eq_add_neg,add_assoc] using h

 theorem shiftedPiece_eq_bot {ι : Type*}
    (𝓐 : ℤ → Submodule k A) (hneg : ∀ i < 0, 𝓐 i = ⊥) (d : ι → ℤ)
    (n : ℤ) (h : ∀ i, n < d i) : shiftedPiece 𝓐 d n = ⊥ := by
  apply le_antisymm _ bot_le
  intro m hm
  funext i
  have hi := hm i
  rw [hneg _ (by have := h i; omega)] at hi
  exact hi

end KLInvariance.Graded

end


section

namespace KLInvariance.Graded
universe uk ua um un ui
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {M : Type um} [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]
  {N : Type un} [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N]

omit [Algebra k A] [IsScalarTower k A M] [IsScalarTower k A N] in
 theorem map_component
    (𝓜 : ℤ → Submodule k M) (𝓝 : ℤ → Submodule k N)
    [DirectSum.Decomposition 𝓜] [DirectSum.Decomposition 𝓝]
    (f : M →ₗ[A] N) (d : ℤ)
    (hf : ∀ i m, m ∈ 𝓜 i → f m ∈ 𝓝 (i+d)) (n : ℤ) (m : M) :
    component 𝓝 n (f m) = f (component 𝓜 (n-d) m) := by
  classical
  refine DirectSum.Decomposition.inductionOn 𝓜 ?_ ?_ ?_ m
  · simp
  · intro j v
    by_cases h : j+d=n
    · have h' : n-d=j := by omega
      change (DirectSum.decompose 𝓝 (f (v : M)) n : N) =
        f (DirectSum.decompose 𝓜 (v : M) (n-d) : M)
      rw [← h, DirectSum.decompose_of_mem_same 𝓝 (hf j v v.property),
        show j+d-d=j by omega, DirectSum.decompose_of_mem_same 𝓜 v.property]
    · have h' : j ≠ n-d := by omega
      change (DirectSum.decompose 𝓝 (f (v : M)) n : N) =
        f (DirectSum.decompose 𝓜 (v : M) (n-d) : M)
      rw [DirectSum.decompose_of_mem_ne 𝓝 (hf j v v.property) h,
        DirectSum.decompose_of_mem_ne 𝓜 v.property h', map_zero]
  · intro x y hx hy
    simp only [map_add,hx,hy]

omit [Algebra k A] [IsScalarTower k A M] [IsScalarTower k A N] in
 theorem range_homogeneous
    (𝓜 : ℤ → Submodule k M) (𝓝 : ℤ → Submodule k N)
    [DirectSum.Decomposition 𝓜] [DirectSum.Decomposition 𝓝]
    (f : M →ₗ[A] N) (d : ℤ)
    (hf : ∀ i m, m ∈ 𝓜 i → f m ∈ 𝓝 (i+d)) :
    ∀ n m, m ∈ LinearMap.range f → component 𝓝 n m ∈ LinearMap.range f := by
  rintro n _ ⟨m,rfl⟩
  exact ⟨component 𝓜 (n-d) m,(map_component 𝓜 𝓝 f d hf n m).symm⟩

omit [IsScalarTower k A M] in
 theorem scalar_range_homogeneous
    (𝓐 : ℤ → Submodule k A) (𝓜 : ℤ → Submodule k M)
    [DirectSum.Decomposition 𝓜] [SetLike.GradedSMul 𝓐 𝓜]
    (d : ℤ) (a : A) (ha : a ∈ 𝓐 d) :
    ∀ n m, m ∈ LinearMap.range (LinearMap.lsmul A M a) →
      component 𝓜 n m ∈ LinearMap.range (LinearMap.lsmul A M a) := by
  apply range_homogeneous 𝓜 𝓜 (LinearMap.lsmul A M a) d
  intro i v hv
  simpa [add_comm] using SetLike.GradedSMul.smul_mem ha hv

section Pi
variable {ι : Type ui} {P : ι → Type um}
  [∀ i, AddCommGroup (P i)] [∀ i, Module k (P i)]

 def piPiece (𝓟 : ∀ i, ℤ → Submodule k (P i)) : ℤ → Submodule k (∀ i, P i) :=
  fun n => Submodule.pi Set.univ (fun i => 𝓟 i n)

 theorem pi_isInternal [Fintype ι]
    (𝓟 : ∀ i, ℤ → Submodule k (P i)) [∀ i, DirectSum.Decomposition (𝓟 i)] :
    DirectSum.IsInternal (piPiece 𝓟) := by
  classical
  let p : ℤ → (∀ i, P i) →ₗ[k] (∀ i, P i) := fun n =>
    LinearMap.pi fun i => (component (𝓟 i) n).comp (LinearMap.proj i)
  apply internal_of_components (piPiece 𝓟) p
  · intro n v i _
    exact (DirectSum.decompose (𝓟 i) (v i) n).property
  · intro n v hv
    funext i
    exact DirectSum.decompose_of_mem_same (𝓟 i) (hv i (Set.mem_univ i))
  · intro n j v hnj hv
    funext i
    exact DirectSum.decompose_of_mem_ne (𝓟 i) (hv i (Set.mem_univ i)) hnj.symm
  · intro v
    let s : ι → Finset ℤ := fun i => (DirectSum.decompose (𝓟 i) (v i)).support
    refine ⟨Finset.univ.biUnion s, ?_⟩
    funext i
    rw [Finset.sum_apply]
    have hsub : s i ⊆ Finset.univ.biUnion s :=
      Finset.subset_biUnion_of_mem s (Finset.mem_univ i)
    have hout (n : ℤ) (_ : n ∈ Finset.univ.biUnion s) (hn : n ∉ s i) :
        p n v i = 0 := by
      change n ∉ (DirectSum.decompose (𝓟 i) (v i)).support at hn
      have hz := DFinsupp.notMem_support_iff.mp hn
      exact congrArg Subtype.val hz
    rw [← Finset.sum_subset hsub hout]
    exact DirectSum.sum_support_decompose (𝓟 i) (v i)

 instance pi_gradedSMul [∀ i, Module A (P i)] [∀ i, IsScalarTower k A (P i)]
    (𝓐 : ℤ → Submodule k A) (𝓟 : ∀ i, ℤ → Submodule k (P i))
    [∀ i, SetLike.GradedSMul 𝓐 (𝓟 i)] : SetLike.GradedSMul 𝓐 (piPiece 𝓟) where
  smul_mem := by
    intro n j a v ha hv i hi
    exact SetLike.GradedSMul.smul_mem ha (hv i hi)

 theorem piPiece_eq_bot
    (𝓟 : ∀ i, ℤ → Submodule k (P i)) (n : ℤ) (h : ∀ i, 𝓟 i n = ⊥) :
    piPiece 𝓟 n = ⊥ := by
  apply le_antisymm _ bot_le
  intro v hv
  funext i
  have hi : v i ∈ 𝓟 i n := hv i (Set.mem_univ i)
  rw [h i] at hi
  exact hi

end Pi
end KLInvariance.Graded

end


section

namespace KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]

/-- Actual finite nonnegatively graded modules; no character or duality property
is folded into this data. -/
structure ModuleData (𝓐 : ℤ → Submodule k A) where
  obj : ModuleCat.{max ua um} A
  kModule : Module k obj
  tower : IsScalarTower k A obj
  piece : ℤ → Submodule k obj
  decomposition : DirectSum.Decomposition piece
  graded : SetLike.GradedSMul 𝓐 piece
  nonneg : ∀ n < 0, piece n = ⊥
  finite : Module.Finite A obj

attribute [instance] ModuleData.kModule ModuleData.tower ModuleData.decomposition
  ModuleData.graded ModuleData.finite

instance instCoeSortModuleDataType {𝓐 : ℤ → Submodule k A} : CoeSort (ModuleData.{uk,ua,um} 𝓐) (Type (max ua um)) :=
  ⟨fun M => M.obj⟩

namespace ModuleData
variable {𝓐 : ℤ → Submodule k A}

instance instAddCommGroupCarrierObj (M : ModuleData.{uk,ua,um} 𝓐) : AddCommGroup M := inferInstanceAs (AddCommGroup M.obj)

structure Hom (M N : ModuleData.{uk,ua,um} 𝓐) where
  map : M →ₗ[A] N
  graded : ∀ n m, m ∈ M.piece n → map m ∈ N.piece n

noncomputable def sub [IsNoetherianRing A] (M : ModuleData.{uk,ua,um} 𝓐)
    (S : Submodule A M) (hS : ∀ n m, m ∈ S → component M.piece n m ∈ S) :
    ModuleData.{uk,ua,um} 𝓐 where
  obj := ModuleCat.of A S
  kModule := inferInstance
  tower := inferInstance
  piece := subPiece M.piece S
  decomposition := (sub_isInternal M.piece S hS).chooseDecomposition
  graded := inferInstance
  nonneg := fun n hn => subPiece_eq_bot M.piece S n (M.nonneg n hn)
  finite := inferInstance

noncomputable def quotient (M : ModuleData.{uk,ua,um} 𝓐)
    (S : Submodule A M) (hS : ∀ n m, m ∈ S → component M.piece n m ∈ S) :
    ModuleData.{uk,ua,um} 𝓐 where
  obj := ModuleCat.of A (M ⧸ S)
  kModule := inferInstance
  tower := inferInstance
  piece := quotientPiece M.piece S
  decomposition := (quotient_isInternal M.piece S hS).chooseDecomposition
  graded := inferInstance
  nonneg := fun n hn => quotientPiece_eq_bot M.piece S n (M.nonneg n hn)
  finite := inferInstance

noncomputable def pi {ι : Type um} [Fintype ι] (M : ι → ModuleData.{uk,ua,um} 𝓐) :
    ModuleData.{uk,ua,um} 𝓐 where
  obj := ModuleCat.of A (∀ i, M i)
  kModule := inferInstance
  tower := inferInstance
  piece := piPiece fun i => (M i).piece
  decomposition := (pi_isInternal (fun i => (M i).piece)).chooseDecomposition
  graded := inferInstance
  nonneg := fun n hn => piPiece_eq_bot (fun i => (M i).piece) n (fun i => (M i).nonneg n hn)
  finite := inferInstance

noncomputable def range [IsNoetherianRing A] {M N : ModuleData.{uk,ua,um} 𝓐}
    (f : Hom M N) : ModuleData.{uk,ua,um} 𝓐 :=
  sub N f.map.range (range_homogeneous M.piece N.piece f.map 0
    (by simpa using f.graded))

noncomputable def scalarQuotient (M : ModuleData.{uk,ua,um} 𝓐)
    (a : A) (d : ℤ) (ha : a ∈ 𝓐 d) : ModuleData.{uk,ua,um} 𝓐 :=
  quotient M (LinearMap.range (LinearMap.lsmul A M a))
    (scalar_range_homogeneous 𝓐 M.piece d a ha)

 def projection {ι : Type um} [Fintype ι] (M : ι → ModuleData.{uk,ua,um} 𝓐) (i : ι) :
    Hom (pi M) (M i) where
  map := LinearMap.proj i
  graded := fun _ _ hm => hm i (Set.mem_univ i)

 def quotientMap (M : ModuleData.{uk,ua,um} 𝓐)
    (S : Submodule A M) (hS : ∀ n m, m ∈ S → component M.piece n m ∈ S) :
    Hom M (quotient M S hS) where
  map := S.mkQ
  graded := by
    intro n m hm
    change S.mkQ m ∈ quotientPiece M.piece S n
    exact Submodule.mem_map.mpr ⟨m,hm,rfl⟩

 def subtype [IsNoetherianRing A] (M : ModuleData.{uk,ua,um} 𝓐)
    (S : Submodule A M) (hS : ∀ n m, m ∈ S → component M.piece n m ∈ S) :
    Hom (sub M S hS) M where
  map := S.subtype
  graded := fun _ _ hm => hm


 def Hom.comp {M N P : ModuleData.{uk,ua,um} 𝓐} (g : Hom N P) (f : Hom M N) :
    Hom M P where
  map := g.map.comp f.map
  graded := fun n m hm => g.graded n _ (f.graded n m hm)

 def Hom.id (M : ModuleData.{uk,ua,um} 𝓐) : Hom M M where
  map := LinearMap.id
  graded := fun _ _ h => h

 theorem Hom.component {M N : ModuleData.{uk,ua,um} 𝓐} (f : Hom M N) (n : ℤ) (m : M) :
    component N.piece n (f.map m) = f.map (component M.piece n m) := by
  simpa using map_component M.piece N.piece f.map 0 (by simpa using f.graded) n m

variable [DirectSum.Decomposition 𝓐] [SetLike.GradedMonoid 𝓐]

noncomputable def free {ι : Type (max ua um)} [Fintype ι]
    (hneg : ∀ n < 0, 𝓐 n = ⊥) (d : ι → ℤ) (hd : ∀ i, 0 ≤ d i) :
    ModuleData.{uk,ua,um} 𝓐 where
  obj := ModuleCat.of A (ι → A)
  kModule := inferInstance
  tower := inferInstance
  piece := shiftedPiece 𝓐 d
  decomposition := (shifted_isInternal 𝓐 d).chooseDecomposition
  graded := inferInstance
  nonneg := fun n hn => shiftedPiece_eq_bot 𝓐 hneg d n (fun i => lt_of_lt_of_le hn (hd i))
  finite := inferInstance

 structure MinimalCover (M : ModuleData.{uk,ua,um} 𝓐) where
  source : ModuleData.{uk,ua,um} 𝓐
  free : Module.Free A source
  hom : Hom source M
  surjective : Function.Surjective hom.map
  minimal : LinearMap.ker hom.map ≤ positiveIdeal 𝓐 • (⊤ : Submodule A source)

 theorem exists_minimalCover
    (hneg : ∀ n < 0, 𝓐 n = ⊥)
    (hscalar : ∀ a : A, ∃ c : k, a-algebraMap k A c ∈ positiveIdeal 𝓐)
    (M : ModuleData.{uk,ua,um} 𝓐) : Nonempty (MinimalCover M) := by
  classical
  obtain ⟨ι,hι,v,d,hd,hspan,hind⟩ :=
    exists_homogeneous_minimal_generators 𝓐 M.piece 0 M.nonneg hscalar
  let : Finite ι := hι
  let : Fintype ι := Fintype.ofFinite ι
  have hd0 (i : ι) : 0 ≤ d i := by
    by_contra h
    have hbot := M.nonneg (d i) (lt_of_not_ge h)
    have hv0 : v i = 0 := by simpa only [hbot, Submodule.mem_bot] using hd i
    have hz := hind.ne_zero i
    exact hz (by rw [hv0,map_zero])
  let F := free hneg d hd0
  let f : Hom F M :=
    { map := Fintype.linearCombination A v
      graded := by
        intro n c hc
        apply Submodule.sum_mem
        intro i _
        simpa using SetLike.GradedSMul.smul_mem (hc i) (hd i) }
  have hfree : Module.Free A F := inferInstanceAs (Module.Free A (ι → A))
  refine ⟨⟨F,hfree,f,?_,?_⟩⟩
  · intro m
    exact (Submodule.mem_span_range_iff_exists_fun A).mp (hspan ▸ Submodule.mem_top)
  · exact kernel_minimal_cover _ hscalar v hind

end ModuleData
end KLInvariance.Graded

end


end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_Coxeter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Signed reflection permutations and strong exchange for arbitrary Coxeter systems.
-/

section


namespace KLInvariance.CoxeterSupport

open CoxeterSystem

universe u v
variable {B : Type u} {W : Type v} [Group W] {M : CoxeterMatrix B}
variable (cs : CoxeterSystem M W)

noncomputable local instance instDecidableEq_solutions : DecidableEq W := Classical.decEq W

noncomputable def simpleAction (i : B) : Equiv.Perm (W × ZMod 2) := by
  classical
  let f : W × ZMod 2 → W × ZMod 2 := fun p =>
    (cs.simple i * p.1 * cs.simple i, p.2 + if p.1 = cs.simple i then 1 else 0)
  have hf : Function.Involutive f := by
    rintro ⟨t, a⟩
    dsimp [f]
    have heq : cs.simple i * t * cs.simple i = cs.simple i ↔ t = cs.simple i := by
      constructor
      · intro h
        have := congrArg (fun z => cs.simple i * z * cs.simple i) h
        simpa [mul_assoc] using this
      · rintro rfl
        simp
    simp only [heq]
    ext
    · simp [mul_assoc]
    · split_ifs
      · simp only [add_assoc, ZModModule.add_self, add_zero]
      · simp
  exact ⟨f, f, hf, hf⟩

@[simp] theorem simpleAction_apply (i : B) (t : W) (a : ZMod 2) :
    simpleAction cs i (t, a) =
      (cs.simple i * t * cs.simple i, a + if t = cs.simple i then 1 else 0) := by
  classical
  rfl

noncomputable def wordAction (ω : List B) : Equiv.Perm (W × ZMod 2) :=
  (ω.map (simpleAction cs)).prod

@[simp] theorem wordAction_nil : wordAction cs [] = 1 := rfl

theorem wordAction_concat (ω : List B) (i : B) :
    wordAction cs (ω.concat i) = wordAction cs ω * simpleAction cs i := by
  simp [wordAction]

/-- Signed action records the parity of the genuine left inversion sequence. -/
theorem wordAction_record (ω : List B) (t : W) (a : ZMod 2) :
    wordAction cs ω ((cs.wordProd ω)⁻¹ * t * cs.wordProd ω, a) =
      (t, a + ((cs.leftInvSeq ω).count t : ZMod 2)) := by
  classical
  induction ω using List.reverseRecOn generalizing a with
  | nil => simp [wordAction]
  | append_singleton ω i ih =>
    rw [← List.concat_eq_append, wordAction_concat, Equiv.Perm.mul_apply,
      cs.wordProd_concat, mul_inv_rev, cs.inv_simple, simpleAction_apply]
    have hc : cs.simple i * ((cs.simple i * (cs.wordProd ω)⁻¹) * t *
          (cs.wordProd ω * cs.simple i)) * cs.simple i =
          (cs.wordProd ω)⁻¹ * t * cs.wordProd ω := by
      simp [mul_assoc]
    rw [hc, ih]
    rw [cs.leftInvSeq_concat]
    have heq : (cs.simple i * (cs.wordProd ω)⁻¹) * t *
          (cs.wordProd ω * cs.simple i) = cs.simple i ↔
          t = cs.wordProd ω * cs.simple i * (cs.wordProd ω)⁻¹ := by
      constructor
      · intro h
        have := congrArg (fun z => cs.wordProd ω * cs.simple i * z *
          cs.simple i * (cs.wordProd ω)⁻¹) h
        simpa [mul_assoc] using this
      · rintro rfl
        simp [mul_assoc]
    simp only [List.concat_eq_append, List.count_append, List.count_singleton,
      Nat.cast_add, heq]
    congr 1
    split_ifs <;> simp_all [add_comm, add_left_comm]

/-- The presentation relation has a doubled inversion sequence, so its
signed action is trivial, including for no-relation entries `M i j = 0`. -/
theorem leftInvSeq_alternating_formula (i j : B) (p : ℕ) :
    cs.leftInvSeq (alternatingWord i j (2 * p)) =
      (List.range (2 * p)).map (fun k => cs.simple i * (cs.simple j * cs.simple i) ^ k) := by
  apply List.ext_getElem (by simp)
  intro k hk hk'
  have hk0 : k < 2 * p := by simpa using hk
  rw [cs.getElem_leftInvSeq_alternatingWord i j p k hk0,
    List.getElem_map, List.getElem_range]
  rw [cs.prod_alternatingWord_eq_mul_pow]
  simp only [Nat.not_even_iff_odd.mpr (show Odd (2 * k + 1) from ⟨k, rfl⟩),
    ↓reduceIte]
  congr 2
  omega

theorem leftInvSeq_relation_doubled (i j : B) :
    ∃ l : List W, cs.leftInvSeq (alternatingWord i j (2 * M i j)) = l ++ l := by
  let f : ℕ → W := fun k => cs.simple i * (cs.simple j * cs.simple i) ^ k
  refine ⟨(List.range (M i j)).map f, ?_⟩
  rw [leftInvSeq_alternating_formula, two_mul, List.range_add, List.map_append, List.map_map]
  congr 1
  apply List.map_congr_left
  intro k _
  dsimp [f]
  rw [pow_add, cs.simple_mul_simple_pow']
  simp

theorem wordAction_alternating (i j : B) (p : ℕ) :
    wordAction cs (alternatingWord i j (2 * p)) =
      (simpleAction cs i * simpleAction cs j) ^ p := by
  induction p with
  | zero => simp [alternatingWord]
  | succ p ih =>
    rw [show 2 * (p + 1) = (2 * p + 1) + 1 by omega,
      alternatingWord_succ', alternatingWord_succ']
    simp only [Nat.not_even_iff_odd.mpr (show Odd (2 * p + 1) from ⟨p, rfl⟩),
      ↓reduceIte, even_two, Even.mul_right]
    change simpleAction cs i * (simpleAction cs j *
      wordAction cs (alternatingWord i j (2 * p))) = _
    rw [ih, ← mul_assoc, pow_succ']

theorem simpleAction_liftable : M.IsLiftable (simpleAction cs) := by
  intro i j
  rw [← wordAction_alternating]
  apply Equiv.ext
  rintro ⟨t, a⟩
  have h := wordAction_record cs (alternatingWord i j (2 * M i j)) t a
  have hw : cs.wordProd (alternatingWord i j (2 * M i j)) = 1 := by
    rw [cs.prod_alternatingWord_eq_mul_pow]
    simp
  obtain ⟨l, hl⟩ := leftInvSeq_relation_doubled cs i j
  simpa [hw, hl, List.count_append, Nat.cast_add, ZModModule.add_self] using h

noncomputable def reflectionAction : W →* Equiv.Perm (W × ZMod 2) :=
  cs.lift ⟨simpleAction cs, simpleAction_liftable cs⟩

@[simp] theorem reflectionAction_simple (i : B) :
    reflectionAction cs (cs.simple i) = simpleAction cs i :=
  cs.lift_apply_simple (simpleAction_liftable cs) i

theorem reflectionAction_wordProd (ω : List B) :
    reflectionAction cs (cs.wordProd ω) = wordAction cs ω := by
  induction ω with
  | nil => simp
  | cons i ω ih =>
    rw [cs.wordProd_cons, map_mul, reflectionAction_simple, ih]
    rfl

/-- The signed action is conjugation on labels and a translation on signs. -/
theorem reflectionAction_translation (w t : W) :
    ∃ δ : ZMod 2, ∀ a : ZMod 2,
      reflectionAction cs w (t, a) = (w * t * w⁻¹, a + δ) := by
  classical
  obtain ⟨ω, rfl⟩ := cs.wordProd_surjective w
  refine ⟨((cs.leftInvSeq ω).count (cs.wordProd ω * t * (cs.wordProd ω)⁻¹) : ZMod 2), ?_⟩
  intro a
  rw [reflectionAction_wordProd]
  have h := wordAction_record cs ω (cs.wordProd ω * t * (cs.wordProd ω)⁻¹) a
  simpa [mul_assoc] using h

/-- A reflection changes the sign of its own label. This is the critical
conjugation step making the representation yield *strong* exchange. -/
theorem reflectionAction_reflection {t : W} (ht : cs.IsReflection t) (a : ZMod 2) :
    reflectionAction cs t (t, a) = (t, a + 1) := by
  obtain ⟨w, i, rfl⟩ := ht
  obtain ⟨δ, hδ⟩ := reflectionAction_translation cs w⁻¹
    (w * cs.simple i * w⁻¹)
  obtain ⟨ε, hε⟩ := reflectionAction_translation cs w (cs.simple i)
  have hδ' (a : ZMod 2) : reflectionAction cs w⁻¹
      (w * cs.simple i * w⁻¹, a) = (cs.simple i, a + δ) := by
    simpa [mul_assoc] using hδ a
  have hz : δ + ε = 0 := by
    have h := congrArg (fun p : W × ZMod 2 => p.2)
      (Equiv.apply_symm_apply (reflectionAction cs w) (w * cs.simple i * w⁻¹, 0))
    change ((reflectionAction cs w) ((reflectionAction cs w)⁻¹
      (w * cs.simple i * w⁻¹, 0))).2 = 0 at h
    rw [← map_inv, hδ', hε] at h
    simpa using h
  rw [map_mul, map_mul, reflectionAction_simple, Equiv.Perm.mul_apply,
    Equiv.Perm.mul_apply, hδ', simpleAction_apply]
  simp only [cs.simple_mul_simple_self, one_mul, ↓reduceIte]
  rw [hε]
  congr 1
  calc
    (a + δ + 1) + ε = (a + 1) + (δ + ε) := by ring
    _ = a + 1 := by rw [hz, add_zero]


theorem mem_leftInvSeq_of_inversion {ω : List B} (_hω : cs.IsReduced ω)
    {t : W} (ht : cs.IsLeftInversion (cs.wordProd ω) t) :
    t ∈ cs.leftInvSeq ω := by
  classical
  by_contra hnot
  obtain ⟨ν, hν, heq⟩ := cs.exists_isReduced (t * cs.wordProd ω)
  have hw := wordAction_record cs ω t (0 : ZMod 2)
  rw [← reflectionAction_wordProd] at hw
  simp only [List.count_eq_zero.mpr hnot, Nat.cast_zero, add_zero] at hw
  have hv := wordAction_record cs ν t (0 : ZMod 2)
  rw [← reflectionAction_wordProd, ← heq] at hv
  have hin : (t * cs.wordProd ω)⁻¹ * t * (t * cs.wordProd ω) =
      (cs.wordProd ω)⁻¹ * t * cs.wordProd ω := by
    rw [mul_inv_rev, ht.1.inv]
    simp [mul_assoc, ht.1.mul_self]
  rw [hin, map_mul, Equiv.Perm.mul_apply, hw,
    reflectionAction_reflection cs ht.1] at hv
  have hmem : t ∈ cs.leftInvSeq ν := by
    by_contra hnone
    have h := congrArg Prod.snd hv
    simp [List.count_eq_zero.mpr hnone] at h
  have hlt := (cs.isLeftInversion_of_mem_leftInvSeq hν hmem).2
  rw [← heq] at hlt
  have hcancel : t * (t * cs.wordProd ω) = cs.wordProd ω := by
    rw [← mul_assoc, ht.1.mul_self, one_mul]
  rw [hcancel] at hlt
  exact (not_lt_of_ge hlt.le) ht.2

/-- Full strong exchange, with the deletion index in the supplied reduced word. -/
theorem strong_exchange {ω : List B} (hω : cs.IsReduced ω) {t : W}
    (ht : cs.IsLeftInversion (cs.wordProd ω) t) :
    ∃ j : ℕ, j < ω.length ∧ t * cs.wordProd ω = cs.wordProd (ω.eraseIdx j) := by
  obtain ⟨j, hj, heq⟩ := List.mem_iff_getElem.mp
    (mem_leftInvSeq_of_inversion cs hω ht)
  refine ⟨j, by simpa using hj, ?_⟩
  rw [← heq, ← List.getD_eq_getElem _ 1 hj]
  exact cs.getD_leftInvSeq_mul_wordProd ω j

end KLInvariance.CoxeterSupport


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

namespace KLInvariance

open Polynomial

universe u v u' v'

variable {B : Type u} {W : Type v} [Group W] {M : CoxeterMatrix B}


theorem bruhat_refl (cs : CoxeterSystem M W) (x : W) : BruhatLE cs x x :=
  Relation.ReflTransGen.refl

theorem bruhat_trans (cs : CoxeterSystem M W) {x y z : W}
    (hxy : BruhatLE cs x y) (hyz : BruhatLE cs y z) : BruhatLE cs x z :=
  hxy.trans hyz

theorem length_le_of_bruhat (cs : CoxeterSystem M W) {x y : W}
    (h : BruhatLE cs x y) : cs.length x ≤ cs.length y := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact le_rfl
  | head hstep _ ih => exact le_trans hstep.1.le ih

theorem length_lt_of_bruhat_ne (cs : CoxeterSystem M W) {x y : W}
    (h : BruhatLE cs x y) (hne : x ≠ y) : cs.length x < cs.length y := by
  rcases h.cases_head with heq | ⟨z, hxz, hzy⟩
  · exact (hne heq).elim
  · exact lt_of_lt_of_le hxz.1 (length_le_of_bruhat cs hzy)

end KLInvariance

section


namespace KLInvariance

open Polynomial

universe u v u' v'

variable {B : Type u} {W : Type v} [klPreservedInstance1 : Group W] {M : CoxeterMatrix B}


/-- A vertex has only finitely many incoming strong Bruhat edges, using
strong exchange proved from the Coxeter presentation above. -/
theorem finite_bruhat_predecessors (cs : CoxeterSystem M W) (b : W) :
    {x : W | BruhatStep cs x b}.Finite := by
  classical
  obtain ⟨ω, hω, heq⟩ := cs.exists_isReduced b
  refine ((cs.leftInvSeq ω).finite_toSet.image (fun t => t * b)).subset ?_
  rintro x ⟨hlen, t, href, hb⟩
  have hx : t * b = x := by
    rw [hb, ← mul_assoc, href.mul_self, one_mul]
  refine ⟨t, ?_, hx⟩
  apply CoxeterSupport.mem_leftInvSeq_of_inversion cs hω
  exact ⟨href, by rw [← heq, hx]; exact hlen⟩

/-- Finiteness of all lower Bruhat ideals, with no finite-rank assumption. -/
theorem finite_bruhat_lower (cs : CoxeterSystem M W) (b : W) :
    {x : W | BruhatLE cs x b}.Finite := by
  classical
  suffices ∀ n : ℕ, ∀ b : W, cs.length b = n → {x : W | BruhatLE cs x b}.Finite by
    exact this (cs.length b) b rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro b hb
    have hfinite : ({b} ∪ ⋃ z ∈ {z : W | BruhatStep cs z b},
        {x : W | BruhatLE cs x z}).Finite :=
      (Set.finite_singleton b).union ((finite_bruhat_predecessors cs b).biUnion
        (fun z hz => ih (cs.length z) (hb ▸ hz.1) z rfl))
    apply hfinite.subset
    intro x hx
    rcases hx.cases_tail with h | ⟨z, hxz, hzb⟩
    · exact Or.inl (h.symm)
    · exact Or.inr (Set.mem_iUnion.mpr ⟨z, Set.mem_iUnion.mpr ⟨hzb, hxz⟩⟩)

/-- The finite-interval obligation in the faithful trusted main target. -/
theorem interval_finite (cs : CoxeterSystem M W) (u b : W) :
    Finite (Interval cs u b) :=
  ((finite_bruhat_lower cs b).subset (fun _ hx => hx.2)).to_subtype


/-! Exchange consequences required for the source's finite-rank reduction
and for consistency of the equal-parameter Hecke recursion. -/

/-- Every word contains a reduced subword with the same product. -/
theorem exists_reduced_subword (cs : CoxeterSystem M W) (ω : List B) :
    ∃ ν : List B, ν.Sublist ω ∧ cs.IsReduced ν ∧ cs.wordProd ν = cs.wordProd ω := by
  induction ω with
  | nil => exact ⟨[], .refl _, by simp [CoxeterSystem.IsReduced], rfl⟩
  | cons i ω ih =>
    obtain ⟨ν, hsub, hν, heq⟩ := ih
    rcases cs.length_simple_mul (cs.wordProd ν) i with hasc | hdesc
    · refine ⟨i :: ν, hsub.cons_cons i, ?_, ?_⟩
      · simpa [CoxeterSystem.IsReduced, cs.wordProd_cons, hν.eq] using hasc
      · simp [cs.wordProd_cons, heq]
    · obtain ⟨j, hj, hdel⟩ := CoxeterSupport.strong_exchange cs hν
        ⟨cs.isReflection_simple i, by omega⟩
      refine ⟨ν.eraseIdx j, ((ν.eraseIdx_sublist j).trans hsub).cons i, ?_, ?_⟩
      · dsimp [CoxeterSystem.IsReduced]
        rw [← hdel, List.length_eraseIdx, ite_eq_left hj]
        have := hν.eq
        omega
      · rw [← hdel, heq, cs.wordProd_cons]

/-- A single downward reflection step can be realized inside any reduced word. -/
theorem subword_of_bruhat_step (cs : CoxeterSystem M W) {x y : W}
    (hxy : BruhatStep cs x y) {ω : List B} (hω : cs.IsReduced ω)
    (hy : cs.wordProd ω = y) :
    ∃ ν : List B, ν.Sublist ω ∧ cs.IsReduced ν ∧ cs.wordProd ν = x := by
  obtain ⟨hlen, t, ht, rfl⟩ := hxy
  have hx : t * cs.wordProd ω = x := by simp [hy, ← mul_assoc, ht.mul_self]
  obtain ⟨j, hj, hdel⟩ := CoxeterSupport.strong_exchange cs hω
    ⟨ht, by
      rw [hx, hy]
      exact hlen⟩
  obtain ⟨ν, hsub, hν, heq⟩ := exists_reduced_subword cs (ω.eraseIdx j)
  exact ⟨ν, hsub.trans (ω.eraseIdx_sublist j), hν, heq.trans (hdel.symm.trans hx)⟩

/-- Forward subword property, for every chosen reduced expression of the top. -/
theorem reduced_subword_of_bruhat (cs : CoxeterSystem M W) {x y : W}
    (hxy : BruhatLE cs x y) {ω : List B} (hω : cs.IsReduced ω)
    (hy : cs.wordProd ω = y) :
    ∃ ν : List B, ν.Sublist ω ∧ cs.IsReduced ν ∧ cs.wordProd ν = x := by
  induction hxy using Relation.ReflTransGen.head_induction_on generalizing ω with
  | refl => exact ⟨ω, .refl _, hω, hy⟩
  | head hstep _ ih =>
    obtain ⟨ν, hsub, hν, heq⟩ := ih hω hy
    obtain ⟨μ, hμsub, hμ, hμeq⟩ := subword_of_bruhat_step cs hstep hν heq
    exact ⟨μ, hμsub.trans hsub, hμ, hμeq⟩


/-- Simple left multiplication preserves the orientation of every reflection
edge except the edge carrying that simple reflection itself. -/
theorem bruhatStep_simple_mul (cs : CoxeterSystem M W) {x y : W}
    (hxy : BruhatStep cs x y) (i : B) (hne : y ≠ cs.simple i * x) :
    BruhatStep cs (cs.simple i * x) (cs.simple i * y) := by
  obtain ⟨hlen, t, ht, heq⟩ := hxy
  refine ⟨?_, cs.simple i * t * cs.simple i, by simpa using ht.conj (cs.simple i), ?_⟩
  · rcases cs.length_simple_mul y i with hasc | hdesc
    · have hx := cs.length_simple_mul x i
      omega
    · obtain ⟨ω, hω, hωeq⟩ := cs.exists_isReduced (cs.simple i * y)
      have hprod : cs.wordProd (i :: ω) = y := by
        rw [cs.wordProd_cons, ← hωeq, cs.simple_mul_simple_cancel_left]
      have hr : cs.IsReduced (i :: ω) := by
        dsimp [CoxeterSystem.IsReduced]
        rw [hprod, ← hω.eq, ← hωeq]
        exact hdesc.symm
      have htx : t * cs.wordProd (i :: ω) = x := by
        rw [hprod, heq, ← mul_assoc, ht.mul_self, one_mul]
      obtain ⟨j, hj, hdel⟩ := CoxeterSupport.strong_exchange cs hr
        ⟨ht, by rw [htx, hprod]; exact hlen⟩
      cases j with
      | zero =>
        have hx : x = cs.wordProd ω := by simpa [htx] using hdel
        exact (hne (by rw [hx, ← cs.wordProd_cons, hprod])).elim
      | succ j =>
        have hx : x = cs.simple i * cs.wordProd (ω.eraseIdx j) := by
          rw [htx, List.eraseIdx_cons_succ, cs.wordProd_cons] at hdel
          exact hdel
        have hsx : cs.simple i * x = cs.wordProd (ω.eraseIdx j) := by simp [hx]
        have hj' : j < ω.length := by simpa using hj
        have hlen' := cs.length_wordProd_le (ω.eraseIdx j)
        rw [List.length_eraseIdx, ite_eq_left hj'] at hlen'
        rw [hsx, hωeq, hω.eq]
        omega
  · rw [heq]
    simp [mul_assoc]

/-- The smaller of `x` and `s*x` in Bruhat order. -/
noncomputable def lowerSimple (cs : CoxeterSystem M W) (i : B) (x : W) : W :=
  if cs.length (cs.simple i * x) < cs.length x then cs.simple i * x else x

/-- The larger of `x` and `s*x` in Bruhat order. -/
noncomputable def upperSimple (cs : CoxeterSystem M W) (i : B) (x : W) : W :=
  if cs.length (cs.simple i * x) < cs.length x then x else cs.simple i * x

theorem lowerSimple_le (cs : CoxeterSystem M W) (i : B) (x : W) :
    BruhatLE cs (lowerSimple cs i x) x := by
  classical
  unfold lowerSimple
  split_ifs with h
  · exact .single ⟨h, cs.simple i, cs.isReflection_simple i, by simp⟩
  · exact .refl

theorem le_upperSimple (cs : CoxeterSystem M W) (i : B) (x : W) :
    BruhatLE cs x (upperSimple cs i x) := by
  classical
  unfold upperSimple
  split_ifs with h
  · exact .refl
  · exact .single ⟨by have := cs.length_simple_mul x i; omega,
      cs.simple i, cs.isReflection_simple i, rfl⟩

@[simp] theorem lowerSimple_mul (cs : CoxeterSystem M W) (i : B) (x : W) :
    lowerSimple cs i (cs.simple i * x) = lowerSimple cs i x := by
  classical
  unfold lowerSimple
  rw [cs.simple_mul_simple_cancel_left]
  have := cs.length_simple_mul x i
  split_ifs <;> first | rfl | omega

@[simp] theorem upperSimple_mul (cs : CoxeterSystem M W) (i : B) (x : W) :
    upperSimple cs i (cs.simple i * x) = upperSimple cs i x := by
  classical
  unfold upperSimple
  rw [cs.simple_mul_simple_cancel_left]
  have := cs.length_simple_mul x i
  split_ifs <;> first | rfl | omega

theorem upperSimple_step_mono (cs : CoxeterSystem M W) (i : B) {x y : W}
    (hxy : BruhatStep cs x y) :
    BruhatLE cs (upperSimple cs i x) (upperSimple cs i y) := by
  classical
  by_cases heq : y = cs.simple i * x
  · rw [heq, upperSimple_mul]
    exact .refl
  · have hs := bruhatStep_simple_mul cs hxy i heq
    by_cases hx : cs.length (cs.simple i * x) < cs.length x
    · by_cases hy : cs.length (cs.simple i * y) < cs.length y
      · simp only [upperSimple, ite_eq_left hx, ite_eq_left hy]
        exact .single hxy
      · simp only [upperSimple, ite_eq_left hx, ite_eq_right hy]
        have hupp := le_upperSimple cs i y
        simp only [upperSimple, ite_eq_right hy] at hupp
        exact (Relation.ReflTransGen.single hxy).trans hupp
    · by_cases hy : cs.length (cs.simple i * y) < cs.length y
      · simp only [upperSimple, ite_eq_right hx, ite_eq_left hy]
        have hlow := lowerSimple_le cs i y
        simp only [lowerSimple, ite_eq_left hy] at hlow
        exact (Relation.ReflTransGen.single hs).trans hlow
      · simp only [upperSimple, ite_eq_right hx, ite_eq_right hy]
        exact .single hs

theorem upperSimple_mono (cs : CoxeterSystem M W) (i : B) {x y : W}
    (hxy : BruhatLE cs x y) :
    BruhatLE cs (upperSimple cs i x) (upperSimple cs i y) := by
  induction hxy using Relation.ReflTransGen.head_induction_on with
  | refl => exact .refl
  | head hstep _ ih => exact (upperSimple_step_mono cs i hstep).trans ih


/-- Converse subword property; no labels are added to Bruhat intervals. -/
theorem bruhat_of_subword (cs : CoxeterSystem M W) {ν ω : List B}
    (hsub : ν.Sublist ω) (hω : cs.IsReduced ω) :
    BruhatLE cs (cs.wordProd ν) (cs.wordProd ω) := by
  induction ω generalizing ν with
  | nil =>
    have : ν = [] := List.sublist_nil.mp hsub
    subst ν
    exact .refl
  | cons i ω ih =>
    have hω' : cs.IsReduced ω := by simpa using hω.drop 1
    have hasc : cs.length (cs.simple i * cs.wordProd ω) = cs.length (cs.wordProd ω) + 1 := by
      simpa [CoxeterSystem.IsReduced, cs.wordProd_cons, hω'.eq] using hω.eq
    have htop : upperSimple cs i (cs.wordProd ω) = cs.wordProd (i :: ω) := by
      simp [upperSimple, show ¬cs.length (cs.simple i * cs.wordProd ω) <
        cs.length (cs.wordProd ω) by omega, cs.wordProd_cons]
    rcases List.sublist_cons_iff.mp hsub with hsub' | ⟨μ, rfl, hμsub⟩
    · exact (ih hsub' hω').trans (htop ▸ le_upperSimple cs i (cs.wordProd ω))
    · have hle := upperSimple_mono cs i (ih hμsub hω')
      rw [htop] at hle
      have hx := le_upperSimple cs i (cs.simple i * cs.wordProd μ)
      rw [upperSimple_mul] at hx
      rw [cs.wordProd_cons]
      exact hx.trans hle

/-- The subword criterion with an arbitrary fixed reduced word for the top. -/
theorem bruhat_iff_reduced_subword (cs : CoxeterSystem M W) {x : W} {ω : List B}
    (hω : cs.IsReduced ω) :
    BruhatLE cs x (cs.wordProd ω) ↔
      ∃ ν : List B, ν.Sublist ω ∧ cs.IsReduced ν ∧ cs.wordProd ν = x := by
  constructor
  · intro hx
    exact reduced_subword_of_bruhat cs hx hω rfl
  · rintro ⟨ν, hsub, _, rfl⟩
    exact bruhat_of_subword cs hsub hω


end KLInvariance
end

end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_Hecke
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Hecke and Laurent actions, braid independence, bar involution, triangular support and inverse coefficients.
-/

section
namespace KLInvariance

open Polynomial

universe u v u' v'

variable {B : Type u} {W : Type v} [klPreservedInstance1 : Group W] {M : CoxeterMatrix B}


namespace Hecke

variable {C : Type*} [CommRing C]

/-- The standard free module of the actual Coxeter group. -/
abbrev Space (W C : Type*) [Zero C] := W →₀ C

noncomputable def basis (w : W) : Space W C := Finsupp.single w 1

include klPreservedInstance1 in
theorem end_ext {f g : Module.End C (Space W C)}
    (h : ∀ w, f (basis w) = g (basis w)) : f = g := by
  have _ := klPreservedInstance1
  apply Finsupp.lhom_ext
  intro w c
  have hc : Finsupp.single w c = c • basis w := by
    simp [basis, Finsupp.smul_single]
  rw [hc, map_smul, map_smul, h]

/-- Normalized Hecke multiplication: H_s² = 1 + a H_s. -/
noncomputable def left (cs : CoxeterSystem M W) (a : C) (i : B) :
    Module.End C (Space W C) :=
  Finsupp.linearCombination C (fun w => basis (cs.simple i * w) +
    if cs.length (cs.simple i * w) < cs.length w then a • basis w else 0)

noncomputable def right (cs : CoxeterSystem M W) (a : C) (i : B) :
    Module.End C (Space W C) :=
  Finsupp.linearCombination C (fun w => basis (w * cs.simple i) +
    if cs.length (w * cs.simple i) < cs.length w then a • basis w else 0)

@[simp] theorem left_basis (cs : CoxeterSystem M W) (a : C) (i : B) (w : W) :
    left cs a i (basis w) = basis (cs.simple i * w) +
      if cs.length (cs.simple i * w) < cs.length w then a • basis w else 0 := by
  simp [left, basis, Finsupp.linearCombination_single]

@[simp] theorem right_basis (cs : CoxeterSystem M W) (a : C) (i : B) (w : W) :
    right cs a i (basis w) = basis (w * cs.simple i) +
      if cs.length (w * cs.simple i) < cs.length w then a • basis w else 0 := by
  simp [right, basis, Finsupp.linearCombination_single]

theorem left_quadratic (cs : CoxeterSystem M W) (a : C) (i : B) :
    left cs a i * left cs a i = 1 + a • left cs a i := by
  apply end_ext
  intro w
  simp only [Module.End.mul_apply, left_basis, map_add,
    cs.simple_mul_simple_cancel_left, LinearMap.add_apply, LinearMap.smul_apply,
    Module.End.one_apply]
  rcases cs.length_simple_mul w i with h | h
  · have hasc : ¬cs.length (cs.simple i * w) < cs.length w := by omega
    have hdesc : cs.length w < cs.length (cs.simple i * w) := by omega
    simp [hasc, hdesc]
  · have hdesc : cs.length (cs.simple i * w) < cs.length w := by omega
    have hasc : ¬cs.length w < cs.length (cs.simple i * w) := by omega
    simp [hasc, hdesc, smul_add, smul_smul]

/-- Inverse normalized Hecke generator, available without inverting any scalar. -/
noncomputable def leftInv (cs : CoxeterSystem M W) (a : C) (i : B) :
    Module.End C (Space W C) := left cs a i - a • 1

theorem left_mul_leftInv (cs : CoxeterSystem M W) (a : C) (i : B) :
    left cs a i * leftInv cs a i = 1 := by
  apply end_ext
  intro w
  have h := congrArg (fun f : Module.End C (Space W C) => f (basis w))
    (left_quadratic cs a i)
  simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.smul_apply,
    Module.End.one_apply] at h
  simp only [Module.End.mul_apply, leftInv, LinearMap.sub_apply, LinearMap.smul_apply,
    Module.End.one_apply, map_sub, map_smul]
  rw [h]
  abel

theorem leftInv_mul_left (cs : CoxeterSystem M W) (a : C) (i : B) :
    leftInv cs a i * left cs a i = 1 := by
  apply end_ext
  intro w
  have h := congrArg (fun f : Module.End C (Space W C) => f (basis w))
    (left_quadratic cs a i)
  simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.smul_apply,
    Module.End.one_apply] at h
  simp only [Module.End.mul_apply, leftInv, LinearMap.sub_apply, LinearMap.smul_apply,
    Module.End.one_apply]
  rw [h]
  abel

noncomputable def leftWord (cs : CoxeterSystem M W) (a : C) (ω : List B) :
    Module.End C (Space W C) := (ω.map (left cs a)).prod

@[simp] theorem leftWord_nil (cs : CoxeterSystem M W) (a : C) :
    leftWord cs a [] = 1 := rfl

@[simp] theorem leftWord_cons (cs : CoxeterSystem M W) (a : C) (i : B) (ω : List B) :
    leftWord cs a (i :: ω) = left cs a i * leftWord cs a ω := rfl

noncomputable def rightWord (cs : CoxeterSystem M W) (a : C) (ω : List B) :
    Module.End C (Space W C) := (ω.map (right cs a)).prod

@[simp] theorem rightWord_nil (cs : CoxeterSystem M W) (a : C) :
    rightWord cs a [] = 1 := rfl

@[simp] theorem rightWord_cons (cs : CoxeterSystem M W) (a : C) (i : B) (ω : List B) :
    rightWord cs a (i :: ω) = right cs a i * rightWord cs a ω := rfl

noncomputable def unit (cs : CoxeterSystem M W) (a : C) (i : B) :
    (Module.End C (Space W C))ˣ where
  val := left cs a i
  inv := leftInv cs a i
  val_inv := left_mul_leftInv cs a i
  inv_val := leftInv_mul_left cs a i

noncomputable def wordUnit (cs : CoxeterSystem M W) (a : C) (ω : List B) :
    (Module.End C (Space W C))ˣ := (ω.map (unit cs a)).prod

@[simp] theorem wordUnit_val (cs : CoxeterSystem M W) (a : C) (ω : List B) :
    (wordUnit cs a ω).val = leftWord cs a ω := by
  induction ω with
  | nil => rfl
  | cons i ω ih =>
    change (unit cs a i).val * (wordUnit cs a ω).val = left cs a i * leftWord cs a ω
    rw [ih]
    rfl


@[simp] theorem leftInv_basis (cs : CoxeterSystem M W) (a : C) (i : B) (w : W) :
    leftInv cs a i (basis w) = basis (cs.simple i * w) -
      if cs.length (cs.simple i * w) < cs.length w then 0 else a • basis w := by
  simp only [leftInv, LinearMap.sub_apply, LinearMap.smul_apply,
    Module.End.one_apply, left_basis]
  split_ifs <;> abel


end Hecke


namespace HeckeQ

open Hecke (Space basis end_ext)
variable {C : Type*} [CommRing C]

/-- Unnormalized equal-parameter Hecke multiplication, T_s²=q+(q−1)T_s. -/
noncomputable def left (cs : CoxeterSystem M W) (q : C) (i : B) :
    Module.End C (Space W C) :=
  Finsupp.linearCombination C (fun w =>
    if cs.length (cs.simple i * w) < cs.length w then
      q • basis (cs.simple i * w) + (q - 1) • basis w
    else basis (cs.simple i * w))

noncomputable def right (cs : CoxeterSystem M W) (q : C) (i : B) :
    Module.End C (Space W C) :=
  Finsupp.linearCombination C (fun w =>
    if cs.length (w * cs.simple i) < cs.length w then
      q • basis (w * cs.simple i) + (q - 1) • basis w
    else basis (w * cs.simple i))

@[simp] theorem left_basis (cs : CoxeterSystem M W) (q : C) (i : B) (w : W) :
    left cs q i (basis w) = if cs.length (cs.simple i * w) < cs.length w then
      q • basis (cs.simple i * w) + (q - 1) • basis w
    else basis (cs.simple i * w) := by
  simp [left, basis, Finsupp.linearCombination_single]

@[simp] theorem right_basis (cs : CoxeterSystem M W) (q : C) (i : B) (w : W) :
    right cs q i (basis w) = if cs.length (w * cs.simple i) < cs.length w then
      q • basis (w * cs.simple i) + (q - 1) • basis w
    else basis (w * cs.simple i) := by
  simp [right, basis, Finsupp.linearCombination_single]


noncomputable def leftWord (cs : CoxeterSystem M W) (q : C) (ω : List B) :
    Module.End C (Space W C) := (ω.map (left cs q)).prod

@[simp] theorem leftWord_nil (cs : CoxeterSystem M W) (q : C) :
    leftWord cs q [] = 1 := rfl

@[simp] theorem leftWord_cons (cs : CoxeterSystem M W) (q : C) (i : B) (ω : List B) :
    leftWord cs q (i :: ω) = left cs q i * leftWord cs q ω := rfl

noncomputable def rightWord (cs : CoxeterSystem M W) (q : C) (ω : List B) :
    Module.End C (Space W C) := (ω.map (right cs q)).prod

@[simp] theorem rightWord_nil (cs : CoxeterSystem M W) (q : C) :
    rightWord cs q [] = 1 := rfl

@[simp] theorem rightWord_cons (cs : CoxeterSystem M W) (q : C) (i : B) (ω : List B) :
    rightWord cs q (i :: ω) = right cs q i * rightWord cs q ω := rfl

end HeckeQ

/-- A concrete finite lower ideal of the genuine Bruhat order. -/
noncomputable def lowerFinset (cs : CoxeterSystem M W) (y : W) : Finset W :=
  (finite_bruhat_lower cs y).toFinset

noncomputable local instance instDecidableEq_solutions_r1f31a4_1 : DecidableEq W := Classical.decEq W
@[simp] theorem mem_lowerFinset (cs : CoxeterSystem M W) (y x : W) :
    x ∈ lowerFinset cs y ↔ BruhatLE cs x y := by
  classical
  exact Set.Finite.mem_toFinset _


end KLInvariance
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

noncomputable local instance instDecidableEq_solutions_1 : DecidableEq W := Classical.decEq W

noncomputable def properIntervalFinset (cs : CoxeterSystem M W) (x y : W) : Finset W := by
  classical
  exact (lowerFinset cs y).filter (fun z => BruhatLE cs x z ∧ x ≠ z)

@[simp] theorem mem_properIntervalFinset (cs : CoxeterSystem M W) (x y z : W) :
    z ∈ properIntervalFinset cs x y ↔ BruhatLE cs z y ∧ BruhatLE cs x z ∧ x ≠ z := by
  classical
  simp [properIntervalFinset]


end KLInvariance
end

end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_Dihedral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Interval restrictions, dihedral Coxeter and Hecke calculations, and the genuine square-parameter R normalization.
-/

section

namespace KLInvariance

universe u₁ v₁ u₂ v₂
variable {B : Type u₁} {W : Type v₁} [Group W] {M : CoxeterMatrix B}
variable {B' : Type u₂} {W' : Type v₂} [Group W'] {M' : CoxeterMatrix B'}

/-- Restriction of the actual interval isomorphism to any subinterval. This
is the same unlabeled map, not a new isomorphism with extra structure. -/
def intervalIso_restrict (cs : CoxeterSystem M W) (cs' : CoxeterSystem M' W')
    {u b : W} {u' b' : W'} (ι : Interval cs u b ≃o Interval cs' u' b')
    (x y : Interval cs u b) :
    Interval cs x.val y.val ≃o Interval cs' (ι x).val (ι y).val where
  toFun z :=
    let zI : Interval cs u b := ⟨z.val, bruhat_trans cs x.property.1 z.property.1,
      bruhat_trans cs z.property.2 y.property.2⟩
    ⟨(ι zI).val, ι.monotone (show x ≤ zI from z.property.1),
      ι.monotone (show zI ≤ y from z.property.2)⟩
  invFun z :=
    let zI : Interval cs' u' b' := ⟨z.val,
      bruhat_trans cs' (ι x).property.1 z.property.1,
      bruhat_trans cs' z.property.2 (ι y).property.2⟩
    ⟨(ι.symm zI).val,
      by
        change x ≤ ι.symm zI
        simpa only [OrderIso.symm_apply_apply] using
          ι.symm.monotone (show ι x ≤ zI from z.property.1),
      by
        change ι.symm zI ≤ y
        simpa only [OrderIso.symm_apply_apply] using
          ι.symm.monotone (show zI ≤ ι y from z.property.2)⟩
  left_inv z := by
    apply Subtype.ext
    let zI : Interval cs u b := ⟨z.val, bruhat_trans cs x.property.1 z.property.1,
      bruhat_trans cs z.property.2 y.property.2⟩
    change (ι.symm (ι zI)).val = zI.val
    rw [ι.symm_apply_apply]
  right_inv z := by
    apply Subtype.ext
    let zI : Interval cs' u' b' := ⟨z.val,
      bruhat_trans cs' (ι x).property.1 z.property.1,
      bruhat_trans cs' z.property.2 (ι y).property.2⟩
    change (ι (ι.symm zI)).val = zI.val
    rw [ι.apply_symm_apply]
  map_rel_iff' := by
    intro z w
    exact ι.map_rel_iff

@[simp] theorem intervalIso_restrict_val (cs : CoxeterSystem M W)
    (cs' : CoxeterSystem M' W') {u b : W} {u' b' : W'}
    (ι : Interval cs u b ≃o Interval cs' u' b') (x y : Interval cs u b)
    (z : Interval cs x.val y.val) :
    (intervalIso_restrict cs cs' ι x y z).val =
      (ι ⟨z.val, bruhat_trans cs x.property.1 z.property.1,
        bruhat_trans cs z.property.2 y.property.2⟩).val := rfl

end KLInvariance

namespace KLInvariance.Dihedral

variable {W : Type*} [Group W] {M : CoxeterMatrix Bool}

/-- The alternating expression starting with `i`, unlike Mathlib's
`alternatingWord`, which specifies the final letter. -/
def alt (i : Bool) : ℕ → List Bool
  | 0 => []
  | n + 1 => i :: alt (!i) n

@[simp] theorem alt_zero (i : Bool) : alt i 0 = [] := rfl
@[simp] theorem alt_succ (i : Bool) (n : ℕ) : alt i (n+1) = i :: alt (!i) n := rfl
@[simp] theorem length_alt (i : Bool) (n : ℕ) : (alt i n).length = n := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih => simp [ih]

@[simp] theorem take_alt (i : Bool) (k n : ℕ) : (alt i n).take k = alt i (min k n) := by
  induction n generalizing i k with
  | zero => simp
  | succ n ih =>
    cases k with
    | zero => simp
    | succ k => simp [ih]

theorem reduced_cons_cons_ne (cs : CoxeterSystem M W) {i j : Bool} {ω : List Bool}
    (h : cs.IsReduced (i :: j :: ω)) : i ≠ j := by
  rintro rfl
  have hlen := cs.length_wordProd_le ω
  have heq := h.eq
  simp only [cs.wordProd_cons, cs.simple_mul_simple_cancel_left, List.length_cons] at heq
  omega

theorem reduced_cons_eq_alt (cs : CoxeterSystem M W) (i : Bool) (ω : List Bool)
    (h : cs.IsReduced (i :: ω)) : i :: ω = alt i (ω.length + 1) := by
  induction ω generalizing i with
  | nil => simp
  | cons j ω ih =>
    have hj : j = !i := by
      have := reduced_cons_cons_ne cs h
      cases i <;> cases j <;> simp_all
    have hω : cs.IsReduced (j :: ω) := by simpa using h.drop 1
    rw [show (j :: ω).length + 1 = (ω.length + 1) + 1 by rfl, alt_succ]
    congr 1
    rw [ih j hω, hj]

theorem reduced_eq_alt (cs : CoxeterSystem M W) (ω : List Bool)
    (h : cs.IsReduced ω) : ∃ i, ω = alt i ω.length := by
  cases ω with
  | nil => exact ⟨false, rfl⟩
  | cons i ω => exact ⟨i, reduced_cons_eq_alt cs i ω h⟩

theorem exists_alt (cs : CoxeterSystem M W) (w : W) :
    ∃ i, w = cs.wordProd (alt i (cs.length w)) := by
  obtain ⟨ω, hω, hw⟩ := cs.exists_isReduced w
  obtain ⟨i, hi⟩ := reduced_eq_alt cs ω hω
  refine ⟨i, ?_⟩
  rw [hw, hω.eq, ← hi]

theorem alt_sublist (i : Bool) {k n : ℕ} (h : k ≤ n) : (alt i k).Sublist (alt i n) := by
  simpa only [take_alt, Nat.min_eq_left h] using List.take_sublist k (alt i n)

end KLInvariance.Dihedral

namespace KLInvariance.Dihedral

noncomputable local instance instDecidable_solutions (p : Prop) : Decidable p := Classical.propDecidable p

variable {W : Type*} [Group W] {M : CoxeterMatrix Bool}

/-- In a rank-two Coxeter system, every strictly shorter element lies below
every longer element. This uses the actual Bruhat subword theorem. -/
theorem shorter_bruhat (cs : CoxeterSystem M W) {x w : W}
    (h : cs.length x < cs.length w) : BruhatLE cs x w := by
  obtain ⟨i, hi⟩ := exists_alt cs w
  obtain ⟨j, hj⟩ := exists_alt cs x
  have hr : cs.IsReduced (alt i (cs.length w)) := by
    change cs.length (cs.wordProd (alt i (cs.length w))) = (alt i (cs.length w)).length
    rw [← hi, length_alt]
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (show cs.length w ≠ 0 by omega)
  rw [hn] at hi hr h
  rw [hi, hj]
  apply bruhat_of_subword cs _ hr
  by_cases hji : j = i
  · subst j
    exact alt_sublist i (by omega)
  · have hj' : j = !i := by cases i <;> cases j <;> first | rfl | exact (hji rfl).elim
    rw [hj', alt_succ]
    exact (alt_sublist (!i) (by omega)).cons i

theorem bruhat_iff_length_lt_or_eq (cs : CoxeterSystem M W) (x w : W) :
    BruhatLE cs x w ↔ cs.length x < cs.length w ∨ x = w := by
  constructor
  · intro h
    by_cases he : x = w
    · exact Or.inr he
    · exact Or.inl (length_lt_of_bruhat_ne cs h he)
  · rintro (h | rfl)
    · exact shorter_bruhat cs h
    · exact bruhat_refl cs _

end KLInvariance.Dihedral

end

end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_Sheaves
attribute [-instance] _root_.OAI.KLInvariance.Graded.ModuleData.instAddCommGroupCarrierObj
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Ordered moment graphs, sheaves, flabbiness, sections and boundary images.
-/

section


/-! The finite-section extension argument required by source §4.3. No BMP
character theorem is postulated. These definitions are ordinary module-valued
sheaves on a directed ordered graph; labels enter later through which edge
modules vanish after localization. -/

namespace KLInvariance.MomentGraph

universe u v w z

structure OrderedGraph (V : Type v) [PartialOrder V] (E : Type w) where
  source : E → V
  target : E → V
  increasing : ∀ e, source e < target e

variable {R : Type u} [CommRing R] {V : Type v} [PartialOrder V] {E : Type w}

structure Sheaf (G : OrderedGraph V E) where
  vertex : V → ModuleCat.{z} R
  edge : E → ModuleCat.{z} R
  lower : ∀ e, (vertex (G.source e)) →ₗ[R] edge e
  upper : ∀ e, (vertex (G.target e)) →ₗ[R] edge e

namespace Sheaf
variable {G : OrderedGraph V E} (B : Sheaf (R := R) G)

abbrev Assignment := ∀ x, B.vertex x

/-- Exactly the usual section compatibility on edges with both endpoints in
`Ω`; coordinates outside `Ω` are ignored and can be chosen arbitrarily. -/
def CompatibleOn (Ω : Set V) (f : B.Assignment) : Prop :=
  ∀ e, G.source e ∈ Ω → G.target e ∈ Ω →
    B.lower e (f (G.source e)) = B.upper e (f (G.target e))

def IsGlobal (f : B.Assignment) : Prop := B.CompatibleOn Set.univ f

/-- Closure under the edges whose modules survive, strictly weaker than
being an ambient upper set. -/
def ClosedUnder (_B : Sheaf (R := R) G) (live : Set E) (Ω : Set V) : Prop :=
  ∀ e ∈ live, G.source e ∈ Ω → G.target e ∈ Ω

end Sheaf
end KLInvariance.MomentGraph

end

section

namespace KLInvariance.MomentGraph.Sheaf

universe u v w z
variable {R : Type u} [CommRing R] {V : Type v} [PartialOrder V] {E : Type w}
  {G : OrderedGraph V E} (B : Sheaf.{u,v,w,z} (R := R) G)

/-- The actual module of sections on a vertex set. Coordinates outside the
set are harmless and ignored by all restriction maps. -/
def sections (Ω : Set V) : Submodule R B.Assignment where
  carrier := {f | B.CompatibleOn Ω f}
  zero_mem' := by intro e hs ht; simp
  add_mem' := by
    intro f g hf hg e hs ht
    change B.lower e (f (G.source e) + g (G.source e)) =
      B.upper e (f (G.target e) + g (G.target e))
    rw [map_add, map_add, hf e hs ht, hg e hs ht]
  smul_mem' := by
    intro r f hf e hs ht
    change B.lower e (r • f (G.source e)) = B.upper e (r • f (G.target e))
    rw [map_smul, map_smul, hf e hs ht]

/-- Generation at a stalk by genuine global sections. -/
def Generated : Prop :=
  ∀ x (b : B.vertex x), ∃ f : B.Assignment, B.IsGlobal f ∧ f x = b

end KLInvariance.MomentGraph.Sheaf


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

namespace KLInvariance
namespace BruhatGraph
universe u v
variable {B : Type u} {W : Type v} [Group W] {M : CoxeterMatrix B}
  (cs : CoxeterSystem M W) (u b : W)

/-- Actual finite directed moment-graph edges, including the non-cover
reflection edges. No reconstruction from the abstract poset is assumed. -/
def Edge := {p : Interval cs u b × Interval cs u b // BruhatStep cs p.1.val p.2.val}

instance instFiniteEdge : Finite (Edge cs u b) := by
  let := interval_finite cs u b
  unfold Edge
  infer_instance

def source (e : Edge cs u b) : Interval cs u b := e.val.1
def target (e : Edge cs u b) : Interval cs u b := e.val.2

def graph : MomentGraph.OrderedGraph (Interval cs u b) (Edge cs u b) where
  source := source cs u b
  target := target cs u b
  increasing e := by
    refine ⟨Relation.ReflTransGen.single e.property, ?_⟩
    intro h
    exact (not_lt_of_ge (length_le_of_bruhat cs h)) e.property.1

/-- Genuine left reflection label; uniquely determined by the endpoints. -/
def label (e : Edge cs u b) : W := (target cs u b e).val * (source cs u b e).val⁻¹

theorem label_isReflection (e : Edge cs u b) : cs.IsReflection (label cs u b e) := by
  obtain ⟨t, ht, htx⟩ := e.property.2
  simpa [label, source, target, htx, mul_assoc] using ht

@[simp] theorem label_mul_source (e : Edge cs u b) :
    label cs u b e * (source cs u b e).val = (target cs u b e).val := by
  simp [label, mul_assoc]

@[simp] theorem label_mul_target (e : Edge cs u b) :
    label cs u b e * (target cs u b e).val = (source cs u b e).val := by
  rw [← label_mul_source cs u b e, ← mul_assoc,
    (label_isReflection cs u b e).mul_self, one_mul]

end BruhatGraph
end KLInvariance


/-! The finite Coxeter relations for the actual real geometric reflection
operators required in `bg:realization`. Faithfulness is not assumed or claimed. -/
namespace KLInvariance.Realization
open Module Polynomial.Chebyshev
variable {V : Type*} [AddCommGroup V] [Module ℝ V]

theorem reflection_pow_even_eq_one
    {α β : V} {f g : Module.Dual ℝ V} (hf : f α = 2) (hg : g β = 2)
    (k : ℕ) (hS : (S ℝ ((k : ℤ) - 1)).eval (f β * g α - 2) = 0) :
    (Module.reflection hf * Module.reflection hg) ^ (2 * k) = 1 := by
  ext v
  rw [Module.reflection_mul_reflection_pow_apply hf hg]
  have h₁ : ((↑(2 * k) : ℤ) - 2) / 2 = (k : ℤ) - 1 := by omega
  have h₂ : ((↑(2 * k) : ℤ) - 1) / 2 = (k : ℤ) - 1 := by omega
  rw [h₁, h₂, hS]
  simp

theorem reflection_pow_odd_eq_one
    {α β : V} {f g : Module.Dual ℝ V} (hf : f α = 2) (hg : g β = 2)
    (k : ℕ)
    (hS : (S ℝ (k : ℤ)).eval (f β * g α - 2) +
      (S ℝ ((k : ℤ) - 1)).eval (f β * g α - 2) = 0) :
    (Module.reflection hf * Module.reflection hg) ^ (2 * k + 1) = 1 := by
  ext v
  rw [Module.reflection_mul_reflection_pow_apply hf hg]
  have h₀ : (↑(2 * k + 1) : ℤ) / 2 = (k : ℤ) := by omega
  have h₁ : ((↑(2 * k + 1) : ℤ) - 2) / 2 = (k : ℤ) - 1 := by omega
  have h₂ : ((↑(2 * k + 1) : ℤ) - 1) / 2 = (k : ℤ) := by omega
  have h₃ : ((↑(2 * k + 1) : ℤ) - 3) / 2 = (k : ℤ) - 1 := by omega
  rw [h₀, h₁, h₂, h₃, hS]
  simp

/-- If the two simple roots have the exact Tits pairing, the corresponding
linear equivalences satisfy their finite Coxeter relation on the entire
ambient space, not just on the root plane. -/
theorem geometric_reflection_relation
    {α β : V} {f g : Module.Dual ℝ V} (hf : f α = 2) (hg : g β = 2)
    (m : ℕ) (hm : 2 ≤ m)
    (hfg : f β = -2 * Real.cos (Real.pi / m))
    (hgf : g α = -2 * Real.cos (Real.pi / m)) :
    (Module.reflection hf * Module.reflection hg) ^ m = 1 := by
  by_cases hm2 : m = 2
  · subst m
    have hfg0 : f β = 0 := by simpa using hfg
    have hgf0 : g α = 0 := by simpa using hgf
    ext v
    change ((Module.reflection hf * Module.reflection hg) ^ 2) v = v
    simp only [pow_two, LinearEquiv.mul_apply, Module.reflection_apply,
      map_sub, map_smul, hf, hg, hfg0, hgf0, ]
    module
  have hm3 : 2 < m := by omega
  have hmR : (2 : ℝ) < m := by exact_mod_cast hm3
  let θ : ℝ := Real.pi / m
  have hθ : (m : ℝ) * θ = Real.pi := by dsimp [θ]; field_simp
  have hθpos : 0 < θ := div_pos Real.pi_pos (by positivity)
  have hθlt : 2 * θ < Real.pi := by
    dsimp [θ]
    rw [← mul_div_assoc]
    apply (div_lt_iff₀ (show (0 : ℝ) < m by positivity)).2
    nlinarith [Real.pi_pos]
  have hsin : Real.sin (2 * θ) ≠ 0 :=
    ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by positivity) hθlt)
  have ht : f β * g α - 2 = 2 * Real.cos (2 * θ) := by
    rw [hfg, hgf, Real.cos_two_mul]
    dsimp [θ]
    ring
  rcases Nat.even_or_odd m with he | ho
  · obtain ⟨k, hk⟩ := he
    have hm' : m = 2 * k := by omega
    clear hk
    subst m
    apply reflection_pow_even_eq_one hf hg k
    rw [ht]
    have h := S_two_mul_real_cos (2 * θ) ((k : ℤ) - 1)
    have ha : (((k : ℤ) - 1 : ℤ) + 1 : ℝ) * (2 * θ) = Real.pi := by
      push_cast
      push_cast at hθ
      nlinarith [hθ]
    rw [ha, Real.sin_pi] at h
    exact (mul_eq_zero.mp h).resolve_right hsin
  · obtain ⟨k, hk⟩ := ho
    have hm' : m = 2 * k + 1 := by omega
    clear hk
    subst m
    apply reflection_pow_odd_eq_one hf hg k
    rw [ht]
    have h₁ := S_two_mul_real_cos (2 * θ) (k : ℤ)
    have h₂ := S_two_mul_real_cos (2 * θ) ((k : ℤ) - 1)
    have ha : ((k : ℤ) + 1 : ℝ) * (2 * θ) = Real.pi + θ := by
      push_cast
      push_cast at hθ
      nlinarith [hθ]
    have hb : (((k : ℤ) - 1 : ℤ) + 1 : ℝ) * (2 * θ) = Real.pi - θ := by
      push_cast
      push_cast at hθ
      nlinarith [hθ]
    rw [ha] at h₁
    simp only [Real.sin_add, Real.sin_pi, Real.cos_pi, zero_mul, neg_one_mul,
      zero_add] at h₁
    rw [hb, Real.sin_pi_sub] at h₂
    apply (mul_eq_zero.mp (show
      ((S ℝ (k : ℤ)).eval (2 * Real.cos (2 * θ)) +
      (S ℝ ((k : ℤ) - 1)).eval (2 * Real.cos (2 * θ))) *
      Real.sin (2 * θ) = 0 by nlinarith [h₁, h₂])).resolve_right hsin
end KLInvariance.Realization

namespace KLInvariance.Realization
open Module
universe u v z
variable {I : Type u} {W : Type v} [Group W] {M : CoxeterMatrix I}
variable (cs : CoxeterSystem M W)
variable {V : Type z} [AddCommGroup V] [Module ℝ V]
variable (B : LinearMap.BilinForm ℝ V) (α : I → V)
variable (hα : ∀ i j, B (α i) (α j) = -2 * Real.cos (Real.pi / M i j))

include hα

lemma simple_normal_value (i : I) : B (α i) (α i) = 2 := by
  rw [hα]
  simp

noncomputable def geometricSimple (i : I) : V ≃ₗ[ℝ] V :=
  Module.reflection (simple_normal_value B α hα i)

theorem geometricSimple_liftable : M.IsLiftable (geometricSimple B α hα) := by
  intro i j
  by_cases hij : i = j
  · subst j
    rw [M.diagonal, pow_one]
    ext v
    exact Module.involutive_reflection (simple_normal_value B α hα i) v
  by_cases hm0 : M i j = 0
  · rw [hm0, pow_zero]
  have hm2 : 2 ≤ M i j := by
    have := M.off_diagonal i j hij
    omega
  exact geometric_reflection_relation (simple_normal_value B α hα i)
    (simple_normal_value B α hα j) (M i j) hm2 (hα i j)
    (by rw [hα j i, M.symmetric j i])

/-- The genuine geometric reflection action. Each relation has been proved;
this definition does not presuppose a faithful representation. -/
noncomputable def geometricAction : W →* (V ≃ₗ[ℝ] V) :=
  cs.lift ⟨geometricSimple B α hα, geometricSimple_liftable B α hα⟩

@[simp] theorem geometricAction_simple (i : I) :
    geometricAction cs B α hα (cs.simple i) = geometricSimple B α hα i :=
  cs.lift_apply_simple (geometricSimple_liftable B α hα) i

theorem geometricSimple_preserves (hs : B.IsSymm) (i : I) (v w : V) :
    B (geometricSimple B α hα i v) (geometricSimple B α hα i w) = B v w := by
  simp only [geometricSimple, Module.reflection_apply, map_sub, map_smul,
    LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
  rw [hs.eq v (α i), simple_normal_value B α hα i]
  ring

theorem geometricAction_preserves (hs : B.IsSymm) (w : W) (v z : V) :
    B (geometricAction cs B α hα w v) (geometricAction cs B α hα w z) = B v z := by
  obtain ⟨ω, rfl⟩ := cs.wordProd_surjective w
  induction ω with
  | nil => simp
  | cons i ω ih =>
    rw [cs.wordProd_cons, map_mul]
    simp only [LinearEquiv.mul_apply, geometricAction_simple]
    rw [geometricSimple_preserves B α hα hs, ih]

end KLInvariance.Realization

namespace KLInvariance.TitsSpace
open Module
universe u v
variable {I : Type u} [Fintype I] (M : CoxeterMatrix I)
noncomputable section


def gram (i j : I) : ℝ := -2 * Real.cos (Real.pi / M i j)

def root (i : I) : I → ℝ := by
  classical
  exact Pi.single i 1

def normal (i : I) : Module.Dual ℝ (I → ℝ) :=
  ∑ j, gram M i j • LinearMap.proj j

def form : LinearMap.BilinForm ℝ (I → ℝ) :=
  ∑ i, (LinearMap.proj i).smulRight (normal M i)

@[simp] theorem normal_root (i j : I) : normal M i (root j) = gram M i j := by
  classical
  simp only [normal, root, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.proj_apply, smul_eq_mul]
  rw [Finset.sum_eq_single j]
  · simp
  · intro b _ hbj
    simp [hbj]
  · simp

@[simp] theorem form_root (i : I) (v : I → ℝ) : form M (root i) v = normal M i v := by
  classical
  simp [form, root, LinearMap.sum_apply]

theorem form_symm : (form M).IsSymm := by
  constructor
  intro v w
  simp only [form, normal, LinearMap.sum_apply, LinearMap.smulRight_apply,
    LinearMap.smul_apply, LinearMap.proj_apply, smul_eq_mul]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [show gram M j i = gram M i j by simp only [gram, M.symmetric j i]]
  ring

theorem form_roots (i j : I) : form M (root i) (root j) =
    -2 * Real.cos (Real.pi / M i j) := by simp [gram]

/-- A concrete action on the ordinary geometric root space over ℝ. Its
faithfulness and the root-sign theorem are still required for the main proof. -/
def action {W : Type v} [Group W] (cs : CoxeterSystem M W) :
    W →* ((I → ℝ) ≃ₗ[ℝ] (I → ℝ)) :=
  Realization.geometricAction cs (form M) root (form_roots M)

@[simp] theorem action_simple {W : Type v} [Group W] (cs : CoxeterSystem M W)
    (i : I) (v : I → ℝ) :
    action M cs (cs.simple i) v = v - normal M i v • root i := by
  simp [action, Realization.geometricAction_simple, Realization.geometricSimple,
    Module.reflection_apply]

theorem action_preserves {W : Type v} [Group W] (cs : CoxeterSystem M W)
    (w : W) (v z : I → ℝ) : form M (action M cs w v) (action M cs w z) = form M v z :=
  Realization.geometricAction_preserves cs (form M) root (form_roots M) (form_symm M) w v z
end
end KLInvariance.TitsSpace

namespace KLInvariance.Realization
universe u
variable {V : Type u} [AddCommGroup V] [Module ℝ V]


abbrev Extension (B : LinearMap.BilinForm ℝ V) := V × Module.Dual ℝ (LinearMap.ker B)

noncomputable def extensionForm (B : LinearMap.BilinForm ℝ V)
    (p : V →ₗ[ℝ] LinearMap.ker B) : LinearMap.BilinForm ℝ (Extension B) where
  toFun x :=
    { toFun := fun y => B x.1 y.1 + x.2 (p y.1) + y.2 (p x.1)
      map_add' := by intro y z; simp [map_add]; ring
      map_smul' := by intro t y; simp [map_smul]; ring }
  map_add' := by
    intro x y
    apply LinearMap.ext
    intro z
    change B (x.1 + y.1) z.1 + (x.2 + y.2) (p z.1) + z.2 (p (x.1 + y.1)) = _
    simp [map_add]
    ring
  map_smul' := by
    intro t x
    apply LinearMap.ext
    intro z
    change B (t • x.1) z.1 + (t • x.2) (p z.1) + z.2 (p (t • x.1)) = _
    simp [map_smul]
    ring

@[simp] theorem extensionForm_apply (B : LinearMap.BilinForm ℝ V)
    (p : V →ₗ[ℝ] LinearMap.ker B) (x y : Extension B) :
    extensionForm B p x y = B x.1 y.1 + x.2 (p y.1) + y.2 (p x.1) := rfl

@[simp] theorem extensionForm_inl (B : LinearMap.BilinForm ℝ V)
    (p : V →ₗ[ℝ] LinearMap.ker B) (v w : V) :
    extensionForm B p (v, 0) (w, 0) = B v w := by simp

theorem extensionForm_symm (B : LinearMap.BilinForm ℝ V) (hB : B.IsSymm)
    (p : V →ₗ[ℝ] LinearMap.ker B) : (extensionForm B p).IsSymm := by
  constructor
  intro x y
  simp only [extensionForm_apply]
  rw [hB.eq x.1 y.1]
  ring

theorem extensionForm_nondegenerate (B : LinearMap.BilinForm ℝ V)
    (hB : B.IsSymm) (p : V →ₗ[ℝ] LinearMap.ker B)
    (hp : ∀ k : LinearMap.ker B, p k.val = k) : (extensionForm B p).Nondegenerate := by
  have hf : ∀ x : Extension B, (∀ y, extensionForm B p x y = 0) → x = 0 := by
    rintro ⟨v, φ⟩ hx
    have hpv : p v = 0 := by
      apply (Module.forall_dual_apply_eq_zero_iff ℝ (p v)).mp
      intro ψ
      simpa using hx (0, ψ)
    have hφ : φ = 0 := by
      ext k
      have hbk : B k.val = 0 := k.property
      have hvk : B v k.val = 0 := by
        rw [hB.eq v k.val, hbk]
        rfl
      simpa [hvk, hp k, hpv] using hx (k.val, 0)
    have hbv : v ∈ LinearMap.ker B := by
      change B v = 0
      ext w
      simpa [hφ, hpv] using hx (w, 0)
    have hv : v = 0 := by
      have h := hp ⟨v, hbv⟩
      rw [hpv] at h
      exact (congrArg Subtype.val h).symm
    simp [hv, hφ]
  exact ⟨hf, fun x hx => hf x (fun y => by
    rw [(extensionForm_symm B hB p).eq]
    exact hx y)⟩

theorem exists_minimal_nondegenerate_extension (B : LinearMap.BilinForm ℝ V)
    (hB : B.IsSymm) :
    ∃ C : LinearMap.BilinForm ℝ (Extension B), C.IsSymm ∧ C.Nondegenerate ∧
      ∀ v w, C (v, 0) (w, 0) = B v w := by
  obtain ⟨Q, hQ⟩ := (LinearMap.ker B).exists_isCompl
  let p := (LinearMap.ker B).projectionOnto Q hQ
  exact ⟨extensionForm B p, extensionForm_symm B hB p,
    extensionForm_nondegenerate B hB p (Submodule.projectionOnto_apply_left hQ),
    extensionForm_inl B p⟩

end KLInvariance.Realization

namespace KLInvariance.TitsSpace
open Module
universe u v
variable {I : Type u} [Fintype I] (M : CoxeterMatrix I)
noncomputable section

abbrev Extended := Realization.Extension (form M)

def extendedForm : LinearMap.BilinForm ℝ (Extended M) :=
  Classical.choose (Realization.exists_minimal_nondegenerate_extension (form M) (form_symm M))

theorem extendedForm_spec : (extendedForm M).IsSymm ∧ (extendedForm M).Nondegenerate ∧
    ∀ v w, extendedForm M (v, 0) (w, 0) = form M v w :=
  Classical.choose_spec (Realization.exists_minimal_nondegenerate_extension (form M) (form_symm M))

def extendedRoot (i : I) : Extended M := (root i, 0)

@[simp] theorem extendedForm_roots (i j : I) :
    extendedForm M (extendedRoot M i) (extendedRoot M j) =
      -2 * Real.cos (Real.pi / M i j) := by
  rw [extendedRoot, extendedRoot, (extendedForm_spec M).2.2, form_roots]

def extendedAction {W : Type v} [Group W] (cs : CoxeterSystem M W) :
    W →* (Extended M ≃ₗ[ℝ] Extended M) :=
  Realization.geometricAction cs (extendedForm M) (extendedRoot M) (extendedForm_roots M)

theorem extendedAction_preserves {W : Type v} [Group W] (cs : CoxeterSystem M W)
    (w : W) (v z : Extended M) :
    extendedForm M (extendedAction M cs w v) (extendedAction M cs w z) = extendedForm M v z :=
  Realization.geometricAction_preserves cs (extendedForm M) (extendedRoot M)
    (extendedForm_roots M) (extendedForm_spec M).1 w v z

@[simp] theorem extendedAction_simple {W : Type v} [Group W] (cs : CoxeterSystem M W)
    (i : I) (v : Extended M) :
    extendedAction M cs (cs.simple i) v =
      v - extendedForm M (extendedRoot M i) v • extendedRoot M i := by
  simp only [extendedAction, Realization.geometricAction_simple,
    Realization.geometricSimple, Module.reflection_apply]

/-- The extended action genuinely restricts to the ordinary geometric action.
Injectivity of that latter action is an outstanding obligation, not a hypothesis
hidden in the construction of this extension. -/
theorem extendedAction_restrict {W : Type v} [Group W] (cs : CoxeterSystem M W)
    (w : W) (v : I → ℝ) :
    extendedAction M cs w (v, 0) = (action M cs w v, 0) := by
  obtain ⟨ω, rfl⟩ := cs.wordProd_surjective w
  induction ω generalizing v with
  | nil => simp
  | cons i ω ih =>
    rw [cs.wordProd_cons, map_mul, map_mul]
    simp only [LinearEquiv.mul_apply, ih, extendedAction_simple, action_simple]
    change (action M cs (cs.wordProd ω) v, 0) -
      extendedForm M (root i, 0) (action M cs (cs.wordProd ω) v, 0) • (root i, 0) = _
    rw [(extendedForm_spec M).2.2, form_root]
    ext <;> simp

end
end KLInvariance.TitsSpace

namespace KLInvariance
universe u v
variable {B : Type u} {W : Type v} [Group W] {M : CoxeterMatrix B}

namespace ParabolicSupport
open CoxeterSystem

variable (cs : CoxeterSystem M W) (J : Set B)

/-- The genuine subgroup generated by a subset of simple reflections. -/
def subgroup : Subgroup W := Subgroup.closure (cs.simple '' J)

theorem word_mem {ν : List B} (hν : ∀ i ∈ ν, i ∈ J) :
    cs.wordProd ν ∈ subgroup cs J := by
  induction ν with
  | nil => exact (subgroup cs J).one_mem
  | cons i ν ih =>
    rw [cs.wordProd_cons]
    exact (subgroup cs J).mul_mem
      (Subgroup.subset_closure ⟨i, hν i (by simp), rfl⟩)
      (ih fun j hj => hν j (by simp [hj]))

theorem exists_word {w : W} (hw : w ∈ subgroup cs J) :
    ∃ ν : List B, (∀ i ∈ ν, i ∈ J) ∧ cs.wordProd ν = w := by
  induction hw using Subgroup.closure_induction with
  | mem w hw =>
    obtain ⟨i, hi, rfl⟩ := hw
    exact ⟨[i], by simpa using hi, by simp⟩
  | one => exact ⟨[], by simp, by simp⟩
  | mul x y hx hy ihx ihy =>
    obtain ⟨ω, hω, rfl⟩ := ihx
    obtain ⟨ν, hν, rfl⟩ := ihy
    exact ⟨ω ++ ν, fun i hi => (List.mem_append.mp hi).elim (hω i) (hν i),
      cs.wordProd_append ω ν⟩
  | inv x hx ih =>
    obtain ⟨ω, hω, rfl⟩ := ih
    exact ⟨ω.reverse, by simpa using hω, cs.wordProd_reverse ω⟩

theorem exists_reduced_word {w : W} (hw : w ∈ subgroup cs J) :
    ∃ ν : List B, (∀ i ∈ ν, i ∈ J) ∧ cs.IsReduced ν ∧ cs.wordProd ν = w := by
  obtain ⟨ω, hω, hprod⟩ := exists_word cs J hw
  obtain ⟨ν, hsub, hν, heq⟩ := exists_reduced_subword cs ω
  exact ⟨ν, fun i hi => hω i (hsub.subset hi), hν, heq.trans hprod⟩

/-- A minimal right-coset representative concatenates with every reduced
word in the parabolic generators without cancellations. -/
theorem reduced_append_of_minimal {u : W}
    (hmin : ∀ v ∈ subgroup cs J, cs.length u ≤ cs.length (u * v))
    {ω ν : List B} (hω : cs.IsReduced ω) (hu : cs.wordProd ω = u)
    (hν : cs.IsReduced ν) (hJ : ∀ i ∈ ν, i ∈ J) :
    cs.IsReduced (ω ++ ν) := by
  obtain ⟨τ, hsub, hτ, hprod⟩ := exists_reduced_subword cs (ω ++ ν)
  obtain ⟨ω', ν', rfl, hωsub, hνsub⟩ := List.sublist_append_iff.mp hsub
  have hprod' : cs.wordProd ω' * cs.wordProd ν' = u * cs.wordProd ν := by
    simpa [cs.wordProd_append, hu] using hprod
  have hω' : cs.wordProd ω' = u * (cs.wordProd ν * (cs.wordProd ν')⁻¹) := by
    rw [← mul_assoc, ← hprod']
    group
  have hlen := hmin (cs.wordProd ν * (cs.wordProd ν')⁻¹)
    ((subgroup cs J).mul_mem (word_mem cs J hJ)
      ((subgroup cs J).inv_mem (word_mem cs J fun i hi => hJ i (hνsub.subset hi))))
  rw [← hω'] at hlen
  have hbound := cs.length_wordProd_le ω'
  have homega := hω.eq
  rw [hu] at homega
  have hle := hωsub.length_le
  have heqω := hωsub.eq_of_length (by omega)
  subst ω'
  have heqν : cs.wordProd ν' = cs.wordProd ν := by
    rw [hu] at hprod'
    exact mul_left_cancel hprod'
  have hboundν := cs.length_wordProd_le ν'
  rw [heqν, hν.eq] at hboundν
  have heqν' := hνsub.eq_of_length (by have := hνsub.length_le; omega)
  simpa [heqν'] using hτ

theorem length_mul_of_minimal {u v : W}
    (hmin : ∀ z ∈ subgroup cs J, cs.length u ≤ cs.length (u * z))
    (hv : v ∈ subgroup cs J) : cs.length (u * v) = cs.length u + cs.length v := by
  obtain ⟨ω, hω, hu⟩ := cs.exists_isReduced u
  obtain ⟨ν, hJ, hν, hvprod⟩ := exists_reduced_word cs J hv
  have h := (reduced_append_of_minimal cs J hmin hω hu.symm hν hJ).eq
  simpa [cs.wordProd_append, hu, ← hvprod, hω.eq, hν.eq] using h

/-- Every right parabolic coset has a minimal representative. -/
theorem exists_minimal (w : W) :
    ∃ u v : W, v ∈ subgroup cs J ∧ w = u * v ∧
      ∀ z ∈ subgroup cs J, cs.length u ≤ cs.length (u * z) := by
  classical
  have hex : ∃ n : ℕ, ∃ u v : W, v ∈ subgroup cs J ∧ w = u * v ∧ cs.length u = n :=
    ⟨cs.length w, w, 1, (subgroup cs J).one_mem, by simp, rfl⟩
  obtain ⟨u, v, hv, hw, hu⟩ := Nat.find_spec hex
  refine ⟨u, v, hv, hw, fun z hz => ?_⟩
  rw [hu]
  apply Nat.find_min' hex
  refine ⟨u * z, z⁻¹ * v, (subgroup cs J).mul_mem ((subgroup cs J).inv_mem hz) hv, ?_, rfl⟩
  simpa [mul_assoc] using hw

theorem minimal_simple_ascent {u : W}
    (hmin : ∀ z ∈ subgroup cs J, cs.length u ≤ cs.length (u * z))
    {i : B} (hi : i ∈ J) : cs.length (u * cs.simple i) = cs.length u + 1 := by
  have h := length_mul_of_minimal cs J hmin (Subgroup.subset_closure ⟨i, hi, rfl⟩)
  simpa using h

/-- The decomposition is length-additive, including after multiplying by
any of the chosen simple generators. This is used in the root-sign induction. -/
theorem exists_length_additive_decomposition (w : W) :
    ∃ u v : W, v ∈ subgroup cs J ∧ w = u * v ∧
      cs.length w = cs.length u + cs.length v ∧
      (∀ i ∈ J, cs.length (u * cs.simple i) = cs.length u + 1) ∧
      (∀ i ∈ J, cs.length (w * cs.simple i) = cs.length u + cs.length (v * cs.simple i)) := by
  obtain ⟨u, v, hv, hw, hmin⟩ := exists_minimal cs J w
  refine ⟨u, v, hv, hw, ?_, (fun i hi => minimal_simple_ascent cs J hmin hi), ?_⟩
  · rw [hw]
    exact length_mul_of_minimal cs J hmin hv
  · intro i hi
    rw [hw, mul_assoc]
    exact length_mul_of_minimal cs J hmin
      ((subgroup cs J).mul_mem hv (Subgroup.subset_closure ⟨i, hi, rfl⟩))

end ParabolicSupport

end KLInvariance

namespace KLInvariance.ParabolicSupport
open CoxeterSystem
universe u v
variable {B : Type u} {W : Type v} [Group W] {M : CoxeterMatrix B}
variable (cs : CoxeterSystem M W)

theorem reduced_of_append {ω ν : List B} (h : cs.IsReduced (ω ++ ν)) :
    cs.IsReduced ω := by
  simpa using h.take ω.length

/-- A reduced two-letter word followed by `i` must alternate and end in `j`. -/
theorem reduced_pair_eq_alternating {ω : List B} {i j : B} (hij : i ≠ j)
    (hJ : ∀ k ∈ ω, k = i ∨ k = j) (hred : cs.IsReduced (ω ++ [i])) :
    ω = alternatingWord i j ω.length := by
  induction ω using List.reverseRecOn generalizing i j with
  | nil => rfl
  | append_singleton ω k ih =>
    have hk : k = i ∨ k = j := hJ k (by simp)
    have hki : k ≠ i := by
      rintro rfl
      have hlen := hred.eq
      simp only [cs.wordProd_append, cs.wordProd_singleton, List.length_append,
        List.length_singleton, mul_assoc, cs.simple_mul_simple_self, mul_one] at hlen
      have := cs.length_wordProd_le ω
      omega
    have hkj : k = j := hk.resolve_left hki
    subst k
    have hprefix : cs.IsReduced (ω ++ [j]) := reduced_of_append cs hred
    rw [List.length_append, List.length_singleton, alternatingWord_succ, List.concat_eq_append]
    congr 1
    apply ih hij.symm
    · intro k hk
      exact (hJ k (List.mem_append.mpr (Or.inl hk))).symm
    · exact hprefix

/-- The coefficients in the root formula are controlled by genuine reducedness,
not by a separate rank-two length assumption. -/
theorem alternating_length_bound {ω : List B} {i j : B} (hij : i ≠ j)
    (hJ : ∀ k ∈ ω, k = i ∨ k = j) (hred : cs.IsReduced (ω ++ [i])) :
    M i j = 0 ∨ ω.length + 1 ≤ M i j := by
  by_cases hm : M i j = 0
  · exact Or.inl hm
  · right
    have heq := reduced_pair_eq_alternating cs hij hJ hred
    have hr : cs.IsReduced (alternatingWord j i (ω.length + 1)) := by
      rw [alternatingWord_succ, ← heq]
      simpa [List.concat_eq_append] using hred
    by_contra hn
    apply cs.not_isReduced_alternatingWord j i (by simpa [M.symmetric] using hm)
      (by simpa [M.symmetric] using (show M i j < ω.length + 1 by omega)) hr

end KLInvariance.ParabolicSupport

namespace KLInvariance.TitsSpace
open CoxeterSystem Polynomial Polynomial.Chebyshev
universe u v
variable {I : Type u} [klPreservedInstance5 : Fintype I] (M : CoxeterMatrix I)
variable {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section

def rootCoeff (i j : I) (n : ℤ) : ℝ :=
  (S ℝ n).eval (2 * Real.cos (Real.pi / M i j))

include klPreservedInstance5 in
@[simp] theorem rootCoeff_zero (i j : I) : rootCoeff M i j 0 = 1 := by
  have _ := klPreservedInstance5
  simp [rootCoeff]
include klPreservedInstance5 in
@[simp] theorem rootCoeff_neg_one (i j : I) : rootCoeff M i j (-1) = 0 := by
  have _ := klPreservedInstance5
  simp [rootCoeff]

include klPreservedInstance5 in
theorem rootCoeff_succ (i j : I) (n : ℤ) :
    rootCoeff M i j (n + 1) =
      (2 * Real.cos (Real.pi / M i j)) * rootCoeff M i j n - rootCoeff M i j (n-1) := by
  have _ := klPreservedInstance5
  simp [rootCoeff, S_add_one]

include klPreservedInstance5 in
@[simp] theorem gram_diag (i : I) : gram M i i = 2 := by
  have _ := klPreservedInstance5
  simp [gram]

/-- Exact rank-two root formula, including the infinite pairing. -/
theorem alternating_root (i j : I) (n : ℕ) :
    action M cs (cs.wordProd (alternatingWord i j n)) (root i) =
      if Even n then
        rootCoeff M i j n • root i + rootCoeff M i j ((n : ℤ)-1) • root j
      else rootCoeff M i j ((n : ℤ)-1) • root i + rootCoeff M i j n • root j := by
  induction n with
  | zero => simp [alternatingWord]
  | succ n ih =>
    rw [alternatingWord_succ', cs.wordProd_cons, map_mul, LinearEquiv.mul_apply, ih]
    have hrec := rootCoeff_succ M i j (n : ℤ)
    have hsymm : gram M j i = gram M i j := by simp [gram, M.symmetric j i]
    by_cases hn : Even n
    · simp only [hn, ite_true, if_true, Nat.even_add_one, not_true_eq_false, ite_false, if_false]
      rw [action_simple]
      simp only [map_add, map_smul, normal_root, gram_diag, hsymm]
      push_cast
      rw [show (n : ℤ) + 1 - 1 = n by omega, hrec]
      simp only [gram]
      module
    · simp only [hn, ite_false, if_false, Nat.even_add_one, not_false_eq_true, ite_true, if_true]
      rw [action_simple]
      simp only [map_add, map_smul, normal_root, gram_diag]
      push_cast
      rw [show (n : ℤ) + 1 - 1 = n by omega, hrec]
      simp only [gram]
      module

/-- For a reduced alternating word followed by the other generator, both
rank-two coefficients are nonnegative. -/
theorem rootCoeff_nonneg (i j : I) {n : ℤ} (hn : -1 ≤ n)
    (hm : M i j = 0 ∨ n + 1 ≤ (M i j : ℤ)) (hij : i ≠ j) :
    0 ≤ rootCoeff M i j n := by
  rcases hm with hm | hm
  · simp only [rootCoeff, hm, Nat.cast_zero, div_zero, Real.cos_zero, mul_one, S_eval_two]
    exact_mod_cast (by omega : (0 : ℤ) ≤ n + 1)
  · by_cases hn0 : n = -1
    · simp [hn0]
    have hn1 : 0 < n + 1 := by omega
    have hMpos : (0 : ℝ) < M i j := by exact_mod_cast (by omega : 0 < M i j)
    have hM2 : 2 ≤ M i j := by
      have := M.off_diagonal i j hij
      omega
    let θ : ℝ := Real.pi / M i j
    have hθpos : 0 < θ := div_pos Real.pi_pos hMpos
    have hθlt : θ < Real.pi := by
      dsimp [θ]
      apply (div_lt_iff₀ hMpos).2
      have : (2 : ℝ) ≤ M i j := by exact_mod_cast hM2
      nlinarith [Real.pi_pos]
    have hsin := Real.sin_pos_of_pos_of_lt_pi hθpos hθlt
    have heq := S_two_mul_real_cos θ n
    have hargpos : 0 ≤ ((n : ℝ) + 1) * θ := by
      have : (0 : ℝ) < (n : ℝ) + 1 := by exact_mod_cast hn1
      positivity
    have hargle : ((n : ℝ) + 1) * θ ≤ Real.pi := by
      dsimp [θ]
      rw [← mul_div_assoc]
      apply (div_le_iff₀ hMpos).2
      have : (n : ℝ) + 1 ≤ M i j := by exact_mod_cast hm
      nlinarith [Real.pi_pos]
    have hs := Real.sin_nonneg_of_nonneg_of_le_pi hargpos hargle
    change 0 ≤ (S ℝ n).eval (2 * Real.cos θ)
    nlinarith [heq]
end
end KLInvariance.TitsSpace

namespace KLInvariance.TitsSpace
open CoxeterSystem
universe u v
variable {I : Type u} [klPreservedInstance6 : Fintype I] (M : CoxeterMatrix I)
variable {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section

include klPreservedInstance6 in
@[simp] theorem root_nonneg (i k : I) : 0 ≤ root i k := by
  have _ := klPreservedInstance6
  classical
  simp only [root, Pi.single_apply]
  split_ifs <;> norm_num

/-- Positivity of a rank-two reduced tail after an already positive prefix. -/
theorem pair_image_nonneg (u : W) {i j : I} (hij : i ≠ j)
    (hi : ∀ k, 0 ≤ action M cs u (root i) k)
    (hj : ∀ k, 0 ≤ action M cs u (root j) k)
    {ω : List I} (hJ : ∀ k ∈ ω, k = i ∨ k = j)
    (hred : cs.IsReduced (ω ++ [i])) :
    ∀ k, 0 ≤ action M cs (u * cs.wordProd ω) (root i) k := by
  have heq := ParabolicSupport.reduced_pair_eq_alternating cs hij hJ hred
  have hbound := ParabolicSupport.alternating_length_bound cs hij hJ hred
  have hn : 0 ≤ rootCoeff M i j (ω.length : ℤ) :=
    rootCoeff_nonneg M i j (by omega) (by rcases hbound with h|h; exact Or.inl h; right; omega) hij
  have hn' : 0 ≤ rootCoeff M i j ((ω.length : ℤ)-1) :=
    rootCoeff_nonneg M i j (by omega) (by rcases hbound with h|h; exact Or.inl h; right; omega) hij
  intro k
  rw [map_mul, LinearEquiv.mul_apply, heq, alternating_root]
  split_ifs
  all_goals
    simp only [map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg (by assumption) (by exact hi k))
      (mul_nonneg (by assumption) (by first | exact hi k | exact hj k))

/-- The genuine Tits root-sign theorem for ascents, proved from exchange,
minimal parabolic cosets and the rank-two trigonometric formulas. -/
theorem action_root_nonneg_of_ascent (w : W) (i : I)
    (hasc : cs.length (w * cs.simple i) = cs.length w + 1) :
    ∀ k, 0 ≤ action M cs w (root i) k := by
  suffices ∀ n : ℕ, ∀ w : W, cs.length w = n → ∀ i : I,
      cs.length (w * cs.simple i) = cs.length w + 1 →
      ∀ k, 0 ≤ action M cs w (root i) k by
    exact this (cs.length w) w rfl i hasc
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro w hwlen i hasc
    by_cases hw : w = 1
    · subst w
      simp
    obtain ⟨j, hj⟩ := cs.exists_rightDescent_of_ne_one hw
    change cs.length (w * cs.simple j) < cs.length w at hj
    have hij : i ≠ j := by rintro rfl; omega
    obtain ⟨u, v, hv, huv, hlen, huasc, hmul⟩ :=
      ParabolicSupport.exists_length_additive_decomposition cs ({i, j} : Set I) w
    have himem : i ∈ ({i, j} : Set I) := by simp
    have hjmem : j ∈ ({i, j} : Set I) := by simp
    have hult : cs.length u < n := by
      have h := hmul j hjmem
      omega
    have hui := ih (cs.length u) hult u rfl i (huasc i himem)
    have huj := ih (cs.length u) hult u rfl j (huasc j hjmem)
    obtain ⟨ω, hJ, hω, hprod⟩ := ParabolicSupport.exists_reduced_word cs ({i,j} : Set I) hv
    have hvi : cs.length (v * cs.simple i) = cs.length v + 1 := by
      have h := hmul i himem
      omega
    have hωi : cs.IsReduced (ω ++ [i]) := by
      change cs.length (cs.wordProd (ω ++ [i])) = (ω ++ [i]).length
      simp only [cs.wordProd_append, cs.wordProd_singleton, hprod, List.length_append,
        List.length_singleton]
      rw [hvi, ← hprod, hω.eq]
    have hJ' : ∀ k ∈ ω, k = i ∨ k = j := by simpa using hJ
    rw [huv, ← hprod]
    exact pair_image_nonneg M cs u hij hui huj hJ' hωi

@[simp] theorem action_simple_root (i : I) : action M cs (cs.simple i) (root i) = -root i := by
  rw [action_simple, normal_root, gram_diag]
  module

/-- Descents carry a simple root into the negative cone. -/
theorem action_root_nonpos_of_descent (w : W) (i : I)
    (hdesc : cs.length (w * cs.simple i) < cs.length w) :
    ∀ k, action M cs w (root i) k ≤ 0 := by
  have hasc : cs.length ((w * cs.simple i) * cs.simple i) = cs.length (w * cs.simple i) + 1 := by
    rcases cs.length_mul_simple w i with h|h
    · omega
    · simpa [mul_assoc] using h.symm
  have h := action_root_nonneg_of_ascent M cs (w * cs.simple i) i hasc
  simpa only [map_mul, LinearEquiv.mul_apply, action_simple_root, map_neg,
    Pi.neg_apply, neg_nonneg] using h

/-- Faithfulness of the actual ordinary Tits action, not an added axiom. -/
theorem action_injective : Function.Injective (action M cs) := by
  apply (MonoidHom.ker_eq_bot_iff _).1
  apply (Subgroup.eq_bot_iff_forall _).2
  intro w hw
  by_contra hne
  obtain ⟨i, hi⟩ := cs.exists_rightDescent_of_ne_one hne
  have h := action_root_nonpos_of_descent M cs w i hi i
  have hw' : action M cs w = 1 := hw
  rw [hw'] at h
  norm_num [root] at h
end
end KLInvariance.TitsSpace

namespace KLInvariance.TitsSpace
open Module
universe u v
variable {I : Type u} [Fintype I] (M : CoxeterMatrix I)
variable {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section

/-- Faithfulness persists in the actual nondegenerate extension. -/
theorem extendedAction_injective : Function.Injective (extendedAction M cs) := by
  intro w z h
  apply action_injective M cs
  ext v i
  have hv := congrArg (fun g : Extended M ≃ₗ[ℝ] Extended M => (g (v, 0)).1 i) h
  simpa only [extendedAction_restrict] using hv

@[simp] theorem extendedForm_root_self (i : I) :
    extendedForm M (extendedRoot M i) (extendedRoot M i) = 2 := by
  rw [extendedForm_roots, M.diagonal]
  norm_num

@[simp] theorem extendedAction_simple_eq (i : I) :
    extendedAction M cs (cs.simple i) = Module.reflection (extendedForm_root_self M i) := by
  apply LinearEquiv.ext
  intro v
  rw [extendedAction_simple, Module.reflection_apply]

end
end KLInvariance.TitsSpace

/-! Coordinate-dual geometric action. This exists in arbitrary rank and is
used only to prove the finite standard-parabolic reduction of the main goal. -/
namespace KLInvariance.Cotangent
open Module
universe u v
variable {I : Type u} (M : CoxeterMatrix I)
noncomputable section

def root (i : I) : I → ℝ := fun j => -2 * Real.cos (Real.pi / M i j)

lemma normal_root (i : I) : (LinearMap.proj i : (I → ℝ) →ₗ[ℝ] ℝ) (root M i) = 2 := by
  simp [root]

def simple (i : I) : (I → ℝ) ≃ₗ[ℝ] (I → ℝ) := Module.reflection (normal_root M i)

theorem simple_liftable : M.IsLiftable (simple M) := by
  intro i j
  by_cases hij : i = j
  · subst j
    rw [M.diagonal, pow_one]
    apply LinearEquiv.ext
    intro v
    exact Module.involutive_reflection (normal_root M i) v
  by_cases hm0 : M i j = 0
  · rw [hm0, pow_zero]
  have hm2 : 2 ≤ M i j := by
    have := M.off_diagonal i j hij
    omega
  apply Realization.geometric_reflection_relation (normal_root M i) (normal_root M j)
    (M i j) hm2
  · simp [root, M.symmetric j i]
  · rfl

def action {W : Type v} [Group W] (cs : CoxeterSystem M W) :
    W →* ((I → ℝ) ≃ₗ[ℝ] (I → ℝ)) := cs.lift ⟨simple M, simple_liftable M⟩

@[simp] theorem action_simple {W : Type v} [Group W] (cs : CoxeterSystem M W)
    (i : I) (l : I → ℝ) :
    action M cs (cs.simple i) l = l - l i • root M i := by
  rw [action, cs.lift_apply_simple]
  rfl

section Finite
variable [Fintype I] {W : Type v} [Group W] (cs : CoxeterSystem M W)

lemma dot_root (l : I → ℝ) (i : I) : l ⬝ᵥ TitsSpace.root i = l i := by
  classical
  simp [TitsSpace.root, dotProduct, Pi.single_apply]

lemma root_dot (i : I) (v : I → ℝ) :
    root M i ⬝ᵥ v = TitsSpace.normal M i v := by
  simp [root, TitsSpace.normal, TitsSpace.gram, dotProduct]

lemma simple_pairing (i : I) (l v : I → ℝ) :
    (action M cs (cs.simple i) l) ⬝ᵥ (TitsSpace.action M cs (cs.simple i) v) =
      l ⬝ᵥ v := by
  rw [action_simple, TitsSpace.action_simple]
  simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul,
    dot_root, root_dot]
  have hd : root M i i = 2 := by simp [root]
  rw [hd]
  simp only [smul_eq_mul]
  ring

theorem pairing (w : W) (l v : I → ℝ) :
    (action M cs w l) ⬝ᵥ (TitsSpace.action M cs w v) = l ⬝ᵥ v := by
  obtain ⟨ω, rfl⟩ := cs.wordProd_surjective w
  induction ω generalizing l v with
  | nil => simp
  | cons i ω ih =>
    rw [cs.wordProd_cons, map_mul, map_mul, LinearEquiv.mul_apply,
      LinearEquiv.mul_apply, simple_pairing, ih]

theorem action_injective : Function.Injective (action M cs) := by
  apply (injective_iff_map_eq_one _).2
  intro w hw
  apply TitsSpace.action_injective M cs
  rw [map_one]
  apply LinearEquiv.ext
  intro v
  apply dotProduct_eq
  intro l
  have h := pairing M cs w l v
  rw [hw] at h
  simpa [dotProduct_comm] using h
end Finite
end
end KLInvariance.Cotangent

namespace KLInvariance.StandardParabolic
open CoxeterSystem
universe u v
variable {I : Type u} {W : Type v} [Group W] {M : CoxeterMatrix I}
variable (cs : CoxeterSystem M W) (J : Set I)
noncomputable section

def matrix : CoxeterMatrix J where
  M i j := M i.val j.val
  isSymm := M.isSymm.submatrix Subtype.val
  diagonal i := M.diagonal i.val
  off_diagonal i j h := M.off_diagonal i.val j.val (fun h' => h (Subtype.ext h'))

abbrev system : CoxeterSystem (matrix (M := M) J) (matrix (M := M) J).Group :=
  (matrix (M := M) J).toCoxeterSystem

def inclusion : (matrix (M := M) J).Group →* W :=
  (system (M := M) J).lift ⟨fun i => cs.simple i.val,
    fun i j => cs.simple_mul_simple_pow i.val j.val⟩

@[simp] theorem inclusion_simple (i : J) :
    inclusion cs J ((system (M := M) J).simple i) = cs.simple i.val :=
  (system (M := M) J).lift_apply_simple _ i

lemma inclusion_word (ω : List J) :
    inclusion cs J ((system (M := M) J).wordProd ω) = cs.wordProd (ω.map Subtype.val) := by
  induction ω with
  | nil => simp
  | cons i ω ih =>
    rw [wordProd_cons, map_mul, inclusion_simple, List.map_cons, wordProd_cons, ih]

def restrictVec (l : I → ℝ) : J → ℝ := fun j => l j.val

lemma simple_restrict (i : J) (l : I → ℝ) :
    restrictVec J (Cotangent.action M cs (cs.simple i.val) l) =
      Cotangent.action (matrix (M := M) J) (system (M := M) J)
        ((system (M := M) J).simple i) (restrictVec J l) := by
  rw [Cotangent.action_simple, Cotangent.action_simple]
  funext j
  rfl

theorem action_restrict (w : (matrix (M := M) J).Group) (l : I → ℝ) :
    restrictVec J (Cotangent.action M cs (inclusion cs J w) l) =
      Cotangent.action (matrix (M := M) J) (system (M := M) J) w (restrictVec J l) := by
  obtain ⟨ω, rfl⟩ := (system (M := M) J).wordProd_surjective w
  induction ω generalizing l with
  | nil => simp
  | cons i ω ih =>
    rw [wordProd_cons, map_mul, inclusion_simple, map_mul, map_mul,
      LinearEquiv.mul_apply, LinearEquiv.mul_apply, simple_restrict, ih]

theorem inclusion_injective [Fintype J] : Function.Injective (inclusion cs J) := by
  classical
  apply (injective_iff_map_eq_one _).2
  intro w hw
  apply Cotangent.action_injective (matrix (M := M) J) (system (M := M) J)
  rw [map_one]
  apply LinearEquiv.ext
  intro l
  let l' : I → ℝ := fun i => if hi : i ∈ J then l ⟨i, hi⟩ else 0
  have hr : restrictVec J l' = l := by ext j; simp [restrictVec, l', j.property]
  have h := action_restrict cs J w l'
  rw [hw, map_one] at h
  change restrictVec J l' = _ at h
  rw [hr] at h
  exact h.symm

lemma lift_word {ω : List I} (hω : ∀ i ∈ ω, i ∈ J) :
    ∃ ν : List J, ν.map Subtype.val = ω := by
  induction ω with
  | nil => exact ⟨[], rfl⟩
  | cons i ω ih =>
    obtain ⟨ν, rfl⟩ := ih (fun j hj => hω j (by simp [hj]))
    exact ⟨⟨i, hω i (by simp)⟩ :: ν, rfl⟩

theorem inclusion_mem (w : (matrix (M := M) J).Group) :
    inclusion cs J w ∈ ParabolicSupport.subgroup cs J := by
  obtain ⟨ω, rfl⟩ := (system (M := M) J).wordProd_surjective w
  rw [inclusion_word]
  apply ParabolicSupport.word_mem
  intro i hi
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp hi
  exact j.property

theorem length_inclusion [Fintype J] (w : (matrix (M := M) J).Group) :
    cs.length (inclusion cs J w) = (system (M := M) J).length w := by
  apply le_antisymm
  · obtain ⟨ω, hω, rfl⟩ := (system (M := M) J).exists_isReduced w
    rw [inclusion_word, hω.eq]
    simpa using cs.length_wordProd_le (ω.map Subtype.val)
  · obtain ⟨ω, hω, hred, hprod⟩ := ParabolicSupport.exists_reduced_word cs J
      (inclusion_mem cs J w)
    obtain ⟨ν, rfl⟩ := lift_word J hω
    have heq : (system (M := M) J).wordProd ν = w :=
      inclusion_injective cs J ((inclusion_word cs J ν).trans hprod)
    have hb := (system (M := M) J).length_wordProd_le ν
    rw [heq] at hb
    have hr := hred.eq
    rw [hprod, List.length_map] at hr
    omega

lemma reduced_map_iff [Fintype J] (ω : List J) :
    cs.IsReduced (ω.map Subtype.val) ↔ (system (M := M) J).IsReduced ω := by
  simp only [CoxeterSystem.IsReduced, List.length_map, ← inclusion_word, length_inclusion]

end
end KLInvariance.StandardParabolic

namespace KLInvariance.StandardParabolic
open CoxeterSystem
universe u v
variable {I : Type u} {W : Type v} [Group W] {M : CoxeterMatrix I}
variable (cs : CoxeterSystem M W) (J : Set I) [Fintype J]
noncomputable section

theorem bruhat_inclusion_iff (x y : (matrix (M := M) J).Group) :
    BruhatLE cs (inclusion cs J x) (inclusion cs J y) ↔
      BruhatLE (system (M := M) J) x y := by
  obtain ⟨ω, hω, rfl⟩ := (system (M := M) J).exists_isReduced y
  rw [inclusion_word]
  constructor
  · intro h
    obtain ⟨ν, hsub, _, hprod⟩ := (bruhat_iff_reduced_subword cs
      ((reduced_map_iff cs J ω).2 hω)).1 h
    obtain ⟨τ, hτ, rfl⟩ := List.sublist_map_iff.mp hsub
    have hx : (system (M := M) J).wordProd τ = x :=
      inclusion_injective cs J ((inclusion_word cs J τ).trans hprod)
    rw [← hx]
    exact bruhat_of_subword _ hτ hω
  · intro h
    obtain ⟨ν, hsub, _, rfl⟩ := (bruhat_iff_reduced_subword _ hω).1 h
    rw [inclusion_word]
    exact bruhat_of_subword cs (hsub.map Subtype.val) ((reduced_map_iff cs J ω).2 hω)

theorem lower_range (y : (matrix (M := M) J).Group) {z : W}
    (hzy : BruhatLE cs z (inclusion cs J y)) :
    ∃ x, inclusion cs J x = z := by
  obtain ⟨ω, hω, rfl⟩ := (system (M := M) J).exists_isReduced y
  rw [inclusion_word] at hzy
  obtain ⟨ν, hsub, _, hprod⟩ := (bruhat_iff_reduced_subword cs
    ((reduced_map_iff cs J ω).2 hω)).1 hzy
  obtain ⟨τ, _, rfl⟩ := List.sublist_map_iff.mp hsub
  exact ⟨(system (M := M) J).wordProd τ, (inclusion_word cs J τ).trans hprod⟩

def intervalMap (x y : (matrix (M := M) J).Group) :
    Interval (system (M := M) J) x y →
      Interval cs (inclusion cs J x) (inclusion cs J y) :=
  fun z => ⟨inclusion cs J z.val, (bruhat_inclusion_iff cs J x z.val).2 z.property.1,
    (bruhat_inclusion_iff cs J z.val y).2 z.property.2⟩

lemma intervalMap_bijective (x y : (matrix (M := M) J).Group) :
    Function.Bijective (intervalMap cs J x y) := by
  constructor
  · intro z t h
    exact Subtype.ext (inclusion_injective cs J (congrArg Subtype.val h))
  · intro z
    obtain ⟨w, hw⟩ := lower_range cs J y z.property.2
    refine ⟨⟨w, ?_, ?_⟩, Subtype.ext hw⟩
    · apply (bruhat_inclusion_iff cs J x w).1
      rw [hw]
      exact z.property.1
    · apply (bruhat_inclusion_iff cs J w y).1
      rw [hw]
      exact z.property.2

/-- The exact unlabelled interval identification used in the finite-rank
reduction; it arises from a proved embedding, not an added main hypothesis. -/
def intervalIso (x y : (matrix (M := M) J).Group) :
    Interval (system (M := M) J) x y ≃o
      Interval cs (inclusion cs J x) (inclusion cs J y) where
  toEquiv := Equiv.ofBijective _ (intervalMap_bijective cs J x y)
  map_rel_iff' := by
    intro z t
    exact bruhat_inclusion_iff cs J z.val t.val

@[simp] theorem intervalIso_val (x y : (matrix (M := M) J).Group)
    (z : Interval (system (M := M) J) x y) :
    (intervalIso cs J x y z).val = inclusion cs J z.val := rfl

end
end KLInvariance.StandardParabolic

namespace KLInvariance.TitsSpace
open Module
universe u v
variable {I : Type u} [Fintype I] (M : CoxeterMatrix I)
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section

/-- A genuine real root, obtained from a simple root by the Tits action. -/
def IsRoot (a : I → ℝ) : Prop := ∃ w : W, ∃ i : I, a = action M cs w (root i)

/-- A normalized real root representing a genuine Coxeter reflection. -/
def Represents (t : W) (a : I → ℝ) : Prop :=
  ∃ w : W, ∃ i : I, t = w * cs.simple i * w⁻¹ ∧ a = action M cs w (root i)

abbrev embed (a : I → ℝ) : Extended M := (a, 0)

@[simp] theorem form_root_self (i : I) : form M (root i) (root i) = 2 := by
  simp []

variable {M cs}

theorem IsRoot.norm {a : I → ℝ} (ha : IsRoot M cs a) : form M a a = 2 := by
  obtain ⟨w,i,rfl⟩ := ha
  rw [action_preserves, form_root_self]

theorem IsRoot.ne_zero {a : I → ℝ} (ha : IsRoot M cs a) : a ≠ 0 := by
  intro he
  have hn := ha.norm
  simp [he] at hn

theorem IsRoot.sign {a : I → ℝ} (ha : IsRoot M cs a) :
    (∀ i, 0 ≤ a i) ∨ (∀ i, a i ≤ 0) := by
  obtain ⟨w,i,rfl⟩ := ha
  rcases lt_or_gt_of_ne (cs.length_mul_simple_ne w i) with h|h
  · exact Or.inr (action_root_nonpos_of_descent M cs w i h)
  · exact Or.inl (action_root_nonneg_of_ascent M cs w i (by
      rcases cs.length_mul_simple w i with h'|h' <;> omega))

theorem IsRoot.act {a : I → ℝ} (ha : IsRoot M cs a) (w : W) :
    IsRoot M cs (action M cs w a) := by
  obtain ⟨z,i,rfl⟩ := ha
  exact ⟨w*z, i, by simp only [map_mul, LinearEquiv.mul_apply]⟩

theorem Represents.isRoot {t : W} {a : I → ℝ} (ha : Represents M cs t a) :
    IsRoot M cs a := by
  obtain ⟨w,i,_,h⟩ := ha
  exact ⟨w,i,h⟩

theorem Represents.isReflection {t : W} {a : I → ℝ} (ha : Represents M cs t a) :
    cs.IsReflection t := by
  obtain ⟨w,i,h,_⟩ := ha
  exact ⟨w,i,h⟩

theorem Represents.neg {t : W} {a : I → ℝ} (ha : Represents M cs t a) :
    Represents M cs t (-a) := by
  obtain ⟨w,i,rfl,rfl⟩ := ha
  refine ⟨w * cs.simple i, i, ?_, ?_⟩
  · simp [mul_assoc]
  · simp only [map_mul, LinearEquiv.mul_apply, action_simple_root, map_neg]

theorem Represents.act {t : W} {a : I → ℝ} (ha : Represents M cs t a) (w : W) :
    Represents M cs (w*t*w⁻¹) (action M cs w a) := by
  obtain ⟨z,i,rfl,rfl⟩ := ha
  refine ⟨w*z,i,?_,?_⟩
  · group
  · simp only [map_mul, LinearEquiv.mul_apply]

/-- The actual reflection formula for every conjugate root in the minimal
nondegenerate extension, not merely for simple roots. -/
theorem Represents.formula {t : W} {a : I → ℝ} (ha : Represents M cs t a)
    (v : Extended M) :
    extendedAction M cs t v = v - extendedForm M (embed M a) v • embed M a := by
  obtain ⟨w,i,rfl,rfl⟩ := ha
  have hv : extendedAction M cs w (extendedAction M cs w⁻¹ v) = v := by
    rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    rfl
  have hp := extendedAction_preserves M cs w (extendedRoot M i)
    (extendedAction M cs w⁻¹ v)
  rw [hv] at hp
  rw [map_mul, map_mul]
  simp only [LinearEquiv.mul_apply, extendedAction_simple, map_sub, map_smul]
  rw [hv, ← hp, extendedRoot, extendedAction_restrict]

theorem Represents.action_formula {t : W} {a : I → ℝ} (ha : Represents M cs t a)
    (v : I → ℝ) : action M cs t v = v - form M a v • a := by
  have h := congrArg Prod.fst (ha.formula (embed M v))
  simpa only [extendedAction_restrict, embed, (extendedForm_spec M).2.2,
    Prod.fst_sub, Prod.smul_fst] using h

theorem Represents.unique_up_to_sign {t : W} {a b : I → ℝ}
    (ha : Represents M cs t a) (hb : Represents M cs t b) : a = b ∨ a = -b := by
  have hn := ha.isRoot.norm
  have hm := hb.isRoot.norm
  have hf := ha.action_formula a
  rw [hb.action_formula a, hn] at hf
  have hmul : form M b a • b = (2 : ℝ) • a := by
    have h := congrArg (fun z => a-z) hf
    simpa only [sub_sub_cancel] using h
  have hab : a = (form M b a / 2) • b := by
    calc
      a = (1/2 : ℝ) • ((2 : ℝ) • a) := by module
      _ = (1/2 : ℝ) • (form M b a • b) := by rw [hmul]
      _ = _ := by module
  have hc : (form M b a / 2) ^ 2 = 1 := by
    rw [hab] at hn
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, hm] at hn
    nlinarith
  rcases sq_eq_one_iff.mp hc with h|h
  · exact Or.inl (by simpa [h] using hab)
  · exact Or.inr (by simpa [h] using hab)

theorem Represents.reflection_unique {t s : W} {a : I → ℝ}
    (ha : Represents M cs t a) (hb : Represents M cs s a) : t = s := by
  apply extendedAction_injective M cs
  apply LinearEquiv.ext
  intro v
  rw [ha.formula, hb.formula]

theorem Represents.unique_positive {t : W} {a b : I → ℝ}
    (ha : Represents M cs t a) (hb : Represents M cs t b)
    (hpa : ∀ i, 0 ≤ a i) (hpb : ∀ i, 0 ≤ b i) : a = b := by
  rcases ha.unique_up_to_sign hb with h|h
  · exact h
  · exfalso
    apply ha.isRoot.ne_zero
    ext i
    have hi := congrFun h i
    simp only [Pi.neg_apply] at hi
    have := hpa i
    have := hpb i
    simp only [Pi.zero_apply]
    linarith

variable (M) (cs)

theorem exists_positive_root {t : W} (ht : cs.IsReflection t) :
    ∃ a : I → ℝ, Represents M cs t a ∧ ∀ i, 0 ≤ a i := by
  obtain ⟨w,i,rfl⟩ := ht
  have hr : Represents M cs (w * cs.simple i * w⁻¹) (action M cs w (root i)) :=
    ⟨w,i,rfl,rfl⟩
  rcases hr.isRoot.sign with h|h
  · exact ⟨_,hr,h⟩
  · exact ⟨_,hr.neg,fun i => by simpa only [Pi.neg_apply, neg_nonneg] using h i⟩

/-- Genuine positive roots, with their actual coordinate sign. -/
def PositiveRoot := {a : I → ℝ // IsRoot M cs a ∧ ∀ i, 0 ≤ a i}

def positiveRoot (t : {t : W // cs.IsReflection t}) : PositiveRoot M cs :=
  ⟨(exists_positive_root M cs t.property).choose,
    (exists_positive_root M cs t.property).choose_spec.1.isRoot,
    (exists_positive_root M cs t.property).choose_spec.2⟩

theorem positiveRoot_represents (t : {t : W // cs.IsReflection t}) :
    Represents M cs t.val (positiveRoot M cs t).val :=
  (exists_positive_root M cs t.property).choose_spec.1

def rootReflection (a : PositiveRoot M cs) : {t : W // cs.IsReflection t} := by
  let w := a.property.1.choose
  let i := a.property.1.choose_spec.choose
  exact ⟨w * cs.simple i * w⁻¹, w,i,rfl⟩

theorem rootReflection_represents (a : PositiveRoot M cs) :
    Represents M cs (rootReflection M cs a).val a.val := by
  refine ⟨a.property.1.choose, a.property.1.choose_spec.choose, rfl, ?_⟩
  exact a.property.1.choose_spec.choose_spec


def positiveRootEquiv : {t : W // cs.IsReflection t} ≃ PositiveRoot M cs where
  toFun := positiveRoot M cs
  invFun := rootReflection M cs
  left_inv t := Subtype.ext ((rootReflection_represents M cs _).reflection_unique
      (positiveRoot_represents M cs t))
  right_inv a := Subtype.ext ((positiveRoot_represents M cs _).unique_positive
      (rootReflection_represents M cs a) (positiveRoot M cs _).property.2 a.property.2)

end
end KLInvariance.TitsSpace

namespace KLInvariance.TitsSpace
open Module
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
noncomputable section

theorem IsRoot.not_both {a : I → ℝ} (ha : IsRoot M cs a)
    (hp : ∀ i, 0 ≤ a i) (hn : ∀ i, a i ≤ 0) : False := by
  apply ha.ne_zero
  ext i
  exact le_antisymm (hn i) (hp i)

/-- A simple reflection can turn a positive real root negative only on its
own root. This uses actual Tits coordinates and normalization. -/
theorem IsRoot.eq_simple_of_nonpos {a : I → ℝ} (ha : IsRoot M cs a)
    (hp : ∀ k, 0 ≤ a k) (i : I)
    (hn : ∀ k, action M cs (cs.simple i) a k ≤ 0) : a = root i := by
  classical
  have ha0 (k : I) (hk : k ≠ i) : a k = 0 := by
    have h := hn k
    simp only [action_simple, Pi.sub_apply, Pi.smul_apply, root,
      Pi.single_apply, hk, ↓reduceIte, smul_eq_mul, mul_zero, sub_zero] at h
    exact le_antisymm h (hp k)
  have heq : a = a i • root i := by
    ext k
    by_cases hki : k = i
    · subst k; simp [root]
    · simp [root, hki, ha0 k hki]
  have hnorm := ha.norm
  rw [heq] at hnorm
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, form_root_self] at hnorm
  have hai : a i = 1 := by nlinarith [hp i]
  simpa only [hai, one_smul] using heq

theorem Represents.simple_sign {t : W} {a : I → ℝ} (ha : Represents M cs t a)
    (hp : ∀ k, 0 ≤ a k) (i : I) :
    ((∀ k, action M cs (cs.simple i) a k ≤ 0) ↔ t = cs.simple i) ∧
    ((∀ k, 0 ≤ action M cs (cs.simple i) a k) ↔ t ≠ cs.simple i) := by
  have hi : Represents M cs (cs.simple i) (root i) := ⟨1,i,by simp,by simp⟩
  have hneg : (∀ k, action M cs (cs.simple i) a k ≤ 0) ↔ t = cs.simple i := by
    constructor
    · intro h
      have heq := ha.isRoot.eq_simple_of_nonpos hp i h
      exact ha.reflection_unique (heq.symm ▸ hi)
    · intro h
      have heq := (h ▸ ha).unique_positive hi hp (root_nonneg i)
      simpa only [heq, action_simple_root, Pi.neg_apply, neg_nonpos] using root_nonneg i
  refine ⟨hneg, ?_⟩
  constructor
  · intro h heq
    exact (ha.isRoot.act (cs.simple i)).not_both h (hneg.mpr heq)
  · intro h
    rcases (ha.isRoot.act (cs.simple i)).sign with hp|hn
    · exact hp
    · exact False.elim (h (hneg.mp hn))

/-- The signed combinatorial reflection action is the actual root sign
under the faithful Tits representation. -/
def SignedRepresents (p : W × ZMod 2) (a : I → ℝ) : Prop :=
  Represents M cs p.1 a ∧
    ((p.2 = 0 ∧ ∀ i, 0 ≤ a i) ∨ (p.2 = 1 ∧ ∀ i, a i ≤ 0))

theorem SignedRepresents.simple {p : W × ZMod 2} {a : I → ℝ}
    (ha : SignedRepresents (M := M) (cs := cs) p a) (i : I) :
    SignedRepresents (M := M) (cs := cs) (CoxeterSupport.simpleAction cs i p)
      (action M cs (cs.simple i) a) := by
  rcases p with ⟨t,z⟩
  rw [CoxeterSupport.simpleAction_apply]
  refine ⟨?_,?_⟩
  · simpa only [cs.inv_simple] using ha.1.act (cs.simple i)
  · rcases ha.2 with ⟨rfl,hp⟩|⟨rfl,hn⟩
    · by_cases heq : t = cs.simple i
      · exact Or.inr ⟨by simp [heq], (ha.1.simple_sign hp i).1.mpr heq⟩
      · exact Or.inl ⟨by simp [heq, ZModModule.add_self], (ha.1.simple_sign hp i).2.mpr heq⟩
    · have hp : ∀ k, 0 ≤ (-a) k := fun k => neg_nonneg.mpr (hn k)
      by_cases heq : t = cs.simple i
      · refine Or.inl ⟨by simp [heq, ZModModule.add_self], ?_⟩
        have h := (ha.1.neg.simple_sign hp i).1.mpr heq
        simpa only [map_neg, Pi.neg_apply, neg_nonpos] using h
      · refine Or.inr ⟨by simp [heq], ?_⟩
        have h := (ha.1.neg.simple_sign hp i).2.mpr heq
        simpa only [map_neg, Pi.neg_apply, neg_nonneg] using h

theorem SignedRepresents.act {p : W × ZMod 2} {a : I → ℝ}
    (ha : SignedRepresents (M := M) (cs := cs) p a) (w : W) :
    SignedRepresents (M := M) (cs := cs) (CoxeterSupport.reflectionAction cs w p)
      (action M cs w a) := by
  obtain ⟨ω,rfl⟩ := cs.wordProd_surjective w
  induction ω with
  | nil => simpa using ha
  | cons i ω ih =>
    simpa only [cs.wordProd_cons, map_mul, Equiv.Perm.mul_apply,
      CoxeterSupport.reflectionAction_simple, LinearEquiv.mul_apply] using ih.simple i


theorem Represents.inversion_iff {t : W} {a : I → ℝ} (ha : Represents M cs t a)
    (hp : ∀ i, 0 ≤ a i) (w : W) :
    (∀ i, action M cs w⁻¹ a i ≤ 0) ↔ cs.IsLeftInversion w t := by
  classical
  obtain ⟨ω,hω,heq⟩ := cs.exists_isReduced w
  rw [heq]
  let c : ZMod 2 := (cs.leftInvSeq ω).count t
  have hc : c+c=0 := ZModModule.add_self c
  have hrec := CoxeterSupport.wordAction_record cs ω t c
  rw [← CoxeterSupport.reflectionAction_wordProd] at hrec
  have hrec' : CoxeterSupport.reflectionAction cs (cs.wordProd ω)
      ((cs.wordProd ω)⁻¹ * t * cs.wordProd ω, c) = (t,0) := by
    change CoxeterSupport.reflectionAction cs (cs.wordProd ω)
      ((cs.wordProd ω)⁻¹ * t * cs.wordProd ω,c) = (t,c+c) at hrec
    rwa [hc] at hrec
  have hinv : CoxeterSupport.reflectionAction cs (cs.wordProd ω)⁻¹ (t,0) =
      ((cs.wordProd ω)⁻¹ * t * cs.wordProd ω,c) := by
    rw [map_inv, ← hrec']
    exact Equiv.symm_apply_apply _ _
  have hs : SignedRepresents (M := M) (cs := cs) (t,0) a := ⟨ha,Or.inl ⟨rfl,hp⟩⟩
  have hsi := hs.act (cs.wordProd ω)⁻¹
  rw [hinv] at hsi
  have hcount : c = if t ∈ cs.leftInvSeq ω then 1 else 0 := by
    dsimp [c]
    by_cases hm : t ∈ cs.leftInvSeq ω
    · rw [ite_eq_left hm, List.count_eq_one_of_mem hω.nodup_leftInvSeq hm]
      norm_num
    · rw [ite_eq_right hm, List.count_eq_zero.mpr hm]
      rfl
  have hmem : (∀ i, action M cs (cs.wordProd ω)⁻¹ a i ≤ 0) ↔ t ∈ cs.leftInvSeq ω := by
    by_cases hm : t ∈ cs.leftInvSeq ω
    · have hc1 : c=1 := by simpa [hm] using hcount
      simp only [hc1] at hsi
      rcases hsi.2 with ⟨hbad,_⟩|⟨_,hn⟩
      · norm_num at hbad
      · exact iff_of_true hn hm
    · have hc0 : c=0 := by simpa [hm] using hcount
      simp only [hc0] at hsi
      rcases hsi.2 with ⟨_,hpos⟩|⟨hbad,_⟩
      · exact iff_of_false (fun hn => (ha.isRoot.act _).not_both hpos hn) hm
      · norm_num at hbad
  rw [hmem]
  exact ⟨cs.isLeftInversion_of_mem_leftInvSeq hω,
    CoxeterSupport.mem_leftInvSeq_of_inversion cs hω⟩

end
end KLInvariance.TitsSpace

namespace KLInvariance.TitsSpace
open Module
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
noncomputable section

theorem Represents.independent_of_ne {t s : W} {a b : I → ℝ}
    (ha : Represents M cs t a) (hb : Represents M cs s b) (hts : t ≠ s) :
    LinearIndependent ℝ ![a,b] := by
  apply (LinearIndependent.pair_iff' ha.isRoot.ne_zero).mpr
  intro c heq
  have hn := hb.isRoot.norm
  rw [← heq] at hn
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, ha.isRoot.norm] at hn
  have hc : c^2 = 1 := by nlinarith
  rcases sq_eq_one_iff.mp hc with hc|hc
  · have hab : a=b := by simpa only [hc,one_smul] using heq
    exact hts (ha.reflection_unique (hab.symm ▸ hb))
  · have hab : -a=b := by simpa only [hc,neg_one_smul] using heq
    exact hts (ha.neg.reflection_unique (hab.symm ▸ hb))

variable (M) (cs)
/-- The actual positive ambient roots inverted by `w`. -/
def RootInversions (w : W) :=
  {a : PositiveRoot M cs // ∀ i, action M cs w⁻¹ a.val i ≤ 0}

def rootInversionEquiv (w : W) : RootInversions M cs w ≃ {t : W // cs.IsLeftInversion w t} where
  toFun a := ⟨(rootReflection M cs a.val).val,
    ((rootReflection_represents M cs a.val).inversion_iff a.val.property.2 w).mp a.property⟩
  invFun t := ⟨positiveRoot M cs ⟨t.val,t.property.1⟩,
    ((positiveRoot_represents M cs ⟨t.val,t.property.1⟩).inversion_iff
      (positiveRoot M cs ⟨t.val,t.property.1⟩).property.2 w).mpr t.property⟩
  left_inv a := by
    apply Subtype.ext
    exact (positiveRootEquiv M cs).apply_symm_apply a.val
  right_inv t := by
    apply Subtype.ext
    change (rootReflection M cs (positiveRoot M cs ⟨t.val,t.property.1⟩)).val = t.val
    exact congrArg (fun r : {r : W // cs.IsReflection r} => r.val)
      ((positiveRootEquiv M cs).symm_apply_apply ⟨t.val,t.property.1⟩)

def leftInversionListEquiv {ω : List I} (hω : cs.IsReduced ω) :
    {t : W // cs.IsLeftInversion (cs.wordProd ω) t} ≃ {t : W // t ∈ cs.leftInvSeq ω} where
  toFun t := ⟨t.val,CoxeterSupport.mem_leftInvSeq_of_inversion cs hω t.property⟩
  invFun t := ⟨t.val,cs.isLeftInversion_of_mem_leftInvSeq hω t.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Full ambient inversion count, not a cardinality assumption. -/
theorem rootInversions_finite (w : W) : Finite (RootInversions M cs w) := by
  classical
  obtain ⟨ω,hω,heq⟩ := cs.exists_isReduced w
  rw [heq]
  exact Finite.of_equiv (Fin (cs.leftInvSeq ω).length)
    ((List.Nodup.getEquiv (cs.leftInvSeq ω) hω.nodup_leftInvSeq).trans
      ((leftInversionListEquiv M cs hω).symm.trans (rootInversionEquiv M cs _).symm))

end
end KLInvariance.TitsSpace

namespace KLInvariance.TitsSpace
open Module
universe u v
variable {I : Type u} [Fintype I] (M : CoxeterMatrix I)
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section

/-- Elements whose actual linear displacement lies in `P`. This is a
subgroup even when the invariant bilinear form restricted to `P` is singular. -/
def movingSubgroup (P : Submodule ℝ (I → ℝ)) : Subgroup W where
  carrier := {w | ∀ v, action M cs w v - v ∈ P}
  one_mem' := by intro v; simp
  mul_mem' := by
    intro w z hw hz v
    have h := P.add_mem (hw (action M cs z v)) (hz v)
    simpa only [map_mul, LinearEquiv.mul_apply, sub_add_sub_cancel] using h
  inv_mem' := by
    intro w hw v
    have h := P.neg_mem (hw (action M cs w⁻¹ v))
    have hv : action M cs w (action M cs w⁻¹ v) = v := by
      rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one]
      rfl
    simpa only [hv, neg_sub] using h

/-- The manuscript's maximal plane reflection subgroup, defined using
actual normalized roots, not by assuming a rank-two presentation. -/
def planeSubgroup (P : Submodule ℝ (I → ℝ)) : Subgroup W :=
  Subgroup.closure {t | ∃ a, Represents M cs t a ∧ a ∈ P}

theorem planeSubgroup_le_moving (P : Submodule ℝ (I → ℝ)) :
    planeSubgroup M cs P ≤ movingSubgroup M cs P := by
  apply (Subgroup.closure_le (movingSubgroup M cs P)).mpr
  rintro t ⟨a,ha,haP⟩ v
  rw [ha.action_formula]
  have heq : v - form M a v • a - v = (-form M a v) • a := by module
  rw [heq]
  exact P.smul_mem _ haP

theorem Represents.mem_of_moving {P : Submodule ℝ (I → ℝ)} {t : W} {a : I → ℝ}
    (ha : Represents M cs t a) (ht : t ∈ movingSubgroup M cs P) : a ∈ P := by
  have h := ht a
  change action M cs t a - a ∈ P at h
  rw [ha.action_formula,ha.isRoot.norm] at h
  have heq : a - (2 : ℝ) • a - a = (-2 : ℝ) • a := by module
  rw [heq] at h
  have h' := P.smul_mem (-1/2 : ℝ) h
  have heq' : (-1/2 : ℝ) • ((-2 : ℝ) • a) = a := by module
  rwa [heq'] at h'


theorem Represents.planeSubgroup_mem_iff {P : Submodule ℝ (I → ℝ)} {t : W} {a : I → ℝ}
    (ha : Represents M cs t a) : t ∈ planeSubgroup M cs P ↔ a ∈ P := by
  constructor
  · intro ht
    exact Represents.mem_of_moving M cs ha (planeSubgroup_le_moving M cs P ht)
  · intro haP
    exact Subgroup.subset_closure ⟨a,ha,haP⟩

end
end KLInvariance.TitsSpace

namespace KLInvariance.TitsSpace
open Module
universe u v
variable {I : Type u} [Fintype I] (M : CoxeterMatrix I)
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section

variable {M cs}

theorem planeSubgroup_preserves {P : Submodule ℝ (I → ℝ)} {g : W}
    (hg : g ∈ planeSubgroup M cs P) {a : I → ℝ} (ha : a ∈ P) :
    action M cs g a ∈ P := by
  have h := (planeSubgroup_le_moving M cs P hg) a
  simpa only [sub_add_cancel] using P.add_mem h ha

end
end KLInvariance.TitsSpace

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

namespace KLInvariance.ReflectionSchedules
open Polynomial
universe u v
variable {I : Type u} [Fintype I]
noncomputable section

def coordinatePolynomial (a : I → ℝ) : ℝ[X] :=
  ∑ i, Polynomial.monomial (Fintype.equivFin I i).val (a i)

theorem coordinatePolynomial_coeff (a : I → ℝ) (j : I) :
    (coordinatePolynomial a).coeff (Fintype.equivFin I j).val = a j := by
  classical
  rw [coordinatePolynomial, Polynomial.finsetSum_coeff, Finset.sum_eq_single j]
  · simp
  · intro i _ hij
    have hne : (Fintype.equivFin I i).val ≠ (Fintype.equivFin I j).val := by
      intro h
      exact hij ((Fintype.equivFin I).injective (Fin.ext h))
    simp [Polynomial.coeff_monomial,hne]
  · simp

theorem coordinatePolynomial_injective : Function.Injective (coordinatePolynomial (I := I)) := by
  intro a b h
  funext i
  simpa only [coordinatePolynomial_coeff] using congrArg (fun p : ℝ[X] => p.coeff
    (Fintype.equivFin I i).val) h

def momentFunctional (t : ℝ) : Module.Dual ℝ (I → ℝ) where
  toFun a := ∑ i, a i * t^(Fintype.equivFin I i).val
  map_add' a b := by simp [add_mul,Finset.sum_add_distrib]
  map_smul' r a := by simp [Finset.mul_sum,mul_assoc]

theorem coordinatePolynomial_eval (a : I → ℝ) (t : ℝ) :
    (coordinatePolynomial a).eval t = momentFunctional t a := by
  simp [coordinatePolynomial,momentFunctional,Polynomial.eval_finsetSum]


theorem exists_generic_functional {A : Type v} [Countable A]
    (v : A → (I → ℝ)) (hv : Function.Injective v) :
    ∃ f : Module.Dual ℝ (I → ℝ), Function.Injective (fun a => f (v a)) := by
  classical
  let P := {p : A × A // p.1 ≠ p.2}
  let d : P → ℝ[X] := fun p => coordinatePolynomial (v p.val.1) - coordinatePolynomial (v p.val.2)
  have hd : ∀ p, d p ≠ 0 := by
    intro p h
    exact p.property (hv (coordinatePolynomial_injective (sub_eq_zero.mp h)))
  let bad : Set ℝ := ⋃ p : P, {t | (d p).IsRoot t}
  have hbad : bad.Countable := Set.countable_iUnion (fun p => (Polynomial.finite_setOfPred_isRoot (hd p)).countable)
  have hex : ∃ t, t ∉ bad := by
    by_contra h
    push Not at h
    have heq : bad = Set.univ := Set.eq_univ_of_forall h
    rw [heq] at hbad
    exact Set.not_countable_univ hbad
  obtain ⟨t,ht⟩ := hex
  refine ⟨momentFunctional t,fun a b hab => ?_⟩
  change momentFunctional t (v a) = momentFunctional t (v b) at hab
  by_contra hne
  apply ht
  apply Set.mem_iUnion.mpr
  refine ⟨⟨(a,b),hne⟩,?_⟩
  change (coordinatePolynomial (v a) - coordinatePolynomial (v b)).eval t = 0
  rw [Polynomial.eval_sub,coordinatePolynomial_eval,coordinatePolynomial_eval,hab,sub_self]

end
end KLInvariance.ReflectionSchedules

namespace KLInvariance.TitsSpace
open Module
universe u v
variable {I : Type u} [Fintype I] (M : CoxeterMatrix I)
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section

def height : Module.Dual ℝ (I → ℝ) where
  toFun a := ∑ i, a i
  map_add' a b := by simp [Finset.sum_add_distrib]
  map_smul' r a := by simp [Finset.mul_sum]

variable {M cs}

theorem PositiveRoot.height_pos (a : PositiveRoot M cs) : 0 < height a.val := by
  classical
  have hex : ∃ i, a.val i ≠ 0 := by
    by_contra h
    push Not at h
    exact a.property.1.ne_zero (funext h)
  obtain ⟨i,hi⟩ := hex
  exact Finset.sum_pos' (fun j _ => a.property.2 j)
    ⟨i,Finset.mem_univ _,lt_of_le_of_ne' (a.property.2 i) hi⟩

def normalizedRoot (a : PositiveRoot M cs) : I → ℝ := (height a.val)⁻¹ • a.val

theorem normalizedRoot_injective : Function.Injective (normalizedRoot (M := M) (cs := cs)) := by
  intro a b hab
  have ha : 0 < (height a.val)⁻¹ := inv_pos.mpr a.height_pos
  have hb : 0 < (height b.val)⁻¹ := inv_pos.mpr b.height_pos
  have hn := congrArg (fun v => form M v v) hab
  change form M ((height a.val)⁻¹ • a.val) ((height a.val)⁻¹ • a.val) =
    form M ((height b.val)⁻¹ • b.val) ((height b.val)⁻¹ • b.val) at hn
  simp only [map_smul,LinearMap.smul_apply,smul_eq_mul,a.property.1.norm,b.property.1.norm] at hn
  have hh : (height a.val)⁻¹ = (height b.val)⁻¹ := by nlinarith
  apply Subtype.ext
  change (height a.val)⁻¹ • a.val = (height b.val)⁻¹ • b.val at hab
  rw [← hh] at hab
  exact (smul_right_injective _ ha.ne').eq_iff.mp hab

variable (M cs)

theorem countable_Positiveroot : Countable (PositiveRoot M cs) := by
  let : Countable W := cs.wordProd_surjective.countable
  exact Countable.of_equiv {t : W // cs.IsReflection t} (positiveRootEquiv M cs)


theorem exists_geometric_functional : ∃ f : Module.Dual ℝ (I → ℝ),
    Function.Injective (fun a : PositiveRoot M cs => f a.val / height a.val) := by
  let := countable_Positiveroot M cs
  obtain ⟨f,hf⟩ := ReflectionSchedules.exists_generic_functional
    (normalizedRoot (M := M) (cs := cs)) normalizedRoot_injective
  refine ⟨f,?_⟩
  convert hf using 1
  all_goals try with_reducible_and_instances rfl
  funext a
  simp [normalizedRoot,div_eq_mul_inv,mul_comm]

/-- Betweenness of all positive combinations is the angular-order condition
on every root plane. This is the genuine geometric reflection-order property. -/
theorem functionalRatio_between (f : Module.Dual ℝ (I → ℝ))
    (a b c : PositiveRoot M cs) {r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    (hc : c.val = r • a.val + s • b.val)
    (hab : f a.val / height a.val < f b.val / height b.val) :
    f a.val / height a.val < f c.val / height c.val ∧
      f c.val / height c.val < f b.val / height b.val := by
  have ha := a.height_pos
  have hb := b.height_pos
  have hh := c.height_pos
  have hfc : f c.val = r*f a.val+s*f b.val := by rw [hc]; simp
  have hhc : height c.val = r*height a.val+s*height b.val := by rw [hc]; simp
  rw [div_lt_div_iff₀ ha hb] at hab
  constructor
  · rw [div_lt_div_iff₀ ha hh,hfc,hhc]
    nlinarith [mul_pos hs (sub_pos.mpr hab)]
  · rw [div_lt_div_iff₀ hh hb,hfc,hhc]
    nlinarith [mul_pos hr (sub_pos.mpr hab)]

end
end KLInvariance.TitsSpace

namespace KLInvariance.TitsSpace
open Module
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
noncomputable section

/-- Conjugation on the actual root lines, represented by positive roots. -/
def positiveAction (w : W) (a : PositiveRoot M cs) : PositiveRoot M cs :=
  positiveRoot M cs ⟨w * (rootReflection M cs a).val * w⁻¹,
    (rootReflection M cs a).property.conj w⟩

theorem positiveAction_represents (w : W) (a : PositiveRoot M cs) :
    Represents M cs (w * (rootReflection M cs a).val * w⁻¹) (positiveAction w a).val :=
  positiveRoot_represents M cs ⟨w * (rootReflection M cs a).val * w⁻¹,
    (rootReflection M cs a).property.conj w⟩

theorem positiveAction_eq_of_nonneg (w : W) (a : PositiveRoot M cs)
    (hp : ∀ i, 0 ≤ action M cs w a.val i) :
    (positiveAction w a).val = action M cs w a.val :=
  (positiveAction_represents w a).unique_positive
    ((rootReflection_represents M cs a).act w) (positiveAction w a).property.2 hp

theorem positiveAction_eq_of_nonpos (w : W) (a : PositiveRoot M cs)
    (hn : ∀ i, action M cs w a.val i ≤ 0) :
    (positiveAction w a).val = -action M cs w a.val :=
  (positiveAction_represents w a).unique_positive
    ((rootReflection_represents M cs a).act w).neg (positiveAction w a).property.2
    (fun i => neg_nonneg.mpr (hn i))

@[simp] theorem rootReflection_positiveAction (w : W) (a : PositiveRoot M cs) :
    (rootReflection M cs (positiveAction w a)).val = w*(rootReflection M cs a).val*w⁻¹ :=
  (rootReflection_represents M cs _).reflection_unique (positiveAction_represents w a)

@[simp] theorem positiveAction_one (a : PositiveRoot M cs) : positiveAction 1 a = a := by
  apply (positiveRootEquiv M cs).symm.injective
  apply Subtype.ext
  change (rootReflection M cs (positiveAction 1 a)).val = (rootReflection M cs a).val
  simp

theorem positiveAction_mul (w z : W) (a : PositiveRoot M cs) :
    positiveAction (w*z) a = positiveAction w (positiveAction z a) := by
  apply (positiveRootEquiv M cs).symm.injective
  apply Subtype.ext
  change (rootReflection M cs (positiveAction (w*z) a)).val =
    (rootReflection M cs (positiveAction w (positiveAction z a))).val
  simp only [rootReflection_positiveAction]
  group

def positiveActionEquiv (w : W) : Equiv.Perm (PositiveRoot M cs) where
  toFun := positiveAction w
  invFun := positiveAction w⁻¹
  left_inv a := by rw [← positiveAction_mul, inv_mul_cancel, positiveAction_one]
  right_inv a := by rw [← positiveAction_mul, mul_inv_cancel, positiveAction_one]

abbrev rootRef (a : PositiveRoot M cs) : W := (rootReflection M cs a).val

theorem positiveAction_involutive (a : PositiveRoot M cs) :
    Function.Involutive (positiveAction (M := M) (cs := cs) (rootRef a)) := by
  intro b
  rw [← positiveAction_mul, (rootReflection M cs a).property.mul_self, positiveAction_one]

def rootInverted (w : W) (a : PositiveRoot M cs) : Prop :=
  ∀ i, action M cs w⁻¹ a.val i ≤ 0

theorem not_rootInverted_iff (w : W) (a : PositiveRoot M cs) :
    ¬ rootInverted w a ↔ ∀ i, 0 ≤ action M cs w⁻¹ a.val i := by
  constructor
  · intro hn
    exact (a.property.1.act w⁻¹).sign.resolve_right hn
  · intro hp hn
    exact (a.property.1.act w⁻¹).not_both hp hn

theorem rootInverted_mul_of_nonneg (x : W) (a b : PositiveRoot M cs)
    (hp : ∀ i, 0 ≤ action M cs (rootRef a) b.val i) :
    rootInverted (rootRef a*x) b ↔ rootInverted x (positiveAction (rootRef a) b) := by
  unfold rootInverted
  rw [positiveAction_eq_of_nonneg _ _ hp, mul_inv_rev, (rootReflection M cs a).property.inv,
    map_mul]
  rfl

theorem rootInverted_mul_of_nonpos (x : W) (a b : PositiveRoot M cs)
    (hn : ∀ i, action M cs (rootRef a) b.val i ≤ 0) :
    rootInverted (rootRef a*x) b ↔ ¬ rootInverted x (positiveAction (rootRef a) b) := by
  rw [not_rootInverted_iff]
  unfold rootInverted
  rw [positiveAction_eq_of_nonpos _ _ hn, mul_inv_rev, (rootReflection M cs a).property.inv,
    map_mul, map_neg]
  simp only [LinearEquiv.mul_apply, Pi.neg_apply, neg_nonneg]

theorem negative_pair_sum (a b : PositiveRoot M cs)
    (hn : ∀ i, action M cs (rootRef a) b.val i ≤ 0) :
    b.val + (positiveAction (rootRef a) b).val = form M a.val b.val • a.val := by
  rw [positiveAction_eq_of_nonpos _ _ hn, (rootReflection_represents M cs a).action_formula]
  module

theorem negative_pair_coefficient_pos (a b : PositiveRoot M cs)
    (hn : ∀ i, action M cs (rootRef a) b.val i ≤ 0) : 0 < form M a.val b.val := by
  have h := congrArg (fun z => height z) (negative_pair_sum a b hn)
  simp only [map_add,map_smul,smul_eq_mul] at h
  have hp := b.height_pos
  have hq := (positiveAction (rootRef a) b).height_pos
  have ha := a.height_pos
  nlinarith

/-- The crucial direct positivity argument: over an ascent in alpha, the
negative root-pair for its reflection cannot both already be inversions.
This works in degenerate planes and does not assume a dihedral presentation. -/
theorem negative_pair_not_both (x : W) (a b : PositiveRoot M cs)
    (hx : ¬ rootInverted x a)
    (hn : ∀ i, action M cs (rootRef a) b.val i ≤ 0) :
    ¬ (rootInverted x b ∧ rootInverted x (positiveAction (rootRef a) b)) := by
  rintro ⟨hb,hc⟩
  have hp := (not_rootInverted_iff x a).mp hx
  have hs := congrArg (action M cs x⁻¹) (negative_pair_sum a b hn)
  simp only [map_add,map_smul] at hs
  have hcoef := negative_pair_coefficient_pos a b hn
  have hna : ∀ i, action M cs x⁻¹ a.val i ≤ 0 := by
    intro i
    have hi := congrFun hs i
    change action M cs x⁻¹ b.val i +
      action M cs x⁻¹ (positiveAction (rootRef a) b).val i =
        form M a.val b.val * action M cs x⁻¹ a.val i at hi
    have hb' := hb i
    have hc' := hc i
    nlinarith
  exact (a.property.1.act x⁻¹).not_both hp hna

end
end KLInvariance.TitsSpace

namespace KLInvariance.TitsSpace
open Module
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
noncomputable section
local instance instDecidable_solutions (p : Prop) : Decidable p := Classical.propDecidable p

theorem finite_rootInverted (w : W) : {a : PositiveRoot M cs | rootInverted w a}.Finite := by
  exact Set.finite_coe_iff.mp (rootInversions_finite M cs w)

def inversionVector (w : W) : PositiveRoot M cs →₀ ℤ := by
  classical
  refine Finsupp.ofSupportFinite (fun a => if rootInverted w a then 1 else 0) ?_
  simpa only [Function.support, ne_eq, ite_eq_right_iff, one_ne_zero, imp_false,
    not_not] using finite_rootInverted (M := M) (cs := cs) w

@[simp] theorem inversionVector_apply (w : W) (a : PositiveRoot M cs) :
    inversionVector w a = if rootInverted w a then 1 else 0 := by
  classical
  rfl

def rootChange (x y : W) : PositiveRoot M cs →₀ ℤ := inversionVector y - inversionVector x

def rootPlane (a b : PositiveRoot M cs) : Submodule ℝ (I → ℝ) :=
  Submodule.span ℝ {a.val,b.val}

/-- The finitely supported change in root inversions, with the distinguished
root removed, grouped by actual root planes. -/
def planeDefect (x y : W) (a : PositiveRoot M cs) : Submodule ℝ (I → ℝ) →₀ ℤ :=
  Finsupp.mapDomain (rootPlane a) ((rootChange x y).erase a)

theorem rootInverted_mul_self (x : W) (a : PositiveRoot M cs) :
    rootInverted (rootRef a*x) a ↔ ¬ rootInverted x a := by
  have h := (rootReflection M cs a).property.isLeftInversion_mul_right_iff (w := x)
  simpa only [rootInverted, ← (rootReflection_represents M cs a).inversion_iff a.property.2] using h

theorem rootChange_distinguished (x : W) (a : PositiveRoot M cs)
    (hx : ¬ rootInverted x a) : rootChange x (rootRef a*x) a = 1 := by
  classical
  simp only [rootChange, Finsupp.sub_apply, inversionVector_apply,
    (rootInverted_mul_self x a).mpr hx, hx, ite_true, if_true, ite_false, if_false, sub_zero]


end
end KLInvariance.TitsSpace

namespace KLInvariance.TitsSpace
open Module
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
noncomputable section
local instance instDecidable_solutions_1 (p : Prop) : Decidable p := Classical.propDecidable p

abbrev partner (a b : PositiveRoot M cs) := positiveAction (rootRef a) b

theorem partner_self (a : PositiveRoot M cs) : partner a a = a := by
  apply (positiveRootEquiv M cs).symm.injective
  apply Subtype.ext
  change (rootReflection M cs (positiveAction (rootRef a) a)).val = rootRef a
  rw [rootReflection_positiveAction, (rootReflection M cs a).property.mul_self, one_mul,
    (rootReflection M cs a).property.inv]

theorem partner_involutive (a : PositiveRoot M cs) : Function.Involutive (partner a) :=
  positiveAction_involutive a

theorem partner_eq_self_of_eq (a b : PositiveRoot M cs) : partner a b = a ↔ b = a := by
  constructor
  · intro h
    have hh := congrArg (partner a) h
    rwa [partner_involutive a b,partner_self] at hh
  · rintro rfl
    exact partner_self _

abbrev flipped (a b : PositiveRoot M cs) : Prop :=
  ∀ i, action M cs (rootRef a) b.val i ≤ 0

theorem flipped_partner_iff (a b : PositiveRoot M cs) : flipped a (partner a b) ↔ flipped a b := by
  have hact : action M cs (rootRef a) * action M cs (rootRef a) = 1 := by
    rw [← map_mul, (rootReflection M cs a).property.mul_self, map_one]
  by_cases hb : flipped a b
  · have heq := positiveAction_eq_of_nonpos (rootRef a) b hb
    have hp : flipped a (partner a b) := by
      intro i
      change action M cs (rootRef a) (positiveAction (rootRef a) b).val i ≤ 0
      rw [heq,map_neg, ← LinearEquiv.mul_apply,hact]
      exact neg_nonpos.mpr (b.property.2 i)
    exact iff_of_true hp hb
  · have hpos := (b.property.1.act (rootRef a)).sign.resolve_right hb
    have heq := positiveAction_eq_of_nonneg (rootRef a) b hpos
    have hp : ¬ flipped a (partner a b) := by
      intro hh
      have hneg : ∀ i, b.val i ≤ 0 := by
        intro i
        have hi := hh i
        change action M cs (rootRef a) (positiveAction (rootRef a) b).val i ≤ 0 at hi
        rwa [heq, ← LinearEquiv.mul_apply, hact] at hi
      exact b.property.1.not_both b.property.2 hneg
    exact iff_of_false hp hb

theorem partner_mem {P : Submodule ℝ (I → ℝ)} (a b : PositiveRoot M cs)
    (ha : a.val ∈ P) (hb : b.val ∈ P) : (partner a b).val ∈ P := by
  have hm : action M cs (rootRef a) b.val ∈ P := by
    rw [(rootReflection_represents M cs a).action_formula]
    exact P.sub_mem hb (P.smul_mem _ ha)
  rcases (b.property.1.act (rootRef a)).sign with hp|hn
  · exact (positiveAction_eq_of_nonneg (rootRef a) b hp).symm ▸ hm
  · exact (positiveAction_eq_of_nonpos (rootRef a) b hn).symm ▸ P.neg_mem hm

theorem rootPlane_partner (a b : PositiveRoot M cs) : rootPlane a (partner a b) = rootPlane a b := by
  have hle (b : PositiveRoot M cs) : rootPlane a (partner a b) ≤ rootPlane a b := by
    apply Submodule.span_le.mpr
    intro z hz
    rcases Set.mem_insert_iff.mp hz with rfl|hz
    · exact Submodule.subset_span (Set.mem_insert _ _)
    · rcases Set.mem_singleton_iff.mp hz with rfl
      exact partner_mem a b (Submodule.subset_span (Set.mem_insert _ _))
        (Submodule.subset_span (Set.mem_insert_of_mem _ rfl))
  exact le_antisymm (hle b) (by simpa only [partner_involutive a b] using hle (partner a b))

theorem negative_partner_fixed (a b : PositiveRoot M cs) (hn : flipped a b)
    (heq : partner a b = b) : b = a := by
  have hs := negative_pair_sum a b hn
  change b.val + (partner a b).val = form M a.val b.val • a.val at hs
  rw [heq] at hs
  have hc := negative_pair_coefficient_pos a b hn
  have hb : b.val = (form M a.val b.val / 2) • a.val := by
    calc
      b.val = (1/2:ℝ) • (b.val+b.val) := by module
      _ = _ := by rw [hs]; module
  have hnorm := b.property.1.norm
  rw [hb] at hnorm
  simp only [map_smul,LinearMap.smul_apply,smul_eq_mul,a.property.1.norm] at hnorm
  have hc2 : form M a.val b.val / 2 = 1 := by nlinarith
  apply Subtype.ext
  simpa only [hc2,one_smul] using hb

/-- Roots in a negative pair which are both positive before the ascent. -/
def goodPairRoot (x : W) (a b : PositiveRoot M cs) : Prop :=
  flipped a b ∧ ¬ rootInverted x b ∧ ¬ rootInverted x (partner a b)

theorem goodPairRoot_partner (x : W) (a b : PositiveRoot M cs) :
    goodPairRoot x a (partner a b) ↔ goodPairRoot x a b := by
  simp only [goodPairRoot,flipped_partner_iff,partner_involutive a b]
  tauto

/-- The pairwise change is either zero or two, with no negative case. -/
theorem rootChange_pair (x : W) (a b : PositiveRoot M cs) (hx : ¬ rootInverted x a) :
    rootChange x (rootRef a*x) b + rootChange x (rootRef a*x) (partner a b) =
      if goodPairRoot x a b then 2 else 0 := by
  by_cases hn : flipped a b
  · have hn' := (flipped_partner_iff a b).mpr hn
    have hi := rootInverted_mul_of_nonpos x a b hn
    have hi' := rootInverted_mul_of_nonpos x a (partner a b) hn'
    have hpair : positiveAction (rootRef a) (partner a b) = b := partner_involutive a b
    rw [hpair] at hi'
    have hnnb := negative_pair_not_both x a b hx hn
    simp only [rootChange,Finsupp.sub_apply,inversionVector_apply,hi,hi',goodPairRoot,]
    by_cases hb : rootInverted x b <;> by_cases hc : rootInverted x (partner a b) <;>
      simp_all
  · have hp := (b.property.1.act (rootRef a)).sign.resolve_right hn
    have hn' := mt (flipped_partner_iff a b).mp hn
    have hp' := ((partner a b).property.1.act (rootRef a)).sign.resolve_right hn'
    have hi := rootInverted_mul_of_nonneg x a b hp
    have hi' := rootInverted_mul_of_nonneg x a (partner a b) hp'
    have hpair : positiveAction (rootRef a) (partner a b) = b := partner_involutive a b
    rw [hpair] at hi'
    simp only [rootChange,Finsupp.sub_apply,inversionVector_apply,hi,hi',goodPairRoot,hn,false_and,ite_false, if_false]
    ring

end
end KLInvariance.TitsSpace

namespace KLInvariance.TitsSpace
open Module
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
noncomputable section
local instance instDecidable_solutions_2 (p : Prop) : Decidable p := Classical.propDecidable p

def geometricFunctional : Module.Dual ℝ (I → ℝ) := (exists_geometric_functional M cs).choose

def geometricSlope (a : PositiveRoot M cs) : ℝ := geometricFunctional (M := M) (cs := cs) a.val / height a.val

theorem geometricSlope_injective : Function.Injective (geometricSlope (M := M) (cs := cs)) :=
  (exists_geometric_functional M cs).choose_spec

@[instance_reducible]
def geometricOrder : LinearOrder (PositiveRoot M cs) := LinearOrder.lift' geometricSlope geometricSlope_injective

theorem geometricSlope_between (a b c : PositiveRoot M cs) {r s : ℝ}
    (hr : 0 < r) (hs : 0 < s) (hc : c.val = r • a.val+s • b.val)
    (hab : geometricSlope a < geometricSlope b) :
    geometricSlope a < geometricSlope c ∧ geometricSlope c < geometricSlope b :=
  functionalRatio_between M cs (geometricFunctional (M := M) (cs := cs)) a b c hr hs hc hab

def partnerEquiv (a : PositiveRoot M cs) : Equiv.Perm (PositiveRoot M cs) :=
  Function.Involutive.toPerm (partner a) (partner_involutive a)

@[simp] theorem partnerEquiv_apply (a b : PositiveRoot M cs) : partnerEquiv a b = partner a b := rfl
@[simp] theorem partnerEquiv_symm_apply (a b : PositiveRoot M cs) : (partnerEquiv a).symm b = partner a b := rfl

def extraRoot (x : W) (a b : PositiveRoot M cs) : Prop := b ≠ a ∧ goodPairRoot x a b

theorem extraRoot_partner (x : W) (a b : PositiveRoot M cs) :
    extraRoot x a (partner a b) ↔ extraRoot x a b := by
  simp only [extraRoot,ne_eq,partner_eq_self_of_eq,goodPairRoot_partner]

theorem extraRoot_finite (x : W) (a : PositiveRoot M cs) : {b | extraRoot x a b}.Finite := by
  apply (finite_rootInverted (M := M) (cs := cs) (rootRef a*x)).subset
  intro b hb
  exact (rootInverted_mul_of_nonpos x a b hb.2.1).mpr hb.2.2.2

def halfRoot (x : W) (a b : PositiveRoot M cs) : Prop :=
  extraRoot x a b ∧ geometricSlope b < geometricSlope (partner a b)

theorem halfRoot_finite (x : W) (a : PositiveRoot M cs) : {b | halfRoot x a b}.Finite :=
  (extraRoot_finite x a).subset (fun _ h => h.1)

def rootIndicator (p : PositiveRoot M cs → Prop) (hp : {a | p a}.Finite) : PositiveRoot M cs →₀ ℤ :=
  Finsupp.ofSupportFinite (fun a => if p a then 1 else 0) (by
    simpa only [Function.support,ne_eq,ite_eq_right_iff,one_ne_zero,imp_false,not_not] using hp)

@[simp] theorem rootIndicator_apply (p : PositiveRoot M cs → Prop) (hp : {a | p a}.Finite)
    (a : PositiveRoot M cs) : rootIndicator p hp a = if p a then 1 else 0 := rfl

def extraVector (x : W) (a : PositiveRoot M cs) := rootIndicator (extraRoot x a) (extraRoot_finite x a)
def halfVector (x : W) (a : PositiveRoot M cs) := rootIndicator (halfRoot x a) (halfRoot_finite x a)

/-- A choice of one root in each actual two-element negative pair. -/
theorem extraVector_eq_half (x : W) (a : PositiveRoot M cs) :
    extraVector x a = halfVector x a + Finsupp.mapDomain (partnerEquiv a) (halfVector x a) := by
  ext b
  simp only [Finsupp.add_apply,Finsupp.mapDomain_equiv_apply,partnerEquiv_symm_apply,
    extraVector,halfVector,rootIndicator_apply,halfRoot,extraRoot_partner,partner_involutive a b]
  by_cases hb : extraRoot x a b
  · have hne : geometricSlope b ≠ geometricSlope (partner a b) := by
      intro h
      exact hb.1 (negative_partner_fixed a b hb.2.1 (geometricSlope_injective h).symm)
    rcases lt_or_gt_of_ne hne with h|h
    · simp [hb,h,not_lt_of_gt h]
    · simp [hb,h,not_lt_of_gt h]
  · simp [hb]

/-- All apparent negative contributions cancel under the actual reflection on
root lines; the remaining pairs are precisely `extraVector`. -/
theorem erasedChange_pair (x : W) (a : PositiveRoot M cs) (hx : ¬ rootInverted x a) :
    (rootChange x (rootRef a*x)).erase a +
      Finsupp.mapDomain (partnerEquiv a) ((rootChange x (rootRef a*x)).erase a) =
        extraVector x a + extraVector x a := by
  classical
  ext b
  simp only [Finsupp.add_apply,Finsupp.mapDomain_equiv_apply,partnerEquiv_symm_apply]
  by_cases hb : b=a
  · subst b
    simp [partner_self,extraVector,extraRoot]
  · have hpb : partner a b ≠ a := mt (partner_eq_self_of_eq a b).mp hb
    rw [Finsupp.erase_ne hb,Finsupp.erase_ne hpb,rootChange_pair x a b hx]
    simp only [extraVector,rootIndicator_apply,extraRoot,]
    by_cases hg : goodPairRoot x a b <;> simp [hg,hb]

theorem mapDomain_plane_partner (a : PositiveRoot M cs) (f : PositiveRoot M cs →₀ ℤ) :
    Finsupp.mapDomain (rootPlane a) (Finsupp.mapDomain (partnerEquiv a) f) =
      Finsupp.mapDomain (rootPlane a) f := by
  rw [← Finsupp.mapDomain_comp]
  apply Finsupp.mapDomain_congr
  intro b _
  exact rootPlane_partner a b

def planeWeight (x : W) (a : PositiveRoot M cs) : Submodule ℝ (I → ℝ) →₀ ℤ :=
  Finsupp.mapDomain (rootPlane a) (halfVector x a)


theorem planeDefect_eq_double_weight (x : W) (a : PositiveRoot M cs) (hx : ¬ rootInverted x a) :
    planeDefect x (rootRef a*x) a = planeWeight x a + planeWeight x a := by
  have h := congrArg (Finsupp.mapDomain (rootPlane a)) (erasedChange_pair x a hx)
  rw [Finsupp.mapDomain_add,mapDomain_plane_partner,Finsupp.mapDomain_add] at h
  have heq : planeDefect x (rootRef a*x) a = Finsupp.mapDomain (rootPlane a) (extraVector x a) := by
    ext P
    have hh := congrArg (fun f : Submodule ℝ (I → ℝ) →₀ ℤ => f P) h
    simp only [Finsupp.add_apply] at hh
    change planeDefect x (rootRef a*x) a P = _
    dsimp [planeDefect]
    omega
  rw [heq,extraVector_eq_half,Finsupp.mapDomain_add,mapDomain_plane_partner]
  rfl

end
end KLInvariance.TitsSpace

namespace KLInvariance.TitsSpace
open Module
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
noncomputable section

local instance instDecidable_solutions_3_r1f31a4_1 (p : Prop) : Decidable p := Classical.propDecidable p
theorem positiveRoots_independent (a b : PositiveRoot M cs) (hab : a ≠ b) :
    LinearIndependent ℝ ![a.val,b.val] := by
  apply (rootReflection_represents M cs a).independent_of_ne (rootReflection_represents M cs b)
  intro h
  apply hab
  apply (positiveRootEquiv M cs).symm.injective
  exact Subtype.ext h

theorem rootPlane_finrank (a b : PositiveRoot M cs) (hab : a ≠ b) :
    Module.finrank ℝ (rootPlane a b) = 2 := by
  have h := finrank_span_eq_card (positiveRoots_independent a b hab)
  have hrange : Set.range ![a.val,b.val] = {a.val,b.val} := by
    ext z
    simp only [Set.mem_range,Set.mem_insert_iff,Set.mem_singleton_iff]
    constructor
    · rintro ⟨i,rfl⟩
      fin_cases i <;> simp
    · rintro (rfl|rfl)
      · exact ⟨0,rfl⟩
      · exact ⟨1,rfl⟩
  rw [hrange] at h
  exact h

theorem rootPlane_self_finrank (a : PositiveRoot M cs) :
    Module.finrank ℝ (rootPlane a a) = 1 := by
  have hset : ({a.val,a.val} : Set (I → ℝ)) = {a.val} := by ext z; simp
  rw [rootPlane,hset]
  exact finrank_span_singleton (K := ℝ) (a.property.1.ne_zero)

theorem rootPlane_eq_iff (a b c : PositiveRoot M cs) (hab : a ≠ b) :
    rootPlane a c = rootPlane a b ↔ c ≠ a ∧ c.val ∈ rootPlane a b := by
  constructor
  · intro h
    constructor
    · intro hc
      subst c
      have h' := congrArg (fun P : Submodule ℝ (I → ℝ) => Module.finrank ℝ P) h
      rw [rootPlane_self_finrank,rootPlane_finrank a b hab] at h'
      norm_num at h'
    · rw [← h]
      exact Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  · rintro ⟨hc,hcP⟩
    apply Submodule.eq_of_le_of_finrank_eq
    · apply Submodule.span_le.mpr
      intro z hz
      rcases (Set.mem_insert_iff.mp hz) with rfl|hz
      · exact Submodule.subset_span (Set.mem_insert _ _)
      · have hzc := Set.mem_singleton_iff.mp hz
        subst z
        exact hcP
    · rw [rootPlane_finrank a c (Ne.symm hc),rootPlane_finrank a b hab]

end
end KLInvariance.TitsSpace

namespace KLInvariance.TitsSpace
open Module
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
noncomputable section
local instance instDecidable_solutions_4 (p : Prop) : Decidable p := Classical.propDecidable p

/-- The actual finite count of ambient inversions belonging to a root plane.
No Coxeter presentation of the plane subgroup is assumed here. -/
def planeLength (P : Submodule ℝ (I → ℝ)) (w : W) : ℤ :=
  (inversionVector (M := M) (cs := cs) w).sum (fun a n => if a.val ∈ P then n else 0)

theorem rootPlane_grouped_erase (a b : PositiveRoot M cs) (hab : a ≠ b)
    (f : PositiveRoot M cs →₀ ℤ) :
    Finsupp.mapDomain (rootPlane a) (f.erase a) (rootPlane a b) =
      f.sum (fun c n => if c.val ∈ rootPlane a b then n else 0) - f a := by
  classical
  have haP : a.val ∈ rootPlane a b := Submodule.subset_span (Set.mem_insert _ _)
  have heq : Finsupp.mapDomain (rootPlane a) (f.erase a) (rootPlane a b) =
      (f.erase a).sum (fun c n => if c.val ∈ rootPlane a b then n else 0) := by
    rw [Finsupp.mapDomain,Finsupp.sum_apply]
    apply Finset.sum_congr rfl
    intro c hc
    have hca : c ≠ a := by
      intro h
      subst c
      simp only [Finsupp.mem_support_iff,Finsupp.erase_same,ne_eq,not_true_eq_false] at hc
    change (Finsupp.single (rootPlane a c) ((f.erase a) c)) (rootPlane a b) =
      (if c.val ∈ rootPlane a b then (f.erase a) c else 0)
    rw [Finsupp.single_apply]
    by_cases hm : c.val ∈ rootPlane a b
    · rw [ite_eq_left ((rootPlane_eq_iff a b c hab).mpr ⟨hca,hm⟩),ite_eq_left hm]
    · rw [ite_eq_right (fun heq => hm ((rootPlane_eq_iff a b c hab).mp heq).2),ite_eq_right hm]
  rw [heq,Finsupp.erase_eq_sub_single,
    Finsupp.sum_sub_index (fun c m n => by split_ifs <;> simp),
    Finsupp.sum_single_index (by simp),ite_eq_left haP]

theorem planeDefect_eq_relative_difference (x : W) (a b : PositiveRoot M cs)
    (hab : a ≠ b) (hx : ¬ rootInverted x a) :
    planeDefect x (rootRef a*x) a (rootPlane a b) =
      planeLength (M := M) (cs := cs) (rootPlane a b) (rootRef a*x) - planeLength (M := M) (cs := cs) (rootPlane a b) x - 1 := by
  rw [planeDefect,rootPlane_grouped_erase a b hab,rootChange_distinguished x a hx,
    rootChange,Finsupp.sum_sub_index (fun c m n => by split_ifs <;> simp)]
  rfl


theorem planeWeight_relative_degree (x : W) (a b : PositiveRoot M cs)
    (hab : a ≠ b) (hx : ¬ rootInverted x a) :
    2 * planeWeight x a (rootPlane a b) =
      planeLength (M := M) (cs := cs) (rootPlane a b) (rootRef a*x) - planeLength (M := M) (cs := cs) (rootPlane a b) x - 1 := by
  have h := planeDefect_eq_relative_difference x a b hab hx
  rw [planeDefect_eq_double_weight x a hx,Finsupp.add_apply] at h
  linarith

end
end KLInvariance.TitsSpace

namespace KLInvariance.EdgeAlgebra
open Module
universe u v
variable {k : Type u} [Field k] {V : Type v} [AddCommGroup V] [Module k V]
noncomputable section


def rootIdeal (a : V) : Ideal (SymmetricAlgebra k V) :=
  Ideal.span {SymmetricAlgebra.ι k V a}

def rootLine (a : V) : Submodule k V := Submodule.span k {a}

def symQuotientMap (a : V) : SymmetricAlgebra k V →ₐ[k] SymmetricAlgebra k (V ⧸ rootLine (k := k) a) :=
  SymmetricAlgebra.lift ((SymmetricAlgebra.ι k (V ⧸ rootLine (k := k) a)).comp (rootLine (k := k) a).mkQ)

@[simp] theorem symQuotientMap_ι (a v : V) :
    symQuotientMap a (SymmetricAlgebra.ι k V v) =
      SymmetricAlgebra.ι k (V ⧸ rootLine (k := k) a) ((rootLine (k := k) a).mkQ v) :=
  SymmetricAlgebra.lift_ι_apply _ _

theorem rootIdeal_le_ker (a : V) : rootIdeal (k := k) a ≤ RingHom.ker (symQuotientMap a) := by
  apply Ideal.span_le.mpr
  intro z hz
  have hz' := Set.mem_singleton_iff.mp hz
  subst z
  change symQuotientMap a (SymmetricAlgebra.ι k V a) = 0
  rw [symQuotientMap_ι]
  have ha : (rootLine (k := k) a).mkQ a = 0 := by
    exact (Submodule.Quotient.mk_eq_zero (rootLine (k := k) a)).mpr (Submodule.subset_span (Set.mem_singleton a))
  rw [ha,map_zero]

def quotientForward (a : V) : (SymmetricAlgebra k V ⧸ rootIdeal (k := k) a) →ₐ[k]
    SymmetricAlgebra k (V ⧸ rootLine (k := k) a) :=
  Ideal.Quotient.liftₐ _ (symQuotientMap a) (fun _ hz => rootIdeal_le_ker a hz)

@[simp] theorem quotientForward_mk (a : V) (z : SymmetricAlgebra k V) :
    quotientForward a (Ideal.Quotient.mk (rootIdeal (k := k) a) z) = symQuotientMap a z := rfl

end
end KLInvariance.EdgeAlgebra


namespace KLInvariance.SchedulePaths
universe u v w
variable {V : Type u} {E : Type v} {R : Type w}
noncomputable section
variable (source target : E → V)

def IsPath (x y : V) : List E → Prop
  | [] => x = y
  | e :: p => source e = x ∧ IsPath (target e) y p

end
end KLInvariance.SchedulePaths

/-! NEW GRAPH CLOSURE -/
namespace KLInvariance
universe u v
variable {I : Type u} [klPreservedInstance7 : Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
noncomputable section

include klPreservedInstance7 in
 theorem BruhatStep.label_reflection {x y : W} (h : BruhatStep cs x y) :
    cs.IsReflection (y*x⁻¹) := by
  have _ := klPreservedInstance7
  obtain ⟨_,t,ht,rfl⟩ := h
  simpa [mul_assoc] using ht

namespace TitsSpace
open Module

 def graphRoot {x y : W} (h : BruhatStep cs x y) : PositiveRoot M cs :=
   positiveRoot M cs ⟨y*x⁻¹,h.label_reflection⟩

end TitsSpace
end
end KLInvariance


namespace KLInvariance.Dihedral
variable {W : Type*} [Group W] {M : CoxeterMatrix Bool}

theorem alt_add_two (i : Bool) (n : ℕ) :
    alt i (n+2) = i :: (!i) :: alt i n := by
  simp only [alt_succ,Bool.not_not]

theorem alt_odd_sandwich (i : Bool) (n : ℕ) :
    alt i (2*(n+1)+1) = i :: (alt (!i) (2*n+1) ++ [i]) := by
  induction n generalizing i with
  | zero => cases i <;> rfl
  | succ n ih =>
    have h₁ : 2*(n+1+1)+1 = (2*(n+1)+1)+2 := by omega
    have h₂ : 2*(n+1)+1 = (2*n+1)+2 := by omega
    rw [h₁,alt_add_two,ih,h₂,alt_add_two]
    simp only [Bool.not_not,List.cons_append]

theorem odd_alt_reflection (cs : CoxeterSystem M W) (i : Bool) (n : ℕ) :
    cs.IsReflection (cs.wordProd (alt i (2*n+1))) := by
  induction n generalizing i with
  | zero => simpa [alt] using cs.isReflection_simple i
  | succ n ih =>
    rw [alt_odd_sandwich,cs.wordProd_cons,cs.wordProd_append]
    obtain ⟨w,j,hw⟩ := ih (!i)
    refine ⟨cs.simple i*w,j,?_⟩
    simp only [cs.wordProd_cons,cs.wordProd_nil,mul_one,hw,mul_inv_rev,
      cs.inv_simple]
    group

theorem reflection_iff_odd (cs : CoxeterSystem M W) (w : W) :
    cs.IsReflection w ↔ Odd (cs.length w) := by
  constructor
  · exact fun h => h.odd_length
  · intro h
    obtain ⟨n,hn⟩ := h
    obtain ⟨i,hi⟩ := exists_alt cs w
    rw [hi,hn]
    convert odd_alt_reflection cs i n using 2
    all_goals try with_reducible_and_instances rfl

theorem step_iff_odd (cs : CoxeterSystem M W) (x y : W) :
    BruhatStep cs x y ↔ cs.length x < cs.length y ∧ Odd (cs.length y-cs.length x) := by
  have hm := cs.length_mul_mod_two y x⁻¹
  rw [cs.length_inv] at hm
  constructor
  · rintro ⟨hlen,t,ht,hprod⟩
    refine ⟨hlen,?_⟩
    have hteq : y*x⁻¹=t := by rw [hprod]; group
    have ho := ht.odd_length
    rw [← hteq,Nat.odd_iff] at ho
    rw [Nat.odd_iff]
    omega
  · rintro ⟨hlen,ho⟩
    refine ⟨hlen,y*x⁻¹,?_,by group⟩
    rw [reflection_iff_odd,Nat.odd_iff]
    rw [Nat.odd_iff] at ho
    omega

end KLInvariance.Dihedral


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

namespace KLInvariance.MomentGraph
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A}
  {V E : Type um} [PartialOrder V] (G : OrderedGraph V E)

structure GradedSheaf where
  vertex : V → ModuleData.{uk,ua,um} 𝓐
  edge : E → ModuleData.{uk,ua,um} 𝓐
  lower : ∀ e, ModuleData.Hom (vertex (G.source e)) (edge e)
  upper : ∀ e, ModuleData.Hom (vertex (G.target e)) (edge e)

namespace GradedSheaf
variable {G} (B : GradedSheaf (𝓐 := 𝓐) G)

def forget : Sheaf (R := A) G where
  vertex := fun x => (B.vertex x).obj
  edge := fun e => (B.edge e).obj
  lower := fun e => (B.lower e).map
  upper := fun e => (B.upper e).map

/-- Extension for sets closed under actual edges. It implies the source's
ordinary flabbiness, and is convenient for the descending construction. -/
def EdgeFlabby : Prop :=
  ∀ Ω : Set V, B.forget.ClosedUnder Set.univ Ω →
    ∀ f : B.forget.Assignment, B.forget.CompatibleOn Ω f →
    ∃ g : B.forget.Assignment, B.forget.IsGlobal g ∧ ∀ x ∈ Ω, g x = f x

variable [Fintype V] [Fintype E]

noncomputable def assignments : ModuleData.{uk,ua,um} 𝓐 := ModuleData.pi B.vertex

noncomputable def lowerGlobal (e : E) : ModuleData.Hom B.assignments (B.edge e) :=
  (B.lower e).comp (ModuleData.projection B.vertex (G.source e))

noncomputable def upperGlobal (e : E) : ModuleData.Hom B.assignments (B.edge e) :=
  (B.upper e).comp (ModuleData.projection B.vertex (G.target e))

omit [Fintype E] in
 theorem sections_homogeneous (Ω : Set V) :
    ∀ n f, f ∈ B.forget.sections Ω → component B.assignments.piece n f ∈ B.forget.sections Ω := by
  intro n f hf e hs ht
  change (B.lowerGlobal e).map (component B.assignments.piece n f) =
    (B.upperGlobal e).map (component B.assignments.piece n f)
  rw [← (B.lowerGlobal e).component n f, ← (B.upperGlobal e).component n f]
  exact congrArg (component (B.edge e).piece n) (hf e hs ht)

noncomputable def sections [IsNoetherianRing A] (Ω : Set V) : ModuleData.{uk,ua,um} 𝓐 :=
  ModuleData.sub B.assignments (B.forget.sections Ω) (B.sections_homogeneous Ω)

end GradedSheaf
end KLInvariance.MomentGraph

end


section

namespace KLInvariance.MomentGraph
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A}
  {V E D : Type um} [PartialOrder V] (G : OrderedGraph V E)

/-- Adjoin a vertex below the old vertices, with specified outgoing edges.
Only the edge orientations, not the extra comparabilities, enter sections. -/
def bottomGraph (τ : D → V) : OrderedGraph (WithBot V) (E ⊕ D) where
  source := Sum.elim (fun e => (G.source e : WithBot V)) (fun _ => ⊥)
  target := Sum.elim (fun e => (G.target e : WithBot V)) (fun d => (τ d : WithBot V))
  increasing := by
    intro e
    cases e with
    | inl e => exact WithBot.coe_lt_coe.mpr (G.increasing e)
    | inr d => exact WithBot.bot_lt_coe (τ d)

namespace GradedSheaf
variable {G} (B : GradedSheaf (𝓐 := 𝓐) G)
  [Fintype V] [Fintype D] [IsNoetherianRing A]
  (τ : D → V) (α : D → A) (hα : ∀ d, α d ∈ 𝓐 1)

noncomputable def attachEdges (d : D) : ModuleData.{uk,ua,um} 𝓐 :=
  (B.vertex (τ d)).scalarQuotient (α d) 1 (hα d)

noncomputable def attachQuotient (d : D) :
    ModuleData.Hom (B.vertex (τ d)) (B.attachEdges τ α hα d) :=
  ModuleData.quotientMap _ _ (scalar_range_homogeneous 𝓐 (B.vertex (τ d)).piece 1 (α d) (hα d))

noncomputable def attachBoundary : ModuleData.{uk,ua,um} 𝓐 :=
  ModuleData.pi (B.attachEdges τ α hα)

noncomputable def attachBoundaryMap :
    ModuleData.Hom (B.sections Set.univ) (B.attachBoundary τ α hα) where
  map := LinearMap.pi fun d => (B.attachQuotient τ α hα d).map.comp
    ((LinearMap.proj (τ d)).comp (B.forget.sections Set.univ).subtype)
  graded := by
    intro n f hf d _
    exact (B.attachQuotient τ α hα d).graded n _ (hf (τ d) (Set.mem_univ _))

noncomputable def attachImage : ModuleData.{uk,ua,um} 𝓐 :=
  ModuleData.range (B.attachBoundaryMap τ α hα)

variable (C : ModuleData.MinimalCover (B.attachImage τ α hα))

noncomputable def attachStalkMap : ModuleData.Hom C.source (B.attachBoundary τ α hα) :=
  (ModuleData.subtype (B.attachBoundary τ α hα) _
    (range_homogeneous _ _ (B.attachBoundaryMap τ α hα).map 0
      (by simpa using (B.attachBoundaryMap τ α hα).graded))).comp C.hom

noncomputable def extendBottom : GradedSheaf (𝓐 := 𝓐) (bottomGraph G τ) where
  vertex := WithBot.recBotCoe C.source B.vertex
  edge := Sum.elim B.edge (B.attachEdges τ α hα)
  lower := by
    intro e
    cases e with
    | inl e => exact B.lower e
    | inr d =>
      exact (ModuleData.projection (B.attachEdges τ α hα) d).comp
        (B.attachStalkMap τ α hα C)
  upper := by
    intro e
    cases e with
    | inl e => exact B.upper e
    | inr d => exact B.attachQuotient τ α hα d

 def attachAssignment (z : C.source) (f : B.forget.Assignment) :
    (B.extendBottom τ α hα C).forget.Assignment := WithBot.recBotCoe z f

 theorem attachAssignment_global (z : C.source) (f : B.forget.Assignment)
    (hf : B.forget.IsGlobal f)
    (hz : ∀ d, (B.attachStalkMap τ α hα C).map z d =
      (B.attachQuotient τ α hα d).map (f (τ d))) :
    (B.extendBottom τ α hα C).forget.IsGlobal (B.attachAssignment τ α hα C z f) := by
  intro e _ _
  cases e with
  | inl e => exact hf e (Set.mem_univ _) (Set.mem_univ _)
  | inr d => exact hz d

 theorem lift_global (f : B.forget.Assignment) (hf : B.forget.IsGlobal f) :
    ∃ z : C.source, (B.extendBottom τ α hα C).forget.IsGlobal
      (B.attachAssignment τ α hα C z f) := by
  let s : B.sections Set.univ := ⟨f,hf⟩
  let v : B.attachImage τ α hα :=
    ⟨(B.attachBoundaryMap τ α hα).map s, ⟨s,rfl⟩⟩
  obtain ⟨z,hz⟩ := C.surjective v
  refine ⟨z,B.attachAssignment_global τ α hα C z f hf ?_⟩
  intro d
  exact congrArg (fun t : B.attachImage τ α hα => t.val d) hz

 theorem extendBottom_edgeFlabby (hf : B.EdgeFlabby) :
    (B.extendBottom τ α hα C).EdgeFlabby := by
  intro Ω hΩ f hcompat
  let Ω' : Set V := {x | (x : WithBot V) ∈ Ω}
  let f' : B.forget.Assignment := fun x => f (x : WithBot V)
  have hc : B.forget.ClosedUnder Set.univ Ω' := by
    intro e _ hs
    exact hΩ (Sum.inl e) (Set.mem_univ _) hs
  have hcf : B.forget.CompatibleOn Ω' f' := by
    intro e hs ht
    exact hcompat (Sum.inl e) hs ht
  obtain ⟨g,hg,hgf⟩ := hf Ω' hc f' hcf
  classical
  by_cases hb : (⊥ : WithBot V) ∈ Ω
  · refine ⟨B.attachAssignment τ α hα C (f ⊥) g,
      B.attachAssignment_global τ α hα C (f ⊥) g hg ?_,?_⟩
    · intro d
      have hd : (τ d : WithBot V) ∈ Ω := hΩ (Sum.inr d) (Set.mem_univ _) hb
      rw [hgf (τ d) hd]
      exact hcompat (Sum.inr d) hb hd
    · intro x hx
      induction x using WithBot.recBotCoe with
      | bot => rfl
      | coe x => exact hgf x hx
  · obtain ⟨z,hz⟩ := B.lift_global τ α hα C g hg
    refine ⟨B.attachAssignment τ α hα C z g,hz,?_⟩
    intro x hx
    induction x using WithBot.recBotCoe with
    | bot => exact (hb hx).elim
    | coe x => exact hgf x hx

end GradedSheaf
end KLInvariance.MomentGraph

end


section

namespace KLInvariance.Graded.ModuleData
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A}

def Hom.ofEq {M N : ModuleData.{uk,ua,um} 𝓐} (h : M = N) : Hom M N := h ▸ Hom.id M

@[simp] theorem Hom.ofEq_rfl (M : ModuleData.{uk,ua,um} 𝓐) : Hom.ofEq (rfl : M=M) = Hom.id M := rfl

theorem Hom.ofEq_apply {ι : Type*} (M : ι → ModuleData.{uk,ua,um} 𝓐)
    {x y : ι} (h : x = y) (v : ∀ z, M z) :
    (Hom.ofEq (congrArg M h)).map (v x) = v y := by subst y; rfl

end KLInvariance.Graded.ModuleData

namespace KLInvariance.MomentGraph
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A}
  {V E W F : Type um} [PartialOrder V] [PartialOrder W]
  {G : OrderedGraph V E} {H : OrderedGraph W F}

/-- An isomorphism of directed graphs, with no order-reflection requirement. -/
structure GraphEquiv (G : OrderedGraph V E) (H : OrderedGraph W F) where
  vertex : V ≃ W
  edge : E ≃ F
  source : ∀ e, vertex (G.source e) = H.source (edge e)
  target : ∀ e, vertex (G.target e) = H.target (edge e)

namespace GradedSheaf
variable (B : GradedSheaf (𝓐 := 𝓐) H) (e : GraphEquiv G H)

def reindex : GradedSheaf (𝓐 := 𝓐) G where
  vertex := fun x => B.vertex (e.vertex x)
  edge := fun a => B.edge (e.edge a)
  lower := fun a => (B.lower (e.edge a)).comp (ModuleData.Hom.ofEq (congrArg B.vertex (e.source a)))
  upper := fun a => (B.upper (e.edge a)).comp (ModuleData.Hom.ofEq (congrArg B.vertex (e.target a)))

def reindexAssignment (f : B.forget.Assignment) : (B.reindex e).forget.Assignment :=
  fun x => f (e.vertex x)

@[simp] theorem reindex_lower (a : E) (f : B.forget.Assignment) :
    (B.reindex e).forget.lower a (B.reindexAssignment e f (G.source a)) =
      B.forget.lower (e.edge a) (f (H.source (e.edge a))) := by
  change (B.lower (e.edge a)).map ((ModuleData.Hom.ofEq (congrArg B.vertex (e.source a))).map
    (f (e.vertex (G.source a)))) = _
  exact congrArg (B.lower (e.edge a)).map
    (ModuleData.Hom.ofEq_apply B.vertex (e.source a) f)

@[simp] theorem reindex_upper (a : E) (f : B.forget.Assignment) :
    (B.reindex e).forget.upper a (B.reindexAssignment e f (G.target a)) =
      B.forget.upper (e.edge a) (f (H.target (e.edge a))) := by
  change (B.upper (e.edge a)).map ((ModuleData.Hom.ofEq (congrArg B.vertex (e.target a))).map
    (f (e.vertex (G.target a)))) = _
  exact congrArg (B.upper (e.edge a)).map
    (ModuleData.Hom.ofEq_apply B.vertex (e.target a) f)

def unreindexAssignment (f : (B.reindex e).forget.Assignment) : B.forget.Assignment :=
  fun y => (ModuleData.Hom.ofEq (congrArg B.vertex (e.vertex.apply_symm_apply y))).map
    (f (e.vertex.symm y))

@[simp] theorem unreindex_reindexAssignment (f : B.forget.Assignment) :
    B.unreindexAssignment e (B.reindexAssignment e f) = f := by
  funext y
  exact ModuleData.Hom.ofEq_apply B.vertex (e.vertex.apply_symm_apply y) f

@[simp] theorem reindex_unreindexAssignment (f : (B.reindex e).forget.Assignment) :
    B.reindexAssignment e (B.unreindexAssignment e f) = f := by
  funext x
  change (ModuleData.Hom.ofEq (congrArg B.vertex (e.vertex.apply_symm_apply (e.vertex x)))).map
    (f (e.vertex.symm (e.vertex x))) = f x
  have h : e.vertex.symm (e.vertex x) = x := e.vertex.symm_apply_apply x
  have hh : (ModuleData.Hom.ofEq
      (congrArg (fun t => B.vertex (e.vertex t)) h)).map
      (f (e.vertex.symm (e.vertex x))) = f x :=
    ModuleData.Hom.ofEq_apply (fun t => B.vertex (e.vertex t)) h f
  exact hh

end GradedSheaf
end KLInvariance.MomentGraph

end


section

namespace KLInvariance.Graded.ModuleData
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A}

noncomputable def unit [DirectSum.Decomposition 𝓐] [SetLike.GradedMonoid 𝓐]
    (hneg : ∀ n < 0, 𝓐 n = ⊥) : ModuleData.{uk,ua,um} 𝓐 :=
  free (ι := PUnit.{max ua um + 1}) hneg (fun _ => 0) (fun _ => le_rfl)

end KLInvariance.Graded.ModuleData

namespace KLInvariance.MomentGraph.GradedSheaf
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A}
  {V E W F : Type um} [PartialOrder V] [PartialOrder W]
  {G : OrderedGraph V E} {H : OrderedGraph W F}

 def FreeStalks (B : GradedSheaf (𝓐 := 𝓐) G) : Prop := ∀ x, Module.Free A (B.vertex x)

/-- The genuine upper-end quotient rule, expressed without choosing a quotient
presentation of the edge object. -/
 def UpperQuotient (B : GradedSheaf (𝓐 := 𝓐) G) (α : E → A) : Prop :=
  ∀ e, Function.Surjective (B.upper e).map ∧
    ∀ v, (B.upper e).map v = 0 ↔ ∃ w, v = α e • w

/-- Minimality of the full outgoing boundary cover. The assignment formulation
avoids dependent casts and is equivalent to the usual kernel containment. -/
 def KernelMinimal (B : GradedSheaf (𝓐 := 𝓐) G) (x : V) : Prop :=
  ∀ f : B.forget.Assignment,
    (∀ e, G.source e = x → B.forget.lower e (f (G.source e)) = 0) →
    f x ∈ positiveIdeal 𝓐 • (⊤ : Submodule A (B.vertex x))

end KLInvariance.MomentGraph.GradedSheaf

end


section

namespace KLInvariance.MomentGraph
open _root_.OAI.KLInvariance.Graded
universe uk ua um
variable {k : Type uk} [Field k] {A : Type ua} [CommRing A] [Algebra k A]
  {𝓐 : ℤ → Submodule k A} [DirectSum.Decomposition 𝓐] [SetLike.GradedMonoid 𝓐]
  (hneg : ∀ n < 0, 𝓐 n = ⊥)

/-- The outcome of the actual minimal boundary construction. Full upward-kernel
freeness, integral duality and KL characters are NOT part of this structure. -/
structure BoundarySheaf {V E : Type um} [PartialOrder V] (G : OrderedGraph V E)
    (α : E → A) (b : V) where
  sheaf : GradedSheaf (𝓐 := 𝓐) G
  free : sheaf.FreeStalks
  quotient : sheaf.UpperQuotient α
  flabby : sheaf.EdgeFlabby
  generated : sheaf.forget.Generated
  top : sheaf.vertex b = ModuleData.unit hneg
  minimal : ∀ x, x ≠ b → sheaf.KernelMinimal x

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

namespace KLInvariance.Graded
universe uk us
variable (k : Type uk) [Field k] (σ : Type us)

 theorem polynomial_scalar_mod_positive (a : MvPolynomial σ k) :
    ∃ c : k, a-algebraMap k (MvPolynomial σ k) c ∈ positiveIdeal (polynomialGrading k σ) := by
  obtain ⟨c,hc⟩ := polynomialGrading_zero k σ _
    (DirectSum.decompose (polynomialGrading k σ) a 0).property
  refine ⟨c,?_⟩
  rw [positiveIdeal_eq_augmentation_ker _ (polynomialGrading_negative k σ)]
  change component (polynomialGrading k σ) 0 (a-algebraMap k (MvPolynomial σ k) c)=0
  rw [map_sub,hc]
  rw [show component (polynomialGrading k σ) 0
    (DirectSum.decompose (polynomialGrading k σ) a 0 : MvPolynomial σ k) =
    (DirectSum.decompose (polynomialGrading k σ) a 0 : MvPolynomial σ k) from
    DirectSum.decompose_of_mem_same _ (DirectSum.decompose (polynomialGrading k σ) a 0).property]
  exact sub_self _

end KLInvariance.Graded

namespace KLInvariance.BruhatGraph
open Module TitsSpace _root_.OAI.KLInvariance.Graded MomentGraph
universe u v us
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W) (u b : W)
  {σ : Type us} [Fintype σ] (basis : Basis σ ℝ (Extended M))
noncomputable section


abbrev Coefficient := MvPolynomial σ ℝ

def root (e : Edge cs u b) : PositiveRoot M cs :=
  positiveRootEquiv M cs ⟨label cs u b e,label_isReflection cs u b e⟩

def polynomialLabel (e : Edge cs u b) : Coefficient (σ := σ) :=
  SymmetricAlgebra.equivMvPolynomial basis
    (SymmetricAlgebra.ι ℝ (Extended M) (embed M (root cs u b e).val))

 theorem polynomialLabel_homogeneous (e : Edge cs u b) :
    polynomialLabel cs u b basis e ∈ polynomialGrading ℝ σ 1 := by
  classical
  unfold polynomialLabel
  rw [← basis.sum_repr (embed M (root cs u b e).val)]
  simp only [map_sum,map_smul,SymmetricAlgebra.equivMvPolynomial_ι_apply]
  apply Submodule.sum_mem
  intro i _
  exact (polynomialGrading ℝ σ 1).smul_mem _
    (MvPolynomial.isWeightedHomogeneous_X ℝ (fun _ : σ => (1 : ℤ)) i)

end
end KLInvariance.BruhatGraph

end


section

/-! Parity matching in finite lower Bruhat intervals, used only to construct
actual dihedral interpolation sections. -/
namespace KLInvariance
universe u v
variable {I : Type u} {M : CoxeterMatrix I} {W : Type v} [Group W]
  (cs : CoxeterSystem M W)
noncomputable section

 def externalLower (x c : W) : Finset W := by
  classical
  exact (lowerFinset cs c) \ (lowerFinset cs x)

@[simp] theorem mem_externalLower (x c z : W) :
    z ∈ externalLower cs x c ↔ BruhatLE cs z c ∧ ¬ BruhatLE cs z x := by
  classical
  simp [externalLower]

end
end KLInvariance

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


namespace KLInvariance.Dihedral
noncomputable section

variable {G : Type*} [Group G]

/-- The matrix of a pair of distinct involutions. -/
def pairMatrix (s t : G) (hs : s * s = 1) (hst : s ≠ t) : CoxeterMatrix Bool where
  M i j := if i = j then 1 else orderOf (s * t)
  isSymm := by
    ext i j
    change (if j = i then 1 else orderOf (s*t)) = if i = j then 1 else orderOf (s*t)
    cases i <;> cases j <;> rfl
  diagonal i := ite_eq_left rfl
  off_diagonal i j hij := by
    rw [ite_eq_right hij]
    intro h
    have he := orderOf_eq_one_iff.mp h
    apply hst
    calc
      s = s * (s * t) := by rw [he, mul_one]
      _ = t := by rw [← mul_assoc, hs, one_mul]

/-- Alternating even words are powers of the product of the two generators. -/
theorem wordProd_alt_even {N : CoxeterMatrix Bool} {H : Type*} [Group H]
    (cs : CoxeterSystem N H) (i : Bool) (n : ℕ) :
    cs.wordProd (alt i (2 * n)) = (cs.simple i * cs.simple (!i)) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 2 by omega, alt_add_two]
    rw [cs.wordProd_cons, cs.wordProd_cons, ih, pow_succ']
    exact (mul_assoc _ _ _).symm

/-- Homomorphisms out of a rank-two Coxeter group that do not lower
its product order and do not kill either generator are injective. -/
theorem injective_of_simple_order {N : CoxeterMatrix Bool} {H : Type*} [Group H]
    (cs : CoxeterSystem N H) (f : H →* G)
    (hne : ∀ i, f (cs.simple i) ≠ 1)
    (horder : ∀ i, orderOf (f (cs.simple i) * f (cs.simple (!i))) = N i (!i)) :
    Function.Injective f := by
  apply (injective_iff_map_eq_one f).mpr
  intro w hw
  rcases Nat.even_or_odd (cs.length w) with he | ho
  · obtain ⟨n, hn⟩ := he
    have hn' : cs.length w = 2 * n := by omega
    obtain ⟨i, hi⟩ := exists_alt cs w
    rw [hn', wordProd_alt_even] at hi
    have hpow : (f (cs.simple i) * f (cs.simple (!i))) ^ n = 1 := by
      simpa only [hi, map_pow, map_mul] using hw
    have hdiv := orderOf_dvd_of_pow_eq_one hpow
    rw [horder i] at hdiv
    obtain ⟨k, hk⟩ := hdiv
    rw [hi, hk, pow_mul, cs.simple_mul_simple_pow, one_pow]
  · obtain ⟨a, i, ha⟩ := (reflection_iff_odd cs w).mpr ho
    have h := hw
    rw [ha, map_mul, map_mul, map_inv] at h
    apply False.elim
    apply hne i
    have h' := congrArg (fun z => (f a)⁻¹ * z * f a) h
    simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one,
      one_mul, mul_inv_cancel_left] using h'

variable (s t : G) (hs : s * s = 1) (ht : t * t = 1) (hst : s ≠ t)

/-- The map from the genuine presented rank-two Coxeter group. -/
def pairLift : (pairMatrix s t hs hst).Group →* G :=
  (pairMatrix s t hs hst).toCoxeterSystem.lift
    ⟨(fun i => if i then t else s), by
      intro i j
      cases i <;> cases j
      · simpa [pairMatrix] using hs
      · simp only [pairMatrix, Bool.false_eq_true, ↓reduceIte]
        exact pow_orderOf_eq_one (s*t)
      · simp only [pairMatrix, Bool.true_eq_false, Bool.false_eq_true, ↓reduceIte]
        have hinv : (s*t)⁻¹ = t*s := by
          rw [mul_inv_rev, (inv_eq_of_mul_eq_one_right ht), (inv_eq_of_mul_eq_one_right hs)]
        rw [← hinv, inv_pow, pow_orderOf_eq_one, inv_one]
      · simpa [pairMatrix] using ht⟩

@[simp] theorem pairLift_simple (i : Bool) :
    pairLift s t hs ht hst ((pairMatrix s t hs hst).toCoxeterSystem.simple i) =
      if i then t else s := by
  apply CoxeterSystem.lift_apply_simple

/-- No relation other than the Coxeter relations is introduced by the pair. -/
theorem pairLift_injective (hs1 : s ≠ 1) (ht1 : t ≠ 1) :
    Function.Injective (pairLift s t hs ht hst) := by
  apply injective_of_simple_order (pairMatrix s t hs hst).toCoxeterSystem
  · intro i
    rw [pairLift_simple]
    cases i <;> simp_all
  · intro i
    simp only [pairLift_simple]
    cases i
    · simp [pairMatrix]
    · simp only [Bool.not_true, ↓reduceIte, pairMatrix, Bool.true_eq_false, Bool.false_eq_true]
      have hinv : (s*t)⁻¹ = t*s := by
        rw [mul_inv_rev, (inv_eq_of_mul_eq_one_right ht), (inv_eq_of_mul_eq_one_right hs)]
      rw [← hinv, orderOf_inv]

/-- The presented pair generates exactly the subgroup generated by its images. -/
theorem pairLift_range :
    (pairLift s t hs ht hst).range = Subgroup.closure {s, t} := by
  apply le_antisymm
  · rintro x ⟨w, rfl⟩
    apply (pairMatrix s t hs hst).toCoxeterSystem.simple_induction w
    · intro i
      rw [pairLift_simple]
      cases i <;> apply Subgroup.subset_closure <;> simp
    · simp only [map_one, Subgroup.one_mem]
    · intro a b ha hb
      rw [map_mul]
      exact Subgroup.mul_mem _ ha hb
  · apply (Subgroup.closure_le _).mpr
    intro x hx
    rcases Set.mem_insert_iff.mp hx with hx | hx
    · rw [hx]
      exact ⟨(pairMatrix s t hs hst).toCoxeterSystem.simple false, pairLift_simple _ _ _ _ _ _⟩
    · have : x = t := Set.mem_singleton_iff.mp hx
      subst x
      exact ⟨(pairMatrix s t hs hst).toCoxeterSystem.simple true, pairLift_simple _ _ _ _ _ _⟩

/-- An actual Coxeter system on the generated subgroup, not an extra assumption. -/
def pairSystem (hs1 : s ≠ 1) (ht1 : t ≠ 1) :
    CoxeterSystem (pairMatrix s t hs hst) (Subgroup.closure {s, t}) :=
  (pairMatrix s t hs hst).toCoxeterSystem.map
    ((MulEquiv.ofBijective (pairLift s t hs ht hst).rangeRestrict
      ⟨MonoidHom.rangeRestrict_injective_iff.mpr
        (pairLift_injective s t hs ht hst hs1 ht1),
       (pairLift s t hs ht hst).rangeRestrict_surjective⟩).trans
      (MulEquiv.subgroupCongr (pairLift_range s t hs ht hst)))

@[simp] theorem pairSystem_simple (hs1 : s ≠ 1) (ht1 : t ≠ 1) (i : Bool) :
    ((pairSystem s t hs ht hst hs1 ht1).simple i : G) = if i then t else s := by
  exact pairLift_simple s t hs ht hst i

end
end KLInvariance.Dihedral


namespace KLInvariance.TitsSpace
open Module
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
noncomputable section

/-- Slope betweenness detects the actual positive cone, not only one implication. -/
theorem positive_combination_of_slope_between (a b c : PositiveRoot M cs)
    (hc : c.val ∈ rootPlane a b)
    (hac : geometricSlope a < geometricSlope c)
    (hcb : geometricSlope c < geometricSlope b) :
    ∃ r s : ℝ, 0 < r ∧ 0 < s ∧ c.val = r • a.val + s • b.val := by
  let f := geometricFunctional (M := M) (cs := cs)
  obtain ⟨r, s, he⟩ := Submodule.mem_span_pair.mp hc
  refine ⟨r, s, ?_, ?_, he.symm⟩
  all_goals
    have ha := a.height_pos
    have hb := b.height_pos
    have hh := c.height_pos
    have hfc := congrArg f he
    have hhc := congrArg (height (I := I)) he
    simp only [map_add, map_smul, smul_eq_mul] at hfc hhc
    change f a.val / height a.val <
      f c.val / height c.val at hac
    change f c.val / height c.val <
      f b.val / height b.val at hcb
    have hab := lt_trans hac hcb
    rw [div_lt_div_iff₀ ha hb] at hab
    rw [div_lt_div_iff₀ ha hh] at hac
    rw [div_lt_div_iff₀ hh hb] at hcb
  · have heq : r * (f b.val * height a.val -
        f a.val * height b.val) =
        f b.val * height c.val -
          f c.val * height b.val := by rw [← hfc, ← hhc]; ring
    have hp : 0 < r * (f b.val * height a.val -
        f a.val * height b.val) := by rw [heq]; linarith
    exact (mul_pos_iff.mp hp).resolve_right (by intro h; linarith [h.2]) |>.1
  · have heq : s * (f b.val * height a.val -
        f a.val * height b.val) =
        f c.val * height a.val -
          f a.val * height c.val := by rw [← hfc, ← hhc]; ring
    have hp : 0 < s * (f b.val * height a.val -
        f a.val * height b.val) := by rw [heq]; linarith
    exact (mul_pos_iff.mp hp).resolve_right (by intro h; linarith [h.2]) |>.1

/-- Positivity is convex in the root cone. -/
theorem noninverted_of_positive_combination (w : W) (a b c : PositiveRoot M cs)
    {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hc : c.val = r • a.val + s • b.val)
    (ha : ¬ rootInverted w a) (hb : ¬ rootInverted w b) :
    ¬ rootInverted w c := by
  rw [not_rootInverted_iff] at ha hb ⊢
  intro i
  rw [hc, map_add, map_smul, map_smul]
  exact add_nonneg (mul_nonneg hr (ha i)) (mul_nonneg hs (hb i))

@[simp] theorem not_rootInverted_one (a : PositiveRoot M cs) :
    ¬ rootInverted (1 : W) a := by
  rw [not_rootInverted_iff]
  simp only [inv_one, map_one]
  exact a.property.2

@[simp] theorem rootInverted_ref_self (a : PositiveRoot M cs) :
    rootInverted (rootRef a) a := by
  simpa only [mul_one] using (rootInverted_mul_self 1 a).mpr (not_rootInverted_one a)

/-- The canonical simple-root criterion stated on the actual ambient roots. -/
def PlaneSimple (P : Submodule ℝ (I → ℝ)) (a : PositiveRoot M cs) : Prop :=
  a.val ∈ P ∧ ∀ b : PositiveRoot M cs, b.val ∈ P →
    (rootInverted (rootRef a) b ↔ b = a)

theorem rootInverted_ref_iff_flipped (a b : PositiveRoot M cs) :
    rootInverted (rootRef a) b ↔ flipped a b := by
  unfold rootInverted flipped
  rw [(rootReflection M cs a).property.inv]

/-- An angular extreme inverts exactly its own positive root. -/
theorem planeSimple_of_extreme {P : Submodule ℝ (I → ℝ)}
    (a : PositiveRoot M cs) (ha : a.val ∈ P)
    (hext : (∀ r : PositiveRoot M cs, r.val ∈ P → geometricSlope a ≤ geometricSlope r) ∨
      (∀ r : PositiveRoot M cs, r.val ∈ P → geometricSlope r ≤ geometricSlope a)) :
    PlaneSimple P a := by
  refine ⟨ha, fun b hb => ⟨?_, ?_⟩⟩
  · intro hinv
    by_contra hba
    have hn := (rootInverted_ref_iff_flipped a b).mp hinv
    have hp := partner_mem a b ha hb
    have hs := negative_pair_sum a b hn
    have hc := negative_pair_coefficient_pos a b hn
    have he : a.val = (form M a.val b.val)⁻¹ • b.val +
        (form M a.val b.val)⁻¹ • (partner a b).val := by
      calc
        a.val = (form M a.val b.val)⁻¹ • (form M a.val b.val • a.val) := by
          rw [smul_smul, inv_mul_cancel₀ hc.ne', one_smul]
        _ = _ := by rw [← hs, smul_add]
    have hne : geometricSlope b ≠ geometricSlope (partner a b) := by
      intro h
      exact hba (negative_partner_fixed a b hn (geometricSlope_injective h).symm)
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have hh := geometricSlope_between b (partner a b) a
        (inv_pos.mpr hc) (inv_pos.mpr hc) he hlt
      rcases hext with hmin | hmax
      · exact (not_lt_of_ge (hmin b hb)) hh.1
      · exact (not_lt_of_ge (hmax (partner a b) hp)) hh.2
    · have he' : a.val = (form M a.val b.val)⁻¹ • (partner a b).val +
          (form M a.val b.val)⁻¹ • b.val := by rw [add_comm]; exact he
      have hh := geometricSlope_between (partner a b) b a
        (inv_pos.mpr hc) (inv_pos.mpr hc) he' hlt
      rcases hext with hmin | hmax
      · exact (not_lt_of_ge (hmin (partner a b) hp)) hh.1
      · exact (not_lt_of_ge (hmax b hb)) hh.2
  · intro h
    rw [h]
    exact rootInverted_ref_self a

/-- Canonical angular endpoints of a plane; no Coxeter-system assertion is
built into this data. The latter will be proved from the inversion criterion. -/
structure PlaneBasis (P : Submodule ℝ (I → ℝ)) where
  left : PositiveRoot M cs
  right : PositiveRoot M cs
  distinct : left ≠ right
  plane_eq : rootPlane left right = P
  left_min : ∀ r : PositiveRoot M cs, r.val ∈ P → geometricSlope left ≤ geometricSlope r
  right_max : ∀ r : PositiveRoot M cs, r.val ∈ P → geometricSlope r ≤ geometricSlope right

namespace PlaneBasis
variable {P : Submodule ℝ (I → ℝ)} (B : PlaneBasis (M := M) (cs := cs) P)

theorem left_mem : B.left.val ∈ P := by
  apply B.plane_eq.le
  exact Submodule.subset_span (Set.mem_insert _ _)

theorem right_mem : B.right.val ∈ P := by
  apply B.plane_eq.le
  exact Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))

theorem left_simple : PlaneSimple P B.left :=
  planeSimple_of_extreme B.left B.left_mem (.inl B.left_min)

theorem right_simple : PlaneSimple P B.right :=
  planeSimple_of_extreme B.right B.right_mem (.inr B.right_max)

/-- Every positive root in the plane is in its canonical nonnegative cone. -/
theorem positive_cone (r : PositiveRoot M cs) (hr : r.val ∈ P) :
    ∃ c d : ℝ, 0 ≤ c ∧ 0 ≤ d ∧ r.val = c • B.left.val + d • B.right.val := by
  by_cases hl : r = B.left
  · exact ⟨1, 0, zero_le_one, le_refl 0, by rw [hl]; simp⟩
  by_cases hh : r = B.right
  · exact ⟨0, 1, le_refl 0, zero_le_one, by rw [hh]; simp⟩
  have hlr : geometricSlope B.left < geometricSlope r :=
    lt_of_le_of_ne (B.left_min r hr) (fun h => hl (geometricSlope_injective h).symm)
  have hrr : geometricSlope r < geometricSlope B.right :=
    lt_of_le_of_ne (B.right_max r hr) (fun h => hh (geometricSlope_injective h))
  obtain ⟨c, d, hc, hd, he⟩ := positive_combination_of_slope_between B.left B.right r
    (B.plane_eq.ge hr) hlr hrr
  exact ⟨c, d, hc.le, hd.le, he⟩

end PlaneBasis


/-- Canonical-simple reflections have no extra root pair in their own plane. -/
theorem PlaneSimple.planeWeight_eq_zero {P : Submodule ℝ (I → ℝ)}
    {a : PositiveRoot M cs} (ha : PlaneSimple P a) (x : W) :
    planeWeight x a P = 0 := by
  classical
  rw [planeWeight, Finsupp.mapDomain, Finsupp.sum_apply]
  apply Finset.sum_eq_zero
  intro b _
  change (Finsupp.single (rootPlane a b) (halfVector x a b)) P = 0
  rw [Finsupp.single_apply]
  by_cases hP : rootPlane a b = P
  · rw [ite_eq_left hP]
    simp only [halfVector, rootIndicator_apply]
    apply ite_eq_right
    intro hh
    have hbP : b.val ∈ P := hP.le
      (Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
    exact hh.1.1 ((ha.2 b hbP).mp ((rootInverted_ref_iff_flipped a b).mpr hh.1.2.1))
  · exact ite_eq_right hP

/-- The relative inversion count has the genuine simple-reflection step. -/
theorem PlaneSimple.planeLength_step {P : Submodule ℝ (I → ℝ)}
    {a b : PositiveRoot M cs} (ha : PlaneSimple P a)
    (hab : a ≠ b) (hP : rootPlane a b = P) (x : W)
    (hx : ¬ rootInverted x a) :
    planeLength (M := M) (cs := cs) P (rootRef a * x) =
      planeLength (M := M) (cs := cs) P x + 1 := by
  have hh := planeWeight_relative_degree x a b hab hx
  rw [hP, ha.planeWeight_eq_zero] at hh
  linarith

theorem PlaneSimple.planeLength_step_down {P : Submodule ℝ (I → ℝ)}
    {a b : PositiveRoot M cs} (ha : PlaneSimple P a)
    (hab : a ≠ b) (hP : rootPlane a b = P) (x : W)
    (hx : rootInverted x a) :
    planeLength (M := M) (cs := cs) P (rootRef a * x) =
      planeLength (M := M) (cs := cs) P x - 1 := by
  have hy : ¬ rootInverted (rootRef a * x) a :=
    fun h => (rootInverted_mul_self x a).mp h hx
  have hh := ha.planeLength_step hab hP (rootRef a * x) hy
  rw [← mul_assoc, (rootReflection M cs a).property.mul_self, one_mul] at hh
  linarith

/-- The usual inversion bijection, proved on the actual positive roots. -/
theorem rootInverted_inverse_action (w : W) (a : PositiveRoot M cs) :
    rootInverted w⁻¹ (positiveAction w⁻¹ a) ↔ rootInverted w a := by
  have hw : action M cs w (action M cs w⁻¹ a.val) = a.val := by
    rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    rfl
  by_cases hi : rootInverted w a
  · apply iff_of_true ?_ hi
    unfold rootInverted
    rw [inv_inv, positiveAction_eq_of_nonpos _ _ hi, map_neg, hw]
    exact fun i => neg_nonpos.mpr (a.property.2 i)
  · apply iff_of_false ?_ hi
    rw [not_rootInverted_iff, inv_inv,
      positiveAction_eq_of_nonneg _ _ ((not_rootInverted_iff w a).mp hi), hw]
    exact a.property.2

/-- Reindexing the inversion indicator by the inverse root action. -/
theorem inversionVector_inverse (w : W) :
    inversionVector (M := M) (cs := cs) w⁻¹ =
      Finsupp.mapDomain (positiveActionEquiv w⁻¹) (inversionVector w) := by
  classical
  apply (Finsupp.ext_iff).mpr
  intro b
  obtain ⟨a, rfl⟩ := (positiveActionEquiv (M := M) (cs := cs) w⁻¹).surjective b
  rw [Finsupp.mapDomain_equiv_apply, Equiv.symm_apply_apply]
  simp only [inversionVector_apply]
  change (if rootInverted w⁻¹ (positiveAction w⁻¹ a) then 1 else 0) = _
  rw [rootInverted_inverse_action]

theorem positiveAction_mem_plane {P : Submodule ℝ (I → ℝ)}
    {w : W} (hw : w ∈ planeSubgroup M cs P) (a : PositiveRoot M cs)
    (ha : a.val ∈ P) : (positiveAction w a).val ∈ P := by
  have hp := planeSubgroup_preserves hw ha
  rcases (a.property.1.act w).sign with hs | hs
  · exact (positiveAction_eq_of_nonneg w a hs).symm ▸ hp
  · exact (positiveAction_eq_of_nonpos w a hs).symm ▸ P.neg_mem hp

theorem positiveAction_mem_plane_iff {P : Submodule ℝ (I → ℝ)}
    {w : W} (hw : w ∈ planeSubgroup M cs P) (a : PositiveRoot M cs) :
    (positiveAction w a).val ∈ P ↔ a.val ∈ P := by
  refine ⟨fun h => ?_, positiveAction_mem_plane hw a⟩
  have hh := positiveAction_mem_plane ((planeSubgroup M cs P).inv_mem hw)
    (positiveAction w a) h
  rwa [← positiveAction_mul, inv_mul_cancel, positiveAction_one] at hh

/-- Relative inversion count is invariant under inverse on the actual plane subgroup. -/
theorem planeLength_inv {P : Submodule ℝ (I → ℝ)} {w : W}
    (hw : w ∈ planeSubgroup M cs P) :
    planeLength (M := M) (cs := cs) P w⁻¹ = planeLength (M := M) (cs := cs) P w := by
  classical
  rw [planeLength, inversionVector_inverse,
    Finsupp.sum_mapDomain_index (by intros; split_ifs <;> rfl)
      (by intros; split_ifs <;> simp)]
  apply Finsupp.sum_congr
  intro a _
  change (if (positiveAction w⁻¹ a).val ∈ P then _ else _) = _
  rw [positiveAction_mem_plane_iff ((planeSubgroup M cs P).inv_mem hw)]

theorem planeLength_nonneg (P : Submodule ℝ (I → ℝ)) (w : W) :
    0 ≤ planeLength (M := M) (cs := cs) P w := by
  classical
  apply Finset.sum_nonneg
  intro a _
  simp only [inversionVector_apply]
  split_ifs <;> norm_num

namespace PlaneBasis
variable {P : Submodule ℝ (I → ℝ)} (B : PlaneBasis (M := M) (cs := cs) P)

/-- A plane reflection must invert at least one of the canonical endpoints.
This uses convex positivity, not any assumed Coxeter structure on the subgroup. -/
theorem reflection_inverts_endpoint (r : PositiveRoot M cs) (hr : r.val ∈ P) :
    rootInverted (rootRef r) B.left ∨ rootInverted (rootRef r) B.right := by
  by_contra h
  push Not at h
  obtain ⟨c, d, hc, hd, he⟩ := B.positive_cone r hr
  exact (noninverted_of_positive_combination (rootRef r) B.left B.right r
    hc hd he h.1 h.2) (rootInverted_ref_self r)

end PlaneBasis


/-- The second descent in a simple conjugation of a nonsimple reflection. -/
theorem PlaneSimple.inverted_after_mul {P : Submodule ℝ (I → ℝ)}
    {a r : PositiveRoot M cs} (ha : PlaneSimple P a) (hr : r.val ∈ P)
    (hra : r ≠ a) (hi : rootInverted (rootRef r) a) :
    rootInverted (rootRef r * rootRef a) a := by
  have hn := (rootInverted_ref_iff_flipped r a).mp hi
  apply (rootInverted_mul_of_nonpos (rootRef a) r a hn).mpr
  intro hinv
  have he : partner r a = a := (ha.2 (partner r a) (partner_mem r a hr ha.1)).mp hinv
  exact hra (negative_partner_fixed r a hn he).symm

/-- The honest relative length drops by two under the chosen simple conjugation. -/
theorem PlaneSimple.planeLength_conj_drop {P : Submodule ℝ (I → ℝ)}
    {a b r : PositiveRoot M cs} (ha : PlaneSimple P a)
    (hab : a ≠ b) (hP : rootPlane a b = P) (hr : r.val ∈ P)
    (hra : r ≠ a) (hi : rootInverted (rootRef r) a) :
    planeLength (M := M) (cs := cs) P (rootRef (partner a r)) =
      planeLength (M := M) (cs := cs) P (rootRef r) - 2 := by
  have har : rootRef a ∈ planeSubgroup M cs P :=
    ((rootReflection_represents M cs a).planeSubgroup_mem_iff M cs).mpr ha.1
  have hrr : rootRef r ∈ planeSubgroup M cs P :=
    ((rootReflection_represents M cs r).planeSubgroup_mem_iff M cs).mpr hr
  have hmul := (planeSubgroup M cs P).mul_mem har hrr
  have hd := ha.planeLength_step_down hab hP (rootRef r) hi
  have hd' := ha.planeLength_step_down hab hP (rootRef r * rootRef a)
    (ha.inverted_after_mul hr hra hi)
  have hli := planeLength_inv hmul
  rw [mul_inv_rev, (rootReflection M cs r).property.inv,
    (rootReflection M cs a).property.inv] at hli
  change planeLength (M := M) (cs := cs) P
    (rootReflection M cs (positiveAction (rootRef a) r)).val = _
  rw [rootReflection_positiveAction, (rootReflection M cs a).property.inv, mul_assoc]
  linarith

namespace PlaneBasis
variable {P : Submodule ℝ (I → ℝ)} (B : PlaneBasis (M := M) (cs := cs) P)

/-- The canonical endpoint reflections generate every ambient reflection in the plane. -/
theorem rootRef_mem_pairClosure (r : PositiveRoot M cs) (hr : r.val ∈ P) :
    rootRef r ∈ Subgroup.closure {rootRef B.left, rootRef B.right} := by
  classical
  generalize hn : (planeLength (M := M) (cs := cs) P (rootRef r)).toNat = n
  induction n using Nat.strong_induction_on generalizing r with
  | h n ih =>
    by_cases hl : r = B.left
    · rw [hl]; exact Subgroup.subset_closure (Set.mem_insert _ _)
    by_cases hh : r = B.right
    · rw [hh]; exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
    have step (a b : PositiveRoot M cs) (ha : PlaneSimple P a)
        (hab : a ≠ b) (hP : rootPlane a b = P) (hra : r ≠ a)
        (hgen : rootRef a ∈ Subgroup.closure {rootRef B.left, rootRef B.right})
        (hi : rootInverted (rootRef r) a) :
        rootRef r ∈ Subgroup.closure {rootRef B.left, rootRef B.right} := by
      have hp : (partner a r).val ∈ P := partner_mem a r ha.1 hr
      have hdrop := ha.planeLength_conj_drop hab hP hr hra hi
      have hless : (planeLength (M := M) (cs := cs) P (rootRef (partner a r))).toNat < n := by
        have hnonneg := planeLength_nonneg (M := M) (cs := cs) P (rootRef (partner a r))
        omega
      have hind := ih _ hless (partner a r) hp rfl
      have hlen := (Subgroup.closure {rootRef B.left, rootRef B.right}).mul_mem
        ((Subgroup.closure {rootRef B.left, rootRef B.right}).mul_mem hgen hind) hgen
      change rootRef a * (rootReflection M cs (positiveAction (rootRef a) r)).val * rootRef a ∈ _ at hlen
      rw [rootReflection_positiveAction, (rootReflection M cs a).property.inv] at hlen
      rw [← mul_assoc, ← mul_assoc, (rootReflection M cs a).property.mul_self,
        one_mul, mul_assoc, (rootReflection M cs a).property.mul_self, mul_one] at hlen
      exact hlen
    rcases B.reflection_inverts_endpoint r hr with hi | hi
    · exact step B.left B.right B.left_simple B.distinct B.plane_eq hl
        (Subgroup.subset_closure (Set.mem_insert _ _)) hi
    · exact step B.right B.left B.right_simple B.distinct.symm
        (by rw [rootPlane, Set.pair_comm]; exact B.plane_eq) hh
        (Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))) hi

/-- Exact identification with the manuscript's maximal root-plane subgroup. -/
theorem pairClosure_eq_planeSubgroup :
    Subgroup.closure {rootRef B.left, rootRef B.right} = planeSubgroup M cs P := by
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    intro t ht
    rcases Set.mem_insert_iff.mp ht with he | he
    · rw [he]
      exact ((rootReflection_represents M cs B.left).planeSubgroup_mem_iff M cs).mpr B.left_mem
    · rw [Set.mem_singleton_iff.mp he]
      exact ((rootReflection_represents M cs B.right).planeSubgroup_mem_iff M cs).mpr B.right_mem
  · apply (Subgroup.closure_le _).mpr
    rintro t ⟨a, ha, haP⟩
    let r := positiveRoot M cs ⟨t, ha.isReflection⟩
    have hre : rootRef r = t := (rootReflection_represents M cs r).reflection_unique
      (positiveRoot_represents M cs ⟨t, ha.isReflection⟩)
    have hrP : r.val ∈ P := ((positiveRoot_represents M cs
      ⟨t, ha.isReflection⟩).planeSubgroup_mem_iff M cs).mp (Subgroup.subset_closure ⟨a, ha, haP⟩)
    rw [← hre]
    exact B.rootRef_mem_pairClosure r hrP

/-- Distinct positive roots give distinct actual reflections. -/
theorem rootRef_distinct : rootRef B.left ≠ rootRef B.right := by
  intro he
  apply B.distinct
  apply (positiveRootEquiv M cs).symm.injective
  exact Subtype.ext he

theorem rootRef_ne_one (a : PositiveRoot M cs) : rootRef a ≠ 1 := by
  intro h
  exact (not_rootInverted_one a) (h ▸ rootInverted_ref_self a)

/-- The genuine dihedral matrix attached to the canonical plane endpoints. -/
def matrix : CoxeterMatrix Bool :=
  Dihedral.pairMatrix (rootRef B.left) (rootRef B.right)
    (rootReflection M cs B.left).property.mul_self B.rootRef_distinct

/-- A proved Coxeter system on the *actual maximal plane subgroup*. -/
def system : CoxeterSystem B.matrix (planeSubgroup M cs P) :=
  (Dihedral.pairSystem (rootRef B.left) (rootRef B.right)
    (rootReflection M cs B.left).property.mul_self
    (rootReflection M cs B.right).property.mul_self B.rootRef_distinct
    (rootRef_ne_one B.left)
    (rootRef_ne_one B.right)).map
      (MulEquiv.subgroupCongr B.pairClosure_eq_planeSubgroup)

/-- Canonical simple positive roots, indexed by Bool just like the system. -/
def simpleRoot (i : Bool) : PositiveRoot M cs := if i then B.right else B.left

@[simp] theorem system_simple (i : Bool) :
    (B.system.simple i : W) = rootRef (B.simpleRoot i) := by
  change ((Dihedral.pairSystem (rootRef B.left) (rootRef B.right)
    (rootReflection M cs B.left).property.mul_self
    (rootReflection M cs B.right).property.mul_self B.rootRef_distinct
    (rootRef_ne_one B.left) (rootRef_ne_one B.right)).simple i : W) = _
  rw [Dihedral.pairSystem_simple]
  cases i <;> rfl

end PlaneBasis


end
end KLInvariance.TitsSpace

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

namespace ConjugateRange
open Module
universe ur um un
variable {R : Type ur} [CommRing R]
  {M : Type um} [AddCommGroup M] [Module R M]
  {N : Type un} [AddCommGroup N] [Module R N]
  (e : M ≃ₗ[R] N) (f : End R N)
noncomputable section

 def conjugate : End R M := e.symm.toLinearMap.comp (f.comp e.toLinearMap)

 def map : LinearMap.range f →ₗ[R] LinearMap.range (conjugate e f) :=
  (e.symm.toLinearMap.domRestrict f.range).codRestrict _ (by
    rintro ⟨_,n,rfl⟩
    refine ⟨e.symm n,?_⟩
    change e.symm (f (e (e.symm n)))=e.symm (f n)
    rw [LinearEquiv.apply_symm_apply])

 theorem map_bijective : Function.Bijective (map e f) := by
  constructor
  · intro m n h
    apply Subtype.ext
    apply e.symm.injective
    exact congrArg Subtype.val h
  · rintro ⟨_,m,rfl⟩
    refine ⟨⟨f (e m),e m,rfl⟩,?_⟩
    rfl

 def equiv : LinearMap.range f ≃ₗ[R] LinearMap.range (conjugate e f) :=
  LinearEquiv.ofBijective (map e f) (map_bijective e f)

end
end ConjugateRange

end


section

/-! The correct integral summand duality. A chosen summand of a perfectly
paired module is paired with its ADJOINT summand, not with itself by fiat.
This is the algebraic connector for the unresolved BMP summand recognition.
No existence of a BMP summand, or isomorphism with its adjoint, is asserted. -/
namespace AdjointSummandDuality
universe ur um un
variable {R : Type ur} [CommRing R]
  {M : Type um} [AddCommGroup M] [Module R M]
  {N : Type un} [AddCommGroup N] [Module R N]
  (d : M ≃ₗ[R] Module.Dual R M) (i : N →ₗ[R] M) (p : M →ₗ[R] N)
  (hpi : ∀ n, p (i n)=n)
noncomputable section

 def dualSection : Module.Dual R N →ₗ[R] M :=
  d.symm.toLinearMap.comp p.dualMap

 def dualProjection : M →ₗ[R] Module.Dual R N := i.dualMap.comp d.toLinearMap

include hpi in
 theorem projection_section (lam : Module.Dual R N) :
    dualProjection d i (dualSection d p lam)=lam := by
  apply LinearMap.ext
  intro n
  change d (d.symm (p.dualMap lam)) (i n)=lam n
  rw [LinearEquiv.apply_symm_apply]
  change lam (p (i n))=lam n
  rw [hpi]

 def adjointProjector : Module.End R M := (dualSection d p).comp (dualProjection d i)

 def adjointSummand : Submodule R M := LinearMap.range (dualSection d p)

include hpi in
 theorem dualProjection_injective_on_adjoint :
    Function.Injective ((dualProjection d i).domRestrict (adjointSummand d p)) := by
  rintro ⟨m,lam,rfl⟩ ⟨n,mu,rfl⟩ h
  apply Subtype.ext
  change dualSection d p lam=dualSection d p mu
  change dualProjection d i (dualSection d p lam)=dualProjection d i (dualSection d p mu) at h
  rw [projection_section d i p hpi,projection_section d i p hpi] at h
  rw [h]

include hpi in
 theorem dualProjection_surjective_on_adjoint :
    Function.Surjective ((dualProjection d i).domRestrict (adjointSummand d p)) := by
  intro lam
  exact ⟨⟨dualSection d p lam,lam,rfl⟩,projection_section d i p hpi lam⟩

 def adjointEquivDual : adjointSummand d p ≃ₗ[R] Module.Dual R N :=
  LinearEquiv.ofBijective ((dualProjection d i).domRestrict (adjointSummand d p))
    ⟨dualProjection_injective_on_adjoint d i p hpi,dualProjection_surjective_on_adjoint d i p hpi⟩

include hpi in
 theorem adjointProjector_range :
    LinearMap.range (adjointProjector d i p)=adjointSummand d p := by
  apply le_antisymm
  · rintro m ⟨n,rfl⟩
    exact ⟨dualProjection d i n,rfl⟩
  · rintro m ⟨lam,rfl⟩
    refine ⟨dualSection d p lam,?_⟩
    change dualSection d p (dualProjection d i (dualSection d p lam))=dualSection d p lam
    rw [projection_section d i p hpi]

end
end AdjointSummandDuality

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

/-! Balance of a two-sided perfect pairing needs orthogonality on both
sides, not equality of its two integral embeddings into an ambient form. -/
namespace BalancedCuts
universe ur um ua
variable {R : Type ur} [CommRing R] [IsDomain R]
  {M : Type um} [AddCommGroup M] [Module R M]
  {A : Type ua} [AddCommGroup A] [Module R A]
  (d : M →ₗ[R] Module.Dual R M) (π : M →ₗ[R] A) (c : M →ₗ[R] M)
  (p : R) (hp : p≠0) (hπ : ∀ m, π (c m)=p • π m)
  (hleft : ∀ m n, π n=0 → d (c m) n=0)
  (hright : ∀ m n, π m=0 → d m (c n)=0)

include hp hπ hleft hright in
 theorem balanced_two (m n : M) : d (c m) n=d m (c n) := by
  have hn : π (p • n-c n)=0 := by rw [map_sub,map_smul,hπ,sub_self]
  have hm : π (p • m-c m)=0 := by rw [map_sub,map_smul,hπ,sub_self]
  have en := hleft m _ hn
  have em := hright _ n hm
  simp only [map_sub,map_smul,LinearMap.sub_apply,LinearMap.smul_apply,smul_eq_mul,sub_eq_zero] at en em
  exact mul_left_cancel₀ hp (en.trans em.symm)

end BalancedCuts

end


end OAI
end

section
-- module Solutions.OAIQ124_KL.KazhdanLusztig_DyerPaths
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Finite character cancellation, reflection-ratio orders and adapted Dyer decreasing paths.
-/


section


namespace KLInvariance.Dihedral
variable {W : Type*} [Group W] {M : CoxeterMatrix Bool}
noncomputable section

/-- The genuine diagram automorphism of an arbitrary rank-two Coxeter system,
including the infinite one. -/
def swapHom (cs : CoxeterSystem M W) : W →* W :=
  cs.lift ⟨fun i => cs.simple (!i), by
    intro i j
    have he : M i j = M (!i) (!j) := by
      cases i <;> cases j
      · simp
      · exact M.symmetric _ _
      · exact M.symmetric _ _
      · simp
    rw [he]
    exact cs.simple_mul_simple_pow _ _⟩

@[simp] theorem swapHom_simple (cs : CoxeterSystem M W) (i : Bool) :
    swapHom cs (cs.simple i) = cs.simple (!i) := cs.lift_apply_simple _ i

@[simp] theorem swapHom_involutive (cs : CoxeterSystem M W) :
    Function.Involutive (swapHom cs) := by
  intro w
  apply cs.simple_induction w
  · intro i
    simp
  · simp
  · intro a b ha hb
    simp only [map_mul,ha,hb]

def swap (cs : CoxeterSystem M W) : W ≃* W where
  toFun := swapHom cs
  invFun := swapHom cs
  left_inv := swapHom_involutive cs
  right_inv := swapHom_involutive cs
  map_mul' := map_mul (swapHom cs)

@[simp] theorem swap_simple (cs : CoxeterSystem M W) (i : Bool) :
    swap cs (cs.simple i) = cs.simple (!i) := swapHom_simple cs i

@[simp] theorem swap_swap (cs : CoxeterSystem M W) (w : W) :
    swap cs (swap cs w) = w := swapHom_involutive cs w

theorem swap_wordProd (cs : CoxeterSystem M W) (ω : List Bool) :
    swap cs (cs.wordProd ω) = cs.wordProd (ω.map Bool.not) := by
  induction ω with
  | nil => simp
  | cons i ω ih =>
    simp only [cs.wordProd_cons, map_mul, swap_simple, List.map_cons, ih]

@[simp] theorem length_swap (cs : CoxeterSystem M W) (w : W) :
    cs.length (swap cs w) = cs.length w := by
  have hle (z : W) : cs.length (swap cs z) ≤ cs.length z := by
    obtain ⟨ω,hω,rfl⟩ := cs.exists_isReduced z
    rw [swap_wordProd, hω.eq]
    simpa using cs.length_wordProd_le (ω.map Bool.not)
  exact le_antisymm (hle w) (by simpa using hle (swap cs w))

@[simp] theorem descent_swap (cs : CoxeterSystem M W) (w : W) (i : Bool) :
    cs.IsLeftDescent (swap cs w) i ↔ cs.IsLeftDescent w (!i) := by
  unfold CoxeterSystem.IsLeftDescent
  rw [length_swap, ← Bool.not_not i, ← swap_simple, ← map_mul, length_swap]
  simp

end
end KLInvariance.Dihedral

end


section

/-! Geometric orders adapted to a fixed upper vertex. These are honest
ratios of linear functionals, with a strictly positive denominator. They
will be used only as a permissible choice of the source's schedule. -/
namespace KLInvariance.TitsSpace
open Module
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
noncomputable section

local instance instDecidable_solutions_8_r1f31a4_1 (p : Prop) : Decidable p := Classical.propDecidable p
def simplePositive (i : I) : PositiveRoot M cs :=
  ⟨root i, ⟨1,i,by simp⟩, root_nonneg i⟩

@[simp] theorem simplePositive_val (i : I) :
    (simplePositive (M := M) (cs := cs) i).val = root i := rfl

@[simp] theorem rootRef_simplePositive (i : I) :
    rootRef (simplePositive (M := M) (cs := cs) i) = cs.simple i := by
  exact (rootReflection_represents M cs _).reflection_unique ⟨1,i,by simp,by simp⟩

def PositiveFunctional (h : Module.Dual ℝ (I → ℝ)) : Prop := ∀ i, 0 < h (root i)

/-- Both functionals are actual dual vectors; the root order is not a
label-carrying addition to the interval isomorphism. -/
structure RatioOrder where
  denominator : Module.Dual ℝ (I → ℝ)
  numerator : Module.Dual ℝ (I → ℝ)
  positive : PositiveFunctional denominator
  generic : Function.Injective (fun a : PositiveRoot M cs => numerator a.val / denominator a.val)

namespace RatioOrder
variable (O : RatioOrder (M := M) (cs := cs))

local instance instDecidable_solutions_8_r1f31a4_2 (p : Prop) : Decidable p := Classical.propDecidable p
def slope (a : PositiveRoot M cs) : ℝ := O.numerator a.val / O.denominator a.val

end RatioOrder

@[simp] theorem positiveAction_simplePositive (i : I) :
    positiveAction (cs.simple i) (simplePositive (M := M) (cs := cs) i) = simplePositive i := by
  apply Subtype.ext
  rw [positiveAction_eq_of_nonpos]
  · simp only [simplePositive_val,action_simple_root,neg_neg]
  · simpa only [simplePositive_val,action_simple_root,Pi.neg_apply,neg_nonpos] using root_nonneg i

end
end KLInvariance.TitsSpace

end


section

/-! Rank-two path reversal in the actual induced root plane, for every finite
full interval. This is a required Dyer wall-crossing relation, not the Dyer
identification itself. -/
namespace KLInvariance.Dihedral
variable {W : Type*} [Group W] {M : CoxeterMatrix Bool}
noncomputable section

local instance instDecidable_solutions_5_r1f31a4_1 (p : Prop) : Decidable p := Classical.propDecidable p
/-- Switch the two vertices at every strictly internal rank, leaving all
other ranks fixed. The diagram involution supplies the intrinsic switch. -/
def rankFlip (cs : CoxeterSystem M W) (L H : ℕ) (w : W) : W :=
  if L < cs.length w ∧ cs.length w < H then swap cs w else w

@[simp] theorem length_rankFlip (cs : CoxeterSystem M W) (L H : ℕ) (w : W) :
    cs.length (rankFlip cs L H w) = cs.length w := by
  unfold rankFlip
  split <;> simp

@[simp] theorem rankFlip_involutive (cs : CoxeterSystem M W) (L H : ℕ) :
    Function.Involutive (rankFlip cs L H) := by
  intro w
  unfold rankFlip
  split <;> simp_all

@[simp] theorem rankFlip_lower (cs : CoxeterSystem M W) (x y : W) :
    rankFlip cs (cs.length x) (cs.length y) x = x := by simp [rankFlip]

@[simp] theorem rankFlip_upper (cs : CoxeterSystem M W) (x y : W) :
    rankFlip cs (cs.length x) (cs.length y) y = y := by simp [rankFlip]

@[simp] theorem rankFlip_bruhat_iff (cs : CoxeterSystem M W) (L H : ℕ) (x y : W) :
    BruhatLE cs (rankFlip cs L H x) (rankFlip cs L H y) ↔ BruhatLE cs x y := by
  simp only [bruhat_iff_length_lt_or_eq, length_rankFlip,
    (rankFlip_involutive cs L H).injective.eq_iff]

@[simp] theorem rankFlip_step_iff (cs : CoxeterSystem M W) (L H : ℕ) (x y : W) :
    BruhatStep cs (rankFlip cs L H x) (rankFlip cs L H y) ↔ BruhatStep cs x y := by
  simp only [step_iff_odd, length_rankFlip]

/-- An automorphism of the unlabelled full dihedral interval, fixing its ends.
It need not arise from a Coxeter-system automorphism at those ends. -/
def intervalFlip (cs : CoxeterSystem M W) (lo hi : W) :
    Interval cs lo hi ≃o Interval cs lo hi where
  toFun x := ⟨rankFlip cs (cs.length lo) (cs.length hi) x.val, by
    constructor
    · simpa only [rankFlip_lower] using
        (rankFlip_bruhat_iff cs (cs.length lo) (cs.length hi) lo x.val).mpr x.property.1
    · simpa only [rankFlip_upper] using
        (rankFlip_bruhat_iff cs (cs.length lo) (cs.length hi) x.val hi).mpr x.property.2⟩
  invFun x := ⟨rankFlip cs (cs.length lo) (cs.length hi) x.val, by
    constructor
    · simpa only [rankFlip_lower] using
        (rankFlip_bruhat_iff cs (cs.length lo) (cs.length hi) lo x.val).mpr x.property.1
    · simpa only [rankFlip_upper] using
        (rankFlip_bruhat_iff cs (cs.length lo) (cs.length hi) x.val hi).mpr x.property.2⟩
  left_inv x := Subtype.ext (rankFlip_involutive cs _ _ x.val)
  right_inv x := Subtype.ext (rankFlip_involutive cs _ _ x.val)
  map_rel_iff' := rankFlip_bruhat_iff cs _ _ _ _

@[simp] theorem intervalFlip_val (cs : CoxeterSystem M W) (lo hi : W)
    (x : Interval cs lo hi) :
    (intervalFlip cs lo hi x).val = rankFlip cs (cs.length lo) (cs.length hi) x.val := rfl

@[simp] theorem intervalFlip_involutive (cs : CoxeterSystem M W) (lo hi : W) :
    Function.Involutive (intervalFlip cs lo hi) :=
  fun x => Subtype.ext (rankFlip_involutive cs _ _ x.val)

def edgeFlip (cs : CoxeterSystem M W) (lo hi : W) :
    BruhatGraph.Edge cs lo hi ≃ BruhatGraph.Edge cs lo hi where
  toFun e := ⟨(intervalFlip cs lo hi e.val.1, intervalFlip cs lo hi e.val.2),
    (rankFlip_step_iff cs _ _ _ _).mpr e.property⟩
  invFun e := ⟨(intervalFlip cs lo hi e.val.1, intervalFlip cs lo hi e.val.2),
    (rankFlip_step_iff cs _ _ _ _).mpr e.property⟩
  left_inv e := Subtype.ext (Prod.ext
    (intervalFlip_involutive cs lo hi e.val.1)
    (intervalFlip_involutive cs lo hi e.val.2))
  right_inv e := Subtype.ext (Prod.ext
    (intervalFlip_involutive cs lo hi e.val.1)
    (intervalFlip_involutive cs lo hi e.val.2))

@[simp] theorem edgeFlip_source (cs : CoxeterSystem M W) (lo hi : W)
    (e : BruhatGraph.Edge cs lo hi) :
    BruhatGraph.source cs lo hi (edgeFlip cs lo hi e) =
      intervalFlip cs lo hi (BruhatGraph.source cs lo hi e) := rfl

@[simp] theorem edgeFlip_target (cs : CoxeterSystem M W) (lo hi : W)
    (e : BruhatGraph.Edge cs lo hi) :
    BruhatGraph.target cs lo hi (edgeFlip cs lo hi e) =
      intervalFlip cs lo hi (BruhatGraph.target cs lo hi e) := rfl

end
end KLInvariance.Dihedral

namespace KLInvariance.SchedulePaths
open scoped BigOperators
variable {V E R : Type*} (source target : E → V)
noncomputable section
local instance instDecidable_solutions_1 (p : Prop) : Decidable p := Classical.propDecidable p

/-- The finite set of genuine directed paths selected by an edge schedule. -/
def subpaths (schedule : List E) (x y : V) : Finset (List E) :=
  schedule.sublists'.toFinset.filter (IsPath source target x y)

@[simp] theorem mem_subpaths (schedule : List E) (x y : V) (p : List E) :
    p ∈ subpaths source target schedule x y ↔
      p.Sublist schedule ∧ IsPath source target x y p := by
  simp [subpaths, List.mem_sublists']

end
end KLInvariance.SchedulePaths

end


section

/-! Genuine Dyer identification for geometric orders adapted to a fixed top.
The path values below are defined from actual reflection edges; equality with
`Hecke.rTilde` will be proved by its genuine simple-descent recurrence. -/
namespace KLInvariance.AdaptedDyer
open TitsSpace SchedulePaths
open scoped BigOperators
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] (cs : CoxeterSystem M W)
noncomputable section
local instance instDecidable_solutions (p : Prop) : Decidable p := Classical.propDecidable p

abbrev Edge := {e : W × W // BruhatStep cs e.1 e.2}
def source (e : Edge cs) : W := e.val.1
def target (e : Edge cs) : W := e.val.2
def rootLabel (e : Edge cs) : PositiveRoot M cs := graphRoot e.property

@[simp] theorem rootRef_rootLabel (e : Edge cs) :
    rootRef (rootLabel cs e) = target cs e * (source cs e)⁻¹ := by
  exact congrArg Subtype.val ((positiveRootEquiv M cs).left_inv
    ⟨e.val.2 * e.val.1⁻¹,e.property.label_reflection⟩)

variable {cs}
def score (O : RatioOrder (M := M) (cs := cs)) (e : Edge cs) : ℝ :=
  O.slope (rootLabel cs e)

variable (cs)
def edgeFinset (b : W) : Finset (Edge cs) :=
  let P := ((lowerFinset cs b).product (lowerFinset cs b)).filter
    (fun e => BruhatStep cs e.1 e.2)
  P.attach.image (fun e => (⟨e.val,by
    exact (Finset.mem_filter.mp e.property).2⟩ : Edge cs))

omit [Fintype I] in
@[simp] theorem mem_edgeFinset (b : W) (e : Edge cs) :
    e ∈ edgeFinset cs b ↔ BruhatLE cs (target cs e) b := by
  unfold edgeFinset
  constructor
  · intro h
    obtain ⟨p,_,he⟩ := Finset.mem_image.mp h
    subst e
    exact (mem_lowerFinset cs b p.val.2).mp
      (Finset.mem_product.mp (Finset.mem_filter.mp p.property).1).2
  · intro h
    apply Finset.mem_image.mpr
    have hx : BruhatLE cs (source cs e) b := (show BruhatLE cs (source cs e) (target cs e) from .single e.property).trans h
    refine ⟨⟨e.val,Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨(mem_lowerFinset cs b _).mpr hx,(mem_lowerFinset cs b _).mpr h⟩,e.property⟩⟩,
      Finset.mem_attach _ _,?_⟩
    rfl

variable {cs}
def schedule (O : RatioOrder (M := M) (cs := cs)) (b : W) : List (Edge cs) :=
  (edgeFinset cs b).toList.mergeSort (fun e f => score O e ≤ score O f)

@[simp] theorem mem_schedule (O : RatioOrder (M := M) (cs := cs)) (b : W) (e : Edge cs) :
    e ∈ schedule O b ↔ BruhatLE cs (target cs e) b := by
  simp [schedule]

variable (cs)

variable {cs}
def paths (O : RatioOrder (M := M) (cs := cs)) (x y : W) : Finset (List (Edge cs)) :=
  subpaths (source cs) (target cs) (schedule O y) x y

def polynomial (O : RatioOrder (M := M) (cs := cs)) (x y : W) : Polynomial ℤ :=
  ∑ p ∈ paths O x y, Polynomial.X ^ p.length


variable (cs)

/-- On a non-simple-labelled edge this is actual left multiplication by s.
Simple-labelled edges are fixed merely to make the extension a total involution;
all path uses below exclude them before applying this map. -/
def rotateEdge (i : I) (e : Edge cs) : Edge cs :=
  if h : target cs e = cs.simple i * source cs e then e else
    ⟨(cs.simple i * source cs e,cs.simple i * target cs e),
      bruhatStep_simple_mul cs e.property i h⟩

variable {cs}
def Nonsimple (i : I) (p : List (Edge cs)) : Prop :=
  ∀ e ∈ p, rootLabel cs e ≠ simplePositive i

def nonsimplePaths (O : RatioOrder (M := M) (cs := cs)) (i : I) (x y : W) :
    Finset (List (Edge cs)) := (paths O x y).filter (Nonsimple i)


variable (cs)
def simpleEdge (i : I) (x : W) (hx : cs.length x < cs.length (cs.simple i*x)) : Edge cs :=
  ⟨(x,cs.simple i*x),hx,cs.simple i,cs.isReflection_simple i,rfl⟩

omit [Fintype I] in
@[simp] theorem simpleEdge_source (i : I) (x : W) (hx : cs.length x < cs.length (cs.simple i*x)) :
    source cs (simpleEdge cs i x hx) = x := rfl

omit [Fintype I] in
@[simp] theorem simpleEdge_target (i : I) (x : W) (hx : cs.length x < cs.length (cs.simple i*x)) :
    target cs (simpleEdge cs i x hx) = cs.simple i*x := rfl

end
end KLInvariance.AdaptedDyer

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

/-! Linear coordinates on the actual normalized root line. These give the
rank-two geometry of finite wall crossings for genuine root schedules. -/
namespace KLInvariance.TitsSpace
open Module
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
noncomputable section

local instance instDecidable_solutions_9_r1f31a4_1 (p : Prop) : Decidable p := Classical.propDecidable p
@[simp] theorem normalizedRoot_height (a : PositiveRoot M cs) :
    height (normalizedRoot a) = 1 := by
  simp [normalizedRoot,a.height_pos.ne']

end
end KLInvariance.TitsSpace

end


section

/-! Localization of genuine directed paths in a maximal root-plane coset.
The full relative interval is proved to contain every such path. -/
namespace KLInvariance.TitsSpace.PlaneBasis
open Module SchedulePaths
open AdaptedDyer
universe u v
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
  {P : Submodule ℝ (I → ℝ)} (B : PlaneBasis (M := M) (cs := cs) P)
noncomputable section

local instance instDecidable_2_r1f31a4_1 (p : Prop) : Decidable p := Classical.propDecidable p
def intervalToAmbient {a₀ : W} {g k : planeSubgroup M cs P}
    (z : Interval B.system g k) : W := (z.val:W)*a₀

end
end KLInvariance.TitsSpace.PlaneBasis

end


end OAI
end


