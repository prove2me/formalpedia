-- Prove2me | solution 1 for AronszajnRK.Inclusion.subclass_of_dominated
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-05T00:58:29.70997+00:00
-- url     : https://prove2.me/submissions/cb006e91-a3c3-4683-b9f9-fce134dacf8d

import Mathlib
import Definitions.Def_AronszajnRK_Sum_kernelFn
import Definitions.Def_AronszajnRK_Limits_KernelLE

/-!
# Aronszajn §7, Theorem I: `K₁ ≪ K` implies `F₁ ⊂ F` contractively

If `K₁ ≪ K` in the kernel order (i.e. `K − K₁` is a positive matrix), then every function of
the RKHS `H₁` of `K₁` is a function of the RKHS `H` of `K`, and the `H`-norm is dominated by
the `H₁`-norm.

## Proof

The kernel inequality says that the quadratic form of `K` dominates that of `K₁` on every
finitely supported family. Since inner products of kernel-section combinations are exactly
these quadratic forms, the map `U₀` sending an `H`-section combination `∑ a x • K(·,x)` to the
`H₁`-section combination `∑ a x • K₁(·,x)` is norm-decreasing on a dense subspace of `H`.
It therefore extends to a contraction `U : H →L[ℂ] H₁` (`LinearMap.extendOfNorm`). The
adjoint `T = U*` then satisfies the reproducing identity `⟪T g₁, K(·,x)⟫ = ⟪g₁, K₁(·,x)⟫₁`,
so `T g₁` is an element of `H` whose function is `g₁`; and the duality bound
`‖U* g₁‖² = ⟪g₁, U U* g₁⟫ ≤ ‖g₁‖·‖U U* g₁‖ ≤ ‖g₁‖·‖U* g₁‖` gives `‖U* g₁‖ ≤ ‖g₁‖`.
-/

open Filter Topology
open scoped ComplexOrder

namespace AronszajnRK.Inclusion

section Sections

variable {X H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [RKHS ℂ H X ℂ]

/-- The linear map `a ↦ ∑ a x • K(·,x)` from finitely supported families to `H`. -/
noncomputable def sectionMap : (X →₀ ℂ) →ₗ[ℂ] H :=
  Finsupp.linearCombination ℂ (fun x => RKHS.kerFun H x 1)

lemma sectionMap_apply (a : X →₀ ℂ) :
    sectionMap (H := H) a = a.sum (fun x c => c • RKHS.kerFun H x 1) :=
  Finsupp.linearCombination_apply ℂ a

lemma sectionMap_single (x : X) :
    sectionMap (H := H) (Finsupp.single x 1) = RKHS.kerFun H x 1 := by
  rw [sectionMap_apply]
  simp

/-- Inner product of two kernel sections in terms of the scalar kernel. -/
lemma inner_kerFun_one (x y : X) :
    inner ℂ (RKHS.kerFun H x 1) (RKHS.kerFun H y 1) = AronszajnRK.Sum.kernelFn H x y := by
  rw [RKHS.kerFun_inner x 1 (RKHS.kerFun H y 1), RKHS.kerFun_apply]
  simp [AronszajnRK.Sum.kernelFn]

/-- Inner products of combinations are finite quadratic forms of the scalar kernel. -/
lemma inner_sectionMap (a b : X →₀ ℂ) :
    inner ℂ (sectionMap (H := H) a) (sectionMap (H := H) b)
      = a.sum (fun i ai => b.sum (fun j bj => star ai * AronszajnRK.Sum.kernelFn H i j * bj)) := by
  classical
  have e1 : inner ℂ (sectionMap (H := H) a) (sectionMap (H := H) b)
      = ∑ i ∈ a.support, inner ℂ (a i • RKHS.kerFun H i 1) (sectionMap (H := H) b) := by
    rw [sectionMap_apply]
    simp only [Finsupp.sum]
    exact sum_inner _ _ _
  have e2 : ∀ i ∈ a.support, inner ℂ (a i • RKHS.kerFun H i 1) (sectionMap (H := H) b)
      = ∑ j ∈ b.support, inner ℂ (a i • RKHS.kerFun H i 1) (b j • RKHS.kerFun H j 1) := by
    intro i _
    rw [sectionMap_apply]
    simp only [Finsupp.sum]
    exact inner_sum _ _ _
  rw [e1]
  refine Finset.sum_congr rfl fun i hi => (e2 i hi).trans ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [inner_smul_left, inner_smul_right, inner_kerFun_one]
  simp [mul_comm, mul_assoc, mul_left_comm]

/-- The range of the section-combination map is dense. -/
lemma denseRange_sectionMap : DenseRange (sectionMap (H := H)) := by
  rw [denseRange_iff_closure_range]
  have h3 := RKHS.kerFun_dense (𝕜 := ℂ) (H := H) (X := X) (V := ℂ)
  have hc := congrArg (fun p : Submodule ℂ H => (p : Set H)) h3
  have hc' : closure (((Submodule.span ℂ {RKHS.kerFun H x v | (x) (v)}) : Submodule ℂ H) : Set H)
      = ((⊤ : Submodule ℂ H) : Set H) := hc
  have hset : closure (((Submodule.span ℂ {RKHS.kerFun H x v | (x) (v)}) : Submodule ℂ H) : Set H)
      = Set.univ := hc'.trans (Set.eq_univ_iff_forall.mpr fun z => SetLike.mem_coe.mpr Submodule.mem_top)
  have hspan : (Submodule.span ℂ {RKHS.kerFun H x v | (x) (v)} : Submodule ℂ H)
      = Submodule.span ℂ (Set.range fun x => RKHS.kerFun H x 1) := by
    refine le_antisymm ?_ ?_
    · refine Submodule.span_le.mpr fun v hv => ?_
      rcases hv with ⟨x, v, rfl⟩
      have hv' : RKHS.kerFun H x v = v • RKHS.kerFun H x 1 := by
        rw [← map_smul (RKHS.kerFun H x) v (1 : ℂ)]
        simp [smul_eq_mul]
      rw [hv']
      exact Submodule.smul_mem _ v (Submodule.subset_span ⟨x, rfl⟩)
    · refine Submodule.span_le.mpr fun v hv => ?_
      rcases hv with ⟨x, rfl⟩
      exact Submodule.subset_span ⟨x, 1, rfl⟩
  rw [show Set.range ⇑(sectionMap (H := H))
      = ((LinearMap.range (sectionMap (H := H)) : Submodule ℂ H) : Set H) from (LinearMap.coe_range _).symm]
  show closure (((Finsupp.linearCombination ℂ (fun x => RKHS.kerFun H x 1)).range : Submodule ℂ H) : Set H) = Set.univ
  rw [Finsupp.range_linearCombination ℂ, ← hspan]
  exact hset

end Sections


/-- Splitting a quadratic form of a difference of kernels. -/
lemma qf_sub {X : Type*} (P Q : X → X → ℂ) (b : X →₀ ℂ) :
    b.sum (fun i bi => b.sum (fun j bj => star bi * (P i j - Q i j) * bj))
      = b.sum (fun i bi => b.sum (fun j bj => star bi * P i j * bj))
        - b.sum (fun i bi => b.sum (fun j bj => star bi * Q i j * bj)) := by
  classical
  simp only [Finsupp.sum]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

section Dominated

/-- Aronszajn, *Theory of Reproducing Kernels*, Trans. Amer. Math. Soc. 68 (1950), §7, Theorem I,
p. 354 (PDF p. 18). If `K` and `K₁` are the reproducing kernels of the classes `F` and `F₁` with
the norms `‖ ‖`, `‖ ‖₁`, and if `K₁ ≪ K`, then `F₁ ⊂ F` and `‖f₁‖₁ ≥ ‖f₁‖` for every `f₁ ∈ F₁`.
The classes are complex RKHSs `H` (norm `‖ ‖`) and `H₁` (norm `‖ ‖₁`) of functions on `X`; the norm
comparison is between the elements of `H₁` and of `H` carrying the same function. -/
theorem subclass_of_dominated {X H H₁ : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [RKHS ℂ H X ℂ]
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁] [RKHS ℂ H₁ X ℂ]
    (hK : AronszajnRK.Limits.KernelLE (AronszajnRK.Sum.kernelFn H₁) (AronszajnRK.Sum.kernelFn H)) :
    Set.range (fun f₁ : H₁ => ⇑f₁) ⊆ Set.range (fun f : H => ⇑f) ∧
      ∀ (f₁ : H₁) (f : H), ⇑f = ⇑f₁ → ‖f‖ ≤ ‖f₁‖ := by
  classical
  obtain ⟨_, hpsd⟩ := hK
  simp only [Matrix.sub_apply, Matrix.of_apply] at hpsd
  -- the section-combination maps are comparable in norm
  have hbound : ∀ a : X →₀ ℂ,
      ‖sectionMap (H := H₁) a‖ ≤ (1 : ℝ) * ‖sectionMap (H := H) a‖ := by
    intro a
    have hqf : (‖sectionMap (H := H₁) a‖ : ℝ) ^ 2 ≤ ‖sectionMap (H := H) a‖ ^ 2 := by
      have hn₁ : (‖sectionMap (H := H₁) a‖ : ℝ) ^ 2
          = Complex.re (a.sum (fun i ai =>
              a.sum (fun j aj => star ai * AronszajnRK.Sum.kernelFn H₁ i j * aj))) := by
        have h := (inner_self_eq_norm_sq (𝕜 := ℂ) (sectionMap (H := H₁) a))
        rw [inner_sectionMap a a] at h
        exact h.symm
      have hn : (‖sectionMap (H := H) a‖ : ℝ) ^ 2
          = Complex.re (a.sum (fun i ai =>
              a.sum (fun j aj => star ai * AronszajnRK.Sum.kernelFn H i j * aj))) := by
        have h := (inner_self_eq_norm_sq (𝕜 := ℂ) (sectionMap (H := H) a))
        rw [inner_sectionMap a a] at h
        exact h.symm
      have hsplit := qf_sub (AronszajnRK.Sum.kernelFn H) (AronszajnRK.Sum.kernelFn H₁) a
      have hz : (0 : ℂ) ≤ a.sum (fun i ai =>
              a.sum (fun j aj => star ai * AronszajnRK.Sum.kernelFn H i j * aj))
          - a.sum (fun i ai =>
              a.sum (fun j aj => star ai * AronszajnRK.Sum.kernelFn H₁ i j * aj)) := by
        rw [← hsplit]; exact hpsd a
      obtain ⟨hre, _⟩ := Complex.nonneg_iff.mp hz
      rw [Complex.sub_re] at hre
      rw [hn₁, hn]
      linarith
    have e1 : (0 : ℝ) ≤ ‖sectionMap (H := H₁) a‖ := norm_nonneg _
    have e2 : (0 : ℝ) ≤ ‖sectionMap (H := H) a‖ := norm_nonneg _
    have hle : ‖sectionMap (H := H₁) a‖ ≤ ‖sectionMap (H := H) a‖ := by
      nlinarith [hqf, e1, e2]
    linarith
  -- the extension to a contraction H →L H₁
  have hdense : DenseRange (sectionMap (H := H)) := denseRange_sectionMap
  set U : H →L[ℂ] H₁ := LinearMap.extendOfNorm (sectionMap (H := H₁)) (sectionMap (H := H)) with hU
  have hUsec : ∀ a : X →₀ ℂ, U (sectionMap (H := H) a) = sectionMap (H := H₁) a :=
    LinearMap.extendOfNorm_eq hdense ⟨1, hbound⟩
  have hUnorm : ∀ z : H, ‖U z‖ ≤ (1 : ℝ) * ‖z‖ :=
    LinearMap.norm_extendOfNorm_apply_le hdense 1 hbound
  -- the reproducing identity for the adjoint
  have hrepro : ∀ (g₁ : H₁) (x : X), (U.adjoint g₁) x = g₁ x := by
    intro g₁ x
    have h1 : (U.adjoint g₁) x
        = inner ℂ (RKHS.kerFun H x 1) (U.adjoint g₁) := by
      rw [RKHS.kerFun_inner x 1 (U.adjoint g₁)]
      simp
    have h2 : inner ℂ (RKHS.kerFun H x 1) (U.adjoint g₁)
        = inner ℂ (RKHS.kerFun H₁ x 1) g₁ := by
      rw [ContinuousLinearMap.adjoint_inner_right U (RKHS.kerFun H x 1) g₁,
        ← sectionMap_single (H := H) x, hUsec, sectionMap_single (H := H₁) x]
    have h3 : inner ℂ (RKHS.kerFun H₁ x 1) g₁ = g₁ x := by
      rw [RKHS.kerFun_inner x 1 g₁]
      simp
    rw [h1, h2, h3]
  -- the duality bound for the adjoint
  have hstar : ∀ g₁ : H₁, ‖U.adjoint g₁‖ ≤ ‖g₁‖ := by
    intro g₁
    by_cases h0 : ‖U.adjoint g₁‖ = 0
    · rw [h0]; exact norm_nonneg _
    · have hpos : (0 : ℝ) < ‖U.adjoint g₁‖ :=
        lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
      have hsq : ‖U.adjoint g₁‖ ^ 2 ≤ ‖g₁‖ * ‖U.adjoint g₁‖ := by
        have e1 : ‖U.adjoint g₁‖ ^ 2
            = Complex.re (inner ℂ (U.adjoint g₁) (U.adjoint g₁)) :=
          (inner_self_eq_norm_sq (𝕜 := ℂ) _).symm
        have e2 : inner ℂ (U.adjoint g₁) (U.adjoint g₁)
            = inner ℂ g₁ (U (U.adjoint g₁)) :=
          ContinuousLinearMap.adjoint_inner_left U (U.adjoint g₁) g₁
        have e3 : Complex.re (inner ℂ g₁ (U (U.adjoint g₁)))
            ≤ ‖inner ℂ g₁ (U (U.adjoint g₁))‖ := Complex.re_le_norm _
        have e4 : ‖inner ℂ g₁ (U (U.adjoint g₁))‖ ≤ ‖g₁‖ * ‖U (U.adjoint g₁)‖ :=
          norm_inner_le_norm g₁ _
        have e5 : ‖U (U.adjoint g₁)‖ ≤ (1 : ℝ) * ‖U.adjoint g₁‖ := hUnorm _
        have e6 : ‖U (U.adjoint g₁)‖ ≤ ‖U.adjoint g₁‖ := by simpa using e5
        calc ‖U.adjoint g₁‖ ^ 2 = Complex.re (inner ℂ g₁ (U (U.adjoint g₁))) := by
              rw [e1, e2]
          _ ≤ ‖inner ℂ g₁ (U (U.adjoint g₁))‖ := e3
          _ ≤ ‖g₁‖ * ‖U (U.adjoint g₁)‖ := e4
          _ ≤ ‖g₁‖ * ‖U.adjoint g₁‖ := by nlinarith [e6, norm_nonneg g₁]
      nlinarith [hpos, norm_nonneg g₁]
  -- assemble the two conclusions
  refine ⟨?_, ?_⟩
  · rintro _ ⟨g₁, rfl⟩
    exact ⟨U.adjoint g₁, funext fun x => hrepro g₁ x⟩
  · intro f₁ f hf
    have hfe : f = U.adjoint f₁ := RKHS.ext fun x => by
      rw [show f x = f₁ x from congrFun hf x, hrepro f₁ x]
    rw [hfe]
    exact hstar f₁

end Dominated

end AronszajnRK.Inclusion

/-- Solution entry point. -/
theorem solution {X H H₁ : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [RKHS ℂ H X ℂ]
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁] [RKHS ℂ H₁ X ℂ]
    (hK : AronszajnRK.Limits.KernelLE (AronszajnRK.Sum.kernelFn H₁) (AronszajnRK.Sum.kernelFn H)) :
    Set.range (fun f₁ : H₁ => ⇑f₁) ⊆ Set.range (fun f : H => ⇑f) ∧
      ∀ (f₁ : H₁) (f : H), ⇑f = ⇑f₁ → ‖f‖ ≤ ‖f₁‖ :=
  AronszajnRK.Inclusion.subclass_of_dominated hK
