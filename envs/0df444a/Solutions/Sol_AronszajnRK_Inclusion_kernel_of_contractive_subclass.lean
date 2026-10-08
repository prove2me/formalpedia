-- Prove2me | solution 1 for AronszajnRK.Inclusion.kernel_of_contractive_subclass
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-05T07:21:42.456178+00:00
-- url     : https://prove2.me/submissions/9cbfd77d-8ecc-4bd7-9782-c5ad7526f594

import Mathlib.Analysis.InnerProductSpace.Reproducing
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Order
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Topology.Basic
import Mathlib.Tactic
import Definitions.Def_AronszajnRK_Sum_kernelFn
import Definitions.Def_AronszajnRK_Limits_KernelLE

open Filter Topology
open scoped ComplexOrder

namespace AronszajnRK.Inclusion

section Sections

variable {X H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [RKHS ℂ H X ℂ]

noncomputable def sectionMap : (X →₀ ℂ) →ₗ[ℂ] H :=
  Finsupp.linearCombination ℂ (fun x => RKHS.kerFun H x 1)

lemma sectionMap_apply (a : X →₀ ℂ) :
    sectionMap (H := H) a = a.sum (fun x c => c • RKHS.kerFun H x 1) :=
  Finsupp.linearCombination_apply ℂ a

lemma sectionMap_single (x : X) :
    sectionMap (H := H) (Finsupp.single x 1) = RKHS.kerFun H x 1 := by
  rw [sectionMap_apply]
  simp

lemma inner_kerFun_one (x y : X) :
    inner ℂ (RKHS.kerFun H x 1) (RKHS.kerFun H y 1) = AronszajnRK.Sum.kernelFn H x y := by
  rw [RKHS.kerFun_inner x 1 (RKHS.kerFun H y 1), RKHS.kerFun_apply]
  simp [AronszajnRK.Sum.kernelFn]

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

section Transfer

variable {X H H₁ : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [RKHS ℂ H X ℂ] [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
  [RKHS ℂ H₁ X ℂ]

noncomputable def transfer (hsub : Set.range (fun f₁ : H₁ => ⇑f₁) ⊆ Set.range (fun f : H => ⇑f)) :
    H₁ → H :=
  fun f₁ => Classical.choose (hsub ⟨f₁, rfl⟩)

lemma transfer_apply (hsub : Set.range (fun f₁ : H₁ => ⇑f₁) ⊆ Set.range (fun f : H => ⇑f))
    (f₁ : H₁) (x : X) : (transfer hsub f₁) x = f₁ x :=
  congrFun (Classical.choose_spec (hsub ⟨f₁, rfl⟩)) x

end Transfer

theorem normBoundAux {X H H₁ : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [RKHS ℂ H X ℂ]
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁] [RKHS ℂ H₁ X ℂ]
    (hsub : Set.range (fun f₁ : H₁ => ⇑f₁) ⊆ Set.range (fun f : H => ⇑f)) :
    ∃ M : ℝ, 0 < M ∧ ∀ (f₁ : H₁) (f : H), ⇑f = ⇑f₁ → ‖f‖ ≤ M * ‖f₁‖ := by
  classical

  have key : ∀ (f₁ : H₁) (x : X), (transfer hsub f₁) x = f₁ x := transfer_apply hsub
  have addval : ∀ (f g : H₁) (x : X), ((f + g : H₁)) x = f x + g x := by
    intro f g x
    simpa using congrFun (RKHS.coe_add f g) x
  have smulval : ∀ (c : ℂ) (f : H₁) (x : X), ((c • f : H₁)) x = c * f x := by
    intro c f x
    simpa [Pi.smul_apply] using congrFun (RKHS.coe_smul f c) x

  have hadd : ∀ a b : H₁, transfer hsub (a + b) = transfer hsub a + transfer hsub b := by
    intro a b
    have e : ∀ x : X, (transfer hsub (a + b)) x = (transfer hsub a + transfer hsub b) x := by
      intro x
      calc (transfer hsub (a + b)) x = (a + b : H₁) x := key (a + b) x
        _ = a x + b x := addval a b x
        _ = (transfer hsub a) x + (transfer hsub b) x := by rw [key, key]
        _ = (transfer hsub a + transfer hsub b) x := by
            rw [show (transfer hsub a + transfer hsub b) x
                = (transfer hsub a) x + (transfer hsub b) x from by
              rw [RKHS.coe_add, Pi.add_apply]]
    exact RKHS.ext e
  have hzero : transfer hsub 0 = 0 := by
    have e : ∀ x : X, (transfer hsub 0) x = (0 : H) x := by
      intro x
      rw [key]
      simp [RKHS.coe_zero]
    exact RKHS.ext e
  have hsmul : ∀ (c : ℂ) (a : H₁), transfer hsub (c • a) = c • transfer hsub a := by
    intro c a
    have e : ∀ x : X, (transfer hsub (c • a)) x = (c • transfer hsub a) x := by
      intro x
      calc (transfer hsub (c • a)) x = (c • a : H₁) x := key (c • a) x
        _ = c * a x := smulval c a x
        _ = (c • transfer hsub a) x := by
            rw [show (c • transfer hsub a) x = c * (transfer hsub a) x from by
              rw [RKHS.coe_smul, Pi.smul_apply, smul_eq_mul]]
            rw [key]
    exact RKHS.ext e
  let L : H₁ →ₗ[ℂ] H :=
    { toFun := transfer hsub, map_add' := hadd, map_smul' := fun c a => hsmul c a }

  have hgraph : ∀ (u : ℕ → H₁) (a : H₁) (b : H),
      Filter.Tendsto u Filter.atTop (𝓝 a) → Filter.Tendsto (fun n => L (u n)) Filter.atTop (𝓝 b) → b = L a := by
    intro u a b hu hy
    apply RKHS.ext (f := b) (g := L a)
    intro x₀
    have h1 : Filter.Tendsto (fun n => (u n) x₀) Filter.atTop (𝓝 (a x₀)) :=
      ((RKHS.continuous_eval (𝕜 := ℂ) (H := H₁) x₀).tendsto a).comp hu
    have h2 : Filter.Tendsto (fun n => (L (u n)) x₀) Filter.atTop (𝓝 (b x₀)) :=
      ((RKHS.continuous_eval (𝕜 := ℂ) (H := H) x₀).tendsto b).comp hy
    have h3 : ∀ n, (L (u n)) x₀ = (u n) x₀ := fun n => key (u n) x₀
    rw [funext h3] at h2
    have h4 : (L a) x₀ = a x₀ := key a x₀
    rw [h4]
    exact tendsto_nhds_unique h2 h1
  have hcont : Continuous L := L.continuous_of_seq_closed_graph hgraph
  obtain ⟨C, hC₀, hC⟩ := SemilinearMapClass.bound_of_continuous L hcont
  refine ⟨C, hC₀, fun f₁ f hf => ?_⟩
  have hf' : f = L f₁ := RKHS.ext fun x => (congrFun hf x).trans (key f₁ x).symm
  calc ‖f‖ = ‖L f₁‖ := by rw [hf']
    _ ≤ C * ‖f₁‖ := hC f₁

lemma kernelFn_conj_symm {X H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [RKHS ℂ H X ℂ] (x y : X) :
    AronszajnRK.Sum.kernelFn H x y = star (AronszajnRK.Sum.kernelFn H y x) := by
  rw [← inner_kerFun_one x y, ← inner_kerFun_one y x]
  exact (inner_conj_symm (𝕜 := ℂ) (RKHS.kerFun H x 1) (RKHS.kerFun H y 1)).symm

lemma inner_left_sectionMap {X H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [RKHS ℂ H X ℂ] (g : H) (a : X →₀ ℂ) :
    inner ℂ g (sectionMap (H := H) a) = a.sum (fun x c => c * star (g x)) := by
  classical
  rw [sectionMap_apply]
  simp only [Finsupp.sum]
  rw [inner_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_smul_right, RKHS.inner_kerFun]
  simp

lemma qf_const_smul {X : Type*} (m : ℂ) (K : X → X → ℂ) (b : X →₀ ℂ) :
    b.sum (fun i bi => b.sum (fun j bj => star bi * (m * K i j) * bj))
      = m * b.sum (fun i bi => b.sum (fun j bj => star bi * K i j * bj)) := by
  classical
  simp only [Finsupp.sum]
  rw [show (∑ i ∈ b.support, ∑ x ∈ b.support, star (b i) * (m * K i x) * b x)
        = m * ∑ i ∈ b.support, ∑ x ∈ b.support, star (b i) * K i x * b x from by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring]


/-- Inner products of finite combinations of an arbitrary family. -/
lemma inner_family {X M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M]
    (u : X → M) (v w : X →₀ ℂ) :
    inner ℂ (v.sum (fun i ci => ci • u i)) (w.sum (fun j cj => cj • u j))
      = v.sum (fun i ci => w.sum (fun j cj => star ci * inner ℂ (u i) (u j) * cj)) := by
  classical
  have e1 : inner ℂ (v.sum (fun i ci => ci • u i)) (w.sum (fun j cj => cj • u j))
      = ∑ i ∈ v.support, inner ℂ ((fun i ci => ci • u i) i (v i))
          (w.sum (fun j cj => cj • u j)) := by
    rw [Finsupp.sum]
    exact sum_inner _ _ _
  have e2 : ∀ i ∈ v.support, inner ℂ ((fun (i : X) (ci : ℂ) => ci • u i) i (v i))
      (w.sum (fun j cj => cj • u j))
      = ∑ j ∈ w.support, inner ℂ ((fun (i : X) (ci : ℂ) => ci • u i) i (v i))
          ((fun (j : X) (cj : ℂ) => cj • u j) j (w j)) := by
    intro i _
    rw [Finsupp.sum]
    exact inner_sum _ _ _
  rw [e1]
  refine Finset.sum_congr rfl fun i hi => (e2 i hi).trans ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [inner_smul_left, inner_smul_right]
  show star (v i) * (w j * inner ℂ (u i) (u j))
      = star (v i) * inner ℂ (u i) (u j) * w j
  ring

/-- Aronszajn §7, Theorem II: a contractively embedded Hilbert subclass of an RKHS has a
reproducing kernel dominated by the ambient kernel. -/
theorem kernel_of_contractive_subclass {X H H₁ : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [RKHS ℂ H X ℂ]
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
    (ι : H₁ →ₗ[ℂ] (X → ℂ)) (hι : Function.Injective ι)
    (hsub : ∀ f₁ : H₁, ∃ f : H, ⇑f = ι f₁)
    (hnorm : ∀ (f₁ : H₁) (f : H), ⇑f = ι f₁ → ‖f‖ ≤ ‖f₁‖) :
    ∃ k₁ : X → H₁, (∀ (y : X) (f₁ : H₁), inner ℂ (k₁ y) f₁ = ι f₁ y) ∧
      AronszajnRK.Limits.KernelLE (fun x y => ι (k₁ y) x) (AronszajnRK.Sum.kernelFn H) := by
  classical
  -- boundedness of the evaluation functionals on H1
  have hbnd : ∀ (y : X) (f₁ : H₁), ‖ι f₁ y‖ ≤ ‖f₁‖ * Real.sqrt ‖RKHS.kernel H y y‖ := by
    intro y f₁
    obtain ⟨f, hf⟩ := hsub f₁
    have h1 := RKHS.norm_apply_le f y
    have h2 : ‖f‖ ≤ ‖f₁‖ := hnorm f₁ f hf
    have h3 : f y = ι f₁ y := congrFun hf y
    rw [h3] at h1
    calc ‖ι f₁ y‖ ≤ ‖f‖ * Real.sqrt ‖RKHS.kernel H y y‖ := h1
      _ ≤ ‖f₁‖ * Real.sqrt ‖RKHS.kernel H y y‖ :=
          mul_le_mul_of_nonneg_right h2 (Real.sqrt_nonneg _)
  have hfun : ∀ (y : X), ∃ (φ : H₁ →L[ℂ] ℂ), ∀ f₁ : H₁, φ f₁ = ι f₁ y := by
    intro y
    refine ⟨LinearMap.mkContinuous
      ({ toFun := fun f₁ => ι f₁ y,
         map_add' := by
           intro p q
           simp [map_add, Pi.add_apply],
         map_smul' := by
           intro c p
           simp [map_smul, Pi.smul_apply, smul_eq_mul] } : H₁ →ₗ[ℂ] ℂ)
      (Real.sqrt ‖RKHS.kernel H y y‖) (fun f₁ => by rw [mul_comm]; exact hbnd y f₁),
      fun f₁ => rfl⟩
  choose φ hφ using hfun
  obtain ⟨k₁, hrep⟩ : ∃ k₁ : X → H₁, ∀ (y : X) (f₁ : H₁), inner ℂ (k₁ y) f₁ = ι f₁ y := by
    refine ⟨fun y => (InnerProductSpace.toDual ℂ H₁).symm (φ y), fun y f₁ => ?_⟩
    show inner ℂ ((InnerProductSpace.toDual ℂ H₁).symm (φ y)) f₁ = ι f₁ y
    exact InnerProductSpace.toDual_symm_apply (𝕜 := ℂ) (E := H₁) (x := f₁) (y := φ y)
      |>.trans (hφ y f₁)
  have hK₁ : ∀ (x y : X), ι (k₁ y) x = inner ℂ (k₁ x) (k₁ y) := fun x y =>
    (hrep x (k₁ y)).symm
  refine ⟨k₁, hrep, ⟨?_, ?_⟩⟩
  · -- Hermitian
    unfold Matrix.IsHermitian
    ext i j
    simp only [Matrix.conjTranspose_apply, Matrix.sub_apply, Matrix.of_apply]
    have e1 : star (AronszajnRK.Sum.kernelFn H j i) = AronszajnRK.Sum.kernelFn H i j :=
      (kernelFn_conj_symm (H := H) i j).symm
    have e2 : star (ι (k₁ i) j) = ι (k₁ j) i :=
      (hK₁ j i).symm ▸ (inner_conj_symm (𝕜 := ℂ) (k₁ i) (k₁ j)).trans (hK₁ i j).symm
    show star (AronszajnRK.Sum.kernelFn H j i - ι (k₁ i) j)
        = AronszajnRK.Sum.kernelFn H i j - ι (k₁ j) i
    rw [star_sub, e1, e2]
  · -- quadratic forms
    intro v
    set g₁ : H₁ := v.sum (fun i ci => ci • k₁ i) with hg₁
    have hqK : (v.sum (fun i ci => v.sum (fun j cj =>
            star ci * AronszajnRK.Sum.kernelFn H i j * cj))).re
          = ‖sectionMap (H := H) v‖ ^ 2 := by
      rw [← inner_sectionMap v v]
      exact inner_self_eq_norm_sq (𝕜 := ℂ) _
    have hqKim : (v.sum (fun i ci => v.sum (fun j cj =>
            star ci * AronszajnRK.Sum.kernelFn H i j * cj))).im = 0 := by
      rw [← inner_sectionMap v v]
      exact inner_self_im (𝕜 := ℂ) _
    have hexp : v.sum (fun i ci => v.sum (fun j cj => star ci * (ι (k₁ j) i) * cj))
        = inner ℂ g₁ g₁ := by
      rw [hg₁, inner_family k₁ v v]
      refine Finsupp.sum_congr fun i _ => Finsupp.sum_congr fun j _ => ?_
      rw [hK₁ i j]
    have hqK₁re : (v.sum (fun i ci => v.sum (fun j cj =>
            star ci * (ι (k₁ j) i) * cj))).re = ‖g₁‖ ^ 2 := by
      rw [hexp]
      exact inner_self_eq_norm_sq (𝕜 := ℂ) _
    have hqK₁im : (v.sum (fun i ci => v.sum (fun j cj =>
            star ci * (ι (k₁ j) i) * cj))).im = 0 := by
      rw [hexp]
      exact inner_self_im (𝕜 := ℂ) _
    -- the transfer element of g1 and the evaluation identity
    obtain ⟨f, hf⟩ := hsub g₁
    have hnf : ‖f‖ ≤ ‖g₁‖ := hnorm g₁ f hf
    have hig : ∀ x : X, ι g₁ x = v.sum (fun j cj => cj * ι (k₁ j) x) := by
      intro x
      rw [hg₁]
      simp only [Finsupp.sum]
      rw [map_sum, Finset.sum_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul]
      simp [Pi.smul_apply, smul_eq_mul]
    have hval : inner ℂ (sectionMap (H := H) v) f
        = v.sum (fun i ci => v.sum (fun j cj => star ci * ι (k₁ j) i * cj)) := by
      rw [sectionMap_apply]
      simp only [Finsupp.sum]
      rw [sum_inner]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [inner_smul_left, RKHS.kerFun_inner i (1 : ℂ) f,
        show (f i : ℂ) = ι g₁ i from congrFun hf i, hig i]
      rw [RCLike.inner_apply, map_one, mul_one, Finsupp.sum]
      simp only [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
      exact Finset.sum_congr rfl fun j _ => rfl
    -- Cauchy-Schwarz domination
    have hnn : (0 : ℂ) ≤ v.sum (fun i ci => v.sum (fun j cj => star ci * ι (k₁ j) i * cj)) := by
      rw [Complex.nonneg_iff]
      exact ⟨by rw [hqK₁re]; exact sq_nonneg _, hqK₁im.symm⟩
    have hreal : v.sum (fun i ci => v.sum (fun j cj => star ci * ι (k₁ j) i * cj))
        = ((‖g₁‖ ^ 2 : ℝ) : ℂ) := by
      refine Complex.ext ?_ ?_
      · rw [hqK₁re, Complex.ofReal_re]
      · rw [hqK₁im, Complex.ofReal_im]
    have hmod : ‖v.sum (fun i ci => v.sum (fun j cj => star ci * ι (k₁ j) i * cj))‖
        = ‖g₁‖ ^ 2 := by
      rw [hreal]
      simp
    have habs : ‖g₁‖ ^ 2
        ≤ ‖sectionMap (H := H) v‖ * ‖g₁‖ := by
      have h1 : ‖inner ℂ (sectionMap (H := H) v) f‖
          ≤ ‖sectionMap (H := H) v‖ * ‖f‖ := norm_inner_le_norm _ _
      rw [hval, hmod] at h1
      have h2 : ‖sectionMap (H := H) v‖ * ‖f‖ ≤ ‖sectionMap (H := H) v‖ * ‖g₁‖ :=
        mul_le_mul_of_nonneg_left hnf (norm_nonneg _)
      linarith
    have hfin : ‖g₁‖ ^ 2 ≤ ‖sectionMap (H := H) v‖ ^ 2 := by
      by_cases h0 : ‖g₁‖ = 0
      · rw [h0, zero_pow two_ne_zero]
        exact sq_nonneg _
      · have hpos : (0 : ℝ) < ‖g₁‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
        have hle : ‖g₁‖ ≤ ‖sectionMap (H := H) v‖ := by
          nlinarith [habs, hpos, norm_nonneg (sectionMap (H := H) v)]
        nlinarith [hle, norm_nonneg (sectionMap (H := H) v)]
    show 0 ≤ v.sum (fun i ci => v.sum (fun j cj =>
        star ci * (AronszajnRK.Sum.kernelFn H i j - ι (k₁ j) i) * cj))
    rw [qf_sub (fun x y => AronszajnRK.Sum.kernelFn H x y) (fun x y => ι (k₁ y) x) v,
      Complex.nonneg_iff]
    constructor
    · rw [Complex.sub_re, hqK, hqK₁re]
      linarith
    · rw [Complex.sub_im, hqKim, hqK₁im]
      ring

end AronszajnRK.Inclusion

/-- Solution entry point. -/
theorem solution {X H H₁ : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [RKHS ℂ H X ℂ]
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
    (ι : H₁ →ₗ[ℂ] (X → ℂ)) (hι : Function.Injective ι)
    (hsub : ∀ f₁ : H₁, ∃ f : H, ⇑f = ι f₁)
    (hnorm : ∀ (f₁ : H₁) (f : H), ⇑f = ι f₁ → ‖f‖ ≤ ‖f₁‖) :
    ∃ k₁ : X → H₁, (∀ (y : X) (f₁ : H₁), inner ℂ (k₁ y) f₁ = ι f₁ y) ∧
      AronszajnRK.Limits.KernelLE (fun x y => ι (k₁ y) x) (AronszajnRK.Sum.kernelFn H) :=
  AronszajnRK.Inclusion.kernel_of_contractive_subclass ι hι hsub hnorm
