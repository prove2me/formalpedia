-- Prove2me | solution 1 for AronszajnRK.Inclusion.eq_class_iff_kernel_two_sided
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-05T08:45:36.238898+00:00
-- url     : https://prove2.me/submissions/c545a12b-c35d-4ba9-9d84-d9d45c174d9b

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

section Iff

/-- Necessity half of Corollary IV₂, extracted. -/
private lemma exists_dominated_of_sub {X H H₁ : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [RKHS ℂ H X ℂ]
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁] [RKHS ℂ H₁ X ℂ]
    (hsub : Set.range (fun f₁ : H₁ => ⇑f₁) ⊆ Set.range (fun f : H => ⇑f)) :
    ∃ M : ℝ, 0 < M ∧ AronszajnRK.Limits.KernelLE (AronszajnRK.Sum.kernelFn H₁)
      (fun x y => (M : ℂ) * AronszajnRK.Sum.kernelFn H x y) := by
  classical
  obtain ⟨M₀, hM₀, hb⟩ := normBoundAux (X := X) hsub
  refine ⟨M₀ * M₀, mul_pos hM₀ hM₀, ⟨?_, ?_⟩⟩
  ·
    unfold Matrix.IsHermitian
    ext i j
    simp only [Matrix.conjTranspose_apply, Matrix.sub_apply, Matrix.of_apply,
      Complex.conj_ofReal, star_sub, star_mul, star_star]
    rw [(kernelFn_conj_symm (H := H) i j).symm, (kernelFn_conj_symm (H := H₁) i j).symm]
    simp
    ring
  ·
    intro c
    obtain ⟨g, hg⟩ : ∃ g : H, ⇑g = ⇑(sectionMap (H := H₁) c) := hsub ⟨_, rfl⟩
    have hnorm : ‖g‖ ≤ M₀ * ‖sectionMap (H := H₁) c‖ := hb _ _ hg
    have hqreK : (c.sum (fun i ci => c.sum (fun j cj =>
            star ci * AronszajnRK.Sum.kernelFn H i j * cj))).re
        = ‖sectionMap (H := H) c‖ ^ 2 := by
      rw [← inner_sectionMap c c]; exact inner_self_eq_norm_sq (𝕜 := ℂ) _
    have hqreK₁ : (c.sum (fun i ci => c.sum (fun j cj =>
            star ci * AronszajnRK.Sum.kernelFn H₁ i j * cj))).re
        = ‖sectionMap (H := H₁) c‖ ^ 2 := by
      rw [← inner_sectionMap c c]; exact inner_self_eq_norm_sq (𝕜 := ℂ) _
    have hqimK : (c.sum (fun i ci => c.sum (fun j cj =>
            star ci * AronszajnRK.Sum.kernelFn H i j * cj))).im = 0 := by
      rw [← inner_sectionMap c c]; exact inner_self_im (𝕜 := ℂ) _
    have hqimK₁ : (c.sum (fun i ci => c.sum (fun j cj =>
            star ci * AronszajnRK.Sum.kernelFn H₁ i j * cj))).im = 0 := by
      rw [← inner_sectionMap c c]; exact inner_self_im (𝕜 := ℂ) _

    have hkey : ‖sectionMap (H := H₁) c‖ ^ 2 ≤ (M₀ * M₀) * ‖sectionMap (H := H) c‖ ^ 2 := by
      have e1 := inner_left_sectionMap g c
      have e2 := inner_left_sectionMap (H := H₁) (sectionMap (H := H₁) c) c
      have esum : c.sum (fun x cx => cx * star (g x))
          = c.sum (fun x cx => cx * star ((sectionMap (H := H₁) c) x)) :=
        Finset.sum_congr rfl fun x _ => by
          show c x * star (g x) = c x * star ((sectionMap (H := H₁) c) x)
          rw [congrFun hg x]
      have hval : (inner ℂ g (sectionMap (H := H) c)).re
          = ‖sectionMap (H := H₁) c‖ ^ 2 := by
        rw [e1, esum, ← e2]
        exact inner_self_eq_norm_sq (𝕜 := ℂ) _
      have himg : (inner ℂ g (sectionMap (H := H) c)).im = 0 := by
        rw [e1, esum, ← e2]
        exact inner_self_im (𝕜 := ℂ) _
      have hnn : 0 ≤ inner ℂ g (sectionMap (H := H) c) := by
        rw [Complex.nonneg_iff]
        exact ⟨by rw [hval]; exact sq_nonneg _, himg.symm⟩
      have habs : ‖sectionMap (H := H₁) c‖ ^ 2 ≤ ‖g‖ * ‖sectionMap (H := H) c‖ := by
        have hreal : inner ℂ g (sectionMap (H := H) c)
            = ((‖sectionMap (H := H₁) c‖ ^ 2 : ℝ) : ℂ) := by
          refine Complex.ext ?_ ?_
          · rw [hval, Complex.ofReal_re]
          · rw [himg, Complex.ofReal_im]
        have h1 : ‖inner ℂ g (sectionMap (H := H) c)‖
            = ‖sectionMap (H := H₁) c‖ ^ 2 := by
          rw [hreal]
          simp
        have h2 : ‖inner ℂ g (sectionMap (H := H) c)‖
            ≤ ‖g‖ * ‖sectionMap (H := H) c‖ := norm_inner_le_norm g _
        rw [h1] at h2
        exact h2
      by_cases h0 : ‖sectionMap (H := H₁) c‖ = 0
      · rw [h0, zero_pow two_ne_zero]
        exact mul_nonneg (mul_nonneg hM₀.le hM₀.le) (sq_nonneg _)
      · have hpos : (0 : ℝ) < ‖sectionMap (H := H₁) c‖ :=
          lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
        nlinarith [habs, hnorm, hpos, norm_nonneg (sectionMap (H := H) c),
          mul_nonneg (norm_nonneg (sectionMap (H := H₁) c)) (norm_nonneg (sectionMap (H := H) c)),
          sq_nonneg (‖sectionMap (H := H₁) c‖ - M₀ * ‖sectionMap (H := H) c‖)]

    show 0 ≤ c.sum (fun i ci => c.sum (fun j cj =>
        star ci * (((M₀ * M₀ : ℝ) : ℂ) * AronszajnRK.Sum.kernelFn H i j
          - AronszajnRK.Sum.kernelFn H₁ i j) * cj))
    rw [qf_sub (fun x y => ((M₀ * M₀ : ℝ) : ℂ) * AronszajnRK.Sum.kernelFn H x y)
        (AronszajnRK.Sum.kernelFn H₁) c,
      qf_const_smul ((M₀ * M₀ : ℝ) : ℂ) (AronszajnRK.Sum.kernelFn H) c,
      Complex.nonneg_iff]
    constructor
    · rw [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, hqreK, hqreK₁]
      linarith
    · rw [Complex.sub_im, Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re,
        zero_mul, hqimK, hqimK₁]
      ring

/-- Sufficiency half of Corollary IV₂, extracted. -/
private lemma sub_of_dominated {X H H₁ : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [RKHS ℂ H X ℂ]
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁] [RKHS ℂ H₁ X ℂ]
    {M : ℝ} (hM : 0 < M)
    (hle : AronszajnRK.Limits.KernelLE (AronszajnRK.Sum.kernelFn H₁)
      (fun x y => (M : ℂ) * AronszajnRK.Sum.kernelFn H x y)) :
    Set.range (fun f₁ : H₁ => ⇑f₁) ⊆ Set.range (fun f : H => ⇑f) := by
  classical
  obtain ⟨_, hpsd⟩ := hle
  simp only [Matrix.sub_apply, Matrix.of_apply] at hpsd
  have hsq : ∀ a : X →₀ ℂ,
      ‖sectionMap (H := H₁) a‖ ^ 2 ≤ (M : ℝ) * ‖sectionMap (H := H) a‖ ^ 2 := by
    intro a
    have hqreK : (a.sum (fun i ai => a.sum (fun j aj =>
            star ai * AronszajnRK.Sum.kernelFn H i j * aj))).re
        = ‖sectionMap (H := H) a‖ ^ 2 := by
      rw [← inner_sectionMap a a]; exact inner_self_eq_norm_sq (𝕜 := ℂ) _
    have hqreK₁ : (a.sum (fun i ai => a.sum (fun j aj =>
            star ai * AronszajnRK.Sum.kernelFn H₁ i j * aj))).re
        = ‖sectionMap (H := H₁) a‖ ^ 2 := by
      rw [← inner_sectionMap a a]; exact inner_self_eq_norm_sq (𝕜 := ℂ) _
    have hz : (0 : ℂ) ≤ ((M : ℝ) : ℂ) * a.sum (fun i ai => a.sum (fun j aj =>
            star ai * AronszajnRK.Sum.kernelFn H i j * aj))
        - a.sum (fun i ai => a.sum (fun j aj =>
            star ai * AronszajnRK.Sum.kernelFn H₁ i j * aj)) := by
      have h := hpsd a
      rw [qf_sub (fun x y => ((M : ℝ) : ℂ) * AronszajnRK.Sum.kernelFn H x y)
          (AronszajnRK.Sum.kernelFn H₁) a,
        qf_const_smul ((M : ℝ) : ℂ) (AronszajnRK.Sum.kernelFn H) a] at h
      exact h
    obtain ⟨hre, _⟩ := Complex.nonneg_iff.mp hz
    rw [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, hqreK, hqreK₁] at hre
    linarith

  have hbound : ∀ a : X →₀ ℂ,
      ‖sectionMap (H := H₁) a‖ ≤ Real.sqrt M * ‖sectionMap (H := H) a‖ := by
    intro a
    have h := hsq a
    have hsqm : Real.sqrt M * Real.sqrt M = M := Real.mul_self_sqrt (le_of_lt hM)
    have e1 : (0 : ℝ) ≤ ‖sectionMap (H := H₁) a‖ := norm_nonneg _
    have e2 : (0 : ℝ) ≤ ‖sectionMap (H := H) a‖ := norm_nonneg _
    nlinarith [h, hsqm, e1, e2, mul_nonneg (Real.sqrt_nonneg M) e2,
      sq_nonneg (‖sectionMap (H := H₁) a‖ - Real.sqrt M * ‖sectionMap (H := H) a‖)]

  have hdense : DenseRange (sectionMap (H := H)) := denseRange_sectionMap
  set U : H →L[ℂ] H₁ := LinearMap.extendOfNorm (sectionMap (H := H₁)) (sectionMap (H := H))
    with hU
  have hUsec : ∀ a : X →₀ ℂ, U (sectionMap (H := H) a) = sectionMap (H := H₁) a :=
    LinearMap.extendOfNorm_eq hdense ⟨Real.sqrt M, hbound⟩
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
  rintro _ ⟨g₁, rfl⟩
  exact ⟨U.adjoint g₁, funext fun x => hrepro g₁ x⟩

end Iff

/-- Rescaling a dominated kernel: `c·K ≪ K₁` implies `K ≪ (1/c)·K₁`. -/
lemma kernelLE_rescale {X : Type*} {K K₁ : X → X → ℂ} {c : ℝ} (hc : 0 < c)
    (h : AronszajnRK.Limits.KernelLE (fun x y => (c : ℂ) * K x y) K₁) :
    AronszajnRK.Limits.KernelLE K (fun x y => ((1 / c : ℝ) : ℂ) * K₁ x y) := by
  classical
  obtain ⟨hh, hf⟩ := h
  simp only [Matrix.sub_apply, Matrix.of_apply] at hf
  have hcne : (c : ℂ) ≠ 0 := by
    intro h0
    have h1 : c = 0 := by exact_mod_cast h0
    linarith
  have hco : ((1 / c : ℝ) : ℂ) = ((c : ℝ) : ℂ)⁻¹ := by
    rw [show (1 / c : ℝ) = c⁻¹ from by field_simp, Complex.ofReal_inv]
  have hscale : ∀ x y : X,
      ((1 / c : ℝ) : ℂ) * K₁ x y - K x y
        = ((1 / c : ℝ) : ℂ) * (K₁ x y - (c : ℂ) * K x y) := by
    intro x y
    rw [hco, mul_sub, ← mul_assoc, inv_mul_cancel₀ hcne, one_mul]
  -- Hermitian
  refine ⟨?_, ?_⟩
  · unfold Matrix.IsHermitian
    ext i j
    simp only [Matrix.conjTranspose_apply, Matrix.sub_apply, Matrix.of_apply]
    have hentry : star (K₁ j i - (c : ℂ) * K j i) = K₁ i j - (c : ℂ) * K i j := by
      have := congrArg (fun M : Matrix X X ℂ => M i j) hh.eq
      simpa [Matrix.conjTranspose_apply, Matrix.of_apply] using this
    show star (((1 / c : ℝ) : ℂ) * K₁ j i - K j i)
        = ((1 / c : ℝ) : ℂ) * K₁ i j - K i j
    rw [hscale j i, star_mul, hentry,
      show star (((1 / c : ℝ) : ℂ)) = ((1 / c : ℝ) : ℂ) from by simp, hco]
    rw [mul_comm, mul_sub, ← mul_assoc, inv_mul_cancel₀ hcne, one_mul]
  · -- quadratic forms
    intro v
    have hqf : v.sum (fun i vi => v.sum (fun j vj =>
            star vi * (((1 / c : ℝ) : ℂ) * K₁ i j - K i j) * vj))
        = ((1 / c : ℝ) : ℂ) * v.sum (fun i vi => v.sum (fun j vj =>
            star vi * (K₁ i j - (c : ℂ) * K i j) * vj)) := by
      rw [← qf_const_smul ((1 / c : ℝ) : ℂ) (fun x y => K₁ x y - (c : ℂ) * K x y) v]
      refine Finsupp.sum_congr fun i _ => Finsupp.sum_congr fun j _ => ?_
      rw [hscale i j]
    obtain ⟨hre, him⟩ := Complex.nonneg_iff.mp (hf v)
    show 0 ≤ v.sum (fun i vi => v.sum (fun j vj =>
        star vi * (((1 / c : ℝ) : ℂ) * K₁ i j - K i j) * vj))
    rw [hqf, Complex.nonneg_iff]
    constructor
    · rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      exact mul_nonneg (by positivity) hre
    · rw [Complex.mul_im, Complex.ofReal_im, zero_mul, Complex.ofReal_re]
      have hzz : (v.sum (fun i vi => v.sum (fun j vj =>
          star vi * (K₁ i j - (c : ℂ) * K i j) * vj))).im = 0 := him.symm
      rw [hzz]
      ring

/-- Rescaling, mirrored direction: `K ≪ c·K₁` implies `(1/c)·K ≪ K₁`. -/
lemma kernelLE_inv_rescale {X : Type*} {K K₁ : X → X → ℂ} {c : ℝ} (hc : 0 < c)
    (h : AronszajnRK.Limits.KernelLE K (fun x y => (c : ℂ) * K₁ x y)) :
    AronszajnRK.Limits.KernelLE (fun x y => ((1 / c : ℝ) : ℂ) * K x y) K₁ := by
  classical
  obtain ⟨hh, hf⟩ := h
  simp only [Matrix.sub_apply, Matrix.of_apply] at hf
  have hco : ((1 / c : ℝ) : ℂ) = ((c : ℝ) : ℂ)⁻¹ := by
    rw [show (1 / c : ℝ) = c⁻¹ from by field_simp, Complex.ofReal_inv]
  have hscale : ∀ x y : X,
      K₁ x y - ((1 / c : ℝ) : ℂ) * K x y
        = ((1 / c : ℝ) : ℂ) * ((c : ℂ) * K₁ x y - K x y) := by
    intro x y
    rw [hco, mul_sub]
    field_simp
  refine ⟨?_, ?_⟩
  · unfold Matrix.IsHermitian
    ext i j
    simp only [Matrix.conjTranspose_apply, Matrix.sub_apply, Matrix.of_apply]
    have hentry : star ((c : ℂ) * K₁ j i - K j i) = (c : ℂ) * K₁ i j - K i j := by
      have := congrArg (fun M : Matrix X X ℂ => M i j) hh.eq
      simpa [Matrix.conjTranspose_apply, Matrix.of_apply] using this
    show star (K₁ j i - ((1 / c : ℝ) : ℂ) * K j i)
        = K₁ i j - ((1 / c : ℝ) : ℂ) * K i j
    rw [hscale j i, star_mul, hentry,
      show star (((1 / c : ℝ) : ℂ)) = ((1 / c : ℝ) : ℂ) from by simp]
    rw [mul_comm, mul_sub, ← mul_assoc, hco, inv_mul_cancel₀ (by exact_mod_cast hc.ne'), one_mul]
  · intro v
    have hqf : v.sum (fun i vi => v.sum (fun j vj =>
            star vi * (K₁ i j - ((1 / c : ℝ) : ℂ) * K i j) * vj))
        = ((1 / c : ℝ) : ℂ) * v.sum (fun i vi => v.sum (fun j vj =>
            star vi * ((c : ℂ) * K₁ i j - K i j) * vj)) := by
      rw [← qf_const_smul ((1 / c : ℝ) : ℂ) (fun x y => (c : ℂ) * K₁ x y - K x y) v]
      refine Finsupp.sum_congr fun i _ => Finsupp.sum_congr fun j _ => ?_
      rw [hscale i j]
    obtain ⟨hre, him⟩ := Complex.nonneg_iff.mp (hf v)
    show 0 ≤ v.sum (fun i vi => v.sum (fun j vj =>
        star vi * (K₁ i j - ((1 / c : ℝ) : ℂ) * K i j) * vj))
    rw [hqf, Complex.nonneg_iff]
    constructor
    · rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      exact mul_nonneg (by positivity) hre
    · rw [Complex.mul_im, Complex.ofReal_im, zero_mul, Complex.ofReal_re]
      have hzz : (v.sum (fun i vi => v.sum (fun j vj =>
          star vi * ((c : ℂ) * K₁ i j - K i j) * vj))).im = 0 := him.symm
      rw [hzz]
      ring

/-- Aronszajn, *Theory of Reproducing Kernels*, Trans. Amer. Math. Soc. 68 (1950), §13 (C),
Corollary IV₃, p. 383 (PDF p. 47). Under the hypotheses of Corollary IV₂ (`K`, `K₁` positive
matrices, `F`, `F₁` the corresponding classes), in order that `F₁ = F` it is necessary and
sufficient that there exist two positive constants `m` and `M` such that `mK ≪ K₁ ≪ MK`.
Stated, as Corollary IV₂, for arbitrary complex RKHSs `H`, `H₁` with kernels `K`, `K₁`. -/
theorem eq_class_iff_kernel_two_sided {X H H₁ : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [RKHS ℂ H X ℂ]
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁] [RKHS ℂ H₁ X ℂ] :
    Set.range (fun f₁ : H₁ => ⇑f₁) = Set.range (fun f : H => ⇑f) ↔
      ∃ m M : ℝ, 0 < m ∧ 0 < M ∧
        AronszajnRK.Limits.KernelLE (fun x y => (m : ℂ) * AronszajnRK.Sum.kernelFn H x y) (AronszajnRK.Sum.kernelFn H₁) ∧
        AronszajnRK.Limits.KernelLE (AronszajnRK.Sum.kernelFn H₁) (fun x y => (M : ℂ) * AronszajnRK.Sum.kernelFn H x y) := by
  classical
  constructor
  · -- necessity: both inclusions are dominated
    intro heq
    have hs1 : Set.range (fun f₁ : H₁ => ⇑f₁) ⊆ Set.range (fun f : H => ⇑f) := by
      rw [heq]
    have hs2 : Set.range (fun f : H => ⇑f) ⊆ Set.range (fun f₁ : H₁ => ⇑f₁) := by
      rw [heq]
    obtain ⟨M, hM, hle2⟩ := exists_dominated_of_sub (X := X) (H := H) (H₁ := H₁) hs1
    obtain ⟨M', hM', hleK⟩ := exists_dominated_of_sub (X := X) (H := H₁) (H₁ := H) hs2
    have hres : AronszajnRK.Limits.KernelLE
        (fun x y => ((1 / M' : ℝ) : ℂ) * AronszajnRK.Sum.kernelFn H x y)
        (AronszajnRK.Sum.kernelFn H₁) :=
      kernelLE_inv_rescale hM' hleK
    exact ⟨1 / M', M, by positivity, hM, hres, hle2⟩
  · -- sufficiency: both dominations give inclusions; combine by antisymmetry
    rintro ⟨m, M, hm, hM, hle1, hle2⟩
    have hs1 : Set.range (fun f₁ : H₁ => ⇑f₁) ⊆ Set.range (fun f : H => ⇑f) :=
      sub_of_dominated hM hle2
    have hres : AronszajnRK.Limits.KernelLE
        (AronszajnRK.Sum.kernelFn H)
        (fun x y => ((1 / m : ℝ) : ℂ) * AronszajnRK.Sum.kernelFn H₁ x y) :=
      kernelLE_rescale hm hle1
    have hs2 : Set.range (fun f : H => ⇑f) ⊆ Set.range (fun f₁ : H₁ => ⇑f₁) :=
      sub_of_dominated (by positivity) hres
    exact Set.Subset.antisymm hs1 hs2

end AronszajnRK.Inclusion

/-- Solution entry point. -/
theorem solution {X H H₁ : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [RKHS ℂ H X ℂ]
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁] [RKHS ℂ H₁ X ℂ] :
    Set.range (fun f₁ : H₁ => ⇑f₁) = Set.range (fun f : H => ⇑f) ↔
      ∃ m M : ℝ, 0 < m ∧ 0 < M ∧
        AronszajnRK.Limits.KernelLE (fun x y => (m : ℂ) * AronszajnRK.Sum.kernelFn H x y) (AronszajnRK.Sum.kernelFn H₁) ∧
        AronszajnRK.Limits.KernelLE (AronszajnRK.Sum.kernelFn H₁) (fun x y => (M : ℂ) * AronszajnRK.Sum.kernelFn H x y) :=
  AronszajnRK.Inclusion.eq_class_iff_kernel_two_sided
