-- Prove2me | Definitions.Def_RepTheory_TestFunctionAction
-- name    : RepTheory_TestFunctionAction
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:29.330635+00:00
-- url     : https://prove2.me/theorems/596f1de6-d162-5492-9757-70f7ce0ab677
-- title:
--   Hecke action of locally constant compactly supported test functions
-- statement:
--   Throughout, $\mathbb{k}$ is a commutative ring equipped with an $\mathbb{R}$-algebra structure, $V$ a $\mathbb{k}$-module and $G$ a group with a measurable (and, where needed, topological) structure acting on $V$ by additive maps commuting with the $\mathbb{k}$-scalars. Four definitions carry the module. `HasOpenStabilizer G v` abbreviates the assertion that the stabiliser subgroup of $v$ is open as a subset of $G$; it is characterised by the existence of an open (respectively, of a compact open, given that one compact open subgroup exists) subgroup all of whose elements fix $v$, and it is stable under $v \mapsto g \bullet v$ and under multiplication by scalars commuting with the action. `measureCoeff 𝕜 μ s` is the image under $\mathbb{R} \to \mathbb{k}$ of the real number underlying $\mu(s)$, hence $0$ when $\mu(s) = \infty$. `finiteRangeIntegral 𝕜 μ F`, for $F : X \to V$, is $\sum_{w} \mathrm{measureCoeff}(F^{-1}\{w\}) \bullet w$ over the (finite) range of $F$, and is $0$ when the range is infinite: a genuine integral only for functions of finite range, defined by a case split rather than by a limit. `heckeSmul μ f v` is the finite-range integral of $g \mapsto f(g) \bullet (g \bullet v)$, and `heckeIdempotent 𝕜 μ K` is the function equal on $K$ to the image in $\mathbb{k}$ of $\mu(K)^{-1}$ (computed on the underlying real) and $0$ off $K$.
--
--   For a subgroup $K \le G$, `fixedPointsSubmodule 𝕜 K` is the submodule of $v$ with $k \bullet v = v$ for all $k \in K$, and `augmentationSubmodule 𝕜 K` is the $\mathbb{k}$-span of the vectors $k \bullet u - u$ with $k \in K$, $u \in V$. The results establish bilinearity and translation behaviour of `heckeSmul` for locally constant compactly supported $f$ and $v$ with open stabiliser, that `heckeIdempotent` acts as the identity on $K$-fixed vectors and as $0$ on the augmentation submodule, and finally that these two submodules are complementary when $K$ is compact open of positive finite measure and every vector has open stabiliser. A witness lemma exhibits the action of $\mathbb{R}_{>0}^{\times} \times \mathbb{Z}^{\times}$ on $\mathbb{Z}$ through the second factor, where $1$ has open but proper stabiliser.
--
--   **Relation to Mathlib.** Mathlib supplies the measure-theoretic, locally constant and open-subgroup machinery used here; the finite-range integral, the test-function action `heckeSmul`, the normalised idempotent of a compact open subgroup, and the fixed-point and augmentation submodules are the project's own notions.
--
--   **Where it is used.** The complementarity of fixed points and the augmentation submodule, together with the idempotent $e_K$ acting as a projector, is the standard device for splitting off $K$-invariants in a smooth representation of a locally profinite group, as used when Hecke operators are brought to bear on spaces of automorphic forms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_RepTheory_TestFunctionAction.lean

import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Algebra.Module.BigOperators

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory
open scoped Topology

namespace TestFunctionAction

section OpenStabilizer

variable {G : Type*} [Group G] [TopologicalSpace G] {M : Type*}

abbrev HasOpenStabilizer (G : Type*) {M : Type*} [Group G] [TopologicalSpace G] [MulAction G M]
    (v : M) : Prop :=
  IsOpen ((MulAction.stabilizer G v : Subgroup G) : Set G)

variable [MulAction G M]

theorem hasOpenStabilizer_iff_exists_isOpen_subgroup [ContinuousMul G] {v : M} :
    HasOpenStabilizer G v ↔ ∃ U : Subgroup G, IsOpen (U : Set G) ∧ ∀ u ∈ U, u • v = v := by
  constructor
  · intro hv
    exact ⟨MulAction.stabilizer G v, hv, fun u hu => MulAction.mem_stabilizer_iff.mp hu⟩
  · rintro ⟨U, hUo, hUv⟩
    exact Subgroup.isOpen_mono (fun u hu => MulAction.mem_stabilizer_iff.mpr (hUv u hu)) hUo

theorem hasOpenStabilizer_iff_exists_isCompact_isOpen_subgroup [ContinuousMul G]
    (hex : ∃ K : Subgroup G, IsCompact (K : Set G) ∧ IsOpen (K : Set G)) {v : M} :
    HasOpenStabilizer G v ↔
      ∃ K : Subgroup G, IsCompact (K : Set G) ∧ IsOpen (K : Set G) ∧ ∀ u ∈ K, u • v = v := by
  constructor
  · intro hv
    obtain ⟨K₀, hK₀c, hK₀o⟩ := hex
    refine ⟨K₀ ⊓ MulAction.stabilizer G v, ?_, ?_, ?_⟩
    · rw [Subgroup.coe_inf]
      exact hK₀c.inter_right (Subgroup.isClosed_of_isOpen _ hv)
    · rw [Subgroup.coe_inf]
      exact hK₀o.inter hv
    · intro u hu
      exact MulAction.mem_stabilizer_iff.mp (Subgroup.mem_inf.mp hu).2
  · rintro ⟨K, -, hKo, hKv⟩
    exact hasOpenStabilizer_iff_exists_isOpen_subgroup.mpr ⟨K, hKo, hKv⟩

theorem HasOpenStabilizer.smul [ContinuousMul G] {v : M} (hv : HasOpenStabilizer G v) (g : G) :
    HasOpenStabilizer G (g • v) := by
  have hset : ((MulAction.stabilizer G (g • v) : Subgroup G) : Set G)
      = (fun h : G => g⁻¹ * h * g) ⁻¹' ((MulAction.stabilizer G v : Subgroup G) : Set G) := by
    ext h
    simp only [SetLike.mem_coe, Set.mem_preimage, MulAction.mem_stabilizer_iff]
    constructor
    · intro hh
      calc (g⁻¹ * h * g) • v = g⁻¹ • h • g • v := by rw [mul_smul, mul_smul]
        _ = g⁻¹ • g • v := by rw [hh]
        _ = v := inv_smul_smul g v
    · intro hh
      calc h • g • v = g • g⁻¹ • h • g • v := (smul_inv_smul g _).symm
        _ = g • (g⁻¹ * h * g) • v := by rw [mul_smul, mul_smul]
        _ = g • v := by rw [hh]
  show IsOpen ((MulAction.stabilizer G (g • v) : Subgroup G) : Set G)
  rw [hset]
  exact hv.preimage (by fun_prop)

theorem HasOpenStabilizer.const_smul [ContinuousMul G] {R : Type*} [SMul R M] [SMulCommClass G R M]
    {v : M} (hv : HasOpenStabilizer G v) (r : R) : HasOpenStabilizer G (r • v) := by
  refine Subgroup.isOpen_mono (H₁ := MulAction.stabilizer G v) (fun g hg => ?_) hv
  rw [MulAction.mem_stabilizer_iff] at hg ⊢
  rw [smul_comm, hg]

theorem isLocallyConstant_indicator_const_of_isClopen {X : Type*} [TopologicalSpace X]
    {s : Set X} (hs : IsClopen s) {N : Type*} [Zero N] (c : N) :
    IsLocallyConstant (s.indicator fun _ => c) := by
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  by_cases hx : x ∈ s
  · exact ⟨s, hs.isOpen, hx, fun y hy => by
      rw [Set.indicator_of_mem hy, Set.indicator_of_mem hx]⟩
  · exact ⟨sᶜ, hs.compl.isOpen, hx, fun y hy => by
      rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]⟩

end OpenStabilizer

section Witness

theorem hasOpenStabilizer_one_int_real_prod_units :
    letI : MulAction (Multiplicative ℝ × ℤˣ) ℤ :=
      MulAction.compHom ℤ (MonoidHom.snd (Multiplicative ℝ) ℤˣ)
    HasOpenStabilizer (Multiplicative ℝ × ℤˣ) (1 : ℤ) ∧
      MulAction.stabilizer (Multiplicative ℝ × ℤˣ) (1 : ℤ) ≠ ⊤ := by
  letI : MulAction (Multiplicative ℝ × ℤˣ) ℤ :=
    MulAction.compHom ℤ (MonoidHom.snd (Multiplicative ℝ) ℤˣ)
  refine ⟨?_, fun htop => ?_⟩
  · have hcont : Continuous fun p : Multiplicative ℝ × ℤˣ => ((p.2 : ℤˣ) : ℤ) :=
      Units.continuous_val.comp continuous_snd
    have hopen : IsOpen ((fun p : Multiplicative ℝ × ℤˣ => ((p.2 : ℤˣ) : ℤ)) ⁻¹' {1}) :=
      (isOpen_discrete _).preimage hcont
    unfold HasOpenStabilizer
    convert hopen using 1
    ext p
    simp [MulAction.mem_stabilizer_iff, MulAction.compHom_smul_def, Units.smul_def]
  · have hmem : ((1 : Multiplicative ℝ), (-1 : ℤˣ)) ∈
        MulAction.stabilizer (Multiplicative ℝ × ℤˣ) (1 : ℤ) := by
      rw [htop]; exact Subgroup.mem_top _
    simp [MulAction.mem_stabilizer_iff, MulAction.compHom_smul_def, Units.smul_def] at hmem

end Witness

section MeasureCoeff

variable (𝕜 : Type*) [CommRing 𝕜] [Algebra ℝ 𝕜]
variable {X : Type*} [MeasurableSpace X]

noncomputable def measureCoeff (μ : Measure X) (s : Set X) : 𝕜 :=
  algebraMap ℝ 𝕜 (μ s).toReal

theorem measureCoeff_def (μ : Measure X) (s : Set X) :
    measureCoeff 𝕜 μ s = algebraMap ℝ 𝕜 (μ s).toReal := rfl

theorem measureCoeff_congr (μ : Measure X) {s t : Set X} (h : μ s = μ t) :
    measureCoeff 𝕜 μ s = measureCoeff 𝕜 μ t := by
  rw [measureCoeff_def, measureCoeff_def, h]

@[simp]
theorem measureCoeff_empty (μ : Measure X) : measureCoeff 𝕜 μ (∅ : Set X) = 0 := by
  simp [measureCoeff_def]

end MeasureCoeff

section FiniteRangeIntegral

variable (𝕜 : Type*) [CommRing 𝕜] [Algebra ℝ 𝕜]
variable {X : Type*} [MeasurableSpace X]
variable {V : Type*} [AddCommGroup V] [Module 𝕜 V]

open Classical in
noncomputable def finiteRangeIntegral (μ : Measure X) (F : X → V) : V :=
  if h : (Set.range F).Finite then
    ∑ w ∈ h.toFinset, measureCoeff 𝕜 μ (F ⁻¹' {w}) • w
  else 0

theorem finiteRangeIntegral_of_finite (μ : Measure X) {F : X → V}
    (h : (Set.range F).Finite) :
    finiteRangeIntegral 𝕜 μ F = ∑ w ∈ h.toFinset, measureCoeff 𝕜 μ (F ⁻¹' {w}) • w := by
  unfold finiteRangeIntegral
  exact dif_pos h

theorem finiteRangeIntegral_eq_sum (μ : Measure X) {F : X → V} (hF : (Set.range F).Finite)
    {T : Finset V} (hT : ∀ x : X, F x ≠ 0 → F x ∈ T) :
    finiteRangeIntegral 𝕜 μ F = ∑ w ∈ T, measureCoeff 𝕜 μ (F ⁻¹' {w}) • w := by
  classical
  rw [finiteRangeIntegral_of_finite 𝕜 μ hF]
  have hzero₁ : ∀ w ∈ hF.toFinset ∪ T, w ∉ hF.toFinset →
      measureCoeff 𝕜 μ (F ⁻¹' {w}) • w = 0 := by
    intro w _ hw
    have hempty : F ⁻¹' {w} = ∅ := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
      intro hx
      exact hw (hF.mem_toFinset.mpr ⟨x, hx⟩)
    rw [hempty, measureCoeff_empty, zero_smul]
  have hzero₂ : ∀ w ∈ hF.toFinset ∪ T, w ∉ T →
      measureCoeff 𝕜 μ (F ⁻¹' {w}) • w = 0 := by
    intro w hw hwT
    rcases Finset.mem_union.mp hw with hw₁ | hw₂
    · obtain ⟨x, hx⟩ := hF.mem_toFinset.mp hw₁
      by_cases hx0 : F x = 0
      · rw [← hx, hx0, smul_zero]
      · exact absurd (hx ▸ hT x hx0) hwT
    · exact absurd hw₂ hwT
  calc ∑ w ∈ hF.toFinset, measureCoeff 𝕜 μ (F ⁻¹' {w}) • w
      = ∑ w ∈ hF.toFinset ∪ T, measureCoeff 𝕜 μ (F ⁻¹' {w}) • w :=
        Finset.sum_subset Finset.subset_union_left hzero₁
    _ = ∑ w ∈ T, measureCoeff 𝕜 μ (F ⁻¹' {w}) • w :=
        (Finset.sum_subset Finset.subset_union_right hzero₂).symm

theorem finiteRangeIntegral_zero (μ : Measure X) :
    finiteRangeIntegral 𝕜 μ (fun _ : X => (0 : V)) = 0 := by
  classical
  have hfin : (Set.range fun _ : X => (0 : V)).Finite :=
    (Set.finite_singleton (0 : V)).subset (by rintro _ ⟨x, rfl⟩; exact rfl)
  rw [finiteRangeIntegral_eq_sum 𝕜 μ hfin (T := ∅) (fun x hx => absurd rfl hx)]
  simp

theorem finiteRangeIntegral_indicator_const (μ : Measure X) (s : Set X) (x : V) :
    finiteRangeIntegral 𝕜 μ (s.indicator fun _ => x) = measureCoeff 𝕜 μ s • x := by
  classical
  have hfin : (Set.range (s.indicator fun _ : X => x)).Finite := by
    refine ((Set.finite_singleton x).insert 0).subset ?_
    rintro _ ⟨y, rfl⟩
    by_cases hy : y ∈ s
    · rw [Set.indicator_of_mem hy]
      exact Set.mem_insert_of_mem _ rfl
    · rw [Set.indicator_of_notMem hy]
      exact Set.mem_insert _ _
  have hT : ∀ y : X, (s.indicator fun _ : X => x) y ≠ 0 →
      (s.indicator fun _ : X => x) y ∈ ({x} : Finset V) := by
    intro y hy
    by_cases hys : y ∈ s
    · rw [Set.indicator_of_mem hys]
      exact Finset.mem_singleton_self x
    · exact absurd (Set.indicator_of_notMem hys _) hy
  rw [finiteRangeIntegral_eq_sum 𝕜 μ hfin hT, Finset.sum_singleton]
  by_cases hx : x = 0
  · rw [hx, smul_zero, smul_zero]
  · have hpre : (s.indicator fun _ : X => x) ⁻¹' {x} = s := by
      ext y
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      by_cases hys : y ∈ s
      · simp [hys]
      · simp [hys, Ne.symm hx]
    rw [hpre]

theorem finiteRangeIntegral_comp_eq_sum {W : Type*} (μ : Measure X) {P : X → W}
    (hP : (Set.range P).Finite) (hmeas : ∀ w : W, MeasurableSet (P ⁻¹' {w})) (φ : W → V)
    (hfin : ∀ w : W, φ w ≠ 0 → μ (P ⁻¹' {w}) ≠ ⊤) :
    finiteRangeIntegral 𝕜 μ (fun x => φ (P x))
      = ∑ w ∈ hP.toFinset, measureCoeff 𝕜 μ (P ⁻¹' {w}) • φ w := by
  classical
  have hrange : (Set.range fun x => φ (P x)).Finite := by
    refine (hP.image φ).subset ?_
    rintro _ ⟨x, rfl⟩
    exact ⟨P x, ⟨x, rfl⟩, rfl⟩
  have hT : ∀ x : X, φ (P x) ≠ 0 → φ (P x) ∈ hP.toFinset.image φ := fun x _ =>
    Finset.mem_image_of_mem φ (hP.mem_toFinset.mpr ⟨x, rfl⟩)
  calc finiteRangeIntegral 𝕜 μ (fun x => φ (P x))
      = ∑ v ∈ hP.toFinset.image φ,
          measureCoeff 𝕜 μ ((fun x => φ (P x)) ⁻¹' {v}) • v :=
        finiteRangeIntegral_eq_sum 𝕜 μ hrange hT
    _ = ∑ v ∈ hP.toFinset.image φ, ∑ w ∈ hP.toFinset.filter (fun w => φ w = v),
          measureCoeff 𝕜 μ (P ⁻¹' {w}) • φ w := by
        refine Finset.sum_congr rfl fun v _ => ?_
        by_cases hv0 : v = 0
        · subst hv0
          rw [smul_zero]
          refine (Finset.sum_eq_zero fun w hw => ?_).symm
          rw [(Finset.mem_filter.mp hw).2, smul_zero]
        · have hseteq : (fun x => φ (P x)) ⁻¹' {v}
              = ⋃ w ∈ hP.toFinset.filter (fun w => φ w = v), P ⁻¹' {w} := by
            ext x
            simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iUnion,
              Finset.mem_filter, Set.Finite.mem_toFinset, exists_prop]
            constructor
            · intro hx
              exact ⟨P x, ⟨⟨x, rfl⟩, hx⟩, rfl⟩
            · rintro ⟨w, ⟨-, hφw⟩, hPx⟩
              rw [hPx]
              exact hφw
          have hmeasure : μ ((fun x => φ (P x)) ⁻¹' {v})
              = ∑ w ∈ hP.toFinset.filter (fun w => φ w = v), μ (P ⁻¹' {w}) := by
            rw [hseteq]
            exact measure_biUnion_finset (Set.pairwiseDisjoint_fiber P _) fun w _ => hmeas w
          have hne : ∀ w ∈ hP.toFinset.filter (fun w => φ w = v), μ (P ⁻¹' {w}) ≠ ⊤ := by
            intro w hw
            refine hfin w ?_
            rw [(Finset.mem_filter.mp hw).2]
            exact hv0
          have hcoeff : measureCoeff 𝕜 μ ((fun x => φ (P x)) ⁻¹' {v})
              = ∑ w ∈ hP.toFinset.filter (fun w => φ w = v),
                  measureCoeff 𝕜 μ (P ⁻¹' {w}) := by
            simp only [measureCoeff_def]
            rw [hmeasure, ENNReal.toReal_sum hne, map_sum]
          rw [hcoeff, Finset.sum_smul]
          refine Finset.sum_congr rfl fun w hw => ?_
          rw [(Finset.mem_filter.mp hw).2]
    _ = ∑ w ∈ hP.toFinset, measureCoeff 𝕜 μ (P ⁻¹' {w}) • φ w :=
        Finset.sum_fiberwise_of_maps_to (fun w hw => Finset.mem_image_of_mem φ hw) _

theorem finiteRangeIntegral_add (μ : Measure X) {F G : X → V}
    (hF : (Set.range F).Finite) (hG : (Set.range G).Finite)
    (hFm : ∀ w : V, MeasurableSet (F ⁻¹' {w})) (hGm : ∀ w : V, MeasurableSet (G ⁻¹' {w}))
    (hFfin : ∀ w : V, w ≠ 0 → μ (F ⁻¹' {w}) ≠ ⊤) (hGfin : ∀ w : V, w ≠ 0 → μ (G ⁻¹' {w}) ≠ ⊤) :
    finiteRangeIntegral 𝕜 μ (fun x => F x + G x)
      = finiteRangeIntegral 𝕜 μ F + finiteRangeIntegral 𝕜 μ G := by
  classical
  have hP : (Set.range fun x => (F x, G x)).Finite := by
    refine (hF.prod hG).subset ?_
    rintro _ ⟨x, rfl⟩
    exact ⟨⟨x, rfl⟩, ⟨x, rfl⟩⟩
  have hPm : ∀ w : V × V, MeasurableSet ((fun x => (F x, G x)) ⁻¹' {w}) := by
    intro w
    have hset : (fun x => (F x, G x)) ⁻¹' {w} = F ⁻¹' {w.1} ∩ G ⁻¹' {w.2} := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_inter_iff, Prod.ext_iff]
    rw [hset]
    exact (hFm w.1).inter (hGm w.2)
  have hsub1 : ∀ w : V × V, (fun x => (F x, G x)) ⁻¹' {w} ⊆ F ⁻¹' {w.1} := by
    intro w x hx
    have hx' : (F x, G x) = w := hx
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    rw [← hx']
  have hsub2 : ∀ w : V × V, (fun x => (F x, G x)) ⁻¹' {w} ⊆ G ⁻¹' {w.2} := by
    intro w x hx
    have hx' : (F x, G x) = w := hx
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    rw [← hx']
  have hPfst : ∀ w : V × V, w.1 ≠ 0 → μ ((fun x => (F x, G x)) ⁻¹' {w}) ≠ ⊤ := fun w hw =>
    ne_top_of_le_ne_top (hFfin w.1 hw) (measure_mono (hsub1 w))
  have hPsnd : ∀ w : V × V, w.2 ≠ 0 → μ ((fun x => (F x, G x)) ⁻¹' {w}) ≠ ⊤ := fun w hw =>
    ne_top_of_le_ne_top (hGfin w.2 hw) (measure_mono (hsub2 w))
  have e1 : finiteRangeIntegral 𝕜 μ (fun x => F x + G x)
      = ∑ w ∈ hP.toFinset, measureCoeff 𝕜 μ ((fun x => (F x, G x)) ⁻¹' {w}) • (w.1 + w.2) := by
    refine finiteRangeIntegral_comp_eq_sum 𝕜 μ hP hPm (fun w => w.1 + w.2) ?_
    intro w hw
    by_cases h1 : w.1 = 0
    · refine hPsnd w ?_
      intro h2
      exact hw (by show w.1 + w.2 = 0; rw [h1, h2, add_zero])
    · exact hPfst w h1
  have e2 : finiteRangeIntegral 𝕜 μ F
      = ∑ w ∈ hP.toFinset, measureCoeff 𝕜 μ ((fun x => (F x, G x)) ⁻¹' {w}) • w.1 :=
    finiteRangeIntegral_comp_eq_sum 𝕜 μ hP hPm Prod.fst hPfst
  have e3 : finiteRangeIntegral 𝕜 μ G
      = ∑ w ∈ hP.toFinset, measureCoeff 𝕜 μ ((fun x => (F x, G x)) ⁻¹' {w}) • w.2 :=
    finiteRangeIntegral_comp_eq_sum 𝕜 μ hP hPm Prod.snd hPsnd
  rw [e1, e2, e3, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [smul_add]

theorem finiteRangeIntegral_const_smul (μ : Measure X) {F : X → V}
    (hF : (Set.range F).Finite) (hFm : ∀ w : V, MeasurableSet (F ⁻¹' {w}))
    (hFfin : ∀ w : V, w ≠ 0 → μ (F ⁻¹' {w}) ≠ ⊤) (c : 𝕜) :
    finiteRangeIntegral 𝕜 μ (fun x => c • F x) = c • finiteRangeIntegral 𝕜 μ F := by
  classical
  have h1 : finiteRangeIntegral 𝕜 μ (fun x => c • F x)
      = ∑ w ∈ hF.toFinset, measureCoeff 𝕜 μ (F ⁻¹' {w}) • (c • w) :=
    finiteRangeIntegral_comp_eq_sum 𝕜 μ hF hFm (fun w => c • w)
      (fun w hw => hFfin w (fun h0 => hw (by rw [h0]; exact smul_zero c)))
  have h2 : finiteRangeIntegral 𝕜 μ F
      = ∑ w ∈ hF.toFinset, measureCoeff 𝕜 μ (F ⁻¹' {w}) • w :=
    finiteRangeIntegral_comp_eq_sum 𝕜 μ hF hFm (fun w => w) (fun w hw => hFfin w hw)
  rw [h1, h2, Finset.smul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [smul_comm]

theorem finiteRangeIntegral_distrib_smul {M : Type*} [Monoid M] [DistribMulAction M V]
    [SMulCommClass M 𝕜 V] (μ : Measure X) {F : X → V}
    (hF : (Set.range F).Finite) (hFm : ∀ w : V, MeasurableSet (F ⁻¹' {w}))
    (hFfin : ∀ w : V, w ≠ 0 → μ (F ⁻¹' {w}) ≠ ⊤) (m : M) :
    finiteRangeIntegral 𝕜 μ (fun x => m • F x) = m • finiteRangeIntegral 𝕜 μ F := by
  classical
  have h1 : finiteRangeIntegral 𝕜 μ (fun x => m • F x)
      = ∑ w ∈ hF.toFinset, measureCoeff 𝕜 μ (F ⁻¹' {w}) • (m • w) :=
    finiteRangeIntegral_comp_eq_sum 𝕜 μ hF hFm (fun w => m • w)
      (fun w hw => hFfin w (fun h0 => hw (by rw [h0]; exact smul_zero m)))
  have h2 : finiteRangeIntegral 𝕜 μ F
      = ∑ w ∈ hF.toFinset, measureCoeff 𝕜 μ (F ⁻¹' {w}) • w :=
    finiteRangeIntegral_comp_eq_sum 𝕜 μ hF hFm (fun w => w) (fun w hw => hFfin w hw)
  rw [h1, h2, Finset.smul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  exact (smul_comm m (measureCoeff 𝕜 μ (F ⁻¹' {w})) w).symm

theorem finiteRangeIntegral_comp_mulLeft {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul G] (μ : Measure G) [μ.IsMulLeftInvariant] {F : G → V}
    (hF : (Set.range F).Finite) (a : G) :
    finiteRangeIntegral 𝕜 μ (fun x => F (a * x)) = finiteRangeIntegral 𝕜 μ F := by
  classical
  have hreq : (Set.range fun x => F (a * x)) = Set.range F := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨a * x, rfl⟩
    · rintro ⟨x, rfl⟩
      exact ⟨a⁻¹ * x, by show F (a * (a⁻¹ * x)) = F x; rw [mul_inv_cancel_left]⟩
  have hrange : (Set.range fun x => F (a * x)).Finite := by
    rw [hreq]
    exact hF
  rw [finiteRangeIntegral_eq_sum 𝕜 μ hrange (T := hF.toFinset)
      (fun x _ => hF.mem_toFinset.mpr ⟨a * x, rfl⟩),
    finiteRangeIntegral_eq_sum 𝕜 μ hF (T := hF.toFinset)
      (fun x _ => hF.mem_toFinset.mpr ⟨x, rfl⟩)]
  refine Finset.sum_congr rfl fun w _ => ?_
  have hμ : μ ((fun x => F (a * x)) ⁻¹' {w}) = μ (F ⁻¹' {w}) := by
    have hset : (fun x => F (a * x)) ⁻¹' {w} = (fun x => a * x) ⁻¹' (F ⁻¹' {w}) := rfl
    rw [hset]
    exact measure_preimage_mul μ a _
  rw [measureCoeff_congr 𝕜 μ hμ]

theorem finiteRangeIntegral_comp_mulRight {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul G] (μ : Measure G) [μ.IsMulRightInvariant] {F : G → V}
    (hF : (Set.range F).Finite) (a : G) :
    finiteRangeIntegral 𝕜 μ (fun x => F (x * a)) = finiteRangeIntegral 𝕜 μ F := by
  classical
  have hreq : (Set.range fun x => F (x * a)) = Set.range F := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x * a, rfl⟩
    · rintro ⟨x, rfl⟩
      exact ⟨x * a⁻¹, by show F (x * a⁻¹ * a) = F x; rw [inv_mul_cancel_right]⟩
  have hrange : (Set.range fun x => F (x * a)).Finite := by
    rw [hreq]
    exact hF
  rw [finiteRangeIntegral_eq_sum 𝕜 μ hrange (T := hF.toFinset)
      (fun x _ => hF.mem_toFinset.mpr ⟨x * a, rfl⟩),
    finiteRangeIntegral_eq_sum 𝕜 μ hF (T := hF.toFinset)
      (fun x _ => hF.mem_toFinset.mpr ⟨x, rfl⟩)]
  refine Finset.sum_congr rfl fun w _ => ?_
  have hμ : μ ((fun x => F (x * a)) ⁻¹' {w}) = μ (F ⁻¹' {w}) := by
    have hset : (fun x => F (x * a)) ⁻¹' {w} = (fun x => x * a) ⁻¹' (F ⁻¹' {w}) := rfl
    rw [hset]
    exact measure_preimage_mul_right μ a _
  rw [measureCoeff_congr 𝕜 μ hμ]

end FiniteRangeIntegral

section Integrand

variable {𝕜 : Type*} [CommRing 𝕜] [Algebra ℝ 𝕜]
variable {V : Type*} [AddCommGroup V] [Module 𝕜 V]

theorem finite_range_of_isLocallyConstant_of_hasCompactSupport {X : Type*} [TopologicalSpace X]
    {E : Type*} [Zero E] {F : X → E} (hlc : IsLocallyConstant F) (hsupp : HasCompactSupport F) :
    (Set.range F).Finite := by
  have hcs : IsCompact (tsupport F) := hsupp
  haveI hcsp : CompactSpace (tsupport F) := isCompact_iff_compactSpace.mp hcs
  have h1 : IsLocallyConstant fun x : tsupport F => F (x : X) :=
    hlc.comp_continuous continuous_subtype_val
  have h2 : (F '' tsupport F).Finite := by
    rw [Set.image_eq_range]
    exact h1.range_finite
  refine (h2.insert 0).subset ?_
  rintro _ ⟨x, rfl⟩
  by_cases hx : x ∈ tsupport F
  · exact Set.mem_insert_of_mem _ (Set.mem_image_of_mem _ hx)
  · rw [image_eq_zero_of_notMem_tsupport hx]
    exact Set.mem_insert _ _

variable {G : Type*} [Group G] [TopologicalSpace G] [ContinuousMul G]
variable [DistribMulAction G V] [SMulCommClass G 𝕜 V]

omit [Algebra ℝ 𝕜] [SMulCommClass G 𝕜 V] in
theorem isLocallyConstant_heckeIntegrand {f : G → 𝕜} (hf : IsLocallyConstant f) {v : V}
    (hv : HasOpenStabilizer G v) :
    IsLocallyConstant fun g => f g • g • v := by
  rw [IsLocallyConstant.iff_exists_open]
  intro g₀
  refine ⟨{g : G | f g = f g₀} ∩
    (fun g : G => g₀⁻¹ * g) ⁻¹' ((MulAction.stabilizer G v : Subgroup G) : Set G), ?_, ?_, ?_⟩
  · exact (hf.isOpen_fiber (f g₀)).inter
      (hv.preimage (continuous_const.mul continuous_id))
  · refine ⟨rfl, ?_⟩
    show g₀⁻¹ * g₀ ∈ ((MulAction.stabilizer G v : Subgroup G) : Set G)
    rw [inv_mul_cancel]
    exact (MulAction.stabilizer G v).one_mem
  · rintro g ⟨hg1, hg2⟩
    have hstab : (g₀⁻¹ * g) • v = v := MulAction.mem_stabilizer_iff.mp hg2
    have hgv : g • v = g₀ • v := by
      calc g • v = (g₀ * (g₀⁻¹ * g)) • v := by rw [mul_inv_cancel_left]
        _ = g₀ • (g₀⁻¹ * g) • v := by rw [mul_smul]
        _ = g₀ • v := by rw [hstab]
    have hfg : f g = f g₀ := hg1
    rw [hfg, hgv]

omit [Algebra ℝ 𝕜] [TopologicalSpace G] [ContinuousMul G] [SMulCommClass G 𝕜 V] in
theorem support_heckeIntegrand_subset (f : G → 𝕜) (v : V) :
    (Function.support fun g => f g • g • v) ⊆ Function.support f := by
  intro g hg
  rw [Function.mem_support] at hg ⊢
  intro h0
  exact hg (by rw [h0, zero_smul])

omit [Algebra ℝ 𝕜] [ContinuousMul G] [SMulCommClass G 𝕜 V] in
theorem hasCompactSupport_heckeIntegrand {f : G → 𝕜} (hf : HasCompactSupport f) (v : V) :
    HasCompactSupport fun g => f g • g • v :=
  hf.mono (support_heckeIntegrand_subset f v)

omit [Algebra ℝ 𝕜] [SMulCommClass G 𝕜 V] in
theorem finite_range_heckeIntegrand {f : G → 𝕜} (hf : IsLocallyConstant f)
    (hf' : HasCompactSupport f) {v : V} (hv : HasOpenStabilizer G v) :
    (Set.range fun g => f g • g • v).Finite :=
  finite_range_of_isLocallyConstant_of_hasCompactSupport
    (isLocallyConstant_heckeIntegrand hf hv) (hasCompactSupport_heckeIntegrand hf' v)

omit [Algebra ℝ 𝕜] [SMulCommClass G 𝕜 V] in
theorem measurableSet_fiber_heckeIntegrand [MeasurableSpace G] [OpensMeasurableSpace G]
    {f : G → 𝕜} (hf : IsLocallyConstant f) {v : V} (hv : HasOpenStabilizer G v) (w : V) :
    MeasurableSet ((fun g => f g • g • v) ⁻¹' {w}) :=
  ((isLocallyConstant_heckeIntegrand hf hv).isOpen_fiber w).measurableSet

omit [Algebra ℝ 𝕜] [ContinuousMul G] [SMulCommClass G 𝕜 V] in
theorem measure_fiber_heckeIntegrand_ne_top [MeasurableSpace G] (μ : Measure G)
    [IsFiniteMeasureOnCompacts μ] {f : G → 𝕜} (hf' : HasCompactSupport f) (v : V) {w : V}
    (hw : w ≠ 0) : μ ((fun g => f g • g • v) ⁻¹' {w}) ≠ ⊤ := by
  have hK : IsCompact (tsupport f) := hf'
  have hsub : (fun g => f g • g • v) ⁻¹' {w} ⊆ tsupport f := by
    intro g hg
    have hgw : f g • g • v = w := hg
    refine subset_tsupport f ?_
    rw [Function.mem_support]
    intro h0
    exact hw (by rw [← hgw, h0, zero_smul])
  exact ne_top_of_le_ne_top hK.measure_lt_top.ne (measure_mono hsub)

end Integrand

section HeckeSmul

variable {𝕜 : Type*} [CommRing 𝕜] [Algebra ℝ 𝕜]
variable {V : Type*} [AddCommGroup V] [Module 𝕜 V]
variable {G : Type*} [Group G] [MeasurableSpace G]
variable [DistribMulAction G V] [SMulCommClass G 𝕜 V]

noncomputable def heckeSmul (μ : Measure G) (f : G → 𝕜) (v : V) : V :=
  finiteRangeIntegral 𝕜 μ fun g => f g • g • v

omit [SMulCommClass G 𝕜 V] in
theorem heckeSmul_def (μ : Measure G) (f : G → 𝕜) (v : V) :
    heckeSmul μ f v = finiteRangeIntegral 𝕜 μ fun g => f g • g • v := rfl

omit [SMulCommClass G 𝕜 V] in
theorem heckeSmul_zero_vector (μ : Measure G) (f : G → 𝕜) :
    heckeSmul μ f (0 : V) = 0 := by
  have h : (fun g => f g • g • (0 : V)) = fun _ : G => (0 : V) := by
    funext g
    rw [smul_zero, smul_zero]
  rw [heckeSmul_def, h]
  exact finiteRangeIntegral_zero 𝕜 μ

variable [TopologicalSpace G] [ContinuousMul G]

omit [SMulCommClass G 𝕜 V] in
theorem heckeSmul_eq_sum (μ : Measure G) {f : G → 𝕜} (hf : IsLocallyConstant f)
    (hf' : HasCompactSupport f) {v : V} (hv : HasOpenStabilizer G v) {T : Finset V}
    (hT : ∀ g : G, f g • g • v ≠ 0 → f g • g • v ∈ T) :
    heckeSmul μ f v = ∑ w ∈ T, measureCoeff 𝕜 μ ((fun g => f g • g • v) ⁻¹' {w}) • w :=
  finiteRangeIntegral_eq_sum 𝕜 μ (finite_range_heckeIntegrand hf hf' hv) hT

omit [SMulCommClass G 𝕜 V] in
theorem heckeSmul_add_right [OpensMeasurableSpace G] (μ : Measure G)
    [IsFiniteMeasureOnCompacts μ] {f : G → 𝕜} (hf : IsLocallyConstant f)
    (hf' : HasCompactSupport f) {v w : V} (hv : HasOpenStabilizer G v) (hw : HasOpenStabilizer G w) :
    heckeSmul μ f (v + w) = heckeSmul μ f v + heckeSmul μ f w := by
  have h : (fun g => f g • g • (v + w)) = fun g => (f g • g • v) + (f g • g • w) := by
    funext g
    rw [smul_add, smul_add]
  rw [heckeSmul_def, h]
  exact finiteRangeIntegral_add 𝕜 μ
    (finite_range_heckeIntegrand hf hf' hv) (finite_range_heckeIntegrand hf hf' hw)
    (measurableSet_fiber_heckeIntegrand hf hv) (measurableSet_fiber_heckeIntegrand hf hw)
    (fun x hx => measure_fiber_heckeIntegrand_ne_top μ hf' v hx)
    (fun x hx => measure_fiber_heckeIntegrand_ne_top μ hf' w hx)

theorem heckeSmul_smul_right [OpensMeasurableSpace G] (μ : Measure G)
    [IsFiniteMeasureOnCompacts μ] {f : G → 𝕜} (hf : IsLocallyConstant f)
    (hf' : HasCompactSupport f) {v : V} (hv : HasOpenStabilizer G v) (c : 𝕜) :
    heckeSmul μ f (c • v) = c • heckeSmul μ f v := by
  have h : (fun g => f g • g • (c • v)) = fun g => c • (f g • g • v) := by
    funext g
    rw [smul_comm (g : G) c v, smul_comm (f g) c (g • v)]
  rw [heckeSmul_def, h]
  exact finiteRangeIntegral_const_smul 𝕜 μ (finite_range_heckeIntegrand hf hf' hv)
    (measurableSet_fiber_heckeIntegrand hf hv)
    (fun x hx => measure_fiber_heckeIntegrand_ne_top μ hf' v hx) c

theorem heckeSmul_neg_right [OpensMeasurableSpace G] (μ : Measure G)
    [IsFiniteMeasureOnCompacts μ] {f : G → 𝕜} (hf : IsLocallyConstant f)
    (hf' : HasCompactSupport f) {w : V} (hw : HasOpenStabilizer G w) :
    heckeSmul μ f (-w) = -heckeSmul μ f w := by
  have h := heckeSmul_smul_right μ hf hf' hw (-1 : 𝕜)
  rwa [neg_one_smul, neg_one_smul] at h

theorem heckeSmul_sub_right [OpensMeasurableSpace G] (μ : Measure G)
    [IsFiniteMeasureOnCompacts μ] {f : G → 𝕜} (hf : IsLocallyConstant f)
    (hf' : HasCompactSupport f) {v w : V} (hv : HasOpenStabilizer G v) (hw : HasOpenStabilizer G w) :
    heckeSmul μ f (v - w) = heckeSmul μ f v - heckeSmul μ f w := by
  have hneg : HasOpenStabilizer G (-w) := by
    have h := hw.const_smul (-1 : 𝕜)
    rwa [neg_one_smul] at h
  rw [sub_eq_add_neg, heckeSmul_add_right μ hf hf' hv hneg,
    heckeSmul_neg_right μ hf hf' hw, ← sub_eq_add_neg]

omit [SMulCommClass G 𝕜 V] in
theorem heckeSmul_add_left [OpensMeasurableSpace G] (μ : Measure G)
    [IsFiniteMeasureOnCompacts μ] {f₁ f₂ : G → 𝕜} (hf₁ : IsLocallyConstant f₁)
    (hf₁' : HasCompactSupport f₁) (hf₂ : IsLocallyConstant f₂) (hf₂' : HasCompactSupport f₂)
    {v : V} (hv : HasOpenStabilizer G v) :
    heckeSmul μ (f₁ + f₂) v = heckeSmul μ f₁ v + heckeSmul μ f₂ v := by
  have h : (fun g => (f₁ + f₂) g • g • v) = fun g => (f₁ g • g • v) + (f₂ g • g • v) := by
    funext g
    rw [Pi.add_apply, add_smul]
  rw [heckeSmul_def, h]
  exact finiteRangeIntegral_add 𝕜 μ
    (finite_range_heckeIntegrand hf₁ hf₁' hv) (finite_range_heckeIntegrand hf₂ hf₂' hv)
    (measurableSet_fiber_heckeIntegrand hf₁ hv) (measurableSet_fiber_heckeIntegrand hf₂ hv)
    (fun x hx => measure_fiber_heckeIntegrand_ne_top μ hf₁' v hx)
    (fun x hx => measure_fiber_heckeIntegrand_ne_top μ hf₂' v hx)

omit [SMulCommClass G 𝕜 V] in
theorem heckeSmul_smul_left [OpensMeasurableSpace G] (μ : Measure G)
    [IsFiniteMeasureOnCompacts μ] {f : G → 𝕜} (hf : IsLocallyConstant f)
    (hf' : HasCompactSupport f) {v : V} (hv : HasOpenStabilizer G v) (c : 𝕜) :
    heckeSmul μ (c • f) v = c • heckeSmul μ f v := by
  have h : (fun g => (c • f) g • g • v) = fun g => c • (f g • g • v) := by
    funext g
    rw [Pi.smul_apply, smul_eq_mul, mul_smul]
  rw [heckeSmul_def, h]
  exact finiteRangeIntegral_const_smul 𝕜 μ (finite_range_heckeIntegrand hf hf' hv)
    (measurableSet_fiber_heckeIntegrand hf hv)
    (fun x hx => measure_fiber_heckeIntegrand_ne_top μ hf' v hx) c

theorem heckeSmul_translate_left [OpensMeasurableSpace G] [MeasurableMul G] (μ : Measure G)
    [μ.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts μ] {f : G → 𝕜} (hf : IsLocallyConstant f)
    (hf' : HasCompactSupport f) {v : V} (hv : HasOpenStabilizer G v) (g : G) :
    heckeSmul μ (fun h => f (g⁻¹ * h)) v = g • heckeSmul μ f v := by

  have hB : heckeSmul μ (fun h => f (g⁻¹ * h)) v
      = finiteRangeIntegral 𝕜 μ fun h => g • (f (g⁻¹ * h) • (g⁻¹ * h) • v) := by
    rw [heckeSmul_def]
    congr 1
    funext h
    rw [smul_comm g (f (g⁻¹ * h)) ((g⁻¹ * h) • v), ← mul_smul, mul_inv_cancel_left]

  have hFg : (Set.range fun x : G => g • (f x • x • v)).Finite := by
    refine ((finite_range_heckeIntegrand hf hf' hv).image (fun w => g • w)).subset ?_
    rintro _ ⟨x, rfl⟩
    exact ⟨f x • x • v, ⟨x, rfl⟩, rfl⟩
  have hC : finiteRangeIntegral 𝕜 μ (fun h => g • (f (g⁻¹ * h) • (g⁻¹ * h) • v))
      = finiteRangeIntegral 𝕜 μ fun x => g • (f x • x • v) :=
    finiteRangeIntegral_comp_mulLeft 𝕜 μ (F := fun x => g • (f x • x • v)) hFg g⁻¹

  have hD : finiteRangeIntegral 𝕜 μ (fun x => g • (f x • x • v))
      = g • finiteRangeIntegral 𝕜 μ fun x => f x • x • v := by
    refine finiteRangeIntegral_distrib_smul 𝕜 μ ?_ ?_ ?_ g
    · exact finite_range_heckeIntegrand hf hf' hv
    · exact measurableSet_fiber_heckeIntegrand hf hv
    · exact fun x hx => measure_fiber_heckeIntegrand_ne_top μ hf' v hx
  rw [hB, hC, hD, heckeSmul_def]

omit [SMulCommClass G 𝕜 V] in
theorem heckeSmul_smul_vector [MeasurableMul G] (μ : Measure G)
    [μ.IsMulRightInvariant] {f : G → 𝕜} (hf : IsLocallyConstant f)
    (hf' : HasCompactSupport f) {v : V} (hv : HasOpenStabilizer G v) (k : G) :
    heckeSmul μ f (k • v) = heckeSmul μ (fun h => f (h * k⁻¹)) v := by

  have hlc' : IsLocallyConstant fun h : G => f (h * k⁻¹) :=
    hf.comp_continuous (continuous_id.mul continuous_const)
  have hcs' : HasCompactSupport fun h : G => f (h * k⁻¹) := by
    have h := hf'.comp_homeomorph (Homeomorph.mulRight k⁻¹)
    simpa only [Homeomorph.coe_mulRight, Function.comp_def] using h

  have hB : heckeSmul μ f (k • v)
      = finiteRangeIntegral 𝕜 μ fun h => f (h * k * k⁻¹) • (h * k) • v := by
    rw [heckeSmul_def]
    congr 1
    funext h
    rw [mul_inv_cancel_right, ← mul_smul]

  have hC : finiteRangeIntegral 𝕜 μ (fun h => f (h * k * k⁻¹) • (h * k) • v)
      = finiteRangeIntegral 𝕜 μ fun x => f (x * k⁻¹) • x • v :=
    finiteRangeIntegral_comp_mulRight 𝕜 μ (finite_range_heckeIntegrand hlc' hcs' hv) k
  rw [hB, hC, heckeSmul_def]

end HeckeSmul

section Idempotent

variable (𝕜 : Type*) [CommRing 𝕜] [Algebra ℝ 𝕜]
variable {G : Type*}

noncomputable def heckeIdempotent [MeasurableSpace G] (μ : Measure G) (K : Set G) : G → 𝕜 :=
  K.indicator fun _ => algebraMap ℝ 𝕜 ((μ K).toReal)⁻¹

theorem heckeIdempotent_def [MeasurableSpace G] (μ : Measure G) (K : Set G) :
    heckeIdempotent 𝕜 μ K = K.indicator fun _ => algebraMap ℝ 𝕜 ((μ K).toReal)⁻¹ := rfl

theorem heckeIdempotent_apply_of_mem [MeasurableSpace G] (μ : Measure G) {K : Set G} {g : G}
    (hg : g ∈ K) : heckeIdempotent 𝕜 μ K g = algebraMap ℝ 𝕜 ((μ K).toReal)⁻¹ :=
  Set.indicator_of_mem hg _

theorem heckeIdempotent_apply_of_notMem [MeasurableSpace G] (μ : Measure G) {K : Set G} {g : G}
    (hg : g ∉ K) : heckeIdempotent 𝕜 μ K g = 0 :=
  Set.indicator_of_notMem hg _

theorem isLocallyConstant_heckeIdempotent [MeasurableSpace G] [TopologicalSpace G]
    (μ : Measure G) {K : Set G} (hK : IsClopen K) :
    IsLocallyConstant (heckeIdempotent 𝕜 μ K) :=
  isLocallyConstant_indicator_const_of_isClopen hK _

theorem hasCompactSupport_heckeIdempotent [MeasurableSpace G] [TopologicalSpace G]
    (μ : Measure G) {K : Set G} (hKc : IsCompact K) (hKcl : IsClosed K) :
    HasCompactSupport (heckeIdempotent 𝕜 μ K) :=
  HasCompactSupport.intro' hKc hKcl fun _x hx => Set.indicator_of_notMem hx _

variable {𝕜}
variable {V : Type*} [AddCommGroup V] [Module 𝕜 V]
variable [Group G] [MeasurableSpace G] [DistribMulAction G V] [SMulCommClass G 𝕜 V]

omit [SMulCommClass G 𝕜 V] in
theorem heckeSmul_indicator_of_forall_smul_eq (μ : Measure G) {K : Set G} (c : 𝕜) {v : V}
    (hfix : ∀ k ∈ K, k • v = v) :
    heckeSmul μ (K.indicator fun _ => c) v = (measureCoeff 𝕜 μ K * c) • v := by
  have h : (fun g => (K.indicator fun _ => c) g • g • v)
      = K.indicator fun _ => c • v := by
    funext g
    by_cases hg : g ∈ K
    · rw [Set.indicator_of_mem hg, Set.indicator_of_mem hg, hfix g hg]
    · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem hg, zero_smul]
  rw [heckeSmul_def, h, finiteRangeIntegral_indicator_const, smul_smul]

omit [SMulCommClass G 𝕜 V] in
theorem heckeSmul_heckeIdempotent_of_forall_smul_eq (μ : Measure G) {K : Set G}
    (hKne : μ K ≠ 0) (hKfin : μ K ≠ ⊤) {v : V} (hfix : ∀ k ∈ K, k • v = v) :
    heckeSmul μ (heckeIdempotent 𝕜 μ K) v = v := by
  have h := heckeSmul_indicator_of_forall_smul_eq μ
    (K := K) (algebraMap ℝ 𝕜 ((μ K).toReal)⁻¹) hfix
  rw [heckeIdempotent_def, h, measureCoeff_def, ← map_mul,
    mul_inv_cancel₀ (ENNReal.toReal_ne_zero.mpr ⟨hKne, hKfin⟩), map_one, one_smul]

variable [TopologicalSpace G] [ContinuousMul G]

omit [SMulCommClass G 𝕜 V] in
theorem exists_isLocallyConstant_hasCompactSupport_heckeSmul_eq_self
    (μ : Measure G) [μ.IsOpenPosMeasure] [IsFiniteMeasureOnCompacts μ]
    (hex : ∃ K : Subgroup G, IsCompact (K : Set G) ∧ IsOpen (K : Set G)) {v : V}
    (hv : HasOpenStabilizer G v) :
    ∃ f : G → 𝕜, IsLocallyConstant f ∧ HasCompactSupport f ∧ heckeSmul μ f v = v := by
  obtain ⟨K, hKc, hKo, hKfix⟩ :=
    (hasOpenStabilizer_iff_exists_isCompact_isOpen_subgroup hex).mp hv
  have hKne : μ (K : Set G) ≠ 0 := hKo.measure_ne_zero μ ⟨1, K.one_mem⟩
  have hKfin : μ (K : Set G) ≠ ⊤ := hKc.measure_lt_top.ne
  refine ⟨heckeIdempotent 𝕜 μ (K : Set G), ?_, ?_, ?_⟩
  · exact isLocallyConstant_heckeIdempotent 𝕜 μ ⟨Subgroup.isClosed_of_isOpen _ hKo, hKo⟩
  · exact hasCompactSupport_heckeIdempotent 𝕜 μ hKc (Subgroup.isClosed_of_isOpen _ hKo)
  · exact heckeSmul_heckeIdempotent_of_forall_smul_eq μ hKne hKfin
      (fun k hk => hKfix k hk)

end Idempotent

section Projection

variable {𝕜 : Type*} [CommRing 𝕜] [Algebra ℝ 𝕜]
variable {V : Type*} [AddCommGroup V] [Module 𝕜 V]
variable {G : Type*} [Group G] [TopologicalSpace G] [ContinuousMul G] [MeasurableSpace G]
variable [DistribMulAction G V] [SMulCommClass G 𝕜 V]

variable (𝕜) in
def fixedPointsSubmodule (K : Subgroup G) : Submodule 𝕜 V where
  carrier := {v : V | ∀ k ∈ K, k • v = v}
  zero_mem' := fun k _ => smul_zero k
  add_mem' := by
    intro v w hv hw k hk
    rw [smul_add, hv k hk, hw k hk]
  smul_mem' := by
    intro c v hv k hk
    rw [smul_comm, hv k hk]

variable (𝕜) in
def augmentationSubmodule (K : Subgroup G) : Submodule 𝕜 V :=
  Submodule.span 𝕜 {x : V | ∃ k ∈ K, ∃ u : V, k • u - u = x}

omit [Algebra ℝ 𝕜] [TopologicalSpace G] [ContinuousMul G] [MeasurableSpace G] in
theorem mem_fixedPointsSubmodule_iff {K : Subgroup G} {v : V} :
    v ∈ fixedPointsSubmodule 𝕜 K ↔ ∀ k ∈ K, k • v = v := Iff.rfl

omit [Algebra ℝ 𝕜] [TopologicalSpace G] [ContinuousMul G] [MeasurableSpace G] [SMulCommClass G 𝕜 V] in
theorem smul_sub_self_mem_augmentationSubmodule {K : Subgroup G} {k : G} (hk : k ∈ K) (u : V) :
    k • u - u ∈ augmentationSubmodule 𝕜 K :=
  Submodule.subset_span ⟨k, hk, u, rfl⟩

omit [Algebra ℝ 𝕜] [MeasurableSpace G] in
theorem hasOpenStabilizer_of_mem_fixedPointsSubmodule {K : Subgroup G}
    (hKo : IsOpen (K : Set G)) {v : V} (hv : v ∈ fixedPointsSubmodule 𝕜 K) :
    HasOpenStabilizer G v :=
  (hasOpenStabilizer_iff_exists_isOpen_subgroup).mpr ⟨K, hKo, hv⟩

theorem heckeSmul_heckeIdempotent_mem_fixedPoints [OpensMeasurableSpace G] [MeasurableMul G]
    (μ : Measure G) [μ.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts μ] {K : Subgroup G}
    (hKo : IsOpen (K : Set G)) (hKc : IsCompact (K : Set G)) {w : V} (hw : HasOpenStabilizer G w) :
    heckeSmul μ (heckeIdempotent 𝕜 μ (K : Set G)) w ∈ fixedPointsSubmodule 𝕜 K := by
  refine (mem_fixedPointsSubmodule_iff).mpr fun k hk => ?_
  have hlc : IsLocallyConstant (heckeIdempotent 𝕜 μ (K : Set G)) :=
    isLocallyConstant_heckeIdempotent 𝕜 μ ⟨Subgroup.isClosed_of_isOpen _ hKo, hKo⟩
  have hcs : HasCompactSupport (heckeIdempotent 𝕜 μ (K : Set G)) :=
    hasCompactSupport_heckeIdempotent 𝕜 μ hKc (Subgroup.isClosed_of_isOpen _ hKo)
  have htrans := heckeSmul_translate_left μ hlc hcs hw k
  have hinv : (fun h => heckeIdempotent 𝕜 μ (K : Set G) (k⁻¹ * h))
      = heckeIdempotent 𝕜 μ (K : Set G) := by
    funext h
    by_cases hh : h ∈ (K : Set G)
    · rw [heckeIdempotent_apply_of_mem 𝕜 μ hh,
        heckeIdempotent_apply_of_mem 𝕜 μ (by exact (mul_mem_cancel_left (K.inv_mem hk)).mpr hh)]
    · rw [heckeIdempotent_apply_of_notMem 𝕜 μ hh, heckeIdempotent_apply_of_notMem 𝕜 μ
        (by exact fun hmem => hh ((mul_mem_cancel_left (K.inv_mem hk)).mp hmem))]
  rw [hinv] at htrans
  exact htrans.symm

theorem heckeSmul_heckeIdempotent_idem [OpensMeasurableSpace G] [MeasurableMul G]
    (μ : Measure G) [μ.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts μ] {K : Subgroup G}
    (hKo : IsOpen (K : Set G)) (hKc : IsCompact (K : Set G)) (hKne : μ (K : Set G) ≠ 0)
    {w : V} (hw : HasOpenStabilizer G w) :
    heckeSmul μ (heckeIdempotent 𝕜 μ (K : Set G))
        (heckeSmul μ (heckeIdempotent 𝕜 μ (K : Set G)) w)
      = heckeSmul μ (heckeIdempotent 𝕜 μ (K : Set G)) w :=
  heckeSmul_heckeIdempotent_of_forall_smul_eq μ hKne hKc.measure_lt_top.ne
    (fun k hk => (mem_fixedPointsSubmodule_iff.mp
      (heckeSmul_heckeIdempotent_mem_fixedPoints μ hKo hKc hw)) k hk)

omit [SMulCommClass G 𝕜 V] in
theorem measureCoeff_smul_sub_heckeSmul_indicator_mem_augmentation [OpensMeasurableSpace G]
    (μ : Measure G) [IsFiniteMeasureOnCompacts μ] {K : Subgroup G}
    (hKo : IsOpen (K : Set G)) (hKc : IsCompact (K : Set G)) {u : V}
    (hu : HasOpenStabilizer G u) :
    measureCoeff 𝕜 μ (K : Set G) • u
        - heckeSmul μ ((K : Set G).indicator fun _ => (1 : 𝕜)) u
      ∈ augmentationSubmodule 𝕜 K := by
  classical
  by_cases hu0 : u = 0
  · subst hu0
    rw [heckeSmul_zero_vector, smul_zero, sub_zero]
    exact Submodule.zero_mem _
  have hKclopen : IsClopen (K : Set G) := ⟨Subgroup.isClosed_of_isOpen _ hKo, hKo⟩
  have hlc : IsLocallyConstant ((K : Set G).indicator fun _ => (1 : 𝕜)) :=
    isLocallyConstant_indicator_const_of_isClopen hKclopen _
  have hcs : HasCompactSupport ((K : Set G).indicator fun _ => (1 : 𝕜)) :=
    HasCompactSupport.intro' hKc hKclopen.1 fun _x hx => Set.indicator_of_notMem hx _
  have hKfin : μ (K : Set G) ≠ ⊤ := hKc.measure_lt_top.ne
  have hFrange : (Set.range fun g => ((K : Set G).indicator fun _ => (1 : 𝕜)) g • g • u).Finite :=
    finite_range_heckeIntegrand hlc hcs hu
  have hFmeas : ∀ x : V,
      MeasurableSet ((fun g => ((K : Set G).indicator fun _ => (1 : 𝕜)) g • g • u) ⁻¹' {x}) :=
    measurableSet_fiber_heckeIntegrand hlc hu

  have hFmem : ∀ g ∈ (K : Set G),
      ((K : Set G).indicator fun _ => (1 : 𝕜)) g • g • u = g • u := by
    intro g hg
    rw [Set.indicator_of_mem hg, one_smul]
  have hFnotMem : ∀ g : G, g ∉ (K : Set G) →
      ((K : Set G).indicator fun _ => (1 : 𝕜)) g • g • u = 0 := by
    intro g hg
    rw [Set.indicator_of_notMem hg, zero_smul]
  have hFne : ∀ g ∈ (K : Set G),
      ((K : Set G).indicator fun _ => (1 : 𝕜)) g • g • u ≠ 0 := by
    intro g hg h0
    rw [hFmem g hg] at h0
    exact hu0 (by simpa using congrArg (fun x => g⁻¹ • x) h0)

  have hTmem : ∀ g : G, ((K : Set G).indicator fun _ => (1 : 𝕜)) g • g • u ≠ 0 →
      ((K : Set G).indicator fun _ => (1 : 𝕜)) g • g • u ∈ hFrange.toFinset.erase 0 := by
    intro g hg
    exact Finset.mem_erase.mpr ⟨hg, hFrange.mem_toFinset.mpr ⟨g, rfl⟩⟩
  have hTne : ∀ x ∈ hFrange.toFinset.erase 0, x ≠ 0 := fun x hx => (Finset.mem_erase.mp hx).1
  have hTrep : ∀ x ∈ hFrange.toFinset.erase 0, ∃ g ∈ (K : Set G), g • u = x := by
    intro x hx
    obtain ⟨g, hg⟩ := hFrange.mem_toFinset.mp (Finset.mem_of_mem_erase hx)
    by_cases hgK : g ∈ (K : Set G)
    · exact ⟨g, hgK, (hFmem g hgK).symm.trans hg⟩
    · exact absurd (by rw [← hg]; exact hFnotMem g hgK) (hTne x hx)

  have hcover : (K : Set G)
      = ⋃ x ∈ hFrange.toFinset.erase 0,
          (fun g => ((K : Set G).indicator fun _ => (1 : 𝕜)) g • g • u) ⁻¹' {x} := by
    ext g
    simp only [Set.mem_iUnion, Set.mem_preimage, Set.mem_singleton_iff, exists_prop]
    constructor
    · intro hg
      exact ⟨((K : Set G).indicator fun _ => (1 : 𝕜)) g • g • u, hTmem g (hFne g hg), rfl⟩
    · rintro ⟨x, hxT, hgx⟩
      by_contra hgK
      exact hTne x hxT (by rw [← hgx]; exact hFnotMem g hgK)
  have hfibsub : ∀ x ∈ hFrange.toFinset.erase 0,
      (fun g => ((K : Set G).indicator fun _ => (1 : 𝕜)) g • g • u) ⁻¹' {x} ⊆ (K : Set G) := by
    intro x hx g hg
    by_contra hgK
    exact hTne x hx (by rw [← Set.mem_singleton_iff.mp hg]; exact hFnotMem g hgK)
  have hfibtop : ∀ x ∈ hFrange.toFinset.erase 0,
      μ ((fun g => ((K : Set G).indicator fun _ => (1 : 𝕜)) g • g • u) ⁻¹' {x}) ≠ ⊤ :=
    fun x hx => ne_top_of_le_ne_top hKfin (measure_mono (hfibsub x hx))

  have hmass : μ (K : Set G) = ∑ x ∈ hFrange.toFinset.erase 0,
      μ ((fun g => ((K : Set G).indicator fun _ => (1 : 𝕜)) g • g • u) ⁻¹' {x}) := by
    conv_lhs => rw [hcover]
    exact measure_biUnion_finset
      (Set.pairwiseDisjoint_fiber (fun g => ((K : Set G).indicator fun _ => (1 : 𝕜)) g • g • u) _)
      fun x _ => hFmeas x
  have hcoeffsum : measureCoeff 𝕜 μ (K : Set G)
      = ∑ x ∈ hFrange.toFinset.erase 0,
          measureCoeff 𝕜 μ
            ((fun g => ((K : Set G).indicator fun _ => (1 : 𝕜)) g • g • u) ⁻¹' {x}) := by
    simp only [measureCoeff_def]
    rw [hmass, ENNReal.toReal_sum hfibtop, map_sum]

  have hsum : heckeSmul μ ((K : Set G).indicator fun _ => (1 : 𝕜)) u
      = ∑ x ∈ hFrange.toFinset.erase 0,
          measureCoeff 𝕜 μ
            ((fun g => ((K : Set G).indicator fun _ => (1 : 𝕜)) g • g • u) ⁻¹' {x}) • x :=
    finiteRangeIntegral_eq_sum 𝕜 μ hFrange hTmem

  rw [hsum, hcoeffsum, Finset.sum_smul, ← Finset.sum_sub_distrib]
  refine Submodule.sum_mem _ fun x hx => ?_
  obtain ⟨g, hgK, hgx⟩ := hTrep x hx
  rw [← hgx, ← smul_sub, ← neg_sub (g • u) u]
  exact Submodule.smul_mem _ _
    (Submodule.neg_mem _ (smul_sub_self_mem_augmentationSubmodule hgK u))

theorem sub_heckeSmul_heckeIdempotent_mem_augmentation [OpensMeasurableSpace G]
    (μ : Measure G) [IsFiniteMeasureOnCompacts μ] {K : Subgroup G}
    (hKo : IsOpen (K : Set G)) (hKc : IsCompact (K : Set G)) (hKne : μ (K : Set G) ≠ 0)
    {w : V} (hw : HasOpenStabilizer G w) :
    w - heckeSmul μ (heckeIdempotent 𝕜 μ (K : Set G)) w ∈ augmentationSubmodule 𝕜 K := by
  have hKfin : μ (K : Set G) ≠ ⊤ := hKc.measure_lt_top.ne

  have hpoint : (fun g => heckeIdempotent 𝕜 μ (K : Set G) g • g • w)
      = fun g => ((K : Set G).indicator fun _ => (1 : 𝕜)) g • g •
          (algebraMap ℝ 𝕜 ((μ (K : Set G)).toReal)⁻¹ • w) := by
    funext g
    by_cases hg : g ∈ (K : Set G)
    · rw [heckeIdempotent_apply_of_mem 𝕜 μ hg, Set.indicator_of_mem hg, one_smul]
      exact (smul_comm g (algebraMap ℝ 𝕜 ((μ (K : Set G)).toReal)⁻¹) w).symm
    · rw [heckeIdempotent_apply_of_notMem 𝕜 μ hg, Set.indicator_of_notMem hg, zero_smul,
        zero_smul]
  have h1 : heckeSmul μ (heckeIdempotent 𝕜 μ (K : Set G)) w
      = heckeSmul μ ((K : Set G).indicator fun _ => (1 : 𝕜))
          (algebraMap ℝ 𝕜 ((μ (K : Set G)).toReal)⁻¹ • w) := by
    rw [heckeSmul_def, heckeSmul_def, hpoint]
  have h2 : measureCoeff 𝕜 μ (K : Set G) • (algebraMap ℝ 𝕜 ((μ (K : Set G)).toReal)⁻¹ • w)
      = w := by
    rw [measureCoeff_def, smul_smul, ← map_mul,
      mul_inv_cancel₀ (ENNReal.toReal_ne_zero.mpr ⟨hKne, hKfin⟩), map_one, one_smul]
  have h3 := measureCoeff_smul_sub_heckeSmul_indicator_mem_augmentation (𝕜 := 𝕜) μ hKo hKc
    (hw.const_smul (algebraMap ℝ 𝕜 ((μ (K : Set G)).toReal)⁻¹))
  rw [h2] at h3
  rw [h1]
  exact h3

theorem fixedPoints_sup_augmentation_eq_top [OpensMeasurableSpace G] [MeasurableMul G]
    (μ : Measure G) [μ.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts μ]
    (hsm : ∀ v : V, HasOpenStabilizer G v) {K : Subgroup G}
    (hKo : IsOpen (K : Set G)) (hKc : IsCompact (K : Set G)) (hKne : μ (K : Set G) ≠ 0) :
    (fixedPointsSubmodule 𝕜 K) ⊔ (augmentationSubmodule 𝕜 K) = (⊤ : Submodule 𝕜 V) := by
  rw [Submodule.eq_top_iff']
  intro w
  have hw : HasOpenStabilizer G w := hsm w
  have hsplit : w = heckeSmul μ (heckeIdempotent 𝕜 μ (K : Set G)) w
      + (w - heckeSmul μ (heckeIdempotent 𝕜 μ (K : Set G)) w) := by
    abel
  rw [hsplit]
  exact Submodule.add_mem _
    (Submodule.mem_sup_left (heckeSmul_heckeIdempotent_mem_fixedPoints μ hKo hKc hw))
    (Submodule.mem_sup_right (sub_heckeSmul_heckeIdempotent_mem_augmentation μ hKo hKc hKne hw))

theorem heckeSmul_heckeIdempotent_eq_zero_of_mem_augmentation [OpensMeasurableSpace G]
    [MeasurableMul G] (μ : Measure G) [μ.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μ]
    (hsm : ∀ v : V, HasOpenStabilizer G v) {K : Subgroup G}
    (hKo : IsOpen (K : Set G)) (hKc : IsCompact (K : Set G)) {x : V}
    (hx : x ∈ augmentationSubmodule 𝕜 K) :
    heckeSmul μ (heckeIdempotent 𝕜 μ (K : Set G)) x = 0 := by
  have hlc : IsLocallyConstant (heckeIdempotent 𝕜 μ (K : Set G)) :=
    isLocallyConstant_heckeIdempotent 𝕜 μ ⟨Subgroup.isClosed_of_isOpen _ hKo, hKo⟩
  have hcs : HasCompactSupport (heckeIdempotent 𝕜 μ (K : Set G)) :=
    hasCompactSupport_heckeIdempotent 𝕜 μ hKc (Subgroup.isClosed_of_isOpen _ hKo)
  refine Submodule.span_induction
    (p := fun y _ => heckeSmul μ (heckeIdempotent 𝕜 μ (K : Set G)) y = 0) ?_ ?_ ?_ ?_ hx
  ·
    rintro _ ⟨k, hk, u, rfl⟩
    have hu : HasOpenStabilizer G u := hsm u
    have hku : HasOpenStabilizer G (k • u) := hu.smul k
    rw [heckeSmul_sub_right μ hlc hcs hku hu]
    have hρ := heckeSmul_smul_vector μ hlc hcs hu k
    have hinv : (fun h => heckeIdempotent 𝕜 μ (K : Set G) (h * k⁻¹))
        = heckeIdempotent 𝕜 μ (K : Set G) := by
      funext h
      by_cases hh : h ∈ (K : Set G)
      · rw [heckeIdempotent_apply_of_mem 𝕜 μ hh, heckeIdempotent_apply_of_mem 𝕜 μ
          (by exact (mul_mem_cancel_right (K.inv_mem hk)).mpr hh)]
      · rw [heckeIdempotent_apply_of_notMem 𝕜 μ hh, heckeIdempotent_apply_of_notMem 𝕜 μ
          (by exact fun hmem => hh ((mul_mem_cancel_right (K.inv_mem hk)).mp hmem))]
    rw [hinv] at hρ
    rw [hρ, sub_self]
  ·
    exact heckeSmul_zero_vector μ _
  ·
    intro y z _ _ hy hz
    have hys : HasOpenStabilizer G y := hsm y
    have hzs : HasOpenStabilizer G z := hsm z
    rw [heckeSmul_add_right μ hlc hcs hys hzs, hy, hz, add_zero]
  ·
    intro a y _ hy
    have hys : HasOpenStabilizer G y := hsm y
    rw [heckeSmul_smul_right μ hlc hcs hys a, hy, smul_zero]

theorem disjoint_fixedPoints_augmentation [OpensMeasurableSpace G] [MeasurableMul G]
    (μ : Measure G) [μ.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μ]
    (hsm : ∀ v : V, HasOpenStabilizer G v) {K : Subgroup G}
    (hKo : IsOpen (K : Set G)) (hKc : IsCompact (K : Set G)) (hKne : μ (K : Set G) ≠ 0) :
    Disjoint (fixedPointsSubmodule 𝕜 K) (augmentationSubmodule 𝕜 K : Submodule 𝕜 V) := by
  rw [Submodule.disjoint_def]
  intro x hxfix hxaug
  have h1 : heckeSmul μ (heckeIdempotent 𝕜 μ (K : Set G)) x = x :=
    heckeSmul_heckeIdempotent_of_forall_smul_eq μ hKne hKc.measure_lt_top.ne
      (fun k hk => (mem_fixedPointsSubmodule_iff.mp hxfix) k hk)
  have h2 : heckeSmul μ (heckeIdempotent 𝕜 μ (K : Set G)) x = 0 :=
    heckeSmul_heckeIdempotent_eq_zero_of_mem_augmentation μ hsm hKo hKc hxaug
  rw [h1] at h2
  exact h2

theorem isCompl_fixedPoints_augmentation [OpensMeasurableSpace G] [MeasurableMul G]
    (μ : Measure G) [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant]
    [IsFiniteMeasureOnCompacts μ] (hsm : ∀ v : V, HasOpenStabilizer G v) {K : Subgroup G}
    (hKo : IsOpen (K : Set G)) (hKc : IsCompact (K : Set G)) (hKne : μ (K : Set G) ≠ 0) :
    IsCompl (fixedPointsSubmodule 𝕜 K) (augmentationSubmodule 𝕜 K : Submodule 𝕜 V) := by
  constructor
  · exact disjoint_fixedPoints_augmentation μ hsm hKo hKc hKne
  · rw [codisjoint_iff]
    exact fixedPoints_sup_augmentation_eq_top μ hsm hKo hKc hKne

end Projection

end TestFunctionAction


