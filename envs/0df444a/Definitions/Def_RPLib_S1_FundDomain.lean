-- Prove2me | Definitions.Def_RPLib_S1_FundDomain
-- name    : RPLib_S1_FundDomain
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-13T05:14:05.915241+00:00
-- url     : https://prove2.me/theorems/99814979-6d45-4874-bb5f-889c377994c0
-- title:
--   The standard fundamental domain for $\mathrm{SL}_2(\mathbb{Z})$ and its translates as measure-theoretic fundamental domains
-- statement:
--   Let $\mathbb{H}$ be the upper half-plane with the hyperbolic measure $d\mu = y^{-2}\,dx\,dy$ and let $$\mathcal{D} = \{\tau \in \mathbb{H} : |\tau| \ge 1,\ |\operatorname{Re}\tau| \le \tfrac12\}.$$ Since $-1$ acts trivially, the file works with the image $\overline{\Gamma}$ of a group $\Gamma \le \mathrm{SL}_2(\mathbb{Z})$ in $\mathrm{PGL}_2(\mathbb{R})$. It shows that the boundary of $\mathcal{D}$ is null, that $\mathcal{D}$ is a fundamental domain of finite measure for $\mathrm{PSL}_2(\mathbb{Z})$, and that for a subgroup $\Gamma$ of finite index the union $\bigcup_j \gamma_j^{-1}\mathcal{D}$ over coset representatives of $\pm\Gamma$ is a fundamental domain for $\Gamma$. Integrals of $\Gamma$-invariant functions over it do not depend on the representatives, and a conjugate $\alpha\mathcal{F}$ is a fundamental domain for $\alpha\Gamma\alpha^{-1}$. These facts underlie the Petersson inner product.
--
--   **Formalization note.** This file is a library module of a formalization of the Ramanujan-Petersson conjecture for holomorphic cusp forms on $\Gamma_1(M)$. It contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   F. Diamond and J. Shurman, A First Course in Modular Forms, GTM 228, Springer 2005, doi:10.1007/978-0-387-27226-9, Section 2.3 and Section 5.4

import Mathlib

/-!
# The fundamental domain of `SL(2, ℤ)` as a measure-theoretic fundamental domain

RP project, unit S1-FUNDDOM.

Since `-1 ∈ SL(2, ℤ)` acts trivially on `ℍ`, no set is a fundamental domain for `SL(2, ℤ)` itself in
the sense of Mathlib's `MeasureTheory.IsFundamentalDomain` (translates by `g` and `-g` coincide).
We therefore let the *image* of a group in `PGL(2, ℝ)` act (Mathlib's `MulAction PGL(2, ℝ) ℍ`,
which is faithful). For `Γ : Subgroup (GL (Fin 2) ℝ)` we write `pglImage Γ` for this image and
`PSL2Z = pglImage 𝒮ℒ`.

Main results
* `volume_fd_diff_fdo`, `volume_frontier_fd` : the boundary of `𝒟` is null;
* `isFundamentalDomain_fd` : `𝒟` is a fundamental domain for `PSL2Z`;
* `volume_fd_lt_top`, `integrableOn_fd_of_bounded` : `𝒟` has finite volume;
* `isFundamentalDomain_iUnion_smul` (abstract) and `isFundamentalDomain_iUnion_inv_smul_fd`
  (for `Γ ≤ SL(2, ℤ)`, using coset representatives of `pmSL Γ = Γ ∪ -Γ`, the preimage of
  `Subgroup.adjoinNegOne`) : the union of the translates of `𝒟` is a fundamental domain for `Γ`;
  `setIntegral_iUnion_inv_smul_fd_eq` : integrals of `Γ`-invariant functions over it do not depend
  on the representatives; `setIntegral_iUnion_inv_smul_fd_eq_index_smul` : index formula;
* `isFundamentalDomain_conj`, `setIntegral_smul_set` : `α • F` is a fundamental domain for the
  conjugate group `α Γ α⁻¹`, and integrals transform accordingly.
-/

set_option autoImplicit false

open MeasureTheory Set Matrix Matrix.SpecialLinearGroup UpperHalfPlane ModularGroup
open scoped MatrixGroups Modular Pointwise ENNReal NNReal

noncomputable section

namespace RP.FundDomain

/-! ### Measurability and invariance of the action of `PGL(2, ℝ)` and its subgroups -/

theorem measurableConstSMul_pgl : MeasurableConstSMul PGL(2, ℝ) ℍ where
  measurable_const_smul g := by
    induction g using ProjGenLinGroup.induction_on with
    | mk g =>
      have h : (fun x : ℍ => ProjGenLinGroup.mk g • x) = fun x => g • x :=
        funext fun x => pglMk_smul g x
      rw [h]
      exact measurable_const_smul g

theorem smulInvariantMeasure_pgl : SMulInvariantMeasure PGL(2, ℝ) ℍ volume where
  measure_preimage_smul g s hs := by
    induction g using ProjGenLinGroup.induction_on with
    | mk g =>
      have h : (fun x : ℍ => ProjGenLinGroup.mk g • x) = fun x => g • x :=
        funext fun x => pglMk_smul g x
      rw [h]
      exact SMulInvariantMeasure.measure_preimage_smul g hs

theorem smulInvariantMeasure_subgroup {P α : Type*} [Group P] [MulAction P α] [MeasurableSpace α]
    {μ : Measure α} [SMulInvariantMeasure P α μ] (H : Subgroup P) :
    SMulInvariantMeasure H α μ :=
  ⟨fun g _ hs => SMulInvariantMeasure.measure_preimage_smul (g : P) hs⟩

attribute [local instance] measurableConstSMul_pgl smulInvariantMeasure_pgl
  smulInvariantMeasure_subgroup

/-! ### The image of a subgroup of `GL(2, ℝ)` in `PGL(2, ℝ)` -/

/-- The image of a subgroup of `GL(2, ℝ)` in `PGL(2, ℝ)`: the group of Möbius maps of `ℍ` that it
induces. Scalars (in particular `-1`) act trivially. -/
def pglImage (Γ : Subgroup (GL (Fin 2) ℝ)) : Subgroup PGL(2, ℝ) :=
  Γ.map ProjGenLinGroup.mk

lemma mk_mem_pglImage {Γ : Subgroup (GL (Fin 2) ℝ)} {γ : GL (Fin 2) ℝ} (h : γ ∈ Γ) :
    ProjGenLinGroup.mk γ ∈ pglImage Γ :=
  Subgroup.mem_map_of_mem _ h

lemma mk_neg (g : GL (Fin 2) ℝ) : ProjGenLinGroup.mk (-g) = ProjGenLinGroup.mk g := by
  have h1 : ProjGenLinGroup.mk (-1 : GL (Fin 2) ℝ) = 1 :=
    ProjGenLinGroup.mk_eq_one.2 (Subgroup.mem_center_iff.2 fun h => by simp)
  rw [← neg_one_mul, map_mul, h1, one_mul]

/-- Adjoining `-1` does not change the image in `PGL(2, ℝ)`. -/
lemma pglImage_adjoinNegOne (Γ : Subgroup (GL (Fin 2) ℝ)) :
    pglImage Γ.adjoinNegOne = pglImage Γ := by
  ext g
  simp only [pglImage, Subgroup.mem_map, Subgroup.mem_adjoinNegOne_iff]
  constructor
  · rintro ⟨γ, hγ | hγ, rfl⟩
    · exact ⟨γ, hγ, rfl⟩
    · exact ⟨-γ, hγ, mk_neg γ⟩
  · rintro ⟨γ, hγ, rfl⟩
    exact ⟨γ, Or.inl hγ, rfl⟩

/-- The natural map `SL(2, ℤ) → PGL(2, ℝ)`. -/
def toPGLR : SL(2, ℤ) →* PGL(2, ℝ) :=
  ProjGenLinGroup.mk.comp (mapGL ℝ)

lemma toPGLR_apply (γ : SL(2, ℤ)) : toPGLR γ = ProjGenLinGroup.mk (mapGL ℝ γ) := rfl

lemma toPGLR_smul (γ : SL(2, ℤ)) (z : ℍ) : toPGLR γ • z = γ • z := by
  rw [toPGLR_apply, pglMk_smul]
  rfl

lemma toPGLR_smul_set (γ : SL(2, ℤ)) (S : Set ℍ) : toPGLR γ • S = γ • S := by
  simp only [← Set.image_smul, toPGLR_smul]

lemma mapGL_neg (γ : SL(2, ℤ)) : mapGL ℝ (-γ) = -mapGL ℝ γ := by
  ext i j
  simp [mapGL_coe_matrix]

lemma toPGLR_neg (γ : SL(2, ℤ)) : toPGLR (-γ) = toPGLR γ := by
  rw [toPGLR_apply, toPGLR_apply, mapGL_neg, mk_neg]

/-- The kernel of `SL(2, ℤ) → PGL(2, ℝ)` is `{±1}`. -/
lemma toPGLR_eq_one_iff (γ : SL(2, ℤ)) : toPGLR γ = 1 ↔ γ = 1 ∨ γ = -1 := by
  constructor
  · intro h
    let z : ℍ := UpperHalfPlane.mk (2 * Complex.I) (by simp)
    have hz : z ∈ 𝒟ᵒ := by
      refine ⟨?_, ?_⟩
      · simp [z, Complex.normSq_mul]
        norm_num
      · simp [z]
    have hγz : γ • z = z := by rw [← toPGLR_smul, h, one_smul]
    exact eq_one_or_neg_one_of_mem_fdo_mem_fd hz (by rw [hγz]; exact fdo_subset_fd hz)
  · rintro (rfl | rfl)
    · simp
    · rw [toPGLR_neg, map_one]

lemma toPGLR_eq_toPGLR_iff (x y : SL(2, ℤ)) : toPGLR x = toPGLR y ↔ x = y ∨ x = -y := by
  rw [← mul_inv_eq_one, ← map_inv, ← map_mul, toPGLR_eq_one_iff, mul_inv_eq_one,
    mul_inv_eq_iff_eq_mul, neg_one_mul]

lemma mem_pglImage_coe {Γ : Subgroup SL(2, ℤ)} {g : PGL(2, ℝ)} :
    g ∈ pglImage (Γ : Subgroup (GL (Fin 2) ℝ)) ↔ ∃ γ ∈ Γ, toPGLR γ = g := by
  simp only [pglImage, Subgroup.mem_map]
  constructor
  · rintro ⟨_, ⟨γ, hγ, rfl⟩, rfl⟩
    exact ⟨γ, hγ, rfl⟩
  · rintro ⟨γ, hγ, rfl⟩
    exact ⟨_, ⟨γ, hγ, rfl⟩, rfl⟩

lemma toPGLR_mem_pglImage {Γ : Subgroup SL(2, ℤ)} {γ : SL(2, ℤ)} (h : γ ∈ Γ) :
    toPGLR γ ∈ pglImage (Γ : Subgroup (GL (Fin 2) ℝ)) :=
  mem_pglImage_coe.2 ⟨γ, h, rfl⟩

/-- `PSL(2, ℤ)`, as the image of `SL(2, ℤ)` in `PGL(2, ℝ)`. -/
abbrev PSL2Z : Subgroup PGL(2, ℝ) := pglImage 𝒮ℒ

lemma mem_PSL2Z {g : PGL(2, ℝ)} : g ∈ PSL2Z ↔ ∃ γ : SL(2, ℤ), toPGLR γ = g := by
  simp only [PSL2Z, pglImage, Subgroup.mem_map, MonoidHom.mem_range]
  constructor
  · rintro ⟨_, ⟨γ, rfl⟩, rfl⟩
    exact ⟨γ, rfl⟩
  · rintro ⟨γ, rfl⟩
    exact ⟨_, ⟨γ, rfl⟩, rfl⟩

lemma toPGLR_mem_PSL2Z (γ : SL(2, ℤ)) : toPGLR γ ∈ PSL2Z := mem_PSL2Z.2 ⟨γ, rfl⟩

lemma pglImage_le_PSL2Z (Γ : Subgroup SL(2, ℤ)) :
    pglImage (Γ : Subgroup (GL (Fin 2) ℝ)) ≤ PSL2Z := by
  intro g hg
  obtain ⟨γ, -, rfl⟩ := mem_pglImage_coe.1 hg
  exact toPGLR_mem_PSL2Z γ

lemma countable_SL2Z : Countable SL(2, ℤ) := by
  have : Countable (Matrix (Fin 2) (Fin 2) ℤ) := inferInstanceAs (Countable (Fin 2 → Fin 2 → ℤ))
  exact inferInstanceAs (Countable {A : Matrix (Fin 2) (Fin 2) ℤ // A.det = 1})

lemma countable_pglImage_coe (Γ : Subgroup SL(2, ℤ)) :
    Countable (pglImage (Γ : Subgroup (GL (Fin 2) ℝ))) := by
  have := countable_SL2Z
  refine Function.Surjective.countable
    (f := fun γ : Γ => (⟨toPGLR γ, toPGLR_mem_pglImage γ.2⟩ :
      pglImage (Γ : Subgroup (GL (Fin 2) ℝ)))) ?_
  rintro ⟨g, hg⟩
  obtain ⟨γ, hγ, rfl⟩ := mem_pglImage_coe.1 hg
  exact ⟨⟨γ, hγ⟩, rfl⟩

lemma countable_PSL2Z : Countable PSL2Z := by
  have := countable_SL2Z
  refine Function.Surjective.countable
    (f := fun γ : SL(2, ℤ) => (⟨toPGLR γ, toPGLR_mem_PSL2Z γ⟩ : PSL2Z)) ?_
  rintro ⟨g, hg⟩
  obtain ⟨γ, rfl⟩ := mem_PSL2Z.1 hg
  exact ⟨γ, rfl⟩

/-! ### (a) The boundary of `𝒟` is null -/

/-- A subset of `ℍ` whose image in `ℂ` is Lebesgue-null is null for the hyperbolic measure. -/
lemma volume_eq_zero_of_coe_image {s : Set ℍ} (h : volume ((↑) '' s : Set ℂ) = 0) :
    volume s = 0 := by
  rw [volume_eq_lintegral]
  exact setLIntegral_measure_zero _ _ h

lemma volume_re_eq (c : ℝ) : volume {z : ℂ | z.re = c} = 0 := by
  have hs : {z : ℂ | z.re = c} =
      Complex.measurableEquivRealProd ⁻¹' ({c} ×ˢ (univ : Set ℝ)) := by
    ext z
    simp
  rw [hs, Complex.volume_preserving_equiv_real_prod.measure_preimage
    ((measurableSet_singleton c).prod MeasurableSet.univ).nullMeasurableSet,
    Measure.volume_eq_prod, Measure.prod_prod, Real.volume_singleton, zero_mul]

lemma fd_diff_fdo_subset :
    𝒟 \ 𝒟ᵒ ⊆ {z : ℍ | Complex.normSq (z : ℂ) = 1} ∪ {z : ℍ | z.re = 1 / 2} ∪
      {z : ℍ | z.re = -(1 / 2)} := by
  rintro z ⟨⟨h1, h2⟩, h3⟩
  have h3' : ¬ (1 < Complex.normSq (z : ℂ) ∧ |z.re| < 1 / 2) := h3
  rw [not_and_or, not_lt, not_lt] at h3'
  rcases h3' with h3' | h3'
  · exact Or.inl (Or.inl (le_antisymm h3' h1))
  · have h4 : |z.re| = 1 / 2 := le_antisymm h2 h3'
    rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1 / 2)).1 h4 with h | h
    · exact Or.inl (Or.inr h)
    · exact Or.inr h

/-- **(a)** The boundary `𝒟 \ 𝒟ᵒ` of the fundamental domain is null. -/
theorem volume_fd_diff_fdo : volume (𝒟 \ 𝒟ᵒ) = 0 := by
  refine measure_mono_null fd_diff_fdo_subset (measure_union_null (measure_union_null ?_ ?_) ?_)
  · apply volume_eq_zero_of_coe_image
    refine measure_mono_null ?_ (Measure.addHaar_sphere (μ := volume) (0 : ℂ) 1)
    rintro _ ⟨z, hz, rfl⟩
    have hz' : Complex.normSq (z : ℂ) = 1 := hz
    rw [Complex.normSq_eq_norm_sq] at hz'
    rw [mem_sphere_zero_iff_norm]
    nlinarith [norm_nonneg (z : ℂ)]
  · apply volume_eq_zero_of_coe_image
    refine measure_mono_null ?_ (volume_re_eq (1 / 2))
    rintro _ ⟨z, hz, rfl⟩
    exact hz
  · apply volume_eq_zero_of_coe_image
    refine measure_mono_null ?_ (volume_re_eq (-(1 / 2)))
    rintro _ ⟨z, hz, rfl⟩
    exact hz

theorem volume_frontier_fd : volume (frontier 𝒟) = 0 := by
  rw [isClosed_fd.frontier_eq, ← fdo_eq_interior_fd]
  exact volume_fd_diff_fdo

theorem fdo_ae_eq_fd : (𝒟ᵒ : Set ℍ) =ᵐ[volume] 𝒟 := by
  rw [ae_eq_set, sdiff_eq_empty.2 fdo_subset_fd]
  exact ⟨measure_empty, volume_fd_diff_fdo⟩

/-! ### (b) `𝒟` is a fundamental domain for `PSL(2, ℤ)` -/

/-- **(b)** The closed fundamental domain `𝒟` is an (a.e.) fundamental domain for the action of
`PSL(2, ℤ) = SL(2, ℤ)/{±1}` (as a subgroup of `PGL(2, ℝ)`) on `ℍ` with the hyperbolic measure. -/
theorem isFundamentalDomain_fd : IsFundamentalDomain PSL2Z 𝒟 volume := by
  refine IsFundamentalDomain.mk'' isClosed_fd.measurableSet.nullMeasurableSet ?_ ?_ ?_
  · refine Filter.Eventually.of_forall fun z => ?_
    obtain ⟨γ, hγ⟩ := exists_smul_mem_fd z
    refine ⟨⟨toPGLR γ, toPGLR_mem_PSL2Z γ⟩, ?_⟩
    show toPGLR γ • z ∈ 𝒟
    rwa [toPGLR_smul]
  · intro g hg
    obtain ⟨γ, hγ⟩ := mem_PSL2Z.1 g.2
    show volume ((g • 𝒟) ∩ 𝒟) = 0
    refine measure_mono_null ?_ volume_fd_diff_fdo
    rintro z ⟨hz1, hz⟩
    obtain ⟨w, hw, rfl⟩ := Set.mem_smul_set.1 hz1
    refine ⟨hz, fun hzo => hg ?_⟩
    have hgw : g • w = γ • w := by
      show (g : PGL(2, ℝ)) • w = γ • w
      rw [← hγ, toPGLR_smul]
    rw [hgw] at hzo
    have hmem : γ⁻¹ • γ • w ∈ 𝒟 := by rwa [inv_smul_smul]
    have h1 : toPGLR γ⁻¹ = 1 := (toPGLR_eq_one_iff _).2 (eq_one_or_neg_one_of_mem_fdo_mem_fd hzo hmem)
    rw [map_inv, inv_eq_one, hγ] at h1
    exact OneMemClass.coe_eq_one.1 h1
  · intro g
    exact (measurePreserving_smul g volume).quasiMeasurePreserving

/-! ### (c) `𝒟` has finite volume -/

lemma fd_subset_strip : 𝒟 ⊆ {z : ℍ | |z.re| ≤ 1 / 2 ∧ 1 / 2 ≤ z.im} := by
  intro z hz
  refine ⟨hz.2, ?_⟩
  have h := three_le_four_mul_im_sq_of_mem_fd hz
  nlinarith [z.im_pos]

lemma lintegral_Ici_inv_sq_lt_top :
    ∫⁻ y in Ici (1 / 2 : ℝ), (((1 / ‖y‖₊) ^ 2 : ℝ≥0) : ℝ≥0∞) < ∞ := by
  have hint : IntegrableOn (fun y : ℝ => (1 / y) ^ 2) (Ici (1 / 2 : ℝ)) := by
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    refine (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1)
      (by norm_num : (0 : ℝ) < 1 / 2)).congr_fun (fun y hy => ?_) measurableSet_Ioi
    have hy' : (0 : ℝ) < y := lt_trans (by norm_num) hy
    dsimp only
    rw [Real.rpow_neg hy'.le, Real.rpow_two, one_div, inv_pow]
  have h := hint.2
  have hfun : (fun y : ℝ => (((1 / ‖y‖₊) ^ 2 : ℝ≥0) : ℝ≥0∞)) = fun y => ‖(1 / y) ^ 2‖ₑ := by
    funext y
    rw [enorm_eq_nnnorm, nnnorm_pow, nnnorm_div, nnnorm_one]
  rw [hfun]
  exact h

lemma volume_strip_lt_top : volume {z : ℍ | |z.re| ≤ 1 / 2 ∧ 1 / 2 ≤ z.im} < ∞ := by
  rw [volume_eq_lintegral]
  set T : Set ℂ := {w | |w.re| ≤ 1 / 2 ∧ 1 / 2 ≤ w.im} with hT
  have hsub : (UpperHalfPlane.coe '' {z : ℍ | |z.re| ≤ 1 / 2 ∧ 1 / 2 ≤ z.im}) ⊆ T := by
    rintro _ ⟨z, hz, rfl⟩
    exact hz
  refine lt_of_le_of_lt (lintegral_mono_set hsub) ?_
  have hT' : T = Complex.measurableEquivRealProd ⁻¹' (Icc (-(1 / 2) : ℝ) (1 / 2) ×ˢ Ici (1 / 2)) := by
    ext w
    simp [hT, abs_le]
  have key := Complex.volume_preserving_equiv_real_prod.setLIntegral_comp_preimage_emb
    Complex.measurableEquivRealProd.measurableEmbedding
    (fun p : ℝ × ℝ => (((1 / ‖p.2‖₊) ^ 2 : ℝ≥0) : ℝ≥0∞))
    (Icc (-(1 / 2) : ℝ) (1 / 2) ×ˢ Ici (1 / 2))
  rw [hT']
  simp only [Complex.measurableEquivRealProd_apply] at key
  rw [key, Measure.volume_eq_prod, setLIntegral_prod _ (by fun_prop)]
  simp only [setLIntegral_const, Real.volume_Icc]
  exact ENNReal.mul_lt_top lintegral_Ici_inv_sq_lt_top ENNReal.ofReal_lt_top

/-- **(c)** The fundamental domain has finite hyperbolic volume. -/
theorem volume_fd_lt_top : volume 𝒟 < ∞ :=
  lt_of_le_of_lt (measure_mono fd_subset_strip) volume_strip_lt_top

/-- **(c)** Every bounded (a.e.-strongly) measurable function is integrable on `𝒟`. -/
theorem integrableOn_fd_of_bounded {E : Type*} [NormedAddCommGroup E] {f : ℍ → E}
    (hf : AEStronglyMeasurable f (volume.restrict 𝒟)) {C : ℝ} (hC : ∀ z ∈ 𝒟, ‖f z‖ ≤ C) :
    IntegrableOn f 𝒟 volume :=
  ⟨hf, .restrict_of_bounded (C := C) volume_fd_lt_top
    (ae_restrict_of_forall_mem isClosed_fd.measurableSet hC)⟩

theorem integrableOn_fd_of_continuous {E : Type*} [NormedAddCommGroup E] {f : ℍ → E}
    (hf : Continuous f) {C : ℝ} (hC : ∀ z ∈ 𝒟, ‖f z‖ ≤ C) : IntegrableOn f 𝒟 volume :=
  integrableOn_fd_of_bounded hf.aestronglyMeasurable hC


/-! ### Change of variables under the action -/

/-- Integrals over a translate `g • F` (for any group acting measurably and preserving `volume`,
e.g. `GL(2, ℝ)`, `PGL(2, ℝ)` or a subgroup of it). -/
theorem setIntegral_smul_set {G E : Type*} [Group G] [MulAction G ℍ] [MeasurableConstSMul G ℍ]
    [SMulInvariantMeasure G ℍ volume] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : G) (F : Set ℍ) (f : ℍ → E) :
    ∫ z in g • F, f z = ∫ z in F, f (g • z) := by
  rw [← Set.image_smul]
  exact (measurePreserving_smul g volume).setIntegral_image_emb (measurableEmbedding_const_smul g) f F

/-! ### (d) Fundamental domains of subgroups from coset representatives -/

section Cosets

variable {P α : Type*} [Group P] [MulAction P α] [MeasurableSpace α] [MeasurableConstSMul P α]
  {μ : Measure α} [SMulInvariantMeasure P α μ]

/-- `q` is a system of representatives of the right cosets `H * q i` of `H` in `G`. -/
def IsRightCosetReps {ι : Type*} (G H : Subgroup P) (q : ι → P) : Prop :=
  (∀ i, q i ∈ G) ∧ ∀ g ∈ G, ∃! i, ∃ h ∈ H, g = h * q i

/-- **(d), abstract form.** If `s` is a fundamental domain for `G`, `H ≤ G`, and `q` runs over
representatives of the right cosets `H * q i` of `H` in `G`, then `⋃ i, q i • s` is a fundamental
domain for `H`. -/
theorem isFundamentalDomain_iUnion_smul {ι : Type*} [Countable ι] {G H : Subgroup P} (hHG : H ≤ G)
    {s : Set α} (hs : IsFundamentalDomain G s μ) {q : ι → P} (hq : IsRightCosetReps G H q) :
    IsFundamentalDomain H (⋃ i, q i • s) μ where
  nullMeasurableSet := .iUnion fun i => hs.nullMeasurableSet_smul ⟨q i, hq.1 i⟩
  ae_covers := by
    filter_upwards [hs.ae_covers] with x ⟨g, hg⟩
    obtain ⟨i, ⟨h, hh, hgi⟩, -⟩ := hq.2 (g : P)⁻¹ (G.inv_mem g.2)
    refine ⟨⟨h⁻¹, H.inv_mem hh⟩, mem_iUnion.2 ⟨i, (g : P) • x, hg, ?_⟩⟩
    have hqi : q i = h⁻¹ * (g : P)⁻¹ := by rw [hgi]; group
    show q i • (g : P) • x = h⁻¹ • x
    rw [hqi, mul_smul, inv_smul_smul]
  aedisjoint := by
    intro a b hab
    show AEDisjoint μ ((a : P) • ⋃ i, q i • s) ((b : P) • ⋃ i, q i • s)
    simp only [smul_set_iUnion, smul_smul]
    rw [AEDisjoint.iUnion_left_iff]
    intro i
    rw [AEDisjoint.iUnion_right_iff]
    intro j
    have hai : (a : P) * q i ∈ G := G.mul_mem (hHG a.2) (hq.1 i)
    have hbj : (b : P) * q j ∈ G := G.mul_mem (hHG b.2) (hq.1 j)
    have hne : (⟨(a : P) * q i, hai⟩ : G) ≠ ⟨(b : P) * q j, hbj⟩ := by
      intro h
      have h' : (a : P) * q i = b * q j := congrArg Subtype.val h
      obtain ⟨k, -, huniq⟩ := hq.2 _ hai
      have hi := huniq i ⟨a, a.2, rfl⟩
      have hj := huniq j ⟨b, b.2, h'⟩
      have hij : i = j := hi.trans hj.symm
      subst hij
      exact hab (Subtype.ext (mul_right_cancel h'))
    exact hs.aedisjoint hne

end Cosets

/-- `Γ ∪ -Γ` as a subgroup of `SL(2, ℤ)`: the preimage of `Subgroup.adjoinNegOne Γ`. -/
def pmSL (Γ : Subgroup SL(2, ℤ)) : Subgroup SL(2, ℤ) :=
  (Γ : Subgroup (GL (Fin 2) ℝ)).adjoinNegOne.comap (mapGL ℝ)

lemma mem_pmSL {Γ : Subgroup SL(2, ℤ)} {g : SL(2, ℤ)} : g ∈ pmSL Γ ↔ g ∈ Γ ∨ -g ∈ Γ := by
  have key : ∀ x : SL(2, ℤ), mapGL ℝ x ∈ (Γ : Subgroup (GL (Fin 2) ℝ)) ↔ x ∈ Γ := fun x =>
    ⟨fun ⟨y, hy, hyx⟩ => by rw [← mapGL_injective hyx]; exact hy, fun hx => ⟨x, hx, rfl⟩⟩
  rw [pmSL, Subgroup.mem_comap, Subgroup.mem_adjoinNegOne_iff, ← mapGL_neg, key, key]

lemma le_pmSL (Γ : Subgroup SL(2, ℤ)) : Γ ≤ pmSL Γ := fun _ hg => mem_pmSL.2 (Or.inl hg)

lemma isRightCosetReps_toPGLR (Γ : Subgroup SL(2, ℤ)) (q : SL(2, ℤ) ⧸ pmSL Γ → SL(2, ℤ))
    (hq : ∀ c, (q c : SL(2, ℤ) ⧸ pmSL Γ) = c) :
    IsRightCosetReps PSL2Z (pglImage (Γ : Subgroup (GL (Fin 2) ℝ))) (fun c => toPGLR (q c)⁻¹) := by
  refine ⟨fun c => toPGLR_mem_PSL2Z _, fun g hg => ?_⟩
  obtain ⟨γ, rfl⟩ := mem_PSL2Z.1 hg
  have hc : ∀ c : SL(2, ℤ) ⧸ pmSL Γ,
      (∃ h ∈ pglImage (Γ : Subgroup (GL (Fin 2) ℝ)), toPGLR γ = h * toPGLR (q c)⁻¹) ↔
        c = (QuotientGroup.mk γ⁻¹ : SL(2, ℤ) ⧸ pmSL Γ) := by
    intro c
    constructor
    · rintro ⟨h, hh, hγ⟩
      obtain ⟨δ, hδ, rfl⟩ := mem_pglImage_coe.1 hh
      rw [← map_mul, toPGLR_eq_toPGLR_iff] at hγ
      have h2 : γ * q c = δ ∨ γ * q c = -δ := by
        rcases hγ with h | h
        · left
          rw [h, inv_mul_cancel_right]
        · right
          rw [h, neg_mul, inv_mul_cancel_right]
      rw [← hq c, QuotientGroup.eq, ← _root_.mul_inv_rev]
      refine (pmSL Γ).inv_mem ?_
      rw [mem_pmSL]
      rcases h2 with h | h
      · rw [h]
        exact Or.inl hδ
      · rw [h, neg_neg]
        exact Or.inr hδ
    · rintro rfl
      have h1 := hq (QuotientGroup.mk γ⁻¹ : SL(2, ℤ) ⧸ pmSL Γ)
      rw [QuotientGroup.eq] at h1
      have h2 : γ * q (QuotientGroup.mk γ⁻¹) ∈ pmSL Γ := by
        have := (pmSL Γ).inv_mem h1
        simpa [_root_.mul_inv_rev] using this
      rcases mem_pmSL.1 h2 with h | h
      · refine ⟨toPGLR (γ * q (QuotientGroup.mk γ⁻¹)), toPGLR_mem_pglImage h, ?_⟩
        rw [← map_mul, mul_inv_cancel_right]
      · refine ⟨toPGLR (-(γ * q (QuotientGroup.mk γ⁻¹))), toPGLR_mem_pglImage h, ?_⟩
        rw [toPGLR_neg, ← map_mul, mul_inv_cancel_right]
  exact ⟨(QuotientGroup.mk γ⁻¹ : SL(2, ℤ) ⧸ pmSL Γ), (hc _).2 rfl, fun c hc' => (hc c).1 hc'⟩

lemma countable_quotient_pmSL (Γ : Subgroup SL(2, ℤ)) : Countable (SL(2, ℤ) ⧸ pmSL Γ) := by
  have := countable_SL2Z
  exact QuotientGroup.mk_surjective.countable

/-- **(d)** For any subgroup `Γ ≤ SL(2, ℤ)` and any choice `q` of representatives of the cosets
`g (±Γ)` (Mathlib's `SL(2, ℤ) ⧸ pmSL Γ`), the union `⋃ c, (q c)⁻¹ • 𝒟` is a fundamental domain for
`Γ` (acting through its image in `PGL(2, ℝ)`). The `(q c)⁻¹` run over representatives of the
right cosets `(±Γ) (q c)⁻¹`. -/
theorem isFundamentalDomain_iUnion_inv_smul_fd (Γ : Subgroup SL(2, ℤ))
    (q : SL(2, ℤ) ⧸ pmSL Γ → SL(2, ℤ)) (hq : ∀ c, (q c : SL(2, ℤ) ⧸ pmSL Γ) = c) :
    IsFundamentalDomain (pglImage (Γ : Subgroup (GL (Fin 2) ℝ))) (⋃ c, (q c)⁻¹ • 𝒟) volume := by
  have := countable_quotient_pmSL Γ
  have h := isFundamentalDomain_iUnion_smul (pglImage_le_PSL2Z Γ) isFundamentalDomain_fd
    (isRightCosetReps_toPGLR Γ q hq)
  simpa only [toPGLR_smul_set] using h

/-- The canonical choice of representatives (`Quotient.out`). -/
theorem isFundamentalDomain_iUnion_out_inv_smul_fd (Γ : Subgroup SL(2, ℤ)) :
    IsFundamentalDomain (pglImage (Γ : Subgroup (GL (Fin 2) ℝ)))
      (⋃ c : SL(2, ℤ) ⧸ pmSL Γ, c.out⁻¹ • 𝒟) volume :=
  isFundamentalDomain_iUnion_inv_smul_fd Γ _ QuotientGroup.out_eq'

/-- The translates `(q c)⁻¹ • 𝒟` are pairwise a.e. disjoint. -/
lemma aedisjoint_inv_smul_fd (Γ : Subgroup SL(2, ℤ)) (q : SL(2, ℤ) ⧸ pmSL Γ → SL(2, ℤ))
    (hq : ∀ c, (q c : SL(2, ℤ) ⧸ pmSL Γ) = c) :
    Pairwise (Function.onFun (AEDisjoint volume) fun c => (q c)⁻¹ • 𝒟) := by
  intro c c' hcc'
  have hne : (⟨toPGLR (q c)⁻¹, toPGLR_mem_PSL2Z _⟩ : PSL2Z) ≠
      ⟨toPGLR (q c')⁻¹, toPGLR_mem_PSL2Z _⟩ := by
    intro h
    have h' : toPGLR (q c)⁻¹ = toPGLR (q c')⁻¹ := congrArg Subtype.val h
    apply hcc'
    rw [← hq c, ← hq c', QuotientGroup.eq, mem_pmSL]
    rcases (toPGLR_eq_toPGLR_iff _ _).1 h' with h'' | h''
    · rw [h'', inv_mul_cancel]
      exact Or.inl Γ.one_mem
    · rw [h'', neg_mul, inv_mul_cancel, neg_neg]
      exact Or.inr Γ.one_mem
  have h := isFundamentalDomain_fd.aedisjoint hne
  change AEDisjoint volume (toPGLR (q c)⁻¹ • 𝒟) (toPGLR (q c')⁻¹ • 𝒟) at h
  rw [toPGLR_smul_set, toPGLR_smul_set] at h
  exact h

/-- For `Γ` of finite index the fundamental domain `⋃ c, (q c)⁻¹ • 𝒟` has finite volume. -/
theorem volume_iUnion_inv_smul_fd_lt_top (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex]
    (q : SL(2, ℤ) ⧸ pmSL Γ → SL(2, ℤ)) : volume (⋃ c, (q c)⁻¹ • 𝒟) < ∞ := by
  have : (pmSL Γ).FiniteIndex := Subgroup.finiteIndex_of_le (le_pmSL Γ)
  have : Fintype (SL(2, ℤ) ⧸ pmSL Γ) := Fintype.ofFinite _
  refine lt_of_le_of_lt (measure_iUnion_le _) ?_
  rw [tsum_fintype]
  refine ENNReal.sum_lt_top.2 fun c _ => ?_
  rw [← toPGLR_smul_set, measure_smul]
  exact volume_fd_lt_top

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Integrals of `Γ`-invariant functions over two fundamental domains of `Γ` agree. -/
theorem setIntegral_eq_of_isFundamentalDomain (Γ : Subgroup SL(2, ℤ)) {F F' : Set ℍ}
    (hF : IsFundamentalDomain (pglImage (Γ : Subgroup (GL (Fin 2) ℝ))) F volume)
    (hF' : IsFundamentalDomain (pglImage (Γ : Subgroup (GL (Fin 2) ℝ))) F' volume)
    {f : ℍ → E} (hf : ∀ γ ∈ Γ, ∀ z : ℍ, f (γ • z) = f z) :
    ∫ z in F, f z = ∫ z in F', f z := by
  have := countable_pglImage_coe Γ
  refine hF.setIntegral_eq hF' fun g z => ?_
  obtain ⟨γ, hγ, hg⟩ := mem_pglImage_coe.1 g.2
  show f ((g : PGL(2, ℝ)) • z) = f z
  rw [← hg, toPGLR_smul, hf γ hγ z]

/-- **(d)** The integral of a `Γ`-invariant function over `⋃ c, (q c)⁻¹ • 𝒟` does not depend on the
choice of representatives. -/
theorem setIntegral_iUnion_inv_smul_fd_eq (Γ : Subgroup SL(2, ℤ))
    (q q' : SL(2, ℤ) ⧸ pmSL Γ → SL(2, ℤ)) (hq : ∀ c, (q c : SL(2, ℤ) ⧸ pmSL Γ) = c)
    (hq' : ∀ c, (q' c : SL(2, ℤ) ⧸ pmSL Γ) = c)
    {f : ℍ → E} (hf : ∀ γ ∈ Γ, ∀ z : ℍ, f (γ • z) = f z) :
    ∫ z in ⋃ c, (q c)⁻¹ • 𝒟, f z = ∫ z in ⋃ c, (q' c)⁻¹ • 𝒟, f z :=
  setIntegral_eq_of_isFundamentalDomain Γ (isFundamentalDomain_iUnion_inv_smul_fd Γ q hq)
    (isFundamentalDomain_iUnion_inv_smul_fd Γ q' hq') hf

/-- The integral over `⋃ c, (q c)⁻¹ • 𝒟` as a sum of integrals over `𝒟`. -/
theorem setIntegral_iUnion_inv_smul_fd (Γ : Subgroup SL(2, ℤ))
    (q : SL(2, ℤ) ⧸ pmSL Γ → SL(2, ℤ)) (hq : ∀ c, (q c : SL(2, ℤ) ⧸ pmSL Γ) = c)
    {f : ℍ → E} (hfi : IntegrableOn f (⋃ c, (q c)⁻¹ • 𝒟)) :
    ∫ z in ⋃ c, (q c)⁻¹ • 𝒟, f z = ∑' c, ∫ z in 𝒟, f ((q c)⁻¹ • z) := by
  have := countable_quotient_pmSL Γ
  rw [integral_iUnion_ae (fun c => ?_) (aedisjoint_inv_smul_fd Γ q hq) hfi]
  · congr 1
    funext c
    rw [← toPGLR_smul_set, setIntegral_smul_set]
    simp only [toPGLR_smul]
  · rw [← toPGLR_smul_set]
    exact (isClosed_fd.measurableSet.const_smul _).nullMeasurableSet

/-- **Index formula.** For `Γ` of finite index and `f` invariant under all of `SL(2, ℤ)` and
integrable on `𝒟`, the integral over the fundamental domain of `Γ` is `[SL(2, ℤ) : ±Γ]` times the
integral over `𝒟`. -/
theorem setIntegral_iUnion_inv_smul_fd_eq_index_smul (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex]
    (q : SL(2, ℤ) ⧸ pmSL Γ → SL(2, ℤ)) (hq : ∀ c, (q c : SL(2, ℤ) ⧸ pmSL Γ) = c)
    {f : ℍ → E} (hf : ∀ (γ : SL(2, ℤ)) (z : ℍ), f (γ • z) = f z) (hfi : IntegrableOn f 𝒟) :
    ∫ z in ⋃ c, (q c)⁻¹ • 𝒟, f z = (pmSL Γ).index • ∫ z in 𝒟, f z := by
  have : (pmSL Γ).FiniteIndex := Subgroup.finiteIndex_of_le (le_pmSL Γ)
  have : Fintype (SL(2, ℤ) ⧸ pmSL Γ) := Fintype.ofFinite _
  have hfi' : IntegrableOn f (⋃ c, (q c)⁻¹ • 𝒟) := by
    rw [integrableOn_finite_iUnion]
    intro c
    rw [← toPGLR_smul_set, ← Set.image_smul,
      (measurePreserving_smul (toPGLR (q c)⁻¹) volume).integrableOn_image
        (measurableEmbedding_const_smul _)]
    refine hfi.congr_fun (fun z _ => ?_) isClosed_fd.measurableSet
    simp only [Function.comp, toPGLR_smul, hf]
  rw [setIntegral_iUnion_inv_smul_fd Γ q hq hfi', tsum_fintype]
  simp only [hf, Finset.sum_const, Finset.card_univ]
  rw [Subgroup.index, Nat.card_eq_fintype_card]

/-! ### (e) Conjugation -/

lemma conj_mem_pglImage {Γ : Subgroup (GL (Fin 2) ℝ)} (α : GL (Fin 2) ℝ) {h : PGL(2, ℝ)}
    (hh : h ∈ pglImage (ConjAct.toConjAct α • Γ)) :
    ProjGenLinGroup.mk α⁻¹ * h * ProjGenLinGroup.mk α ∈ pglImage Γ := by
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hh
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ConjAct.smul_def] at hy
  simp only [ConjAct.ofConjAct_inv, ConjAct.ofConjAct_toConjAct, inv_inv] at hy
  rw [← map_mul, ← map_mul]
  exact mk_mem_pglImage hy

lemma conj_mem_pglImage' {Γ : Subgroup (GL (Fin 2) ℝ)} (α : GL (Fin 2) ℝ) {g : PGL(2, ℝ)}
    (hg : g ∈ pglImage Γ) :
    ProjGenLinGroup.mk α * g * ProjGenLinGroup.mk α⁻¹ ∈ pglImage (ConjAct.toConjAct α • Γ) := by
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hg
  rw [← map_mul, ← map_mul]
  refine mk_mem_pglImage ?_
  rw [← ConjAct.toConjAct_smul]
  exact Subgroup.smul_mem_pointwise_smul _ _ _ hy

/-- Conjugation by `α⁻¹` as an equivalence between the images in `PGL(2, ℝ)` of `α Γ α⁻¹` and
of `Γ`. -/
def conjEquiv (Γ : Subgroup (GL (Fin 2) ℝ)) (α : GL (Fin 2) ℝ) :
    pglImage (ConjAct.toConjAct α • Γ) ≃ pglImage Γ where
  toFun h := ⟨_, conj_mem_pglImage α h.2⟩
  invFun g := ⟨_, conj_mem_pglImage' α g.2⟩
  left_inv h := Subtype.ext <| by
    show ProjGenLinGroup.mk α * (ProjGenLinGroup.mk α⁻¹ * (h : PGL(2, ℝ)) *
      ProjGenLinGroup.mk α) * ProjGenLinGroup.mk α⁻¹ = h
    simp only [map_inv]
    group
  right_inv g := Subtype.ext <| by
    show ProjGenLinGroup.mk α⁻¹ * (ProjGenLinGroup.mk α * (g : PGL(2, ℝ)) *
      ProjGenLinGroup.mk α⁻¹) * ProjGenLinGroup.mk α = g
    simp only [map_inv]
    group

/-- **(e)** If `F` is a fundamental domain for `Γ ≤ GL(2, ℝ)` (acting through `PGL(2, ℝ)`), then
for every `α ∈ GL(2, ℝ)` the translate `α • F` is a fundamental domain for `α Γ α⁻¹`. -/
theorem isFundamentalDomain_conj {Γ : Subgroup (GL (Fin 2) ℝ)} {F : Set ℍ}
    (hF : IsFundamentalDomain (pglImage Γ) F volume) (α : GL (Fin 2) ℝ) :
    IsFundamentalDomain (pglImage (ConjAct.toConjAct α • Γ)) (α • F) volume := by
  have h := hF.image_of_equiv (MulAction.toPerm α)
    (measurePreserving_smul α⁻¹ volume).quasiMeasurePreserving (conjEquiv Γ α) (fun g x => by
      show α • ((ProjGenLinGroup.mk α⁻¹ * (g : PGL(2, ℝ)) * ProjGenLinGroup.mk α) • x) =
        (g : PGL(2, ℝ)) • α • x
      rw [mul_smul, mul_smul, pglMk_smul, pglMk_smul, smul_inv_smul])
  exact h

/-- **(e)** The action of `α ∈ GL(2, ℝ)` preserves volume and transforms integrals. -/
theorem volume_smul_set (α : GL (Fin 2) ℝ) (F : Set ℍ) : volume (α • F) = volume F :=
  measure_smul volume α F

theorem setIntegral_gl_smul_set (α : GL (Fin 2) ℝ) (F : Set ℍ) (f : ℍ → E) :
    ∫ z in α • F, f z = ∫ z in F, f (α • z) :=
  setIntegral_smul_set α F f

end RP.FundDomain


