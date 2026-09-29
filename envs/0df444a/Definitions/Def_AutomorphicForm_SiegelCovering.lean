-- Prove2me | Definitions.Def_AutomorphicForm_SiegelCovering
-- name    : AutomorphicForm_SiegelCovering
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/e6920b5b-5d51-5f3f-a5bb-1b9acbf042b1
-- title:
--   Siegel reduction over the reals; adelic covering predicates
-- statement:
--   Two predicates are introduced for a number field $F$. `FiniteIntegralCovering F` says that every $g\in\mathrm{GL}_2$ of the finite adele ring of $F$ can be moved into the finite integral subgroup `finiteIntegralGL2` by a global element: there is $\gamma\in\mathrm{GL}_2(F)$ with the finite component of $\gamma$ times $g$ lying in that subgroup. `CoversModCentre F D`, for a subset $D$ of the adelic group `AdelicGL2`, says that every $g$ admits $\gamma\in\mathrm{GL}_2(F)$ and an adelic unit $z$ with $\gamma\, g\, \mathrm{diag}(z,z)\in D$; thus $D$ meets every orbit under left translation by global points and right translation by the centre. Elementary consequences are recorded: monotonicity in $D$, and that the empty set does not cover.
--
--   The remaining results compute the window functionals of `AutomorphicForm_WindowedSiegelSet` on $\mathrm{GL}_2(\mathbb{R})$: $\mathrm{localHeight}(h)=\operatorname{Im}(h\cdot i)$ and $\mathrm{xWindowSq}(h)=\operatorname{Re}(h\cdot i)^2$, together with the entrywise formulas for $\mathrm{num}$, $\mathrm{denom}$, $\mathrm{rowNormSq}$ and $\mathrm{topNormSq}$ at $i$. From the standard fundamental domain for $\mathrm{SL}_2(\mathbb{Z})$ one obtains, for each $h\in\mathrm{GL}_2(\mathbb{R})$, some $\gamma\in\mathrm{SL}_2(\mathbb{Z})$ with $\mathrm{localHeight}(\gamma h)\ge\sqrt3/2$ and $\mathrm{xWindowSq}(\gamma h)\le(1/2)^2$; the constant $\sqrt3/2$ cannot be improved to $1$, since for the element carrying $i$ to $\rho$ every $\mathrm{SL}_2(\mathbb{Z})$-translate has height at most $\sqrt3/2$ (via $1\le c^2-cd+d^2$ for $(c,d)\neq(0,0)$). These statements are transported, through the isometric embedding of the completion at a real place into $\mathbb{R}$, to $\mathrm{GL}_2(F_w)$ for $w$ real, and then to $\mathbb{Q}$. The concluding theorem: if `FiniteIntegralCovering ℚ` holds and $c\le\sqrt3/2$, $1/2\le u$, $0<d_2$, $d_1\le d_2$, then `centreCutSiegelSet ℚ c u d₁ d₂` satisfies `CoversModCentre ℚ`, the central scalar being chosen at the real place so as to normalise the archimedean determinant norm to $d_2$.
--
--   **Relation to Mathlib.** The window functionals, the covering predicates and the centre-cut Siegel set are the project's own; the input over $\mathbb{R}$ is Mathlib's fundamental domain for the modular group (`ModularGroup.exists_smul_mem_fd`, `ModularGroup.three_le_four_mul_im_sq_of_mem_fd`), and the real-place transfer uses Mathlib's isometric embedding of the completion at a real infinite place.
--
--   **Where it is used.** This is part of the reduction theory for adelic $\mathrm{GL}_2$ underlying the treatment of automorphic forms: the covering property lets integrals and finiteness statements over $\mathrm{GL}_2(\mathbb{A})$ modulo global points and the centre be reduced to the centre-cut Siegel set, whose compactness and measurability are established alongside it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AutomorphicForm_SiegelCovering.lean

import Definitions.Def_AutomorphicForm_CentreCutSiegelSet
import Definitions.Def_AutomorphicForm_SiegelReduction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open Matrix NumberField UpperHalfPlane
open scoped MatrixGroups Modular

noncomputable section

namespace AutomorphicForm

namespace SiegelCovering

open WindowedSiegel SiegelCoordinates

section Real

theorem re_denom_I (h : GL (Fin 2) ℝ) : (denom h UpperHalfPlane.I).re = h 1 1 := by
  simp [denom, UpperHalfPlane.coe_I]

theorem im_denom_I (h : GL (Fin 2) ℝ) : (denom h UpperHalfPlane.I).im = h 1 0 := by
  simp [denom, UpperHalfPlane.coe_I]

theorem re_num_I (h : GL (Fin 2) ℝ) : (num h UpperHalfPlane.I).re = h 0 1 := by
  simp [num, UpperHalfPlane.coe_I]

theorem im_num_I (h : GL (Fin 2) ℝ) : (num h UpperHalfPlane.I).im = h 0 0 := by
  simp [num, UpperHalfPlane.coe_I]

theorem normSq_denom_I (h : GL (Fin 2) ℝ) :
    Complex.normSq (denom h UpperHalfPlane.I) = h 1 0 ^ 2 + h 1 1 ^ 2 := by
  rw [Complex.normSq_apply, re_denom_I, im_denom_I]
  ring

theorem rowNormSq_real (h : GL (Fin 2) ℝ) :
    rowNormSq (h : Matrix (Fin 2) (Fin 2) ℝ) = h 1 0 ^ 2 + h 1 1 ^ 2 := by
  simp only [rowNormSq, Real.norm_eq_abs, sq_abs]

theorem topNormSq_real (h : GL (Fin 2) ℝ) :
    topNormSq (h : Matrix (Fin 2) (Fin 2) ℝ) = h 0 0 ^ 2 + h 0 1 ^ 2 := by
  simp only [topNormSq, Real.norm_eq_abs, sq_abs]

theorem localHeight_eq_im_smul_I (h : GL (Fin 2) ℝ) :
    localHeight h = (h • UpperHalfPlane.I).im := by
  rw [im_smul_eq_div_normSq, UpperHalfPlane.I_im, mul_one, normSq_denom_I, ← rowNormSq_real]
  unfold localHeight
  rw [Matrix.GeneralLinearGroup.val_det_apply, Real.norm_eq_abs]

theorem re_smul_I (h : GL (Fin 2) ℝ) :
    (h • UpperHalfPlane.I).re = (h 0 0 * h 1 0 + h 0 1 * h 1 1) / (h 1 0 ^ 2 + h 1 1 ^ 2) := by
  rw [re_smul, Complex.div_re, normSq_denom_I, re_num_I, im_num_I, re_denom_I, im_denom_I,
    ← add_div]
  ring

theorem xWindowSq_eq_re_smul_I_sq (h : GL (Fin 2) ℝ) :
    xWindowSq h = (h • UpperHalfPlane.I).re ^ 2 := by
  have hpos : 0 < h 1 0 ^ 2 + h 1 1 ^ 2 := rowNormSq_real h ▸ rowNormSq_pos h
  have hdet : ‖(h : Matrix (Fin 2) (Fin 2) ℝ).det‖ ^ 2 = (h 0 0 * h 1 1 - h 0 1 * h 1 0) ^ 2 := by
    rw [Real.norm_eq_abs, sq_abs, Matrix.det_fin_two]
  rw [re_smul_I]
  unfold xWindowSq localHeight
  rw [div_pow, hdet, rowNormSq_real, topNormSq_real, div_pow,
    div_sub_div _ _ hpos.ne' (pow_ne_zero 2 hpos.ne'),
    div_eq_div_iff (mul_ne_zero hpos.ne' (pow_ne_zero 2 hpos.ne')) (pow_ne_zero 2 hpos.ne')]
  ring

theorem exists_mapGL_mul_reduced (h : GL (Fin 2) ℝ) :
    ∃ γ : SL(2, ℤ),
      Real.sqrt 3 / 2 ≤ localHeight (Matrix.SpecialLinearGroup.mapGL ℝ γ * h) ∧
      xWindowSq (Matrix.SpecialLinearGroup.mapGL ℝ γ * h) ≤ (1 / 2) ^ 2 := by
  obtain ⟨γ, hγ⟩ := ModularGroup.exists_smul_mem_fd (h • UpperHalfPlane.I)
  have hsmul : (Matrix.SpecialLinearGroup.mapGL ℝ γ * h) • UpperHalfPlane.I
      = γ • h • UpperHalfPlane.I := by
    rw [mul_smul]
    rfl
  refine ⟨γ, ?_, ?_⟩
  · rw [localHeight_eq_im_smul_I, hsmul]
    have h3 := ModularGroup.three_le_four_mul_im_sq_of_mem_fd hγ
    have hpos := (γ • h • UpperHalfPlane.I).im_pos
    have h4 : (3 : ℝ) ≤ (2 * (γ • h • UpperHalfPlane.I).im) ^ 2 := by nlinarith [h3]
    have h5 := Real.sqrt_le_sqrt h4
    rw [Real.sqrt_sq (by positivity)] at h5
    linarith
  · rw [xWindowSq_eq_re_smul_I_sq, hsmul]
    have h2 := hγ.2
    exact sq_le_sq.mpr (by rwa [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)])

theorem one_le_quadratic_form (c d : ℤ) (h : c ≠ 0 ∨ d ≠ 0) :
    1 ≤ c ^ 2 - c * d + d ^ 2 := by
  have key : 0 < c ^ 2 - c * d + d ^ 2 := by
    rcases h with hc | hd
    · rcases lt_or_gt_of_ne hc with h' | h' <;>
        nlinarith [sq_nonneg (c - 2 * d), Int.add_one_le_iff.mpr h']
    · rcases lt_or_gt_of_ne hd with h' | h' <;>
        nlinarith [sq_nonneg (2 * c - d), Int.add_one_le_iff.mpr h']
  linarith [Int.add_one_le_iff.mpr key]

theorem im_smul_rho_le (g : SL(2, ℤ)) :
    (g • UpperHalfPlane.ρ).im ≤ Real.sqrt 3 / 2 := by
  have h3 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  have hcd : (g 1 0 : ℤ) ≠ 0 ∨ (g 1 1 : ℤ) ≠ 0 :=
    (ModularGroup.bottom_row_coprime g).ne_zero_or_ne_zero
  have hint : (1 : ℤ) ≤ g 1 0 ^ 2 - g 1 0 * g 1 1 + g 1 1 ^ 2 :=
    one_le_quadratic_form _ _ hcd
  have hden : (1 : ℝ) ≤ Complex.normSq (denom g UpperHalfPlane.ρ) := by
    have heq : Complex.normSq (denom g UpperHalfPlane.ρ) =
        ((g 1 0 ^ 2 - g 1 0 * g 1 1 + g 1 1 ^ 2 : ℤ) : ℝ) := by
      rw [ModularGroup.denom_apply]
      simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
        Complex.mul_im, Complex.intCast_re, Complex.intCast_im, UpperHalfPlane.coe_re,
        UpperHalfPlane.coe_im]
      rw [show (UpperHalfPlane.ρ).re = -1 / 2 from rfl,
        show (UpperHalfPlane.ρ).im = Real.sqrt 3 / 2 from rfl]
      push_cast
      linear_combination ((g 1 0 : ℤ) : ℝ) ^ 2 / 4 * h3
    rw [heq]
    exact_mod_cast hint
  rw [ModularGroup.im_smul_eq_div_normSq]
  calc (UpperHalfPlane.ρ).im / Complex.normSq (denom g UpperHalfPlane.ρ)
      ≤ (UpperHalfPlane.ρ).im := by
        refine div_le_self ?_ hden
        rw [show (UpperHalfPlane.ρ).im = Real.sqrt 3 / 2 from rfl]
        positivity
    _ = Real.sqrt 3 / 2 := rfl

theorem localHeight_mapGL_mul_toSL2R_rho_le (γ : SL(2, ℤ)) :
    localHeight (Matrix.SpecialLinearGroup.mapGL ℝ γ *
        Matrix.SpecialLinearGroup.mapGL ℝ (UpperHalfPlane.toSL2R UpperHalfPlane.ρ))
      ≤ Real.sqrt 3 / 2 := by
  rw [localHeight_eq_im_smul_I, mul_smul]
  have h1 : Matrix.SpecialLinearGroup.mapGL ℝ (UpperHalfPlane.toSL2R UpperHalfPlane.ρ) •
      UpperHalfPlane.I = UpperHalfPlane.ρ :=
    UpperHalfPlane.toSL2R_smul_I UpperHalfPlane.ρ
  rw [h1]
  exact im_smul_rho_le γ

theorem not_forall_exists_one_le_localHeight :
    ¬ ∀ h : GL (Fin 2) ℝ, ∃ γ : SL(2, ℤ),
        1 ≤ localHeight (Matrix.SpecialLinearGroup.mapGL ℝ γ * h) := by
  intro hall
  obtain ⟨γ, hγ⟩ :=
    hall (Matrix.SpecialLinearGroup.mapGL ℝ (UpperHalfPlane.toSL2R UpperHalfPlane.ρ))
  have hle := localHeight_mapGL_mul_toSL2R_rho_le γ
  have hlt : Real.sqrt 3 / 2 < 1 := by
    rw [div_lt_one (by norm_num : (0 : ℝ) < 2)]
    rw [show (2 : ℝ) = Real.sqrt 4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  linarith

end Real

section RealPlace

variable {K : Type*} [Field K]

theorem norm_extensionEmbeddingOfIsReal {w : InfinitePlace K} (hw : w.IsReal) (x : w.Completion) :
    ‖InfinitePlace.Completion.extensionEmbeddingOfIsReal hw x‖ = ‖x‖ :=
  (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero
    (map_zero _) x

theorem map_extensionEmbeddingOfIsReal_mapGL {w : InfinitePlace K} (hw : w.IsReal) (γ : SL(2, ℤ)) :
    Matrix.GeneralLinearGroup.map (InfinitePlace.Completion.extensionEmbeddingOfIsReal hw)
        (Matrix.SpecialLinearGroup.mapGL w.Completion γ)
      = Matrix.SpecialLinearGroup.mapGL ℝ γ := by
  ext i j
  simp [Matrix.SpecialLinearGroup.mapGL, Matrix.SpecialLinearGroup.map_apply_coe,
    RingHom.mapMatrix_apply, Matrix.map_apply]

theorem exists_mapGL_mul_reduced_of_isReal {w : InfinitePlace K} (hw : w.IsReal)
    (g : GL (Fin 2) w.Completion) :
    ∃ γ : SL(2, ℤ),
      Real.sqrt 3 / 2 ≤ localHeight (Matrix.SpecialLinearGroup.mapGL w.Completion γ * g) ∧
      xWindowSq (Matrix.SpecialLinearGroup.mapGL w.Completion γ * g) ≤ (1 / 2) ^ 2 := by
  set e := InfinitePlace.Completion.extensionEmbeddingOfIsReal hw with he_def
  have he : ∀ x, ‖e x‖ = ‖x‖ := norm_extensionEmbeddingOfIsReal hw
  obtain ⟨γ, h1, h2⟩ := exists_mapGL_mul_reduced (Matrix.GeneralLinearGroup.map e g)
  have hmap : Matrix.GeneralLinearGroup.map e (Matrix.SpecialLinearGroup.mapGL w.Completion γ * g)
      = Matrix.SpecialLinearGroup.mapGL ℝ γ * Matrix.GeneralLinearGroup.map e g := by
    rw [map_mul, he_def, map_extensionEmbeddingOfIsReal_mapGL hw γ]
  refine ⟨γ, ?_, ?_⟩
  · rw [← localHeight_map e he, hmap]
    exact h1
  · rw [← xWindowSq_map e he, hmap]
    exact h2

theorem map_algebraMap_mapGL (w : InfinitePlace K) (γ : SL(2, ℤ)) :
    Matrix.GeneralLinearGroup.map (algebraMap K w.Completion) (Matrix.SpecialLinearGroup.mapGL K γ)
      = Matrix.SpecialLinearGroup.mapGL w.Completion γ :=
  by ext i j; simp [Matrix.SpecialLinearGroup.mapGL_coe_matrix]

end RealPlace

section Rat

theorem isReal_infinitePlace_rat (w : InfinitePlace ℚ) : w.IsReal := by
  rw [Subsingleton.elim w Rat.infinitePlace]
  exact Rat.isReal_infinitePlace

theorem exists_rat_translate_reduced (w : InfinitePlace ℚ) (g : GL (Fin 2) w.Completion) :
    ∃ γ : SL(2, ℤ),
      Real.sqrt 3 / 2 ≤ localHeight (Matrix.GeneralLinearGroup.map (algebraMap ℚ w.Completion)
          (Matrix.SpecialLinearGroup.mapGL ℚ γ) * g) ∧
      xWindowSq (Matrix.GeneralLinearGroup.map (algebraMap ℚ w.Completion)
          (Matrix.SpecialLinearGroup.mapGL ℚ γ) * g) ≤ (1 / 2) ^ 2 := by
  obtain ⟨γ, hγ⟩ := exists_mapGL_mul_reduced_of_isReal (isReal_infinitePlace_rat w) g
  refine ⟨γ, ?_⟩
  rw [map_algebraMap_mapGL]
  exact hγ

end Rat

section Adelic

open NumberField.AdelicLevel NumberField.AdelicVolume IsDedekindDomain Set SiegelReduction

variable (F : Type) [Field F] [NumberField F]

def FiniteIntegralCovering : Prop :=
  ∀ g : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F), ∃ γ : GL (Fin 2) F,
    glFin (𝓞 F) F (globalPoints (𝓞 F) F γ) * g ∈ finiteIntegralGL2 (𝓞 F) F

def CoversModCentre (D : Set (AdelicGL2 (𝓞 F) F)) : Prop :=
  ∀ g : AdelicGL2 (𝓞 F) F, ∃ γ : GL (Fin 2) F, ∃ z : (AdeleRing (𝓞 F) F)ˣ,
    globalPoints (𝓞 F) F γ * g * centralScalar (𝓞 F) F z ∈ D

variable {F}

theorem CoversModCentre.mono {D D' : Set (AdelicGL2 (𝓞 F) F)} (hDD' : D ⊆ D')
    (h : CoversModCentre F D) : CoversModCentre F D' := fun g => by
  obtain ⟨γ, z, hγ⟩ := h g
  exact ⟨γ, z, hDD' hγ⟩

theorem not_coversModCentre_empty : ¬ CoversModCentre F (∅ : Set (AdelicGL2 (𝓞 F) F)) := fun h => by
  obtain ⟨_, _, hγ⟩ := h 1
  exact hγ

theorem mul_centralScalar_comm (z : (AdeleRing (𝓞 F) F)ˣ) (X : AdelicGL2 (𝓞 F) F) :
    X * centralScalar (𝓞 F) F z = centralScalar (𝓞 F) F z * X := by
  refine Units.ext ?_
  show (X : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) * Matrix.scalar (Fin 2) (z : AdeleRing (𝓞 F) F)
    = Matrix.scalar (Fin 2) (z : AdeleRing (𝓞 F) F) * (X : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
  exact ((Matrix.scalar_commute _ (fun r' => Commute.all _ r') _).eq).symm

theorem algebraMap_intCast_mem_integralFiniteAdeles (n : ℤ) :
    algebraMap F (FiniteAdeleRing (𝓞 F) F) n ∈ integralFiniteAdeles (𝓞 F) F := by
  intro v
  rw [FiniteAdeleRing.algebraMap_apply, HeightOneSpectrum.mem_adicCompletionIntegers,
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation', ← map_intCast (algebraMap (𝓞 F) F) n]
  exact v.valuation_le_one _

theorem glFin_globalPoints_mapGL_mem (γ : SL(2, ℤ)) :
    glFin (𝓞 F) F (globalPoints (𝓞 F) F (Matrix.SpecialLinearGroup.mapGL F γ))
      ∈ finiteIntegralGL2 (𝓞 F) F := by
  rw [mem_finiteIntegralGL2_iff]
  constructor
  · intro i j
    rw [glFin_globalPoints_apply]
    convert algebraMap_intCast_mem_integralFiniteAdeles (F := F) (γ i j) using 2 <;>
      simp only [Matrix.SpecialLinearGroup.mapGL_coe_matrix, Matrix.SpecialLinearGroup.map_apply_coe,
        RingHom.mapMatrix_apply, Matrix.map_apply, eq_intCast]
  · intro i j
    rw [← map_inv, ← map_inv, ← map_inv, glFin_globalPoints_apply]
    convert algebraMap_intCast_mem_integralFiniteAdeles (F := F) ((γ⁻¹ : SL(2, ℤ)) i j) using 2 <;>
      simp only [Matrix.SpecialLinearGroup.mapGL_coe_matrix, Matrix.SpecialLinearGroup.map_apply_coe,
        RingHom.mapMatrix_apply, Matrix.map_apply, eq_intCast]

theorem glFin_centralScalar_archCentralUnit (w₀ : InfinitePlace F) (a : (w₀.Completion)ˣ) :
    glFin (𝓞 F) F (centralScalar (𝓞 F) F (archCentralUnit F w₀ a)) = 1 := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [glFin_apply, Units.val_one]
  by_cases h : i = j
  · subst h
    rw [centralScalar_apply_eq, archCentralUnit_snd, Matrix.one_apply_eq]
  · rw [centralScalar_apply_ne _ h, Matrix.one_apply_ne h]
    rfl

theorem archComponent_centralScalar_archCentralUnit_apply (w₀ : InfinitePlace F)
    (a : (w₀.Completion)ˣ) (i j : Fin 2) :
    ((archComponent F w₀ (glArch (𝓞 F) F (centralScalar (𝓞 F) F (archCentralUnit F w₀ a))) :
        GL (Fin 2) w₀.Completion) : Matrix (Fin 2) (Fin 2) w₀.Completion) i j
      = if i = j then (a : w₀.Completion) else 0 := by
  simp only [archComponent_apply, glArch_apply]
  by_cases h : i = j
  · subst h
    rw [centralScalar_apply_eq, if_pos rfl]
    exact archCentralUnit_fst_self w₀ a
  · rw [centralScalar_apply_ne _ h, if_neg h]
    rfl

theorem archComponent_glArch_globalPoints_mapGL (w : InfinitePlace F) (γ : SL(2, ℤ)) :
    archComponent F w (glArch (𝓞 F) F (globalPoints (𝓞 F) F (Matrix.SpecialLinearGroup.mapGL F γ)))
      = Matrix.SpecialLinearGroup.mapGL w.Completion γ := by
  rw [← map_algebraMap_mapGL]
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rfl

theorem coversModCentre_centreCutSiegelSet_rat (hfin : FiniteIntegralCovering ℚ) {c u d₁ d₂ : ℝ}
    (hc : c ≤ Real.sqrt 3 / 2) (hu : 1 / 2 ≤ u) (hd₂ : 0 < d₂) (hd : d₁ ≤ d₂) :
    CoversModCentre ℚ (centreCutSiegelSet ℚ c u d₁ d₂) := by
  intro g
  set w₀ : InfinitePlace ℚ := Rat.infinitePlace with hw₀
  have hw : w₀.IsReal := Rat.isReal_infinitePlace
  obtain ⟨γ₁, h₁⟩ := hfin (glFin (𝓞 ℚ) ℚ g)
  set g₁ := globalPoints (𝓞 ℚ) ℚ γ₁ * g with hg₁
  obtain ⟨γ₂, hh, hx⟩ :=
    exists_mapGL_mul_reduced_of_isReal hw (archComponent ℚ w₀ (glArch (𝓞 ℚ) ℚ g₁))
  set X := globalPoints (𝓞 ℚ) ℚ (Matrix.SpecialLinearGroup.mapGL ℚ γ₂) * g₁ with hX
  have hN := archDetNorm_pos w₀ X
  set t : ℝ := Real.sqrt (d₂ / archDetNorm w₀ X) with ht
  have ht2 : t * t * archDetNorm w₀ X = d₂ := by
    rw [ht, Real.mul_self_sqrt (div_nonneg hd₂.le hN.le), div_mul_cancel₀ _ hN.ne']
  have htpos : 0 < t := Real.sqrt_pos.mpr (div_pos hd₂ hN)
  set a₀ : w₀.Completion := (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm t with ha₀
  have hna : ‖a₀‖ = t := by
    rw [← norm_extensionEmbeddingOfIsReal hw a₀,
      ← InfinitePlace.Completion.ringEquivRealOfIsReal_apply hw, ha₀, RingEquiv.apply_symm_apply,
      Real.norm_eq_abs, abs_of_pos htpos]
  have ha0 : a₀ ≠ 0 := norm_pos_iff.mp (hna ▸ htpos)
  set a : (w₀.Completion)ˣ := Units.mk0 a₀ ha0 with ha
  refine ⟨Matrix.SpecialLinearGroup.mapGL ℚ γ₂ * γ₁, archCentralUnit ℚ w₀ a, ?_⟩
  have hY : globalPoints (𝓞 ℚ) ℚ (Matrix.SpecialLinearGroup.mapGL ℚ γ₂ * γ₁) * g *
      centralScalar (𝓞 ℚ) ℚ (archCentralUnit ℚ w₀ a)
        = centralScalar (𝓞 ℚ) ℚ (archCentralUnit ℚ w₀ a) * X := by
    rw [mul_centralScalar_comm, map_mul]
    simp only [hX, hg₁, mul_assoc]
  have h00 := archComponent_centralScalar_archCentralUnit_apply (F := ℚ) w₀ a 0 0
  have h01 := archComponent_centralScalar_archCentralUnit_apply (F := ℚ) w₀ a 0 1
  have h10 := archComponent_centralScalar_archCentralUnit_apply (F := ℚ) w₀ a 1 0
  have h11 := archComponent_centralScalar_archCentralUnit_apply (F := ℚ) w₀ a 1 1
  rw [if_pos rfl] at h00 h11
  rw [if_neg (by decide)] at h01 h10
  rw [hY, mem_centreCutSiegelSet_iff]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [map_mul, glFin_centralScalar_archCentralUnit, one_mul, hX, map_mul, hg₁, map_mul]
    exact mul_mem (glFin_globalPoints_mapGL_mem γ₂) h₁
  · intro w
    obtain rfl : w = w₀ := Subsingleton.elim _ _
    rw [map_mul, map_mul, localHeight_scalar_entries_mul a.ne_zero h00 h01 h10 h11, hX, map_mul,
      map_mul, archComponent_glArch_globalPoints_mapGL]
    exact hc.trans hh
  · intro w
    obtain rfl : w = w₀ := Subsingleton.elim _ _
    rw [map_mul, map_mul, xWindowSq_scalar_entries_mul a.ne_zero h00 h01 h10 h11, hX, map_mul,
      map_mul, archComponent_glArch_globalPoints_mapGL]
    exact hx.trans (pow_le_pow_left₀ (by norm_num) hu 2)
  · intro w
    obtain rfl : w = w₀ := Subsingleton.elim _ _
    rw [archDetNorm_centralScalar_mul, ha, Units.val_mk0, hna, ht2]
    exact ⟨hd, le_rfl⟩

end Adelic

end SiegelCovering

end AutomorphicForm


