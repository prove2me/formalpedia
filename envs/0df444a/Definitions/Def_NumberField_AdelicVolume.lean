-- Prove2me | Definitions.Def_NumberField_AdelicVolume
-- name    : NumberField_AdelicVolume
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:29.330635+00:00
-- url     : https://prove2.me/theorems/bcf2e085-ceb7-50c9-aab8-43e0b6bb026d
-- title:
--   Adelic central scaling and volumes of windowed Siegel sets
-- statement:
--   Fix a number field $F$ and work in $G=\mathrm{GL}_2(\mathbb A_F)$ (`AdelicGL2 (𝓞 F) F`). Two definitions are made. First, for an infinite place $v_0$ of $F$ and $a\in(F_{v_0})^\times$, `archCentralUnit F v₀ a` is the adelic unit whose finite part is $1$ and whose infinite part is the constant function $1$ updated to $a$ at $v_0$, with inverse given by the same construction applied to $a^{-1}$; the accompanying lemmas record that its finite part is $1$, that its $v_0$-component is $a$, that its components at other infinite places are $1$, and hence that all its archimedean components are nonzero. Second, `archDetNorm v₀ g` $:= ‖\det(g_{v_0})‖$, the norm of the determinant of the $v_0$-component of the archimedean part of $g$; it is continuous, strictly positive, and satisfies $\mathrm{archDetNorm}_{v_0}(\mathrm{diag}(w,w)\,g)=\|a\|^2\,\mathrm{archDetNorm}_{v_0}(g)$ for $w=$ `archCentralUnit F v₀ a`, where $\mathrm{diag}(w,w)$ is the project's `centralScalar`, whose entries are computed in the three lemmas `centralScalar_val`, `centralScalar_apply_eq`, `centralScalar_apply_ne`. A separate lemma gives $\|2\|=2$ in every archimedean completion.
--
--   These feed the theorems of the module. Taking $a=2$ at some infinite place (so the scaling factor is $4>1$) and applying the project's scaling dichotomy, any Borel-measurable $D\subseteq G$ stable under left multiplication by the central scalars $\mathrm{diag}(w,w)$ with $w$ of finite part $1$ and nonzero archimedean components has $\mu(D)=0$ or $\mu(D)=\infty$ for every left-invariant measure $\mu$ on the Borel sets of $G$; if in addition $\mu$ is positive on nonempty open sets and $D$ contains a nonempty open set, then $\mu(D)=\infty$. The integrally windowed Siegel set $\mathfrak S(c,u)$ (finite part in the integral level subgroup, archimedean height $\ge c$, window `xWindowSq` $\le u^2$ at each infinite place) is such a $D$: hence `MeasureZeroOrInfiniteAt` holds for all $\mu$, $c$, $u$, its measure is never both positive and finite, and $\mu(\mathfrak S(c,u))=\infty$ whenever $c<1$, $u\ne0$ and $\mu$ is left-invariant and open-positive. Finally, for $c<1$, $u\ne0$ the image of $\mathfrak S(c,u)$ in the central quotient `AdelicPGL2 (𝓞 F) F` has positive measure for any open-positive measure there, and in particular for the Haar measure `adelicPGLHaar`. No finiteness statement on the quotient is asserted.
--
--   **Relation to Mathlib.** Mathlib supplies the adele ring, $\mathrm{GL}_2$ over it, `Matrix.GeneralLinearGroup.scalar`, Haar measures and the Borel machinery; the archimedean central unit, the local determinant norm `archDetNorm`, the windowed Siegel set and the zero-or-infinite scaling dichotomy they feed are the project's own notions.
--
--   **Where it is used.** The windowed Siegel set is the candidate fundamental domain in the project's adelic framework for automorphic forms on $\mathrm{GL}_2$. These results show that the two volume conditions usually imposed on such a set — nonzero and finite Haar measure — can never hold simultaneously in $\mathrm{GL}_2(\mathbb A_F)$ itself, so they must be formulated on the central quotient, where positivity is proved here.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_NumberField_AdelicVolume.lean

import Definitions.Def_MeasureTheory_ScalingDichotomy
import Definitions.Def_AutomorphicForm_WindowedSiegelTopology
import Definitions.Def_NumberField_AdelicCentre

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory Set IsDedekindDomain NumberField MeasureTheory.ScalingDichotomy
open scoped ENNReal

noncomputable section

namespace NumberField.AdelicVolume

section Adelic

open AutomorphicForm AutomorphicForm.WindowedSiegel NumberField.AdelicLevel

variable (F : Type) [Field F] [NumberField F]

open scoped Classical in

def archCentralUnit (v₀ : InfinitePlace F) (a : (v₀.Completion)ˣ) : (AdeleRing (𝓞 F) F)ˣ where
  val := (Function.update (1 : InfiniteAdeleRing F) v₀ (a : v₀.Completion), 1)
  inv := (Function.update (1 : InfiniteAdeleRing F) v₀ ((a⁻¹ : (v₀.Completion)ˣ) : v₀.Completion), 1)
  val_inv := by
    refine Prod.ext (funext fun v => ?_) (one_mul 1)
    show Function.update (1 : InfiniteAdeleRing F) v₀ (a : v₀.Completion) v *
        Function.update (1 : InfiniteAdeleRing F) v₀ ((a⁻¹ : (v₀.Completion)ˣ) : v₀.Completion) v
      = 1
    by_cases hv : v = v₀
    · subst hv
      simp
    · simp only [Function.update_of_ne hv]
      exact mul_one (1 : v.Completion)
  inv_val := by
    refine Prod.ext (funext fun v => ?_) (one_mul 1)
    show Function.update (1 : InfiniteAdeleRing F) v₀ ((a⁻¹ : (v₀.Completion)ˣ) : v₀.Completion) v *
        Function.update (1 : InfiniteAdeleRing F) v₀ (a : v₀.Completion) v = 1
    by_cases hv : v = v₀
    · subst hv
      simp
    · simp only [Function.update_of_ne hv]
      exact mul_one (1 : v.Completion)

variable {F}

theorem archCentralUnit_snd (v₀ : InfinitePlace F) (a : (v₀.Completion)ˣ) :
    ((archCentralUnit F v₀ a : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 = 1 := rfl

open scoped Classical in
theorem archCentralUnit_fst_self (v₀ : InfinitePlace F) (a : (v₀.Completion)ˣ) :
    ((archCentralUnit F v₀ a : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 v₀ = a := by
  show Function.update (1 : InfiniteAdeleRing F) v₀ (a : v₀.Completion) v₀ = a
  simp

open scoped Classical in
theorem archCentralUnit_fst_of_ne (v₀ : InfinitePlace F) (a : (v₀.Completion)ˣ) {v : InfinitePlace F}
    (hv : v ≠ v₀) :
    ((archCentralUnit F v₀ a : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 v = 1 := by
  show Function.update (1 : InfiniteAdeleRing F) v₀ (a : v₀.Completion) v = 1
  rw [Function.update_of_ne hv]
  rfl

theorem archCentralUnit_fst_ne_zero (v₀ : InfinitePlace F) (a : (v₀.Completion)ˣ) (v : InfinitePlace F) :
    ((archCentralUnit F v₀ a : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 v ≠ 0 := by
  by_cases hv : v = v₀
  · subst hv
    rw [archCentralUnit_fst_self]
    exact a.ne_zero
  · rw [archCentralUnit_fst_of_ne v₀ a hv]
    exact one_ne_zero

theorem centralScalar_val (w : (AdeleRing (𝓞 F) F)ˣ) :
    ((centralScalar (𝓞 F) F w : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
      = Matrix.diagonal fun _ => (w : AdeleRing (𝓞 F) F) := by
  show Matrix.scalar (Fin 2) (w : AdeleRing (𝓞 F) F) = _
  rw [Matrix.scalar_apply]

theorem centralScalar_apply_eq (w : (AdeleRing (𝓞 F) F)ˣ) (i : Fin 2) :
    ((centralScalar (𝓞 F) F w : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i i
      = (w : AdeleRing (𝓞 F) F) := by
  rw [centralScalar_val, Matrix.diagonal_apply_eq]

theorem centralScalar_apply_ne (w : (AdeleRing (𝓞 F) F)ˣ) {i j : Fin 2} (h : i ≠ j) :
    ((centralScalar (𝓞 F) F w : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j
      = 0 := by
  rw [centralScalar_val, Matrix.diagonal_apply_ne _ h]

omit [NumberField F] in

theorem norm_two_completion (v₀ : InfinitePlace F) : ‖(2 : v₀.Completion)‖ = 2 := by
  rw [← (InfinitePlace.Completion.isometry_extensionEmbedding v₀).norm_map_of_map_zero (map_zero _),
    map_ofNat, RCLike.norm_ofNat]

def archDetNorm (v₀ : InfinitePlace F) (g : AdelicGL2 (𝓞 F) F) : ℝ :=
  ‖((archComponent F v₀ (glArch (𝓞 F) F g) : GL (Fin 2) v₀.Completion) :
      Matrix (Fin 2) (Fin 2) v₀.Completion).det‖

theorem continuous_archDetNorm (v₀ : InfinitePlace F) : Continuous (archDetNorm (F := F) v₀) :=
  continuous_norm.comp ((Units.continuous_val.comp
    ((continuous_archComponent F v₀).comp (continuous_glArch (𝓞 F) F))).matrix_det)

theorem archDetNorm_pos (v₀ : InfinitePlace F) (g : AdelicGL2 (𝓞 F) F) : 0 < archDetNorm v₀ g :=
  norm_pos_iff.mpr (Matrix.GeneralLinearGroup.det_ne_zero _)

theorem archDetNorm_centralScalar_mul (v₀ : InfinitePlace F) (a : (v₀.Completion)ˣ)
    (g : AdelicGL2 (𝓞 F) F) :
    archDetNorm v₀ (centralScalar (𝓞 F) F (archCentralUnit F v₀ a) * g)
      = (‖(a : v₀.Completion)‖ * ‖(a : v₀.Completion)‖) * archDetNorm v₀ g := by
  unfold archDetNorm
  rw [map_mul, map_mul, Units.val_mul, Matrix.det_mul, norm_mul]
  congr 1

  set s := archComponent F v₀ (glArch (𝓞 F) F (centralScalar (𝓞 F) F (archCentralUnit F v₀ a)))
  have hs : ∀ i j : Fin 2, (s : Matrix (Fin 2) (Fin 2) v₀.Completion) i j
      = if i = j then (a : v₀.Completion) else 0 := by
    intro i j
    simp only [s, archComponent_apply, glArch_apply]
    by_cases h : i = j
    · subst h
      rw [centralScalar_apply_eq, if_pos rfl]
      exact archCentralUnit_fst_self v₀ a
    · rw [centralScalar_apply_ne _ h, if_neg h]
      rfl
  rw [Matrix.det_fin_two, hs, hs, hs, hs]
  simp [norm_mul]

theorem measure_eq_zero_or_top_of_central_stable [MeasurableSpace (AdelicGL2 (𝓞 F) F)]
    [BorelSpace (AdelicGL2 (𝓞 F) F)] (μ : Measure (AdelicGL2 (𝓞 F) F)) [μ.IsMulLeftInvariant]
    {D : Set (AdelicGL2 (𝓞 F) F)} (hD : MeasurableSet D)
    (hstab : ∀ w : (AdeleRing (𝓞 F) F)ˣ, (w : AdeleRing (𝓞 F) F).2 = 1 →
      (∀ v : InfinitePlace F, (w : AdeleRing (𝓞 F) F).1 v ≠ 0) →
      ∀ g ∈ D, centralScalar (𝓞 F) F w * g ∈ D) :
    μ D = 0 ∨ μ D = ⊤ := by
  obtain ⟨v₀⟩ := (inferInstance : Nonempty (InfinitePlace F))
  have ha₀ : (1 : ℝ) < ‖(2 : v₀.Completion)‖ := by rw [norm_two_completion]; norm_num
  have ha0 : (2 : v₀.Completion) ≠ 0 := norm_pos_iff.mp (zero_lt_one.trans ha₀)
  set a : (v₀.Completion)ˣ := Units.mk0 (2 : v₀.Completion) ha0
  set z := centralScalar (𝓞 F) F (archCentralUnit F v₀ a)
  have hzinv : z⁻¹ = centralScalar (𝓞 F) F (archCentralUnit F v₀ a⁻¹) := by
    rw [← map_inv]
    congr 1
  have hzD : (fun g => z * g) ⁻¹' D = D := by
    ext g
    simp only [mem_preimage]
    constructor
    · intro h
      have := hstab (archCentralUnit F v₀ a⁻¹) (archCentralUnit_snd v₀ a⁻¹)
        (archCentralUnit_fst_ne_zero v₀ a⁻¹) _ h
      rwa [← hzinv, inv_mul_cancel_left] at this
    · intro h
      exact hstab (archCentralUnit F v₀ a) (archCentralUnit_snd v₀ a) (archCentralUnit_fst_ne_zero v₀ a) _ h
  refine measure_eq_zero_or_top_of_mul_preimage_eq μ (continuous_archDetNorm v₀).measurable
    (r := ‖(a : v₀.Completion)‖ * ‖(a : v₀.Completion)‖) (one_lt_mul_of_le_of_lt ha₀.le ha₀)
    (archDetNorm_centralScalar_mul v₀ a) (fun g _ => archDetNorm_pos v₀ g) hD hzD

theorem centralScalar_mul_mem_integralWindowedSiegelSet {c u : ℝ} {w : (AdeleRing (𝓞 F) F)ˣ}
    (hwf : (w : AdeleRing (𝓞 F) F).2 = 1) (hwa : ∀ v : InfinitePlace F, (w : AdeleRing (𝓞 F) F).1 v ≠ 0)
    {g : AdelicGL2 (𝓞 F) F} (hg : g ∈ integralWindowedSiegelSet F c u) :
    centralScalar (𝓞 F) F w * g ∈ integralWindowedSiegelSet F c u :=
  scalar_smul_mem_integralWindowedSiegelSet F hwf hwa (centralScalar_apply_eq w 0)
    (centralScalar_apply_ne w (by decide)) (centralScalar_apply_ne w (by decide))
    (centralScalar_apply_eq w 1) hg

theorem measureZeroOrInfiniteAt [MeasurableSpace (AdelicGL2 (𝓞 F) F)]
    [BorelSpace (AdelicGL2 (𝓞 F) F)] (μ : Measure (AdelicGL2 (𝓞 F) F)) [μ.IsMulLeftInvariant]
    (c u : ℝ) : MeasureZeroOrInfiniteAt F μ c u :=
  measure_eq_zero_or_top_of_central_stable μ (measurableSet_integralWindowedSiegelSet F c u)
    fun _ hwf hwa _ hg => centralScalar_mul_mem_integralWindowedSiegelSet hwf hwa hg

theorem not_pos_and_lt_top_measure_integralWindowedSiegelSet [MeasurableSpace (AdelicGL2 (𝓞 F) F)]
    [BorelSpace (AdelicGL2 (𝓞 F) F)] (μ : Measure (AdelicGL2 (𝓞 F) F)) [μ.IsMulLeftInvariant]
    (c u : ℝ) :
    ¬(0 < μ (integralWindowedSiegelSet F c u) ∧ μ (integralWindowedSiegelSet F c u) < ⊤) :=
  not_pos_and_lt_top_of_measureZeroOrInfiniteAt F (measureZeroOrInfiniteAt μ c u)

theorem measure_eq_top_of_central_stable_of_interior [MeasurableSpace (AdelicGL2 (𝓞 F) F)]
    [BorelSpace (AdelicGL2 (𝓞 F) F)] (μ : Measure (AdelicGL2 (𝓞 F) F)) [μ.IsMulLeftInvariant]
    [μ.IsOpenPosMeasure] {D : Set (AdelicGL2 (𝓞 F) F)} (hD : MeasurableSet D)
    (hstab : ∀ w : (AdeleRing (𝓞 F) F)ˣ, (w : AdeleRing (𝓞 F) F).2 = 1 →
      (∀ v : InfinitePlace F, (w : AdeleRing (𝓞 F) F).1 v ≠ 0) →
      ∀ g ∈ D, centralScalar (𝓞 F) F w * g ∈ D)
    (hU : ∃ U : Set (AdelicGL2 (𝓞 F) F), IsOpen U ∧ U.Nonempty ∧ U ⊆ D) :
    μ D = ⊤ := by
  obtain ⟨U, hUo, hUne, hUD⟩ := hU
  have hpos : 0 < μ D := (hUo.measure_pos μ hUne).trans_le (measure_mono hUD)
  exact (measure_eq_zero_or_top_of_central_stable μ hD hstab).resolve_left hpos.ne'

theorem measure_integralWindowedSiegelSet_eq_top [MeasurableSpace (AdelicGL2 (𝓞 F) F)]
    [BorelSpace (AdelicGL2 (𝓞 F) F)] (μ : Measure (AdelicGL2 (𝓞 F) F)) [μ.IsMulLeftInvariant]
    [μ.IsOpenPosMeasure] {c u : ℝ} (hc : c < 1) (hu : u ≠ 0) :
    μ (integralWindowedSiegelSet F c u) = ⊤ :=
  measure_eq_top_of_central_stable_of_interior μ (measurableSet_integralWindowedSiegelSet F c u)
    (fun _ hwf hwa _ hg => centralScalar_mul_mem_integralWindowedSiegelSet hwf hwa hg)
    (exists_isOpen_subset_integralWindowedSiegelSet F hc hu)

open NumberField.AdelicCentre in

theorem measure_image_mk_integralWindowedSiegelSet_pos {m : MeasurableSpace (AdelicPGL2 (𝓞 F) F)}
    (μ : Measure (AdelicPGL2 (𝓞 F) F)) [μ.IsOpenPosMeasure] {c u : ℝ} (hc : c < 1) (hu : u ≠ 0) :
    0 < μ (QuotientGroup.mk '' integralWindowedSiegelSet F c u) :=
  measure_image_mk_pos (𝓞 F) F μ (exists_isOpen_subset_integralWindowedSiegelSet F hc hu)

open NumberField.AdelicCentre in

theorem adelicPGLHaar_image_integralWindowedSiegelSet_pos {c u : ℝ} (hc : c < 1) (hu : u ≠ 0) :
    0 < adelicPGLHaar (𝓞 F) F (QuotientGroup.mk '' integralWindowedSiegelSet F c u) :=
  adelicPGLHaar_image_pos (𝓞 F) F (exists_isOpen_subset_integralWindowedSiegelSet F hc hu)

end Adelic

end NumberField.AdelicVolume

end


