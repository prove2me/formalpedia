-- Prove2me | Definitions.Def_AutomorphicForm_SiegelReduction
-- name    : AutomorphicForm_SiegelReduction
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/c3b130a5-dd7b-5d98-b82b-f9cd5d153483
-- title:
--   Archimedean height bound for integral global translates
-- statement:
--   Throughout, $F$ is a number field with ring of integers $\mathcal{O}_F$, and the heights are those of the windowed Siegel framework: for $g \in \mathrm{GL}_2(K)$ over a normed field $K$, `localHeight g` is $\lVert \det g\rVert/(\lVert g_{10}\rVert^2 + \lVert g_{11}\rVert^2)$, and `archHeight F` of an element of $\mathrm{GL}_2$ over the infinite adeles is the product over infinite places $w$ of $F$ of the local height of its $w$-component, raised to the power $w.\mathrm{mult}$. The module records the elementary compatibilities of the adelic component maps with global points — the $(i,j)$ entry of the $w$-component of the archimedean part of `globalPoints` $\gamma$ is the image of $\gamma_{ij}$ in $w$'s completion, the $(i,j)$ entry of the finite part is the image of $\gamma_{ij}$ in the finite adele ring, the determinant of the $w$-component is the image of $\det\gamma$, and $\lVert x\rVert = w(x)$ for $x \in F$ viewed in $w$'s completion — and then two inequalities.
--
--   First, for $\gamma \in \mathrm{GL}_2(F)$ with $\gamma_{10} \neq 0$ and any $h \in \mathrm{GL}_2$ over the infinite adeles, $$\mathrm{archHeight}(\gamma_\infty h)\cdot \mathrm{archHeight}(h) \le \bigl|N_{F/\mathbb{Q}}(\det\gamma)\bigr| \big/ \bigl|N_{F/\mathbb{Q}}(\gamma_{10})\bigr|^{2},$$ obtained from the place-by-place bound of the Siegel-coordinates module together with $\prod_w w(x)^{w.\mathrm{mult}} = |N_{F/\mathbb{Q}}(x)|$.
--
--   Second, an integrality package: an element of $F$ whose image in the finite adeles is integral lies in the image of $\mathcal{O}_F$; hence if the finite part of `globalPoints` $\gamma$ lies in `finiteIntegralGL2`, then every entry of $\gamma$ and of $\gamma^{-1}$ lies in the image of $\mathcal{O}_F$; an element of $F$ integral together with its inverse has $|N_{F/\mathbb{Q}}|=1$, and a nonzero integral element has $|N_{F/\mathbb{Q}}| \ge 1$. Combining these gives the main statement: if $\gamma_{10} \neq 0$ and the finite parts of both $g$ and $\gamma g$ lie in `finiteIntegralGL2`, then the product of the archimedean heights of $\gamma g$ and of $g$ is at most $1$.
--
--   **Relation to Mathlib.** The local and archimedean heights on $\mathrm{GL}_2$ over completions and over the adeles, and the integral subgroup `finiteIntegralGL2`, are the project's own notions; Mathlib supplies the adele rings, infinite places and their completions, and the facts about $\mathcal{O}_F$ used (unit criterion via the norm, nonvanishing of the integral norm).
--
--   **Where it is used.** The bound belongs to the adelic reduction theory supporting the windowed Siegel sets: it is the archimedean constraint that forces the set of global $\gamma$ translating one integral windowed Siegel set into another to be controlled, feeding the finiteness and reduction properties used in the adelic automorphic-forms infrastructure of the modularity argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AutomorphicForm_SiegelReduction.lean

import Definitions.Def_AutomorphicForm_SiegelCoordinates

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open NumberField IsDedekindDomain Matrix

noncomputable section

namespace AutomorphicForm

namespace SiegelReduction

open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCoordinates NumberField.AdelicLevel
  NumberField.InfinitePlace

variable (F : Type) [Field F] [NumberField F]

theorem archComponent_globalPoints_apply (w : InfinitePlace F) (γ : GL (Fin 2) F) (i j : Fin 2) :
    ((archComponent F w (glArch (𝓞 F) F (globalPoints (𝓞 F) F γ)) : GL (Fin 2) w.Completion) :
        Matrix (Fin 2) (Fin 2) w.Completion) i j
      = ((γ : Matrix (Fin 2) (Fin 2) F) i j : w.Completion) := rfl

theorem glFin_globalPoints_apply (γ : GL (Fin 2) F) (i j : Fin 2) :
    ((glFin (𝓞 F) F (globalPoints (𝓞 F) F γ) : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :
        Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j
      = algebraMap F (FiniteAdeleRing (𝓞 F) F) ((γ : Matrix (Fin 2) (Fin 2) F) i j) := rfl

omit [NumberField F] in

theorem norm_coe_completion (w : InfinitePlace F) (x : F) : ‖(x : w.Completion)‖ = w x := by
  rw [InfinitePlace.Completion.norm_coe]
  rfl

theorem det_archComponent_globalPoints (w : InfinitePlace F) (γ : GL (Fin 2) F) :
    ((archComponent F w (glArch (𝓞 F) F (globalPoints (𝓞 F) F γ)) : GL (Fin 2) w.Completion) :
        Matrix (Fin 2) (Fin 2) w.Completion).det
      = ((γ : Matrix (Fin 2) (Fin 2) F).det : w.Completion) := by
  rw [Matrix.det_fin_two, Matrix.det_fin_two]
  simp only [archComponent_globalPoints_apply, WithAbs.toAbs_sub, WithAbs.toAbs_mul,
    UniformSpace.Completion.coe_sub, UniformSpace.Completion.coe_mul]
  apply NumberField.InfinitePlace.Completion.ext
  rw [← NumberField.InfinitePlace.Completion.equiv_apply, map_sub, map_mul, map_mul]
  simp only [NumberField.InfinitePlace.Completion.equiv_apply]

theorem archHeight_globalPoints_mul_mul_archHeight_le (γ : GL (Fin 2) F)
    (hγ : (γ : Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0) (h : GL (Fin 2) (InfiniteAdeleRing F)) :
    archHeight F (glArch (𝓞 F) F (globalPoints (𝓞 F) F γ) * h) * archHeight F h
      ≤ |(Algebra.norm ℚ ((γ : Matrix (Fin 2) (Fin 2) F).det) : ℝ)|
          / |(Algebra.norm ℚ ((γ : Matrix (Fin 2) (Fin 2) F) 1 0) : ℝ)| ^ 2 := by
  have hplace : ∀ w : InfinitePlace F,
      localHeight (archComponent F w (glArch (𝓞 F) F (globalPoints (𝓞 F) F γ) * h))
          * localHeight (archComponent F w h)
        ≤ w ((γ : Matrix (Fin 2) (Fin 2) F).det) / w ((γ : Matrix (Fin 2) (Fin 2) F) 1 0) ^ 2 := by
    intro w
    have h10 : ((archComponent F w (glArch (𝓞 F) F (globalPoints (𝓞 F) F γ)) :
        GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion) 1 0 ≠ 0 := by
      rw [archComponent_globalPoints_apply, ← norm_pos_iff, norm_coe_completion]
      exact InfinitePlace.pos_iff.mpr hγ
    have hle := localHeight_mul_mul_localHeight_le
      (archComponent F w (glArch (𝓞 F) F (globalPoints (𝓞 F) F γ))) (archComponent F w h) h10
    rw [det_archComponent_globalPoints, archComponent_globalPoints_apply, norm_coe_completion,
      norm_coe_completion] at hle
    rwa [map_mul]
  have hnonneg : ∀ w : InfinitePlace F,
      0 ≤ localHeight (archComponent F w (glArch (𝓞 F) F (globalPoints (𝓞 F) F γ) * h))
        * localHeight (archComponent F w h) :=
    fun w => mul_nonneg (localHeight_pos _).le (localHeight_pos _).le
  unfold archHeight
  rw [← Finset.prod_mul_distrib]
  calc ∏ w : InfinitePlace F,
          localHeight (archComponent F w (glArch (𝓞 F) F (globalPoints (𝓞 F) F γ) * h)) ^ w.mult
            * localHeight (archComponent F w h) ^ w.mult
      = ∏ w : InfinitePlace F,
          (localHeight (archComponent F w (glArch (𝓞 F) F (globalPoints (𝓞 F) F γ) * h))
            * localHeight (archComponent F w h)) ^ w.mult := by
        refine Finset.prod_congr rfl fun w _ => ?_
        rw [mul_pow]
    _ ≤ ∏ w : InfinitePlace F,
          (w ((γ : Matrix (Fin 2) (Fin 2) F).det) / w ((γ : Matrix (Fin 2) (Fin 2) F) 1 0) ^ 2)
            ^ w.mult := by
        refine Finset.prod_le_prod (fun w _ => pow_nonneg (hnonneg w) _) fun w _ => ?_
        exact pow_le_pow_left₀ (hnonneg w) (hplace w) _
    _ = (∏ w : InfinitePlace F, w ((γ : Matrix (Fin 2) (Fin 2) F).det) ^ w.mult)
          / (∏ w : InfinitePlace F, w ((γ : Matrix (Fin 2) (Fin 2) F) 1 0) ^ w.mult) ^ 2 := by
        rw [← Finset.prod_pow, ← Finset.prod_div_distrib]
        refine Finset.prod_congr rfl fun w _ => ?_
        rw [div_pow, ← pow_mul, ← pow_mul, mul_comm 2]
    _ = |(Algebra.norm ℚ ((γ : Matrix (Fin 2) (Fin 2) F).det) : ℝ)|
          / |(Algebra.norm ℚ ((γ : Matrix (Fin 2) (Fin 2) F) 1 0) : ℝ)| ^ 2 := by
        rw [prod_eq_abs_norm, prod_eq_abs_norm, Rat.cast_abs, Rat.cast_abs]

theorem mem_range_of_coe_mem_integralFiniteAdeles {x : F}
    (hx : algebraMap F (FiniteAdeleRing (𝓞 F) F) x ∈ integralFiniteAdeles (𝓞 F) F) :
    x ∈ (algebraMap (𝓞 F) F).range := by
  refine HeightOneSpectrum.mem_integers_of_valuation_le_one F x fun v => ?_
  rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  exact valued_apply_le_one hx v

theorem mem_range_of_glFin_globalPoints_mem {γ : GL (Fin 2) F}
    (hγ : glFin (𝓞 F) F (globalPoints (𝓞 F) F γ) ∈ finiteIntegralGL2 (𝓞 F) F) (i j : Fin 2) :
    (γ : Matrix (Fin 2) (Fin 2) F) i j ∈ (algebraMap (𝓞 F) F).range ∧
      ((γ⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) i j ∈ (algebraMap (𝓞 F) F).range := by
  rw [mem_finiteIntegralGL2_iff] at hγ
  refine ⟨mem_range_of_coe_mem_integralFiniteAdeles F ?_,
    mem_range_of_coe_mem_integralFiniteAdeles F ?_⟩
  · rw [← glFin_globalPoints_apply]
    exact hγ.1 i j
  · rw [← glFin_globalPoints_apply, map_inv, map_inv]
    exact hγ.2 i j

theorem abs_norm_eq_one_of_mem_range {x : F} (hx : x ∈ (algebraMap (𝓞 F) F).range)
    (hx' : x⁻¹ ∈ (algebraMap (𝓞 F) F).range) (hx0 : x ≠ 0) : |Algebra.norm ℚ x| = 1 := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, hb⟩ := hx'
  have hab : a * b = 1 := by
    apply IsFractionRing.injective (𝓞 F) F
    rw [map_mul, map_one, hb, mul_inv_cancel₀ hx0]
  have hu : IsUnit a := IsUnit.of_mul_eq_one b hab
  have h1 := NumberField.isUnit_iff_norm.mp hu
  rw [RingOfIntegers.coe_norm] at h1
  exact h1

theorem one_le_abs_norm_of_mem_range {x : F} (hx : x ∈ (algebraMap (𝓞 F) F).range) (hx0 : x ≠ 0) :
    (1 : ℝ) ≤ |(Algebra.norm ℚ x : ℝ)| := by
  obtain ⟨a, rfl⟩ := hx
  have ha : a ≠ 0 := fun h => hx0 (by rw [h, map_zero])
  have hz : Algebra.norm ℤ a ≠ 0 := Algebra.norm_ne_zero_iff.mpr ha
  have hq : (Algebra.norm ℚ (algebraMap (𝓞 F) F a) : ℝ) = ((Algebra.norm ℤ a : ℤ) : ℝ) := by
    rw [show (algebraMap (𝓞 F) F a) = ((a : 𝓞 F) : F) from rfl, ← Algebra.coe_norm_int]
    push_cast
    rfl
  rw [hq, ← Int.cast_abs]
  exact_mod_cast Int.one_le_abs hz

theorem archHeight_mul_mul_archHeight_le_one (γ : GL (Fin 2) F)
    (hγ : (γ : Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0) (g : AdelicGL2 (𝓞 F) F)
    (hg : glFin (𝓞 F) F g ∈ finiteIntegralGL2 (𝓞 F) F)
    (hγg : glFin (𝓞 F) F (globalPoints (𝓞 F) F γ * g) ∈ finiteIntegralGL2 (𝓞 F) F) :
    archHeight F (glArch (𝓞 F) F (globalPoints (𝓞 F) F γ * g)) * archHeight F (glArch (𝓞 F) F g)
      ≤ 1 := by
  have hγint : glFin (𝓞 F) F (globalPoints (𝓞 F) F γ) ∈ finiteIntegralGL2 (𝓞 F) F := by
    have h := Subgroup.mul_mem _ hγg (Subgroup.inv_mem _ hg)
    rwa [map_mul, mul_inv_cancel_right] at h
  have hdet : ((γ : Matrix (Fin 2) (Fin 2) F).det) ∈ (algebraMap (𝓞 F) F).range := by
    rw [Matrix.det_fin_two]
    exact Subring.sub_mem _
      (Subring.mul_mem _ (mem_range_of_glFin_globalPoints_mem F hγint 0 0).1
        (mem_range_of_glFin_globalPoints_mem F hγint 1 1).1)
      (Subring.mul_mem _ (mem_range_of_glFin_globalPoints_mem F hγint 0 1).1
        (mem_range_of_glFin_globalPoints_mem F hγint 1 0).1)
  have hdet' : ((γ : Matrix (Fin 2) (Fin 2) F).det)⁻¹ ∈ (algebraMap (𝓞 F) F).range := by
    have hinv : ((γ : Matrix (Fin 2) (Fin 2) F).det)⁻¹
        = ((γ⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det := by
      rw [Matrix.coe_units_inv, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
    rw [hinv, Matrix.det_fin_two]
    exact Subring.sub_mem _
      (Subring.mul_mem _ (mem_range_of_glFin_globalPoints_mem F hγint 0 0).2
        (mem_range_of_glFin_globalPoints_mem F hγint 1 1).2)
      (Subring.mul_mem _ (mem_range_of_glFin_globalPoints_mem F hγint 0 1).2
        (mem_range_of_glFin_globalPoints_mem F hγint 1 0).2)
  have hdet0 : ((γ : Matrix (Fin 2) (Fin 2) F).det) ≠ 0 := (Matrix.isUnits_det_units γ).ne_zero
  have hN1 : |(Algebra.norm ℚ ((γ : Matrix (Fin 2) (Fin 2) F).det) : ℝ)| = 1 := by
    have h1 := abs_norm_eq_one_of_mem_range F hdet hdet' hdet0
    rw [← Rat.cast_abs, h1, Rat.cast_one]
  have hN2 : (1 : ℝ) ≤ |(Algebra.norm ℚ ((γ : Matrix (Fin 2) (Fin 2) F) 1 0) : ℝ)| :=
    one_le_abs_norm_of_mem_range F (mem_range_of_glFin_globalPoints_mem F hγint 1 0).1 hγ
  rw [map_mul]
  refine (archHeight_globalPoints_mul_mul_archHeight_le F γ hγ _).trans ?_
  rw [hN1, div_le_one (by positivity)]
  exact one_le_pow₀ hN2

end SiegelReduction

end AutomorphicForm


