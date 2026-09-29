-- Prove2me | Definitions.Def_AutomorphicForm_WindowedSiegelSet
-- name    : AutomorphicForm_WindowedSiegelSet
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/53435bdf-ee62-54e7-a6fe-20e104c6ab33
-- title:
--   Windowed Siegel sets for adelic GL2​
-- statement:
--   For a normed field $K$ and $g=\begin{pmatrix}a&b\\c&d\end{pmatrix}\in\mathrm{GL}_2(K)$ the module defines four real-valued functionals: `topNormSq` $=\|a\|^2+\|b\|^2$ and `rowNormSq` $=\|c\|^2+\|d\|^2$ (both on matrices), `localHeight` $g=\|\det g\|/\mathrm{rowNormSq}(g)$ and `xWindowSq` $g=\mathrm{topNormSq}(g)/\mathrm{rowNormSq}(g)-\mathrm{localHeight}(g)^2$ (on units). For a number field $F$, `archHeight F` of $g\in\mathrm{GL}_2(\mathbb{A}_{F,\infty})$ is $\prod_{v\mid\infty}\mathrm{localHeight}(g_v)^{\mathrm{mult}(v)}$, the $v$-component being taken through the project's `AdelicLevel.archComponent`. The central object, `integralWindowedSiegelSet F c u`, is the subset of the project's carrier `AdelicGL2 (𝓞 F) F` of those $g$ whose finite part `AdelicLevel.glFin` lies in `AdelicLevel.finiteIntegralGL2`, whose archimedean part has `archHeight` $\ge c$, and which satisfy $\mathrm{xWindowSq}(g_v)\le u^2$ at every infinite place $v$. Auxiliary definitions: `globalTranslate F γ g` is left multiplication by the image of $\gamma\in\mathrm{GL}_2(F)$ under `globalPoints`; `siegelOverlapSet F c u` is the set of $\gamma$ for which some point of the set is carried into the set; and three `Prop`-valued definitions stating properties rather than proving them: `WindowedSiegelProperty` (the image of the overlap set in $\mathrm{GL}_2(F)/Z$ is finite), `WindowedAdelicReduction` (every adelic point has a rational translate in the set), and `MeasureZeroOrInfiniteAt` (a given measure on the carrier assigns the set measure $0$ or $\infty$).
--
--   The theorems proved are elementary: $\mathrm{rowNormSq}>0$ and $\mathrm{localHeight}>0$ on invertible matrices (via non-vanishing of the bottom row), $\mathrm{archHeight}>0$, the normalisations at the identity, membership of $1$ when $c\le 1$, the scaling of `topNormSq`, `rowNormSq` by $\|z\|^2$ and the invariance of `localHeight`, `xWindowSq`, `archHeight` under left multiplication by a matrix with diagonal entries $z$ and vanishing off-diagonal entries, whence stability of the windowed Siegel set under such central elements with finite part $1$ and nonvanishing archimedean components; finally, the trivial remark that a measure satisfying `MeasureZeroOrInfiniteAt` cannot give the set finite nonzero measure.
--
--   **Relation to Mathlib.** Mathlib has no notion of Siegel set or of these height/window functionals; all definitions here are the project's own, built on Mathlib's `GL (Fin 2)`, `InfiniteAdeleRing`, `AdeleRing`, `InfinitePlace` and `MeasureTheory.Measure`.
--
--   **Where it is used.** The windowed Siegel set supplies the explicit domain used when adelic automorphic forms for $\mathrm{GL}_2$ are handled through the project's carrier-pins bundle; the `Prop`-valued definitions `WindowedSiegelProperty`, `WindowedAdelicReduction` and `MeasureZeroOrInfiniteAt` are the reduction-theoretic and measure-theoretic statements that consumer modules assume or establish about it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AutomorphicForm_WindowedSiegelSet.lean

import Definitions.Def_AutomorphicForm_CarrierPins
import Definitions.Def_NumberField_AdelicLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open IsDedekindDomain NumberField Matrix MeasureTheory

open scoped ENNReal

noncomputable section

namespace AutomorphicForm

namespace WindowedSiegel

variable {K : Type*} [NormedField K]

def topNormSq (g : Matrix (Fin 2) (Fin 2) K) : ℝ :=
  ‖g 0 0‖ ^ 2 + ‖g 0 1‖ ^ 2

def rowNormSq (g : Matrix (Fin 2) (Fin 2) K) : ℝ :=
  ‖g 1 0‖ ^ 2 + ‖g 1 1‖ ^ 2

def localHeight (g : GL (Fin 2) K) : ℝ :=
  ‖(g : Matrix (Fin 2) (Fin 2) K).det‖ / rowNormSq (g : Matrix (Fin 2) (Fin 2) K)

def xWindowSq (g : GL (Fin 2) K) : ℝ :=
  topNormSq (g : Matrix (Fin 2) (Fin 2) K) / rowNormSq (g : Matrix (Fin 2) (Fin 2) K)
    - localHeight g ^ 2

theorem rowNormSq_one : rowNormSq (1 : Matrix (Fin 2) (Fin 2) K) = 1 := by
  unfold rowNormSq
  rw [Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0), Matrix.one_apply_eq]
  simp

theorem localHeight_one : localHeight (1 : GL (Fin 2) K) = 1 := by
  unfold localHeight
  rw [show ((1 : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = 1 from rfl, rowNormSq_one,
    Matrix.det_one]
  simp

theorem xWindowSq_one : xWindowSq (1 : GL (Fin 2) K) = 0 := by
  unfold xWindowSq topNormSq
  rw [show ((1 : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = 1 from rfl, rowNormSq_one,
    localHeight_one, Matrix.one_apply_eq, Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1)]
  simp

variable (F : Type) [Field F] [NumberField F]

def archHeight (g : GL (Fin 2) (InfiniteAdeleRing F)) : ℝ :=
  ∏ v : InfinitePlace F, localHeight (AdelicLevel.archComponent F v g) ^ v.mult

theorem archHeight_one : archHeight F (1 : GL (Fin 2) (InfiniteAdeleRing F)) = 1 := by
  unfold archHeight
  simp [map_one, localHeight_one]

def integralWindowedSiegelSet (c u : ℝ) : Set (AdelicGL2 (𝓞 F) F) :=
  {g | AdelicLevel.glFin (𝓞 F) F g ∈ AdelicLevel.finiteIntegralGL2 (𝓞 F) F ∧ c ≤ archHeight F (AdelicLevel.glArch (𝓞 F) F g) ∧
    ∀ v : InfinitePlace F, xWindowSq (AdelicLevel.archComponent F v (AdelicLevel.glArch (𝓞 F) F g)) ≤ u ^ 2}

def globalTranslate (γ : GL (Fin 2) F) (g : AdelicGL2 (𝓞 F) F) : AdelicGL2 (𝓞 F) F :=
  globalPoints (𝓞 F) F γ * g

def siegelOverlapSet (c u : ℝ) : Set (GL (Fin 2) F) :=
  {γ | ∃ g ∈ integralWindowedSiegelSet F c u,
    globalTranslate F γ g ∈ integralWindowedSiegelSet F c u}

def WindowedSiegelProperty (c u : ℝ) : Prop :=
  (((QuotientGroup.mk : GL (Fin 2) F → GL (Fin 2) F ⧸ Subgroup.center (GL (Fin 2) F))) ''
    siegelOverlapSet F c u).Finite

def WindowedAdelicReduction (c u : ℝ) : Prop :=
  ∀ g : AdelicGL2 (𝓞 F) F, ∃ γ : GL (Fin 2) F,
    globalTranslate F γ g ∈ integralWindowedSiegelSet F c u

theorem one_mem_integralWindowedSiegelSet {c u : ℝ} (hc : c ≤ 1) :
    (1 : AdelicGL2 (𝓞 F) F) ∈ integralWindowedSiegelSet F c u := by
  refine ⟨?_, ?_, fun v => ?_⟩
  · rw [map_one]
    exact one_mem _
  · rw [map_one, archHeight_one]
    exact hc
  · rw [map_one, map_one, xWindowSq_one]
    exact sq_nonneg u

section Invariance

variable {K : Type*} [NormedField K]

theorem bottom_row_ne_zero (g : GL (Fin 2) K) :
    (g : Matrix (Fin 2) (Fin 2) K) 1 0 ≠ 0 ∨ (g : Matrix (Fin 2) (Fin 2) K) 1 1 ≠ 0 := by
  rcases eq_or_ne ((g : Matrix (Fin 2) (Fin 2) K) 1 0) 0 with h0 | h0
  · rcases eq_or_ne ((g : Matrix (Fin 2) (Fin 2) K) 1 1) 0 with h1 | h1
    · exact absurd (by rw [Matrix.det_fin_two, h0, h1]; ring)
        (Matrix.GeneralLinearGroup.det_ne_zero g)
    · exact Or.inr h1
  · exact Or.inl h0

theorem rowNormSq_pos (g : GL (Fin 2) K) :
    0 < rowNormSq (g : Matrix (Fin 2) (Fin 2) K) := by
  unfold rowNormSq
  rcases bottom_row_ne_zero g with h | h
  · exact add_pos_of_pos_of_nonneg (pow_pos (norm_pos_iff.2 h) 2) (sq_nonneg _)
  · exact add_pos_of_nonneg_of_pos (sq_nonneg _) (pow_pos (norm_pos_iff.2 h) 2)

theorem rowNormSq_scalar_entries_mul {s : GL (Fin 2) K} {z : K}
    (h10 : (s : Matrix (Fin 2) (Fin 2) K) 1 0 = 0)
    (h11 : (s : Matrix (Fin 2) (Fin 2) K) 1 1 = z)
    (g : GL (Fin 2) K) :
    rowNormSq ((s * g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
      = ‖z‖ ^ 2 * rowNormSq (g : Matrix (Fin 2) (Fin 2) K) := by
  have hcoe : ((s * g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
      = (s : Matrix (Fin 2) (Fin 2) K) * (g : Matrix (Fin 2) (Fin 2) K) := rfl
  have hbot : ∀ j : Fin 2,
      ((s : Matrix (Fin 2) (Fin 2) K) * (g : Matrix (Fin 2) (Fin 2) K)) 1 j
        = z * (g : Matrix (Fin 2) (Fin 2) K) 1 j := by
    intro j
    rw [Matrix.mul_apply, Fin.sum_univ_two, h10, h11]
    ring
  unfold rowNormSq
  rw [hcoe, hbot 0, hbot 1, norm_mul, norm_mul, mul_pow, mul_pow]
  ring

theorem topNormSq_scalar_entries_mul {s : GL (Fin 2) K} {z : K}
    (h00 : (s : Matrix (Fin 2) (Fin 2) K) 0 0 = z)
    (h01 : (s : Matrix (Fin 2) (Fin 2) K) 0 1 = 0)
    (g : GL (Fin 2) K) :
    topNormSq ((s * g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
      = ‖z‖ ^ 2 * topNormSq (g : Matrix (Fin 2) (Fin 2) K) := by
  have hcoe : ((s * g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
      = (s : Matrix (Fin 2) (Fin 2) K) * (g : Matrix (Fin 2) (Fin 2) K) := rfl
  have htop : ∀ j : Fin 2,
      ((s : Matrix (Fin 2) (Fin 2) K) * (g : Matrix (Fin 2) (Fin 2) K)) 0 j
        = z * (g : Matrix (Fin 2) (Fin 2) K) 0 j := by
    intro j
    rw [Matrix.mul_apply, Fin.sum_univ_two, h00, h01]
    ring
  unfold topNormSq
  rw [hcoe, htop 0, htop 1, norm_mul, norm_mul, mul_pow, mul_pow]
  ring

theorem localHeight_scalar_entries_mul {s : GL (Fin 2) K} {z : K} (hz : z ≠ 0)
    (h00 : (s : Matrix (Fin 2) (Fin 2) K) 0 0 = z)
    (h01 : (s : Matrix (Fin 2) (Fin 2) K) 0 1 = 0)
    (h10 : (s : Matrix (Fin 2) (Fin 2) K) 1 0 = 0)
    (h11 : (s : Matrix (Fin 2) (Fin 2) K) 1 1 = z)
    (g : GL (Fin 2) K) :
    localHeight (s * g) = localHeight g := by
  have hcoe : ((s * g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
      = (s : Matrix (Fin 2) (Fin 2) K) * (g : Matrix (Fin 2) (Fin 2) K) := rfl
  have hdets : (s : Matrix (Fin 2) (Fin 2) K).det = z ^ 2 := by
    rw [Matrix.det_fin_two, h00, h01, h10, h11]
    ring
  have hdet : ‖((s * g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det‖
      = ‖z‖ ^ 2 * ‖(g : Matrix (Fin 2) (Fin 2) K).det‖ := by
    rw [hcoe, Matrix.det_mul, hdets, norm_mul, norm_pow]
  have hz2 : (0 : ℝ) < ‖z‖ ^ 2 := pow_pos (norm_pos_iff.2 hz) 2
  have hrow := rowNormSq_scalar_entries_mul h10 h11 g
  unfold localHeight
  rw [hdet, hrow,
    div_eq_div_iff (mul_pos hz2 (rowNormSq_pos g)).ne' (rowNormSq_pos g).ne']
  ring

theorem xWindowSq_scalar_entries_mul {s : GL (Fin 2) K} {z : K} (hz : z ≠ 0)
    (h00 : (s : Matrix (Fin 2) (Fin 2) K) 0 0 = z)
    (h01 : (s : Matrix (Fin 2) (Fin 2) K) 0 1 = 0)
    (h10 : (s : Matrix (Fin 2) (Fin 2) K) 1 0 = 0)
    (h11 : (s : Matrix (Fin 2) (Fin 2) K) 1 1 = z)
    (g : GL (Fin 2) K) :
    xWindowSq (s * g) = xWindowSq g := by
  have hz2 : (‖z‖ ^ 2 : ℝ) ≠ 0 := (pow_pos (norm_pos_iff.2 hz) 2).ne'
  unfold xWindowSq
  rw [topNormSq_scalar_entries_mul h00 h01 g, rowNormSq_scalar_entries_mul h10 h11 g,
    localHeight_scalar_entries_mul hz h00 h01 h10 h11 g,
    mul_div_mul_left _ _ hz2]

end Invariance

section AdelicInvariance

variable (F : Type) [Field F] [NumberField F]

theorem glFin_scalar_eq_one {s : AdelicGL2 (𝓞 F) F} {w : AdeleRing (𝓞 F) F}
    (hwf : w.2 = 1)
    (h00 : (s : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 0 0 = w)
    (h01 : (s : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 0 1 = 0)
    (h10 : (s : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 0 = 0)
    (h11 : (s : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 1 = w) :
    AdelicLevel.glFin (𝓞 F) F s = 1 := by
  have h00' : ((s : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 0 0).2 = 1 := by
    rw [h00, hwf]
  have h01' : ((s : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 0 1).2 = 0 := by
    rw [h01]; rfl
  have h10' : ((s : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 0).2 = 0 := by
    rw [h10]; rfl
  have h11' : ((s : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 1).2 = 1 := by
    rw [h11, hwf]
  apply Units.ext
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [AdelicLevel.glFin_apply, h00', h01', h10', h11']

theorem archHeight_scalar_entries_mul {s : GL (Fin 2) (InfiniteAdeleRing F)}
    {z : InfiniteAdeleRing F} (hz : ∀ v : InfinitePlace F, z v ≠ 0)
    (h00 : (s : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) 0 0 = z)
    (h01 : (s : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) 0 1 = 0)
    (h10 : (s : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) 1 0 = 0)
    (h11 : (s : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) 1 1 = z)
    (g : GL (Fin 2) (InfiniteAdeleRing F)) :
    archHeight F (s * g) = archHeight F g := by
  unfold archHeight
  refine Finset.prod_congr rfl fun v _ ↦ ?_
  rw [map_mul]
  congr 1
  refine localHeight_scalar_entries_mul (hz v) ?_ ?_ ?_ ?_ (AdelicLevel.archComponent F v g)
  · rw [AdelicLevel.archComponent_apply, h00]
  · rw [AdelicLevel.archComponent_apply, h01]
    rfl
  · rw [AdelicLevel.archComponent_apply, h10]
    rfl
  · rw [AdelicLevel.archComponent_apply, h11]

theorem scalar_smul_mem_integralWindowedSiegelSet {c u : ℝ}
    {s : AdelicGL2 (𝓞 F) F} {w : AdeleRing (𝓞 F) F}
    (hwf : w.2 = 1) (hwa : ∀ v : InfinitePlace F, w.1 v ≠ 0)
    (h00 : (s : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 0 0 = w)
    (h01 : (s : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 0 1 = 0)
    (h10 : (s : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 0 = 0)
    (h11 : (s : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 1 = w)
    {g : AdelicGL2 (𝓞 F) F} (hg : g ∈ integralWindowedSiegelSet F c u) :
    s * g ∈ integralWindowedSiegelSet F c u := by
  obtain ⟨h1, h2, h3⟩ := hg
  have hglFin : AdelicLevel.glFin (𝓞 F) F s = 1 := glFin_scalar_eq_one F hwf h00 h01 h10 h11
  have harch00 : ((AdelicLevel.glArch (𝓞 F) F s : GL (Fin 2) (InfiniteAdeleRing F)) :
      Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) 0 0 = w.1 := by
    rw [AdelicLevel.glArch_apply, h00]
  have harch01 : ((AdelicLevel.glArch (𝓞 F) F s : GL (Fin 2) (InfiniteAdeleRing F)) :
      Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) 0 1 = 0 := by
    rw [AdelicLevel.glArch_apply, h01]
    rfl
  have harch10 : ((AdelicLevel.glArch (𝓞 F) F s : GL (Fin 2) (InfiniteAdeleRing F)) :
      Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) 1 0 = 0 := by
    rw [AdelicLevel.glArch_apply, h10]
    rfl
  have harch11 : ((AdelicLevel.glArch (𝓞 F) F s : GL (Fin 2) (InfiniteAdeleRing F)) :
      Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) 1 1 = w.1 := by
    rw [AdelicLevel.glArch_apply, h11]
  refine ⟨?_, ?_, fun v => ?_⟩
  · rw [map_mul, hglFin, one_mul]
    exact h1
  · rw [map_mul, archHeight_scalar_entries_mul F hwa harch00 harch01 harch10 harch11]
    exact h2
  · rw [map_mul, map_mul]
    have hcomp00 : ((AdelicLevel.archComponent F v (AdelicLevel.glArch (𝓞 F) F s) : GL (Fin 2) (v.Completion)) :
        Matrix (Fin 2) (Fin 2) (v.Completion)) 0 0 = w.1 v := by
      rw [AdelicLevel.archComponent_apply, harch00]
    have hcomp01 : ((AdelicLevel.archComponent F v (AdelicLevel.glArch (𝓞 F) F s) : GL (Fin 2) (v.Completion)) :
        Matrix (Fin 2) (Fin 2) (v.Completion)) 0 1 = 0 := by
      rw [AdelicLevel.archComponent_apply, harch01]
      rfl
    have hcomp10 : ((AdelicLevel.archComponent F v (AdelicLevel.glArch (𝓞 F) F s) : GL (Fin 2) (v.Completion)) :
        Matrix (Fin 2) (Fin 2) (v.Completion)) 1 0 = 0 := by
      rw [AdelicLevel.archComponent_apply, harch10]
      rfl
    have hcomp11 : ((AdelicLevel.archComponent F v (AdelicLevel.glArch (𝓞 F) F s) : GL (Fin 2) (v.Completion)) :
        Matrix (Fin 2) (Fin 2) (v.Completion)) 1 1 = w.1 v := by
      rw [AdelicLevel.archComponent_apply, harch11]
    rw [xWindowSq_scalar_entries_mul (hwa v) hcomp00 hcomp01 hcomp10 hcomp11]
    exact h3 v

end AdelicInvariance

section Positivity

variable {K : Type*} [NormedField K]

theorem localHeight_pos (g : GL (Fin 2) K) : 0 < localHeight g := by
  refine div_pos ?_ (rowNormSq_pos g)
  rw [norm_pos_iff]
  exact Matrix.GeneralLinearGroup.det_ne_zero g

end Positivity

variable (F : Type) [Field F] [NumberField F]

theorem archHeight_pos (g : GL (Fin 2) (InfiniteAdeleRing F)) : 0 < archHeight F g := by
  unfold archHeight
  exact Finset.prod_pos fun v _ => pow_pos (localHeight_pos _) _

def MeasureZeroOrInfiniteAt [MeasurableSpace (AdelicGL2 (𝓞 F) F)]
    (μ : Measure (AdelicGL2 (𝓞 F) F)) (c u : ℝ) : Prop :=
  μ (integralWindowedSiegelSet F c u) = 0 ∨ μ (integralWindowedSiegelSet F c u) = ⊤

theorem not_pos_and_lt_top_of_eq_zero_or_top {x : ℝ≥0∞} (h : x = 0 ∨ x = ⊤) :
    ¬(0 < x ∧ x < ⊤) := by
  rcases h with h | h <;> simp [h]

theorem not_pos_and_lt_top_of_measureZeroOrInfiniteAt [MeasurableSpace (AdelicGL2 (𝓞 F) F)]
    {μ : Measure (AdelicGL2 (𝓞 F) F)}
    {c u : ℝ} (h : MeasureZeroOrInfiniteAt F μ c u) :
    ¬(0 < μ (integralWindowedSiegelSet F c u) ∧ μ (integralWindowedSiegelSet F c u) < ⊤) :=
  not_pos_and_lt_top_of_eq_zero_or_top h

end WindowedSiegel

end AutomorphicForm

end


