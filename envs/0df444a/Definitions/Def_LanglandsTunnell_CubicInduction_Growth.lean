-- Prove2me | Definitions.Def_LanglandsTunnell_CubicInduction_Growth
-- name    : LanglandsTunnell_CubicInduction_Growth
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:27.528425+00:00
-- url     : https://prove2.me/theorems/cec2f2d3-7097-5498-99a5-abf360a731a4
-- title:
--   Adelic gauge on GL3​ and moderate growth
-- statement:
--   Throughout, $F$ is a number field and `AdelicGL 3 (𝓞 F) F` denotes $GL_3$ of the adele ring of $F$. For an infinite place $w$, `archPlaceComponent3` is the group homomorphism from $GL_3(\mathbb{A}_F)$ to $GL_3(F_w)$ obtained by projecting entrywise to the infinite adeles and then evaluating at $w$. Two entrywise sizes are introduced for a matrix $k \in GL_3(L)$ over a normed field $L$: `matrixSize` is the real number $\sum_{i,j}(\lVert k_{ij}\rVert + \lVert (k^{-1})_{ij}\rVert)$, an $\ell^1$-type size of $k$ together with its inverse rather than an operator norm, and `matrixSupSize` is the corresponding supremum $\sup_{i,j}\max(\lVert k_{ij}\rVert_+,\lVert (k^{-1})_{ij}\rVert_+)$ taken in $\mathbb{R}_{\ge 0}$. From these, `archGauge3` $g = 1 + \sum_{w \mid \infty}$ `matrixSize` of the component of $g$ at $w$, and `finGauge3` $g$ is the (Mathlib-style) unrestricted product over the height-one spectrum of $\mathcal{O}_F$ of the numbers `matrixSupSize` of the component of $g$ at $v$, so that it is the product over the finitely many $v$ where that factor differs from $1$ when the multiplicative support is finite. The gauge itself is `gauge3` $g = \max(1,$ `archGauge3` $g \cdot$ `finGauge3` $g)$; it satisfies $1 \le$ `gauge3` $F\,g$ and hence is strictly positive, and `archGauge3` is likewise bounded below by $1$ since `matrixSize` is nonnegative.
--
--   The growth condition `IsModerateGrowth3` for a function $\Phi : GL_3(\mathbb{A}_F) \to \mathbb{C}$ is the project's `IsSlowlyIncreasingOn` for the set of all group elements with height function `gauge3` $F$: there are a constant $C$ and an exponent $N \in \mathbb{N}$ with $\lVert \Phi(g)\rVert \le C \cdot ($`gauge3` $F\,g)^N$ for every $g$. Two immediate consequences are recorded: the zero function has moderate growth, and any globally bounded $\Phi$ has moderate growth (take $N = 0$).
--
--   **Relation to Mathlib.** Mathlib supplies the adele ring, the adic completions, completions at infinite places and `Matrix.GeneralLinearGroup`; the gauge functions and the moderate-growth predicate are the project's own, the latter phrased through the project's predicate [`AutomorphicForm.IsSlowlyIncreasingOn`](../def/AutomorphicForm_TruncationOperator.html#L13).
--
--   **Where it is used.** These definitions set up the analytic side of the carrier for automorphic forms on $GL_3$ over a number field, used in the cubic-induction treatment of the Langlands–Tunnell theorem: moderate growth with respect to `gauge3` is the growth axiom imposed on such forms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_LanglandsTunnell_CubicInduction_Growth.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_Carrier
import Definitions.Def_AutomorphicForm_TruncationOperator

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField Matrix

noncomputable section

namespace LanglandsTunnell.CubicInduction

section Gauge

variable (F : Type) [Field F] [NumberField F]

def archPlaceComponent3 (w : InfinitePlace F) : AdelicGL 3 (𝓞 F) F →* GL (Fin 3) w.Completion :=
  (Matrix.GeneralLinearGroup.map (AdelicLevel.archEval F w)).comp (archComponent3 (𝓞 F) F)

variable {F}

def matrixSize {L : Type*} [NormedField L] (k : GL (Fin 3) L) : ℝ :=
  ∑ i : Fin 3, ∑ j : Fin 3,
    (‖(k : Matrix (Fin 3) (Fin 3) L) i j‖ + ‖((k⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) i j‖)

theorem matrixSize_nonneg {L : Type*} [NormedField L] (k : GL (Fin 3) L) : 0 ≤ matrixSize k :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => add_nonneg (norm_nonneg _) (norm_nonneg _)

def matrixSupSize {L : Type*} [NormedField L] (k : GL (Fin 3) L) : NNReal :=
  Finset.univ.sup fun ij : Fin 3 × Fin 3 =>
    max ‖(k : Matrix (Fin 3) (Fin 3) L) ij.1 ij.2‖₊
      ‖((k⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) ij.1 ij.2‖₊

variable (F)

def archGauge3 (g : AdelicGL 3 (𝓞 F) F) : ℝ :=
  1 + ∑ w : InfinitePlace F, matrixSize (archPlaceComponent3 F w g)

def finGauge3 (g : AdelicGL 3 (𝓞 F) F) : ℝ :=
  ∏ᶠ v : HeightOneSpectrum (𝓞 F), ((matrixSupSize (componentAt3 (𝓞 F) F v g) : NNReal) : ℝ)

def gauge3 (g : AdelicGL 3 (𝓞 F) F) : ℝ :=
  max 1 (archGauge3 F g * finGauge3 F g)

theorem one_le_gauge3 (g : AdelicGL 3 (𝓞 F) F) : 1 ≤ gauge3 F g :=
  le_max_left _ _

theorem gauge3_pos (g : AdelicGL 3 (𝓞 F) F) : 0 < gauge3 F g :=
  lt_of_lt_of_le zero_lt_one (one_le_gauge3 F g)

theorem one_le_archGauge3 (g : AdelicGL 3 (𝓞 F) F) : 1 ≤ archGauge3 F g := by
  unfold archGauge3
  have h : 0 ≤ ∑ w : InfinitePlace F, matrixSize (archPlaceComponent3 F w g) :=
    Finset.sum_nonneg fun w _ => matrixSize_nonneg _
  linarith

end Gauge

section Growth

variable (F : Type) [Field F] [NumberField F]

def IsModerateGrowth3 (Φ : AdelicGL 3 (𝓞 F) F → ℂ) : Prop :=
  AutomorphicForm.IsSlowlyIncreasingOn Set.univ (gauge3 F) Φ

theorem isModerateGrowth3_zero : IsModerateGrowth3 F (fun _ => (0 : ℂ)) :=
  AutomorphicForm.isSlowlyIncreasingOn_of_bounded (C := 0) fun _ _ => by simp

theorem isModerateGrowth3_of_bounded {Φ : AdelicGL 3 (𝓞 F) F → ℂ} {C : ℝ} (hC : ∀ g, ‖Φ g‖ ≤ C) :
    IsModerateGrowth3 F Φ :=
  AutomorphicForm.isSlowlyIncreasingOn_of_bounded fun g _ => hC g

end Growth

end LanglandsTunnell.CubicInduction


