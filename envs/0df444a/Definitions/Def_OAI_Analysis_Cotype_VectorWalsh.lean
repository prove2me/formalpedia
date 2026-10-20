-- Prove2me | Definitions.Def_OAI_Analysis_Cotype_VectorWalsh
-- name    : OAI_Analysis_Cotype_VectorWalsh
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T16:28:41.171095+00:00
-- url     : https://prove2.me/theorems/3ff6ab1a-421a-4b08-bb3a-01968df5d8f4
-- title:
--   The vector-valued Walsh transform
-- statement:
--   These notions belong to a proof that a real Banach space $X$ with the approximation property is K-convex (the Rademacher projection is bounded on $L_2(\{\pm1\}^n;X)$ uniformly in $n$) if and only if $X$ and its dual $X^*$ both have finite cotype. The converse direction shows that such $X$ has nontrivial type, i.e. does not contain $\ell_1^n$ uniformly, and then derives K-convexity from a power-gap estimate for commuting coordinate projections. The cube $\{0,1\}^n$ (Booleans) carries the uniform average $\mathbb E$, the signs $\varepsilon_i=\pm1$, the Walsh characters $w_A(\varepsilon)=\prod_{i\in A}\varepsilon_i$, and the norm $\|f\|_{L_2}=(\mathbb E\|f(\varepsilon)\|^2)^{1/2}$ for $X$-valued functions. Let $X,Y$ be real normed spaces.
--
--   1. **Averages.** $\|\mathbb Ef\|\le\mathbb E\|f\|\le\|f\|_{L_2}$, and $|w_p(\varepsilon)|=1$.
--   2. **Vector Walsh transform.**
--   $$
--   \widehat f(v)=\mathbb E_u\,w_v(u)f(u)\in X ,
--   $$
--   with $\|\widehat f(v)\|\le\|f\|_{L_2}$.
--   3. **Operator Walsh transform.** For $T:X\to Y$, the transform of $u\mapsto T(f(u))$. The $L_2(X)$ norm also has a description through the Euclidean product space $\ell_2(\{0,1\}^n;X)$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Cotype/VectorWalsh.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Cotype/VectorWalsh.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the Cotype mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_Cotype
import Definitions.Def_OAI_Analysis_Cotype_ComplexDualLift
import Definitions.Def_OAI_Analysis_Cotype_Cube
import Definitions.Def_OAI_Analysis_Cotype_Target
import Definitions.Def_OAI_Analysis_Cotype_Moments
import Definitions.Def_OAI_Analysis_Cotype_Fourier
import Definitions.Def_OAI_Analysis_Cotype_ScalarWalsh

namespace OAI

noncomputable section
open scoped BigOperators
open WithLp
namespace Cotype
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

omit [NormedSpace ℝ X] in
theorem cubeL2_eq_piLp {n : ℕ} (f : Cube n → X) :
    cubeL2 X f = Real.sqrt ((Fintype.card (Cube n) : ℝ)⁻¹) *
      ‖(toLp 2 f : PiLp 2 (fun _ : Cube n => X))‖ := by
  rw [PiLp.norm_eq_of_L2]
  simp only [cubeL2, average, smul_eq_mul]
  exact Real.sqrt_mul (by positivity) _

theorem norm_average_le {α : Type*} [Fintype α] (f : α → X) :
    ‖average f‖ ≤ average (fun x => ‖f x‖) := by
  simp only [average, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity :
    0 ≤ (Fintype.card α : ℝ)⁻¹), smul_eq_mul]
  exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)

omit [NormedSpace ℝ X] in
theorem average_norm_le_cubeL2 {n : ℕ} (f : Cube n → X) :
    average (fun ε => ‖f ε‖) ≤ cubeL2 X f := by
  have hc : (Fintype.card (Cube n) : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hcs : (∑ ε, ‖f ε‖)^2 ≤ (Fintype.card (Cube n) : ℝ) * ∑ ε, ‖f ε‖^2 := by
    simpa using Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : Cube n => (1:ℝ)) (fun ε => ‖f ε‖)
  apply (sq_le_sq₀ (by exact mul_nonneg (by positivity) (Finset.sum_nonneg (fun ε _ => norm_nonneg _)))
    (cubeL2_nonneg f)).mp
  rw [cubeL2_sq]
  simp only [average, smul_eq_mul]
  apply (mul_le_mul_iff_right₀ (sq_pos_of_ne_zero hc)).mp
  field_simp
  exact hcs

theorem abs_character {n : ℕ} (p ε : Cube n) : |character p ε| = 1 := by
  have h := character_sq p ε
  nlinarith [sq_abs (character p ε), abs_nonneg (character p ε)]

def vectorWalsh {n : ℕ} (f : Cube n → X) (v : Cube n) : X :=
  average (fun u => character v u • f u)

def operatorWalsh {n : ℕ} (T : X →L[ℝ] Y) (f : Cube n → X) : Cube n → Y :=
  vectorWalsh (fun u => T (f u))

theorem vectorWalsh_bound {n : ℕ} (f : Cube n → X) (v : Cube n) :
    ‖vectorWalsh f v‖ ≤ cubeL2 X f := by
  have h := norm_average_le (fun u => character v u • f u)
  simp only [norm_smul, Real.norm_eq_abs, abs_character, one_mul] at h
  exact h.trans (average_norm_le_cubeL2 f)

end Cotype

end

end OAI


