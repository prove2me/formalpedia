-- Prove2me | Definitions.Def_OAI_Analysis_Cotype_Moments
-- name    : OAI_Analysis_Cotype_Moments
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T16:23:05.895428+00:00
-- url     : https://prove2.me/theorems/7dc68e32-c94f-443e-8029-ce33f4ab3a6e
-- title:
--   Coordinate moments on the cube
-- statement:
--   These notions belong to a proof that a real Banach space $X$ with the approximation property is K-convex (the Rademacher projection is bounded on $L_2(\{\pm1\}^n;X)$ uniformly in $n$) if and only if $X$ and its dual $X^*$ both have finite cotype. The converse direction shows that such $X$ has nontrivial type, i.e. does not contain $\ell_1^n$ uniformly, and then derives K-convexity from a power-gap estimate for commuting coordinate projections. The cube $\{0,1\}^n$ (Booleans) carries the uniform average $\mathbb E$, the signs $\varepsilon_i=\pm1$, the Walsh characters $w_A(\varepsilon)=\prod_{i\in A}\varepsilon_i$, and the norm $\|f\|_{L_2}=(\mathbb E\|f(\varepsilon)\|^2)^{1/2}$ for $X$-valued functions.
--
--   1. **Averages.** The average of a sum is the sum of averages, and $\mathbb E(a(\varepsilon)x)=(\mathbb Ea)\,x$.
--   2. **Unit indices.** $e_i\in\{0,1\}^n$ with a single $1$ at $i$, so $w_{e_i}(\varepsilon)=\varepsilon_i$.
--   3. **Coordinate orthogonality and moments.** $\mathbb E\,\varepsilon_i\varepsilon_j=[i=j]$. The moment of $f$ at $i$ is $\mathbb E\,\varepsilon_if(\varepsilon)$, and the Rademacher sum $\sum_j\varepsilon_jx_j$ has moments
--   $$
--   \mathbb E\,\varepsilon_i\sum_j\varepsilon_jx_j=x_i .
--   $$
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Cotype/Moments.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Cotype/Moments.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the Cotype mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_Cotype
import Definitions.Def_OAI_Analysis_Cotype_ComplexDualLift
import Definitions.Def_OAI_Analysis_Cotype_Cube
import Definitions.Def_OAI_Analysis_Cotype_Target

namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype

variable {ι κ E : Type*} [Fintype ι] [Fintype κ]
  [AddCommMonoid E] [Module ℝ E]

theorem average_sum (f : κ → ι → E) :
    average (fun i => ∑ k, f k i) = ∑ k, average (f k) := by
  simp only [average, Finset.smul_sum]
  rw [Finset.sum_comm]

theorem average_smul_const (a : ι → ℝ) (x : E) :
    average (fun i => a i • x) = average a • x := by
  simp only [average, smul_eq_mul]
  rw [← Finset.sum_smul, smul_smul]

def unitIndex {n : ℕ} (i : Fin n) : Cube n := fun j => decide (i = j)

@[simp] theorem character_unitIndex {n : ℕ} (i : Fin n) (ε : Cube n) :
    character (unitIndex i) ε = sign (ε i) := by
  simp [character, unitIndex]

theorem unitIndex_injective {n : ℕ} : Function.Injective (@unitIndex n) := by
  intro i j h
  have hh := congrFun h i
  simpa [unitIndex, eq_comm] using hh.symm

theorem coordinate_orthogonality {n : ℕ} (i j : Fin n) :
    average (fun ε : Cube n => sign (ε i) * sign (ε j)) = if i = j then 1 else 0 := by
  simpa [unitIndex_injective.eq_iff] using average_character_mul (unitIndex i) (unitIndex j)

variable (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem moment_rademacherSum {n : ℕ} (x : Fin n → X) (i : Fin n) :
    moment X (rademacherSum X x) i = x i := by
  simp only [moment, rademacherSum, Finset.smul_sum, smul_smul]
  rw [average_sum]
  simp_rw [average_smul_const, coordinate_orthogonality]
  simp

end Cotype

end

end OAI


