-- Prove2me | Definitions.Def_OAI_Analysis_Cotype_Cube
-- name    : OAI_Analysis_Cotype_Cube
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T16:20:46.150106+00:00
-- url     : https://prove2.me/theorems/842c045f-dd92-421a-b111-e5c053b763c3
-- title:
--   Walsh characters and Fourier coefficients on the cube
-- statement:
--   These notions belong to a proof that a real Banach space $X$ with the approximation property is K-convex (the Rademacher projection is bounded on $L_2(\{\pm1\}^n;X)$ uniformly in $n$) if and only if $X$ and its dual $X^*$ both have finite cotype. The converse direction shows that such $X$ has nontrivial type, i.e. does not contain $\ell_1^n$ uniformly, and then derives K-convexity from a power-gap estimate for commuting coordinate projections. Let $\iota$ be finite.
--
--   1. **Characters.** For $p,\varepsilon\in\{0,1\}^\iota$, $w_p(\varepsilon)=\prod_{i:\,p_i=1}\varepsilon_i$, where $\varepsilon_i=\pm1$ is the sign of the bit.
--   2. **Orthogonality.**
--   $$
--   \mathbb E_\varepsilon\,w_p(\varepsilon)w_q(\varepsilon)=[p=q] .
--   $$
--   3. **Fourier coefficients.** $\hat f(p)=\mathbb E_\varepsilon f(\varepsilon)w_p(\varepsilon)$ for real functions on the cube.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Cotype/Cube.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Cotype/Cube.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the Cotype mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_Cotype
import Definitions.Def_OAI_Analysis_Cotype_ComplexDualLift

namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
@[simp] theorem sign_false : sign false = 1 := rfl
@[simp] theorem sign_true : sign true = -1 := rfl
@[simp] theorem sign_sq (b : Bool) : sign b * sign b = 1 := by cases b <;> norm_num
@[simp] theorem sign_not (b : Bool) : sign (!b) = -sign b := by cases b <;> norm_num

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def character (p ε : ι → Bool) : ℝ := ∏ i, if p i then sign (ε i) else 1

omit [DecidableEq ι] in
@[simp] theorem character_sq (p ε : ι → Bool) : character p ε * character p ε = 1 := by
  rw [character, ← Finset.prod_mul_distrib]
  have h : ∀ i, (if p i then sign (ε i) else 1) *
      (if p i then sign (ε i) else 1) = (1 : ℝ) := by
    intro i; cases p i <;> simp
  simp_rw [h]
  simp

theorem character_orthogonality (p q : ι → Bool) :
    (∑ ε : ι → Bool, character p ε * character q ε) =
      if p = q then (Fintype.card (ι → Bool) : ℝ) else 0 := by
  simp only [character, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun i (b : Bool) =>
    (if p i then sign b else 1) * (if q i then sign b else 1))]
  have h : ∀ i, (∑ b : Bool, (if p i then sign b else 1) *
      (if q i then sign b else 1)) = if p i = q i then (2 : ℝ) else 0 := by
    intro i
    cases p i <;> cases q i <;> norm_num [Fintype.sum_bool]
  simp_rw [h]
  rw [Fintype.prod_ite_zero]
  have heq : (∀ i, p i = q i) ↔ p = q := funext_iff.symm
  simp only [heq]
  split_ifs <;> simp

theorem average_character_mul (p q : ι → Bool) :
    average (fun ε => character p ε * character q ε) = if p = q then 1 else 0 := by
  classical
  have hc : (Fintype.card (ι → Bool) : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero (α := ι → Bool))
  simp only [average, smul_eq_mul, character_orthogonality]
  split_ifs <;> simp_all

def fourier (f : (ι → Bool) → ℝ) (p : ι → Bool) : ℝ :=
  average (fun ε => f ε * character p ε)

end Cotype

end

end OAI


