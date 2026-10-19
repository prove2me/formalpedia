-- Prove2me | Definitions.Def_OAI_Probability_EntangledGames_Resolvent
-- name    : OAI_Probability_EntangledGames_Resolvent
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T09:48:58.792601+00:00
-- url     : https://prove2.me/theorems/f2917e3a-fa36-48c9-99b0-b62a18fc675d
-- title:
--   Resolvent $(A+sI)^{-1}$, purification kernel $A(A+sI)^{-1}$, and the integral $\int_0^\infty t^2(t+s)^{-2}\,ds=t$
-- statement:
--   Let $n$ be a finite index set, $A\in\mathbb{C}^{n\times n}$ a complex square matrix, $I$ the $n\times n$ identity matrix and $s\in\mathbb{R}$ a real parameter.
--
--   1. **Resolvent.** $R_A(s)=(A+sI)^{-1}$. For positive semidefinite $A$ and $s>0$ the matrix $A+sI$ is positive definite, hence invertible.
--   2. **Purification kernel.** $K_A(s)=A\,R_A(s)=A\,(A+sI)^{-1}$. For positive semidefinite $A$ and $s>0$ this is the matrix function obtained by applying $t\mapsto t/(t+s)$ to the eigenvalues of $A$.
--   3. **A scalar integral.** For every real $t\ge 0$ the function $s\mapsto t^2/(t+s)^2$ is Lebesgue integrable on $(0,\infty)$ and
--   $$\int_0^\infty\frac{t^2}{(t+s)^2}\,ds=t .$$
--
--   Applied eigenvalue by eigenvalue, item 3 gives the operator identity $\int_0^\infty K_A(s)^*K_A(s)\,ds=A$ for positive semidefinite $A$: the family $(K_A(s))_{s>0}$ is a continuous Gram factorization of $A$. Comparing these kernels for several matrices underlies the finite purification of a family of effects, and the same kernels give integral representations of the operator entropy, such as $\int_0^\infty\bigl(\tfrac{1}{1+s}A-K_A(s)\bigr)\,ds=A\log A$ for positive semidefinite $A$.
--
--   **Formalization Note** `resolvent A s` uses Mathlib's matrix inverse, which returns $0$ for a singular matrix; the two definitions carry no positivity hypothesis. Item 3 is the lemma `scalar_square_integral` (integrability on `Ioi 0` together with the value of the integral); for $t=0$ the integrand is identically $0$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/EntangledGames/Resolvent.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/EntangledGames/Resolvent.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the EntangledGames mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_EntangledGames
import Definitions.Def_OAI_Probability_EntangledGames_Basic

namespace OAI

universe u_n u_J

open scoped BigOperators ComplexOrder

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix

namespace ThresholdParallelRepetition.Resolvent

variable {n : Type u_n} [Fintype n] [DecidableEq n]

def resolvent (A : Matrix n n ℂ) (s : ℝ) : Matrix n n ℂ :=
  (A + s • (1 : Matrix n n ℂ))⁻¹

def purificationKernel (A : Matrix n n ℂ) (s : ℝ) : Matrix n n ℂ :=
  A * resolvent A s

end ThresholdParallelRepetition.Resolvent

noncomputable section
open MeasureTheory Filter Set
open scoped Topology

namespace ThresholdParallelRepetition.Resolvent

lemma scalar_square_integral {t : ℝ} (ht : 0 ≤ t) :
    IntegrableOn (fun s : ℝ => t ^ 2 / (t + s) ^ 2) (Ioi 0) ∧
      (∫ s : ℝ in Ioi 0, t ^ 2 / (t + s) ^ 2) = t := by
  rcases eq_or_lt_of_le ht with rfl | ht
  · simp
  have hd (s : ℝ) (hs : s ∈ Ici (0 : ℝ)) :
      HasDerivAt (fun u : ℝ => -(t ^ 2) / (t + u)) (t ^ 2 / (t + s) ^ 2) s := by
    convert! (hasDerivAt_const s (-(t ^ 2))).div
      ((hasDerivAt_id s).const_add t) (ne_of_gt (add_pos_of_pos_of_nonneg ht hs)) using 1
    simp only [id_eq]
    ring
  have htop : Tendsto (fun s : ℝ => t + s) atTop atTop := by
    refine tendsto_atTop.2 fun b => ?_
    filter_upwards [eventually_ge_atTop (b - t)] with s hs
    linarith
  have hl := htop.const_div_atTop (-(t ^ 2))
  have hpos (s : ℝ) (_hs : s ∈ Ioi (0 : ℝ)) : 0 ≤ t ^ 2 / (t + s) ^ 2 := by positivity
  refine ⟨integrableOn_Ioi_deriv_of_nonneg' hd hpos hl, ?_⟩
  rw [integral_Ioi_of_hasDerivAt_of_nonneg' hd hpos hl]
  simp only [add_zero, zero_sub, neg_div, neg_neg]
  field_simp

end ThresholdParallelRepetition.Resolvent

end
end

end OAI


