-- Prove2me | Definitions.Def_LanglandsTunnell_RSGlobalIntegral
-- name    : LanglandsTunnell_RSGlobalIntegral
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.084567+00:00
-- url     : https://prove2.me/theorems/1ecfad0a-afdc-5192-9dfd-9a2046b14b35
-- title:
--   Global Rankin–Selberg integral for GL2​ against GL3​
-- statement:
--   The module is set over $\mathbb{Q}$, with $\mathrm{GL}_2$ of the adele ring written `AdelicGL2 (𝓞 ℚ) ℚ` and $\mathrm{GL}_3$ of the adele ring written `AdelicGL 3 (𝓞 ℚ) ℚ`, both carrying the Borel measurable structure [`NumberField.AdelicHaar.glBorel`](../def/NumberField_AdelicHaar.html#L176).
--
--   The main definition is `rsGlobalIntegral`: given a set $D$ of adelic $2\times 2$ matrices, a complex parameter $s$, a function $\varphi$ on $\mathrm{GL}_2(\mathbb{A}_{\mathbb{Q}})$ and a function $\Theta$ on $\mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}})$, it is the Bochner integral
--   $$\int_{D}\varphi(g)\,\Theta\bigl(\iota(g)\bigr)\,\lVert\det g\rVert^{\,s-1/2}\,dg$$
--   against the Haar measure [`NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ`](../def/NumberField_AdelicHaar.html#L189), where $\iota$ is the group embedding `iota (𝓞 ℚ) ℚ` of adelic $\mathrm{GL}_2$ into adelic $\mathrm{GL}_3$, and $\lVert\det g\rVert$ is `detNorm g`, the idele norm [`NumberField.TateGlobal.ideleNorm ℚ`](../def/NumberField_TateGlobalZeta.html#L19) of the determinant of $g$, a real number, coerced to $\mathbb{C}$ and raised to the complex power $s-1/2$ in the principal-branch sense. No integrability hypothesis is imposed: off the region of convergence the Bochner integral takes its default value $0$. Two elementary companions record this: `rsGlobalIntegral_def` restates the defining formula, and `rsGlobalIntegral_zero_left` states that the integral vanishes when $\varphi$ is the zero function.
--
--   The module also contains a compatibility lemma, `iotaGL_transposeInvN`: for a commutative ring $A$ and $g \in \mathrm{GL}_2(A)$, the embedding `iotaGL` (induced by the matrix map `embedMat2`) intertwines the transpose-inverse involutions, $\iota({}^t g^{-1}) = {}^t(\iota g)^{-1}$, where `transposeInvN (Fin 2)` and `transposeInv3` are the maps $h \mapsto {}^t(h^{-1})$ in sizes $2$ and $3$.
--
--   **Relation to Mathlib.** Mathlib has no Rankin–Selberg integrals, nor Haar measure on adelic $\mathrm{GL}_n$; the measure, the embedding of adelic $\mathrm{GL}_2$ into adelic $\mathrm{GL}_3$ and the idele norm are the project's own, while the integral itself is Mathlib's Bochner integral with Mathlib's complex power.
--
--   **Where it is used.** The integral is the global object of the Rankin–Selberg theory used in the Langlands–Tunnell input to the argument: for $D$ a fundamental domain for $\mathrm{GL}_2(\mathbb{Q})$ and $\varphi$, $\Theta$ cusp forms on $\mathrm{GL}_2$ and $\mathrm{GL}_3$, it represents the $\mathrm{GL}_2\times\mathrm{GL}_3$ convolution $L$-function whose analytic properties feed the converse theorem. The transpose-inverse compatibility is what lets the dual (contragredient) side of the functional equation be compared with the original one.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_LanglandsTunnell_RSGlobalIntegral.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_AutomorphicForm_SmoothingKernel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Matrix IsDedekindDomain NumberField MeasureTheory

noncomputable section

namespace LanglandsTunnell.RankinSelberg

open LanglandsTunnell.CubicInduction AutomorphicForm

theorem iotaGL_transposeInvN {A : Type*} [CommRing A] (g : GL (Fin 2) A) :
    iotaGL (transposeInvN (Fin 2) g) = transposeInv3 (iotaGL g) := by
  refine Units.ext ?_
  change embedMat2 _ = (((iotaGL g)⁻¹ : GL (Fin 3) A) : Matrix (Fin 3) (Fin 3) A)ᵀ
  rw [← map_inv, coe_iotaGL, coe_transposeInvN]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [embedMat2, Matrix.transpose_apply]

attribute [local instance] NumberField.AdelicHaar.glBorel
attribute [local instance] NumberField.AdelicHaar.borelSpace_glBorel

def rsGlobalIntegral (D : Set (AdelicGL2 (𝓞 ℚ) ℚ)) (s : ℂ) (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (Θ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) : ℂ :=
  ∫ g in D, φ g * Θ (iota (𝓞 ℚ) ℚ g) * ((detNorm g : ℝ) : ℂ) ^ (s - 1 / 2)
    ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ)

theorem rsGlobalIntegral_def (D : Set (AdelicGL2 (𝓞 ℚ) ℚ)) (s : ℂ) (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
    (Θ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) :
    rsGlobalIntegral D s φ Θ =
      ∫ g in D, φ g * Θ (iota (𝓞 ℚ) ℚ g) * ((detNorm g : ℝ) : ℂ) ^ (s - 1 / 2)
        ∂(NumberField.AdelicHaar.adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ) := rfl

@[simp] theorem rsGlobalIntegral_zero_left (D : Set (AdelicGL2 (𝓞 ℚ) ℚ)) (s : ℂ)
    (Θ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) : rsGlobalIntegral D s 0 Θ = 0 := by
  simp [rsGlobalIntegral]

end LanglandsTunnell.RankinSelberg

end


