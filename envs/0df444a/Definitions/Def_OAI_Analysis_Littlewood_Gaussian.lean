-- Prove2me | Definitions.Def_OAI_Analysis_Littlewood_Gaussian
-- name    : OAI_Analysis_Littlewood_Gaussian
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T03:56:31.13666+00:00
-- url     : https://prove2.me/theorems/136da34b-4268-41aa-9596-181b0570e483
-- title:
--   The unit-modulus phase $x \mapsto e^{ix}$ on the real line
-- statement:
--   This file introduces the basic phase function used throughout the construction of flat Littlewood polynomials. For a real number $x$, the **real phase** is the complex number
--   $$
--   \operatorname{ph}(x)=e^{ix}=\exp(i x)\in\mathbb{C}.
--   $$
--   Two elementary identities are recorded with it: $|\operatorname{ph}(x)|=1$ for every $x\in\mathbb{R}$, and $\operatorname{ph}(x+y)=\operatorname{ph}(x)\operatorname{ph}(y)$ for all $x,y\in\mathbb{R}$.
--
--   All oscillatory factors of the surrounding analysis are written through this function: the additive character $e(\theta)=e^{2\pi i\theta}$ is $\operatorname{ph}(2\pi\theta)$, a point of the unit circle can be written as $\operatorname{ph}(2\pi t)$ with $t\in[0,1]$, and quadratic chirps such as $\operatorname{ph}(\pi t x^2-2\pi u x)$ occur in the stationary-phase identities for Schwartz functions. The two identities allow one to remove unimodular factors from norms and to split the phase of a sum into a product.
--
--   **Formalization Note** `realPhase x` is defined as `Complex.exp (Complex.I * (x : ℂ))`; `norm_realPhase` and `realPhase_add` are the two identities above, registered as simp lemmas.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Littlewood/Gaussian.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Littlewood/Gaussian.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the AsymptoticallyMinimalLittlewood mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_AsymptoticallyMinimalLittlewood

namespace OAI

namespace AsymptoticallyMinimalLittlewood
noncomputable section

open MeasureTheory Complex Real FourierTransform Filter Topology
open scoped FourierTransform SchwartzMap ContDiff

def realPhase (x : ℝ) : ℂ := Complex.exp (Complex.I * (x : ℂ))

@[simp] theorem norm_realPhase (x : ℝ) : ‖realPhase x‖ = 1 := by
  simp [realPhase, Complex.norm_exp, Complex.mul_re]

@[simp] theorem realPhase_add (x y : ℝ) :
    realPhase (x + y) = realPhase x * realPhase y := by
  simp [realPhase, Complex.ofReal_add, mul_add, Complex.exp_add]

end
end AsymptoticallyMinimalLittlewood

end OAI


