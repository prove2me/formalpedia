-- Prove2me | Definitions.Def_OAI_Combinatorics_CliqueFree_Numerical
-- name    : OAI_Combinatorics_CliqueFree_Numerical
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T20:40:50.754102+00:00
-- url     : https://prove2.me/theorems/d020718e-1e07-4aa9-9e69-54f94637bdf7
-- title:
--   Mass threshold, logarithmic loss ratio and iterated-squaring scales
-- statement:
--   This file fixes three elementary real functions that serve as numerical parameters in a weighted-graph proof of a logarithmic independence bound for clique-free graphs. Throughout, $\log$ is the natural logarithm and $x,X$ are real numbers.
--
--   1. **Mass threshold.** For $x\in\mathbb{R}$,
--
--      $$\theta(x)=\frac{1}{e^{x}\,x^{6}} .$$
--
--   2. **Loss ratio.** For $x\in\mathbb{R}$,
--
--      $$\lambda(x)=\frac{\log x}{\sqrt{x}} .$$
--
--   3. **Iterated-squaring scales.** For $X\in\mathbb{R}$, the sequence $(X_n)_{n\ge 0}$ given by
--
--      $$X_0=X,\qquad X_{n+1}=X_n^{2}\quad(n\ge 0),$$
--
--      so that $X_n=X^{2^n}$.
--
--   The threshold $\theta(x)$ is the level of weighted neighbourhood mass at which a vertex is absorbed when a vertex set is enlarged in the localisation of a random walk inside neighbourhoods at scale $x$. The ratio $\lambda(x)$, which tends to $0$ as $x\to\infty$, measures the relative loss of weighted triangle mass in one vertex-splitting step; such a step lowers the logarithm of the largest weighted neighbourhood mass from $x$ to $\sqrt{x}$. The scales $X_n$ undo this square root, so an induction on $n$ treats weights whose neighbourhood masses are at most $e^{X_n}$, starting from the base scale $X$.
--
--   **Formalization Note** The functions are `threshold`, `lossRatio` and `scale X n`. Lean's conventions make them total: `threshold 0 = 0` because division by zero is zero, and `lossRatio x = 0` for $x\le 0$ because `Real.sqrt x = 0` there. These values play no role, since the functions are only evaluated at large positive arguments.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/CliqueFree/Numerical.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/CliqueFree/Numerical.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the CliqueFreeLog mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_CliqueFreeLog

namespace OAI

noncomputable section

open scoped BigOperators
open Finset

attribute [local instance] Classical.propDecidable

namespace CliqueFreeIndependence

universe u v

namespace Numerical

noncomputable def threshold (x : ℝ) : ℝ := 1 / (Real.exp x * x ^ 6)

end Numerical

end CliqueFreeIndependence

open Filter
namespace CliqueFreeIndependence.Numerical

def lossRatio (x : ℝ) : ℝ := Real.log x / Real.sqrt x

def scale (X : ℝ) : ℕ → ℝ
  | 0 => X
  | n+1 => (scale X n)^2

end CliqueFreeIndependence.Numerical

end

end OAI


