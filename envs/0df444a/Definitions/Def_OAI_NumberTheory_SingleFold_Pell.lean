-- Prove2me | Definitions.Def_OAI_NumberTheory_SingleFold_Pell
-- name    : OAI_NumberTheory_SingleFold_Pell
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T16:25:56.999575+00:00
-- url     : https://prove2.me/theorems/3c2c84b9-70a7-4ea4-a90f-7de2f714a544
-- title:
--   Growth ratio of Pell solutions
-- statement:
--   For an integer $a>1$ let $(x_n,y_n)$ be the solutions of the Pell equation $x^2-(a^2-1)y^2=1$, indexed so that $x_n+y_n\sqrt{a^2-1}=(a+\sqrt{a^2-1})^n$. The ratio of consecutive $y$-values is
--   $$
--   \rho_n=\frac{y_{n+2}}{y_{n+1}} .
--   $$
--
--   These ratios approach $a+\sqrt{a^2-1}$. They control how fast $y_n$ grows, which is needed to compute powers through Pell equations.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/SingleFold/Pell.lean

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/SingleFold/Pell.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the SingleFold mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_SingleFold
import Definitions.Def_OAI_NumberTheory_SingleFold_PolynomialCompiler
import Definitions.Def_OAI_NumberTheory_SingleFold_RationalCodes
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticCoordinates
import Definitions.Def_OAI_NumberTheory_SingleFold_FunctionalCompiler
import Definitions.Def_OAI_NumberTheory_SingleFold_DescentMap
import Definitions.Def_OAI_NumberTheory_SingleFold_SquareSupport
import Definitions.Def_OAI_NumberTheory_SingleFold_LocalDescent
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticHeight
import Definitions.Def_OAI_NumberTheory_SingleFold_QuadraticHeight
import Definitions.Def_OAI_NumberTheory_SingleFold_FiniteGeneration
import Definitions.Def_OAI_NumberTheory_SingleFold_Rank
import Definitions.Def_OAI_NumberTheory_SingleFold_Duplication
import Definitions.Def_OAI_NumberTheory_SingleFold_Torsion
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticGrowth

namespace OAI

namespace SingleFold.PellPower

variable {a : ℕ} (ha : 1 < a)

noncomputable def rate (n : ℕ) : ℝ := (Pell.yn ha (n+2):ℝ)/Pell.yn ha (n+1)

end SingleFold.PellPower

namespace SingleFold.PellAnalytics
end SingleFold.PellAnalytics

namespace SingleFold.PellSystem
end SingleFold.PellSystem

end OAI


