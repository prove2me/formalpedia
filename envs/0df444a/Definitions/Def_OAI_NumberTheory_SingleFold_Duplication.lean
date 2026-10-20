-- Prove2me | Definitions.Def_OAI_NumberTheory_SingleFold_Duplication
-- name    : OAI_NumberTheory_SingleFold_Duplication
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T16:19:35.866312+00:00
-- url     : https://prove2.me/theorems/94622b59-36cb-48c0-a9e3-ffa80b9d246c
-- title:
--   Height of a rational number and the duplication formula
-- statement:
--   1. The height of a rational number $x$ is $\max(|\mathrm{num}(x)|,\mathrm{den}(x))$, computed from the reduced fraction.
--   2. The duplication map for $y^2=x^3-25x$ is
--   $$
--   \mathrm{dup}(x)=\frac{(x^2+25)^2}{4x(x^2-25)} ,
--   $$
--      the $x$-coordinate of $2P$ when $x(P)=x$ and $P$ is not $2$-torsion.
--
--   Comparing the height of $\mathrm{dup}(x)$ with that of $x$ shows that heights roughly get raised to the fourth power under doubling.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/SingleFold/Duplication.lean

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/SingleFold/Duplication.lean by skeleton subtraction
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

namespace OAI

namespace SingleFold.DuplicationBound

def height (x : ℚ) : ℕ := max x.num.natAbs x.den

def dupX (x : ℚ) : ℚ := (x^2+25)^2/(4*x*(x^2-25))

end SingleFold.DuplicationBound

end OAI


