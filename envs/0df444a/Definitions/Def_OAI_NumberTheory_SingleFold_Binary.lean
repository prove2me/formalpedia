-- Prove2me | Definitions.Def_OAI_NumberTheory_SingleFold_Binary
-- name    : OAI_NumberTheory_SingleFold_Binary
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T16:30:24.571172+00:00
-- url     : https://prove2.me/theorems/ae40575b-37b9-46bd-9e79-ab8e6e6ab817
-- title:
--   Binary digit domination and its arithmetic encoding
-- statement:
--   1. For $x,y\in\mathbb{N}$, $x\preceq y$ means every binary digit of $x$ is at most the corresponding digit of $y$:
--   $$
--   \lfloor x/2^i\rfloor\bmod2\le\lfloor y/2^i\rfloor\bmod2\quad\text{for all }i .
--   $$
--   2. The system for $w=(B,H,N,s,d,r,t)\in\mathbb{N}^7$ requires $x\le y$, $B=2^{y+1}$, $H=B^x$, $N=(B+1)^y$, and
--   $$
--   N=sBH+dH+r,\qquad d<B,\quad r<H,\quad d=2t+1 .
--   $$
--
--   The system says that the base-$B$ digit of $(B+1)^y$ at position $x$, which is $\binom yx$, is odd. By Lucas' theorem this is equivalent to the binary domination of $x$ by $y$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/SingleFold/Binary.lean

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/SingleFold/Binary.lean by skeleton subtraction
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
import Definitions.Def_OAI_NumberTheory_SingleFold_Pell
import Definitions.Def_OAI_NumberTheory_SingleFold_Power

namespace OAI

namespace SingleFold.Binary

def Bits (x y : ℕ) : Prop := ∀ i, x/2^i%2 ≤ y/2^i%2

def System (x y : ℕ) (w : Fin 7 → ℕ) : Prop :=
  let B:=w 0; let H:=w 1; let N:=w 2; let s:=w 3; let d:=w 4; let r:=w 5; let t:=w 6
  x≤y ∧ B=2^(y+1) ∧ H=B^x ∧ N=(B+1)^y ∧
    N=s*B*H+d*H+r ∧ d<B ∧ r<H ∧ d=2*t+1

end SingleFold.Binary

namespace SingleFold.Compiler.MapSF
end SingleFold.Compiler.MapSF

namespace SingleFold.Compiler.ScalarSF
variable {α : Type} {f g h : (α → ℕ) → ℕ}
end SingleFold.Compiler.ScalarSF

namespace SingleFold.Binary
open Compiler
end SingleFold.Binary

end OAI


