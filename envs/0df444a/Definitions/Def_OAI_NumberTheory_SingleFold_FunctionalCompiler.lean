-- Prove2me | Definitions.Def_OAI_NumberTheory_SingleFold_FunctionalCompiler
-- name    : OAI_NumberTheory_SingleFold_FunctionalCompiler
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T16:05:30.472323+00:00
-- url     : https://prove2.me/theorems/9b3ccbd1-de00-4990-a325-f1bc89e1bec3
-- title:
--   Functions with single-fold graphs
-- statement:
--   1. A map $f:\mathbb{N}^\alpha\to\mathbb{N}^\beta$ is **map-SF** if its graph
--   $$
--   \{(x,y)\in\mathbb{N}^\alpha\times\mathbb{N}^\beta:\ y=f(x)\}
--   $$
--      is SF, i.e. has a single-fold Diophantine representation.
--   2. A point-valued map $f:\mathbb{N}^\alpha\to E(\mathbb{Q})$, where $E:y^2=x^3-25x$, is **point-SF** if $x\mapsto$ (natural coordinates of the canonical code of $f(x)$) is map-SF.
--   3. A scalar map $f:\mathbb{N}^\alpha\to\mathbb{N}$ is **scalar-SF** if its graph is SF.
--   4. A point code decodes to its point when it is valid, and to $O$ otherwise.
--
--   Functional representability composes. It lets the compiler build representations of point arithmetic from those of its pieces.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/SingleFold/FunctionalCompiler.lean

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/SingleFold/FunctionalCompiler.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the SingleFold mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_SingleFold
import Definitions.Def_OAI_NumberTheory_SingleFold_PolynomialCompiler
import Definitions.Def_OAI_NumberTheory_SingleFold_RationalCodes
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticCoordinates

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace SingleFold.Compiler

def MapSF {α β : Type} (f : (α → ℕ) → (β → ℕ)) : Prop :=
  SF (fun z : α ⊕ β → ℕ => z ∘ Sum.inr=f (z ∘ Sum.inl))
namespace MapSF
variable {α β γ δ : Type}
end MapSF
end SingleFold.Compiler

namespace SingleFold.PointCompiler
open Compiler RationalCompiler
noncomputable def Code.decode (a : Code) : E.Point := by
  classical
  exact if h : a.Valid then a.toPoint h else 0
def PointSF {α : Type} (f : (α → ℕ) → E.Point) : Prop := MapSF (fun z => tuple (encode (f z)))
namespace PointSF
variable {α β : Type} {f g : (α → ℕ) → E.Point}
end PointSF
end SingleFold.PointCompiler

namespace SingleFold.Compiler
def ScalarSF {α : Type} (f : (α → ℕ) → ℕ) : Prop := MapSF (fun z (_ : Unit) => f z)
namespace ScalarSF
variable {α : Type} {f g : (α → ℕ) → ℕ}
end ScalarSF
end SingleFold.Compiler

namespace SingleFold.PointCompiler
open Compiler RationalCompiler
namespace PointSF
variable {α : Type} {f g : (α → ℕ) → E.Point}
end PointSF
end SingleFold.PointCompiler

end OAI


