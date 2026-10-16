-- Prove2me | Definitions.Def_OAI_Algebra_Determinantal_PointBounds
-- name    : OAI_Algebra_Determinantal_PointBounds
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T21:29:10.146984+00:00
-- url     : https://prove2.me/theorems/b04313fd-c194-4b1b-9c36-31948ea41a4a
-- title:
--   Simple zeros of a parametrized family of maps on a Banach space
-- statement:
--   Let $C$ and $V$ be complex Banach spaces and let $F:C\times V\to V$ be a map, viewed as a family of maps $x\mapsto F(c,x)$ on $V$ depending on a parameter $c\in C$. For $c\in C$ and $x\in V$, the family is *simple at* $(c,x)$ if the partial derivative of $F$ with respect to the $V$-variable at $(c,x)$,
--   $$
--   D_xF(c,x)=DF(c,x)\circ\iota_V,\qquad \iota_V:V\to C\times V,\quad \iota_V(v)=(0,v),
--   $$
--   is an invertible continuous linear operator on $V$, i.e. a continuous linear bijection $V\to V$ whose inverse is also continuous. Here $DF(c,x):C\times V\to V$ is the complex Fréchet derivative of $F$ at $(c,x)$. No condition $F(c,x)=0$ is part of the definition.
--
--   A zero $x$ of $F(c,\cdot)$ at which the family is simple is a nondegenerate zero. For continuously differentiable families such zeros persist, by the implicit function theorem, under small changes of the parameter and remain simple, and finitely many distinct simple zeros persist as distinct simple zeros. This is how counts of simple solutions of polynomial systems are transported along deformations of the system.
--
--   **Formalization Note** The definition is `PolarAnalysis.SimpleAt F c x`, stated as `(fderiv ℂ F (c,x) ∘L ContinuousLinearMap.inr ℂ C V).IsInvertible`. Since `fderiv` is $0$ at points where $F$ is not differentiable, at such points the condition holds only when $V$ is the zero space.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/Determinantal/PointBounds.lean

-- Generated from openai/math@1581d4c lean/OAI/Algebra/Determinantal/PointBounds.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the SmoothInitialForm mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_SmoothInitialForm
import Definitions.Def_OAI_Algebra_Determinantal_Multigraded
import Definitions.Def_OAI_Algebra_Determinantal_LinearForms

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace PermanentBorder.Multigraded
section AffineCokernel
variable {K V W : Type*} [Field K]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W] [Module.Finite K W]

end AffineCokernel
end PermanentBorder.Multigraded

namespace PermanentBorder.Multigraded
open MvPolynomial
section GenericPieceBound
variable {K σ G E : Type*} [Field K] [AddCommGroup G] [Fintype E]

end GenericPieceBound

section ProductComparison
variable {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]

end ProductComparison
end PermanentBorder.Multigraded

namespace PermanentBorder.Multigraded
open MvPolynomial
section BlockInterpolation
variable {K σ ι L : Type*} [Field K] [Fintype ι] [DecidableEq ι]
variable (group : σ → ι) (base : ι → σ) (hbase : ∀ j, group (base j) = j)

variable [Fintype L] [DecidableEq L]

end BlockInterpolation
end PermanentBorder.Multigraded

namespace PermanentBorder.Multigraded
open MvPolynomial
section NormalizedPointBound
variable {K σ ι L : Type*} [Field K] [Fintype σ] [Fintype ι] [DecidableEq ι]
  [Fintype L] [DecidableEq L]

end NormalizedPointBound
end PermanentBorder.Multigraded

namespace PermanentBorder.PolarAnalysis
open Filter
open scoped Topology

section Persistence
variable {C V : Type*}
  [NormedAddCommGroup C] [NormedSpace ℂ C] [CompleteSpace C]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]

def SimpleAt (F : C × V → V) (c : C) (x : V) : Prop :=
  (fderiv ℂ F (c,x) ∘L ContinuousLinearMap.inr ℂ C V).IsInvertible

end Persistence
end PermanentBorder.PolarAnalysis

namespace PermanentBorder.PolarAnalysis
end PermanentBorder.PolarAnalysis

namespace PermanentBorder.PolarAnalysis
open MvPolynomial
variable {τ : Type*} [Fintype τ]
end PermanentBorder.PolarAnalysis

namespace PermanentBorder.Multigraded
open MvPolynomial Filter
open scoped Topology
section ProductSimplePointBound
variable {ι L : Type*} [Fintype ι] [DecidableEq ι] [Fintype L] [DecidableEq L]

end ProductSimplePointBound
end PermanentBorder.Multigraded

end OAI


