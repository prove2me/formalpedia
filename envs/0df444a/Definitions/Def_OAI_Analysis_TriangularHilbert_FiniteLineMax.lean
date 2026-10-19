-- Prove2me | Definitions.Def_OAI_Analysis_TriangularHilbert_FiniteLineMax
-- name    : OAI_Analysis_TriangularHilbert_FiniteLineMax
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T00:13:44.392739+00:00
-- url     : https://prove2.me/theorems/0d951779-961b-4bee-935a-c4a9bb6396a6
-- title:
--   Maximal function of a function on a finite line
-- statement:
--   Let $D\subset\mathbb Z$ be finite and let $f$ be a real function on $D$.
--
--   1. **Extension.** $\mathrm{lineExtend}(D,f)(n)=f(n)$ for $n\in D$ and $0$ otherwise.
--   2. **Line maximal function.**
--   $$
--   \mathrm{lineMax}(D,f,n)=\mathrm{intMax}\bigl(D,\mathrm{lineExtend}(D,f),n\bigr),
--   $$
--   the centred discrete Hardy–Littlewood maximal function of the zero extension, evaluated at any integer $n$.
--
--   This form is convenient for functions defined on the finite grid of a sampled problem.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/TriangularHilbert/FiniteLineMax.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/TriangularHilbert/FiniteLineMax.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the TriangularHilbert mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_TriangularHilbert
import Definitions.Def_OAI_Analysis_TriangularHilbert_Gaussian
import Definitions.Def_OAI_Analysis_TriangularHilbert_MeshMass
import Definitions.Def_OAI_Analysis_TriangularHilbert_GaussianMoments
import Definitions.Def_OAI_Analysis_TriangularHilbert_SignedWindowScalar
import Definitions.Def_OAI_Analysis_TriangularHilbert_MatrixSupport
import Definitions.Def_OAI_Analysis_TriangularHilbert_Support
import Definitions.Def_OAI_Analysis_TriangularHilbert_WeightedGram
import Definitions.Def_OAI_Analysis_TriangularHilbert_WeightedStar
import Definitions.Def_OAI_Analysis_TriangularHilbert_GroupedGaussian
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatStar
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatCost
import Definitions.Def_OAI_Analysis_TriangularHilbert_NormBounds
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatInsert
import Definitions.Def_OAI_Analysis_TriangularHilbert_GaussianDom
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneChart
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneDom
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatBound
import Definitions.Def_OAI_Analysis_TriangularHilbert_GramDeriv
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneIntegral
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneDissipation
import Definitions.Def_OAI_Analysis_TriangularHilbert_SignedTraceOrder
import Definitions.Def_OAI_Analysis_TriangularHilbert_MassPlane
import Definitions.Def_OAI_Analysis_TriangularHilbert_SignedConvolution
import Definitions.Def_OAI_Analysis_TriangularHilbert_RankJump
import Definitions.Def_OAI_Analysis_TriangularHilbert_ZeroStar
import Definitions.Def_OAI_Analysis_TriangularHilbert_StarJump
import Definitions.Def_OAI_Analysis_TriangularHilbert_InitialAlgebra
import Definitions.Def_OAI_Analysis_TriangularHilbert_InitialPlane
import Definitions.Def_OAI_Analysis_TriangularHilbert_TotalJump
import Definitions.Def_OAI_Analysis_TriangularHilbert_IntWeak
import Definitions.Def_OAI_Analysis_TriangularHilbert_StrongLayer
import Definitions.Def_OAI_Analysis_TriangularHilbert_IntMax

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uκ

section
namespace TriangularHilbert
open scoped BigOperators
noncomputable section

def lineExtend (D : Finset ℤ) (f : D → ℝ) (n : ℤ) : ℝ :=
  if hn : n ∈ D then f ⟨n,hn⟩ else 0

def lineMax (D : Finset ℤ) (f : D → ℝ) (n : ℤ) : ℝ := intMax D (lineExtend D f) n

end
end TriangularHilbert
end

end OAI


