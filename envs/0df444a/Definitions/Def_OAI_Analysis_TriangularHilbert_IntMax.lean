-- Prove2me | Definitions.Def_OAI_Analysis_TriangularHilbert_IntMax
-- name    : OAI_Analysis_TriangularHilbert_IntMax
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T00:12:27.813822+00:00
-- url     : https://prove2.me/theorems/0981c519-3c10-4c94-ba88-b50128fd0b07
-- title:
--   Discrete Hardy–Littlewood maximal function on a finite set of integers
-- statement:
--   Let $D\subset\mathbb Z$ be finite and $f:\mathbb Z\to\mathbb R$.
--
--   1. **Support radius.** $\mathrm{supportRadius}(D,n)=\max_{m\in D}|m-n|$.
--   2. **Averages.** $\mathrm{intAverage}(D,f,n,r)=\dfrac1{2r+1}\sum_{m\in D,\,|m-n|\le r}f(m)$.
--   3. **Maximal function.**
--   $$
--   \mathrm{intMax}(D,f,n)=\max_{0\le r\le\mathrm{supportRadius}(D,n)}\mathrm{intAverage}(D,f,n,r).
--   $$
--   Radii beyond the support radius only lower the average of a nonnegative function, so this finite maximum is the centred discrete maximal function of $f\mathbf 1_D$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/TriangularHilbert/IntMax.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/TriangularHilbert/IntMax.lean by skeleton subtraction
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

namespace OAI

section
namespace TriangularHilbert
open scoped BigOperators
noncomputable section

def supportRadius (D : Finset ℤ) (n : ℤ) : ℕ := D.sup (fun m => (m-n).natAbs)

def intAverage (D : Finset ℤ) (f : ℤ → ℝ) (n : ℤ) (r : ℕ) : ℝ :=
  (∑ m ∈ D ∩ intInterval n r, f m)/(2*(r:ℝ)+1)

def intMax (D : Finset ℤ) (f : ℤ → ℝ) (n : ℤ) : ℝ :=
  (Finset.range (supportRadius D n+1)).sup' (by exact ⟨0,Finset.mem_range.mpr (Nat.zero_lt_succ _)⟩) (intAverage D f n)

end
end TriangularHilbert
end

end OAI


