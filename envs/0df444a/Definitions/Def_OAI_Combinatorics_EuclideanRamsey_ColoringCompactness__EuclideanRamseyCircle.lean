-- Prove2me | Definitions.Def_OAI_Combinatorics_EuclideanRamsey_ColoringCompactness__EuclideanRamseyCircle
-- name    : OAI_Combinatorics_EuclideanRamsey_ColoringCompactness__EuclideanRamseyCircle
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T12:12:07.947364+00:00
-- url     : https://prove2.me/theorems/b200184c-8268-42cf-8c9a-2f7010a2f5fe
-- title:
--   Colour of an ultrafilter under a finite colouring, and truncation of finitely supported sequences
-- statement:
--   1. **Every ultrafilter selects a colour.** Let $M$ be a set, $\kappa$ a finite set of colours and $c:M\to\kappa$ a colouring. For every ultrafilter $U$ on $M$ some colour class belongs to $U$: there is $k\in\kappa$ with
--   $$\{\,x\in M:\ c(x)=k\,\}\in U.$$
--   2. **Colour of an ultrafilter.** $\hat c(U)\in\kappa$ denotes a colour $k$ with the property of item 1, chosen once and for all. Since distinct colour classes are disjoint and an ultrafilter never contains two disjoint sets, this colour is in fact unique; $\hat c$ extends $c$ from points to ultrafilters, with $\hat c(\delta_x)=c(x)$ for the principal ultrafilter $\delta_x$ at $x$.
--   3. **Truncation.** Let $E$ be the real inner product space of finitely supported real sequences $x=(x_0,x_1,x_2,\dots)$ (all but finitely many $x_n$ vanish), with $\langle x,y\rangle=\sum_{n\ge 0}x_ny_n$ and $\|x\|=\langle x,x\rangle^{1/2}$; it contains an isometric copy of every Euclidean space $\mathbb{R}^d$. For $d\in\mathbb{N}$, the truncation $\mathrm{tr}_d:E\to\mathbb{R}^d$ keeps the first $d$ coordinates, $\mathrm{tr}_d(x)=(x_0,x_1,\dots,x_{d-1})$, regarded as a vector of the Euclidean space $\mathbb{R}^d$.
--
--   The colour of an ultrafilter turns a finite colouring of a set into a colouring of the ultrafilters on that set. It is used twice in the construction of monochromatic congruent copies: to transport a finite colouring of strings of points to products of ultrafilters, where a Hales–Jewett argument produces a monochromatic configuration, and in the compactness step, with ultrafilters on $\mathbb{N}$, to combine a sequence of colourings of the spaces $\mathbb{R}^{n+1}$ into a single colouring of $E$. Truncation is the other ingredient of the compactness step: a point of $E$ is recovered from its truncation as soon as $d$ exceeds the indices of its nonzero coordinates, so monochromatic congruent copies found in $E$ can be pulled back to a finite-dimensional space $\mathbb{R}^D$.
--
--   **Formalization Note** `exists_ultra_color` is the existence statement of item 1 (with `[Finite κ]`), and `ultraColor c U` chooses the colour with `Exists.choose`. `FiniteEuclidean.truncate d x` is `WithLp.toLp 2 (fun i => coords x i)` with `i : Fin d`, an element of `EuclideanSpace ℝ (Fin d)`, where `FiniteEuclidean = ℕ →₀ ℝ`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/EuclideanRamsey/ColoringCompactness.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/EuclideanRamsey/ColoringCompactness.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the EuclideanRamseyCircle mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_EuclideanRamseyCircle
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Model__EuclideanRamseyCircle
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_CircleInterpolation
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_CircleRows
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_CircleExtension
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorNecessity__EuclideanRamseyCircle
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorDescent__EuclideanRamseyCircle
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SmoothingKernel__EuclideanRamseyCircle
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Hessian__EuclideanRamseyCircle
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_DifferentialSplitting__EuclideanRamseyCircle
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SmoothingMatrix__EuclideanRamseyCircle
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_LatticeMoments__EuclideanRamseyCircle
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Discretization__EuclideanRamseyCircle
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_AdicLifting__EuclideanRamseyCircle
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorPresentation__EuclideanRamseyCircle
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SignedRows__EuclideanRamseyCircle
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_FiniteEuclidean__EuclideanRamseyCircle
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_PathFractions__EuclideanRamseyCircle
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_DerivedFractions__EuclideanRamseyCircle
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_PathWords__EuclideanRamseyCircle
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_UltrafilterStrings__EuclideanRamseyCircle
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_PathSynchronization__EuclideanRamseyCircle
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_CornerGroup__EuclideanRamseyCircle

namespace OAI

universe uModule uColor

noncomputable section

open scoped TensorProduct RealInnerProductSpace
open scoped BigOperators
open Real Filter Topology MeasureTheory Polynomial
open Matrix MeasureTheory
open MeasureTheory
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator
open MeasureTheory Matrix
open scoped TensorProduct
open scoped BigOperators Pointwise Topology
open MeasureTheory Filter
open scoped BigOperators Pointwise
open scoped BigOperators Topology
open scoped TensorProduct BigOperators
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator
open scoped BigOperators RealInnerProductSpace
open Filter
open Set

namespace EuclideanRamsey
open Filter
open scoped BigOperators
attribute [local instance] Ultrafilter.mul Ultrafilter.semigroup

lemma exists_ultra_color {M : Type uModule} {κ : Type uColor} [Finite κ] (U : Ultrafilter M) (c : M → κ) :
    ∃ k,{x | c x=k}∈U := by
  apply Ultrafilter.eventually_exists_iff.mp
  exact Filter.Eventually.of_forall (fun x => ⟨c x,rfl⟩)
noncomputable def ultraColor {M : Type uModule} {κ : Type uColor} [Finite κ] (c : M → κ) (U : Ultrafilter M) : κ :=
  (exists_ultra_color U c).choose
end EuclideanRamsey
namespace EuclideanRamsey
namespace FiniteEuclidean
open Filter
open scoped BigOperators
noncomputable def truncate (d : ℕ) (x : FiniteEuclidean) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (fun i => coords x i)

end FiniteEuclidean

end EuclideanRamsey

end

end OAI


