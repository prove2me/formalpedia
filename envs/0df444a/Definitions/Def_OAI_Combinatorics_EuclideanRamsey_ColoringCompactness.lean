-- Prove2me | Definitions.Def_OAI_Combinatorics_EuclideanRamsey_ColoringCompactness
-- name    : OAI_Combinatorics_EuclideanRamsey_ColoringCompactness
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T01:44:57.204985+00:00
-- url     : https://prove2.me/theorems/55a32f6c-0562-4ba0-b55c-8d46440774b3
-- title:
--   Colour of an ultrafilter under a finite colouring, and truncation of finitely supported sequences
-- statement:
--   1. **Every ultrafilter selects a colour.** Let $M$ be a set, $\kappa$ a finite set of colours and $c:M\to\kappa$ a colouring. For every ultrafilter $U$ on $M$ some colour class belongs to $U$: there is $k\in\kappa$ with
--   $$\{x\in M:\ c(x)=k\}\in U.$$
--   2. **Colour of an ultrafilter.** $\hat c(U)\in\kappa$ is a colour $k$ with this property. Since distinct colour classes are disjoint and an ultrafilter contains no two disjoint sets, this colour is unique, so $\hat c$ is the natural extension of $c$ from points to ultrafilters (in particular $\hat c(\delta_x)=c(x)$ for the principal ultrafilter $\delta_x$).
--   3. **Truncation.** Let $E_\infty$ denotes the real vector space of finitely supported real sequences $x=(x_0,x_1,x_2,\dots)$ with inner product $\langle x,y\rangle=\sum_n x_ny_n$ and norm $\|x\|=\langle x,x\rangle^{1/2}$. For $d\in\mathbb{N}$, the truncation $\mathrm{tr}_d:E_\infty\to\mathbb{R}^d$ keeps the first $d$ coordinates, $\mathrm{tr}_d(x)=(x_0,\dots,x_{d-1})$, as a vector of Euclidean space $\mathbb{R}^d$.
--
--   The colour of an ultrafilter transports a finite colouring of strings of points to a colouring of the ultrafilter semigroup, where idempotent arguments produce monochromatic configurations. Truncation is used in the compactness step: every point of $E_\infty$ is recovered from its truncation once $d$ exceeds its support, which allows one to pass from monochromatic congruent copies in $E_\infty$ for all finite colourings to a single finite dimension $D$ that works for every $r$-colouring of $\mathbb{R}^D$.
--
--   **Formalization Note** `exists_ultra_color` is the existence lemma of item 1 (with `[Finite κ]`), and `ultraColor c U` chooses the colour with `Exists.choose`. `FiniteEuclidean.truncate d x` is `WithLp.toLp 2 (fun i => coords x i)` with `i : Fin d`, an element of `EuclideanSpace ℝ (Fin d)`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/EuclideanRamsey/ColoringCompactness.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/EuclideanRamsey/ColoringCompactness.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the EuclideanRamsey mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_EuclideanRamsey
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorNecessity
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorDescent
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SmoothingKernel
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Hessian
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_DifferentialSplitting
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SmoothingMatrix
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_LatticeMoments
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Discretization
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_AdicLifting
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorPresentation
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SignedRows
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_FiniteEuclidean
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_PathFractions
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_DerivedFractions
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_PathWords
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_UltrafilterStrings
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_PathSynchronization
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_CornerGroup

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


