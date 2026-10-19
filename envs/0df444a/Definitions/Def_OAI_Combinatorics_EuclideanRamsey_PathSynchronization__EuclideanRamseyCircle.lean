-- Prove2me | Definitions.Def_OAI_Combinatorics_EuclideanRamsey_PathSynchronization__EuclideanRamseyCircle
-- name    : OAI_Combinatorics_EuclideanRamsey_PathSynchronization__EuclideanRamseyCircle
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T12:03:12.354219+00:00
-- url     : https://prove2.me/theorems/ee3f4cf5-9af2-46e3-9c53-e898d5b01ea6
-- title:
--   Scaling endomorphism of the free group on the points of a Euclidean space
-- statement:
--   Let $E$ be the real inner product space of finitely supported real sequences $x=(x_0,x_1,x_2,\dots)$ (all but finitely many $x_n$ vanish), with $\langle x,y\rangle=\sum_{n\ge 0}x_ny_n$ and $\|x\|=\langle x,x\rangle^{1/2}$; it contains an isometric copy of every Euclidean space $\mathbb{R}^d$. Let $\Gamma$ be the free group on the set $E$ (the *letter group*); the generator belonging to a point $z\in E$ is written $[z]$. For a real number $c$, the *scaling endomorphism* $\sigma_c:\Gamma\to\Gamma$ is the group homomorphism induced by the map $z\mapsto\sqrt{c}\,z$ on generators:
--   $$\sigma_c\bigl([z_1]^{\epsilon_1}[z_2]^{\epsilon_2}\cdots[z_k]^{\epsilon_k}\bigr)=[\sqrt{c}\,z_1]^{\epsilon_1}[\sqrt{c}\,z_2]^{\epsilon_2}\cdots[\sqrt{c}\,z_k]^{\epsilon_k}\qquad(z_1,\dots,z_k\in E,\ \epsilon_1,\dots,\epsilon_k\in\{1,-1\}).$$
--
--   Scaling a family of points by $\sqrt c$ multiplies all squared distances by $c$. Applied coordinatewise to a tuple of words, $\sigma_c$ therefore turns a weighted path of weight $\lambda$ (a product of constant tuples and of letter tuples of scaled congruent copies of a fixed configuration, the weight being the sum of the squared scale factors) into a path of weight $c\lambda$, for every $c\ge 0$. This rescaling is the tool used to synchronize paths: from one tuple of words that carries two paths of weights $\lambda>0$ and $\mu$ with $\mu/\lambda<1/n$, one obtains a single tuple that carries paths of every weight $1/t$ with $1\le t\le n$.
--
--   **Formalization Note** `scaleGroup c` is `FreeGroup.map (fun z => Real.sqrt c • z)` on `LetterGroup = FreeGroup FiniteEuclidean`, with `FiniteEuclidean = ℕ →₀ ℝ`. Since `Real.sqrt` returns $0$ on negative inputs, for $c<0$ every generator is sent to $[0]$; the lemmas that use $\sigma_c$ assume $c\ge 0$. The configuration variable of the enclosing section is not an argument of this definition.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/EuclideanRamsey/PathSynchronization.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/EuclideanRamsey/PathSynchronization.lean by skeleton subtraction
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

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uIndex uAlpha

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

namespace EuclideanRamsey
open scoped BigOperators
variable {ι : Type uIndex} {a : ι → FiniteEuclidean}

def scaleGroup (c : ℝ) : LetterGroup →* LetterGroup := FreeGroup.map (fun z => Real.sqrt c • z)
end EuclideanRamsey

end

end OAI


