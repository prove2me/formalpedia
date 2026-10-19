-- Prove2me | Definitions.Def_OAI_Combinatorics_EuclideanRamsey_PathSynchronization
-- name    : OAI_Combinatorics_EuclideanRamsey_PathSynchronization
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T01:40:57.559998+00:00
-- url     : https://prove2.me/theorems/92f9f163-6bd1-4f02-97da-fb7c59abf7aa
-- title:
--   Scaling endomorphism of the free group on Euclidean points
-- statement:
--   Let $E_\infty$ denotes the real vector space of finitely supported real sequences $x=(x_0,x_1,x_2,\dots)$ with inner product $\langle x,y\rangle=\sum_n x_ny_n$ and norm $\|x\|=\langle x,x\rangle^{1/2}$, and let $\Gamma=F(E_\infty)$ be the free group whose generators $[z]$ are the points $z\in E_\infty$. For a real number $c$, the *scaling endomorphism* $\sigma_c:\Gamma\to\Gamma$ is the group homomorphism induced by the map $z\mapsto\sqrt c\,z$ on generators:
--   $$\sigma_c\bigl([z_1]^{\pm1}[z_2]^{\pm1}\cdots[z_k]^{\pm1}\bigr)=[\sqrt c\,z_1]^{\pm1}[\sqrt c\,z_2]^{\pm1}\cdots[\sqrt c\,z_k]^{\pm1}\qquad(z_1,\dots,z_k\in E_\infty).$$
--
--   Scaling a configuration by $\sqrt c$ multiplies all squared distances by $c$. Applied coordinatewise to a tuple of words, $\sigma_c$ therefore turns a weighted path of weight $\lambda$ (a product of letter tuples of scaled congruent copies of a fixed configuration) into a path of weight $c\lambda$, for every $c\ge 0$. This rescaling is the tool used to synchronize paths: from a single tuple of words carrying two paths of weights $\lambda>0$ and $\mu$ with $\mu/\lambda<1/n$, one obtains one tuple carrying paths of every weight $1/t$ with $1\le t\le n$.
--
--   **Formalization Note** `scaleGroup c` is `FreeGroup.map (fun z => Real.sqrt c • z)` on `LetterGroup = FreeGroup FiniteEuclidean`. Since `Real.sqrt` returns $0$ on negative inputs, for $c<0$ every generator is sent to $[0]$; the lemmas using $\sigma_c$ assume $c\ge 0$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/EuclideanRamsey/PathSynchronization.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/EuclideanRamsey/PathSynchronization.lean by skeleton subtraction
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


