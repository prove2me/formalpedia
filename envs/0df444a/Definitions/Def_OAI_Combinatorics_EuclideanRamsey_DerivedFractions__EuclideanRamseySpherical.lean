-- Prove2me | Definitions.Def_OAI_Combinatorics_EuclideanRamsey_DerivedFractions__EuclideanRamseySpherical
-- name    : OAI_Combinatorics_EuclideanRamsey_DerivedFractions__EuclideanRamseySpherical
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T06:11:35.642226+00:00
-- url     : https://prove2.me/theorems/e4a848ed-49eb-4cc9-bea8-b052e7546877
-- title:
--   Derived series and the augmentation kernel of a free group
-- statement:
--   A finite configuration $a=(a_0,\dots,a_{s-1})$ of points of $\mathbb R^d$ is Ramsey when, for every number of colours $r$, some dimension $D$ has the property that every $r$-colouring of $\mathbb R^D$ contains a monochromatic copy of $a$ congruent to it. This module is part of the proof that Ramsey configurations lie on a sphere.
--
--   1. **Derived series.** For a subgroup $N$ of a group $G$, the subgroups $N^{(0)}=N$ and $N^{(n+1)}=[N^{(n)},N^{(n)}]$. If $N$ is normal, every $N^{(n)}$ is normal.
--   2. **Augmentation of a free group.** For a set $X$, the homomorphism from the free group $F(X)$ to $\mathbb Z$ that sends every generator to $1$, so a word maps to the sum of its exponents:
--   $$
--   \varepsilon\bigl(x_1^{n_1}\cdots x_r^{n_r}\bigr)=n_1+\dots+n_r .
--   $$
--   3. **Augmentation kernel.** The kernel of $\varepsilon$, a normal subgroup of $F(X)$ consisting of the words with total exponent $0$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/EuclideanRamsey/DerivedFractions.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/EuclideanRamsey/DerivedFractions.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the EuclideanRamseySpherical mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_EuclideanRamseySpherical
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorNecessity__EuclideanRamseySpherical
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Hessian__EuclideanRamseySpherical
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_DifferentialSplitting__EuclideanRamseySpherical
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_LatticeMoments__EuclideanRamseySpherical
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_AdicLifting__EuclideanRamseySpherical
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorPresentation__EuclideanRamseySpherical
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_FiniteEuclidean__EuclideanRamseySpherical
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_PathFractions__EuclideanRamseySpherical

namespace OAI

universe uGroup uIndex uColor uPoint

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

namespace EuclideanRamsey
open scoped commutatorElement
variable {G : Type uGroup} [Group G]

def Derived (N : Subgroup G) : ℕ → Subgroup G
  | 0 => N
  | n+1 => ⁅Derived N n,Derived N n⁆
instance derived_normal (N : Subgroup G) [N.Normal] (n : ℕ) : (Derived N n).Normal := by
  induction n with
  | zero => exact inferInstanceAs N.Normal
  | succ n ih => exact Subgroup.commutator_normal _ _
end EuclideanRamsey

namespace EuclideanRamsey
variable {X : Type uPoint} {G : Type uGroup} [Group G]
def freeAugmentation (X : Type uPoint) : FreeGroup X →* Multiplicative ℤ :=
  FreeGroup.lift (fun _ => Multiplicative.ofAdd 1)
def AugKernel (X : Type uPoint) : Subgroup (FreeGroup X) := (freeAugmentation X).ker
instance (X : Type uPoint) : (AugKernel X).Normal := inferInstanceAs (freeAugmentation X).ker.Normal
end EuclideanRamsey

end

end OAI


