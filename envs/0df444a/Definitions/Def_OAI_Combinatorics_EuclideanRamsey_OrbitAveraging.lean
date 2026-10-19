-- Prove2me | Definitions.Def_OAI_Combinatorics_EuclideanRamsey_OrbitAveraging
-- name    : OAI_Combinatorics_EuclideanRamsey_OrbitAveraging
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T01:49:45.367979+00:00
-- url     : https://prove2.me/theorems/a6202845-fc20-4189-abc9-5d7eafb3b1dd
-- title:
--   Orbit words, orbit-wise bounds and averaging evolutions of group-valued functions
-- statement:
--   Let $G$ and $H$ be groups with $H$ acting on a set $X$, and consider functions $w:X\to G$, multiplied pointwise.
--
--   1. **Orbit words.** For a letter map $\ell:X\to G$, the relation $\mathrm{OW}_\ell(w,m)$ with $m\in\mathbb{N}$ is the smallest one such that every constant function $x\mapsto g$ has degree $0$; for each $h\in H$ the translated letter map $x\mapsto\ell(hx)$ has degree $1$; and $\mathrm{OW}_\ell(u,m)$, $\mathrm{OW}_\ell(v,n)$ imply $\mathrm{OW}_\ell(uv,m+n)$.
--   2. **Closeness on an orbit.** For a subgroup $N\le G$ and $x\in X$, the function $w$ is *$N$-close on the orbit of $x$* if $w(y)\,w(z)^{-1}\in N$ for all $y,z$ in the $H$-orbit of $x$.
--   3. **Orbit bound.** Let $L\le G$ be a subgroup and $\gamma$ a normal cost on $L$ (a function $\gamma:G\to\mathbb{R}$, nonnegative, with $\gamma(1)=0$, which on $L$ is symmetric, invariant under conjugation by $G$ and subadditive). For $B\in\mathbb{R}$, $w$ is *$B$-bounded on the orbit of $x$* if it is $L$-close there and
--   $$\gamma\bigl(w(y)\,w(z)^{-1}\bigr)\le B\qquad\text{for all } y,z \text{ in the orbit of } x.$$
--   4. **Evolution.** For finite $H$, let $\bar v(x)=v(h_1x)\cdots v(h_{|H|}x)$ be the orbit average along a fixed enumeration of $H$. The relation $\mathrm{Ev}(w,m;\,v,n)$ is the smallest one such that $\mathrm{Ev}(w,m;\,w,m)$ holds; $\mathrm{Ev}(w,m;\,v,n)$ implies $\mathrm{Ev}(w,m;\,x\mapsto v(x)a,\ n)$ for every $a\in G$ (right normalization); and $\mathrm{Ev}(w,m;\,v,n)$ implies $\mathrm{Ev}(w,m;\,\bar v,\ |H|\,n)$ (averaging). Thus $(v,n)$ arises from $(w,m)$ by finitely many normalization and averaging steps, the counter being multiplied by $|H|$ at each averaging.
--
--   Both moves preserve orbit words, with the counter tracking the degree. After normalizing by $w(x)^{-1}$ and averaging, $N$-closeness on an orbit improves to $[N,N]$-closeness, while an orbit bound $B$ grows to at most $|H|B$. Iterating along the derived series produces functions that are nearly constant on orbits with controlled cost, which is how correction paths of bounded length are built.
--
--   **Formalization Note** `OrbitWords`, `OrbitIn` (closeness), `OrbitBound` (taking `c : NormalCost L`) and `Evolution` (constructors `refl`, `normalize`, `average`, the last using `orbitAverage` and `Fintype.card H * n`) are the four definitions; `[Fintype H]` is assumed for `Evolution`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/EuclideanRamsey/OrbitAveraging.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/EuclideanRamsey/OrbitAveraging.lean by skeleton subtraction
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
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_ColoringCompactness
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_NormalCost

namespace OAI

universe uGroup uAction uPoint

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
open scoped BigOperators
variable {G : Type uGroup} {H : Type uAction} {X : Type uPoint} [Group G] [Group H] [MulAction H X]

inductive OrbitWords (letter : X → G) : (X → G) → ℕ → Prop
  | diag (g : G) : OrbitWords letter (fun _ => g) 0
  | point (h : H) : OrbitWords letter (fun x => letter (h•x)) 1
  | mul {u v m n} : OrbitWords letter u m → OrbitWords letter v n → OrbitWords letter (u*v) (m+n)
namespace OrbitWords
variable {letter : X → G} {w : X → G} {m : ℕ}
end OrbitWords

def OrbitIn (N : Subgroup G) (w : X → G) (x : X) : Prop :=
  ∀ y z,SameOrbit (H:=H) x y → SameOrbit (H:=H) x z → w y*(w z)⁻¹∈N

def OrbitBound {L : Subgroup G} (c : NormalCost L) (w : X → G) (b : ℝ) (x : X) : Prop :=
  OrbitIn (H:=H) L w x ∧ ∀ y z,SameOrbit (H:=H) x y → SameOrbit (H:=H) x z →
    c.cost (w y*(w z)⁻¹)≤b

end EuclideanRamsey
namespace EuclideanRamsey
open scoped BigOperators
variable {G : Type uGroup} {H : Type uAction} {X : Type uPoint} [Group G] [Group H] [MulAction H X] [Fintype H]

inductive Evolution : (X → G) → ℕ → (X → G) → ℕ → Prop
  | refl (w m) : Evolution w m w m
  | normalize {w m v n} : Evolution w m v n → (a : G) →
      Evolution w m (fun x => v x*a) n
  | average {w m v n} : Evolution w m v n →
      Evolution w m (orbitAverage (H:=H) v) (Fintype.card H*n)
namespace Evolution
variable {w v u : X → G} {m n k : ℕ}
end Evolution

end EuclideanRamsey
namespace EuclideanRamsey
open scoped BigOperators
variable {G : Type uGroup} {H : Type uAction} {X : Type uPoint} [Group G] [Group H] [MulAction H X] [Fintype H] [Fintype X]

end EuclideanRamsey

end

end OAI


