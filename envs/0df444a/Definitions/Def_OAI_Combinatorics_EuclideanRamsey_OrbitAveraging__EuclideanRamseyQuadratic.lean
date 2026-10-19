-- Prove2me | Definitions.Def_OAI_Combinatorics_EuclideanRamsey_OrbitAveraging__EuclideanRamseyQuadratic
-- name    : OAI_Combinatorics_EuclideanRamsey_OrbitAveraging__EuclideanRamseyQuadratic
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T07:57:30.970456+00:00
-- url     : https://prove2.me/theorems/b5888b16-71ce-4af4-849f-3f4df3c1d6f0
-- title:
--   Orbit words, orbit-wise closeness and cost bounds, and averaging evolutions of group-valued functions
-- statement:
--   Let $G$ and $H$ be groups and let $H$ act on a set $X$, written $(h,x)\mapsto hx$; the orbit of $x\in X$ is $\{hx:\ h\in H\}$. Functions $w:X\to G$ are multiplied pointwise.
--
--   1. **Orbit words.** For a letter map $\ell:X\to G$, the relation $\mathrm{OW}_\ell(w,m)$, for $w:X\to G$ and $m\in\mathbb{N}$, is the smallest one such that every constant function $x\mapsto g$ ($g\in G$) has degree $0$; for each $h\in H$ the translated letter map $x\mapsto\ell(hx)$ has degree $1$; and $\mathrm{OW}_\ell(u,m)$ together with $\mathrm{OW}_\ell(v,n)$ implies $\mathrm{OW}_\ell(uv,m+n)$.
--   2. **Closeness on an orbit.** For a subgroup $N\le G$ and $x\in X$, the function $w$ is *$N$-close on the orbit of $x$* if $w(y)\,w(z)^{-1}\in N$ for all $y,z$ in the orbit of $x$.
--   3. **Orbit bound.** Let $L\le G$ be a subgroup and $\gamma$ a normal cost on $L$, that is, a function $\gamma:G\to\mathbb{R}$ with $\gamma\ge 0$ and $\gamma(1)=0$ which on $L$ satisfies $\gamma(g^{-1})=\gamma(g)$, $\gamma(kgk^{-1})=\gamma(g)$ for all $k\in G$, and $\gamma(gh)\le\gamma(g)+\gamma(h)$. For $B\in\mathbb{R}$, the function $w$ is *$B$-bounded on the orbit of $x$* if it is $L$-close there and
--   $$\gamma\bigl(w(y)\,w(z)^{-1}\bigr)\le B\qquad\text{for all } y,z \text{ in the orbit of } x.$$
--   4. **Evolution.** Let $H$ be finite, enumerated in a fixed order as $h_1,\dots,h_{|H|}$, and let $\bar v(x)=v(h_1x)\,v(h_2x)\cdots v(h_{|H|}x)$ be the orbit average of $v:X\to G$. The relation $\mathrm{Ev}(w,m;\,v,n)$, between pairs $(w,m)$ and $(v,n)$ of functions $X\to G$ and natural numbers, is the smallest one such that $\mathrm{Ev}(w,m;\,w,m)$ holds; $\mathrm{Ev}(w,m;\,v,n)$ implies $\mathrm{Ev}(w,m;\,x\mapsto v(x)a,\ n)$ for every $a\in G$ (right normalization); and $\mathrm{Ev}(w,m;\,v,n)$ implies $\mathrm{Ev}(w,m;\,\bar v,\ |H|\,n)$ (averaging). Thus $(v,n)$ arises from $(w,m)$ by finitely many normalization and averaging steps, the counter being multiplied by $|H|$ at each averaging.
--
--   Both moves of an evolution turn an orbit word of degree $m$ into an orbit word whose degree is the new counter, and they preserve closeness on orbits with respect to a normal subgroup. Normalizing by $w(x)^{-1}$ and then averaging upgrades $N$-closeness on the orbit of $x$, for normal $N$, to $[N,N]$-closeness. Moreover, if all values of $v$ on the orbit of $x$ lie in a normal subgroup $L$ and have cost at most $B$, then averaging followed by right normalization with $v(x)^{-1}$ gives values in $L$ of cost at most $(|H|-1)B$, while the counter is multiplied by $|H|$, so costs shrink relative to the counter. Iterating along the derived series, a finite group acting on a finite set yields orbit words that are close on every orbit with cost small compared with their degree; these are the raw material for correction paths in the construction of monochromatic congruent copies.
--
--   **Formalization Note** `OrbitWords`, `OrbitIn` (closeness), `OrbitBound` (taking `c : NormalCost L`) and `Evolution` (constructors `refl`, `normalize`, `average`, the last using `orbitAverage` and `Fintype.card H * n`) are the four definitions; `[Fintype H]` is assumed only for `Evolution`, and the acting group is an implicit argument of all four. The orbit average uses the enumeration `Finset.univ.toList` of `H`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/EuclideanRamsey/OrbitAveraging.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/EuclideanRamsey/OrbitAveraging.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the EuclideanRamseyQuadratic mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_EuclideanRamseyQuadratic
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Model__EuclideanRamseyQuadratic
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorNecessity__EuclideanRamseyQuadratic
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorDescent__EuclideanRamseyQuadratic
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SmoothingKernel__EuclideanRamseyQuadratic
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Hessian__EuclideanRamseyQuadratic
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_DifferentialSplitting__EuclideanRamseyQuadratic
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SmoothingMatrix__EuclideanRamseyQuadratic
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_LatticeMoments__EuclideanRamseyQuadratic
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Discretization__EuclideanRamseyQuadratic
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_AdicLifting__EuclideanRamseyQuadratic
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorPresentation__EuclideanRamseyQuadratic
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SignedRows__EuclideanRamseyQuadratic
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_FiniteEuclidean__EuclideanRamseyQuadratic
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_PathFractions__EuclideanRamseyQuadratic
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_DerivedFractions__EuclideanRamseyQuadratic
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_PathWords__EuclideanRamseyQuadratic
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_UltrafilterStrings__EuclideanRamseyQuadratic
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_PathSynchronization__EuclideanRamseyQuadratic
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_CornerGroup__EuclideanRamseyQuadratic
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_ColoringCompactness__EuclideanRamseyQuadratic
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_NormalCost__EuclideanRamseyQuadratic

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


