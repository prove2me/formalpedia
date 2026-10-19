-- Prove2me | Definitions.Def_OAI_Analysis_DiamondDistortion_Orthogonality
-- name    : OAI_Analysis_DiamondDistortion_Orthogonality
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T00:01:45.800131+00:00
-- url     : https://prove2.me/theorems/fd59fe37-bfad-4b7f-aac6-3d2fd23e51ad
-- title:
--   Colour support of a finitely supported array and restriction of a function to a finite set
-- statement:
--   Let $\iota$ and $\kappa$ be sets, write $c_{00}(\iota)$ for the finitely supported functions $p:\iota\to\mathbb{R}$, with support $\operatorname{supp}p=\{v\in\iota:\ p(v)\neq0\}$, and let $\delta_v$ be the indicator of $\{v\}$. The file defines two elementary constructions.
--
--   1. **Colour support.** For a colouring $c:\iota\to\kappa$ and $p\in c_{00}(\iota)$,
--   $$
--   \mathrm{cs}_c(p)=c(\operatorname{supp}p)=\{c(v):\ v\in\iota,\ p(v)\neq0\},
--   $$
--   a finite subset of $\kappa$. The definition formally also takes a segment system on $\iota$ as an argument, which plays no role in the value.
--
--   2. **Finite array.** For a finite set $S\subseteq\iota$ and an arbitrary function $a:\iota\to\mathbb{R}$,
--   $$
--   a\mathbf 1_S=\sum_{v\in S}a(v)\,\delta_v\in c_{00}(\iota),
--   $$
--   the finitely supported function equal to $a$ on $S$ and to $0$ off $S$.
--
--   These are used with segment norms: given a collection of finite segments of $\iota$ containing all singletons, the segment norm of $u\in c_{00}(\iota)$ is $\sup\big(\sum_i(\sum_{v\in S_i}u(v))^2\big)^{1/2}$ over finite families of pairwise disjoint segments. In the surrounding development, a colouring that is constant on every segment splits $\iota$ into components, and two arrays $p,q$ with disjoint colour supports satisfy $\|p+q\|^2\le\|p\|^2+\|q\|^2$ in the segment norm. The finite-array construction turns a pattern of coefficients, such as the values $x(e_v)$ of a dual functional at finitely many unit vectors, into a finitely supported test vector.
--
--   **Formalization Note** Both definitions live in the namespace `SegmentSystem`: `colorSupport` takes the segment system as an explicit but unused argument and is `p.support.image c`, while `finiteArray` takes no segment system.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/DiamondDistortion/Orthogonality.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/DiamondDistortion/Orthogonality.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the DiamondDistortion mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_DiamondDistortion
import Definitions.Def_OAI_Analysis_DiamondDistortion_SegmentNorm
import Definitions.Def_OAI_Analysis_DiamondDistortion_Ancestry

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe u v

noncomputable section
open scoped BigOperators Classical Topology
open Set

namespace DiamondDistortion

namespace SegmentSystem
variable {ι κ : Type*} (T : SegmentSystem ι)

def colorSupport (_T : SegmentSystem ι) (c : ι → κ) (p : ι →₀ ℝ) : Finset κ := p.support.image c

def finiteArray (S : Finset ι) (a : ι → ℝ) : ι →₀ ℝ :=
  ∑ v ∈ S,a v • Finsupp.single v 1

end SegmentSystem

end DiamondDistortion

end

end OAI


