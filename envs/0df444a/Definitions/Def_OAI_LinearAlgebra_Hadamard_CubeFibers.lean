-- Prove2me | Definitions.Def_OAI_LinearAlgebra_Hadamard_CubeFibers
-- name    : OAI_LinearAlgebra_Hadamard_CubeFibers
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-14T18:17:03.893385+00:00
-- url     : https://prove2.me/theorems/168e6604-7c58-40fe-a39e-0a6a19b8e256
-- title:
--   Membership in the cube fibres $\{k : v_k^3 = z\}$ of a vector in $\mathbb{C}^6$
-- statement:
--   Index the coordinates of $\mathbb{C}^{6}$ by $\{0,1,\dots,5\}$. For a vector $v=(v_0,\dots,v_5)\in\mathbb{C}^{6}$ and a value $z\in\mathbb{C}$, the *cube fibre* of $v$ over $z$ is the set of positions at which the cube of $v$ equals $z$,
--   $$F_z(v)=\{k\in\{0,\dots,5\}:\ v_k^{3}=z\}.$$
--   The fibre itself is introduced in the base definitions of this development, alongside complex Hadamard matrices, entrywise squares and row ratios. This file records its membership rule: for every $v\in\mathbb{C}^{6}$, every $z\in\mathbb{C}$ and every index $k$,
--   $$k\in F_z(v)\iff v_k^{3}=z .$$
--
--   When the cubes $v_k^{3}$ take only two distinct values $a\neq b$, the index set splits as the disjoint union $F_a(v)\sqcup F_b(v)$, and sums over the coordinates decompose along this splitting. This is the language in which the cancellation statement for row ratios is phrased: for a $6\times 6$ complex Hadamard matrix $H$ whose entrywise square is also complex Hadamard, and two distinct rows $i\neq j$, if the cubes of the ratios $r_k=H_{ik}\overline{H_{jk}}$ take only the values $a\neq b$, then the ratios sum to zero over the fibre $F_a(r)$ (and, by symmetry, over $F_b(r)$).
--
--   **Formalization Note** `cubeFiber v z` is the `Finset` obtained by filtering `Finset.univ` over `Index = Fin 6` with the predicate `v i ^ 3 = z` (classical decidability). The only member of this file is the `@[simp]` lemma `mem_cubeFiber`, the displayed equivalence.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/LinearAlgebra/Hadamard/CubeFibers.lean

-- Generated from openai/math@1581d4c lean/OAI/LinearAlgebra/Hadamard/CubeFibers.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the HadamardCubeFiber mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_HadamardCubeFiber
import Definitions.Def_OAI_LinearAlgebra_Hadamard_Polynomials

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-! Cubic values, their multiplicities, and cancellation on each fibre. -/

open scoped BigOperators Matrix

namespace HadamardSix

@[simp] lemma mem_cubeFiber (v : Index → ℂ) (z : ℂ) (i : Index) :
    i ∈ cubeFiber v z ↔ v i ^ 3 = z := by
  classical
  simp [cubeFiber]

end HadamardSix

end OAI


