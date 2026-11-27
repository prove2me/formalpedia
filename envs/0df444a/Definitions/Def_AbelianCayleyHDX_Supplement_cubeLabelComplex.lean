-- Prove2me | Definitions.Def_AbelianCayleyHDX_Supplement_cubeLabelComplex
-- name    : AbelianCayleyHDX_Supplement_cubeLabelComplex
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-27T00:14:18.538887+00:00
-- url     : https://prove2.me/theorems/f4d91e34-c039-4122-b93b-f6a448363966
-- title:
--   Cube–label Cayley complexes (generators, top faces, weights)
-- statement:
--   **Cube–label Cayley complexes.** Fix integers $d\ge2$, $k\ge1$ and $a\ge1$, and write a vertex $x\in\mathbb F_2^{k+a}$ as a pair $(\mathrm{pos}(x),\mathrm{lab}(x))\in\mathbb F_2^k\times\mathbb F_2^a$: its *cube coordinate* (first $k$ coordinates) and its *label* (last $a$ coordinates).
--
--   1. The **generators** are
--   $$S=\{s:\ \mathrm{lab}(s)\neq0,\ \mathrm{pos}(s)\in\{0,e_1,\dots,e_k\}\},$$
--   so $|S|=(k+1)(2^a-1)$.
--   2. The **top faces** are the $(d+1)$-cliques of $\mathrm{Cay}(\mathbb F_2^{k+a},S)$. Equivalently, they are the sets of $d+1$ points with pairwise distinct labels whose cube coordinates lie in a single cube edge $\{u,u+e_i\}$.
--   3. The **unnormalized weight** of a top face $T$ is $(d-1)k$ if all its points lie in one cube fibre. If $T$ meets the two fibres of a cube edge in $j$ and $d+1-j$ points, its weight is
--   $$\binom{d-1}{j-1}^{-1},$$
--   which is symmetric in $j\leftrightarrow d+1-j$.
--   4. The top-face **distribution** $\mu$ is this weight normalized over all top faces.
--
--   These complexes are translation invariant. Each codimension-two link is the tensor product of a small "position" chain (a fibre with its neighbouring fibres, or the two fibres of an edge) with a complete graph on the unused labels. The weights are chosen so that every such link is a two-sided $1/d$-spectral expander. They give an elementary construction of complexes with the properties stated in Theorem 1.3, as an alternative to the graph-product construction of Section 5.
--
--   **Formalization Note** `pos` and `lab` split `Fin (k + a)` with `Fin.castAdd` and `Fin.natAdd`. The weight of a split face is written as the average over its points of $\binom{d-1}{c(x)-1}^{-1}$, where $c(x)$ is the number of points in the fibre of $x$; all terms of this average are equal.
-- source:
--   Construction for Theorem 1.3 of Mao, Abelian Cayley High-Dimensional Expanders with Polylogarithmic Degree, arXiv:2609.08937 (held version, sha256 6f5b0daa…75ba), Theorem 1.3 (p.4); a variant of the cube × labels skeleton of Section 5 (pp.19–21) with explicit split-type weights

import Mathlib
import Definitions.Def_ReplParity_Vec
open ReplParity (Vec)

namespace AbelianCayleyHDX.Supplement.CubeLabel

/-- The cube coordinate `pos x ∈ 𝔽₂ᵏ` of `x ∈ 𝔽₂^{k+a}` (its first `k` coordinates). -/
def pos {k a : ℕ} (x : Vec (k + a)) : Vec k := fun i => x (Fin.castAdd a i)

/-- The label `lab x ∈ 𝔽₂ᵃ` of `x ∈ 𝔽₂^{k+a}` (its last `a` coordinates). -/
def lab {k a : ℕ} (x : Vec (k + a)) : Vec a := fun i => x (Fin.natAdd k i)

/-- The generators: nonzero label, cube part `0` or a unit vector `eᵢ`. -/
def gens (k a : ℕ) : Finset (Vec (k + a)) :=
  Finset.univ.filter fun s => lab s ≠ 0 ∧ (pos s = 0 ∨ ∃ i : Fin k, pos s = Pi.single i 1)

/-- The top faces: `(d+1)`-cliques of the Cayley graph `Cay(𝔽₂^{k+a}, gens k a)`, i.e. `d + 1`
points with pairwise distinct labels whose cube coordinates lie in one cube edge. -/
def tops (d k a : ℕ) : Finset (Finset (Vec (k + a))) :=
  Finset.univ.filter fun T => T.card = d + 1 ∧ ∀ x ∈ T, ∀ y ∈ T, x ≠ y → x + y ∈ gens k a

/-- Unnormalized weight of a top face: `(d - 1)k` if all its points lie in one cube fibre; if it
meets the two fibres of a cube edge in `j` and `d + 1 - j` points, `1 / binom(d - 1, j - 1)`
(symmetric in `j ↔ d + 1 - j`), written as the average over its points. -/
def weight (d k a : ℕ) (T : Finset (Vec (k + a))) : ℚ :=
  if ∀ x ∈ T, ∀ y ∈ T, pos x = pos y then ((d : ℚ) - 1) * k
  else (∑ x ∈ T, (1 : ℚ) / (Nat.choose (d - 1) ((T.filter fun y => pos y = pos x).card - 1) : ℚ)) /
    (d + 1)

/-- The top-face probability distribution: `weight` normalized over `tops`. -/
def mu (d k a : ℕ) (T : Finset (Vec (k + a))) : ℚ :=
  weight d k a T / ∑ τ ∈ tops d k a, weight d k a τ

end AbelianCayleyHDX.Supplement.CubeLabel


