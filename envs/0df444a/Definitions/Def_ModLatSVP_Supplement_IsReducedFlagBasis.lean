-- Prove2me | Definitions.Def_ModLatSVP_Supplement_IsReducedFlagBasis
-- name    : ModLatSVP_Supplement_IsReducedFlagBasis
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:18:59.544324+00:00
-- url     : https://prove2.me/theorems/e30dfc31-1e1c-4dea-849d-c3cfe2a05f04
-- title:
--   A reduced module flag given by an adapted basis
-- statement:
--   Let $M=\mathbb Z^N$, $N=nd$, be a module over a number field $K$ of degree $d$, with Gram matrix $G$ and integer action matrices $A(\omega_a)$ for an integral basis $\omega$ of $\mathcal O_K$. Index the coordinates by blocks: coordinate $id+j$ is the $j$-th vector of block $i$. An integer $N\times N$ matrix $U$ is an **adapted basis of a reduced module flag** if
--
--   1. $U$ is unimodular ($\det U=\pm1$), so its columns form a $\mathbb Z$-basis of $M$;
--   2. in this basis every $U^{-1}A(\omega_a)U$ is block upper triangular, so that the span $V_i$ of the first $i$ blocks is a $K$-subspace, $\dim_K V_i=i$: the subspaces $0=V_0\subset V_1\subset\cdots\subset V_n$ form a **module flag**;
--   3. the flag is **reduced** at every index $1\le i\le n$: for the Gram matrix $U^{T}GU$, the minimum of the block $L_i=\pi_{V_{i-1}^\perp}(M\cap V_i)$ equals the minimum of the projected module $\pi_{V_{i-1}^\perp}M$.
--
--   This is the "reduced module flag" that Algorithm 1 computes (Theorems 4.5 and 6.2).
--
--   **Formalization Note** Reducedness is the published $\texttt{ModLatSVP.ReducedAt}$ applied to $U^{T}GU$ in the block indexing; block triangularity on the integral basis implies it for every $\alpha\in K$ by linearity.
-- source:
--   Kim, Lee, Son, Exact SVP and CVP in Structured Lattices: Polynomial-Space Algorithms and Reductions, STOC 2027 submission (manuscript sha256 e7151fad…), Definition 2.2, p.14 (PDF p.14): module flags, adapted bases, reducedness at every index

import Mathlib
import Definitions.Def_ModLatSVP_IsModuleFlag

open Matrix

namespace ModLatSVP

namespace Supplement

/-- The block indexing of `ℤ^N`, `N = n d`: coordinate `i d + j` is the `j`-th vector of block `i`
(Mathlib's `finProdFinEquiv`), so the first `i d` coordinates are the first `i` blocks. -/
def flagIndex {n d N : ℕ} (hN : N = n * d) : Fin N ≃ Fin n × Fin d :=
  (finCongr hN).trans finProdFinEquiv.symm

/-- A reduced module flag, given by an adapted basis. Kim, Lee, Son, *Exact SVP and CVP in Structured
Lattices: Polynomial-Space Algorithms and Reductions*, STOC 2027 submission (manuscript sha256 e7151fad…),
Definition 2.2, p.14 (PDF p.14): "A module flag of M is a chain of K-subspaces 0 = V₀ ⊂ V₁ ⊂ ⋯ ⊂ V_n =
M ⊗_ℤ ℚ, dim_K V_i = i"; "An adapted basis of M is a ℤ-basis whose first id vectors form a basis of
M_i"; the flag is reduced if it is reduced at every index `1 ≤ i ≤ n`.

For the module `ℤ^N` (`N = n d`) with Gram matrix `G` and action matrices `A a = A(ω_a)`,
`IsReducedFlagBasis hN G A U` says that the columns of the integer matrix `U` are an adapted basis of a
reduced module flag:
1. `U` is unimodular (`det U = ±1`), so its columns are a `ℤ`-basis of the module;
2. in the new basis every action matrix `U⁻¹ A(ω_a) U` is block upper triangular: entry `(p, q)` is zero
   unless block `p` ≤ block `q`, i.e. the span of the first `i` blocks is a `K`-subspace `V_i`;
3. the new Gram matrix `Uᵀ G U` is reduced at every index `1 ≤ i ≤ n` (`ModLatSVP.ReducedAt`).

**Formalization Note.** Block triangularity for the integral basis `ω` gives it for every `α ∈ K` by
`ℚ`-linearity. This is the published `ModLatSVP.IsModuleFlag` and `ModLatSVP.ReducedAt` read in the basis
`U`. -/
def IsReducedFlagBasis {n d N : ℕ} (hN : N = n * d) (G : Matrix (Fin N) (Fin N) ℚ)
    (A : Fin d → Matrix (Fin N) (Fin N) ℤ) (U : Matrix (Fin N) (Fin N) ℤ) : Prop :=
  IsUnit U.det ∧
  (∀ (a : Fin d) (p q : Fin n × Fin d),
    ((U.map (Int.cast : ℤ → ℚ))⁻¹ * (A a).map (Int.cast : ℤ → ℚ) * U.map (Int.cast : ℤ → ℚ))
        ((flagIndex hN).symm p) ((flagIndex hN).symm q) ≠ 0 → p.1 ≤ q.1) ∧
  ∀ i : ℕ, 1 ≤ i → i ≤ n →
    ReducedAt (reindex (flagIndex hN) (flagIndex hN)
      (((U.map (Int.cast : ℤ → ℚ))ᵀ * G * U.map (Int.cast : ℤ → ℚ)).map (fun q : ℚ => (q : ℝ)))) n i

end Supplement

end ModLatSVP


